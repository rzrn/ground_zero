import GroundZero.HITs.Generalized
import GroundZero.HITs.Colimit
import GroundZero.Structures

open GroundZero.Types.Equiv (transport apd pathoverFromTrans)
open GroundZero.Structures
open GroundZero.Types.Id
open GroundZero.Types

namespace GroundZero.HITs
universe u v w

/-
  Propositional truncation is colimit of a following sequence:
    A → {A} → {{A}} → ...

  * https://github.com/fpvandoorn/leansnippets/blob/master/truncation.hlean
  * https://github.com/fpvandoorn/leansnippets/blob/master/cpp.hlean (we use this proof here)
  * https://homotopytypetheory.org/2015/07/28/constructing-the-propositional-truncation-using-nonrecursive-hits/
  * https://homotopytypetheory.org/2016/01/08/colimits-in-hott/
  * https://arxiv.org/pdf/1512.02274
-/

hott definition Merely (A : Type u) :=
Colimit (Generalized.rep A) (Generalized.dep A)

notation "∥" A "∥" => Merely A

namespace Merely
  hott definition elem {A : Type u} (x : A) : ∥A∥ :=
  Colimit.inclusion 0 x

  -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/absolute.20value
  macro:max atomic("|" noWs) x:term noWs "|" : term => `(Merely.elem $x)

  section
    variable {A : Type u} {B : ∥A∥ → Type v} (elemπ : Π x, B (elem x)) (uniqπ : Π x, prop (B x))

    hott definition resp : Π (n : ℕ) (x : Generalized.rep A n), B (Colimit.incl x)
    | Nat.zero,   x => elemπ x
    | Nat.succ n, w => @Generalized.ind _ (λ x, B (Colimit.inclusion (n + 1) x))
                         (λ x, transport B (Colimit.glue x)⁻¹ (resp n x))
                         (λ a b, uniqπ _ _ _) w

    hott definition ind : Π x, B x :=
    Colimit.ind (resp elemπ uniqπ) (λ _ _, uniqπ _ _ _)
  end

  attribute [induction_eliminator] ind

  hott definition rec {A : Type u} {B : Type v} (H : prop B) (f : A → B) : ∥A∥ → B :=
  ind f (λ _, H)

  hott lemma weakUniq {A : Type u} (x y : A) : @Id ∥A∥ |x| |y| :=
  begin
    transitivity; { symmetry; apply Colimit.glue }; symmetry;
    transitivity; { symmetry; apply Colimit.glue };
    apply ap; apply Generalized.glue
  end

  hott definition incl {A : Type u} {n : ℕ} :=
  @Colimit.incl (Generalized.rep A) (Generalized.dep A) n

  hott definition glue {A : Type u} {n : ℕ} {x : Generalized.rep A n} :
    incl (Generalized.dep A n x) = incl x :=
  Colimit.glue x

  hott definition exactNth {A : Type u} (a : A) : Π n, Generalized.rep A n
  | Nat.zero   => a
  | Nat.succ n => Generalized.dep A n (exactNth a n)

  hott definition nthGlue {A : Type u} (a : A) : Π n, incl (exactNth a n) = @incl A 0 a
  | Nat.zero   => idp _
  | Nat.succ n => Colimit.glue (exactNth a n) ⬝ nthGlue a n

  hott lemma inclUniq {A : Type u} {n : ℕ} (a b : Generalized.rep A n) :=
  calc incl a = incl (Generalized.dep A n a) : glue⁻¹,
              = incl (Generalized.dep A n b) : ap incl (Generalized.glue a b),
              = incl b                       : glue

  hott lemma inclZeroEqIncl {A : Type u} {n : ℕ} (x : A) (y : Generalized.rep A n) :=
  calc @incl A 0 x = incl (exactNth x n) : (nthGlue x n)⁻¹,
                   = incl y              : inclUniq (exactNth x n) y

  hott theorem weaklyConstantAp {A : Type u} {B : Type v} (f : A → B)
    {a b : A} (p q : a = b) (H : Π a b, f a = f b) : ap f p = ap f q :=
  let L : Π {u v : A} (r : u = v), (H a u)⁻¹ ⬝ H a v = ap f r :=
  begin intros u v r; induction r; apply Types.Id.invComp end; (L p)⁻¹ ⬝ L q

  hott lemma congClose {A : Type u} {n : ℕ} {a b : Generalized.rep A n} (p : a = b) :
    glue⁻¹ ⬝ ap incl (ap (Generalized.dep A n) p) ⬝ glue = ap incl p :=
  begin
    induction p; transitivity; symmetry; apply Id.assoc;
    apply Equiv.rewriteComp; symmetry; apply Id.rid
  end

  hott theorem congOverPath {A : Type u} {n : ℕ} {a b : Generalized.rep A n}
    (p q : a = b) : ap incl p = ap incl q :=
  weaklyConstantAp incl p q inclUniq

  hott lemma glueClose {A : Type u} {n : ℕ} {a b : Generalized.rep A n} :
      glue⁻¹ ⬝ ap incl (Generalized.glue (Generalized.dep A n a) (Generalized.dep A n b)) ⬝ glue
    = ap incl (Generalized.glue a b) :=
  begin
    symmetry; transitivity; { symmetry; apply @congClose A (n + 1) _ _ (Generalized.glue a b) };
    apply ap (· ⬝ glue); apply ap; apply congOverPath
  end

  hott lemma inclUniqClose {A : Type u} {n : ℕ} (a b : Generalized.rep A n) :
    glue⁻¹ ⬝ inclUniq (Generalized.dep A n a) (Generalized.dep A n b) ⬝ glue = inclUniq a b :=
  ap (· ⬝ glue) (ap _ glueClose)

  hott theorem uniq {A : Type u} : prop ∥A∥ :=
  begin
    apply lemContr; fapply ind;
    { intro x; existsi elem x; fapply Colimit.ind <;> intros n y;
      { apply inclZeroEqIncl };
      { apply pathoverFromTrans; symmetry; transitivity;
        apply ap (_ ⬝ ·); symmetry; apply inclUniqClose;
        symmetry; transitivity; apply ap (· ⬝ _ ⬝ _); apply Id.explodeInv;
        transitivity; symmetry; apply Id.assoc;
        transitivity; symmetry; apply Id.assoc;
        apply ap ((nthGlue x n)⁻¹ ⬝ ·); apply Id.assoc } };
    { intro x; apply contrIsProp }
  end

  hott corollary hprop {A : Type u} : is-(−1)-type ∥A∥ :=
  minusOneEqvProp.left uniq

  hott definition lift {A : Type u} {B : Type v} (f : A → B) : ∥A∥ → ∥B∥ :=
  rec uniq (elem ∘ f)

  hott definition rec₂ {A : Type u} {B : Type v} {γ : Type w} (H : prop γ)
    (φ : A → B → γ) : ∥A∥ → ∥B∥ → γ :=
  @rec A (∥B∥ → γ) (implProp H) (rec H ∘ φ)

  hott definition lift₂ {A : Type u} {B : Type v} {γ : Type w}
    (φ : A → B → γ) : ∥A∥ → ∥B∥ → ∥γ∥ :=
  rec₂ uniq (λ a b, |φ a b|)

  hott theorem equivIffTrunc {A B : Type u} (f : A → B) (g : B → A) : ∥A∥ ≃ ∥B∥ :=
  ⟨lift f, (⟨lift g, λ _, uniq _ _⟩, ⟨lift g, λ _, uniq _ _⟩)⟩

  hott definition diag {A : Type u} (a : A) : A × A := ⟨a, a⟩

  hott corollary productIdentity {A : Type u} : ∥A∥ ≃ ∥A × A∥ :=
  equivIffTrunc diag Prod.fst

  hott corollary uninhabitedImpliesTruncUninhabited {A : Type u} : ¬A → ¬∥A∥ :=
  rec Structures.emptyIsProp
end Merely

end GroundZero.HITs
