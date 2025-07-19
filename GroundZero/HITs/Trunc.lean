import GroundZero.HITs.Merely

open GroundZero.HITs.Interval (happly funext)
open GroundZero.Structures.hlevel (succ)
open GroundZero.Types.Id (ap)
open GroundZero.Proto (idfun)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types

namespace GroundZero.HITs
universe u v w

private def Trunc.aux (n : ℕ₋₂) (A : Type u) := Opaque A

attribute [nothott] Trunc.aux

hott axiom Trunc : ℕ₋₂ → Type u → Type u
| −2,            A => 𝟏
| −1,            A => ∥A∥
| succ (succ n), A => Trunc.aux n A

namespace Trunc
  variable {A : Type u} {n : ℕ₋₂}

  hott axiom elem : Π {n : ℕ₋₂} (x : A), Trunc n A
  | −2,            _ => ★
  | −1,            x => Merely.elem x
  | succ (succ n), x => Opaque.intro x

  hott opaque axiom uniq (n : ℕ₋₂) : is-n-type (Trunc n A) :=
  match n with
  | −2            => unitIsContr
  | −1            => Merely.hprop
  | succ (succ n) => λ _ _, propIsNType (λ _ _, trustCoherence) n

  @[induction_eliminator] hott axiom ind {B : Trunc n A → Type v} (elemπ : Π x, B (elem x)) (uniqπ : Π x, is-n-type (B x)) : Π x, B x :=
  match n with
  | −2            => λ x, (uniqπ x).1
  | −1            => Merely.ind elemπ (λ _, minusOneEqvProp.forward (uniqπ _))
  | succ (succ n) => λ x, Quot.withUseOf uniqπ (Opaque.ind elemπ x) x

  attribute [irreducible] Trunc

  notation "∥" A "∥₋₂" => Trunc −2 A
  notation "∥" A "∥₋₁" => Trunc −1 A

  macro:max "∥" A:term "∥" n:subscript : term => do
    `(Trunc $(← Meta.Notation.parseSubscript n) $A)

  -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/absolute.20value
  macro:max atomic("|" noWs) x:term noWs "|" n:subscript : term =>
    do `(@Trunc.elem _ $(← Meta.Notation.parseSubscript n) $x)

  hott lemma indβrule {B : ∥A∥ₙ → Type v} (elemπ : Π x, B |x|ₙ)
    (uniqπ : Π x, is-n-type (B x)) (x : A) : ind elemπ uniqπ |x|ₙ = elemπ x :=
  begin
    match n with | −2 => _ | −1 => _ | succ (succ n) => _;
    apply (uniqπ (elem x)).2; reflexivity; reflexivity
  end

  section
    variable {B : Type v} (elemπ : A → B) (uniqπ : is-n-type B)

    hott definition rec : ∥A∥ₙ → B := @ind A n (λ _, B) elemπ (λ _, uniqπ)

    hott corollary recβrule (x : A) : rec elemπ uniqπ |x|ₙ = elemπ x :=
    by apply indβrule
  end

  section
    variable {B : Type v} {C : Type w} (elemπ : A → B → C) (uniqπ : is-n-type C)

    hott definition rec₂ : ∥A∥ₙ → ∥B∥ₙ → C :=
    rec (λ a, rec (elemπ a) uniqπ) (piRespectsImpl _ uniqπ)

    hott corollary recβrule₂ (x : A) (y : B) : rec₂ elemπ uniqπ |x|ₙ |y|ₙ = elemπ x y :=
    @ap (∥B∥ₙ → C) C _ _ (· |y|ₙ) (recβrule _ _ _) ⬝ recβrule _ _ _
  end

  section
    variable {B : Type v} {C : ∥A∥ₙ → ∥B∥ₙ → Type w} (elemπ : Π x y, C |x|ₙ |y|ₙ) (uniqπ : Π x y, is-n-type (C x y))

    hott definition ind₂ : Π x y, C x y :=
    ind (λ x, ind (elemπ x) (uniqπ |x|ₙ)) (λ _, piRespectsNType _ (λ _, uniqπ _ _))

    hott corollary indβrule₂ (x : A) (y : B) : ind₂ elemπ uniqπ |x|ₙ |y|ₙ = elemπ x y :=
    @ap (Π (y : ∥B∥ₙ), C |x|ₙ y) (C |x|ₙ |y|ₙ) _ _ (· |y|ₙ) (indβrule _ _ _) ⬝ indβrule _ _ _
  end

  hott definition elemClose {B : Type v} (G : is-n-type B)
    (f g : ∥A∥ₙ → B) (H : f ∘ elem = g ∘ elem) : f = g :=
  begin
    apply Theorems.funext; fapply ind <;> intro x;
    { exact ap (λ (f : A → B), f x) H };
    { apply hlevel.cumulative; assumption }
  end

  hott definition nthTrunc (H : is-n-type A) : A ≃ ∥A∥ₙ :=
  begin
    existsi elem; apply Prod.mk <;> existsi rec id H;
    { intro; apply recβrule; };
    { apply Interval.happly; apply elemClose; apply uniq;
      apply Theorems.funext; intro; apply ap elem; apply recβrule; }
  end

  hott definition setEquiv {A : Type u} (H : hset A) : A ≃ ∥A∥₀ :=
  begin apply nthTrunc; apply zeroEqvSet.left; assumption end

  hott definition ap {A : Type u} {B : Type v} {n : ℕ₋₂} (f : A → B) : ∥A∥ₙ → ∥B∥ₙ :=
  rec (elem ∘ f) (uniq n)

  hott definition ap₂ {A : Type u} {B : Type v} {C : Type w}
    {n : ℕ₋₂} (f : A → B → C) : ∥A∥ₙ → ∥B∥ₙ → ∥C∥ₙ :=
  rec (ap ∘ f) (piRespectsNType n (λ _, uniq n))

  hott corollary apβrule {A : Type u} {B : Type v} {n : ℕ₋₂}
    {f : A → B} (a : A) : ap f |a|ₙ = |f a|ₙ :=
  by apply recβrule

  hott corollary apβrule₂ {A : Type u} {B : Type v} {C : Type w}
    {n : ℕ₋₂} {f : A → B → C} (a : A) (b : B) : ap₂ f |a|ₙ |b|ₙ = |f a b|ₙ :=
  begin transitivity; apply happly; apply recβrule; apply apβrule end

  hott lemma idmap {A : Type u} {n : ℕ₋₂} : ap idfun ~ @idfun ∥A∥ₙ :=
  begin
    fapply ind; intro; apply recβrule; intro;
    apply hlevel.cumulative; apply uniq
  end

  hott lemma apCom {A : Type u} {B : Type v} {C : Type w} {n : ℕ₋₂}
    (f : B → C) (g : A → B) : ap f ∘ ap g ~ @ap A C n (f ∘ g) :=
  begin
    fapply ind; intro; transitivity; apply Id.ap (ap _);
    apply recβrule; transitivity; apply recβrule; symmetry;
    apply recβrule; intro; apply hlevel.cumulative; apply uniq
  end

  hott theorem respectsEquiv {A : Type u} {B : Type v} {n : ℕ₋₂} (φ : A ≃ B) : ∥A∥ₙ ≃ ∥B∥ₙ :=
  ⟨ap φ.forward, (⟨ap φ.left,  (apCom _ _).trans ((happly (Id.ap ap (funext φ.leftForward))).trans  idmap)⟩,
                  ⟨ap φ.right, (apCom _ _).trans ((happly (Id.ap ap (funext φ.forwardRight))).trans idmap)⟩)⟩

  hott lemma transportOverTrunc {A : Type u} {n : ℕ₋₂} {B : A → Type v} {a b : A}
    (p : a = b) (u : ∥B a∥ₙ) : transport (∥B ·∥ₙ) p u = Trunc.ap (transport B p) u :=
  begin induction p; symmetry; apply Trunc.idmap end

  hott lemma recApElem {A : Type u} : Π {n : ℕ₋₂} {a b : A}, ∥a = b∥ₙ → |a|ₙ = |b|ₙ
  | −2            => λ _, contrImplProp (Trunc.uniq −2) _ _
  | hlevel.succ n => Trunc.rec (Id.ap Trunc.elem) (hlevel.cumulative _ (Trunc.uniq (hlevel.succ n) _ _))
end Trunc

end GroundZero.HITs
