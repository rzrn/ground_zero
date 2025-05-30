import GroundZero.Structures

open GroundZero.Structures GroundZero.Types
open GroundZero.Theorems (funext)
open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv

namespace GroundZero
universe u v w

namespace HITs
namespace Interval
  hott definition lift {B : Type u} (φ : 𝟐 → B) (H : prop B) : I → B :=
  rec (φ false) (φ true) (H _ _)

  hott definition contrLeft : Π i, i₀ = i :=
  ind (idp i₀) seg (pathoverFromTrans seg (idp i₀) seg (idp seg))

  hott definition contrRight : Π i, i₁ = i :=
  ind seg⁻¹ (idp i₁) (pathoverFromTrans seg seg⁻¹ (idp i₁) (Id.invComp seg))

  hott theorem intervalContr : contr I := ⟨i₁, contrRight⟩

  hott corollary intervalProp : prop I :=
  contrImplProp intervalContr

  hott corollary transportOverHmtpy {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g₁ g₂ : B → C) (h : A → C) (p : g₁ = g₂) (H : g₁ ∘ f ~ h) (x : A) :
       transport (λ (g : B → C), g ∘ f ~ h) p H x
    = @transport (B → C) (λ (g : B → C), g (f x) = h x) g₁ g₂ p (H x) :=
  happly (transportOverPi _ _ _) x

  hott definition boolToInterval (φ : 𝟐 → 𝟐 → 𝟐) (a b : I) : I :=
  lift (λ x, lift (ofBool ∘ φ x) intervalProp b) intervalProp a

  hott definition neg : I → I := rec i₁ i₀ seg⁻¹
  noncomputable instance : Neg I := ⟨neg⟩

  hott definition min (a b : I) : I :=
  lift (λ | false => i₀ | true => a) intervalProp b

  hott definition max (a b : I) : I :=
  lift (λ | false => a | true => i₁) intervalProp b

  infix:70 " ∧ " => min
  infix:70 " ∨ " => max

  hott abbreviation elim {A : Type u} {a b : A} (p : a = b) : I → A := rec a b p

  hott definition lam {A : Type u} (f : I → A) : f 0 = f 1 := ap f seg

  hott lemma mapExt {A : Type u} (f : I → A) : rec (f 0) (f 1) (ap f seg) ~ f :=
  begin
    fapply ind; reflexivity; reflexivity; apply Id.trans;
    apply Equiv.transportOverHmtpy; transitivity; apply ap (· ⬝ _);
    transitivity; apply Id.rid; transitivity; apply Id.mapInv;
    apply ap; apply recβrule; apply Id.invComp
  end

  hott definition connAnd {A : Type u} {a b : A}
    (p : a = b) : Π i, a = elim p i :=
  λ i, lam (λ j, elim p (i ∧ j))

  hott definition cong {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : a = b) : f a = f b :=
  lam (λ i, f (elim p i))

  hott lemma congRefl {A : Type u} {B : Type v}
    {a : A} (f : A → B) : cong f (idp a) = idp (f a) :=
  begin
    transitivity; apply mapOverComp;
    transitivity; apply ap;
    apply recβrule; reflexivity
  end

  hott lemma mapEqCong {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : a = b) : ap f p = cong f p :=
  begin induction p; symmetry; apply congRefl end

  hott lemma negNeg : Π x, neg (neg x) = x :=
  ind (idp i₀) (idp i₁) (calc
    transport (λ x, neg (neg x) = x) seg (idp i₀) =
    (@ap I I i₁ i₀ (neg ∘ neg) seg⁻¹) ⬝ idp i₀ ⬝ seg :
      by apply transportOverInvolution
    ... = ap neg (ap neg seg⁻¹) ⬝ idp i₀ ⬝ seg :
      begin apply ap (λ p, p ⬝ idp i₀ ⬝ seg);
            apply mapOverComp end
    ... = ap neg (ap neg seg)⁻¹ ⬝ idp i₀ ⬝ seg :
      begin apply ap (λ p, p ⬝ idp i₀ ⬝ seg);
            apply ap; apply Id.mapInv end
    ... = ap neg seg⁻¹⁻¹ ⬝ idp i₀ ⬝ seg :
      begin apply ap (λ p, p ⬝ idp i₀ ⬝ seg);
            apply ap; apply ap Types.Id.symm;
            apply recβrule end
    ... = ap neg seg ⬝ idp i₀ ⬝ seg :
      begin apply ap (λ (p : i₀ = i₁), ap neg p ⬝ idp i₀ ⬝ seg);
            apply Id.invInv end
    ... = seg⁻¹ ⬝ idp i₀ ⬝ seg :
      begin apply ap (· ⬝ idp i₀ ⬝ seg);
            apply recβrule end
    ... = seg⁻¹ ⬝ seg :
      begin apply ap (· ⬝ seg);
            apply Id.rid end
    ... = idp i₁ : by apply Id.invComp)

  hott lemma negNeg' (x : I) : neg (neg x) = x :=
  (connAnd seg⁻¹ (neg x))⁻¹ ⬝ contrRight x

  hott definition twist : I ≃ I :=
  ⟨neg, ⟨⟨neg, negNeg'⟩, ⟨neg, negNeg'⟩⟩⟩

  hott corollary lineRec {A : Type u} (f : I → A) : rec (f 0) (f 1) (ap f seg) = f :=
  begin apply Theorems.funext; apply mapExt; end

  hott lemma transportOverSeg {A : Type u} (B : A → Type v) {a b : A} (p : a = b) (u : B a) :
    @transport I (λ i, B (elim p i)) 0 1 seg u = transport B p u :=
  begin
    transitivity; apply transportComp;
    transitivity; apply ap (transport B · u);
    apply recβrule; reflexivity
  end

  hott corollary transportconstWithSeg {A B : Type u} (p : A = B) (x : A) :
    @transport I (elim p) 0 1 seg x = transportconst p x :=
  by apply transportOverSeg id
end Interval

end HITs
end GroundZero
