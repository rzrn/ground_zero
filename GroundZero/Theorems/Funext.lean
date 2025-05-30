import GroundZero.Types.HEq

open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Types

/-
  The unit Interval I as Higher Inductive Type.
  Proof of functional extensionality from it.
  * HoTT 6.3

  It is primitive HIT.
  * HoTT, chapter 6, exercise 6.13
-/

namespace GroundZero.HITs
universe u v w

inductive I.rel : 𝟐 → 𝟐 → Prop
| intro : rel false true

hott axiom I : Type := Quot I.rel
hott abbreviation Interval := I

namespace Interval
  hott axiom ofBool : 𝟐 → I := Quot.mk I.rel

  hott definition i₀ : I := ofBool false
  hott definition i₁ : I := ofBool true

  hott opaque axiom seg : i₀ = i₁ :=
  trustHigherCtor (Quot.sound I.rel.intro)

  def hrec (B : I → Type u) (b₀ : B i₀) (b₁ : B i₁) (s : HEq b₀ b₁) (x : I) : B x :=
  Quot.hrecOn x (λ | false => b₀ | true => b₁)
    (λ | false, false, _ => HEq.refl b₀
       | false, true,  _ => s
       | true,  false, _ => HEq.symm s
       | true,  true,  _ => HEq.refl b₁)

  @[induction_eliminator] hott axiom ind {B : I → Type u} (b₀ : B i₀) (b₁ : B i₁) (s : b₀ =[seg] b₁) (x : I) : B x :=
  Quot.withUseOf s (hrec B b₀ b₁ (HEq.fromPathover seg s) x) x

  hott opaque axiom indβrule {B : I → Type u} (b₀ : B i₀) (b₁ : B i₁)
    (s : b₀ =[seg] b₁) : apd (ind b₀ b₁ s) seg = s :=
  trustCoherence

  attribute [irreducible] I

  noncomputable instance : OfNat I Nat.zero := ⟨i₀⟩
  noncomputable instance : OfNat I (Nat.succ Nat.zero) := ⟨i₁⟩

  hott abbreviation left  := i₀
  hott abbreviation right := i₁

  hott abbreviation zero := i₀
  hott abbreviation one  := i₁

  @[inline] hott definition rec {B : Type u} (b₀ : B) (b₁ : B) (s : b₀ = b₁) : I → B :=
  ind b₀ b₁ (Equiv.pathoverOfEq seg s)

  hott definition recβrule {B : Type u} (b₀ b₁ : B)
    (s : b₀ = b₁) : ap (rec b₀ b₁ s) seg = s :=
  begin
    apply Equiv.pathoverOfEqInj seg; transitivity;
    symmetry; apply Equiv.apdOverConstantFamily; apply indβrule
  end

  hott definition homotopy {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (p : f ~ g) (x : A) : I → B x :=
  Interval.rec (f x) (g x) (p x)

  hott definition funext {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (p : f ~ g) : f = g :=
  @ap I (Π x, B x) 0 1 (λ i x, homotopy p x i) seg

  hott definition happly {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (p : f = g) : f ~ g :=
  transport (λ g, f ~ g) p (Homotopy.id f)

  hott lemma happlyRev {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (p : f = g) : happly p⁻¹ = Homotopy.symm _ _ (happly p) :=
  begin induction p; reflexivity end

  hott lemma happlyCom {A : Type u} {B : A → Type v} {f g h : Π x, B x}
    (p : f = g) (q : g = h) : happly (p ⬝ q) = Homotopy.trans (happly p) (happly q) :=
  begin induction p; reflexivity end

  hott definition mapHapply {A : Type u} {B : Type v} {C : Type w} {a b : A} {c : B}
    (f : A → B → C) (p : a = b) : ap (f · c) p = happly (ap f p) c :=
  begin induction p; reflexivity end
end Interval

end GroundZero.HITs
