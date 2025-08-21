import GroundZero.HITs.Pushout
import GroundZero.Types.Unit

open GroundZero.Types.Equiv
open GroundZero.Types.Id
open GroundZero.Types

/-
  Suspension.
  * HoTT 6.5
-/

namespace GroundZero
namespace HITs

universe u v w

hott definition Suspension (A : Type u) :=
@Pushout.{0, 0, u} 𝟏 𝟏 A (λ _, ★) (λ _, ★)

notation "∑ " => Suspension

namespace Suspension
  -- https://github.com/leanprover/lean2/blob/master/hott/homotopy/susp.hlean

  hott definition north {A : Type u} : ∑ A := Pushout.inl ★
  hott definition south {A : Type u} : ∑ A := Pushout.inr ★

  hott definition merid {A : Type u} (x : A) : @Id (∑ A) north south :=
  Pushout.glue x

  hott definition ind {A : Type u} {B : ∑ A → Type v} (n : B north) (s : B south)
    (m : Π x, n =[merid x] s) : Π x, B x :=
  Pushout.ind (λ ★, n) (λ ★, s) m

  attribute [induction_eliminator] ind

  hott definition rec {A : Type u} {B : Type v} (n s : B) (m : A → n = s) : ∑ A → B :=
  Pushout.rec (λ _, n) (λ _, s) m

  hott definition indβrule {A : Type u} {B : ∑ A → Type v}
    (n : B north) (s : B south) (m : Π x, n =[merid x] s) (x : A) :
    apd (ind n s m) (merid x) = m x :=
  by apply Pushout.indβrule

  hott definition recβrule {A : Type u} {B : Type v} (n s : B)
    (m : A → n = s) (x : A) : ap (rec n s m) (merid x) = m x :=
  by apply Pushout.recβrule

  hott instance (A : Type u) : isPointed (∑ A) := ⟨north⟩

  hott definition σ {A : Type u} [isPointed A] : A → Ω¹(∑ A) :=
  λ x, merid x ⬝ (merid (pointOf A))⁻¹

  hott lemma σComMerid {A : Type u} [isPointed A] (x : A) : σ x ⬝ merid (pointOf A) = merid x :=
  by apply Id.cancelInvComp

  hott lemma σRevComMerid {A : Type u} [isPointed A] (x : A) : (σ x)⁻¹ ⬝ merid x = merid (pointOf A) :=
  begin apply rewriteComp; symmetry; apply σComMerid end

  section
    variable {A : Type u} [isPointed A] {n : ℕ}

    hott def suspΩ : Ωⁿ(A) → Ωⁿ⁺¹(∑ A) :=
    λ ε, conjugateΩ (compInv (merid (pointOf A))) (apΩ σ ε)

    hott lemma suspIdΩ : suspΩ (idΩ (pointOf A) n) = idΩ north (n + 1) :=
    begin transitivity; apply ap (conjugateΩ _); apply apIdΩ; apply conjugateIdΩ end

    hott lemma suspRevΩ (α : Ωⁿ⁺¹(A)) : suspΩ (revΩ α) = revΩ (suspΩ α) :=
    begin transitivity; apply ap (conjugateΩ _); apply apRevΩ; apply conjugateRevΩ end

    hott lemma suspMultΩ (α β : Ωⁿ⁺¹(A)) : suspΩ (comΩ α β) = comΩ (suspΩ α) (suspΩ β) :=
    begin transitivity; apply ap (conjugateΩ _); apply apFunctorialityΩ; apply conjugateComΩ end
  end
end Suspension

end HITs
end GroundZero
