import GroundZero.Theorems.Univalence
import GroundZero.HITs.Merely

universe u

-- Exercise 6.9

namespace «6.9»
  open GroundZero HITs Types Proto Structures Types.Equiv Theorems.Equiv
  open Interval (happly) open Types.Id (ap) open Coproduct (inl inr)

  variable (lem : LEM₋₁ 0)

  hott definition hasNonidAut (X : Type) :=
  Σ (f : X ≃ X), f ≁ idfun

  hott definition boolNonidAut : hasNonidAut 𝟐 :=
  ⟨negBoolEquiv, λ np, ffNeqTt (np true)⟩

  hott lemma boolNonidAutIsNeg (f : 𝟐 ≃ 𝟐) : f ≁ idfun → f = negBoolEquiv :=
  begin
    intro np; apply boolEquivEqvBool.eqvInj; apply neqBoolToEqNot _ false; intro p;
    apply np; apply happly; apply @ap _ _ _ (ideqv _) Equiv.forward; transitivity;
    symmetry; apply boolEquivEqvBool.leftForward; apply ap boolEquivEqvBool.left p
  end

  hott lemma boolNonidAutContr : contr (hasNonidAut 𝟐) :=
  ⟨boolNonidAut, λ w, Sigma.prod (boolNonidAutIsNeg _ w.2)⁻¹ (notIsProp _ _)⟩

  hott lemma merelyBoolNonidAutContr (X : Type) : ∥X ≃ 𝟐∥ → contr (hasNonidAut X) :=
  Merely.rec contrIsProp (λ f, transport (contr ∘ hasNonidAut) (ua f)⁻¹ boolNonidAutContr)

  hott definition f : Π (X : Type), X → X :=
  λ X, Coproduct.elim (λ H, (merelyBoolNonidAutContr X H).1.1.forward) (λ _, idfun)
                      (lem ∥X ≃ 𝟐∥ Merely.uniq)

  hott proposition lemBoolEqv : inl |ideqv 𝟐| = lem ∥𝟐 ≃ 𝟐∥ Merely.uniq :=
  propEM Merely.uniq _ _

  hott example : f lem 𝟐 ≁ idfun :=
  transport (· ≁ idfun) (ap (Coproduct.elim _ _) (lemBoolEqv lem))
            (merelyBoolNonidAutContr _ _).1.2
end «6.9»
