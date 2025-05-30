import GroundZero.Theorems.Fibration
import GroundZero.HITs.Circle

open GroundZero GroundZero.HITs GroundZero.Types.Equiv
open GroundZero.Structures GroundZero.Types
open GroundZero.Types.Id (ap)
open GroundZero.Proto (idfun)

namespace GroundZero.Theorems.Hopf

namespace Real
  open HITs.Circle

  -- Real (S⁰ ↪ S¹ ↠ S¹)
  hott definition family : S¹ → Type := Circle.rec S⁰ (ua negBoolEquiv)
  hott definition total : Type := Σ x, family x

  hott definition inj (x : S⁰) : total := ⟨base, x⟩

  hott definition map : total → S¹ := Sigma.fst

  hott def μ₁ : total := ⟨base, false⟩
  hott def μ₂ : total := ⟨base, true⟩

  hott abbreviation μ := μ₁

  hott definition μLoop : μ = μ :=
  Sigma.prod (loop ⬝ loop) (Circle.Ωrecβ₂ false not not negNeg negNeg loop ⬝
                    ap not (Circle.Ωrecβ₂ false not not negNeg negNeg (idp base)))

  hott statement mapRecμ : map ∘ rec μ μLoop ~ rec base (loop ⬝ loop) :=
  begin
    fapply ind; exact idp base; apply Id.trans; apply Equiv.transportOverHmtpy;
    transitivity; apply ap (· ⬝ _ ⬝ _); transitivity; apply Id.mapInv; apply ap;
    transitivity; apply Equiv.mapOverComp; transitivity; apply ap; apply recβrule₂;
    apply Sigma.mapFstOverProd; transitivity; symmetry; apply Id.assoc;
    apply Id.compReflIfEq; symmetry; apply recβrule₂
  end

  hott lemma family.transport₁ : transport family loop ~ not :=
  begin
    intro b; transitivity; apply transportToTransportconst;
    transitivity; apply ap (transportconst · b);
    apply recβrule₂; apply uaβ
  end

  hott lemma family.transport₂ : transport family loop⁻¹ ~ not :=
  begin
    intro b; transitivity; apply transportToTransportconst;
    transitivity; apply ap (transportconst · b);
    transitivity; apply Id.mapInv; apply ap;
    apply recβrule₂; apply uaβrev
  end
end Real

namespace Complex
  -- Complex (S¹ ↪ S³ ↠ S²)
  hott def family : S² → Type := Suspension.rec S¹ S¹ (ua ∘ Circle.μₑ)
end Complex

end GroundZero.Theorems.Hopf
