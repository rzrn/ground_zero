import GroundZero.Algebra.Group.Basic

open GroundZero.Structures
open GroundZero.Types
open GroundZero

namespace GroundZero.Algebra
universe u v u' v' w

namespace Group
  variable {G : Group}

  hott definition P.carrier (G : Group) := ℕ → G.carrier

  hott lemma P.hset (G : Group) : Structures.hset (P.carrier G) :=
  begin apply piHset; intro; apply G.hset end

  section
    variable {H : Group}

    hott definition P.mul : P.carrier H → P.carrier H → P.carrier H :=
    λ f g n, H.φ (f n) (g n)

    hott definition P.one : P.carrier H := λ _, H.e
    hott definition P.inv : P.carrier H → P.carrier H := λ f n, H.ι (f n)
  end

  hott definition P (G : Group) : Group :=
  @Group.intro (P.carrier G) (P.hset G) P.mul P.inv P.one
    (λ _ _ _, Theorems.funext (λ _, G.mulAssoc _ _ _))
    (λ _, Theorems.funext (λ _, G.oneMul _))
    (λ _, Theorems.funext (λ _, G.mulLeftInv _))

  hott instance P.abelian (G : Group) (ρ : G.isCommutative) : (P G).isCommutative :=
  begin intros f g; fapply Theorems.funext; intro; apply ρ end

  hott definition P.unitSqr (H : Π x, G.φ x x = G.e) (x : P.carrier G) : P.mul x x = P.one :=
  begin fapply Theorems.funext; intro; apply H end

  hott definition P₂ := P Z₂

  hott theorem P₂.periodic : Π (x : P₂.carrier), P.mul x x = P.one :=
  P.unitSqr (λ | false => Id.refl | true => Id.refl)
end Group

end GroundZero.Algebra
