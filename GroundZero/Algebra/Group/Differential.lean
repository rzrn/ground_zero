import GroundZero.Algebra.Group.Subgroup

open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero

/-
  Differential group.
  * https://encyclopediaofmath.org/wiki/Differential_group
-/

namespace GroundZero.Algebra
universe u v u' v' w

namespace Group
  variable {G : Group}

  hott definition imImplKer {φ : Hom G G} (H : φ ⋅ φ = 0) : (im φ).set ⊆ (ker φ).set :=
  begin
    intro x; fapply HITs.Merely.rec; apply G.hset;
    intro ⟨y, p⟩; change _ = _; transitivity; apply ap _ (Id.inv p);
    apply @idhom _ _ _ _ _ (φ ⋅ φ) 0; apply H
  end

  hott lemma boundaryOfBoundary {φ : Hom G G}
    (p : (im φ).set ⊆ (ker φ).set) : φ ⋅ φ = 0 :=
  begin
    fapply Hom.funext; intro x; apply p;
    apply HITs.Merely.elem; existsi x; reflexivity
  end

  hott lemma boundaryEqv (φ : Hom G G) :
    (φ ⋅ φ = 0) ≃ ((im φ).set ⊆ (ker φ).set) :=
  begin
    apply Structures.propEquivLemma;
    apply Homo.set; apply Ens.ssubset.prop;
    exact imImplKer; exact boundaryOfBoundary
  end
end Group

hott definition Diff := Σ (G : Abelian) (δ : Abelian.Hom G G), δ ⋅ δ = 0

-- Accessors
hott definition Diff.abelian (G : Diff) := G.1
hott definition Diff.group (G : Diff) := G.abelian.group

hott definition Diff.δ   (G : Diff) : Group.Hom G.group G.group := G.2.1
hott definition Diff.sqr (G : Diff) : G.δ ⋅ G.δ = 0 := G.2.2

namespace Diff
  open GroundZero.Algebra.Group (im ker)
  variable (G : Diff)

  hott lemma univ : (Group.im G.δ).set ⊆ (ker G.δ).set :=
  Group.imImplKer G.sqr
end Diff

end GroundZero.Algebra
