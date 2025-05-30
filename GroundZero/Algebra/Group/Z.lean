import GroundZero.Algebra.Group.Symmetric
import GroundZero.HITs.Circle

open GroundZero.Structures GroundZero.Types.Equiv
open GroundZero.HITs.Circle (base loop)
open GroundZero.Types GroundZero.HITs
open GroundZero.Types.Id (ap)

namespace GroundZero.Algebra

hott definition ZΩ : Group :=
Group.intro (Circle.isGroupoid Circle.base Circle.base) Id.trans Id.inv (idp base)
  (λ a b c, (Id.assoc a b c)⁻¹) Id.lid Id.invComp

hott definition ZΩ.abelian : ZΩ.isCommutative := Circle.comm

hott definition helix {G : Group} (z : G.carrier) : S¹ → Type :=
Circle.rec G.carrier (GroundZero.ua (Group.left G z))

hott definition power {G : Group} (z : G.carrier) (p : ZΩ.carrier) : G.carrier :=
@transport S¹ (helix z) base base p G.e

-- In cubicaltt these two lemmas will just compute
hott lemma helix.loop {G : Group} (z x : G.carrier) :
  transport (helix z) loop x = G.φ z x :=
begin
  transitivity; apply Equiv.transportToTransportconst;
  transitivity; apply ap (transportconst · x);
  apply Circle.recβrule₂; apply uaβ
end

hott lemma helix.loopInv {G : Group} (z x : G.carrier) :
  transport (helix z) Circle.loop⁻¹ x = G.φ (G.ι z) x :=
begin
  transitivity; apply Equiv.transportToTransportconst;
  transitivity; apply ap (transportconst · x);
  transitivity; apply Id.mapInv; apply ap;
  apply Circle.recβrule₂; apply uaβrev
end

hott lemma power.succ {G : Group} (z : G.carrier) :
  Π p, power z (Circle.succ p) = G.φ z (power z p) :=
begin intro p; transitivity; apply Equiv.transportcom; apply helix.loop end

hott lemma power.pred {G : Group} (z : G.carrier) :
  Π p, power z (Circle.pred p) = G.φ (G.ι z) (power z p) :=
begin intro p; transitivity; apply Equiv.transportcom; apply helix.loopInv end

hott theorem power.mul {G : Group} (z : G.carrier) :
  Π (p q : ZΩ.carrier), power z (p ⬝ q) = G.φ (power z p) (power z q) :=
begin
  intro p q; fapply @Circle.Ωind₁ _ (λ p, power z (p ⬝ q) = G.φ (power z p) (power z q)) <;> clear p;
  { symmetry; apply G.oneMul };
  { intros p ih; transitivity; apply ap; transitivity;
    symmetry; apply Id.assoc; transitivity; apply ap (Id.trans p);
    apply Circle.comm; apply Id.assoc; transitivity; apply power.succ;
    transitivity; apply ap (G.φ z); exact ih;
    transitivity; symmetry; apply G.mulAssoc;
    apply ap (G.φ · _); symmetry; apply power.succ };
  { intros p ih; transitivity; apply ap; transitivity;
    symmetry; apply Id.assoc; transitivity; apply ap (Id.trans p);
    apply Circle.comm; apply Id.assoc; transitivity; apply power.pred;
    transitivity; apply ap (G.φ (G.ι z)); exact ih;
    transitivity; symmetry; apply G.mulAssoc;
    apply ap (G.φ · _); symmetry; apply power.pred }
end

hott definition ZΩ.rec {G : Group} (z : G.carrier) : Group.Hom ZΩ G :=
Group.mkhomo (power z) (power.mul z)

hott definition ZΩ.mul (p q : ZΩ.carrier) : ZΩ.carrier :=
(@power _ (Group.S ZΩ.1.zero) (Group.left ZΩ p) q).1 Id.refl

hott theorem power.one {G : Group} : Π p, power G.e p = G.e :=
begin
  fapply Circle.Ωind₁; reflexivity;
  { intros p ih; transitivity; apply power.succ;
    transitivity; apply G.oneMul; exact ih };
  { intros p ih; transitivity; apply power.pred;
    transitivity; apply ap (G.φ · _);
    symmetry; apply Group.unitInv;
    transitivity; apply G.oneMul; exact ih }
end

hott definition power.zero {G : Group} (x : G.carrier) : power x (idp base) = G.e :=
by reflexivity

hott remark ZΩ.mulZero (p : ZΩ.carrier) : ZΩ.mul p (idp base) = idp base :=
by reflexivity

-- something is really wrong with this thing
--hott def ZΩ.zeroMul (p : ZΩ.carrier) : ZΩ.mul (idp base) p = idp base :=
--@ap (Group.S ZΩ.1.zero).carrier ZΩ.carrier (power (ideqv _) p) (ideqv _) (λ e, e.1 (idp base)) (power.one p)

end GroundZero.Algebra
