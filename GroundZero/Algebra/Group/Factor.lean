import GroundZero.Algebra.Group.Subgroup
import GroundZero.HITs.Setquot

open GroundZero.Types.Equiv (biinv transport)
open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero.HITs
open GroundZero

/- Factor/Quotient group (as Quotient type). -/

namespace GroundZero.Algebra
universe u v u' v' w

namespace Group
  variable {G : Group}

  local infixl:70 (priority := high) " * " => G.φ
  local postfix:max (priority := high) "⁻¹" => G.ι
  local notation "e" => G.e

  hott definition factorLeftRel (φ : G.subgroup) :
    G.carrier → G.carrier → Prop :=
  λ x y, ⟨ldiv φ x y, Ens.prop _ _⟩

  hott definition factorRightRel (φ : G.subgroup) :
    G.carrier → G.carrier → Prop :=
  λ x y, ⟨rdiv φ x y, Ens.prop _ _⟩

  hott definition factorEqrelLeft (φ : G.subgroup) : eqrel G.carrier :=
  ⟨factorLeftRel φ,
  begin
    apply Prod.mk;
    { intro; apply transport (· ∈ φ.set); symmetry;
      apply G.mulLeftInv; apply φ.unit }; apply Prod.mk;
    { intros x y h; apply transport (· ∈ φ.set);
      apply invMulInv; apply φ.inv; assumption };
    { intros x y z h g; apply transport (· ∈ φ.set);
      apply chainLdiv x y z; apply φ.mul <;> assumption }
  end⟩

  hott definition factorEqrelRight (φ : G.subgroup) : eqrel G.carrier :=
  ⟨factorRightRel φ,
  begin
    apply Prod.mk;
    { intro; apply transport (· ∈ φ.set); symmetry;
      apply Group.mulRightInv; apply φ.unit }; apply Prod.mk;
    { intros x y h; apply transport (· ∈ φ.set);
      apply mulInvInv; apply φ.inv; assumption };
    { intros x y z h g; apply transport (· ∈ φ.set);
      apply chainRdiv x y z; apply φ.mul <;> assumption }
  end⟩

  hott definition factorLeft (G : Group) (φ : G.subgroup) :=
  Relquot (factorEqrelLeft φ)

  hott definition factorRight (G : Group) (φ : G.subgroup) :=
  Relquot (factorEqrelRight φ)

  hott lemma factorSymm (φ : G.subgroup) (ρ : G ⊵ φ) :
    factorLeft G φ = factorRight G φ :=
  begin
    apply ap Relquot; apply GroundZero.eqrel.eq;
    apply Theorems.funext; intro; apply Theorems.funext; intro;
    fapply Types.Sigma.prod; change ldiv φ _ _ = rdiv φ _ _;
    apply HITs.Interval.happly; apply HITs.Interval.happly;
    apply cosetsEq ρ; apply propIsProp
  end

  hott definition Factor.incl {φ : G.subgroup} : G.carrier → factorLeft G φ :=
  Relquot.elem

  section
    variable {φ : G.normal}

    hott definition Factor.mul : factorLeft G φ → factorLeft G φ → factorLeft G φ :=
    begin
      fapply Relquot.lift₂;
      { intros a b; exact Factor.incl (a * b) };
      { apply Relquot.set };
      { intros a b c d p q;
        apply Relquot.sound;
        change _ ∈ φ.set; apply transport (· ∈ φ.set);
        apply calc
             b⁻¹ * (a⁻¹ * c * (d * b⁻¹)) * b
           = b⁻¹ * (a⁻¹ * c * d * b⁻¹) * b :
             ap (b⁻¹ * · * b) (Id.inv (G.mulAssoc (a⁻¹ * c) d b⁻¹))
       ... = b⁻¹ * (a⁻¹ * c * d * b⁻¹ * b) :
             G.mulAssoc b⁻¹ (a⁻¹ * c * d * b⁻¹) b
       ... = b⁻¹ * (a⁻¹ * c * d * (b⁻¹ * b)) :
             ap (G.φ b⁻¹) (G.mulAssoc (a⁻¹ * c * d) b⁻¹ b)
       ... = b⁻¹ * (a⁻¹ * c * d * e) :
             @ap G.carrier G.carrier _ _ (λ x, b⁻¹ * (a⁻¹ * c * d * x)) (G.mulLeftInv b)
       ... = b⁻¹ * (a⁻¹ * c * d) :
             ap (b⁻¹ * ·) (G.mulOne (a⁻¹ * c * d))
       ... = b⁻¹ * (a⁻¹ * (c * d)) :
             ap (b⁻¹ * ·) (G.mulAssoc a⁻¹ c d)
       ... = (b⁻¹ * a⁻¹) * (c * d) :
             Id.inv (G.mulAssoc b⁻¹ a⁻¹ (c * d))
       ... = leftDiv (a * b) (c * d) :
             ap (G.φ · (c * d)) (Id.inv (invExplode a b));
        apply isNormalSubgroup.conj φ.2; apply φ.1.mul;
        { exact p };
        { apply transport (· ∈ φ.set); apply calc
            (b * d⁻¹)⁻¹ = d⁻¹⁻¹ * b⁻¹ : invExplode b d⁻¹
                    ... = d * b⁻¹     : ap (G.φ · b⁻¹) (invInv d);
          apply φ.1.inv; apply (normalSubgroupCosets φ.2).left; exact q } }
    end

    hott definition Factor.one : factorLeft G φ := Factor.incl e

    hott lemma Factor.oneMul : Π (x : factorLeft G φ), Factor.mul Factor.one x = x :=
    begin
      fapply Relquot.indProp;
      { intro; change Relquot.elem _ = _;
        apply ap; apply G.oneMul };
      { intros; apply Relquot.set }
    end

    hott lemma Factor.assoc : Π (x y z : factorLeft G φ),
      Factor.mul (Factor.mul x y) z = Factor.mul x (Factor.mul y z) :=
    begin
      intro (x : Relquot _) (y : Relquot _) (z : Relquot _);
      induction x; induction y; induction z;
      apply ap Factor.incl; apply G.mulAssoc;
      -- ???
      apply Relquot.set; apply propIsSet; apply Relquot.set;
      apply Relquot.set; apply propIsSet; apply Relquot.set;
      apply Relquot.set; apply propIsSet; apply Relquot.set
    end

    hott lemma Factor.inv : factorLeft G φ → factorLeft G φ :=
    begin
      fapply Relquot.rec;
      { intro x; exact Factor.incl x⁻¹ };
      { intros u v H; apply Relquot.sound;
        apply transport (· ∈ φ.set); symmetry;
        apply ap (G.φ · v⁻¹); apply invInv;
        apply (normalSubgroupCosets φ.2).left; exact H };
      { apply Relquot.set }
    end

    hott lemma Factor.leftInv : Π (x : factorLeft G φ), Factor.mul (Factor.inv x) x = Factor.one :=
    begin
      intro (x : Relquot _); induction x;
      apply ap Factor.incl; apply G.mulLeftInv;
      apply Relquot.set; apply propIsSet; apply Relquot.set
    end
  end

  section
    variable (H : Group) (φ : H.normal)

    hott definition Factor : Group :=
    @Group.intro (factorLeft H φ) Relquot.set Factor.mul Factor.inv Factor.one
      Factor.assoc Factor.oneMul Factor.leftInv
  end

  infix:70 " \\ " => Factor

  hott lemma Factor.sound {φ : G.normal} {x : G.carrier} (H : x ∈ φ.set) :
    @Id (factorLeft G φ) (Factor.incl x) Factor.one :=
  begin
    apply Relquot.sound; apply transport (· ∈ φ.set);
    symmetry; apply ldivByUnit; apply φ.1.inv; assumption
  end

  hott definition Factor.lift {H : Group} (f : Hom G H) {φ : G.normal}
    (p : Π x, x ∈ φ.set → f.fst x = H.e) : factorLeft G φ → H.carrier :=
  begin
    fapply Relquot.rec; exact f.1;
    { intros x y q; apply eqOfDivEq; change H.φ _ _ = _;
      transitivity; apply ap (H.φ · (f.1 y));
      symmetry; apply homoInv f; transitivity;
      symmetry; apply homoMul; apply p; apply q };
    apply H.hset
  end

  hott definition triv.encode : G.carrier → factorLeft G (triv G) := Factor.incl

  hott definition triv.decode : factorLeft G (triv G) → G.carrier :=
  begin
    fapply Relquot.rec; exact id;
    { intro x y (p : _ = _); apply invInj;
      apply eqInvOfMulEqOne; exact Id.inv p };
    apply G.hset
  end

  hott theorem triv.factor : G ≅ G\triv G :=
  begin
    fapply mkiso; exact triv.encode;
    { intros x y; reflexivity };
    apply Prod.mk <;> existsi triv.decode;
    { intro; reflexivity };
    { fapply Relquot.indProp <;> intro;
      reflexivity; apply Relquot.set }
  end

  hott definition univ.decode : 𝟏 → factorLeft G (univ G) := λ _, Factor.one

  hott lemma univContr : contr (factorLeft G (univ G)) :=
  begin
    existsi univ.decode.{_, 1, 1} ★;
    fapply Relquot.indProp <;> intro;
    { apply Relquot.sound; apply ★ };
    { apply Relquot.set }
  end

  hott lemma univProp : prop (factorLeft G (univ G)) :=
  contrImplProp univContr

  hott theorem univFactor : Z₁ ≅ G\univ G :=
  begin
    fapply mkiso; exact univ.decode; intros a b; apply univProp;
    apply Prod.mk <;> existsi (λ _, ★) <;> intro;
    apply unitIsProp; apply univProp
  end

  section
    variable {φ : G.normal} {ψ : G.normal}

    hott definition Factor.transfer (f : φ.set ⊆ ψ.set) : (G\φ).carrier → (G\ψ).carrier :=
    begin
      fapply Relquot.rec;
      { exact Factor.incl };
      { intros x y H; apply Relquot.sound; apply f; exact H };
      { apply Relquot.set }
    end

    hott definition Factor.iso (f : φ.set ⊆ ψ.set) (g : ψ.set ⊆ φ.set) : G\φ ≅ G\ψ :=
    begin
      fapply mkiso; exact Factor.transfer f;
      { intro (x : Relquot _) (y : Relquot _);
        induction x; induction y; reflexivity;
        apply Relquot.set; apply propIsSet; apply Relquot.set;
        apply Relquot.set; apply propIsSet; apply Relquot.set };
      { apply Prod.mk <;> existsi Factor.transfer g <;> fapply Relquot.indProp;
        -- “repeat” don’t work here too
        intro; reflexivity; intros; apply Relquot.set;
        intro; reflexivity; intros; apply Relquot.set }
    end
  end
end Group

end GroundZero.Algebra
