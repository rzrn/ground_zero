import GroundZero.Algebra.Basic

open GroundZero.Types.Equiv (bimap biinv transport)
open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero

/-
  Basic lemmas about groups and abelian groups.

  Homomorphism properties.

  ℤ₁ and ℤ₂ groups.

  Opposite group.
  * https://en.wikipedia.org/wiki/Opposite_group
-/

namespace GroundZero.Algebra
universe u v u' v' w

section
  variable {μ : Type u} {η : Type v} (φ : μ → η)
  hott definition im.aux := Theorems.Functions.fibInh φ
  hott definition im : Ens η := ⟨im.aux φ, λ _, HITs.Merely.uniq⟩

  hott definition im.intro (m : μ) : φ m ∈ im φ :=
  begin apply HITs.Merely.elem; existsi m; reflexivity end

  hott definition im.inh (m : μ) : (im φ).inh :=
  begin apply HITs.Merely.elem; existsi φ m; apply im.intro end
end

namespace Group
  variable (G : Group)
  hott definition isproper (x : G.carrier) := x ≠ G.e

  hott definition proper := Σ x, G.isproper x

  hott definition proper.prop {x : G.carrier} : prop (G.isproper x) :=
  Structures.implProp Structures.emptyIsProp

  hott definition isSubgroup (φ : G.subset) :=
  (G.e ∈ φ) × (Π a b, a ∈ φ → b ∈ φ → G.φ a b ∈ φ) × (Π a, a ∈ φ → G.ι a ∈ φ)

  hott definition subgroup := Σ φ, isSubgroup G φ
end Group

namespace Group
  variable {G : Group}
  hott definition conjugate (a x : G.carrier) := G.φ (G.φ (G.ι x) a) x

  hott definition conjugateRev (a x : G.carrier) := G.φ (G.φ x a) (G.ι x)

  hott definition rightDiv (x y : G.carrier) := G.φ x (G.ι y)
  hott definition leftDiv  (x y : G.carrier) := G.φ (G.ι x) y

  hott definition subgroup.set (φ : G.subgroup) : Ens G.carrier := φ.1
  hott definition subgroup.subtype (φ : G.subgroup) := φ.set.subtype

  hott definition subgroup.mem (x : G.carrier) (φ : G.subgroup) := x ∈ φ.set

  hott definition subgroup.ssubset (φ ψ : G.subgroup) :=
  Ens.ssubset φ.set ψ.set

  hott definition subgroup.unit (φ : G.subgroup) := φ.2.1
  hott definition subgroup.mul  (φ : G.subgroup) := φ.2.2.1
  hott definition subgroup.inv  (φ : G.subgroup) := φ.2.2.2

  hott definition subgroup.mk (φ : G.subset) (α : G.e ∈ φ)
    (β : Π a b, a ∈ φ → b ∈ φ → G.φ a b ∈ φ)
    (γ : Π a, a ∈ φ → G.ι a ∈ φ) : subgroup G :=
  ⟨φ, (α, β, γ)⟩
end Group

namespace Group
  variable {G : Group}

  local infixl:70 (priority := high) " * " => G.φ
  local postfix:max (priority := high) "⁻¹" => G.ι
  local notation "e" => G.e

  hott lemma unitOfSqr {x : G.carrier} (H : x * x = x) :=
  calc x = e * x         : Id.inv (G.oneMul _),
         = (x⁻¹ * x) * x : ap (G.φ · x) (Id.inv (G.mulLeftInv x)),
         = x⁻¹ * (x * x) : G.mulAssoc _ _ _,
         = x⁻¹ * x       : ap (G.φ x⁻¹) H,
         = e             : G.mulLeftInv _

  hott lemma mulRightInv (x : G.carrier) : x * x⁻¹ = e :=
  unitOfSqr (calc (x * x⁻¹) * (x * x⁻¹)
                = x * (x⁻¹ * (x * x⁻¹)) : G.mulAssoc _ _ _,
                = x * (x⁻¹ * x * x⁻¹)   : ap (x * ·) (G.mulAssoc _ _ _).inv,
                = x * (e * x⁻¹)         : ap (x * ·) (ap (· * x⁻¹) (G.mulLeftInv _)),
                = x * x⁻¹               : ap (x * ·) (G.oneMul _))

  hott lemma mulOne (x : G.carrier) :=
  calc x * e = x * (x⁻¹ * x) : ap (x * ·) (G.mulLeftInv _).inv,
             = (x * x⁻¹) * x : (G.mulAssoc _ _ _).inv,
             = e * x         : ap (· * x) (G.mulRightInv _),
             = x             : G.oneMul _

  attribute [irreducible] unitOfSqr mulRightInv mulOne

  hott corollary leftUnitUniq (e' : G.carrier) (oneMul' : Π a, e' * a = a) : e' = e :=
  (G.mulOne e').inv ⬝ oneMul' e

  hott corollary rightUnitUniq (e' : G.carrier) (mulOne' : Π a, a * e' = a) : e' = e :=
  (G.oneMul e').inv ⬝ mulOne' e

  hott lemma invEqOfMulEqOne {x y : G.carrier} (H : x * y = e) :=
  calc x⁻¹ = x⁻¹ * e       : (G.mulOne _).inv,
           = x⁻¹ * (x * y) : ap (G.φ x⁻¹) H.inv,
           = (x⁻¹ * x) * y : (G.mulAssoc _ _ _).inv,
           = e * y         : ap (G.φ · y) (G.mulLeftInv x),
           = y             : G.oneMul y

  hott corollary invInv (x : G.carrier) : x⁻¹⁻¹ = x :=
  invEqOfMulEqOne (G.mulLeftInv x)

  hott corollary eqInvOfMulEqOne {x y : G.carrier} (H : x * y = e) : x = y⁻¹ :=
  (invInv x).inv ⬝ ap G.ι (invEqOfMulEqOne H)

  hott corollary mulEqOneOfInvEq {x y : G.carrier} (H : x⁻¹ = y) : x * y = e :=
  (ap (G.φ x) H).inv ⬝ (mulRightInv x)

  hott lemma invInj {x y : G.carrier} (h : x⁻¹ = y⁻¹) : x = y :=
  calc x = x⁻¹⁻¹ : (invInv x).inv,
         = y⁻¹⁻¹ : ap G.ι h,
         = y     : invInv y

  hott theorem mulCancelLeft {a b c : G.carrier} (h : c * a = c * b) :=
  calc a = e * a         : Id.inv (G.oneMul a),
         = (c⁻¹ * c) * a : ap (G.φ · a) (Id.inv (G.mulLeftInv c)),
         = c⁻¹ * (c * a) : G.mulAssoc _ _ _,
         = c⁻¹ * (c * b) : ap (G.φ c⁻¹) h,
         = (c⁻¹ * c) * b : Id.inv (G.mulAssoc _ _ _),
         = e * b         : ap (G.φ · b) (G.mulLeftInv c),
         = b             : G.oneMul b

  hott theorem mulCancelRight {a b c : G.carrier} (h : a * c = b * c) :=
  calc a = a * e         : Id.inv (G.mulOne a),
         = a * (c * c⁻¹) : ap (G.φ a) (Id.inv (mulRightInv c)),
         = (a * c) * c⁻¹ : Id.inv (G.mulAssoc _ _ _),
         = (b * c) * c⁻¹ : ap (G.φ · c⁻¹) h,
         = b * (c * c⁻¹) : G.mulAssoc _ _ _,
         = b * e         : ap (G.φ b) (mulRightInv c),
         = b             : G.mulOne b

  hott corollary unitInv : e = e⁻¹ :=
  Id.inv (mulRightInv e) ⬝ G.oneMul e⁻¹

  hott corollary unitSqr : e = e * e :=
  Id.inv (G.oneMul e)

  hott proposition unitCommutes (x : G.carrier) : e * x = x * e :=
  (G.oneMul x) ⬝ (G.mulOne x).inv

  hott proposition unitCommutesInv (x : G.carrier) : x * e = e * x :=
  (unitCommutes x).inv

  hott theorem invExplode (x y : G.carrier) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
  invEqOfMulEqOne
    (calc (x * y) * (y⁻¹ * x⁻¹)
        = ((x * y) * y⁻¹) * x⁻¹ : Id.inv (G.mulAssoc _ _ _),
        = (x * (y * y⁻¹)) * x⁻¹ : ap (G.φ · x⁻¹) (G.mulAssoc _ _ _),
        = (x * e) * x⁻¹         : ap (λ z, (x * z) * x⁻¹) (mulRightInv _),
        = x * x⁻¹               : ap (G.φ · x⁻¹) (G.mulOne x),
        = e                     : mulRightInv _)

  hott lemma sqrUnit {x : G.carrier} (p : x * x = e) :=
  calc x = x * e         : Id.inv (G.mulOne x),
         = x * (x * x⁻¹) : ap (G.φ x) (Id.inv (mulRightInv x)),
         = (x * x) * x⁻¹ : Id.inv (G.mulAssoc x x x⁻¹),
         = e * x⁻¹       : ap (G.φ · x⁻¹) p,
         = x⁻¹           : G.oneMul x⁻¹

  hott lemma sqrUnitImplsAbelian (H : Π x, x * x = e) : G.isCommutative :=
  begin
    intros x y; have F := λ x, sqrUnit (H x); apply calc
      x * y = x⁻¹ * y⁻¹ : bimap G.φ (F x) (F y),
            = (y * x)⁻¹ : Id.inv (invExplode y x),
            = y * x     : Id.inv (F _)
  end

  local infix:70 (priority := high) " ^ " => conjugate (G := G)
  local infix:70 (priority := high) " / " => rightDiv (G := G)

  hott lemma eqOfDivEq {x y : G.carrier}
    (h : @leftDiv G x y = e) : x = y :=
  Id.inv (invInv x) ⬝ (invEqOfMulEqOne h)

  hott lemma eqOfRdivEq {x y : G.carrier} (h : x / y = e) : x = y :=
  invInj (invEqOfMulEqOne h)

  hott lemma cancelLeft (a b : G.carrier) :=
  calc a = a * e         : Id.inv (G.mulOne a),
         = a * (b⁻¹ * b) : ap (G.φ a) (Id.inv (G.mulLeftInv b)),
         = (a * b⁻¹) * b : Id.inv (G.mulAssoc a b⁻¹ b)

  hott lemma cancelRight (a b : G.carrier) :=
  calc a = a * e         : Id.inv (G.mulOne a),
         = a * (b * b⁻¹) : ap (G.φ a) (Id.inv (mulRightInv b)),
         = (a * b) * b⁻¹ : Id.inv (G.mulAssoc a b b⁻¹)

  hott lemma revCancelLeft (a b : G.carrier) :=
  calc b = e * b         : Id.inv (G.oneMul b),
         = (a⁻¹ * a) * b : ap (G.φ · b) (Id.inv (G.mulLeftInv a)),
         = a⁻¹ * (a * b) : G.mulAssoc a⁻¹ a b

  hott lemma revCancelRight (a b : G.carrier) :=
  calc b = e * b         : Id.inv (G.oneMul b),
         = (a * a⁻¹) * b : ap (G.φ · b) (Id.inv (mulRightInv a)),
         = a * (a⁻¹ * b) : G.mulAssoc a a⁻¹ b

  hott lemma commImplConj {x y : G.carrier} (p : x * y = y * x) : x = x ^ y :=
  calc x = e * x         : Id.inv (G.oneMul x),
         = (y⁻¹ * y) * x : ap (G.φ · x) (Id.inv (G.mulLeftInv y)),
         = y⁻¹ * (y * x) : G.mulAssoc y⁻¹ y x,
         = y⁻¹ * (x * y) : ap (G.φ y⁻¹) (Id.inv p),
         = (y⁻¹ * x) * y : Id.inv (G.mulAssoc y⁻¹ x y),
         = x ^ y         : Id.refl

  hott lemma invEqOfMulRevEqOne {x y : G.carrier} (h : y * x = e) : x⁻¹ = y :=
  begin
    transitivity; apply eqInvOfMulEqOne (y := y⁻¹);
    transitivity; symmetry; apply invExplode;
    transitivity; apply ap G.ι; exact h;
    apply Id.inv unitInv; apply invInv
  end

  hott lemma isLeftInvertibleContr : contr (G.1.isLeftInvertible G.e) :=
  begin
    existsi ⟨G.ι, G.mulLeftInv⟩; intro w; fapply Sigma.prod;
    { fapply Theorems.funext; intro; symmetry;
      apply eqInvOfMulEqOne; apply w.2 };
    { apply piProp; intro; apply G.hset }
  end

  hott lemma isLeftInvertibleProp : prop (G.1.isLeftInvertible G.e) :=
  contrImplProp isLeftInvertibleContr

  hott lemma isLeftUnitalContr : contr G.1.isLeftUnital :=
  begin
    existsi ⟨G.e, G.oneMul⟩; intro w; fapply Sigma.prod;
    { symmetry; apply leftUnitUniq; apply w.2 };
    { apply piProp; intro; apply G.hset }
  end

  hott corollary isLeftUnitalProp : prop G.1.isLeftUnital :=
  contrImplProp isLeftUnitalContr

  hott theorem isGroupProp : prop G.1.isGroup :=
  begin
    apply productProp; apply G.1.assocProp;
    apply sigProp; apply G.isLeftUnitalProp; intro H;
    apply transport (λ g, prop (G.1.isLeftInvertible g));
    symmetry; apply leftUnitUniq; intro;
    apply H.2; apply isLeftInvertibleProp
  end

  hott corollary isGroupPropMagma (M : Magma) : prop M.isGroup :=
  begin apply lemProp; intro H; apply @isGroupProp ⟨M, H⟩ end

  hott definition commutator (x y : G.carrier) := (x * y) * (x⁻¹ * y⁻¹)

  hott lemma commutes {x y : G.carrier} (p : commutator x y = e) : x * y = y * x :=
  begin
    symmetry; transitivity; { symmetry; apply invInv };
    transitivity; apply ap; apply invExplode;
    symmetry; apply eqInvOfMulEqOne; exact p
  end

  hott lemma commutatorOverInv (x y : G.carrier) : (commutator x y)⁻¹ = commutator y x :=
  begin
    transitivity; apply invExplode;
    transitivity; apply ap; apply invExplode;
    apply ap (λ z, z * (y⁻¹ * x⁻¹)); transitivity; apply invExplode;
    transitivity; apply ap; apply invInv;
    apply ap (G.φ · x); apply invInv
  end

  hott definition ldiv (φ : G.subgroup) := λ x y, @leftDiv G x y ∈ φ.set
  hott definition rdiv (φ : G.subgroup) := λ x y, (x / y) ∈ φ.set

  hott lemma invMulInv (x y : G.carrier) :=
  calc (x⁻¹ * y)⁻¹ = y⁻¹ * x⁻¹⁻¹ : invExplode _ _,
                   = y⁻¹ * x     : ap (G.φ y⁻¹) (invInv x)

  hott lemma mulInvInv (x y : G.carrier) :=
  calc (x * y⁻¹)⁻¹ = y⁻¹⁻¹ * x⁻¹ : invExplode _ _,
                   = y * x⁻¹     : ap (G.φ · x⁻¹) (invInv y)

  hott lemma divByUnit (x : G.carrier) : x / e = x :=
  begin change _ * _ = _; transitivity; apply ap; symmetry; apply unitInv; apply G.mulOne end

  hott lemma ldivByUnit (x : G.carrier) : leftDiv x e = x⁻¹ :=
  by apply G.mulOne

  hott lemma chainLdiv (x y z : G.carrier) :=
  calc (leftDiv x y) * (leftDiv y z)
     = (x⁻¹ * y) * (y⁻¹ * z) : Id.refl,
     = x⁻¹ * (y * (y⁻¹ * z)) : G.mulAssoc x⁻¹ y (y⁻¹ * z),
     = x⁻¹ * ((y * y⁻¹) * z) : ap (G.φ x⁻¹) (Id.inv (G.mulAssoc y y⁻¹ z)),
     = x⁻¹ * (e * z)         : ap (λ g, x⁻¹ * (g * z)) (mulRightInv _),
     = leftDiv x z           : ap (G.φ x⁻¹) (G.oneMul z)

  hott lemma chainRdiv (x y z : G.carrier) :=
  calc (x / y) * (y / z)
     = (x * y⁻¹) * (y * z⁻¹) : Id.refl,
     = x * (y⁻¹ * (y * z⁻¹)) : G.mulAssoc x y⁻¹ (y * z⁻¹),
     = x * ((y⁻¹ * y) * z⁻¹) : ap (G.φ x) (Id.inv (G.mulAssoc y⁻¹ y z⁻¹)),
     = x * (e * z⁻¹)         : ap (λ g, x * (g * z⁻¹)) (G.mulLeftInv _),
     = x / z                 : ap (G.φ x) (G.oneMul z⁻¹)

  hott lemma conjugate.idem (x : G.carrier) :=
  calc conjugate x x = G.φ G.e x : ap (G.φ · x) (G.mulLeftInv x),
                     = x         : G.oneMul x

  hott lemma conjugate.eq {x y : G.carrier} (p : conjugate x y = y) : x = y :=
  begin
    symmetry; apply eqOfDivEq; fapply mulCancelRight; exact y;
    transitivity; exact p; symmetry; apply G.oneMul
  end

  hott lemma conjugate.comm {x y : G.carrier} (p : conjugate x y = x) : G.φ x y = G.φ y x :=
  begin
    fapply mulCancelLeft; exact G.ι y;
    transitivity; { symmetry; apply G.mulAssoc };
    transitivity; exact p; transitivity;
    { transitivity; symmetry; apply G.oneMul;
      apply ap (G.φ · x); symmetry; apply G.mulLeftInv y };
    apply G.mulAssoc
  end

  section
    variable {H K : Group}

    hott definition homoMul (φ : Hom H K) (x y : H.carrier) :
      φ.1 (H.φ x y) = K.φ (φ.1 x) (φ.1 y) :=
    φ.2.1 ★ (x, y, ★)
  end

  section
    variable {H : Group}
    local infixl:70 " ∗ " => H.φ

    hott lemma homoRespectsUnit {φ : G.carrier → H.carrier}
      (p : Π a b, φ (a * b) = φ a ∗ φ b) : φ G.e = H.e :=
    begin
      apply unitOfSqr; apply calc
        H.φ (φ e) (φ e) = φ (G.e * G.e) : Id.inv (p G.e G.e),
                        = φ G.e         : ap φ (Id.inv unitSqr)
    end

    hott lemma homoRespectsInv {φ : G.carrier → H.carrier}
      (p : Π a b, φ (a * b) = φ a ∗ φ b) (x : G.carrier) : φ x⁻¹ = H.ι (φ x) :=
    calc φ x⁻¹ = φ x⁻¹ ∗ H.e               : Id.inv (H.mulOne (φ x⁻¹)),
               = φ x⁻¹ ∗ (φ x ∗ H.ι (φ x)) : ap (H.φ (φ x⁻¹)) (Id.inv (mulRightInv (φ x))),
               = φ x⁻¹ ∗ φ x ∗ H.ι (φ x)   : Id.inv (H.mulAssoc _ _ _),
               = φ (x⁻¹ * x) ∗ H.ι (φ x)   : ap (H.φ · (H.ι (φ x))) (Id.inv (p x⁻¹ x)),
               = φ G.e ∗ H.ι (φ x)         : ap (λ y, φ y ∗ H.ι (φ x)) (G.mulLeftInv x),
               = H.e ∗ H.ι (φ x)           : ap (H.φ · (H.ι (φ x))) (homoRespectsUnit p),
               = H.ι (φ x)                 : H.oneMul (H.ι (φ x))

    attribute [irreducible] homoRespectsUnit homoRespectsInv

    hott definition mkhomo (φ : G.carrier → H.carrier)
      (p : Π a b, φ (a * b) = φ a ∗ φ b) : Hom G H :=
    ⟨φ, (λ _ (x, y, _), p x y, λ z, nomatch z)⟩

    hott definition mkiso (φ : G.carrier → H.carrier)
      (p : Π a b, φ (a * b) = φ a ∗ φ b) (q : biinv φ) : G ≅ H :=
    ⟨φ, ((mkhomo φ p).snd, q)⟩

    hott definition homoUnit (φ : Hom G H) : φ.1 G.e = H.e :=
    homoRespectsUnit (homoMul φ)

    hott definition homoInv (φ : Hom G H) : Π x, φ.1 (G.ι x) = H.ι (φ.1 x) :=
    homoRespectsInv (homoMul φ)

    hott definition isoUnit (φ : G ≅ H) : φ.fst G.e = H.e :=
    homoUnit φ.hom

    hott definition isoInv (φ : G ≅ H) : Π x, φ.fst x⁻¹ = H.ι (φ.fst x) :=
    homoInv φ.hom

    hott definition isoMul (φ : G ≅ H) : Π x y, φ.fst (x * y) = φ.fst x ∗ φ.fst y :=
    homoMul φ.hom

    hott definition homoRespectsDiv (φ : Hom G H) (x y : G.carrier) :
      φ.1 (x / y) = rightDiv (φ.1 x) (φ.1 y) :=
    calc φ.1 (x / y) = φ.1 x ∗ φ.1 y⁻¹     : homoMul φ x y⁻¹,
                     = φ.1 x ∗ H.ι (φ.1 y) : ap (H.φ (φ.1 x)) (homoInv φ y)

    attribute [irreducible] homoRespectsDiv

    hott definition Homo.zero : Hom G H :=
    mkhomo (λ _, H.e) (λ _ _, Id.inv (H.oneMul H.e))

    hott instance : OfNat (Hom G H) Nat.zero := ⟨Homo.zero⟩
    hott instance : OfNat (Algebra.Hom G.1 H.1) Nat.zero := ⟨Homo.zero⟩
  end

  section
    variable (G H : Abelian)

    hott instance : OfNat (Abelian.Hom G H) Nat.zero := ⟨@Homo.zero G.group H.group⟩
    hott instance : OfNat (Algebra.Hom G.1 H.1) Nat.zero := ⟨@Homo.zero G.group H.group⟩
  end

  hott lemma Homo.set {G H : Group} : Structures.hset (Hom G H) :=
  Algebra.Hom.hset

  -- Of course, this can be done by induction
  hott lemma Homo.ofPath {G H : Group} (φ : G.carrier = H.carrier) (p : G.φ =[λ G, G → G → G, φ] H.φ) : Hom G H :=
  begin
    fapply mkhomo; exact @transport _ (λ G, G) G.carrier H.carrier φ;
    intros a b; transitivity; apply ap; apply bimap;
    iterate 2 { symmetry; apply @Equiv.transportForwardAndBack _ (λ G, G) _ _ φ };
    transitivity; symmetry; apply Equiv.transportOverOperationPointwise G.φ;
    apply HITs.Interval.happly; apply HITs.Interval.happly; exact p
  end

  hott lemma Iso.ofPath {G H : Group} (φ : G.carrier = H.carrier) (p : G.φ =[λ G, G → G → G, φ] H.φ) : G ≅ H :=
  begin
    fapply Iso.ofHom; apply Homo.ofPath φ p;
    apply Prod.mk <;> existsi @transport _ (λ G, G) H.carrier G.carrier (Id.inv φ) <;> intro x;
    dsimp; apply Equiv.transportForwardAndBack;
    apply @Equiv.transportBackAndForward _ (λ G, G) _ _ φ
  end

  hott corollary Iso.ua {G H : Group} : (G ≅ H) → G = H :=
  begin intro φ; fapply Sigma.prod; apply Alg.ua φ; apply isGroupProp end

  -- This statement in fact says that two groups are equal
  -- if their multiplication tables are equal
  hott theorem table {G H : Group} (φ : G.carrier = H.carrier)
    (p : G.φ =[λ G, G → G → G, φ] H.φ) : G = H :=
  Iso.ua (Iso.ofPath φ p)

  section
    variable {H : Group}
    hott definition Op.mul := λ x y, H.φ y x
    hott definition Op.inv := H.ι
    hott definition Op.one := H.e
  end
end Group

namespace Group
  hott definition Op (G : Group) : Group :=
  @Group.intro G.carrier G.hset Op.mul Op.inv Op.one
    (λ a b c, (G.mulAssoc c b a).inv) G.mulOne G.mulRightInv

  postfix:max "ᵒᵖ" => Op

  variable {G : Group}

  hott definition Op.univ : Hom G Gᵒᵖ :=
  mkhomo G.ι invExplode

  hott definition Op.iso : G ≅ Gᵒᵖ :=
  begin
    fapply mkiso; exact G.ι; apply invExplode;
    apply Prod.mk <;> existsi G.ι <;>
    intro <;> apply invInv
  end
end Group

namespace Group
  hott definition Z₁.mul : 𝟏 → 𝟏 → 𝟏 := λ _ _, ★
  hott definition Z₁.inv : 𝟏 → 𝟏     := λ _, ★

  hott instance Z₁.Mul : Mul 𝟏 := ⟨Z₁.mul⟩

  hott definition Z₁ : Group :=
  @Group.intro 𝟏 unitIsSet Z₁.mul Z₁.inv ★ (λ _ _ _, idp _) (λ _, idp _) (λ _, idp _)

  hott definition Z₂.carrier := 𝟐

  hott definition Z₂.mul : 𝟐 → 𝟐 → 𝟐
  | false => idfun
  | true  => not

  hott definition Z₂.inv := @idfun Z₂.carrier

  hott definition Z₂.set : Structures.hset Z₂.carrier :=
  Structures.Hedberg (λ | false, false => Sum.inl Id.refl
                        | true,  false => Sum.inr (ffNeqTt ∘ Id.inv)
                        | false, true  => Sum.inr ffNeqTt
                        | true,  true  => Sum.inl Id.refl)

  hott definition Z₂ : Group :=
  @Group.intro Z₂.carrier Z₂.set Z₂.mul Z₂.inv false
    (begin
      intros a b c;
      induction a using Bool.casesOn <;>
      induction b using Bool.casesOn <;>
      induction c using Bool.casesOn <;>
      reflexivity
    end)
    (begin intro b; induction b using Bool.casesOn <;> reflexivity end)
    (begin intro b; induction b using Bool.casesOn <;> reflexivity end)
end Group

end GroundZero.Algebra
