import GroundZero.HITs.Circle

open GroundZero.Theorems.Functions (injective)
open GroundZero.Theorems (funext)
open GroundZero.Types.Equiv
open GroundZero.HITs.Circle
open GroundZero.Structures
open GroundZero.Types.Id
open GroundZero.Types
open GroundZero.Proto
open GroundZero

/-
  Homotopical Reals R.
  * HoTT 8.1.5
-/

namespace GroundZero.HITs
universe u v w

inductive Reals.rel : ℤ → ℤ → Type
| glue (x : ℤ) : rel x (Integer.succ x)

hott definition Reals := Quotient Reals.rel

hott definition R := Reals

namespace Reals
  hott definition elem : ℤ → R := Quotient.elem

  hott definition glue (z : ℤ) : elem z = elem (Integer.succ z) :=
  Quotient.line (rel.glue z)

  hott definition indρ {C : R → Type u} (cz : Π x, C (elem x))
    (sz : Π z, cz z =[glue z] cz (Integer.succ z))
    (x y : ℤ) (ρ : rel x y) : cz x =[Quotient.line ρ] cz y :=
  begin induction ρ using rel.casesOn; apply sz end

  hott definition ind {C : R → Type u} (cz : Π x, C (elem x))
    (sz : Π z, cz z =[glue z] cz (Integer.succ z)) (u : R) : C u :=
  Quotient.ind cz (indρ cz sz) u

  attribute [induction_eliminator] ind

  hott definition indβrule {C : R → Type u}
    (cz : Π x, C (elem x)) (sz : Π z, cz z =[glue z] cz (Integer.succ z))
    (z : ℤ) : Equiv.apd (ind cz sz) (glue z) = sz z :=
  @Quotient.indβrule _ _ C cz (indρ cz sz) _ _ (rel.glue z)

  hott definition rec {A : Type u} (cz : ℤ → A)
    (sz : Π z, cz z = cz (Integer.succ z)) : R → A :=
  ind cz (λ x, Equiv.pathoverOfEq (glue x) (sz x))

  hott definition recβrule {A : Type u} (cz : ℤ → A)
    (sz : Π z, cz z = cz (Integer.succ z)) (z : ℤ) :
    ap (rec cz sz) (glue z) = sz z :=
  begin
    apply Equiv.pathoverOfEqInj (glue z); transitivity;
    symmetry; apply Equiv.apdOverConstantFamily;
    transitivity; apply indβrule; reflexivity
  end

  hott definition positive : Π n, elem 0 = elem (Integer.pos n)
  | Nat.zero   => idp (elem 0)
  | Nat.succ n => positive n ⬝ glue (Integer.pos n)

  hott definition negative : Π n, elem 0 = elem (Integer.neg n)
  | Nat.zero   => (glue (Integer.neg 0))⁻¹
  | Nat.succ n => negative n ⬝ (glue (Integer.neg (n + 1)))⁻¹

  hott definition center : Π z, elem 0 = elem z
  | Integer.pos n => positive n
  | Integer.neg n => negative n

  hott definition vect (u v : ℤ) : elem u = elem v :=
  (center u)⁻¹ ⬝ center v

  hott theorem contractible : contr R :=
  ⟨elem 0, @ind (elem 0 = ·) center (begin
    intro z; change _ = _; transitivity;
    apply Equiv.transportComposition; match z with
    | Integer.pos _ => reflexivity;
    | Integer.neg n => _;
    induction n using Nat.casesOn; apply Id.invComp;
    { transitivity; symmetry; apply Id.assoc;
      transitivity; apply ap; apply Id.invComp;
      apply Id.rid }
  end)⟩

  hott definition dist : Π (u v : R), u = v :=
  Structures.contrImplProp contractible

  hott definition lift (f : ℤ → ℤ) : R → R :=
  rec (elem ∘ f) (λ _, dist _ _)

  hott instance (n : ℕ) : OfNat R n := ⟨elem (Integer.pos n)⟩

  section
    variable {A : Type⁎} (H : prop A.space)
    variable (φ : Map⁎ A ⟨S¹, base⟩)

    hott lemma helixOverHomo (x : A.1) : helix (φ.ap x) = ℤ :=
    begin
      transitivity; apply ap (helix ∘ φ.ap);
      apply H x A.point; change _ = helix base;
      apply ap helix; apply φ.id
    end

    hott lemma fibOfHomo (x : S¹) :=
    calc fib φ.ap x ≃ Σ (z : A.1), φ.ap z = x       : Equiv.ideqv (fib φ.ap x),
                    = Σ (z : A.1), φ.ap A.point = x : ap Sigma (funext (λ z, ap (φ.ap · = x) (H z A.point))),
                    = Σ (z : A.1), base = x         : ap Sigma (funext (λ _, ap (· = x) φ.id)),
                    = Σ (z : A.1), helix x          : ap Sigma (funext (λ _, GroundZero.ua (Circle.family x))),
                    ≃ A.1 × (helix x)               : Sigma.const A.1 (helix x),
                    ≃ 𝟏 × (helix x)                 : productEquiv₃ (contrEquivUnit.{_, 0} ⟨A.point, H A.point⟩) (Equiv.ideqv (helix x)),
                    ≃ helix x                       : prodUnitEquiv (helix x)

    hott corollary kerOfHomo : fib φ.ap base ≃ ℤ :=
    fibOfHomo H φ base
  end

  /-
            ≃
       S¹ ←–––– R/τℤ
       ↑          ↑
   eⁱ⁻ |          |
       |          |
       R ════════ R
  -/
  hott definition cis : R → S¹ := rec (λ _, base) (λ _, loop)

  hott theorem Euler : fib cis base ≃ ℤ :=
  @kerOfHomo _ ⟨R, 0⟩ dist ⟨cis, idp base⟩

  -- Another (more tricky) proof, but it does not use R contractibility
  hott lemma helixOverCis (x : R) : helix (cis x) = ℤ :=
  begin
    induction x;
    { case cz x => apply (Integer.shift x)⁻¹ };
    { case sz z =>
      change _ = _; let p := Integer.shift z; apply calc
            Equiv.transport (λ x, helix (cis x) = ℤ) (glue z) (Integer.shift z)⁻¹
          = @ap R Type _ _ (helix ∘ cis) (glue z)⁻¹ ⬝ (Integer.shift z)⁻¹
          : Equiv.transportOverContrMap _ _ _,
          = (ap (helix ∘ cis) (glue z))⁻¹ ⬝ (Integer.shift z)⁻¹
          : ap (· ⬝ p⁻¹) (Id.mapInv _ _),
          = (ap helix (ap cis (glue z)))⁻¹ ⬝ (Integer.shift z)⁻¹
          : ap (·⁻¹ ⬝ p⁻¹) (Equiv.mapOverComp _ _ _),
          = (ap helix loop)⁻¹ ⬝ (Integer.shift z)⁻¹
          : begin apply ap (·⁻¹ ⬝ p⁻¹); apply ap; apply recβrule end,
          = Integer.succPath⁻¹ ⬝ (Integer.shift z)⁻¹
          : begin apply ap (·⁻¹ ⬝ p⁻¹); apply Circle.recβrule₂ end,
          = (Integer.shift z ⬝ Integer.succPath)⁻¹
          : (Id.explodeInv _ _)⁻¹,
          = (Integer.shift (Integer.succ z))⁻¹
          : ap _ (Integer.shiftComp _)
    }
  end

  hott lemma phiEqvBaseImplContr {A : Type u} {x : A}
    (H : Π (φ : A → S¹), φ x = base) : contr S¹ :=
  ⟨base, λ y, (H (λ _, y))⁻¹⟩

  hott lemma phiNeqBaseImplFalse {A : Type u} {x : A} (φ : A → S¹) : ¬¬(φ x = base) :=
  begin induction φ x; intro p; apply p; reflexivity; apply implProp; apply emptyIsProp end

  hott lemma lemInfImplDnegInf (H : LEM∞) {A : Type u} (G : ¬¬A) : A :=
  match H A with
  | Sum.inl x => x
  | Sum.inr y => explode (G y)

  hott remark circleNotHset : ¬(hset S¹) :=
  begin intro H; apply Circle.loopNeqRefl; apply H end

  hott proposition lemInfDisproved : ¬LEM∞ :=
  begin
    intro H; apply circleNotHset; apply propIsSet; apply contrImplProp;
    apply phiEqvBaseImplContr; intro φ; apply lemInfImplDnegInf H;
    apply phiNeqBaseImplFalse φ; exact R; exact 0
  end
end Reals

end GroundZero.HITs
