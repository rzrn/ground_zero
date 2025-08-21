import GroundZero.Theorems.Univalence
import GroundZero.HITs.Suspension
import GroundZero.Types.Integer

open GroundZero.HITs.Interval
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types.Id
open GroundZero.Types
open GroundZero.Proto

/-
  Circle S¹ as Higher Inductive Type.
  * HoTT 6.4

  π₁(S¹) = ℤ proof.
  * HoTT 8.1
-/

namespace GroundZero
namespace HITs

universe u v w

section
  open Suspension (north south rec ind)

  hott lemma suspEmpty : ∑ 𝟎 ≃ 𝟐 :=
  Equiv.intro (rec false true explode)
              (λ | false => north | true => south)
              (ind (idp north) (idp south) (λ ε, nomatch ε))
              (λ | false => idp false | true => idp true)
end

namespace Loop
  variable {A : Type u} {a : A}

  hott definition power (p : a = a) : ℤ → a = a :=
  Integer.recsp (idp a) (· ⬝ p) (· ⬝ p⁻¹)

  hott corollary powerComp (p : a = a) (z : ℤ) : power p z ⬝ p = power p (Integer.succ z) :=
  begin symmetry; apply Integer.recspβ₂; intro; apply Id.cancelInvComp end

  hott corollary powerCompPred (p : a = a) (z : ℤ) : power p z ⬝ p⁻¹ = power p (Integer.pred z) :=
  begin symmetry; apply Integer.recspβ₃; intro; apply Id.cancelCompInv end

  hott lemma compPowerPos (p : a = a) : Π n, p ⬝ power p (Integer.pos n) = power p (Integer.succ (Integer.pos n))
  | Nat.zero   => Id.rid _
  | Nat.succ n => Id.assoc _ _ _ ⬝ ap (· ⬝ p) (compPowerPos p n)

  hott lemma compPowerNeg (p : a = a) : Π n, p ⬝ power p (Integer.neg n) = power p (Integer.succ (Integer.neg n))
  | Nat.zero   => Id.compInv _
  | Nat.succ n =>
  begin
    transitivity; apply Id.assoc;
    symmetry; apply Equiv.invCompRewrite;
    symmetry; transitivity; apply compPowerNeg p n;
    symmetry; apply powerComp
  end

  hott lemma compPower (p : a = a) : Π z, p ⬝ power p z = power p (Integer.succ z)
  | .neg n => compPowerNeg p n
  | .pos m => compPowerPos p m

  hott corollary compPowerPred (p : a = a) (z : ℤ) : p⁻¹ ⬝ power p z = power p (Integer.pred z) :=
  Equiv.rewriteComp (compPower p _ ⬝ ap (power p) (Integer.succPred z))⁻¹

  hott corollary compPowerComm (p : a = a) (z : ℤ) : p ⬝ power p z = power p z ⬝ p :=
  compPower p z ⬝ (powerComp p z)⁻¹

  hott corollary invCompPowerComm (p : a = a) (z : ℤ) : p⁻¹ ⬝ power p z = power p z ⬝ p⁻¹ :=
  compPowerPred p z ⬝ (powerCompPred p z)⁻¹

  hott theorem powerComm (p : a = a) (x y : ℤ) : power p x ⬝ power p y = power p y ⬝ power p x :=
  begin
    fapply @Integer.indsp (λ x, Π y, power p x ⬝ power p y = power p y ⬝ power p x) _ _ _ x <;> clear x;
    { intro y; symmetry; apply Id.rid };
    { intros x ih y; transitivity; apply ap (· ⬝ power p y);
      symmetry; apply compPower;
      transitivity; symmetry; apply Id.assoc;
      transitivity; apply ap; apply ih;
      transitivity; apply Id.assoc;
      transitivity; apply ap (· ⬝ power p x); apply compPowerComm;
      transitivity; symmetry; apply Id.assoc;
      apply ap; apply compPower };
    { intros x ih y; transitivity; apply ap (· ⬝ power p y);
      symmetry; apply compPowerPred;
      transitivity; symmetry; apply Id.assoc;
      transitivity; apply ap; apply ih;
      transitivity; apply Id.assoc;
      transitivity; apply ap (· ⬝ power p x);
      apply invCompPowerComm;
      transitivity; symmetry; apply Id.assoc;
      apply ap; apply compPowerPred }
  end
end Loop

hott definition S : ℕ → Type
| Nat.zero   => 𝟐
| Nat.succ n => ∑ (S n)

macro:max "S" noWs n:superscript : term => do `(GroundZero.HITs.S $(← Meta.Notation.parseSuperscript n))

hott instance (n : ℕ) : isPointed Sⁿ :=
⟨match n with
 | Nat.zero   => false
 | Nat.succ _ => Suspension.north⟩

macro:max "S" : term => `(GroundZero.HITs.S)

section
  open Lean Lean.PrettyPrinter.Delaborator

  @[delab app.GroundZero.HITs.S]
  def delabHigherSphere : Delab := whenPPOption Lean.getPPNotation do {
    let ε ← SubExpr.getExpr; guard (ε.isAppOfArity' `GroundZero.HITs.S 1);

    let dim ← SubExpr.withNaryArg 0 delab;
    match dim.raw.isNatLit? with
    | some n => `(S$(← Meta.Notation.mkSupNumeral dim n))
    | none   => `(S $dim)
  }
end

hott abbreviation Circle := S¹

namespace Circle
  -- https://github.com/leanprover/lean2/blob/master/hott/homotopy/Circle.hlean

  open GroundZero.HITs.Suspension (north south merid)

  hott abbreviation base₁ : S¹ := north
  hott abbreviation base₂ : S¹ := south

  hott definition seg₁ : base₁ = base₂ := merid false
  hott definition seg₂ : base₁ = base₂ := merid true

  hott definition ind₂ {B : S¹ → Type u} (b₁ : B base₁) (b₂ : B base₂)
    (ℓ₁ : b₁ =[seg₁] b₂) (ℓ₂ : b₁ =[seg₂] b₂) : Π x, B x :=
  Suspension.ind b₁ b₂ (λ | false => ℓ₁ | true => ℓ₂)

  hott definition base : S¹ := base₁
  hott definition loop : base = base := seg₂ ⬝ seg₁⁻¹

  hott abbreviation loop₁ : base₁ = base₁ := loop

  hott definition loop₂ : base₂ = base₂ := seg₁⁻¹ ⬝ seg₂

  hott definition rec {B : Type u} (b : B) (ℓ : b = b) : S¹ → B :=
  Suspension.rec b b (λ | false => idp b | true => ℓ)

  hott definition recβrule₁ {B : Type u} (b : B) (ℓ : b = b) : rec b ℓ base = b :=
  idp b

  hott definition recβrule₂ {B : Type u} (b : B) (ℓ : b = b) :=
  calc ap (rec b ℓ) loop
     = ap (rec b ℓ) seg₂ ⬝ ap (rec b ℓ) seg₁⁻¹   : Equiv.mapFunctoriality _,
     = ap (rec b ℓ) seg₂ ⬝ (ap (rec b ℓ) seg₁)⁻¹ : ap (_ ⬝ ·) (Id.mapInv _ _),
     = ℓ ⬝ (idp b)⁻¹                             : bimap (· ⬝ ·⁻¹) (Suspension.recβrule _ _ _ _) (Suspension.recβrule _ _ _ _),
     = ℓ                                         : Id.rid _

  hott definition recβrule₃ {B : Type u} (b : B) (ℓ : b = b) :=
  calc ap (rec b ℓ) loop⁻¹
    = (ap (rec b ℓ) loop)⁻¹ : Id.mapInv _ _,
    = ℓ⁻¹                   : ap Id.inv (recβrule₂ _ _)

  hott definition ind {B : S¹ → Type u} (b : B base) (ℓ : b =[loop] b) : Π (x : S¹), B x :=
  ind₂ b (transport B seg₁ b) (idp _) (depPathTransSymm ℓ)

  attribute [induction_eliminator] ind

  hott definition indβrule₁ {B : S¹ → Type u} (b : B base) (ℓ : b =[loop] b) : ind b ℓ base = b :=
  idp b

  hott definition indβrule₂ {B : S¹ → Type u} (b : B base) (ℓ : b =[loop] b) : apd (ind b ℓ) loop = ℓ :=
  begin
    dsimp [ind, ind₂];
    transitivity; apply apdFunctoriality;
    transitivity; apply bimap depTrans; apply Suspension.indβrule;
    transitivity; apply apdInv; apply ap;
    apply Suspension.indβrule; apply depPathTransSymmCoh
  end

  hott definition indΩ {B : S¹ → Type u} (b : B base) (H : Π x, prop (B x)) : Π x, B x :=
  begin fapply ind; exact b; apply H end

  hott definition indΩ₂ {B : S¹ → S¹ → Type u} (b : B base base) (H : Π x y, prop (B x y)) : Π x y, B x y :=
  begin
    fapply indΩ; fapply indΩ; exact b; intro;
    apply H; intro; apply piProp; apply H
  end

  hott lemma loopEqReflImplsUip {A : Type u} (H : loop = idp base) : K A :=
  begin
    intros a p; transitivity;
    symmetry; apply Circle.recβrule₂ a p;
    change _ = ap (rec a p) (idp _);
    apply ap; apply H
  end

  hott theorem loopNeqRefl : ¬(loop = idp base) :=
  begin
    intro H; apply universeNotASet;
    intros A B p q; apply (KIffSet Type).left;
    apply loopEqReflImplsUip; assumption
  end

  hott corollary ineqMerid : ¬(@Id (@Id S¹ base₁ base₂) (merid false) (merid true)) :=
  begin intro ε; apply loopNeqRefl; transitivity; apply ap (_ ⬝ ·⁻¹); apply ε; apply Id.compInv end

  hott lemma constRec {A : Type u} (a : A) : Π z, rec a (idp a) z = a :=
  begin
    fapply ind; reflexivity; apply Id.trans; apply transportOverContrMap;
    transitivity; apply Id.rid; apply recβrule₃
  end

  hott lemma idfunRec : rec base loop ~ idfun :=
  begin
    fapply ind; reflexivity; apply Id.trans; apply Equiv.transportOverHmtpy;
    transitivity; apply bimap; transitivity; apply Id.rid;
    apply recβrule₃; apply idmap; apply Id.invComp
  end

  namespace map
    hott definition trivial    : S¹ → S¹ := rec base (idp base)
    hott definition nontrivial : S¹ → S¹ := rec base loop

    hott statement trivialNotHmtpy : ¬(trivial = id) :=
    begin
      intro p; apply loopNeqRefl; transitivity; symmetry; apply idmap;
      apply transport (λ f, ap f loop = idp (f base)) p; apply Circle.recβrule₂
    end

    hott definition trivialHmtpy : trivial ~ (λ _, base) :=
    by apply constRec

    hott definition nontrivialHmtpy : nontrivial ~ id :=
    by apply idfunRec

    hott statement nontrivialNotHmtpy : ¬(nontrivial = (λ _, base)) :=
    λ p, trivialNotHmtpy (Theorems.funext trivialHmtpy ⬝ p⁻¹ ⬝
                          Theorems.funext nontrivialHmtpy)
  end map

  hott definition succ (l : Ω¹(S¹)) : Ω¹(S¹) := l ⬝ loop
  hott definition pred (l : Ω¹(S¹)) : Ω¹(S¹) := l ⬝ loop⁻¹

  hott abbreviation zero  := idp base
  hott abbreviation one   := succ zero
  hott abbreviation two   := succ one
  hott abbreviation three := succ two
  hott abbreviation four  := succ three

  hott definition helix : S¹ → Type :=
  rec ℤ (ua Integer.succEquiv)

  hott definition power : ℤ → Ω¹(S¹) :=
  Loop.power loop

  hott definition encode (x : S¹) (p : base = x) : helix x :=
  transport helix p (Integer.pos 0)

  hott example : power 2 = loop ⬝ loop :=
  by reflexivity

  hott definition winding : base = base → ℤ := encode base

  hott theorem transportThere (x : ℤ) :=
  calc transport helix loop x
     = transportconst (ap helix loop) x        : Equiv.transportComp id helix loop x,
     = transportconst (ua Integer.succEquiv) x : ap (transportconst · x) (recβrule₂ _ _),
     = Integer.succ x                          : uaβ _ _

  hott theorem transportBack (x : ℤ) :=
  calc transport helix loop⁻¹ x
     = transportconst (ap helix loop⁻¹) x        : Equiv.transportComp id helix loop⁻¹ x,
     = transportconst (ap helix loop)⁻¹ x        : ap (transportconst · x) (Id.mapInv _ _),
     = transportconst (ua Integer.succEquiv)⁻¹ x : ap (transportconst ·⁻¹ x) (recβrule₂ _ _),
     = Integer.pred x                            : uaβrev _ _

  -- An example of two equal dependent pairs with unequal second components.
  -- Note that this example depends on the univalence.
  hott example (z : ℤ) : @Id (Σ x, helix x) ⟨base, z⟩ ⟨base, Integer.succ z⟩ :=
  Sigma.prod loop (transportThere z)

  hott definition decode (x : S¹) : helix x → base = x :=
  begin
    induction x; exact power; apply Theorems.funext; intro x;
    transitivity; apply happly (transportCharacterization power loop) x;
    transitivity; apply transportComposition;
    transitivity; apply ap (power · ⬝ loop); apply transportBack;
    transitivity; apply ap (· ⬝ loop);
    transitivity; symmetry; apply Loop.compPowerPred; apply Loop.invCompPowerComm;
    apply Id.cancelInvComp
  end

  hott lemma decodeEncode (x : S¹) (p : base = x) : decode x (encode x p) = p :=
  begin induction p; reflexivity end

  hott corollary powerOfWinding : power ∘ winding ~ id :=
  decodeEncode base

  hott lemma windingPos : Π n, winding (power (Integer.pos n)) = Integer.pos n
  | Nat.zero   => idp _
  | Nat.succ n => transportcom _ _ _ ⬝ transportThere _ ⬝ ap _ (windingPos n)

  hott lemma windingNeg : Π n, winding (power (Integer.neg n)) = Integer.neg n
  | Nat.zero   => transportBack _
  | Nat.succ n => transportcom _ _ _ ⬝ transportBack _ ⬝ ap _ (windingNeg n)

  hott corollary windingPower : Π z, winding (power z) = z
  | Integer.neg n => windingNeg n
  | Integer.pos n => windingPos n

  hott lemma encodeDecode (x : S¹) : Π c, encode x (decode x c) = c :=
  begin induction x; intro c; apply windingPower; apply Theorems.funext; intro z; apply Integer.set end

  hott lemma family (x : S¹) : (base = x) ≃ helix x :=
  ⟨encode x, (⟨decode x, decodeEncode x⟩, ⟨decode x, encodeDecode x⟩)⟩

  hott theorem fundamentalGroup : Ω¹(S¹) = ℤ := ua (family base)

  hott definition loopHset : hset (base = base) :=
  transport hset fundamentalGroup⁻¹ Integer.set

  hott example : winding (loop ⬝ loop) = 2 := windingPower 2
  hott example : winding loop = 1          := windingPower 1
  hott example : winding loop⁻¹ = -1       := windingPower (Integer.neg 0)

  hott definition rot : Π (x : S¹), x = x :=
  begin
    fapply ind; exact loop; apply Id.trans; apply transportInvCompComp;
    change _ = idp _ ⬝ loop; apply ap (· ⬝ loop); apply Id.invComp
  end

  hott definition μₑ : S¹ → S¹ ≃ S¹ :=
  Circle.rec (ideqv S¹) (Sigma.prod (Theorems.funext rot) (Theorems.Equiv.biinvProp _ _ _))

  hott definition μ (x : S¹) : S¹ → S¹ := (μₑ x).forward

  hott definition μLoop : ap μ loop = Theorems.funext rot :=
  begin
    transitivity; apply mapOverComp;
    transitivity; apply ap; apply recβrule₂;
    apply Sigma.mapFstOverProd
  end

  hott definition turn : S¹ → S¹ := rec base loop
  hott definition inv  : S¹ → S¹ := rec base loop⁻¹

  hott lemma invol (x : S¹) : inv (inv x) = x :=
  let invₚ := @ap S¹ S¹ base base (inv ∘ inv);
  begin
    induction x; reflexivity; apply calc
              transport (λ x, inv (inv x) = x) loop (idp base)
            = invₚ loop⁻¹ ⬝ idp base ⬝ loop   : transportOverInvolution _ _ _,
            = invₚ loop⁻¹ ⬝ (idp base ⬝ loop) : (Id.assoc _ _ _)⁻¹,
            = ap inv (ap inv loop⁻¹) ⬝ loop   : ap (· ⬝ loop) (mapOverComp _ _ _),
            = ap inv (ap inv loop)⁻¹ ⬝ loop   : ap (· ⬝ loop) (ap (ap inv) (Id.mapInv inv loop)),
            = ap inv loop⁻¹⁻¹ ⬝ loop          : @ap Ω¹(S¹) _ _ _ (ap inv ·⁻¹ ⬝ loop) (Circle.recβrule₂ base loop⁻¹),
            = ap inv loop ⬝ loop              : @ap Ω¹(S¹) _ _ _ (ap inv · ⬝ loop) (Id.invInv _),
            = loop⁻¹ ⬝ loop                   : ap (· ⬝ loop) (Circle.recβrule₂ _ _),
            = idp base                        : Id.invComp _
  end

  hott lemma unitLeft (x : S¹) : μ base x = x := idp x

  hott lemma μRight : ap (μ base) loop = loop := Equiv.idmap _

  hott lemma μLeft :=
  calc ap (μ · base) loop
     = happly (ap μ loop) base             : Interval.mapHapply _ _,
     = (happly ∘ Theorems.funext) rot base : ap (λ f, happly f base) μLoop,
     = loop                                : happly (Theorems.happlyFunext _ _ rot) base

  hott lemma unitRight (x : S¹) : μ x base = x :=
  begin
    induction x; reflexivity; change _ = _;
    transitivity; apply transportOverInvolution (μ · base);
    transitivity; apply ap (· ⬝ idp base ⬝ loop);
    transitivity; apply Id.mapInv; apply ap;
    apply μLeft; transitivity; apply ap (· ⬝ loop);
    apply Id.rid; apply Id.invComp
  end

  hott lemma μLeftApLem {x : S¹} (p : base = x) :
    ap (μ · base) p = transport (base = ·) (unitRight x)⁻¹ p :=
  begin induction p; reflexivity end

  hott lemma μLeftAp  (p : Ω¹(S¹)) : ap (μ · base) p = p := μLeftApLem p
  hott lemma μRightAp (p : Ω¹(S¹)) : ap (μ base)   p = p := Equiv.idmap p

  hott corollary unitComm (x : S¹) : μ base x = μ x base := (unitRight x)⁻¹

  hott theorem mulInv (x : S¹) : base = μ x (inv x) :=
  begin
    induction x; exact loop; change _ = _;
    transitivity; apply transportComp (base = ·) (AS μ inv) loop;
    transitivity; apply transportComposition;
    transitivity; apply ap; apply Equiv.mapOverAS;
    transitivity; apply ap; apply ap; apply Circle.recβrule₂;
    transitivity; apply ap (· ⬝ Equiv.bimap μ loop loop⁻¹);
    symmetry; apply μRight; symmetry; transitivity;
    symmetry; apply μLeft; apply bimapComp
  end

  -- https://github.com/mortberg/cubicaltt/blob/master/examples/helix.ctt#L207
  hott lemma lemSetTorus {π : S¹ → S¹ → Type u} (setπ : hset (π base base))
    (f : Π y, π base y) (g : Π x, π x base) (p : f base = g base) : Π x y, π x y :=
  begin
    intro x; induction x; exact f; change _ = _; transitivity;
    apply transportOverPi; apply Theorems.funext; intro y; induction y;
    transitivity; apply ap; exact p; transitivity; apply apd; exact p⁻¹; apply setπ
  end

  hott theorem isGroupoid : groupoid S¹ :=
  begin
    intros a b; change hset (a = b);
    fapply @indΩ (λ a, Π b, hset (a = b)) _ _ a <;> clear a;
    { intro b; fapply @indΩ (λ b, hset (base = b)) _ _ b <;> clear b;
      apply loopHset; intro; apply Structures.setIsProp };
    intro; apply piProp; intro; apply Structures.setIsProp
  end

  hott theorem mulComm (x y : S¹) : μ x y = μ y x :=
  begin
    fapply @lemSetTorus (λ x y, μ x y = μ y x); apply loopHset;
    { intro z; symmetry; apply unitRight };
    { intro z; apply unitRight }; reflexivity
  end

  hott corollary invMul (x : S¹) : base = μ (inv x) x :=
  begin transitivity; apply mulInv x; apply mulComm end

  hott theorem mulAssoc : Π x y z, μ x (μ y z) = μ (μ x y) z :=
  begin
    intro x; fapply @lemSetTorus (λ y z, μ x (μ y z) = μ (μ x y) z); apply isGroupoid;
    { intro z; apply ap (μ · z); exact (unitRight x)⁻¹ };
    { intro z; transitivity; apply ap; apply unitRight; symmetry; apply unitRight };
    { induction x; reflexivity; apply isGroupoid }
  end

  hott lemma mulTrans (p q : Ω¹(S¹)) : bimap μ p q = p ⬝ q :=
  begin
    transitivity; apply bimapCharacterization;
    apply bimap; apply μLeftAp; apply μRightAp
  end

  hott lemma mulTrans' (p q : Ω¹(S¹)) : bimap μ p q = q ⬝ p :=
  begin
    transitivity; apply bimapCharacterization';
    apply bimap; apply μRightAp; apply μLeftAp
  end

  hott theorem comm (x y : Ω¹(S¹)) : x ⬝ y = y ⬝ x :=
  (mulTrans x y)⁻¹ ⬝ (mulTrans' x y)

  hott theorem comm' (x y : Ω¹(S¹)) : x ⬝ y = y ⬝ x :=
    Equiv.bimap Id.trans (powerOfWinding x)⁻¹ (powerOfWinding y)⁻¹
  ⬝ Loop.powerComm Circle.loop (winding x) (winding y)
  ⬝ Equiv.bimap Id.trans (powerOfWinding y) (powerOfWinding x)

  hott definition Ωind₁ {π : Ω¹(S¹) → Type u}
    (zeroπ : π (idp base)) (succπ : Π x, π x → π (x ⬝ loop))
    (predπ : Π x, π x → π (x ⬝ loop⁻¹)) : Π x, π x :=
  begin
    intro x; apply transport π; apply powerOfWinding;
    fapply @Types.Integer.indsp (π ∘ power) _ _ _ (winding x);
    { exact zeroπ };
    { intros x ih; apply transport π;
      apply Loop.powerComp Circle.loop;
      apply succπ; exact ih };
    { intros x ih; apply transport π;
      apply Loop.powerCompPred;
      apply predπ; exact ih }
  end

  hott definition Ωind₂ {π : Ω¹(S¹) → Type u}
    (zeroπ : π (idp base)) (succπ : Π x, π x → π (loop ⬝ x))
    (predπ : Π x, π x → π (loop⁻¹ ⬝ x)) : Π x, π x :=
  begin
    fapply Ωind₁; exact zeroπ;
    { intros x ih; apply transport π; apply comm; apply succπ; exact ih };
    { intros x ih; apply transport π; apply comm; apply predπ; exact ih }
  end

  hott definition transComm {z : S¹} : Π (p q : z = z), p ⬝ q = q ⬝ p :=
  begin
    induction z; apply comm; apply Theorems.funext; intro;
    apply Theorems.funext; intro; apply isGroupoid
  end

  hott lemma transportOverCircle {z : S¹} {f g : S¹ → S¹} {p : f = g}
    (μ : f z = f z) (η : f z = g z) : @transport (S¹ → S¹) (λ φ, φ z = φ z) f g p μ = η⁻¹ ⬝ μ ⬝ η :=
  begin induction p; symmetry; apply idConjIfComm; apply transComm end

  hott definition halfway.φ : I → S¹ :=
  λ i, Interval.elim loop (i ∧ Interval.neg i)

  hott definition halfway : base = base :=
  Interval.lam halfway.φ

  hott definition halfway.const : halfway.φ ~ λ _, base :=
  begin
    intro x; induction x; reflexivity; reflexivity; change _ = _;
    transitivity; apply transportOverContrMap;
    transitivity; apply Id.rid;
    transitivity; apply Id.mapInv;
    transitivity; apply ap; apply mapOverComp;
    transitivity; apply ap; apply ap (ap (elim loop));
    change _ = idp 0; apply Structures.propIsSet;
    apply Interval.intervalProp; reflexivity
  end

  hott definition halfway.trivial : halfway = idp base :=
  begin
    transitivity; apply Equiv.mapWithHomotopy; apply halfway.const;
    transitivity; apply Id.rid; apply constmap
  end

  hott definition natPow (x : S¹) : ℕ → S¹
  | Nat.zero   => base
  | Nat.succ n => μ x (natPow x n)

  hott definition pow (x : S¹) : ℤ → S¹
  | Integer.pos n => natPow x n
  | Integer.neg n => natPow (inv x) (n + 1)

  hott definition uarec {A : Type u} (φ : A ≃ A) : S¹ → Type u := rec A (ua φ)

  hott abbreviation Ωhelix {A : Type u} {succ pred : A → A} (p : succ ∘ pred ~ id) (q : pred ∘ succ ~ id) : S¹ → Type u :=
  uarec ⟨succ, ⟨pred, q⟩, ⟨pred, p⟩⟩

  hott definition Ωrec {x : S¹} {A : Type u} (zero : A) (succ pred : A → A)
    (p : succ ∘ pred ~ id) (q : pred ∘ succ ~ id) : base = x → Ωhelix p q x :=
  λ r, @transport S¹ (Ωhelix p q) base x r zero

  section
    variable {A : Type u} (zero : A) (succ pred : A → A)
             (p : succ ∘ pred ~ id) (q : pred ∘ succ ~ id)

    hott statement Ωrecβ₁ : Ωrec zero succ pred p q (idp base) = zero :=
    by reflexivity

    hott theorem Ωrecβ₂ (r : Ω¹(S¹)) :
        Ωrec zero succ pred p q (r ⬝ loop)
      = succ (Ωrec zero succ pred p q r) :=
    begin
      transitivity; apply transportToTransportconst;
      transitivity; apply ap (transportconst · zero);
      transitivity; apply mapFunctoriality; apply ap; apply recβrule₂;
      transitivity; apply transportconstOverComposition;
      transitivity; apply uaβ; apply ap succ;
      symmetry; apply transportToTransportconst
    end

    hott theorem Ωrecβ₃ (r : Ω¹(S¹)) :
        Ωrec zero succ pred p q (r ⬝ loop⁻¹)
      = pred (Ωrec zero succ pred p q r) :=
    begin
      transitivity; apply transportToTransportconst;
      transitivity; apply ap (transportconst · zero);
      transitivity; apply mapFunctoriality; apply ap;
      transitivity; apply Id.mapInv; apply ap Id.symm; apply recβrule₂;
      transitivity; apply transportconstOverComposition;
      transitivity; apply uaβrev; apply ap pred;
      symmetry; apply transportToTransportconst
    end

    hott corollary Ωrecβ₄ (r : Ω¹(S¹)) :
        Ωrec zero succ pred p q (loop ⬝ r)
      = succ (Ωrec zero succ pred p q r) :=
    ap (Ωrec _ _ _ _ _) (comm _ _) ⬝ Ωrecβ₂ _ _ _ _ _ _

    hott corollary Ωrecβ₅ (r : Ω¹(S¹)) :
        Ωrec zero succ pred p q (loop⁻¹ ⬝ r)
      = pred (Ωrec zero succ pred p q r) :=
    ap (Ωrec _ _ _ _ _) (comm _ _) ⬝ Ωrecβ₃ _ _ _ _ _ _
  end

  hott definition mult {a b : S¹} (p : a = a) (q : b = b) : rec a p b = rec a p b :=
  ap (rec a p) q

  hott remark multZero {a b : S¹} (p : a = a) : mult p (idp b) = idp (rec a p b) :=
  idp (idp (rec a p b))

  hott corollary multOne {a : S¹} (p : a = a) : mult p loop = p :=
  by apply recβrule₂

  hott lemma multMinusOne {a : S¹} (p : a = a) : mult p loop⁻¹ = p⁻¹ :=
  begin transitivity; apply mapInv; apply ap; apply recβrule₂ end

  hott lemma oneMult (p : Ω¹(S¹)) : mult loop p = p :=
  begin
    transitivity; apply mapWithHomotopy; apply idfunRec;
    transitivity; apply idConjRevIfComm; apply comm; apply idmap
  end

  hott lemma multSucc (p q : Ω¹(S¹)) : mult p (succ q) = mult p q ⬝ p :=
  begin transitivity; apply mapFunctoriality; apply ap; apply recβrule₂ end

  hott lemma multDistrRight (p q r : Ω¹(S¹)) : mult p (q ⬝ r) = mult p q ⬝ mult p r :=
  by apply mapFunctoriality

  hott definition add (f g : S¹ → S¹) := λ x, μ (f x) (g x)

  hott theorem recAdd {a b : S¹} (p : a = a) (q : b = b) :
    add (rec a p) (rec b q) ~ rec (μ a b) (bimap μ p q) :=
  begin
    fapply ind; reflexivity; change _ = _; transitivity;
    apply Equiv.transportOverHmtpy; transitivity;
    apply ap (· ⬝ _ ⬝ _); transitivity; apply mapInv;
    apply ap; transitivity; apply Equiv.bimapBicom (rec a p) (rec b q);
    apply bimap (bimap μ) <;> apply recβrule₂;
    transitivity; apply ap; apply recβrule₂;
    transitivity; symmetry; apply Id.assoc; apply Id.invComp;
  end

  hott theorem recComMap {A : Type u} {B : Type v} (φ : A → B)
    (a : A) (p : a = a) : φ ∘ rec a p ~ rec (φ a) (ap φ p) :=
  begin
    fapply ind; reflexivity; apply Id.trans;
    apply Equiv.transportOverHmtpy; transitivity;
    apply ap (· ⬝ _); apply Id.rid;
    transitivity; apply bimap;
    { transitivity; apply mapInv; apply ap;
      transitivity; apply mapOverComp;
      apply ap; apply recβrule₂ };
    { apply recβrule₂ };
    apply invComp;
  end

  hott corollary recComp {a b : S¹} (p : a = a) (q : b = b) :
    rec a p ∘ rec b q ~ rec (rec a p b) (mult p q) :=
  by apply recComMap

  hott theorem multAssoc (p q r : Ω¹(S¹)) : mult (mult p q) r = mult p (mult q r) :=
  begin
    symmetry; transitivity; symmetry; apply mapOverComp (rec base q) (rec base p) r;
    transitivity; apply Equiv.mapWithHomotopy; apply recComp; apply Id.rid
  end

  hott corollary mulNegRight (p q : Ω¹(S¹)) : mult p q⁻¹ = (mult p q)⁻¹ :=
  by apply Id.mapInv

  hott lemma mapExt {B : Type u} (φ : S¹ → B) : φ ~ rec (φ base) (ap φ loop) :=
  begin
    fapply ind; reflexivity; change _ = _; transitivity; apply Equiv.transportOverHmtpy;
    transitivity; apply bimap; transitivity; apply Id.rid; apply Id.mapInv;
    apply recβrule₂; apply Id.invComp
  end

  hott theorem mapLoopEqv {B : Type u} : (S¹ → B) ≃ (Σ (x : B), x = x) :=
  begin
    fapply Equiv.intro;
    { intro φ; exact ⟨φ base, ap φ loop⟩ };
    { intro w; exact rec w.1 w.2 };
    { intro φ; symmetry; apply Theorems.funext; apply mapExt };
    { intro; fapply Sigma.prod; reflexivity; apply recβrule₂ }
  end

  hott theorem loopCircle {A : Type u} (a : A) : Map⁎ ⟨S¹, base⟩ ⟨A, a⟩ ≃ (a = a) :=
  begin
    fapply Equiv.intro;
    { intro φ; exact transport (λ x, x = x) φ.2 (ap φ.1 loop) };
    { intro p; existsi rec a p; reflexivity };
    { intro ⟨φ, (H : φ base = a)⟩; induction H using J₁;
      fapply Sigma.prod; symmetry; apply Theorems.funext; apply mapExt;
      transitivity; apply transportOverContrMap; transitivity; apply Id.rid;
      transitivity; apply ap (ap _); apply Id.invInv; transitivity; apply Theorems.mapToHapply;
      transitivity; apply happly; apply Theorems.happlyFunext; reflexivity };
    { apply recβrule₂ };
  end

  -- somewhat surprisingly commutativity of Ω¹(S¹) arises out of nowhere
  hott lemma recBaseInj {x : S¹} (p q : x = x) (ε : rec x p = rec x q) : p = q :=
  (recβrule₂ x p)⁻¹ ⬝ transCancelLeft _ _ _ (homotopySquare (happly ε) loop ⬝ transComm _ _)⁻¹ ⬝ recβrule₂ x q

  hott definition wind : Π (x : S¹), x = x → ℤ :=
  begin
    fapply ind; exact winding; apply Id.trans; apply Equiv.transportCharacterization;
    apply Theorems.funext; intro p; transitivity; apply Equiv.transportOverConstFamily;
    apply ap winding; transitivity; apply Equiv.transportInvCompComp;
    apply idConjIfComm; apply comm
  end

  hott definition degree : (S¹ → S¹) → ℤ :=
  λ φ, wind (φ base) (ap φ loop)

  hott lemma degreeToWind {x : S¹} (p : x = x) : degree (rec x p) = wind x p :=
  ap (wind x) (recβrule₂ x p)

  hott corollary degreeToWinding : Π (p : Ω¹(S¹)), degree (rec base p) = winding p :=
  @degreeToWind _ base

  hott lemma eqRecOfHom {A : Type u} {a b : A} (r : a = b)
    {p : a = a} {q : b = b} (ε : p ⬝ r = r ⬝ q) : rec a p = rec b q :=
  begin induction r; apply ap (rec a); exact (Id.rid p)⁻¹ ⬝ ε end

  -- so path between basepoints must be natural over loops to obtain required homotopy
  hott corollary endoHmtpyCriterion {A : Type u} {a b : A} (r : a = b)
    (p : a = a) (q : b = b) (ε : p ⬝ r = r ⬝ q) : rec a p ~ rec b q :=
  begin apply happly; apply eqRecOfHom r ε end

  section
    variable {A : Type u}

    hott definition loopOf {a : A} (p : a = a) : Σ (x : A), x = x := ⟨a, p⟩

    hott lemma eqEquivSquare (f g : S¹ → A) :=
    calc f = g
       ≃ @Id (Σ x, x = x) (loopOf (ap f loop)) (loopOf (ap g loop))
       : apEquivOnEquiv mapLoopEqv,
       ≃ Σ (r : f base = g base), ap f loop =[λ x, x = x, r] ap g loop
       : Sigma.sigmaPath,
       ≃ Σ (r : f base = g base), r⁻¹ ⬝ (ap f loop ⬝ r) = ap g loop
       : Sigma.respectsEquiv (λ _, idtoeqv (ap (· = ap g loop) (transportInvCompComp _ _ ⬝ (Id.assoc _ _ _)⁻¹))),
       ≃ Σ (r : f base = g base), ap f loop ⬝ r = r ⬝ ap g loop
       : Sigma.respectsEquiv (λ _, rewriteCompEquiv.symm)

    hott corollary recEqSquare {a b : A} (p : a = a) (q : b = b) :=
    calc rec a p = rec b q
       ≃ Σ (r : a = b), ap (rec a p) loop ⬝ r = r ⬝ ap (rec b q) loop
       : eqEquivSquare (rec a p) (rec b q),
       ≃ Σ (r : a = b), p ⬝ r = r ⬝ q
       : Sigma.respectsEquiv (λ r, idtoeqv (bimap (· ⬝ r = r ⬝ ·) (recβrule₂ a p) (recβrule₂ b q)))

    hott corollary homEqSquare {A : Type u} {a b : A} (p : a = a) (q : b = b) :=
    calc rec a p ~ rec b q ≃ rec a p = rec b q              : Theorems.full.symm,
                           ≃ (Σ (r : a = b), p ⬝ r = r ⬝ q) : recEqSquare p q
  end

  hott definition roll (x : S¹) : Ω¹(S¹) → x = x :=
  λ p, ap (rec x (rot x)) p

  open GroundZero.Proto (idfun)

  hott definition unroll : Π (x : S¹), x = x → Ω¹(S¹) :=
  begin
    fapply ind; exact idfun; apply Id.trans; apply Equiv.transportCharacterization;
    apply Theorems.funext; intro p; transitivity; apply Equiv.transportOverConstFamily;
    transitivity; apply Equiv.transportInvCompComp; apply idConjIfComm; apply comm
  end

  hott lemma rollNat {x : S¹} (p : Ω¹(S¹)) (ε : base = x) : p ⬝ ε = ε ⬝ roll x p :=
  begin induction ε; transitivity; apply Id.rid; symmetry; apply oneMult end

  hott lemma unrollNat {x : S¹} (p : x = x) (ε : base = x) : unroll x p ⬝ ε = ε ⬝ p :=
  begin induction ε; apply Id.rid end

  hott lemma rollPreservesWind {x : S¹} (p : Ω¹(S¹)) : wind x (roll x p) = winding p :=
  begin induction x using indΩ; apply ap winding; apply oneMult; apply Integer.set end

  hott lemma unrollPreservesWind : Π {x : S¹} (p : x = x), winding (unroll x p) = wind x p :=
  begin fapply indΩ; intro; reflexivity; intro; apply piProp; intro; apply Integer.set end

  section
    open GroundZero.Types.Integer

    hott lemma windingTrans : Π (p q : Ω¹(S¹)), winding (p ⬝ q) = winding p + winding q :=
    begin
      intro p; fapply Ωind₁;
      { transitivity; apply ap; apply Id.rid; symmetry; apply Integer.addZero };
      { intro q ih; transitivity; apply ap; apply Id.assoc; transitivity;
        apply Ωrecβ₂; transitivity; apply ap; exact ih; transitivity;
        symmetry; apply plusSucc; apply ap; symmetry; apply Ωrecβ₂ };
      { intro q ih; transitivity; apply ap; apply Id.assoc; transitivity;
        apply Ωrecβ₃; transitivity; apply ap; exact ih; transitivity;
        symmetry; apply plusPred; apply ap; symmetry; apply Ωrecβ₃ }
    end

    hott theorem windBimap : Π {a b : S¹} (p : a = a) (q : b = b),
      wind (μ a b) (bimap μ p q) = wind a p + wind b q :=
    begin
      fapply indΩ₂; intro p q; transitivity; apply ap winding; apply mulTrans; apply windingTrans;
      intros; apply piProp; intro; apply piProp; intro; apply Integer.set
    end

    hott theorem degAdd (f g : S¹ → S¹) : degree (add f g) = degree f + degree g :=
    begin
      transitivity; apply bimap (λ φ ψ, degree (add φ ψ)) <;> { apply Theorems.funext; apply mapExt };
      transitivity; apply ap degree; apply Theorems.funext; apply recAdd;
      transitivity; apply degreeToWind; apply windBimap
    end

    hott lemma powerRev (z : ℤ) : winding (power z)⁻¹ = -z :=
    begin
      induction z using indsp; reflexivity;
      { transitivity; apply ap winding; transitivity; apply ap; symmetry;
        apply Loop.powerComp; apply Id.explodeInv; transitivity; apply Ωrecβ₅;
        transitivity; apply ap Integer.pred; assumption; symmetry; apply Integer.negateSucc };
      { transitivity; apply ap winding; transitivity; apply ap; symmetry;
        apply Loop.powerCompPred; apply Id.explodeInv; transitivity;
        apply ap (λ p, winding (p ⬝ _)); apply Id.invInv;
        transitivity; apply Ωrecβ₄; transitivity; apply ap Integer.succ;
        assumption; symmetry; apply Integer.negatePred }
    end

    hott theorem windingRev (p : Ω¹(S¹)) : winding p⁻¹ = -(winding p) :=
    begin
      transitivity; apply ap (λ q, winding q⁻¹);
      symmetry; apply powerOfWinding; apply powerRev
    end

    hott corollary windRev : Π {x : S¹} (p : x = x), wind x p⁻¹ = -(wind x p) :=
    begin fapply indΩ; apply windingRev; intro; apply piProp; intro; apply Integer.set end

    hott lemma windingMult : Π (p q : Ω¹(S¹)), winding (mult p q) = winding p * winding q :=
    begin
      intro p; fapply Ωind₁;
      { symmetry; apply Integer.multZero };
      { intro q ih; transitivity; apply ap; apply multDistrRight; transitivity;
        apply windingTrans; transitivity; apply ap (λ z, z + winding _); apply ih;
        transitivity; apply ap; apply ap winding; apply multOne;
        transitivity; symmetry; apply Integer.multSucc;
        apply ap; symmetry; apply Ωrecβ₂ };
      { intro q ih; transitivity; apply ap; apply multDistrRight; transitivity;
        apply windingTrans; transitivity; apply ap (λ z, z + winding _); apply ih;
        transitivity; apply ap; apply ap winding; apply multMinusOne;
        transitivity; apply ap (Integer.add _); apply windingRev;
        transitivity; symmetry; apply Integer.multPred;
        apply ap; symmetry; apply Ωrecβ₃ }
    end

    hott theorem windMult : Π {a b : S¹} (p : a = a) (q : b = b),
      wind (rec a p b) (mult p q) = wind a p * wind b q :=
    begin
      fapply indΩ₂; intros; apply windingMult; intros;
      apply piProp; intro; apply piProp; intro; apply Integer.set
    end

    hott theorem degCom (f g : S¹ → S¹) : degree (f ∘ g) = degree f * degree g :=
    begin
      transitivity; apply bimap (λ φ ψ, degree (φ ∘ ψ)) <;> { apply Theorems.funext; apply mapExt };
      transitivity; apply ap degree; apply Theorems.funext; apply recComp;
      transitivity; apply degreeToWind; apply windMult
    end

    hott lemma degOne : degree idfun = 1 :=
    begin
      transitivity; apply ap degree; apply Theorems.funext;
      symmetry; apply idfunRec; transitivity;
      apply degreeToWind; apply windingPower 1
    end

    hott lemma degZero : degree (λ _, base) = 0 :=
    begin
      transitivity; apply ap degree; apply Theorems.funext;
      symmetry; apply constRec; apply degreeToWind
    end

    hott lemma degMinusOne : degree inv = -1 :=
    begin transitivity; apply degreeToWind; apply windingPower (-1) end
  end

  open GroundZero.Types.Integer (abs)
  open GroundZero.Proto

  hott theorem plusEqZeroRight {n : ℕ} : Π {m : ℕ}, n + m = 0 → m = 0
  | Nat.zero,   _ => idp 0
  | Nat.succ _, H => explode (succNeqZero H)

  hott theorem multEqOneRight : Π (n m : ℕ), n * m = 1 → m = 1
  | n,          Nat.zero,   H => explode (succNeqZero H⁻¹)
  | Nat.zero,   Nat.succ m, H => explode (succNeqZero (H⁻¹ ⬝ Theorems.Nat.zeroMul _))
  | Nat.succ n, Nat.succ m, H => (H⁻¹ ⬝ ap (λ k, Nat.succ k * Nat.succ m)
                                           (plusEqZeroRight (Theorems.Nat.succInj H))
                                      ⬝ Theorems.Nat.oneMul _)⁻¹

  hott corollary multEqOneLeft (n m : ℕ) (H : n * m = 1) : n = 1 :=
  multEqOneRight m n (Theorems.Nat.mulComm _ _ ⬝ H)

  hott lemma zeroNeqOne : ¬@Id ℤ 0 1 :=
  λ p, @succNeqZero 0 (Coproduct.inl.encode p)⁻¹

  hott theorem degOfRetr (f g : S¹ → S¹) (H : f ∘ g ~ id) : abs (degree f) = 1 :=
  begin
    have η := (degCom f g)⁻¹ ⬝ ap degree (Theorems.funext H) ⬝ degOne;
    have ε := (Integer.absMult _ _)⁻¹ ⬝ ap Integer.abs η;
    apply multEqOneLeft; transitivity; symmetry; apply Integer.absMult;
    exact degree g; transitivity; symmetry; apply ap abs; apply degCom;
    transitivity; apply ap (abs ∘ degree); apply Theorems.funext H;
    transitivity; apply ap abs; apply degOne; reflexivity
  end

  hott corollary degOfBiinv (f : S¹ → S¹) : biinv f → abs (degree f) = 1 :=
  λ w, degOfRetr f w.2.1 w.2.2

  hott lemma windingMulPower (z : ℤ) (p : Ω¹(S¹)) : winding (Loop.power p z) = z * winding p :=
  begin
    induction z using Integer.indsp; symmetry; apply Integer.zeroMult;
    { transitivity; apply ap winding; symmetry; apply Loop.powerComp;
      transitivity; apply windingTrans; transitivity; apply ap (λ k, k + winding p);
      assumption; symmetry; apply Integer.succMult };
    { transitivity; apply ap winding; symmetry; apply Loop.powerCompPred;
      transitivity; apply windingTrans; transitivity; apply ap (λ k, k + winding p⁻¹);
      assumption; transitivity; apply ap (Integer.add _);
      apply windingRev; symmetry; apply Integer.predMult }
  end

  hott corollary windMulPower : Π {x : S¹} (z : ℤ) (p : x = x),
    wind x (Loop.power p z) = z * wind x p :=
  begin
    fapply ind; apply windingMulPower; apply piProp;
    intro; apply piProp; intro; apply Integer.set
  end

  hott proposition windRot (x : S¹) : wind x (rot x) = 1 :=
  begin induction x using indΩ; apply windingPower 1; apply Integer.set end

  hott lemma windPowerRot {x : S¹} (z : ℤ) : wind x (Loop.power (rot x) z) = z :=
  begin
    transitivity; apply windMulPower; transitivity;
    apply ap (_ * ·); apply windRot; apply Integer.multOne
  end

  hott corollary degPowerRot {x : S¹} (z : ℤ) : degree (rec x (Loop.power (rot x) z)) = z :=
  begin transitivity; apply degreeToWind; apply windPowerRot end

  hott lemma windPower : Π {x : S¹} (p : x = x), Loop.power (rot x) (wind x p) = p :=
  begin fapply ind; apply powerOfWinding; apply piProp; intro; apply isGroupoid end

  section
    variable {a b : S¹} (p : a = a) (ε : a = b) (z : ℤ)

    hott lemma loopPowerConjLeft : Loop.power (ε⁻¹ ⬝ p ⬝ ε) z = ε⁻¹ ⬝ Loop.power p z ⬝ ε :=
    begin induction ε; transitivity; apply ap (Loop.power · _); apply Id.rid; symmetry; apply Id.rid end

    hott corollary loopPowerConjComm : Loop.power p z ⬝ ε = ε ⬝ Loop.power (ε⁻¹ ⬝ p ⬝ ε) z :=
    invRewriteComp (Id.assoc _ _ _ ⬝ (loopPowerConjLeft _ _ _)⁻¹)
  end

  hott corollary loopPowerConjRight {a b : S¹} (p : b = b) (ε : a = b) (z : ℤ) :
    Loop.power (ε ⬝ p ⬝ ε⁻¹) z = ε ⬝ Loop.power p z ⬝ ε⁻¹ :=
  begin
    transitivity; apply ap (Loop.power · z); apply ap (λ q, q ⬝ p ⬝ ε⁻¹);
    symmetry; apply Id.invInv; transitivity; apply loopPowerConjLeft;
    apply ap (λ q, q ⬝ _ ⬝ _); apply Id.invInv
  end

  hott lemma rotInterchange {a b : S¹} (p : a = b) : p⁻¹ ⬝ rot a ⬝ p = rot b :=
  begin induction p; apply Id.rid end

  hott theorem hmtpyDegCriterion {f g : S¹ → S¹} (p : f base = g base) (q : degree f = degree g) : f ~ g :=
  begin
    transitivity; apply mapExt; transitivity; fapply endoHmtpyCriterion;
    exact g base; exact p; exact ap g loop; transitivity; apply ap (· ⬝ _);
    transitivity; symmetry; apply windPower; apply ap (Loop.power _); exact q;
    transitivity; apply loopPowerConjComm; apply ap; transitivity;
    apply ap (λ p, Loop.power p _); apply rotInterchange;
    apply windPower; symmetry; apply mapExt
  end

  hott proposition circleConnected (x : S¹) : ∥x = base∥ :=
  begin induction x; exact Merely.elem loop; apply Merely.uniq end

  hott corollary minusOneNeqOne : ¬@Id ℤ (-1) 1 :=
  Coproduct.inr.encode

  hott lemma invNeqIdfun : ¬(inv ~ idfun) :=
  λ H, minusOneNeqOne (degMinusOne⁻¹ ⬝ ap degree (Theorems.funext H) ⬝ degOne)

  hott lemma invCancelLeft {a b : S¹} : μ (inv a) (μ a b) = b :=
  mulAssoc _ _ _ ⬝ ap (μ · b) (invMul _)⁻¹ ⬝ unitLeft _

  hott lemma invCancelRight {a b : S¹} : μ a (μ (inv a) b) = b :=
  mulAssoc _ _ _ ⬝ ap (μ · b) (mulInv _)⁻¹ ⬝ unitLeft _

  hott corollary μInj {a b c : S¹} (H : μ c a = μ c b) : a = b :=
  invCancelLeft⁻¹ ⬝ ap (μ (inv c)) H ⬝ invCancelLeft

  hott lemma μSqrNotConst : ¬(Π x, μ x x = base) :=
  begin
    intro H; apply invNeqIdfun; intro x; apply @μInj _ _ x;
    symmetry; transitivity; apply H; apply mulInv
  end

  hott lemma μNotLinv : ¬(Π x, μ x ∘ μ x ~ idfun) :=
  begin
    intro H; apply μSqrNotConst; intro x; transitivity;
    apply ap (μ x); symmetry; apply unitRight; apply H
  end

  hott lemma rotPowerDecom : Π {x : S¹} (p : x = x), mult (rot x) (power (wind x p)) = p :=
  begin
    fapply ind; intro; transitivity; apply oneMult;
    apply powerOfWinding; apply piProp; intro; apply isGroupoid
  end

  hott definition dup (φ : S¹ → S¹) := rec base (power (degree φ))

  hott theorem μDef (x : S¹) : μ x ~ rec x (rot x) :=
  begin
    transitivity; apply mapExt; fapply endoHmtpyCriterion;
    apply unitRight; induction x; transitivity; apply ap (· ⬝ _);
    apply μRight; apply comm; apply isGroupoid
  end

  hott corollary μDegree (x : S¹) : degree (μ x) = 1 :=
  begin
    transitivity; apply ap; apply Theorems.funext;
    apply μDef; transitivity; apply degreeToWind; apply windRot
  end

  hott theorem dupDegree (φ : S¹ → S¹) : degree (dup φ) = degree φ :=
  begin transitivity; apply degreeToWind; apply windingPower end

  hott theorem μDupDecom (φ : S¹ → S¹) : φ ~ μ (φ base) ∘ dup φ :=
  begin
    transitivity; apply mapExt; symmetry; transitivity;
    apply Homotopy.lwhs; apply μDef; transitivity;
    apply recComp; apply happly; apply ap (rec (φ base));
    apply rotPowerDecom
  end

  section
    hott lemma windingOneImplLoop (p : Ω¹(S¹)) : winding p = 1 → p = loop :=
    begin
      apply transport (λ q, winding q = 1 → q = loop); apply powerOfWinding;
      intro ε; transitivity; apply ap power; transitivity; apply ap winding;
      symmetry; apply powerOfWinding; exact ε; reflexivity
    end

    hott corollary idfunIfDegOne (f : S¹ → S¹) (p : f base = base) (H : degree f = 1) : f ~ idfun :=
    begin fapply hmtpyDegCriterion; exact p; transitivity; apply H; symmetry; apply degOne end

    hott theorem absOneDec : Π (z : ℤ), abs z = 1 → (z = 1) + (z = -1)
    | Integer.pos n,            H => Coproduct.inl (ap Integer.pos H)
    | Integer.neg Nat.zero,     _ => Coproduct.inr (idp _)
    | Integer.neg (Nat.succ n), H => explode (succNeqZero (Theorems.Nat.succInj H))

    hott corollary absOneImplSqrEqOne (z : ℤ) (H : abs z = 1) : z * z = 1 :=
    match absOneDec z H with
    | Coproduct.inl p => transport (λ k, k * k = 1) p⁻¹ (idp _)
    | Coproduct.inr q => transport (λ k, k * k = 1) q⁻¹ (idp _)

    hott lemma sqrIdfunHmtpy (f : S¹ → S¹) (H : abs (degree f) = 1) (ε : f (f base) = base) : f ∘ f ~ idfun :=
    begin apply idfunIfDegOne; exact ε; transitivity; apply degCom; apply absOneImplSqrEqOne; exact H end

    /-- It doesn’t mean that classically these maps are not homotopic,
        but that this homotopy cannot be chosen continously.

        This is similar to the fact that we cannot construct “Π x, base = x”,
        but we can construct “Π x, ∥base = x∥”.

        It also means that we cannot drop “f (f base) = base” condition in the previous lemma,
        so the next theorem cannot be proved this way outside of ∥·∥.
    -/
    hott proposition sqrIdfunNonHmtpy : ¬(Π f, abs (degree f) = 1 → f ∘ f ~ idfun) :=
    λ H, μNotLinv (λ x, H (μ x) (ap abs (μDegree x)))

    hott corollary sqrIdfunMerelyHmtpy : Π f, abs (degree f) = 1 → ∥f ∘ f ~ idfun∥ :=
    λ f H, Merely.lift (sqrIdfunHmtpy f H) (circleConnected (f (f base)))

    /-- It’s interesting that this construction of f⁻¹ is not very explicit
        as it was produced inside of ∥·∥, so it’s not definitionally
        in the form “rec x p” as we may expect.

        So this proof is to some extent “non-constructive”, however degree of the inverse
        map obtained from this proof should normalize in CTT as well as degree
        of any other concrete map S¹ → S¹.

        For the more explicit construction see below (`biinvOfDegOneHmtpy'`).
    -/
    hott theorem biinvOfDegOneHmtpy (f : S¹ → S¹) (H : abs (degree f) = 1) : biinv f :=
    begin
      apply Merely.rec _ _ (sqrIdfunMerelyHmtpy f H); apply Theorems.Equiv.biinvProp;
      intro; fapply Qinv.toBiinv; existsi f; apply Prod.intro <;> assumption
    end
  end

  section
    variable (f : S¹ → S¹)

    hott corollary translationMap (H : degree f = 1) : f ~ μ (f base) :=
    begin
      transitivity; apply μDupDecom; apply Homotopy.rwhs;
      transitivity; apply happly; apply ap (rec base);
      apply ap power; exact H; apply idfunRec
    end

    hott corollary reflectionMap (H : degree f = -1) : f ~ μ (f base) ∘ inv :=
    begin
      transitivity; apply μDupDecom; apply Homotopy.rwhs; apply happly; apply ap (rec base);
      transitivity; apply ap power; exact H; reflexivity
    end

    hott theorem translationMapBiinv (H : degree f = 1) : biinv f :=
    begin
      fapply Qinv.toBiinv; existsi μ (inv (f base)); fapply Prod.mk;
      { transitivity; apply Homotopy.lwhs;
        apply translationMap f H; apply invCancelRight };
      { transitivity; apply Homotopy.rwhs;
        apply translationMap f H; apply invCancelLeft }
    end

    hott theorem reflectionMapBiinv (H : degree f = -1) : biinv f :=
    begin
      fapply Qinv.toBiinv; existsi inv ∘ μ (inv (f base)); fapply Prod.mk;
      { transitivity; apply Homotopy.lwhs; apply reflectionMap f H;
        transitivity; apply @Homotopy.rwhs _ _ _ (μ (f base));
        apply @Homotopy.lwhs _ _ _ (inv ∘ inv) idfun (μ (inv (f base)));
        apply invol; apply invCancelRight };
      { transitivity; apply Homotopy.rwhs; apply reflectionMap f H;
        transitivity; apply @Homotopy.rwhs _ _ _ inv;
        apply @Homotopy.lwhs _ _ _ (μ (inv (f base)) ∘ μ (f base)) idfun inv;
        apply invCancelLeft; apply invol }
    end

    -- Explicit version of `biinvOfDegOneHmtpy`.
    hott corollary biinvOfDegOneHmtpy' (f : S¹ → S¹) (H : abs (degree f) = 1) : biinv f :=
    begin
      induction absOneDec (degree f) H;
      apply translationMapBiinv; assumption;
      apply reflectionMapBiinv; assumption
    end
  end

  hott corollary degIffBiinv (f : S¹ → S¹) : biinv f ≃ (abs (degree f) = 1) :=
  begin
    apply Structures.propEquivLemma;
    apply Theorems.Equiv.biinvProp; apply Theorems.Nat.natIsSet;
    apply degOfBiinv; apply biinvOfDegOneHmtpy
  end

  hott theorem endoEquiv : (S¹ → S¹) ≃ ℤ × S¹ :=
  begin
    existsi λ φ, (degree φ, φ base); apply Qinv.toBiinv;
    existsi λ w, rec w.2 (Loop.power (rot w.2) w.1); apply Prod.intro;
    { intro w; apply Product.prod; apply degPowerRot; reflexivity };
    { intro φ; symmetry; apply Theorems.funext;
      transitivity; apply mapExt; apply happly;
      apply ap (rec (φ base)); symmetry; apply windPower }
  end

  hott lemma circleEqvDeg (z : ℤ) : (Σ (f : S¹ → S¹), degree f = z) ≃ S¹ :=
  begin
    fapply Sigma.mk; intro w; exact w.1 base; apply Qinv.toBiinv;
    fapply Sigma.mk; intro x; existsi rec x (Loop.power (rot x) z); apply degPowerRot;
    apply Prod.intro; intro; reflexivity; intro w; fapply Sigma.prod;
    symmetry; apply Theorems.funext; transitivity; apply mapExt;
    apply happly; apply ap (rec (w.1 base)); symmetry;
    transitivity; apply ap (Loop.power _); exact w.2⁻¹;
    apply windPower; apply Integer.set
  end

  section
    open GroundZero.Types.Coproduct (inl inr)

    open GroundZero.Types.Integer (pos auxsucc)

    hott lemma neqZeroImplNeqMinus : Π (i : ℕ), i ≠ 0 → pos i ≠ auxsucc i
    | Nat.zero,   H, G => H (inl.encode G)
    | Nat.succ i, _, G => inl.encode G

    hott lemma absEqEqv {i : ℤ} (j : ℕ) (H : j ≠ 0) : (abs i = j) ≃ (i = pos j) + (i = auxsucc j) :=
    begin
      apply propEquivLemma; apply Theorems.Nat.natIsSet;
      apply propSum; apply Integer.set; apply Integer.set;
      intro w; apply neqZeroImplNeqMinus; exact H; exact w.1⁻¹ ⬝ w.2;
      { intro G; induction i using Sum.casesOn;
        { left; apply ap pos; exact G };
        { induction j using Nat.casesOn; left; apply explode; apply H; reflexivity;
          right; apply ap Sum.inr; apply Theorems.Nat.succInj; exact G } };
      { intro G; induction G using Sum.casesOn; transitivity; apply ap abs; assumption;
        reflexivity; transitivity; apply ap abs; assumption;
        induction j using Nat.casesOn; apply explode;
        apply H; reflexivity; reflexivity }
    end

    hott theorem sigmaSumDistrib {A : Type u} (B : A → Type v) (C : A → Type w) :
      (Σ x, B x + C x) ≃ (Σ x, B x) + (Σ x, C x) :=
    begin
      fapply Sigma.mk; intro w; exact Coproduct.elim (λ b, inl ⟨w.1, b⟩) (λ c, inr ⟨w.1, c⟩) w.2;
      apply Qinv.toBiinv; fapply Sigma.mk; exact Coproduct.elim (λ w, ⟨w.1, inl w.2⟩) (λ w, ⟨w.1, inr w.2⟩);
      apply Prod.intro; intro w; induction w using Sum.casesOn <;> reflexivity;
      intro | ⟨x, inl _⟩ => _ | ⟨x, inr _⟩ => _ <;> reflexivity
    end
  end

  section
    open GroundZero.Types.Integer (auxsucc)

    hott theorem autEquiv :=
    calc (S¹ ≃ S¹) ≃ Σ φ, abs (degree φ) = 1                           : Sigma.respectsEquiv degIffBiinv,
                   ≃ Σ φ, (degree φ = 1) + (degree φ = auxsucc 1)      : Sigma.respectsEquiv (λ _, absEqEqv 1 succNeqZero),
                   ≃ (Σ φ, degree φ = 1) + (Σ φ, degree φ = auxsucc 1) : sigmaSumDistrib _ _,
                   ≃ S¹ + S¹                                           : sumEquiv (circleEqvDeg _) (circleEqvDeg _)
  end

  section
    variable {B : Type u} (b : B) (p q : b = b) (H : p ⬝ q = q ⬝ p)

    hott definition birec : S¹ → S¹ → B :=
    begin
      fapply @rec (S¹ → B) (rec b p); apply Theorems.funext;
      fapply Circle.ind; exact q; change _ = _; transitivity;
      apply Equiv.transportOverHmtpy; transitivity; apply bimap (· ⬝ q ⬝ ·);
      apply recβrule₃; apply recβrule₂; apply idConjIfComm; exact H⁻¹
    end

    hott definition birecβrule₁ : ap (birec b p q H base) loop = p :=
    by apply recβrule₂

    hott definition birecβrule₂ : ap (birec b p q H · base) loop = q :=
    begin
      transitivity; apply Interval.mapHapply;
      transitivity; apply ap (happly · base); apply recβrule₂;
      apply happly (Theorems.happlyFunext _ _ _) base
    end

    hott definition birecBimap : bimap (birec b p q H) loop loop = p ⬝ q :=
    begin
      transitivity; apply Equiv.bimapCharacterization';
      apply bimap; apply birecβrule₁; apply birecβrule₂
    end
  end

  open GroundZero.Types.Coproduct

  hott lemma succNeqIdp : ua (Integer.succEquiv) ≠ idp ℤ :=
  begin
    intro H; apply @succNeqZero 0; apply @inl.encode ℕ ℕ _ (inl 0);
    transitivity; symmetry; apply uaβ Integer.succEquiv 0;
    apply ap (transportconst · 0) H
  end

  hott lemma helixNontriv : helix ≠ (λ _, ℤ) :=
  begin
    intro H; apply succNeqIdp; transitivity; symmetry; apply recβrule₂;
    apply transport (λ φ, ap φ loop = idp (φ base)) H⁻¹; apply constmap
  end

  hott proposition loopSpaceNontriv : ¬(Π (x y : S¹), (x = y) ≃ ℤ) :=
  begin
    intro H; apply helixNontriv; apply Theorems.funext; intro y;
    apply ua; transitivity; symmetry; apply family; apply H
  end

  hott definition funextPath {A : Type u} {B : Type v} {a b c : A} (f : a = b → B) (g : a = c → B)
    (p : b = c) (η : Π q, f (q ⬝ p⁻¹) = g q) : f =[λ x, a = x → B, p] g :=
  begin
    induction p; apply Theorems.funext; intro; transitivity;
    apply ap; apply Id.symm; apply Id.rid; apply η
  end

  hott lemma transportPathMap {A : Type u} {B : Type v} {a b c : A} (φ : a = b → B) (p : b = c) (q : a = c) :
    transport (λ x, a = x → B) p φ q = φ (q ⬝ p⁻¹) :=
  begin induction p; induction q; reflexivity end

  section
    variable {A : Type u} {B : Type v} {a b c : A} {f : a = b → B} {g : a = c → B} {p : b = c} (φ : Π r, f (r ⬝ p⁻¹) = g r)

    hott lemma happlyFunextPath {q : a = c} : happly (funextPath f g p φ) q = transportPathMap f p q ⬝ φ q :=
    begin induction p; induction q; apply Interval.happly (Theorems.happlyFunext _ _ _) end

    hott lemma happlyRevFunextPath {q : b = a} :
        happly (depSymm p (funextPath f g p φ)) q⁻¹
      = transportPathMap g p⁻¹ q⁻¹ ⬝ (φ (q⁻¹ ⬝ p⁻¹⁻¹))⁻¹ ⬝ ap f (cancelInvComp _ _) :=
    begin
      induction p; induction q; transitivity; apply Interval.happly (Interval.happlyRev _);
      transitivity; apply ap Id.symm; apply Interval.happly (Theorems.happlyFunext _ _ _);
      symmetry; apply Id.rid
    end
  end

  hott lemma transportMeet {A : Type u} {a : A} (B : Π x, a = x → Type v)
    (w : B a (idp a)) {b : A} (p : a = b) : transport (λ x, a = x → Type v) p (B a) p :=
  begin induction p; exact w end

  hott definition meetTransportCoh {A : Type u} {a b : A} (B : Π x, a = x → Type v) (w : B a (idp a)) (p : a = b) :
    transportconst (transportPathMap (B a) p p) (transportMeet B w p) = transport (B a) (compInv p)⁻¹ w :=
  begin induction p; reflexivity end

  section
    variable {A : Type u} {a : A} (B : Π x, a = x → Type v) (w : B a (idp a)) {b : A} (p : a = b)

    hott definition ΩJ := transportconst (happly (apd B p) p) (transportMeet B w p)

    hott definition ΩJDef : J₁ B w p = ΩJ B w p :=
    begin induction p; reflexivity end
  end

  section
    variable {x : S¹} (π : x = base → Type u)
             (succπ : Π z, π z → π (z ⬝ loop)) (predπ : Π z, π z → π (z ⬝ loop⁻¹))
             (coh₁ : Π p z, predπ _ (succπ p z) =[cancelCompInv _ _] z)
             (coh₂ : Π p z, succπ _ (predπ p z) =[cancelInvComp _ _] z)

    hott lemma ΩEquivSuccInj {z : x = base} {w₁ w₂ : π z} (H : succπ z w₁ = succπ z w₂) : w₁ = w₂ :=
    begin
      transitivity; apply Id.symm; apply coh₁;
      transitivity; apply ap (transport π _ ∘ predπ _);
      apply H; apply coh₁
    end

    hott lemma ΩEquivPredInj {z : x = base} {w₁ w₂ : π z} (H : predπ z w₁ = predπ z w₂) : w₁ = w₂ :=
    begin
      transitivity; apply Id.symm; apply coh₂;
      transitivity; apply ap (transport π _ ∘ succπ _);
      apply H; apply coh₂
    end

    hott definition ΩSuccEquiv (z : x = base) : π (z ⬝ loop⁻¹) ≃ π z :=
    Equiv.intro (λ H, transport π (cancelInvComp z loop) (succπ _ H)) (predπ z)
      (λ _, ΩEquivSuccInj π succπ predπ coh₁
        ((transportForwardAndBack (cancelInvComp _ _) _)⁻¹ ⬝
          ap (transport _ _) (coh₂ _ _) ⬝ transportForwardAndBack _ _))
      (coh₂ _)

    hott definition ΩHelix : Π y, x = y → Type u :=
    Circle.ind π (funextPath π π loop (λ z, ua (ΩSuccEquiv π succπ predπ coh₁ coh₂ z)))

    hott lemma ΩHelixSucc {z : x = base} (w : π (z ⬝ idp base)) :
        J₁ (λ y r, ΩHelix π succπ predπ coh₁ coh₂ y (z ⬝ r)) w loop
      = succπ z (transport π (rid _) w) :=
    begin
      induction z using J₂; transitivity; apply ΩJDef;
      transitivity; apply ap (transportconst · _);
      transitivity; apply ap (happly · _); apply indβrule₂; apply happlyFunextPath;
      transitivity; apply transportconstOverComposition;
      transitivity; apply ap (transportconst _); apply meetTransportCoh (ΩHelix π succπ predπ coh₁ coh₂);
      transitivity; apply uaβ; show transport _ _ _ = _; transitivity;

      apply ap (transport _ _); transitivity; transitivity; apply happly;
      symmetry; apply apd succπ (compInv loop)⁻¹; apply happly;
      apply transportImpl; apply ap (transport _ _); apply ap (succπ _);
      apply transportForwardAndBack; apply compInvCancelCoh
    end

    hott lemma ΩHelixPred {z : x = base} (w : π (z ⬝ idp base)) :
        J₁ (λ y r, ΩHelix π succπ predπ coh₁ coh₂ y (z ⬝ r)) w loop⁻¹
      = predπ z (transport π (rid _) w) :=
    begin
      induction z using J₂; transitivity; apply ΩJDef;
      transitivity; apply ap (transportconst · _);
      transitivity; apply ap (happly · _);
      transitivity; apply apdInv; apply ap (depSymm _); apply indβrule₂; apply happlyRevFunextPath;
      transitivity; apply transportconstOverComposition;
      transitivity; apply ap (transportconst _);
      transitivity; apply transportconstOverComposition;
      transitivity; apply ap (transportconst _); apply meetTransportCoh (ΩHelix π succπ predπ coh₁ coh₂);
      apply uaβrev; transitivity; symmetry; apply transportToTransportconst;

      show transport _ _ (predπ _ _) = _; transitivity;
      apply ap (transport _ _); transitivity; transitivity; apply happly;
      symmetry; apply apd predπ (compInv loop⁻¹)⁻¹; apply happly;
      apply transportImpl; apply ap (transport _ _); apply ap (predπ _);
      apply transportForwardAndBack; apply compInvCancelCoh
    end
  end

  section
    variable {π : Ω¹(S¹) → Type u} (zeroπ : π (idp base))
             (succπ : Π x, π x → π (x ⬝ loop)) (predπ : Π x, π x → π (x ⬝ loop⁻¹))
             (coh₁ : Π p z, predπ _ (succπ p z) =[cancelCompInv _ _] z)
             (coh₂ : Π p z, succπ _ (predπ p z) =[cancelInvComp _ _] z)

    -- https://github.com/ncfavier/cubical-experiments/blob/998602175a25def84b927b5071dac208aea38d7d/Shapes.agda#L52-L68
    hott definition Ωind (z : Ω¹(S¹)) : π z :=
    J₁ (ΩHelix π succπ predπ coh₁ coh₂) zeroπ z

    hott lemma Ωindβ₁ : Ωind zeroπ succπ predπ coh₁ coh₂ (idp base) = zeroπ :=
    by reflexivity

    hott lemma Ωindβ₂ (z : Ω¹(S¹)) :
        Ωind zeroπ succπ predπ coh₁ coh₂ (z ⬝ loop)
      = succπ z (Ωind zeroπ succπ predπ coh₁ coh₂ z) :=
    begin
      transitivity; apply JTrans;
      transitivity; apply ΩHelixSucc;
      apply ap; apply transportBackAndForward
    end

    hott lemma Ωindβ₃ (z : Ω¹(S¹)) :
        Ωind zeroπ succπ predπ coh₁ coh₂ (z ⬝ loop⁻¹)
      = predπ z (Ωind zeroπ succπ predπ coh₁ coh₂ z) :=
    begin
      transitivity; apply JTrans;
      transitivity; apply ΩHelixPred;
      apply ap; apply transportBackAndForward
    end
  end

  open GroundZero.Theorems

  /--
    This equivalence informally states that filling in a loop is the same as adding
    a new point x₀, the hub, and spokes f z = x₀ for every z : S¹, similar
    to the spokes in a wheel. This means that in a higher inductive type, we can
    replace a 2-path constructor p = idp x by a new point constructor x₀ : A and
    a family of 1-path constructors Π (z : S¹), f z = x₀.

    From “Homotopy Type Theory in Lean”, https://arxiv.org/abs/1704.06781.
  -/
  hott lemma hubSpokesEquiv {A : Type u} {a : A} (p : a = a) :=
  calc (Σ (x₀ : A), Π (z : S¹), rec a p z = x₀)
      ≃ Σ (x₀ : A), Π (z : S¹), rec a p z = rec x₀ (idp x₀) z
      : Sigma.respectsEquiv (λ _, equivFunext (λ z, idtoeqv (ap (rec a p z = ·) (constRec _ _)⁻¹))),
      ≃ Σ (x₀ : A) (ε : a = x₀), p ⬝ ε = ε ⬝ idp x₀
      : Sigma.respectsEquiv (λ x₀, homEqSquare p (idp x₀)),
      ≃ Σ (x₀ : A) (ε : a = x₀), p ⬝ ε = ε
      : Sigma.respectsEquiv (λ x₀, Sigma.respectsEquiv (λ ε, idtoeqv (ap (p ⬝ ε = ·) (Id.rid ε)))),
      ≃ Σ (w : Σ x₀, a = x₀), p ⬝ w.2 = w.2
      : Sigma.assoc (λ w, p ⬝ w.2 = w.2),
      ≃ (p ⬝ idp a = idp a)
      : Equiv.contrFamily (singl.contr a),
      = (p = idp a)
      : ap (· = idp a) (Id.rid p)

  /--
    One might question the need for introducing the hub point x₀ : A; why couldn’t we
    instead simply add paths continuously relating the boundary of the disc to a point
    on that boundary?

    The problem is that the specified path from a : A to itself may not be reflexivity.

    HoTT book, remark 6.7.1.
  -/
  hott remark hubSpokesNonEquiv {A : Type u} {a : A} (p : a = a) :=
  calc (Π (z : S¹), rec a p z = a)
     ≃ (Π (z : S¹), rec a p z = rec a (idp a) z)
     : equivFunext (λ z, idtoeqv (ap (rec a p z = ·) (constRec _ _)⁻¹)),
     ≃ Σ (ε : a = a), p ⬝ ε = ε ⬝ idp a
     : homEqSquare p (idp a),
     ≃ Σ (ε : a = a), p ⬝ ε = idp a ⬝ ε
     : Sigma.respectsEquiv (λ ε, idtoeqv (ap (p ⬝ ε = ·) (Id.rid ε))),
     ≃ Σ (ε : a = a), p = idp a
     : Sigma.respectsEquiv (λ _, cancelRightEquiv),
     ≃ (a = a) × (p = idp a)
     : Sigma.const (a = a) (p = idp a)
end Circle

hott definition Torus := S¹ × S¹
notation "T²" => Torus

namespace Torus
  open Types.Product

  hott definition b : T² := ⟨Circle.base, Circle.base⟩

  hott definition inj₁ : S¹ → T² := Prod.mk Circle.base
  hott definition inj₂ : S¹ → T² := (Prod.mk · Circle.base)

  -- poloidal and toroidal directions
  hott definition p : b = b := prod (idp Circle.base) Circle.loop
  hott definition q : b = b := prod Circle.loop (idp Circle.base)

  hott definition Φ {π : Type u} {x x' y y' : π}
    (α : x = x') (β : y = y') :
    prod (idp x) β ⬝ prod α (idp y') =
    prod α (idp y) ⬝ prod (idp x') β :=
  begin induction α; induction β; reflexivity end

  hott definition t : p ⬝ q = q ⬝ p :=
  Φ Circle.loop Circle.loop
end Torus

end HITs

namespace Types.Integer
  hott definition succPath := ua Integer.succEquiv

  hott definition shift : ℤ → ℤ = ℤ :=
  HITs.Loop.power succPath

  hott definition shiftComp (z : ℤ) :
    shift z ⬝ succPath = shift (Integer.succ z) :=
  HITs.Loop.powerComp succPath z
end Types.Integer

end GroundZero
