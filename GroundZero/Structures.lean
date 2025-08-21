import GroundZero.Types.Unit
import GroundZero.Types.Sigma
import GroundZero.Types.Product
import GroundZero.Types.Coproduct

open GroundZero.HITs.Interval (happly funext)
open GroundZero.Types.Equiv (biinv)
open GroundZero.Types.Id (ap)
open GroundZero.Types.Unit
open GroundZero.Types
open GroundZero.Proto

namespace GroundZero
universe u v w k r w' w''

namespace Structures

hott definition isLoop {A : Type u} {a : A} (p : a = a) := ¬(p = idp a)

hott definition prop (A : Type u) := Π (a b : A), a = b
hott definition hset (A : Type u) := Π (a b : A) (p q : a = b), p = q

hott definition groupoid (A : Type u) :=
Π (a b : A) (p q : a = b) (α β : p = q), α = β

hott definition propset := Σ (A : Type u), prop A
hott definition hsetset := Σ (A : Type u), hset A

macro (priority := high) "Prop" : term => `(propset)
macro (priority := high) "Prop" n:(ppSpace level:max) : term => `(propset.{$n})

macro "Set" : term => `(hsetset)
macro "Set" n:(ppSpace level:max) : term => `(hsetset.{$n})

section
  open Lean Lean.PrettyPrinter.Delaborator

  @[delab app.GroundZero.Structures.propset]
  def delabPropSet : Delab :=
  Meta.Notation.delabCustomSort `(Prop) (λ n, `(Prop $n))

  @[delab app.GroundZero.Structures.hsetset]
  def delabHSetSet : Delab :=
  Meta.Notation.delabCustomSort `(Set) (λ n, `(Set $n))
end

hott definition dec (A : Type u) := A + ¬A

hott definition decEq (A : Type u) := Π (a b : A), dec (a = b)

notation "dec⁼" => decEq

hott definition contr (A : Type u) := Σ (a : A), Π b, a = b

hott remark inhContr {A : Type u} : contr A → A := Sigma.fst

inductive hlevel
| minusTwo : hlevel
| succ     : hlevel → hlevel

notation "ℕ₋₂" => hlevel
notation "−2"  => hlevel.minusTwo
notation "−1"  => hlevel.succ hlevel.minusTwo

namespace hlevel
  hott definition pred : ℕ₋₂ → ℕ₋₂
  | −2     => minusTwo
  | succ n => n

  inductive le : ℕ₋₂ → ℕ₋₂ → Type
  | refl (a : ℕ₋₂)   : le a a
  | step (a b : ℕ₋₂) : le a b → le a (succ b)

  infix:50 " ≤ " => le

  hott definition le.minusTwo : Π (n : ℕ₋₂), −2 ≤ n
  | −2     => le.refl −2
  | succ n => le.step _ _ (le.minusTwo n)

  hott definition le.succ (a b : ℕ₋₂) (ρ : a ≤ b) : succ a ≤ succ b :=
  begin induction ρ; apply le.refl; apply le.step; assumption end

  hott def addNat : ℕ₋₂ → ℕ → ℕ₋₂
  | n, 0          => n
  | n, Nat.succ m => succ (addNat n m)

  hott definition predPred : ℕ → ℕ₋₂
  | Nat.zero   => −2
  | Nat.succ n => succ (predPred n)

  hott definition succSucc : ℕ₋₂ → ℕ
  | −2     => Nat.zero
  | succ n => Nat.succ (succSucc n)

  hott definition add : ℕ₋₂ → ℕ₋₂ → ℕ₋₂
  | n, −2            => pred (pred n)
  | n, −1            => pred n
  | n, succ (succ m) => addNat n (succSucc m)

  hott lemma predPredSuccSucc : Π n, predPred (succSucc n) = n
  | −2     => idp −2
  | succ n => ap succ (predPredSuccSucc n)

  hott lemma succSuccPredPred : Π k, succSucc (predPred k) = k
  | Nat.zero   => idp 0
  | Nat.succ k => ap Nat.succ (succSuccPredPred k)

  hott lemma addNatMinusTwo : Π n, addNat −2 n = predPred n
  | Nat.zero   => idp −2
  | Nat.succ n => ap succ (addNatMinusTwo n)

  hott lemma addNatMinusOne : Π n, addNat −1 n = succ (predPred n)
  | Nat.zero   => idp −1
  | Nat.succ n => ap succ (addNatMinusOne n)

  hott corollary minusTwoAdd : Π n, add −2 n = pred (pred n)
  | −2            => idp −2
  | −1            => idp −2
  | succ (succ n) => addNatMinusTwo (succSucc n) ⬝ predPredSuccSucc n

  hott corollary minusOneAdd : Π n, add −1 n = pred n
  | −2            => idp −2
  | −1            => idp −2
  | succ (succ n) => addNatMinusOne (succSucc n) ⬝ ap succ (predPredSuccSucc n)

  hott lemma addNatToAdd : Π n m, addNat n (succSucc m) = predPred (succSucc n + succSucc m)
  | n, −2     => (predPredSuccSucc n)⁻¹
  | n, succ m => ap succ (addNatToAdd n m)

  hott lemma addNatSuccSucc : Π n m, addNat (succ (succ n)) m = succ (succ (addNat n m))
  | n, Nat.zero   => idp (succ (succ n))
  | n, Nat.succ m => ap succ (addNatSuccSucc n m)

  hott lemma addSuccSucc : Π n m, add (succ (succ n)) m = addNat n (succSucc m)
  | n, −2            => idp n
  | n, −1            => idp (succ n)
  | n, succ (succ m) => addNatSuccSucc n (succSucc m)

  hott instance : HAdd ℕ₋₂ ℕ₋₂ ℕ₋₂ := ⟨add⟩

  hott definition ofNat (n : ℕ) : ℕ₋₂ :=
  succ (succ (predPred n))

  hott instance (n : ℕ) : OfNat ℕ₋₂ n := ⟨ofNat n⟩
  hott instance : Coe ℕ ℕ₋₂ := ⟨ofNat⟩
end hlevel

hott definition isNType : hlevel → Type u → Type u
| −2            => contr
| hlevel.succ n => λ A, Π (x y : A), isNType n (x = y)

notation "is-" n:max "-type" => isNType n

hott definition nType (n : hlevel) : Type (u + 1) :=
Σ (A : Type u), is-n-type A

notation n:max "-Type" => nType n
macro n:term "-Type" l:level : term => `(nType.{$l} $n)

hott lemma hlevel.cumulative {A : Type u} : Π (n : hlevel), is-n-type A → is-(hlevel.succ n)-type A
| −2,            H => λ x y, ⟨(H.2 x)⁻¹ ⬝ H.2 y, λ p, begin induction p; apply Id.invComp end⟩
| hlevel.succ n, H => λ x y, hlevel.cumulative n (H x y)

hott corollary hlevel.strongCumulative (n m : hlevel) (ρ : n ≤ m) :
  Π {A : Type u}, (is-n-type A) → (is-m-type A) :=
begin
  induction ρ; intros; assumption;
  { case step m ρ ih =>
    intros A G; apply @hlevel.cumulative;
    apply ih; assumption }
end

hott definition isTruncated {A : Type u} {B : Type v} (n : ℕ₋₂) (f : A → B) :=
Π (b : B), is-n-type (fib f b)

notation "is-" n "-truncated" => isTruncated n

hott lemma contrImplProp {A : Type u} (H : contr A) : prop A :=
λ a b, (H.2 a)⁻¹ ⬝ (H.2 b)

hott theorem emptyIsProp : prop 𝟎 :=
begin intros x y; induction x end

hott theorem unitIsContr : contr 𝟏 :=
⟨★, λ ★, idp ★⟩

hott corollary unitIsProp : prop 𝟏 :=
contrImplProp unitIsContr

hott lemma contrEquivUnit {A : Type u} (H : contr A) : A ≃ 𝟏 :=
begin
  existsi (λ _, ★); apply Types.Qinv.toBiinv;
  existsi (λ _, H.1) <;> apply Prod.mk <;> intro x;
  induction x; reflexivity; apply H.2
end

hott lemma zeroMorphismContr {A : Type u} : contr (A → 𝟏) :=
⟨λ _, ★, λ f, HITs.Interval.funext (λ x, unitIsProp ★ (f x))⟩

hott lemma zeroMorphismEqv {A : Type u} : (A → 𝟏) ≃ 𝟏 :=
contrEquivUnit zeroMorphismContr

hott lemma familyOverUnit (C : 𝟏 → Type u) : (Π x, C x) ≃ (C ★) :=
begin
  fapply Sigma.mk; { intro φ; apply φ }; apply Types.Qinv.toBiinv;
  fapply Sigma.mk; { intros c x; induction x; exact c };
  fapply Prod.mk; { intro x; reflexivity };
  { intro ψ; apply HITs.Interval.funext; intro x; induction x; reflexivity }
end

hott lemma cozeroMorphismEqv {A : Type u} : (𝟏 → A) ≃ A :=
familyOverUnit (λ _, A)

hott lemma terminalArrow {A : Type u} : A ≃ (𝟏 → A) :=
⟨λ x _, x, Types.Qinv.toBiinv _ ⟨λ φ, φ ★, (λ φ, funext (λ ★, idp _), idp)⟩⟩

hott lemma contrTypeEquiv {A : Type u} {B : Type v}
  (H : contr A) (G : contr B) : A ≃ B :=
calc A ≃ 𝟏 : contrEquivUnit.{_, 0} H,
       ≃ B : (contrEquivUnit G).symm

hott lemma prodUnitEquiv (A : Type u) : 𝟏 × A ≃ A :=
begin existsi Prod.snd; apply Prod.mk <;> existsi Prod.mk ★ <;> { intro; reflexivity } end

hott lemma unitProdEquiv (A : Type u) : A × 𝟏 ≃ A :=
begin existsi Prod.fst; apply Prod.mk <;> existsi (Prod.mk · ★) <;> { intro x; reflexivity } end

hott lemma neqBoolToEqNot : Π (x y : 𝟐), ¬(x = y) → x = not y
| false, false, np => explode (np (idp false))
| false, true,  _  => idp false
| true,  false, _  => idp true
| true,  true,  np => explode (np (idp true))

hott definition boolToUniverse : 𝟐 → Type
| true => 𝟏 | false => 𝟎

hott theorem ffNeqTt : false ≠ true :=
λ p, Types.Equiv.transport boolToUniverse p⁻¹ ★

hott remark functionSpace : ¬(Π (A B : Type), prop (A → B)) :=
λ H, ffNeqTt (happly (H 𝟐 𝟐 id not) false)

hott lemma autoContr {A : Type u} (x : A) (H : prop (A → A)) : prop A :=
begin apply contrImplProp; existsi x; apply happly; apply H end

section
  open Types.Equiv Types.Id

  hott theorem propIsSet {A : Type u} (r : prop A) : hset A :=
  λ x y p q, transCancelLeft _ _ _ ((transportComposition p (r x x))⁻¹ ⬝
                                    apd (r x) p ⬝ (apd (r x) q)⁻¹ ⬝
                                    transportComposition q (r x x))

  hott corollary setImplGroupoid {A : Type u} (r : hset A) : groupoid A :=
  begin intro a b; apply propIsSet; apply r end

  hott corollary emptyIsSet : hset 𝟎 := propIsSet emptyIsProp
  hott corollary unitIsSet  : hset 𝟏 := propIsSet unitIsProp

  hott theorem contrIsProp {A : Type u} : prop (contr A) :=
  begin
    intro ⟨x, u⟩ ⟨y, v⟩; have p := u y;
    induction p; apply ap;
    apply HITs.Interval.funext; intro a;
    apply propIsSet (contrImplProp ⟨x, u⟩)
  end

  hott lemma propIsProp {A : Type u} : prop (prop A) :=
  begin
    intros f g; repeat first | (apply HITs.Interval.funext; intro)
                             | (apply propIsSet; assumption)
  end

  hott lemma setIsProp {A : Type u} : prop (hset A) :=
  begin
    intros f g; repeat first | (apply HITs.Interval.funext; intro)
                             | (apply setImplGroupoid; assumption)
  end

  hott lemma ntypeIsProp : Π (n : hlevel) {A : Type u}, prop (is-n-type A)
  | −2            => contrIsProp
  | hlevel.succ n => λ p q, HITs.Interval.funext (λ x, HITs.Interval.funext (λ y, ntypeIsProp n _ _))

  hott lemma functionToContr {A : Type u} : prop (A → contr A) :=
  begin intros f g; apply HITs.Interval.funext; intro x; apply contrIsProp end
end

hott definition retract (B : Type u) (A : Type v) :=
Σ (r : A → B) (s : B → A), r ∘ s ~ id

hott definition retract.section {B : Type u} {A : Type v} (w : retract B A) : B → A := w.2.1

hott lemma contrRetract {A : Type u} {B : Type v} : retract B A → contr A → contr B :=
λ ⟨r, s, ε⟩ ⟨a₀, p⟩, ⟨r a₀, λ b, ap r (p (s b)) ⬝ (ε b)⟩

hott definition retract.path {A : Type u} {B : Type v} :
  Π (H : retract B A) {a b : B}, retract (a = b) (H.section a = H.section b) :=
λ ⟨r, s, ε⟩ a b, ⟨λ q, (ε a)⁻¹ ⬝ (@ap A B _ _ r q) ⬝ (ε b), ap s,
begin
  intro p; transitivity; symmetry; apply Types.Id.assoc;
  symmetry; apply Types.Equiv.invRewriteComp;
  transitivity; apply ap (· ⬝ p); apply Types.Id.invInv;
  transitivity; apply ap (ε a ⬝ ·); symmetry; apply Types.Equiv.idmap;
  transitivity; apply Types.Equiv.homotopySquare ε p;
  apply ap (· ⬝ ε b); apply Types.Equiv.mapOverComp
end⟩

hott theorem equivRespectsRetraction : Π {n : ℕ₋₂} {A : Type u} {B : Type v},
  retract B A → is-n-type A → is-n-type B
| −2            => contrRetract
| hlevel.succ n => λ G H a b, equivRespectsRetraction (retract.path G) (H _ _)

hott corollary equivInducesRetraction {A : Type u} {B : Type v} : A ≃ B → retract B A :=
λ ⟨f, (_, ⟨g, ε⟩)⟩, ⟨f, g, ε⟩

hott theorem ntypeRespectsEquiv (n : ℕ₋₂) {A : Type u} {B : Type v} :
  A ≃ B → is-n-type A → is-n-type B :=
equivRespectsRetraction ∘ equivInducesRetraction

hott lemma contrRespectsSigma {A : Type u} {B : A → Type v} :
  contr A → (Π x, contr (B x)) → contr (Σ x, B x) :=
λ ⟨a₀, p⟩ w, ⟨⟨a₀, (w a₀).1⟩, λ ⟨a, b⟩, Sigma.prod (p a) (contrImplProp (w a) _ _)⟩

hott theorem ntypeRespectsSigma : Π (n : ℕ₋₂) {A : Type u} {B : A → Type v},
  is-n-type A → (Π x, is-n-type (B x)) → is-n-type (Σ x, B x)
| −2            => contrRespectsSigma
| hlevel.succ n => λ A B p q, ntypeRespectsEquiv n Sigma.sigmaPath.symm (ntypeRespectsSigma n (A p.1 q.1) (λ x, B q.1 _ _))

hott corollary ntypeRespectsProd (n : ℕ₋₂) {A : Type u} {B : Type v} :
  is-n-type A → is-n-type B → is-n-type (A × B) :=
begin
  intro G H; apply ntypeRespectsEquiv; apply Types.Sigma.const;
  apply ntypeRespectsSigma; exact G; intro; exact H
end

inductive propSquash (A : Type u) : Sort 0
| elem : A → propSquash A

inductive Lift (A : Sort 0) : Type
| elem : A → Lift A

hott definition Squash := Lift ∘ propSquash

hott definition Squash.elem {A : Type u} : A → Squash A :=
Lift.elem ∘ propSquash.elem

hott definition Squash.uniq {A : Type u} : Π (a b : Squash A), a = b :=
λ (Lift.elem _) (Lift.elem _), idp _

hott definition Squash.prop {A : Type u} {B : Sort 0} (f : A → B) : Squash A → B :=
λ (Lift.elem (propSquash.elem x)), f x

hott definition Squash.Lift {A : Type u} {B : Type v}
  (f : A → B) : Squash A → Squash B :=
Lift.elem ∘ Squash.prop (propSquash.elem ∘ f)

hott definition K (A : Type u) :=
Π (a : A) (p : a = a), p = idp a

hott lemma KIffSet (A : Type u) : K A ↔ hset A :=
begin
  fapply Prod.mk;
  { intros H x y p q; induction q; apply H };
  { intros H a p; apply H }
end

hott lemma lemProp {A : Type u} (h : A → prop A) : prop A :=
λ a, h a a

hott lemma lemContr {A : Type u} (h : A → contr A) : prop A :=
λ a, contrImplProp (h a) a

hott definition isContrFiber {A : Type u} {B : Type v} (f : A → B) :=
Π (y : B), contr (fib f y)

hott lemma propEquivLemma {A : Type u} {B : Type v}
  (F : prop A) (G : prop B) (f : A → B) (g : B → A) : A ≃ B :=
⟨f, (⟨g, λ _, F _ _⟩, ⟨g, λ _, G _ _⟩)⟩

hott corollary propIffLemma {A : Type u} {B : Type v} : prop A → prop B → A ↔ B → A ≃ B :=
λ F G φ, propEquivLemma F G φ.1 φ.2

hott statement minusTwoEqvContr {A : Type u} : (is-(−2)-type A) ≃ contr A :=
by reflexivity

hott lemma minusOneEqvProp {A : Type u} : (is-(−1)-type A) ≃ prop A :=
begin
  apply propEquivLemma; apply ntypeIsProp; apply propIsProp;
  { intros H a b; exact (H a b).1 };
  { intros H a b; existsi H a b; apply propIsSet H }
end

hott theorem equivFunext {A : Type u} {B : A → Type v} {C : A → Type w}
  (H : Π x, B x ≃ C x) : (Π x, B x) ≃ (Π x, C x) :=
begin
  existsi (λ (f : Π x, B x) (x : A), (H x).forward (f x)); apply Prod.mk;
  { existsi (λ (f : Π x, C x) (x : A), (H x).left (f x));
    intro f; apply HITs.Interval.funext;
    intro x; apply (H x).leftForward };
  { existsi (λ (f : Π x, C x) (x : A), (H x).right (f x));
    intro f; apply HITs.Interval.funext;
    intro x; apply (H x).forwardRight }
end

hott lemma zeroEqvSet {A : Type u} : (is-0-type A) ≃ hset A :=
calc (is-0-type A) ≃ (Π (x y : A), is-(−1)-type (x = y)) : by reflexivity,
                   ≃ (Π (x y : A), prop (x = y)) :
                     begin apply equivFunext; intro x;
                           apply equivFunext; intro y;
                           apply minusOneEqvProp end,
                   ≃ hset A : by reflexivity

hott lemma oneEqvGroupoid {A : Type u} : (is-1-type A) ≃ groupoid A :=
calc (is-1-type A) ≃ (Π (x y : A), is-0-type (x = y)) : by reflexivity,
                   ≃ (Π (x y : A), hset (x = y)) :
                      begin apply equivFunext; intro x;
                            apply equivFunext; intro y;
                            apply zeroEqvSet end,
                   ≃ groupoid A : by reflexivity

hott lemma propIsNType {A : Type u} (H : prop A) : Π n, is-(hlevel.succ n)-type A
| −2            => minusOneEqvProp.left H
| hlevel.succ n => hlevel.cumulative (hlevel.succ n) (propIsNType H n)

hott corollary hsetRespectsEquiv {A : Type u} {B : Type v} : A ≃ B → hset A → hset B :=
begin
  intros e H; apply zeroEqvSet.forward; apply ntypeRespectsEquiv 0 e;
  apply zeroEqvSet.left; assumption
end

hott corollary hsetRespectsSigma {A : Type u} {B : A → Type v}
  (H : hset A) (G : Π x, hset (B x)) : hset (Σ x, B x) :=
begin
  apply zeroEqvSet.forward; apply ntypeRespectsSigma 0;
  { apply zeroEqvSet.left; intros x y; apply H };
  { intro x; apply zeroEqvSet.left; apply G }
end

hott corollary propRespectsEquiv {A : Type u} {B : Type v} : A ≃ B → prop A → prop B :=
begin
  intros e H; apply minusOneEqvProp.forward;
  apply ntypeRespectsEquiv −1 e;
  apply minusOneEqvProp.left;
  assumption
end

hott corollary contrRespectsEquiv {A : Type u} {B : Type v} : A ≃ B → contr A → contr B :=
ntypeRespectsEquiv −2

hott theorem productProp {A : Type u} {B : Type v} (H : prop A) (G : prop B) : prop (A × B) :=
begin intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩; apply Types.Product.prod; apply H; apply G end

hott corollary prodHset {A : Type u} {B : Type v}
  (H : hset A) (G : hset B) : hset (A × B) :=
begin
  apply hsetRespectsEquiv; apply Types.Sigma.const;
  apply hsetRespectsSigma; apply H; intro x; apply G
end

hott lemma piProp {A : Type u} {B : A → Type v}
  (H : Π x, prop (B x)) : prop (Π x, B x) :=
λ f g, HITs.Interval.funext (λ x, H x (f x) (g x))

hott lemma sigProp {A : Type u} {B : A → Type v}
  (H : prop A) (G : Π x, prop (B x)) : prop (Σ x, B x) :=
begin intros w₁ w₂; fapply Types.Sigma.prod; apply H; apply G end

hott corollary implProp {A : Type u} {B : Type v} (H : prop B) : prop (A → B) :=
piProp (λ _, H)

hott corollary notIsProp {A : Type u} : prop (¬ A) :=
implProp emptyIsProp

hott lemma reflMereRel {A : Type u} (R : A → A → Type v) (h : Π x y, prop (R x y))
  (ρ : Π x, R x x) (f : Π x y, R x y → x = y) : hset A :=
begin
  apply (KIffSet _).left; intros a p;
  apply Types.Id.transCancelLeft (f a a (ρ a));
  transitivity; symmetry; apply Types.Equiv.transportComposition;
  transitivity; apply Types.Equiv.liftedHapply (R a); apply Types.Equiv.apd (f a) p;
  transitivity; apply ap (f a a) (h _ _ _ (ρ a)); symmetry; apply Types.Id.rid
end

hott lemma doubleNegEq {A : Type u} (h : Π (x y : A), ¬¬(x = y) → x = y) : hset A :=
begin
  fapply reflMereRel;
  { intros x y; exact ¬¬(x = y) };
  { intros x y; apply implProp; apply emptyIsProp };
  { intro x; intros f; apply f; reflexivity };
  { exact h }
end

hott lemma lemToDoubleNeg {A : Type u} : dec A → (¬¬A → A)
| Sum.inl x => λ _, x
| Sum.inr t => λ g, explode (g t)

hott theorem Hedberg {A : Type u} : dec⁼ A → hset A :=
begin intro H; apply doubleNegEq; intros x y; apply lemToDoubleNeg; apply H x y end

hott remark boolEqTotal (x : 𝟐) : (x = false) + (x = true) :=
begin induction x using Bool.casesOn; left; reflexivity; right; reflexivity end

hott lemma boolDecEq (x y : 𝟐) : dec (x = y) :=
begin
  induction x using Bool.casesOn <;>
  induction y using Bool.casesOn;
  { left; reflexivity };
  { right; apply ffNeqTt };
  { right; intro p; apply ffNeqTt; exact p⁻¹ };
  { left; reflexivity }
end

hott corollary boolIsSet : hset 𝟐 :=
Hedberg boolDecEq

section
  open GroundZero.Types.Not (univ)
  open GroundZero.Types.Coproduct
  open GroundZero.Types

  variable {A : Type u} {B : Type v}

  hott theorem decOverEqv (e : A ≃ B) (H : dec A) : dec B :=
  match H with | inl x => inl (e x) | inr φ => inr (φ ∘ e.left)

  hott theorem decCoproduct (H : dec⁼ A) (G : dec⁼ B) : dec⁼ (A + B)
  | inl a, inl b => decOverEqv (Equiv.symm (inl.inj' a b)) (H a b)
  | inl _, inr _ => inr (univ ∘ inl.encode)
  | inr _, inl _ => inr (univ ∘ inr.encode)
  | inr a, inr b => decOverEqv (Equiv.symm (inr.inj' a b)) (G a b)
end

section
  open GroundZero.Types
  hott definition zeroPath {A B : 0-Type} (p : A.fst = B.fst) : A = B :=
  begin fapply Sigma.prod; exact p; apply ntypeIsProp end

  hott lemma zeroPathRefl (A : 0-Type) : @zeroPath A A (idp A.1) = idp A :=
  begin
    transitivity; apply ap (Sigma.prod (idp _)); change _ = idp _;
    apply propIsSet (ntypeIsProp 0); apply Sigma.prodRefl
  end
end

hott definition Identity.ens {A : Type u} (H : hset A) : hset (Identity A) :=
begin apply hsetRespectsEquiv; apply Types.Equiv.identityEqv; assumption end

hott definition zeroEquiv (A B : 0-Type) := A.1 ≃ B.1
infix:25 " ≃₀ " => zeroEquiv

section
  open GroundZero.Types.Equiv
  open GroundZero.Types

  hott lemma sigmaProdInjHSet {A : Type u} {B : A → Type v} {x : A} {u v : B x}
    (H : hset A) : @Id (Σ x, B x) ⟨x, u⟩ ⟨x, v⟩ → u = v :=
  λ p, ap (transport B · u) (H x x (idp x) (ap Sigma.fst p)) ⬝
       (@transportComp (Σ x, B x) A B ⟨x, u⟩ ⟨x, v⟩ Sigma.fst p u)⁻¹ ⬝
       apd Sigma.snd p
end

end Structures

-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/tiny-library.html
-- http://www.cs.bham.ac.uk/~mhe/truncation-and-extensionality/hsetfunext.html
hott definition singl {A : Type u} (a : A) := Σ b, a = b

namespace singl
  hott definition trivialLoop {A : Type u} (a : A) : singl a :=
  ⟨a, by reflexivity⟩

  hott definition pathFromTrivialLoop {A : Type u} {a b : A}
    (r : a = b) : trivialLoop a = ⟨b, r⟩ :=
  begin induction r; reflexivity end

  hott definition contr {A : Type u} (a : A) : Structures.contr (singl a) :=
  ⟨trivialLoop a, λ t, pathFromTrivialLoop t.2⟩

  hott definition prop {A : Type u} (a : A) : Structures.prop (singl a) :=
  Structures.contrImplProp (contr a)
end singl

namespace Theorems
  open GroundZero.Structures GroundZero.Types.Equiv GroundZero.Types
  open GroundZero.HITs.Interval (happly)

  hott theorem naive {A : Type u} {B : A → Type v} {f g : Π x, B x} : f ~ g → f = g :=
  HITs.Interval.funext

  hott theorem weak {A : Type u} {B : A → Type v} (H : Π x, contr (B x)) : contr (Π x, B x) :=
  begin existsi (λ x, (H x).1); intro f; apply naive; intro x; apply (H x).2 end

  section
    variable {A : Type u} {B : A → Type v}

    hott theorem isContrSigmaHomotopy (f : Π x, B x) : contr (Σ g, f ~ g) :=
    let r (k : Π x, Σ y, f x = y) :=
    @Sigma.mk _ (λ g, f ~ g) (λ x, (k x).1) (λ x, (k x).2);
    let s (g : Π x, B x) (h : f ~ g) x :=
    Sigma.mk (g x) (h x);
    begin
      existsi Sigma.mk f (Homotopy.id f); intro ⟨g, H⟩;
      change r (λ x, Sigma.mk (f x) (idp _)) = r (s g H);
      apply ap r; apply contrImplProp;
      apply weak; intro x; apply singl.contr
    end

    variable (f : Π x, B x) {C : Π g, f ~ g → Type w} (r : C f (Homotopy.id f))

    hott definition homotopyInd (g : Π x, B x) (h : f ~ g) : C g h :=
    @transport (Σ g, f ~ g) (λ (p : Σ g, f ~ g), C p.fst p.snd)
      ⟨f, Homotopy.id f⟩ ⟨g, h⟩ (contrImplProp (isContrSigmaHomotopy f) _ _) r

    hott lemma homotopyIndId : homotopyInd f r f (Homotopy.id f) = r :=
    begin
      transitivity; apply ap
        (λ p, @transport (Σ g, f ~ g) (λ p, C p.fst p.snd)
           ⟨f, Homotopy.id f⟩ ⟨f, Homotopy.id f⟩ p r);
      change _ = idp _; apply propIsSet; apply contrImplProp;
      apply isContrSigmaHomotopy; reflexivity
    end
  end

  hott definition funext {A : Type u} {B : A → Type v}
    {f g : Π x, B x} : (f ~ g) → (f = g) :=
  @homotopyInd _ _ f (λ g x, f = g) (idp _) g

  hott lemma funextHapply {A : Type u} {B : A → Type v}
    {f g : Π x, B x} : funext ∘ @happly A B f g ~ id :=
  begin
    intro p; induction p; change funext (Homotopy.id _) = idp _;
    dsimp [funext]; apply homotopyIndId f
  end

  hott lemma happlyFunext {A : Type u} {B : A → Type v}
    (f g : Π x, B x) : happly ∘ @funext A B f g ~ id :=
  begin
    intro H; fapply @homotopyInd _ _ f (λ g G, happly (funext G) = G) _ g H;
    change _ = happly (idp _); apply ap happly;
    change homotopyInd _ _ _ _ = _; apply homotopyIndId
  end

  hott theorem full {A : Type u} {B : A → Type v} {f g : Π x, B x} : (f = g) ≃ (f ~ g) :=
  begin
    existsi happly; apply Qinv.toBiinv; existsi funext;
    apply Prod.mk; apply happlyFunext; apply funextHapply
  end

  hott corollary funextId {A : Type u} {B : A → Type v}
    {f : Π x, B x} : funext (Homotopy.id f) = idp f :=
  homotopyIndId _ _

  open GroundZero.Types.Equiv (transport)
  hott lemma mapHomotopy {A : Type u} {B : Type v} {a b : A} (f g : A → B) (p : a = b) (q : f ~ g) :
    ap g p = @transport (A → B) (λ h, h a = h b) f g (funext q) (ap f p) :=
  begin
    induction p; symmetry; transitivity; apply Types.Equiv.transportOverHmtpy;
    transitivity; apply ap (· ⬝ ap (λ (h : A → B), h a) (funext q));
    apply Id.rid; transitivity; symmetry; apply mapFunctoriality (λ (h : A → B), h a);
    transitivity; apply ap; apply Id.invComp; reflexivity
  end

  hott lemma mapToHapply {A : Type u} {B : A → Type v}
    (c : A) (f g : Π x, B x) (p : f = g) :
    ap (λ (f : Π x, B x), f c) p = happly p c :=
  begin induction p; reflexivity end

  hott lemma mapToHapply₂ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
    (c₁ : A) (c₂ : B c₁) (f g : Π (x : A) (y : B x), C x y) (p : f = g) :
    ap (λ f, f c₁ c₂) p = happly (happly p c₁) c₂ :=
  begin induction p; reflexivity end

  hott lemma mapToHapply₃ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
    {D : Π x y, C x y → Type w'} (c₁ : A) (c₂ : B c₁) (c₃ : C c₁ c₂) (f g : Π x y z, D x y z) (p : f = g) :
    ap (λ f, f c₁ c₂ c₃) p = happly (happly (happly p c₁) c₂) c₃ :=
  begin induction p; reflexivity end

  hott lemma mapToHapply₄ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
    {D : Π (x : A) (y : B x), C x y → Type w'} {E : Π (x : A) (y : B x) (z : C x y), D x y z → Type w''}
    (c₁ : A) (c₂ : B c₁) (c₃ : C c₁ c₂) (c₄ : D c₁ c₂ c₃) (f g : Π x y z w, E x y z w) (p : f = g) :
    ap (λ f, f c₁ c₂ c₃ c₄) p = happly (happly (happly (happly p c₁) c₂) c₃) c₄ :=
  begin induction p; reflexivity end

  hott lemma happlyFunextPt {A : Type u} {B : A → Type v} {f g : Π x, B x} (H : f ~ g) (x : A) : happly (funext H) x = H x :=
  begin apply happly; apply happlyFunext end

  hott lemma happlyFunextPt₂ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
    {f g : Π x y, C x y} (H : Π x y, f x y = g x y) (c₁ : A) (c₂ : B c₁) :
    happly (happly (funext (λ x, funext (H x))) c₁) c₂ = H c₁ c₂ :=
  begin transitivity; apply ap (happly · c₂); apply happlyFunextPt; apply happlyFunextPt end

  hott lemma happlyFunextPt₃ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
    {D : Π x y, C x y → Type w'} {f g : Π x y z, D x y z}
    (H : Π x y z, f x y z = g x y z) (c₁ : A) (c₂ : B c₁) (c₃ : C c₁ c₂) :
    happly (happly (happly (funext (λ x, funext (λ y, funext (H x y)))) c₁) c₂) c₃ = H c₁ c₂ c₃ :=
  begin transitivity; apply ap (happly · c₃); apply happlyFunextPt₂; apply happlyFunextPt end

  hott lemma happlyFunextPt₄ {A : Type u} {B : A → Type v} {C : Π x, B x → Type w}
    {D : Π x y, C x y → Type w'} {E : Π x y z, D x y z → Type w''} {f g : Π x y z w, E x y z w}
    (H : Π x y z w, f x y z w = g x y z w) (c₁ : A) (c₂ : B c₁) (c₃ : C c₁ c₂) (c₄ : D c₁ c₂ c₃) :
    happly (happly (happly (happly (funext (λ x, funext (λ y, funext (λ z, funext (H x y z))))) c₁) c₂) c₃) c₄ = H c₁ c₂ c₃ c₄ :=
  begin transitivity; apply ap (happly · c₄); apply happlyFunextPt₃; apply happlyFunextPt end

  hott lemma happlyRevPt {A : Type u} {B : A → Type v} {f g : Π x, B x} (p : f = g) (x : A) :
    happly p⁻¹ x = Homotopy.symm f g (happly p) x :=
  begin apply happly; apply HITs.Interval.happlyRev end
end Theorems

namespace Structures
  hott theorem piRespectsNType :
    Π (n : ℕ₋₂) {A : Type u} {B : A → Type v},
      (Π x, is-n-type (B x)) → is-n-type (Π x, B x)
  | −2            => λ H, ⟨λ x, (H x).1, λ φ, Theorems.funext (λ x, (H x).2 (φ x))⟩
  | hlevel.succ n => λ H f g, ntypeRespectsEquiv n (Types.Equiv.symm Theorems.full)
                                (piRespectsNType n (λ x, H x _ _))

  hott corollary piRespectsImpl (n : ℕ₋₂) {A : Type u} {B : Type v} (H : is-n-type B) : is-n-type (A → B) :=
  piRespectsNType n (λ _, H)

  hott corollary piHset {A : Type u} {B : A → Type v}
    (H : Π x, hset (B x)) : hset (Π x, B x) :=
  begin
    apply zeroEqvSet.forward; apply piRespectsNType 0;
    intro x; apply zeroEqvSet.left; apply H
  end
end Structures

hott definition iter (A B : Type) : ℕ → Type
| Nat.zero   => B
| Nat.succ n => Coproduct (iter A B n) A

hott definition pt := iter 𝟏

hott definition vect (A : Type u) : ℕ → Type u
| Nat.zero   => 𝟏
| Nat.succ n => A × vect A n

hott definition vect.const {A : Type u} (a : A) : Π n, vect A n
| Nat.zero   => ★
| Nat.succ n => (a, vect.const a n)

hott definition vect.map {A : Type u} {B : Type v} (f : A → B) :
  Π {n : ℕ}, vect A n → vect B n
| Nat.zero   => λ _, ★
| Nat.succ n => λ v, (f v.1, vect.map f v.2)

section
  open GroundZero.Types.Equiv (transportOverProduct transport)
  open GroundZero.Types

  hott lemma vect.subst {A B : Type u} (p : A = B) (f : B → A) {n : ℕ} (v : vect A n) :
    vect.map f (transport (vect · n) p v) = vect.map (f ∘ transport id p) v :=
  begin induction p; reflexivity end
end

hott theorem vect.idfunc {A : Type u} : Π {n : ℕ} (f : A → A)
  (H : f ~ id) (v : vect A n), vect.map f v = v
| Nat.zero,   f, H, v => idp v
| Nat.succ n, f, H, v => Product.prod (H v.1) (vect.idfunc f H v.2)

hott corollary vect.id {A : Type u} {n : ℕ} (v : vect A n) : vect.map id v = v :=
begin apply vect.idfunc; reflexivity end

hott theorem vect.comp {A : Type u} {B : Type v} {γ : Type w} :
  Π {n : ℕ} (f : A → B) (g : B → γ) (v : vect A n), vect.map g (vect.map f v) = vect.map (g ∘ f) v
| Nat.zero,   f, g, v => idp _
| Nat.succ n, f, g, v => Product.prod (idp _) (vect.comp f g v.2)

hott lemma vect.constMap {A : Type u} {B : Type v} (a : A) (f : A → B) :
  Π {n : ℕ}, vect.map f (vect.const a n) = vect.const (f a) n
| Nat.zero   => idp _
| Nat.succ n => Product.prod (idp _) (vect.constMap a f)

hott definition Finite := iter 𝟏 𝟎

@[match_pattern] hott definition Finite.zero {n : ℕ} : Finite (n + 1) := Sum.inr ★
@[match_pattern] hott definition Finite.succ {n : ℕ} : Finite n → Finite (n + 1) := Sum.inl

open Structures (prop propset)
hott definition hrel (A : Type u) := A → A → Prop v

hott definition LEMinf := Π (A : Type u), A + ¬A
macro "LEM∞" : term => `(LEMinf)
macro "LEM∞" n:level : term => `(LEMinf.{$n})

hott definition LEMprop := Π (A : Type u), prop A → A + ¬A
macro "LEM₋₁" : term => `(LEMprop)
macro "LEM₋₁" n:level : term => `(LEMprop.{$n})

hott definition DNEGinf := Π (A : Type u), ¬¬A → A
macro "DNEG∞" : term => `(DNEGinf)
macro "DNEG∞" n:level : term => `(DNEGinf.{$n})

hott definition DNEGprop := Π (A : Type u), prop A → ¬¬A → A
macro "DNEG₋₁" : term => `(DNEGprop)
macro "DNEG₋₁" n:level : term => `(DNEGprop.{$n})

namespace Structures
  open GroundZero.Types.Coproduct (inl inr)
  open GroundZero.Types.Id (ap)

  hott theorem propSum {A : Type u} {B : Type v} (H₁ : prop A) (H₂ : prop B) (G : ¬(A × B)) : prop (A + B)
  | inl _, inl _ => ap inl (H₁ _ _)
  | inr x, inl y => explode (G (y, x))
  | inl x, inr y => explode (G (x, y))
  | inr _, inr _ => ap inr (H₂ _ _)

  hott corollary propEM {A : Type u} (H : prop A) : prop (A + ¬A) :=
  propSum H notIsProp (λ w, w.2 w.1)
end Structures

section
  variable {A : Type u} (R : hrel A)

  hott definition isrefl  := Π a, (R a a).1
  hott definition issymm  := Π a b, (R a b).1 → (R b a).1
  hott definition istrans := Π a b c, (R a b).1 → (R b c).1 → (R a c).1

  hott definition iseqrel := isrefl R × issymm R × istrans R
end

hott definition eqrel (A : Type u) := Σ φ, @iseqrel A φ

hott definition iseqrel.prop {A : Type u} {R : hrel A} : prop (iseqrel R) :=
begin
  apply Structures.productProp;
  { intros f g; apply Theorems.funext; intro x; apply (R x x).2 };
  apply Structures.productProp <;>
  { intros f g; repeat first | (apply Theorems.funext; intro)
                             | apply (R _ _).2 }
end

section
  variable {A : Type u} (R : eqrel.{u, v} A)

  hott definition eqrel.rel : hrel A := R.1
  hott definition eqrel.iseqv : iseqrel R.rel := R.2

  hott definition eqrel.apply (a b : A) : Type v :=
  (R.rel a b).1

  hott definition eqrel.prop (a b : A) : prop (R.apply a b) :=
  (R.rel a b).2

  -- Accessors
  hott definition eqrel.refl (a : A) : R.apply a a :=
  R.2.1 a

  hott definition eqrel.symm {a b : A} : R.apply a b → R.apply b a :=
  R.2.2.1 a b

  hott definition eqrel.trans {a b c : A} : R.apply a b → R.apply b c → R.apply a c :=
  R.2.2.2 a b c
end

hott definition eqrel.eq {A : Type u} {x y : eqrel A} (p : x.rel = y.rel) : x = y :=
begin apply Types.Sigma.prod p; apply iseqrel.prop end

hott definition iffOverPi {A : Type u} {B : A → Type v} {B' : A → Type w}
  (φ : Π x, B x ↔ B' x) : (Π x, B x) ↔ (Π x, B' x) :=
begin apply Prod.mk; { intros f x; apply (φ x).left; apply f }; { intros g x; apply (φ x).right; apply g } end

hott definition hcommSquare (P : Type k) (A : Type u) (B : Type v) (C : Type w) :=
Σ (f : A → C) (g : B → C) (h : P → A) (k : P → B), f ∘ h = g ∘ k

hott definition pullback {A : Type u} {B : Type v} (C : Type w) (f : A → C) (g : B → C) :=
Σ (p : A × B), f p.1 = g p.2

namespace hcommSquare
  variable {P : Type k} {A : Type u} {B : Type v} {C : Type w}

  hott definition top   (η : hcommSquare P A B C) : P → A := η.2.2.1
  hott definition bot   (η : hcommSquare P A B C) : B → C := η.2.1
  hott definition left  (η : hcommSquare P A B C) : P → B := η.2.2.2.1
  hott definition right (η : hcommSquare P A B C) : A → C := η.1

  hott definition naturality (η : hcommSquare P A B C) : η.right ∘ η.top = η.bot ∘ η.left := η.2.2.2.2

  hott definition induced (η : hcommSquare P A B C) (X : Type r) :
    (X → P) → @pullback (X → A) (X → B) (X → C) (λ f, right η ∘ f) (λ g, bot η ∘ g) :=
  λ φ, ⟨(top η ∘ φ, left η ∘ φ), @ap (P → C) (X → C) (right η ∘ top η) (bot η ∘ left η) (· ∘ φ) η.naturality⟩

  hott definition isPullback (η : hcommSquare P A B C) :=
  Π (X : Type (max u v w k)), biinv (induced η X)
end hcommSquare

hott definition pullbackSquare (P : Type k) (A : Type u) (B : Type v) (C : Type w) :=
Σ (η : hcommSquare P A B C), η.isPullback

namespace Types.Equiv
  open GroundZero.Structures
  universe u' v'

  -- 1-1 correspondence
  hott definition Corr (A : Type u) (B : Type v) :=
  Σ (R : A → B → Type w), (Π a, contr (Σ b, R a b)) × (Π b, contr (Σ a, R a b))

  open GroundZero.Types
  variable {A : Type u} {A' : Type v} {B : Type u'} {B' : Type v'}

  hott lemma prodBiinv {f : A → A'} {g : B → B'} (e₁ : biinv f) (e₂ : biinv g) : biinv (Product.bimap f g) :=
  (⟨Product.bimap e₁.1.1 e₂.1.1, λ w, Product.prod (e₁.1.2 w.1) (e₂.1.2 w.2)⟩,
   ⟨Product.bimap e₁.2.1 e₂.2.1, λ w, Product.prod (e₁.2.2 w.1) (e₂.2.2 w.2)⟩)

  hott theorem prodEquiv (e₁ : A ≃ A') (e₂ : B ≃ B') : (A × B) ≃ (A' × B') :=
  ⟨Product.bimap e₁.1 e₂.1, prodBiinv e₁.2 e₂.2⟩

  open GroundZero.Types.Coproduct (inl inr)
  open GroundZero.Types.Id (ap)

  hott lemma sumBiinv {f : A → A'} {g : B → B'} (e₁ : biinv f) (e₂ : biinv g) : biinv (Coproduct.bimap f g) :=
  (⟨Coproduct.bimap e₁.1.1 e₂.1.1, λ | inl x => ap inl (e₁.1.2 x) | inr y => ap inr (e₂.1.2 y)⟩,
   ⟨Coproduct.bimap e₁.2.1 e₂.2.1, λ | inl x => ap inl (e₁.2.2 x) | inr y => ap inr (e₂.2.2 y)⟩)

  hott theorem sumEquiv (e₁ : A ≃ A') (e₂ : B ≃ B') : (A + B) ≃ (A' + B') :=
  ⟨Coproduct.bimap e₁.1 e₂.1, sumBiinv e₁.2 e₂.2⟩

  hott definition meet {A : Type u} {a b : A} (p : a = b) : @Id (singl a) ⟨a, idp a⟩ ⟨b, p⟩ :=
  Sigma.prod p (transportComposition p (idp a))

  hott theorem transportMeetPi {X : Type u} {A : X → Type v} {B : Π x, A x → Type w}
    {a b : X} (p : a = b) (φ : Π (x : A a), B a x) (u : A b) :
       transport (λ x, Π (a : A x), B x a) p φ u
    = @transport (Σ x, b = x) (λ w, B w.1 (transport A w.2 u)) ⟨a, p⁻¹⟩ ⟨b, idp b⟩
                 (meet p⁻¹)⁻¹ (φ (transport A p⁻¹ u)) :=
  begin induction p; reflexivity end

  hott theorem transportMeetSigma {X : Type u} {A : X → Type v} {B : Π x, A x → Type w}
    {a b : X} (p : a = b) (w : Σ (x : A a), B a x) :
       transport (λ x, Σ (a : A x), B x a) p w
    = ⟨transport A p w.1, @transport (Σ x, a = x) (λ u, B u.1 (transport A u.2 w.1))
                                     ⟨a, idp a⟩ ⟨b, p⟩ (meet p) w.2⟩ :=
  begin induction p; reflexivity end

  hott theorem transportMeetPath {X : Type u} {A : X → Type v} {f g : Π x, A x}
    {a b : X} (p : a = b) (q : f a = g a) :
      transport (λ x, @Id (A x) (f x) (g x)) p q
    = (apd f p)⁻¹ ⬝ ap (transport A p) q ⬝ (apd g p) :=
  begin induction p; symmetry; transitivity; apply Id.rid; apply idmap end
end Types.Equiv

namespace Types.Id
  open GroundZero.HITs.Interval (happly)
  open GroundZero.Types.Equiv
  open GroundZero.Proto

  hott lemma happlyApΩ {A : Type u} {B : Type v} {f g : A → B} (H : f = g) {a : A}
    (n : ℕ) (α : Ωⁿ(A, a)) : apΩ f α = (apΩ g α)^(happly H a)⁻¹ :=
  begin induction H; reflexivity end

  hott lemma happlyApdΩ {A : Type u} {B : A → Type v} {f g : Π x, B x} (H : f = g) {a : A}
    (n : ℕ) (α : Ωⁿ(A, a)) : apdΩ f α = conjugateOverΩ (happly H a)⁻¹ (apdΩ g α) :=
  begin induction H; reflexivity end

  hott theorem apWithHomotopyΩ {A : Type u} {B : Type v} {f g : A → B} (H : f ~ g) {a : A}
    (n : ℕ) (α : Ωⁿ(A, a)) : apΩ f α = (apΩ g α)^(H a)⁻¹ :=
  happlyApΩ (Theorems.funext H) n α ⬝ ap (_^·⁻¹) (happly (Theorems.happlyFunext _ _ _) _)

  hott theorem apdWithHomotopyΩ {A : Type u} {B : A → Type v} {f g : Π x, B x} (H : f ~ g) {a : A}
    (n : ℕ) (α : Ωⁿ(A, a)) : apdΩ f α = conjugateOverΩ (H a)⁻¹ (apdΩ g α) :=
  happlyApdΩ (Theorems.funext H) n α ⬝ ap (conjugateOverΩ ·⁻¹ _) (happly (Theorems.happlyFunext _ _ _) _)

  hott lemma idmapΩ {A : Type u} {a : A} : Π (n : ℕ) (α : Ωⁿ(A, a)), apΩ idfun α = α
  | Nat.zero,   _ => idp _
  | Nat.succ _, _ => apWithHomotopyΩ idmap _ _ ⬝ idmapΩ _ _

  hott lemma constmapΩ {A : Type u} {B : Type v} {a : A} {b : B} : Π (n : ℕ) (α : Ωⁿ(A, a)), apΩ (λ _, b) α = idΩ b n
  | Nat.zero,   _ => idp _
  | Nat.succ n, _ => apWithHomotopyΩ constmap _ _ ⬝ constmapΩ _ _

  hott lemma conjugateSuccΩ {A : Type u} {a b : A} (p : a = b) (n : ℕ) (α : Ωⁿ⁺¹(A, a)) :
    α^p = conjugateΩ (apd idp p) (apΩ (transport (λ x, x = x) p) α) :=
  begin induction p; symmetry; apply idmapΩ end

  hott lemma transportAbelian {A : Type u} {a : A} (ε : idp a = idp a) :
    transport (λ x, x = x) ε ~ λ x, x :=
  λ _, transportInvCompComp _ _ ⬝ cancelHigherConjLeft _ _

  hott theorem abelianΩ {A : Type u} {a : A} (p : idp a = idp a) :
    Π (n : ℕ) (α : Ωⁿ⁺¹(a = a, idp a)), α^p = α
  | Nat.zero,   _ => transportAbelian _ _
  | Nat.succ n, _ => conjugateSuccΩ _ _ _ ⬝ ap (conjugateΩ (apd idp p)) (apWithHomotopyΩ (transportAbelian _) _ _) ⬝
                     (conjugateTransΩ _ _ (n + 1) _)⁻¹ ⬝ abelianΩ _ _ _ ⬝ idmapΩ _ _

  hott definition comApΩ {A : Type u} {B : Type v} {C : Type w} (f : B → C) (g : A → B) {a : A} :
    Π (n : ℕ) (α : Ωⁿ(A, a)), apΩ (f ∘ g) α = apΩ f (apΩ g α)
  | Nat.zero,   _ => idp _
  | Nat.succ _, _ => apWithHomotopyΩ (mapOverComp _ _) _ _ ⬝ comApΩ (ap f) (ap g) _ _

  hott lemma apdDiagΩ {A : Type u} {B : A → Type v} {C : A → Type w} (f : Π x, B x) (φ : Π x, B x → C x) {x : A} :
    Π (n : ℕ) (α : Ωⁿ(A, x)), apdΩ (λ x, φ x (f x)) α = biapdΩ φ n α (apdΩ f α)
  | Nat.zero,   _ => idp _
  | Nat.succ n, α => apdWithHomotopyΩ (apdDiag f φ) n α ⬝ apdDiagΩ (apd f) (biapd φ) n α

  hott definition comApdΩ {A : Type u} {B : Type v} {C : B → Type w} (f : Π x, C x) (g : A → B) {x : A} :
    Π (n : ℕ) (α : Ωⁿ(A, x)), apdΩ (λ x, f (g x)) α = overApΩ C g n α (apdΩ f (apΩ g α))
  | Nat.zero,   _ => idp _
  | Nat.succ n, α => apdWithHomotopyΩ (apdOverComp _ _) _ _ ⬝ apdDiagΩ (λ p, apd f (ap g p)) (pathOverAp g) n α ⬝
                     ap (biapdΩ (pathOverAp g) n α) (comApdΩ (apd f) (ap g) n α)

  hott lemma happlyBiapdΩ {A : Type u} {B₁ : A → Type v} {B₂ : A → Type w} {φ ψ : Π x, B₁ x → B₂ x}
    (H : φ = ψ) {a : A} {b : B₁ a} (n : ℕ) (α : Ωⁿ(A, a)) (β : Ωⁿ(B₁, b, α)) :
      biapdΩ φ n α β = conjugateOverΩ (happly (happly H a) b)⁻¹ (biapdΩ ψ n α β) :=
  begin induction H; reflexivity end

  hott lemma biapdWithHomotopyΩ {A : Type u} {B₁ : A → Type v} {B₂ : A → Type w} {φ ψ : Π x, B₁ x → B₂ x}
    (H : Π x, φ x ~ ψ x) {a : A} {b : B₁ a} (n : ℕ) (α : Ωⁿ(A, a)) (β : Ωⁿ(B₁, b, α)) :
      biapdΩ φ n α β = conjugateOverΩ (H a b)⁻¹ (biapdΩ ψ n α β) :=
  begin
    transitivity; apply happlyBiapdΩ; apply Theorems.funext;
    intro; apply Theorems.funext; intro; apply H;
    apply ap (conjugateOverΩ ·⁻¹ (biapdΩ ψ n α β));
    apply Theorems.happlyFunextPt₂
  end

  hott theorem comBiapdΩ {A : Type u} {B₁ : A → Type v} {B₂ : A → Type w} {B₃ : A → Type k}
    (ψ : Π x, B₂ x → B₃ x) (φ : Π x, B₁ x → B₂ x) {a : A} {b : B₁ a} :
    Π (n : ℕ) (α : Ωⁿ(A, a)) (β : Ωⁿ(B₁, b, α)), biapdΩ ψ n α (biapdΩ φ n α β) = biapdΩ (λ x, ψ x ∘ φ x) n α β
  | Nat.zero,   _, _ => idp _
  | Nat.succ n, α, β => @comBiapdΩ (a = a) (λ p, b =[B₁, p] b) (λ p, φ a b =[B₂, p] φ a b)
                                   (λ p, ψ a (φ a b) =[B₃, p] ψ a (φ a b))
                                   (biapd ψ) (biapd φ) (idp a) (idp b) n α β ⬝
                        biapdWithHomotopyΩ (λ p q, (comBiapd ψ φ p q)⁻¹) n α β

  hott lemma biapdIdfunΩ {A : Type u} {B : A → Type v} {a : A} {b : B a} :
    Π (n : ℕ) (α : Ωⁿ(A, a)) (β : Ωⁿ(B, b, α)), biapdΩ (λ _, idfun) n α β = β
  | Nat.zero,   _, _ => idp _
  | Nat.succ n, α, β => biapdWithHomotopyΩ (λ _, biapdIdfun) _ _ _ ⬝ biapdIdfunΩ n α β

  hott corollary loopOverApBackAndForward {A : Type u} {B₁ : A → Type v} {B₂ : A → Type w}
    (ψ : Π x, B₂ x → B₁ x) (φ : Π x, B₁ x → B₂ x) (H : Π x, ψ x ∘ φ x ~ idfun) {a : A} {b : B₁ a}
    (n : ℕ) (α : Ωⁿ(A, a)) (β : Ωⁿ(B₁, b, α)) : biapdΩ ψ n α (biapdΩ φ n α β) = conjugateOverΩ (H a b)⁻¹ β :=
  begin transitivity; apply comBiapdΩ; transitivity; apply biapdWithHomotopyΩ H; apply ap; apply biapdIdfunΩ end

  hott theorem pathOverApCohΩ {A : Type u} {B : Type v} (C : B → Type w) (f : A → B) {a : A} {b : C (f a)} :
    Π (n : ℕ) (α : Ωⁿ(A, a)) (β : Ωⁿ(C ∘ f, b, α)), overApΩ C f n α (underApΩ C f n α β) = β
  | Nat.zero,   _, _ => idp _
  | Nat.succ n, α, β => ap (biapdΩ (pathOverAp f) n α) (@pathOverApCohΩ (a = a) (f a = f a) (λ p, b =[C, p] b) (ap f) (idp a) (idp b) n α _) ⬝
                        loopOverApBackAndForward (pathOverAp f) (pathUnderAp f) (pathOverApCoh f) n α β

  hott theorem pathUnderApCohΩ {A : Type u} {B : Type v} (C : B → Type w) (f : A → B) {a : A} {b : C (f a)} :
    Π (n : ℕ) (α : Ωⁿ(A, a)) (β : Ωⁿ(C, b, apΩ f α)), underApΩ C f n α (overApΩ C f n α β) = β
  | Nat.zero,   _, _ => idp _
  | Nat.succ n, α, β => ap (underApΩ _ _ n _) (loopOverApBackAndForward (pathUnderAp f) (pathOverAp f) (pathUnderApCoh f) n α _) ⬝
                        @pathUnderApCohΩ (a = a) (f a = f a) (λ p, b =[C, p] b) (ap f) (idp a) (idp b) n α β

  hott corollary comApdUnderΩ {A : Type u} {B : Type v} {C : B → Type w} (f : Π x, C x) (g : A → B) {x : A}
    (n : ℕ) (α : Ωⁿ(A, x)) : underApΩ C g n α (apdΩ (λ x, f (g x)) α) = apdΩ f (apΩ g α) :=
  begin transitivity; apply ap (underApΩ C g n α); apply comApdΩ; apply pathUnderApCohΩ end

  hott definition sigmaProdΩ {A : Type u} {B : A → Type v} {w : Σ x, B x} :
    Π {n : ℕ} (α : Ωⁿ(A, w.1)) (β : Ωⁿ(B, w.2, α)), Ωⁿ(Σ x, B x, w)
  | Nat.zero,   x, y => ⟨x, y⟩
  | Nat.succ n, α, β => apΩ Sigma.eqOfSigmaEq (@sigmaProdΩ (w.1 = w.1) (λ p, w.2 =[B, p] w.2) ⟨idp w.1, idp w.2⟩ n α β)

  hott lemma apFstProdΩ {A : Type u} {B : A → Type v} {w : Σ x, B x} :
    Π {n : ℕ} (α : Ωⁿ(A, w.1)) (β : Ωⁿ(B, w.2, α)), apΩ Sigma.fst (sigmaProdΩ α β) = α
  | Nat.zero,   _, _ => idp _
  | Nat.succ n, α, β =>
  begin
    let ε := @sigmaProdΩ (w.1 = w.1) (λ p, w.2 =[B, p] w.2) ⟨idp w.1, idp w.2⟩ n α β;
    dsimp [apΩ, sigmaProdΩ]; transitivity; symmetry; apply comApΩ (ap Sigma.fst) Sigma.eqOfSigmaEq n ε;
    transitivity; apply apWithHomotopyΩ; intro; apply Sigma.mapFstOverProd; apply apFstProdΩ
  end

  hott theorem apOverSigmaΩ {A : Type u} {B : A → Type v} (f : Π x, B x) {a : A} :
    Π {n : ℕ} (α : Ωⁿ(A, a)), @apΩ A (Σ x, B x) (λ x, ⟨x, f x⟩) a n α = sigmaProdΩ α (apdΩ f α)
  | Nat.zero,   x => idp _
  | Nat.succ n, α =>
  begin
    dsimp [sigmaProdΩ, apΩ, apdΩ];
    transitivity; apply apWithHomotopyΩ; apply Sigma.apOverSigma;
    transitivity; apply @comApΩ (a = a) (Σ p, f a =[p] f a) (@Id (Σ x, B x) ⟨a, f a⟩ ⟨a, f a⟩)
      (@Sigma.eqOfSigmaEq A B ⟨a, f a⟩ ⟨a, f a⟩) (λ p, ⟨p, apd f p⟩);
    apply ap; apply apOverSigmaΩ (apd f)
  end

  hott definition happlyΩ {A : Type u} {B : A → Type v} (φ : Π x, B x) : Π {n : ℕ}, Ωⁿ(Π x, B x, φ) → Π x, Ωⁿ(B x, φ x)
  | Nat.zero,   f => f
  | Nat.succ n, H => @happlyΩ A (λ x, φ x = φ x) (λ x, idp (φ x)) n (apΩ happly H)

  hott definition funextΩ {A : Type u} {B : A → Type v} (φ : Π x, B x) : Π {n : ℕ}, (Π x, Ωⁿ(B x, φ x)) → Ωⁿ(Π x, B x, φ)
  | Nat.zero,   f => f
  | Nat.succ n, H => conjugateΩ Theorems.funextId (apΩ Theorems.funext (@funextΩ A (λ x, φ x = φ x) (λ x, idp (φ x)) n H))

  hott theorem happlyFunextΩ {A : Type u} {B : A → Type v} (φ : Π x, B x) :
    Π {n : ℕ} (α : Π x, Ωⁿ(B x, φ x)), happlyΩ φ (funextΩ φ α) = α
  | Nat.zero,   f => idp f
  | Nat.succ n, H =>
  begin
    dsimp [happlyΩ, funextΩ]; transitivity;
    transitivity; apply ap (happlyΩ _);
    transitivity; apply apConjugateΩ; apply ap (conjugateΩ _);
    transitivity; symmetry; apply comApΩ happly; apply apWithHomotopyΩ;
    apply Theorems.happlyFunext; apply ap (happlyΩ _);
    transitivity; symmetry; apply conjugateTransΩ; apply bimap; apply idmapΩ;
    transitivity; apply ap (·⁻¹ ⬝ _); apply Theorems.homotopyIndId; apply Id.invComp;
    apply @happlyFunextΩ A (λ x, φ x = φ x) (λ x, idp (φ x)) n H
  end

  hott theorem funextHapplyΩ {A : Type u} {B : A → Type v} (φ : Π x, B x) :
    Π {n : ℕ} (α : Ωⁿ(Π x, B x, φ)), funextΩ φ (happlyΩ φ α) = α
  | Nat.zero,   f => idp f
  | Nat.succ n, H =>
  begin
    dsimp [happlyΩ, funextΩ]; transitivity; apply ap (conjugateΩ _);
    transitivity; apply ap (apΩ _); apply funextHapplyΩ;
    transitivity; symmetry; apply comApΩ Theorems.funext happly n H;
    apply apWithHomotopyΩ; apply Theorems.funextHapply;
    transitivity; symmetry; apply conjugateTransΩ;
    transitivity; apply ap (conjugateΩ · _);
    apply Id.invComp; apply idmapΩ
  end

  hott definition prodΩ {A : Type u} {B : Type v} {w : A × B} :
    Π {n : ℕ} (α : Ωⁿ(A, w.1)) (β : Ωⁿ(B, w.2)), Ωⁿ(A × B, w)
  | Nat.zero,   x, y => (x, y)
  | Nat.succ n, α, β => apΩ Product.eqOfProdEq (@prodΩ (w.1 = w.1) (w.2 = w.2) (idp w.1, idp w.2) n α β)

  section
    open Prod (pr₁ pr₂)

    hott lemma apFstΩ {A : Type u} {B : Type v} {w : A × B} :
      Π {n : ℕ} (α : Ωⁿ(A, w.1)) (β : Ωⁿ(B, w.2)), apΩ pr₁ (prodΩ α β) = α
    | Nat.zero,   x, y => idp x
    | Nat.succ n, α, β => (comApΩ (ap pr₁) Product.eqOfProdEq n (@prodΩ (w.1 = w.1) (w.2 = w.2) (idp w.1, idp w.2) n α β))⁻¹ ⬝
                          apWithHomotopyΩ Product.apFst _ _ ⬝
                          apFstΩ _ _

    hott lemma apSndΩ {A : Type u} {B : Type v} {w : A × B} :
      Π {n : ℕ} (α : Ωⁿ(A, w.1)) (β : Ωⁿ(B, w.2)), apΩ pr₂ (prodΩ α β) = β
    | Nat.zero,   x, y => idp y
    | Nat.succ n, α, β => (comApΩ (ap pr₂) Product.eqOfProdEq n (@prodΩ (w.1 = w.1) (w.2 = w.2) (idp w.1, idp w.2) n α β))⁻¹ ⬝
                          apWithHomotopyΩ Product.apSnd _ _ ⬝
                          apSndΩ _ _
  end

  open GroundZero.Structures

  hott lemma levelStableΩ {A : Type u} {a : A} (k : ℕ₋₂) : Π {n : ℕ}, is-k-type A → is-k-type Ωⁿ(A, a)
  | Nat.zero,   H => H
  | Nat.succ n, H => @levelStableΩ (a = a) (idp a) k n (hlevel.cumulative k H a a)

  hott lemma levelOverΩ {A : Type u} {B : A → Type v} {a : A} {b : B a} (k : ℕ₋₂) :
    Π {n : ℕ}, (Π x, is-k-type (B x)) → Π (α : Ωⁿ(A, a)), is-k-type Ωⁿ(B, b, α)
  | Nat.zero,   H, x => H x
  | Nat.succ n, H, α => @levelOverΩ (a = a) (λ p, b =[B, p] b) (idp a) (idp b) k n (λ p, hlevel.cumulative k (H a) _ _) α

  hott lemma zeroTypeLoop {A : Type u} : Π {n : ℕ}, is-n-type A → Π x, is-0-type Ωⁿ(A, x)
  | Nat.zero,   H, _ => H
  | Nat.succ n, H, a => @zeroTypeLoop (a = a) n (H a a) (idp a)

  hott corollary hsetLoop {A : Type u} {n : ℕ} (H : is-n-type A) : Π x, hset Ωⁿ(A, x) :=
  λ x, zeroEqvSet (zeroTypeLoop H x)

  hott definition loopOverProp {A : Type u} {B : A → Type v} (H : Π x, prop (B x))
    {n : ℕ} {a : A} {b : B a} {α : Ωⁿ⁺¹(A, a)} : Ωⁿ⁺¹(B, b, α) :=
  inOverΩ _ _ (minusOneEqvProp.forward (levelOverΩ −1 (λ _, minusOneEqvProp.left (H _)) _) _ _)

  hott definition loopOverHSet {A : Type u} {B : A → Type v} (H : Π x, hset (B x))
    {n : ℕ} {a : A} {b : B a} {α : Ωⁿ⁺²(A, a)} : Ωⁿ⁺²(B, b, α) :=
  inOverΩ _ _ (propRespectsEquiv (Equiv.altDefOverΩ _ _).symm
    (zeroEqvSet.forward (levelOverΩ 0 (λ _, zeroEqvSet.left (H _)) _) _ _) _ _)

  hott definition loopPropNType {A : Type u} : Π {n : ℕ} (H : is-n-type A) (a : A), prop Ωⁿ⁺¹(A, a)
  | Nat.zero,   H, _ => zeroEqvSet.forward H _ _
  | Nat.succ n, H, a => @loopPropNType (a = a) n (H a a) (idp a)

  hott definition loopOverPropNType {A : Type u} {B : A → Type v} :
    Π {n : ℕ} (H : Π x, is-n-type (B x)) {a : A} {b : B a} {α : Ωⁿ⁺¹(A, a)}, prop Ωⁿ⁺¹(B, b, α)
  | Nat.zero,   H, _, _ => zeroEqvSet.forward (H _) _ _
  | Nat.succ n, H, a, _ => @loopOverPropNType (a = a) _ n (λ _, H _ _ _) _ _ _

  hott definition loopOverNType {A : Type u} {B : A → Type v} {n : ℕ} (H : Π x, is-n-type (B x))
    {a : A} {b : B a} {α : Ωⁿ⁺²(A, a)} : Ωⁿ⁺²(B, b, α) :=
  inOverΩ _ _ (loopOverPropNType H _ _)

  hott definition ofApEqΩ {A : Type u} (B : A → Type v) {a : A} {b : B a} :
    Π {n : ℕ} {α : Ωⁿ⁺¹(A, a)}, apΩ (transport B · b) α = idΩ b n → Ωⁿ⁺¹(B, b, α)
  | Nat.zero,   α, β => β
  | Nat.succ n, α, β =>
  begin
    apply @ofApEqΩ (a = a) (λ p, b =[B, p] b) (idp a) (idp b) n α;
    apply Id.trans; apply apWithHomotopyΩ; intro;
    transitivity; apply transportOverContrMap;
    transitivity; apply rid; apply mapInv;
    transitivity; apply comApΩ Id.inv;
    transitivity; apply ap (apΩ _); exact β; apply apIdΩ;
  end
end Types.Id

end GroundZero
