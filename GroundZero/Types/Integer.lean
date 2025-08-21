import GroundZero.Theorems.Nat

open GroundZero.Types.Equiv (bimap)
open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Theorems
open GroundZero

namespace GroundZero.Types

/-
  +2 = pos 2
  +1 = pos 1
   0 = pos 0
  −1 = neg 0
  −2 = neg 1
-/

hott definition Integer := ℕ + ℕ
notation "ℤ" => Integer

@[match_pattern] hott definition Integer.pos : ℕ → ℤ := Coproduct.inl
@[match_pattern] hott definition Integer.neg : ℕ → ℤ := Coproduct.inr

hott instance (n : ℕ) : OfNat ℤ n := ⟨Integer.pos n⟩

namespace Integer

instance : ToString ℤ :=
⟨λ | pos n => toString n
   | neg n => "-" ++ toString (n + 1)⟩

hott definition auxsucc : ℕ → ℤ
| Nat.zero   => pos 0
| Nat.succ n => neg n

hott definition succ : ℤ → ℤ
| neg u => auxsucc u
| pos v => pos (v + 1)

hott definition auxpred : ℕ → ℤ
| Nat.zero   => neg 0
| Nat.succ n => pos n

hott definition pred : ℤ → ℤ
| neg u => neg (u + 1)
| pos v => auxpred v

hott lemma succPred : Π z, succ (pred z) = z
| neg _            => idp _
| pos Nat.zero     => idp _
| pos (Nat.succ _) => idp _

hott lemma predSucc : Π z, pred (succ z) = z
| neg Nat.zero     => idp _
| neg (Nat.succ _) => idp _
| pos _            => idp _

hott definition succEquiv : ℤ ≃ ℤ :=
⟨succ, (⟨pred, predSucc⟩, ⟨pred, succPred⟩)⟩

section
  universe u

  variable {π : ℤ → Type u} (π₀ : π 0)
           (πsucc : Π x, π x → π (succ x))
           (πpred : Π x, π x → π (pred x))
           (coh₁ : Π p z, πpred _ (πsucc p z) =[predSucc _] z)
           (coh₂ : Π p z, πsucc _ (πpred p z) =[succPred _] z)

  hott definition indpos : Π n, π (pos n)
  | Nat.zero   => π₀
  | Nat.succ n => πsucc (pos n) (indpos n)

  hott definition indneg : Π n, π (neg n)
  | Nat.zero   => πpred 0 π₀
  | Nat.succ n => πpred (neg n) (indneg n)

  hott definition indsp : Π z, π z
  | neg n => indneg π₀ πpred n
  | pos n => indpos π₀ πsucc n

  hott theorem indspβ₁ : indsp π₀ πsucc πpred 0 = π₀ :=
  by reflexivity

  hott theorem indspβ₂ : Π z, indsp π₀ πsucc πpred (succ z) = πsucc z (indsp π₀ πsucc πpred z)
  | neg Nat.zero     => (coh₂ (pos 0) _)⁻¹
  | neg (Nat.succ n) => (coh₂ (neg n) _)⁻¹
  | pos n            => idp _

  hott theorem indspβ₃ : Π z, indsp π₀ πsucc πpred (pred z) = πpred z (indsp π₀ πsucc πpred z)
  | neg n            => idp _
  | pos Nat.zero     => idp _
  | pos (Nat.succ n) => (coh₁ (pos n) _)⁻¹
end

section
  universe u

  variable {π : Type u} (π₀ : π)
           (πsucc : π → π) (πpred : π → π)
           (coh₁ : πpred ∘ πsucc ~ id)
           (coh₂ : πsucc ∘ πpred ~ id)

  hott definition recpos : ℕ → π
  | Nat.zero   => π₀
  | Nat.succ n => πsucc (recpos n)

  hott definition recneg : ℕ → π
  | Nat.zero   => πpred π₀
  | Nat.succ n => πpred (recneg n)

  hott definition recsp : ℤ → π
  | neg n => recneg π₀ πpred n
  | pos n => recpos π₀ πsucc n

  hott theorem recspβ₁ : recsp π₀ πsucc πpred 0 = π₀ :=
  by reflexivity

  hott theorem recspβ₂ : Π z, recsp π₀ πsucc πpred (succ z) = πsucc (recsp π₀ πsucc πpred z)
  | neg Nat.zero     => (coh₂ _)⁻¹
  | neg (Nat.succ n) => (coh₂ _)⁻¹
  | pos n            => idp _

  hott theorem recspβ₃ : Π z, recsp π₀ πsucc πpred (pred z) = πpred (recsp π₀ πsucc πpred z)
  | neg n            => idp _
  | pos Nat.zero     => idp _
  | pos (Nat.succ n) => (coh₁ _)⁻¹
end

hott definition abs : ℤ → ℕ
| pos n => n
| neg n => n + 1

hott definition add : ℤ → ℤ → ℤ :=
λ z, recsp z succ pred

hott instance : Add ℤ := ⟨add⟩

hott definition negate : ℤ → ℤ
| pos n => auxsucc n
| neg n => pos (n + 1)

hott instance : Neg ℤ := ⟨negate⟩

hott definition sgn : ℤ → ℤ
| pos Nat.zero     =>  0
| pos (Nat.succ n) =>  1
| neg n            => -1

hott definition sub (x y : ℤ) := x + (-y)
hott instance : Sub ℤ := ⟨sub⟩

hott lemma plusSucc (i j : ℤ) : i + succ j = succ (i + j) :=
begin apply recspβ₂; apply succPred end

hott lemma plusPred (i j : ℤ) : i + pred j = pred (i + j) :=
begin apply recspβ₃; apply predSucc end

hott theorem addZero (x : ℤ) : x + 0 = x :=
by reflexivity

hott theorem zeroAdd (x : ℤ) : 0 + x = x :=
begin
  induction x using indsp; reflexivity;
  { transitivity; apply plusSucc; apply ap; assumption };
  { transitivity; apply plusPred; apply ap; assumption }
end

hott theorem succPlus (i j : ℤ) : succ i + j = succ (i + j) :=
begin
  induction j using indsp; reflexivity;
  { transitivity; apply plusSucc; apply ap;
    transitivity; assumption; symmetry; apply plusSucc };
  { transitivity; apply plusPred; transitivity;
    apply ap pred; assumption; transitivity; apply predSucc;
    transitivity; symmetry; apply succPred; apply ap succ;
    symmetry; apply plusPred }
end

hott theorem predPlus (i j : ℤ) : pred i + j = pred (i + j) :=
begin
  induction j using indsp; reflexivity;
  { transitivity; apply plusSucc; transitivity;
    apply ap succ; assumption; transitivity; apply succPred;
    transitivity; symmetry; apply predSucc; apply ap pred;
    symmetry; apply plusSucc };
  { transitivity; apply plusPred; apply ap pred;
    transitivity; assumption; symmetry; apply plusPred }
end

hott theorem addComm (x y : ℤ) : x + y = y + x :=
begin
  induction y using indsp; symmetry; apply zeroAdd;
  { transitivity; apply plusSucc; transitivity; apply ap succ;
    assumption; symmetry; apply succPlus };
  { transitivity; apply plusPred; transitivity; apply ap pred;
    assumption; symmetry; apply predPlus }
end

hott definition diff : ℕ → ℕ → ℤ
| m,          Nat.zero   => pos m
| Nat.zero,   Nat.succ n => neg n
| Nat.succ m, Nat.succ n => diff m n

hott proposition diffAsymm : Π x y, diff x y = negate (diff y x)
| Nat.zero,   Nat.zero   => idp _
| Nat.succ m, Nat.zero   => idp _
| Nat.zero,   Nat.succ n => idp _
| Nat.succ m, Nat.succ n => diffAsymm m n

hott lemma diffZeroRight : Π (n : Nat), diff n 0 = pos n
| Nat.zero   => idp 0
| Nat.succ n => idp (pos (n + 1))

hott lemma diffZeroLeft : Π (n : ℕ), diff 0 n = auxsucc n
| Nat.zero   => idp 0
| Nat.succ n => idp (neg n)

hott lemma diffSucc : Π (n m : ℕ), diff (n + 1) m = diff n m + 1
| Nat.zero,   Nat.zero   => idp _
| Nat.succ n, Nat.zero   => idp _
| Nat.zero,   Nat.succ m => diffZeroLeft _
| Nat.succ n, Nat.succ m => diffSucc n m

hott lemma succDiff : Π (n m : ℕ), succ (diff n m) = diff (n + 1) m
| Nat.zero,   Nat.zero   => idp _
| Nat.succ n, Nat.zero   => idp _
| Nat.zero,   Nat.succ m => (diffZeroLeft _)⁻¹
| Nat.succ n, Nat.succ m => succDiff n m

hott lemma predDiff : Π (n m : ℕ), pred (diff n m) = diff n (m + 1)
| Nat.zero,   Nat.zero   => idp _
| Nat.succ n, Nat.zero   => (diffZeroRight _)⁻¹
| Nat.zero,   Nat.succ m => idp _
| Nat.succ n, Nat.succ m => predDiff n m

hott lemma diffAddLeft (n : ℕ) : Π (m : ℕ), diff (n + m) m = pos n
| Nat.zero   => diffZeroRight n
| Nat.succ m => diffAddLeft n m

hott lemma diffAddRight (n : ℕ) : Π (m : ℕ), diff m (n + m) = auxsucc n
| Nat.zero   => diffZeroLeft n
| Nat.succ m => diffAddRight n m

hott theorem set : hset ℤ :=
Hedberg (decCoproduct Nat.natDecEq Nat.natDecEq)

hott corollary succToAdd (z : ℤ) : z + 1 = succ z :=
by reflexivity

hott corollary predToSub (z : ℤ) : z - 1 = pred z :=
by apply plusPred z 0

hott definition mul : ℤ → ℤ → ℤ :=
λ i, recsp 0 (λ j, j + i) (λ j, j - i)

hott instance : Mul ℤ := ⟨mul⟩

hott lemma negateSucc : Π (i : ℤ), negate (succ i) = pred (negate i)
| pos Nat.zero     => idp _
| pos (Nat.succ _) => idp _
| neg Nat.zero     => idp _
| neg (Nat.succ _) => idp _

hott lemma negatePred : Π (i : ℤ), negate (pred i) = succ (negate i)
| pos Nat.zero     => idp _
| pos (Nat.succ _) => idp _
| neg Nat.zero     => idp _
| neg (Nat.succ _) => idp _

hott lemma negateNegate : Π (i : ℤ), negate (negate i) = i
| pos Nat.zero     => idp _
| pos (Nat.succ n) => idp _
| neg n            => idp _

hott lemma addSub (i j : ℤ) : (i + j) - j = i :=
begin
  induction j using indsp; reflexivity;
  { transitivity; apply bimap add; apply plusSucc; apply negateSucc;
    transitivity; apply succPlus; transitivity; apply ap succ;
    apply plusPred; transitivity; apply succPred; assumption };
  { transitivity; apply bimap add; apply plusPred; apply negatePred;
    transitivity; apply predPlus; transitivity; apply ap pred;
    apply plusSucc; transitivity; apply predSucc; assumption }
end

hott lemma subAdd (i j : ℤ) : (i - j) + j = i :=
begin transitivity; apply ap (add _); symmetry; apply negateNegate; apply addSub end

hott theorem multZero (i : ℤ) : i * 0 = 0 :=
by reflexivity

hott theorem multOne (i : ℤ) : i * 1 = i :=
by apply zeroAdd

hott theorem multSucc (i j : ℤ) : i * succ j = i * j + i :=
begin apply recspβ₂; intro; apply subAdd end

hott theorem multPred (i j : ℤ) : i * pred j = i * j - i :=
begin apply recspβ₃; intro; apply addSub end

hott lemma zeroMult (i : ℤ) : 0 * i = 0 :=
begin
  induction i using indsp; reflexivity;
  { transitivity; apply multSucc; apply ap (λ z, z + 0); assumption };
  { transitivity; apply multPred; apply ap (λ z, z - 0); assumption }
end

hott theorem multMinusOne (i : ℤ) : i * (-1) = -i :=
begin transitivity; apply multPred i 0; apply zeroAdd end

hott lemma predAuxsucc : Π (n : ℕ), pred (auxsucc n) = neg n
| Nat.zero   => idp _
| Nat.succ _ => idp _

hott lemma absAuxsucc : Π (n : ℕ), abs (auxsucc n) = n
| Nat.zero   => idp _
| Nat.succ _ => idp _

hott lemma negateAuxsucc : Π (n : ℕ), negate (auxsucc n) = pos n
| Nat.zero   => idp _
| Nat.succ _ => idp _

hott lemma negateAdd (i j : ℤ) : -(i + j) = -i - j :=
begin
  induction j using indsp; reflexivity;
  { transitivity; apply ap negate; apply plusSucc;
    transitivity; apply negateSucc;
    transitivity; apply ap pred; assumption;
    transitivity; symmetry; apply plusPred;
    apply ap; symmetry; apply negateSucc };
  { transitivity; apply ap negate; apply plusPred;
    transitivity; apply negatePred;
    transitivity; apply ap succ; assumption;
    transitivity; symmetry; apply plusSucc;
    apply ap; symmetry; apply negatePred }
end

hott theorem addAssoc (i j k : ℤ) : (i + j) + k = i + (j + k) :=
begin
  induction k using indsp; reflexivity;
  { transitivity; apply plusSucc;
    transitivity; apply ap succ; assumption;
    transitivity; symmetry; apply plusSucc;
    apply ap; symmetry; apply plusSucc };
  { transitivity; apply plusPred;
    transitivity; apply ap pred; assumption;
    transitivity; symmetry; apply plusPred;
    apply ap; symmetry; apply plusPred }
end

hott lemma succMult (i j : ℤ) : succ i * j = i * j + j :=
begin
  induction j using indsp; reflexivity;
  { transitivity; apply multSucc; transitivity; apply ap (add · _); assumption;
    transitivity; apply plusSucc; transitivity; apply ap succ;
    transitivity; apply addAssoc; transitivity; apply ap; apply addComm;
    symmetry; apply addAssoc; transitivity; symmetry; apply plusSucc;
    apply ap (add · _); symmetry; apply multSucc };
  { transitivity; apply multPred; transitivity; apply ap (add · (negate (succ i))); assumption;
    transitivity; apply ap (add _); apply negateSucc; transitivity; apply plusPred;
    transitivity; apply ap pred; transitivity; apply addAssoc;
    transitivity; apply ap; apply addComm; symmetry; apply addAssoc;
    transitivity; symmetry; apply plusPred; apply ap (add · _);
    symmetry; apply multPred }
end

hott lemma predMult (i j : ℤ) : pred i * j = i * j - j :=
begin
  induction j using indsp; reflexivity;
  { transitivity; apply multSucc; transitivity; apply ap (add · _); assumption;
    transitivity; apply plusPred; transitivity; apply ap pred;
    transitivity; apply addAssoc; transitivity; apply ap; apply addComm;
    symmetry; apply addAssoc; transitivity; symmetry; apply plusPred;
    transitivity; apply ap (add _); symmetry; apply negateSucc;
    apply ap (add · _); symmetry; apply multSucc };
  { transitivity; apply multPred; transitivity; apply ap (add · (negate (pred i))); assumption;
    transitivity; apply ap (add _); apply negatePred; transitivity; apply plusSucc;
    transitivity; apply ap succ; transitivity; apply addAssoc;
    transitivity; apply ap; apply addComm; symmetry; apply addAssoc;
    transitivity; symmetry; apply plusSucc;
    transitivity; apply ap (add _); symmetry; apply negatePred;
    apply ap (add · _); symmetry; apply multPred }
end

hott theorem multComm (i j : ℤ) : i * j = j * i :=
begin
  induction j using indsp; transitivity; apply multZero; symmetry; apply zeroMult;
  { transitivity; apply multSucc; transitivity; apply ap (λ k, k + i);
    assumption; symmetry; apply succMult };
  { transitivity; apply multPred; transitivity; apply ap (λ k, k - i);
    assumption; symmetry; apply predMult }
end

hott corollary oneMult (i : ℤ) : 1 * i = i :=
multComm _ _ ⬝ multOne _

hott lemma posPosAdd (i : ℕ) : Π (j : ℕ), pos (i + j) = pos i + pos j
| Nat.zero   => idp _
| Nat.succ j => ap succ (posPosAdd i j) ⬝ (plusSucc (pos i) (pos j))⁻¹

hott lemma posNegAdd (i : ℕ) : Π (j : ℕ), diff i (j + 1) = pos i + neg j
| Nat.zero   => (predDiff _ _)⁻¹ ⬝ (predToSub _)⁻¹ ⬝ ap (λ z, z - 1) (diffZeroRight _)
| Nat.succ j => (predDiff _ _)⁻¹ ⬝ ap pred (posNegAdd i j) ⬝ (plusPred (pos i) (neg j))⁻¹

hott lemma negPosAdd : Π (i j : ℕ), diff j (i + 1) = neg i + pos j
| Nat.zero,   j => (predDiff _ _)⁻¹ ⬝ ap pred (diffZeroRight _) ⬝ (predToSub _)⁻¹ ⬝ addComm (pos j) (neg 0)
| Nat.succ i, j => (predDiff _ _)⁻¹ ⬝ ap pred (negPosAdd i j) ⬝ (predPlus (neg i) (pos j))⁻¹

hott lemma negNegAdd (i : ℕ) : Π (j : ℕ), neg (i + j + 1) = neg i + neg j
| Nat.zero   => idp _
| Nat.succ j => ap neg Nat.plusOnePlus ⬝ ap pred (negNegAdd i j) ⬝ (plusPred (neg i) (neg j))⁻¹

hott lemma posPosMult (i : ℕ) : Π (j : ℕ), pos (i * j) = pos i * pos j
| Nat.zero   => idp _
| Nat.succ j => posPosAdd _ _ ⬝ ap (add · _) (posPosMult i j) ⬝ (multSucc (pos i) (pos j))⁻¹

hott lemma negateMultLeft (i j : ℤ) : negate (i * j) = i * negate j :=
begin
  induction j using indsp; reflexivity;
  { transitivity; apply ap negate; apply multSucc;
    transitivity; apply negateAdd;
    transitivity; apply ap (λ k, k - i); assumption;
    transitivity; symmetry; apply multPred;
    apply ap; symmetry; apply negateSucc };
  { transitivity; apply ap negate; apply multPred;
    transitivity; apply negateAdd;
    transitivity; apply ap (λ k, k - (-i)); assumption;
    transitivity; apply ap (add _); apply negateNegate;
    transitivity; symmetry; apply multSucc;
    apply ap; symmetry; apply negatePred }
end

hott lemma posNegMult (i j : ℕ) : auxsucc (i * Nat.succ j) = pos i * neg j :=
begin
  transitivity; symmetry; apply negateNegate; transitivity;
  apply ap negate; transitivity; apply negateAuxsucc;
  apply posPosMult; apply negateMultLeft
end

hott lemma negPosMult (i j : ℕ) : auxsucc (Nat.succ i * j) = neg i * pos j :=
begin
  transitivity; apply ap auxsucc; apply Nat.mulComm;
  transitivity; apply posNegMult; apply multComm
end

hott lemma negNegMult (i : ℕ) : Π (j : ℕ), pos (Nat.succ i * Nat.succ j) = neg i * neg j
| Nat.zero   => ap pos (Nat.mulOne _) ⬝ (multMinusOne _)⁻¹
| Nat.succ j => posPosAdd _ _ ⬝ ap (add · _) (negNegMult i j) ⬝ (multPred (neg i) (neg j))⁻¹

hott theorem absMult : Π (i j : ℤ), abs (i * j) = abs i * abs j
| neg i, neg j => ap abs (negNegMult i j)⁻¹
| neg i, pos j => ap abs (negPosMult i j)⁻¹ ⬝ absAuxsucc _
| pos i, neg j => ap abs (posNegMult i j)⁻¹ ⬝ absAuxsucc _
| pos i, pos j => ap abs (posPosMult i j)⁻¹

end Integer

end GroundZero.Types
