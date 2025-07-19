import GroundZero.Theorems.Connectedness
import GroundZero.Algebra.Group.Action

open GroundZero.Types.Id (idΩ ap)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types
open GroundZero.HITs

universe u

namespace GroundZero.Algebra

namespace Homotopy
  variable {A : Type u} {x : A} {n : ℕ}

  hott definition mul : ∥Ωⁿ⁺¹(A, x)∥₀ → ∥Ωⁿ⁺¹(A, x)∥₀ → ∥Ωⁿ⁺¹(A, x)∥₀ :=
  Trunc.ap₂ comΩ

  hott definition inv : ∥Ωⁿ⁺¹(A, x)∥₀ → ∥Ωⁿ⁺¹(A, x)∥₀ :=
  Trunc.ap revΩ

  hott definition unit : ∥Ωⁿ(A, x)∥₀ :=
  |idΩ x n|₀

  hott lemma isAssoc (a b c : ∥Ωⁿ⁺¹(A, x)∥₀) : mul (mul a b) c = mul a (mul b c) :=
  begin
    induction a; induction b; induction c; transitivity;
    apply Trunc.apβrule₂; apply ap Trunc.elem; symmetry; apply assocΩ;
    -- TODO: write some tactic to solve this automatically?
    apply hlevel.cumulative; apply Trunc.uniq 0;
    apply hlevel.cumulative; apply Trunc.uniq 0;
    apply hlevel.cumulative; apply Trunc.uniq 0
  end

  hott lemma hasLeftUnit (a : ∥Ωⁿ⁺¹(A, x)∥₀) : mul unit a = a :=
  begin
    induction a; transitivity; apply Trunc.apβrule₂; apply ap Trunc.elem;
    apply lidΩ; apply hlevel.cumulative; apply Trunc.uniq 0
  end

  hott lemma hasLeftInverse (a : ∥Ωⁿ⁺¹(A, x)∥₀) : mul (inv a) a = unit :=
  begin
    induction a; transitivity; apply Trunc.apβrule₂; apply ap Trunc.elem;
    apply revlΩ; apply hlevel.cumulative; apply Trunc.uniq 0
  end

  hott lemma isAbelian (a b : ∥Ωⁿ⁺²(A, x)∥₀) : mul a b = mul b a :=
  begin
    induction a; induction b; transitivity; apply Trunc.apβrule₂;
    apply ap Trunc.elem; apply abelianComΩ;
    apply hlevel.cumulative; apply Trunc.uniq 0;
    apply hlevel.cumulative; apply Trunc.uniq 0
  end
end Homotopy

hott definition Homotopy {A : Type u} (a : A) (n : ℕ) : Group :=
@Group.intro ∥Ωⁿ⁺¹(A, a)∥₀ (zeroEqvSet.forward (Trunc.uniq 0))
  Homotopy.mul Homotopy.inv Homotopy.unit Homotopy.isAssoc
  Homotopy.hasLeftUnit Homotopy.hasLeftInverse

namespace GroundZero.Types
  hott definition idTrunc {n : ℕ} {A : Type u} (a b : ∥A∥ₙ₊₁) :=
  (@Trunc.rec₂ A (hlevel.succ n) A (n-Type u) (λ x y, ⟨∥x = y∥ₙ, Trunc.uniq n⟩)
                 (Theorems.Equiv.ntypeIsSuccNType _) a b).1

  hott lemma idTruncTrunc {n : ℕ} {A : Type u} : Π (a b : ∥A∥ₙ₊₁), is-n-type (idTrunc a b) :=
  begin
    apply Trunc.ind₂; intros; apply Trunc.uniq n;
    { intros; apply propIsNType; apply ntypeIsProp }
  end

  hott definition idpTrunc {n : ℕ} {A : Type u} : Π (a : ∥A∥ₙ₊₁), idTrunc a a :=
  Trunc.ind (λ x, |idp x|ₙ) (λ x, hlevel.cumulative n (idTruncTrunc x x))

  hott theorem idTruncElem {n : ℕ} {A : Type u} {a b : ∥A∥ₙ₊₁} : a = b → idTrunc a b :=
  λ p, transport (idTrunc a) p (idpTrunc a)

  hott corollary idTruncElim {n : ℕ} {A : Type u} {a b : A} : |a|ₙ₊₁ = |b|ₙ₊₁ → ∥a = b∥ₙ :=
  idTruncElem

  hott definition Cover (A : Type u) := A → Set u

  hott definition Cover.total {A : Type u} : Cover A → Type u :=
  λ C, Σ x, (C x).1

  hott definition uCov {A : Type u} (a : A) : Cover A :=
  λ b, ⟨∥a = b∥₀, zeroEqvSet (Trunc.uniq 0)⟩

  namespace uCov
    variable {A : Type u}

    hott lemma isConn (a : A) : is-1-connected (uCov a).total :=
    begin
      exists |⟨a, |idp a|₀⟩|₁; apply Trunc.ind;
      { apply Sigma.Ind; intro b; apply Trunc.ind;
        { intro p; induction p; reflexivity };
        { intro; apply Trunc.uniq 1 } };
      { apply hlevel.cumulative; apply Trunc.uniq }
    end

    hott definition encode (C : Cover A) (c : C.total) : Π x, (uCov c.1 x).1 → (C x).1 :=
    λ b, Trunc.rec (transport (λ x, (C x).1) · c.2) (zeroEqvSet.left (C b).2)

    hott definition decode (C : Cover A) (c : C.total) (H : prop ∥C.total∥₁) :
      Π x, (C x).1 → (uCov c.1 x).1 :=
    λ b c', Trunc.ap (ap Sigma.fst) (idTruncElim (H |c|₁ |⟨b, c'⟩|₁))

    hott lemma encodeDecode (C : Cover A) (c₁ c₂ : C.total) (H : prop ∥C.total∥₁) :
      encode C c₁ c₂.1 (decode C c₁ H c₂.1 c₂.2) = c₂.2 :=
    begin
      induction idTruncElim (H |c₁|₁ |c₂|₁);
      { case elemπ p =>
        induction p; transitivity; apply ap (encode _ _ _); apply ap (Trunc.ap _);
        apply ap idTruncElim; show _ = idp _; apply propIsSet; exact H; reflexivity };
      { apply zeroEqvSet.left; apply propIsSet; apply (C c₂.1).2 }
    end

    open GroundZero.Proto (idfun)

    hott lemma decodeEncode (C : Cover A) (c : C.total) (H : prop ∥C.total∥₁) :
      Π b, decode C c H b ∘ encode C c b ~ idfun :=
    begin
      intro b; apply Trunc.ind;
      { intro p; induction p; dsimp; transitivity; apply ap (Trunc.ap _);
        apply ap idTruncElim; show _ = idp _; apply propIsSet;
        exact H; reflexivity };
      { intro; apply hlevel.cumulative; apply Trunc.uniq 0 }
    end

    hott theorem isPropUniv (C : Cover A) (c : C.total) (H : prop ∥C.total∥₁) : uCov c.1 ~ C :=
    begin
      intro b; apply Sigma.prod; apply setIsProp; apply ua;
      fapply Equiv.intro (encode C c b) (decode C c H b);
      apply decodeEncode; intro σ; apply encodeDecode C c ⟨b, σ⟩
    end

    hott corollary isConnUniv (C : Cover A) (c : C.total) :
      is-1-connected C.total → uCov c.1 ~ C :=
    λ H, isPropUniv C c (contrImplProp H)
  end uCov
end GroundZero.Types

end GroundZero.Algebra
