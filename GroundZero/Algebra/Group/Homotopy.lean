import GroundZero.Theorems.Connectedness
import GroundZero.Algebra.Group.Action

open GroundZero.Types.Id (idΩ ap)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types
open GroundZero.HITs

universe u

namespace GroundZero

namespace Algebra

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

end Algebra

namespace HITs.Trunc
  variables {n : ℕ} {A : Type u}

  open GroundZero.Theorems.Equiv

  hott definition idTrunc (a b : ∥A∥ₙ₊₁) :=
  (@Trunc.rec₂ A (hlevel.succ n) A (n-Type u)
                 (λ x y, ⟨∥x = y∥ₙ, Trunc.uniq n⟩)
                 (ntypeIsSuccNType _) a b).1

  hott lemma idTruncTrunc : Π (a b : ∥A∥ₙ₊₁), is-n-type (idTrunc a b) :=
  begin
    apply Trunc.ind₂; intros; apply Trunc.uniq n;
  { intros; apply propIsNType; apply ntypeIsProp }
  end

  hott definition idpTrunc : Π (a : ∥A∥ₙ₊₁), idTrunc a a :=
  Trunc.ind (λ x, |idp x|ₙ) (λ x, hlevel.cumulative n (idTruncTrunc x x))

  hott definition encode {a b : ∥A∥ₙ₊₁} : a = b → idTrunc a b :=
  λ p, transport (idTrunc a) p (idpTrunc a)

  hott lemma decodeElem {A : Type u} {n : ℕ} {a b : A} : ∥a = b∥ₙ → |a|ₙ₊₁ = |b|ₙ₊₁ :=
  Trunc.rec (Id.ap Trunc.elem) (Trunc.uniq (n + 1) _ _)

  hott definition decode : Π (a b : ∥A∥ₙ₊₁), idTrunc a b → a = b :=
  Trunc.ind₂ (@decodeElem A n) (λ _ _, piRespectsImpl _ (hlevel.cumulative _ (Trunc.uniq _) _ _))

  hott lemma decodeIdpTrunc : Π (a : ∥A∥ₙ₊₁), decode a a (idpTrunc a) = idp a :=
  begin
    apply Trunc.ind; intro; reflexivity; intro a;
    apply hlevel.cumulative; apply hlevel.cumulative;
    apply @Trunc.uniq A (n + 1)
  end

  open GroundZero.Proto (idfun)

  hott lemma encodeDecodeElem {a b : A} : encode ∘ decode |a|ₙ₊₁ |b|ₙ₊₁ ~ idfun :=
  begin
    apply Trunc.ind; intro p; induction p; reflexivity;
    intro; apply hlevel.cumulative; apply @Trunc.uniq (a = b) n
  end

  hott lemma encodeDecode : Π {a b : ∥A∥ₙ₊₁}, encode ∘ decode a b ~ idfun :=
  begin
    apply Trunc.ind₂; apply encodeDecodeElem;
    { intros; apply piRespectsNType; intro;
      apply hlevel.cumulative; apply hlevel.cumulative;
      apply idTruncTrunc }
  end

  hott lemma decodeEncode {a b : ∥A∥ₙ₊₁} : decode a b ∘ encode ~ idfun :=
  begin intro p; induction p; apply decodeIdpTrunc end

  hott theorem idTruncEquiv (a b : ∥A∥ₙ₊₁) : (a = b) ≃ idTrunc a b :=
  Equiv.intro encode (decode a b) decodeEncode encodeDecode

  hott corollary truncElemEqEquiv (a b : A) : (|a|ₙ₊₁ = |b|ₙ₊₁) ≃ ∥a = b∥ₙ :=
  idTruncEquiv |a|ₙ₊₁ |b|ₙ₊₁

  hott corollary encodeElem {a b : A} : |a|ₙ₊₁ = |b|ₙ₊₁ → ∥a = b∥ₙ :=
  encode

  hott lemma encodeElemDecodeElem {A : Type u} {n : ℕ} {a b : A}
    (p : ∥a = b∥ₙ) : encodeElem (decodeElem p) = p :=
  @encodeDecodeElem hott% n A a b p

  hott lemma decodeElemPred {A : Type u} {n : ℕ} {a b : A} : ∥a = b∥ₙ → |a|ₙ = |b|ₙ :=
  Trunc.rec (Id.ap Trunc.elem) (hlevel.cumulative _ (Trunc.uniq n _ _))

  hott corollary idElemPred {a b : A} : |a|ₙ₊₁ = |b|ₙ₊₁ → |a|ₙ = |b|ₙ :=
  decodeElemPred ∘ encodeElem
end HITs.Trunc

namespace Types
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
    λ b c', Trunc.ap (ap Sigma.fst) (Trunc.encodeElem (H |c|₁ |⟨b, c'⟩|₁))

    hott lemma encodeDecode (C : Cover A) (c₁ c₂ : C.total) (H : prop ∥C.total∥₁) :
      encode C c₁ c₂.1 (decode C c₁ H c₂.1 c₂.2) = c₂.2 :=
    begin
      induction Trunc.encodeElem (H |c₁|₁ |c₂|₁);
      { case elemπ p =>
        induction p; transitivity; apply ap (encode _ _ _); apply ap (Trunc.ap _);
        apply ap Trunc.encodeElem; show _ = idp _; apply propIsSet; exact H; reflexivity };
      { apply zeroEqvSet.left; apply propIsSet; apply (C c₂.1).2 }
    end

    open GroundZero.Proto (idfun)

    hott lemma decodeEncode (C : Cover A) (c : C.total) (H : prop ∥C.total∥₁) :
      Π b, decode C c H b ∘ encode C c b ~ idfun :=
    begin
      intro b; apply Trunc.ind;
      { intro p; induction p; dsimp; transitivity; apply ap (Trunc.ap _);
        apply ap Trunc.encodeElem; show _ = idp _; apply propIsSet;
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

  open GroundZero.Algebra (Homotopy)

  hott definition covGroupSet {A : Type u} (a : A) (H : is-0-connected A) :
    Cover A → Σ (G : Set u), Homotopy a 0 ⮌ G.1 :=
  λ C, ⟨C a, ⟨λ x, Trunc.rec (λ g, transport (λ y, (C y).1) g x) (zeroEqvSet.left (C a).2),
              (idp, Trunc.ind₂ (λ g h x, (@transportcom A (λ y, (C y).1) _ _ _ _ _ _)⁻¹)
                               (λ _ _, piRespectsNType 0 (λ _, zeroEqvSet.left (propIsSet ((C a).2 _ _)))))⟩⟩
end Types

end GroundZero
