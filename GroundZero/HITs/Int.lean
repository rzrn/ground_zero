import GroundZero.Theorems.Nat

open GroundZero.Types.Id (ap)
open GroundZero.Types
open GroundZero

/-
  Integers ℤ as a quotient of ℕ × ℕ.
  * HoTT 6.10, remark 6.10.7
-/

namespace GroundZero.HITs

hott definition Int.rel (w₁ w₂ : ℕ × ℕ) : Type :=
w₁.1 + w₂.2 = w₁.2 + w₂.1

hott definition Int := Quotient Int.rel
local notation "ℤ" => Int

namespace Nat.Product
  hott definition add (x y : ℕ × ℕ) : ℕ × ℕ :=
  (x.1 + y.1, x.2 + y.2)

  noncomputable instance : Add (ℕ × ℕ) := ⟨add⟩

  hott definition mul (x y : ℕ × ℕ) : ℕ × ℕ :=
  (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)

  noncomputable instance : Mul (ℕ × ℕ) := ⟨mul⟩
end Nat.Product

namespace Int
  universe u v

  hott definition mk : ℕ × ℕ → ℤ := Quotient.elem
  hott definition elem (a b : ℕ) : ℤ := Quotient.elem (a, b)

  hott definition pos (n : ℕ) := mk (n, 0)
  noncomputable instance (n : ℕ) : OfNat ℤ n := ⟨pos n⟩

  hott definition neg (n : ℕ) := mk (0, n)

  hott definition glue {a b c d : ℕ} (H : a + d = b + c) : mk (a, b) = mk (c, d) :=
  Quotient.line H

  hott definition ind {C : ℤ → Type u} (mkπ : Π x, C (mk x))
    (glueπ : Π {a b c d : ℕ} (H : a + d = b + c),
      mkπ (a, b) =[glue H] mkπ (c, d)) (x : ℤ) : C x :=
  begin fapply Quotient.ind; exact mkπ; intros x y H; apply glueπ end

  hott definition rec {C : Type u} (mkπ : ℕ × ℕ → C)
    (glueπ : Π {a b c d : ℕ} (H : a + d = b + c),
      mkπ (a, b) = mkπ (c, d)) : ℤ → C :=
  begin fapply Quotient.rec; exact mkπ; intros x y H; apply glueπ H end

  noncomputable instance : Neg Int :=
  ⟨rec (λ x, mk ⟨x.2, x.1⟩) (λ H, glue H⁻¹)⟩

  hott definition addRight (a b k : ℕ) : mk (a, b) = mk (a + k, b + k) :=
  begin
    apply glue; transitivity; symmetry; apply Theorems.Nat.assoc;
    symmetry; transitivity; symmetry; apply Theorems.Nat.assoc;
    apply ap (λ n, n + k); apply Theorems.Nat.comm
  end
end Int
end GroundZero.HITs
