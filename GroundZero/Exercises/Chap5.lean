import GroundZero.Exercises.Chap4
import GroundZero.Types.Lost
import GroundZero.Types.W

open GroundZero.Types
open GroundZero.Proto
open GroundZero

universe u v w

-- Exercise 5.1

namespace «5.1»
  /-
    Another useful example is the type List(A) of finite lists of elements of some type A,
    which has constructors
    • nil : List(A)
    • cons : A → List(A) → List(A).
  -/

  variable (List : Type → Type)

  variable (A : Type) (nil : List A) (cons : A → List A → List A)

  hott definition indSig :=
  Π (C : List A → Type), C nil → (Π (x : A) (xs : List A), C xs → C (cons x xs)) → Π ys, C ys

  variable (ind : indSig List A nil cons)

  variable (C : List A → Type) (cz : C nil) (cs : Π (x : A) (xs : List A), C xs → C (cons x xs))

  hott definition indβruleSig₁ :=
  ind C cz cs nil = cz

  hott definition indβruleSig₂ :=
  Π (x : A) (xs : List A), ind C cz cs (cons x xs) = cs x xs (ind C cz cs xs)
end «5.1»

-- Exercise 5.2

namespace «5.2»
  open Nat (zero succ)

  hott definition idfun₁ : ℕ → ℕ :=
  λ n, n

  hott definition idfun₂ : ℕ → ℕ
  | zero   => zero
  | succ n => succ (idfun₂ n)

  hott definition ez : ℕ         := zero
  hott definition es : ℕ → ℕ → ℕ := λ n m, succ m

  #failure idfun₁ ≡ idfun₂

  #success idfun₁ zero ≡ ez
  #success idfun₂ zero ≡ ez

  variable (n : ℕ)
  #success idfun₁ (succ n) ≡ es n (idfun₁ n)
  #success idfun₂ (succ n) ≡ es n (idfun₂ n)
end «5.2»

-- Exercise 5.3

namespace «5.3»
  open Nat (zero succ)

  variable {E : Type u} {e : E}

  hott definition ez₁ : E         := e
  hott definition es₁ : ℕ → E → E := λ n ε, ε

  hott definition ez₂ : E         := e
  hott definition es₂ : ℕ → E → E := λ n _, e

  #failure @es₁ E ≡ @es₂ E e : ℕ → E → E

  hott definition f : ℕ → E :=
  λ _, e

  #success (@f E e) zero ≡ @ez₁ E e
  #success (@f E e) zero ≡ @ez₂ E e

  variable (n : ℕ)
  #success (@f E e) (succ n) ≡ (@es₁ E)   n (@f E e n)
  #success (@f E e) (succ n) ≡ (@es₂ E e) n (@f E e n)
end «5.3»

-- Exercise 5.4

hott example (E : 𝟐 → Type u) : (E false × E true) ≃ (Π b, E b) :=
familyOnBool

-- Exercise 5.5

namespace «5.5»
  open Types Equiv Structures open Nat (succ) open Types.Id (ap) open HITs.Interval (happly)

  variable (E : ℕ → Type u)

  hott example : (E 0 × Π n, E (n + 1)) ≃ (Π n, E n) :=
  begin
    fapply Equiv.intro;
    { intro (e₀, eₛ); exact λ | 0 => e₀ | succ n => eₛ n };
    { intro e; exact (e 0, λ n, e (n + 1)) };
    { intro (e₀, eₛ); apply Product.prod;
      reflexivity; reflexivity };
    { intro e; apply Theorems.funext; apply Nat.rec;
      reflexivity; intros; reflexivity }
  end

  hott definition indCod := E 0 × (Π n, E n → E (n + 1))
  hott definition indDom := Π n, E n

  hott definition indNat : indCod E → indDom E :=
  λ (e₀, eₛ), Nat.rec e₀ eₛ

  -- just like in 5.3
  hott definition indVal₁ : indCod (λ _, 𝟐) := (false, λ _ _, false)
  hott definition indVal₂ : indCod (λ _, 𝟐) := (false, λ _ b, b)

  hott lemma valTriv₁ : indNat (λ _, 𝟐) indVal₁ ~ λ _, false
  | 0 => idp false | succ _ => idp false

  hott lemma valTriv₂ : indNat (λ _, 𝟐) indVal₂ ~ λ _, false
  | 0 => idp false | succ n => valTriv₂ n

  hott lemma valIneq : indVal₁ ≠ indVal₂ :=
  λ np, ffNeqTt (happly (happly (ap Prod.pr₂ np) 1) true)

  hott example : ¬(Π E, biinv (indNat E)) :=
  λ H, valIneq (Equiv.eqvInj ⟨indNat (λ _, 𝟐), H (λ _, 𝟐)⟩ indVal₁ indVal₂
                             (Theorems.funext (λ _, valTriv₁ _ ⬝ (valTriv₂ _)⁻¹)))
end «5.5»

-- Exercise 5.7

namespace «5.7»
  variable (C : Type) (c : (C → 𝟎) → C) (elim : Π (P : Type), ((C → 𝟎) → (P → 𝟎) → P) → C → P)

  hott example : 𝟎 :=
  have nc := elim 𝟎 (λ g i, g (c g));
  nc (c nc)
end «5.7»

-- Exercise 5.8

namespace «5.8»
  variable (D : Type) (scott : (D → D) → D)
           (elim : Π (P : Type), ((D → D) → (D → P) → P) → D → P)

  hott example : 𝟎 :=
  have nd := elim 𝟎 (λ f g, g (scott f));
  nd (scott idfun)

  -- Computation rule seems to be not required here.
  variable (elimβrule : Π P h α, elim P h (scott α) = h α (elim P h ∘ α))
end «5.8»

-- Exercise 5.9

namespace «5.9»
  variable {A L : Type} (lawvere : (L → A) → L) (elim : Π (P : Type), ((L → A) → P) → L → P)

  hott definition fix (f : A → A) : A :=
  have φ := elim A (λ α, f (α (lawvere α)));
  φ (lawvere φ)

  variable (elimβrule : Π P h α, elim P h (lawvere α) = h α)

  hott theorem hasFixpoint (f : A → A) (a : A) : f (fix lawvere elim f) = fix lawvere elim f :=
  begin symmetry; apply elimβrule end
end «5.9»

-- Exercise 5.10

namespace «5.10»
  variable {L : Type} (lawvere : (L → 𝟏) → L)

  hott definition indSig :=
  Π (C : L → Type), (Π f, C (lawvere f)) → Π x, C x

  variable (ind : indSig lawvere)

  variable (C : L → Type) (h : Π f, C (lawvere f))

  hott definition indβruleSig :=
  Π f, ind C h (lawvere f) = h f

  open Structures (contr unitIsProp) open Theorems (funext) open Types.Id (ap)

  hott example : contr L :=
  ⟨lawvere (λ _, ★), ind _ (λ _, ap lawvere (funext (λ _, unitIsProp _ _)))⟩
end «5.10»

-- Exercise 5.11

hott example (A : Type u) : Lost A ≃ 𝟎 :=
Lost.isZero

-- Exercise 5.12

namespace «5.12»
  open Structures Types.Equiv open HITs.Interval (happly) open Types.Id (ap)

  variables {A : Type u} {B : A → Type v} (H : prop A)

  hott example : prop (W x, B x) :=
  W.isProp H

  hott example : (W x, B x) ≃ (Σ x, ¬(B x)) :=
  W.propEquivSig H

  hott example : Wd A B :=
  let ε : prop (Σ x, ¬(B x)) := sigProp H (λ _, notIsProp);
  let Φ {x y : A} : B x → B y := transport B (H x y);

  let sup (a : A) (f : B a → Σ (x : A), ¬B x) : Σ x, ¬(B x) :=
  ⟨a, λ b, (f b).2 (Φ b)⟩;

  ⟨Σ x, ¬(B x), sup,
   λ E e, ⟨λ w, transport E (ε _ w) (e w.1 (λ _, w) (λ b, explode (w.2 b))),
           λ a f, (happly (apd (e a) (@implProp (B a) _ ε (λ _, sup a f) f))⁻¹ _
                 ⬝ happly (transportCharacterization _ _) _
                 ⬝ transportComp _ _ _ _
                 ⬝ bimap (@transport (Σ (x : A), ¬B x) E (sup a (λ _, sup a f)) (sup a f))
                         (propIsSet ε _ _ _ _)
                         (ap (e a _) (Theorems.funext (λ b, explode ((f b).2 (Φ b))))))⁻¹⟩⟩
end «5.12»

-- Exercise 5.13

namespace «5.13»
  variables {A : Type u} {B : A → Type v}

  hott example : (Σ x, ¬(B x)) → (W x, B x) :=
  W.propEncode

  hott example : (W x, B x) → ¬(Π x, B x) :=
  W.propDecodeNeg
end «5.13»

-- Exercise 5.14

namespace «5.14»
  open Structures (dec)

  variables {A : Type u} {B : A → Type v} (H : Π x, dec (B x))

  hott example : (W x, B x) → (Σ x, ¬(B x)) :=
  W.propDecodeDec H
end «5.14»

-- Exercise 5.17

namespace «5.17»
  variables {A : Type u} {B : A → Type v}

  hott example : ¬(W x, B x) ≃ ¬(Σ x, ¬(B x)) :=
  W.negEquiv
end «5.17»
