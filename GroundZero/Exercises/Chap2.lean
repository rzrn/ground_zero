import GroundZero.Theorems.Univalence
import GroundZero.Theorems.Pullback

open GroundZero GroundZero.Types
open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Proto

open GroundZero.Structures (prop contr)

universe u v u' v' w w' k k'

-- exercise 2.1

section
  variable {A : Type u} {a b c : A}

  hott definition trans₁ (p : a = b) (q : b = c) : a = c :=
  @J₁ A a (λ x _, x = c → a = c) (@J₁ A a (λ x _, a = x) (idp a) c) b p q

  infixl:99 " ⬝₁ " => trans₁

  hott definition trans₂ (p : a = b) (q : b = c) : a = c :=
  @J₁ A a (λ x _, x = c → a = c) idfun b p q

  infixl:99 " ⬝₂ " => trans₂

  hott definition trans₃ (p : a = b) (q : b = c) : a = c :=
  @J₁ A b (λ x _, a = b → a = x) idfun c q p

  infixl:99 " ⬝₃ " => trans₃

  hott remark eq₁₂ (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₂ q :=
  begin induction p; induction q; reflexivity end

  hott remark eq₂₃ (p : a = b) (q : b = c) : p ⬝₂ q = p ⬝₃ q :=
  begin induction p; induction q; reflexivity end

  hott remark eq₁₃ (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₃ q :=
  begin induction p; induction q; reflexivity end
end

-- exercise 2.2

section
  variable {A : Type u} {a b c : A} (p : a = b) (q : b = c)

  hott example : eq₁₂ p q ⬝ eq₂₃ p q = eq₁₃ p q :=
  begin induction p; induction q; reflexivity end
end

-- exercise 2.3

section
  variable {A : Type u} {a b c : A}

  hott definition trans₄ (p : a = b) (q : b = c) : a = c :=
  @J₁ A b (λ x _, a = b → a = x) (@J₁ A a (λ x _, a = x) (idp a) b) c q p

  infixl:99 " ⬝₄ " => trans₄

  /-
  hott example (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₄ q := idp _
  hott example (p : a = b) (q : b = c) : p ⬝₂ q = p ⬝₄ q := idp _
  hott example (p : a = b) (q : b = c) : p ⬝₃ q = p ⬝₄ q := idp _
  -/

  hott example (p : a = b) (q : b = c) : p ⬝₁ q = p ⬝₄ q :=
  begin induction p; induction q; reflexivity end
end

-- exercise 2.4

hott definition nPath (A : Type u) : ℕ → Type u
| Nat.zero   => A
| Nat.succ n => Σ (a b : nPath A n), a = b

hott definition boundary {A : Type u} {n : ℕ} :
  nPath A (n + 1) → (nPath A n) × (nPath A n) :=
λ ⟨a, b, _⟩, (a, b)

-- exercise 2.5

namespace «2.5»
  variable {A : Type u} {B : Type v} {x y : A} (p : x = y)

  hott definition transconst (b : B) : transport (λ _, B) p b = b :=
  begin induction p; reflexivity end

  hott definition f (φ : A → B) : φ x = φ y → transport (λ _, B) p (φ x) = φ y :=
  λ q, transconst p (φ x) ⬝ q

  hott definition g (φ : A → B) : transport (λ _, B) p (φ x) = φ y → φ x = φ y :=
  λ q, (transconst p (φ x))⁻¹ ⬝ q

  hott example (φ : A → B) : f p φ ∘ g p φ ~ id :=
  begin induction p; reflexivity end

  hott example (φ : A → B) : g p φ ∘ f p φ ~ id :=
  begin induction p; reflexivity end
end «2.5»

-- exercise 2.6

hott example {A : Type u} {x y z : A} (p : x = y) : biinv (@Id.trans A x y z p) :=
begin apply Prod.mk <;> existsi Id.trans p⁻¹ <;> intro q <;> induction p <;> induction q <;> reflexivity end

-- exercise 2.7

namespace «2.7»
  variable {A : Type u} {A' : Type u'} {B : A → Type v} {B' : A' → Type v'}
           (g : A → A') (h : Π a, B a → B' (g a))

  hott definition φ (x : Σ a, B a) : Σ a', B' a' := ⟨g x.1, h x.1 x.2⟩

  hott definition prodMap : Π (x y : Σ a, B a) (p : x.1 = y.1) (q : x.2 =[p] y.2),
      ap (φ g h) (Sigma.prod p q)
    = @Sigma.prod A' B' (φ g h x) (φ g h y)
        (@ap A A' x.1 y.1 g p) (depPathMap' g h q) :=
  begin
    intro ⟨x, H⟩ ⟨y, G⟩ (p : x = y); induction p;
    intro (q : H = G); induction q; reflexivity
  end
end «2.7»

-- exercise 2.8

namespace «2.8»
  variable {A A' B B' : Type u} (g : A → A') (h : B → B')

  hott definition φ : A + B → A' + B' :=
  Coproduct.elim (Coproduct.inl ∘ g) (Coproduct.inr ∘ h)

  hott definition ρ : Π {x y : A + B}, Coproduct.code x y → Coproduct.code (φ g h x) (φ g h y)
  | Sum.inl _, Sum.inl _, p => ap _ p
  | Sum.inr _, Sum.inl _, p => explode p
  | Sum.inl _, Sum.inr _, p => explode p
  | Sum.inr _, Sum.inr _, p => ap _ p

  hott definition mapPathSum (x y : A + B) : Π p,
      ap (φ g h) (Coproduct.pathSum x y p)
    = Coproduct.pathSum (φ g h x) (φ g h y) (ρ g h p) :=
  begin
    match x, y with
    | Sum.inl x, Sum.inl y => _
    | Sum.inr _, Sum.inl _ => _
    | Sum.inl _, Sum.inr _ => _
    | Sum.inr x, Sum.inr y => _;

    { intro (p : x = y); induction p; reflexivity };
    { intro; apply explode; assumption };
    { intro; apply explode; assumption };
    { intro (p : x = y); induction p; reflexivity }
  end
end «2.8»

-- exercise 2.9

hott definition Coproduct.depUnivProperty (A : Type u) (B : Type v) (X : A + B → Type w) :
  (Π x, X x) ≃ (Π a, X (Coproduct.inl a)) × (Π b, X (Coproduct.inr b)) :=
begin
  fapply Sigma.mk; { intro φ; exact (λ a, φ (Coproduct.inl a), λ b, φ (Coproduct.inr b)) };
  apply Qinv.toBiinv; fapply Sigma.mk;
  { intros φ x; induction x using Sum.casesOn; apply φ.1; apply φ.2 };
  apply Prod.mk; { intro (φ, ψ); reflexivity };
  { intro f; apply Theorems.funext; intro z; induction z using Sum.casesOn <;> reflexivity }
end

hott definition Coproduct.univProperty (A : Type u) (B : Type v) (X : Type w) :
  (A + B → X) ≃ (A → X) × (B → X) :=
Coproduct.depUnivProperty A B (λ _, X)

-- exercise 2.10

hott example (A : Type u) (B : A → Type v) (C : (Σ x, B x) → Type w) :
  (Σ x, Σ y, C ⟨x, y⟩) ≃ (Σ p, C p) :=
Sigma.assoc C

-- exercise 2.11

namespace «2.11»
  variable {P : Type k} {A : Type u} {B : Type v} {C : Type w}
           (η : pullbackSquare P A B C)

  hott example : P ≃ pullback C η.1.right η.1.bot :=
  Theorems.pullbackCorner η
end «2.11»

-- exercise 2.12

namespace «2.12»
  variable {A B C D E F : Type u}
           {f : A → C} {g : C → E} {i : A → B} {j : C → D}
           {k : E → F} {h : B → D} {s : D → F}
           (α : j ∘ f = h ∘ i) (β : k ∘ g = s ∘ j)

  hott definition left  : hcommSquare A C B D := ⟨j, h, f, i, α⟩
  hott definition right : hcommSquare C E D F := ⟨k, s, g, j, β⟩

  hott definition outer : hcommSquare A E B F :=
  ⟨k, s ∘ h, g ∘ f, i, @ap (C → F) (A → F) _ _ (· ∘ f) β
                     ⬝ @ap _ (A → F) _ _ (s ∘ ·) α⟩

  hott theorem pullbackLemma (H : (right β).isPullback) :
    (left α).isPullback ↔ (outer α β).isPullback :=
  sorry
end «2.12»

-- exercise 2.13

hott example : (𝟐 ≃ 𝟐) ≃ 𝟐 := Theorems.Equiv.boolEquivEqvBool

-- exercise 2.14

-- Assume Γ, p : x = y ⊢ x ≡ y, let Γ = A : U, a : A. Then Γ, b : A, p : a = b ⊢ p = idp a : U,
-- because in this context we have p : a = b, so a ≡ b, so p : a = a.
-- “@Id.rec A a (λ b, p = idp a) (λ x, idp a) a” is then well-typed.
-- This means that we have a proof of “Π (p : a = a), p = idp a” leading to contradiction.

-- exercise 2.15

hott definition transportMap {A : Type u} {B : A → Type v} {x y : A} (p : x = y) :
  transport B p = idtoeqv (ap B p) :=
begin induction p; reflexivity end

-- exercise 2.18

hott definition transportSquare {A : Type u} {B : A → Type v} {f g : Π x, B x} (H : f ~ g) {x y : A} (p : x = y) :
  ap (transport B p) (H x) ⬝ apd g p = apd f p ⬝ H y :=
begin induction p; transitivity; apply Id.rid; apply Equiv.idmap end

-- exercise 2.19

hott example : @Id (Σ A, A) ⟨𝟐, false⟩ ⟨𝟐, true⟩ :=
Sigma.prod (ua negBoolEquiv) (uaβ _ _)
