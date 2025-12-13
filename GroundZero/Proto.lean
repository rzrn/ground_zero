import GroundZero.Meta.Basic

namespace GroundZero.Proto
universe u v w

hott definition idfun {A : Sort u} : A → A :=
λ a, a

inductive Empty : Type u

attribute [induction_eliminator] Empty.casesOn

hott definition Iff (A : Type u) (B : Type v) := (A → B) × (B → A)

infix:30 (priority := high) " ↔ " => Iff

hott definition Iff.left  {A : Type u} {B : Type v} (w : A ↔ B) : A → B := w.1
hott definition Iff.right {A : Type u} {B : Type v} (w : A ↔ B) : B → A := w.2

hott definition Iff.refl {A : Type u} : A ↔ A :=
⟨idfun, idfun⟩

hott definition Iff.symm {A : Type u} {B : Type v} : (A ↔ B) → (B ↔ A) :=
λ p, ⟨p.right, p.left⟩

hott definition Iff.comp {A : Type u} {B : Type v} {C : Type w} :
  (A ↔ B) → (B ↔ C) → (A ↔ C) :=
λ p q, ⟨q.left ∘ p.left, p.right ∘ q.right⟩

hott instance : @Reflexive  (Type u) Iff := ⟨@Iff.refl⟩
hott instance : @Symmetric  (Type u) Iff := ⟨@Iff.symm⟩
hott instance : @Transitive (Type u) Iff := ⟨@Iff.comp⟩

notation "𝟎" => Empty
notation "𝟐" => Bool
notation "ℕ" => Nat

hott definition explode {A : Sort u} : 𝟎 → A :=
Empty.rec (λ _, A) -- “nomatch” uses large elimination

hott definition Bool.elim {A : Sort u} : A → A → 𝟐 → A :=
λ b₁ b₂ b, @Bool.casesOn (λ _, A) b b₁ b₂

hott abbreviation Bottom := Empty.{0}
notation (priority := low) "⊥" => Bottom

inductive Identity (A : Type u)
| elem : A → Identity A

attribute [induction_eliminator] Identity.casesOn

hott definition Identity.elim {A : Type u} : Identity A → A
| Identity.elem a => a

hott definition Identity.lift {A : Type u} {B : Type v}
  (f : A → B) : Identity A → Identity B
| Identity.elem a => Identity.elem (f a)

hott definition Identity.lift₂ {A : Type u} {B : Type v} {C : Type w}
  (f : A → B → C) : Identity A → Identity B → Identity C
| Identity.elem a, Identity.elem b => Identity.elem (f a b)

end GroundZero.Proto
