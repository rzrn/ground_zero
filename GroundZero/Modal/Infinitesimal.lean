import GroundZero.Types.Equiv

open GroundZero.Types.Equiv (biinv)
open GroundZero.Types.Id (ap)
open GroundZero.Types
open GroundZero.Proto

/-
  Infinitesimal shape modality or coreduction.

  https://github.com/rzrn/anders/blob/master/library/modal/infinitesimal.anders
  https://www.math.kit.edu/iag3/~wellen/media/diss.pdf
  https://arxiv.org/pdf/1806.05966.pdf

  * HoTT 7.7 Modalities
-/

namespace GroundZero.HITs.Infinitesimal
universe u v w

hott axiom Im (A : Type u) : Type u := Opaque A

notation "ℑ" => Im

section
  variable {A : Type u}

  hott axiom ι : A → ℑ A := Opaque.intro
  hott axiom μ : ℑ (ℑ A) → ℑ A := Opaque.value

  hott axiom Im.ind {B : ℑ A → Type v} (f : Π x, ℑ (B (ι x))) : Π x, ℑ (B x) := Opaque.ind f

  hott axiom κ {a b : ℑ A} : ℑ (a = b) → a = b := Opaque.value
end

hott definition Im.indβrule {A : Type u} {B : ℑ A → Type v} {f : Π x, ℑ (B (ι x))} (a : A) : Im.ind f (ι a) = f a :=
idp (f a)

hott definition μcom {A : Type u} : μ ∘ ι ~ @idfun (ℑ A) :=
idp

hott definition ιcoh {A : Type u} : ι ∘ μ ~ @idfun (ℑ (ℑ A)) :=
λ w, κ (@Im.ind (ℑ A) (λ x, ι (μ x) = x) (λ x, ι (idp (ι x))) w)

hott definition κ.right {A : Type u} {a b : ℑ A} : @κ A a b ∘ ι ~ idfun :=
idp

hott definition κ.left {A : Type u} {a b : ℑ A} : ι ∘ @κ A a b ~ idfun :=
λ ρ, κ (@Im.ind (a = b) (λ ρ, ι (κ ρ) = ρ) (λ p, ι (ap ι (κ.right p))) ρ)

hott definition isCoreduced (A : Type u) := biinv (@ι A)

hott definition Im.coreduced (A : Type u) : isCoreduced (ℑ A) :=
Qinv.toBiinv ι ⟨μ, (ιcoh, μcom)⟩

hott definition Im.idCoreduced {A : Type u} (a b : ℑ A) : isCoreduced (a = b) :=
Qinv.toBiinv ι ⟨κ, (κ.left, κ.right)⟩

hott definition Im.indε {A : Type u} {B : ℑ A → Type v}
  (η : Π i, isCoreduced (B i)) (f : Π x, B (ι x)) : Π x, B x :=
λ a, (η a).1.1 (@Im.ind A B (λ x, ι (f x)) a)

hott definition Im.indεβrule {A : Type u} {B : ℑ A → Type v}
  (η : Π i, isCoreduced (B i)) (f : Π x, B (ι x)) : Π x, Im.indε η f (ι x) = f x :=
λ x, (η (ι x)).1.2 (f x)

section
  variable {A : Type u} {B : Type v} (f : A → ℑ B)

  hott definition Im.rec : Im A → ℑ B := Im.ind f
  hott definition Im.recβrule : Π x, Im.rec f (ι x) = f x := Im.indβrule
end

section
  variable {A : Type u} {B : Type v} (η : isCoreduced B) (f : A → B)

  hott definition Im.recε : Im A → B := Im.indε (λ _, η) f

  hott definition Im.recεβrule : Π x, Im.recε η f (ι x) = f x :=
  Im.indεβrule (λ _, η) f
end

section
  variable {A : Type u} {B : Type v} (f : A → B)

  hott definition Im.ap : ℑ A → ℑ B := Im.rec (ι ∘ f)
  hott definition Im.naturality (x : A) : Im.ap f (ι x) = ι (f x) := idp (ι (f x))
end

hott definition Im.apIdfun {A : Type u} : Im.ap idfun ~ @idfun (ℑ A) :=
Im.indε (λ _, Im.idCoreduced _ _) (λ x, idp (ι x))

hott definition Im.apCom {A : Type u} {B : Type v} {C : Type w}
  (f : B → C) (g : A → B) : Im.ap (f ∘ g) ~ Im.ap f ∘ Im.ap g :=
Im.indε (λ _, Im.idCoreduced _ _) (λ x, idp (ι (f (g x))))

end GroundZero.HITs.Infinitesimal
