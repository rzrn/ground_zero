import GroundZero.Modal.Infinitesimal
import GroundZero.Structures

open GroundZero.Types GroundZero.Proto
open GroundZero.Types.Equiv
open GroundZero

namespace GroundZero.HITs.Infinitesimal
universe u v w

-- infinitesimally close
hott definition infinitesimallyClose {A : Type u} (a b : A) := ι a = ι b
infix:80 " ~ " => infinitesimallyClose

hott definition Disc {A : Type u} (a : A) := Σ b, a ~ b
notation "𝔻" => Disc

hott definition discBundle (A : Type u) := Σ (a : A), 𝔻 a
notation "T∞" => discBundle

hott definition center {A : Type u} (a : A) : 𝔻 a := ⟨a, idp (ι a)⟩

section
  variable {A : Type u} {B : Type v} (f : A → B)

  hott definition infProxAp {a b : A} : a ~ b → f a ~ f b :=
  λ ρ, Id.ap (Im.ap f) ρ

  hott definition d (x : A) : 𝔻 x → 𝔻 (f x) :=
  λ ε, ⟨f ε.1, infProxAp f ε.2⟩

  hott definition bundleAp : T∞ A → T∞ B :=
  λ τ, ⟨f τ.1, d f τ.1 τ.2⟩
end

hott lemma infProxApIdp {A : Type u} {a b : A} (ρ : a ~ b) : infProxAp idfun ρ = ρ :=
begin
  transitivity; apply mapWithHomotopy; apply Im.apIdfun;
  transitivity; apply Id.rid; apply Equiv.idmap
end

hott lemma infProxApCom {A : Type u} {B : Type v} {C : Type w} (f : B → C) (g : A → B)
  {a b : A} (ρ : a ~ b) : infProxAp (f ∘ g) ρ = infProxAp f (infProxAp g ρ) :=
begin
  transitivity; apply mapWithHomotopy; apply Im.apCom;
  transitivity; apply Id.rid; apply mapOverComp
end

hott definition diffComHom {A : Type u} {B : Type v} {C : Type w}
  (f : B → C) (g : A → B) {x : A} (ε : 𝔻 x) : d (f ∘ g) x ε = d f (g x) (d g x ε) :=
Id.ap (Sigma.mk _) (infProxApCom f g _)

hott theorem diffCom {A : Type u} {B : Type v} {C : Type w} (f : B → C) (g : A → B)
  {x : A} : d (f ∘ g) x = (d f) (g x) ∘ d g x :=
Theorems.funext (diffComHom f g)

hott lemma diffIdfun {A : Type u} (x : A) (ε : 𝔻 x) : d idfun x ε = ε :=
Id.ap (Sigma.mk _) (infProxApIdp _)

hott definition isHomogeneous (A : Type u) :=
Σ (e : A) (t : A → A ≃ A), Π x, t x e = x

hott definition Homogeneous :=
Σ (A : Type u), isHomogeneous A

hott instance : Coe Homogeneous (Type u) := ⟨Sigma.fst⟩

hott definition Homogeneous.trivial : Homogeneous :=
⟨𝟏, ★, λ _, ideqv 𝟏, λ ★, idp ★⟩

hott definition Homogeneous.cart (A B : Homogeneous) : Homogeneous :=
⟨A.1 × B.1, ⟨(A.2.1, B.2.1), λ w, prodEquiv (A.2.2.1 w.1) (B.2.2.1 w.2),
             λ w, Product.prod (A.2.2.2 w.1) (B.2.2.2 w.2)⟩⟩

hott instance : HMul Homogeneous Homogeneous Homogeneous := ⟨Homogeneous.cart⟩

end GroundZero.HITs.Infinitesimal
