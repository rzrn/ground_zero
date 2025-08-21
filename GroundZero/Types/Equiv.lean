import GroundZero.Meta.Trust

open GroundZero.Proto (idfun Identity Identity.elem Identity.elim)
open GroundZero.Types.Id (ap apΩ)

universe u v w k

hott definition AS {A : Type u} {B : Type v} {C : Type w} (x : A → B → C) (y : A → B) (z : A) := x z (y z)

section
  variable {A : Type u} {B : Type v}

  hott definition Prod.Id {a c : A} {b d : B} (p : a = c) (q : b = d) : (a, b) = (c, d) :=
  begin induction p; induction q; reflexivity end

  hott definition Prod.intro : A → B → A × B := Prod.mk
  hott definition Prod.pr₁   : A × B → A     := Prod.fst
  hott definition Prod.pr₂   : A × B → B     := Prod.snd
end

namespace GroundZero.Types
namespace Equiv

  hott definition Homotopy {A : Type u} {B : A → Type v} (f g : Π x, B x) :=
  Π (x : A), f x = g x
  infix:80 " ~ " => Homotopy

  notation:80 f:81 " ≁ " g:81 => ¬(f ~ g)

  hott definition Homotopy.id {A : Type u} {B : A → Type v} (f : Π x, B x) : f ~ f :=
  begin intro x; reflexivity end

  hott definition Homotopy.symm {A : Type u} {B : A → Type v}
    (f g : Π (x : A), B x) (h : f ~ g) : g ~ f :=
  λ x, (h x)⁻¹

  hott definition Homotopy.trans {A : Type u} {B : A → Type v}
    {f g h : Π (x : A), B x} (p : f ~ g) (q : g ~ h) : f ~ h :=
  λ x, p x ⬝ q x

  namespace Homotopy
    variable {A : Type u} {B : Type v} {C : Type w}

    hott definition hcom {f₁ f₂ : B → C} {g₁ g₂ : A → B} (H : f₁ ~ f₂) (G : g₁ ~ g₂) : f₁ ∘ g₁ ~ f₂ ∘ g₂ :=
    λ x, H (g₁ x) ⬝ ap f₂ (G x)

    hott definition rwhs {f : B → C} {g₁ g₂ : A → B} (H : g₁ ~ g₂) : f ∘ g₁ ~ f ∘ g₂ :=
    hcom (id f) H

    hott definition lwhs {f₁ f₂ : B → C} {g : A → B} (H : f₁ ~ f₂) : f₁ ∘ g ~ f₂ ∘ g :=
    hcom H (id g)
  end Homotopy

  section
    variable {A : Type u} {B : A → Type v}
    hott instance : @Reflexive  (Π x, B x) (· ~ ·) := ⟨@Homotopy.id A B⟩
    hott instance : @Symmetric  (Π x, B x) (· ~ ·) := ⟨@Homotopy.symm A B⟩
    hott instance : @Transitive (Π x, B x) (· ~ ·) := ⟨@Homotopy.trans A B⟩
  end

  hott definition Homotopy.Id {A : Type u} {B : A → Type v}
    {f g : Π x, B x} (η : f = g) : f ~ g :=
  begin induction η; reflexivity end

  section
    variable {A : Type u} {B : Type v}

    hott definition linv (f : A → B) :=
    Σ (g : B → A), g ∘ f ~ idfun

    hott definition rinv (f : A → B) :=
    Σ (g : B → A), f ∘ g ~ idfun

    hott definition biinv (f : A → B) :=
    linv f × rinv f
  end

  hott definition homotopySquare {A : Type u} {B : Type v} {f g : A → B}
    (H : f ~ g) {x y : A} (p : x = y) : H x ⬝ ap g p = ap f p ⬝ H y :=
  begin induction p; apply Id.rid end
end Equiv

hott definition Equiv (A : Type u) (B : Type v) : Type (max u v) :=
Σ (f : A → B), Equiv.biinv f
infix:25 " ≃ " => Equiv

section
  variable {A : Type u} {B : Type v}

  hott definition isQinv (f : A → B) (g : B → A) :=
  (f ∘ g ~ idfun) × (g ∘ f ~ idfun)

  hott definition qinv (f : A → B) :=
  Σ (g : B → A), isQinv f g

  -- half adjoint equivalence
  hott definition ishae (f : A → B) :=
  Σ (g : B → A) (η : g ∘ f ~ id) (ϵ : f ∘ g ~ id), Π x, ap f (η x) = ϵ (f x)
end

hott definition fib {A : Type u} {B : Type v} (f : A → B) (y : B) := Σ (x : A), f x = y

hott definition total {A : Type u} (B : A → Type v) := Σ x, B x
hott definition fiberwise {A : Type u} (B : A → Type v) := Π x, B x

namespace Qinv
  open Equiv (biinv)
  open Id (ap)

  hott definition linvInv {A : Type u} {B : Type v}
    (f : A → B) (g : B → A) (h : B → A)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : g ∘ f ~ id :=
  let F₁ := λ x, H (g (f x));
  let F₂ := λ x, ap h (G (f x));
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ H x

  hott definition rinvInv {A : Type u} {B : Type v}
    (f : A → B) (g : B → A) (h : B → A)
    (G : f ∘ g ~ id) (H : h ∘ f ~ id) : f ∘ h ~ id :=
  let F₁ := λ x, ap (f ∘ h) (G x);
  let F₂ := λ x, ap f (H (g x));
  λ x, (F₁ x)⁻¹ ⬝ F₂ x ⬝ G x

  hott definition toBiinv {A : Type u} {B : Type v} (f : A → B) (q : qinv f) : biinv f :=
  (⟨q.1, q.2.2⟩, ⟨q.1, q.2.1⟩)

  hott definition ofBiinv {A : Type u} {B : Type v} (f : A → B) (F : biinv f) : qinv f :=
  ⟨F.2.1, (F.2.2, linvInv f F.2.1 F.1.1 F.2.2 F.1.2)⟩

  hott definition ideqv {A : Type u} : qinv (@idfun A) :=
  ⟨idfun, (idp, idp)⟩

  hott definition sym {A : Type u} {B : Type v} {f : A → B} (e : qinv f) : qinv e.1 :=
  ⟨f, (e.2.2, e.2.1)⟩

  hott definition com {A : Type u} {B : Type v} {C : Type w} {g : B → C} {f : A → B} :
    qinv g → qinv f → qinv (g ∘ f) :=
  λ e₁ e₂, ⟨e₂.1 ∘ e₁.1, (λ c, ap g (e₂.2.1 (e₁.1 c)) ⬝ e₁.2.1 c,
                          λ a, ap e₂.1 (e₁.2.2 (f a)) ⬝ e₂.2.2 a)⟩

  hott definition toEquiv {A : Type u} {B : Type v} {f : A → B} (e : qinv f) : A ≃ B :=
  ⟨f, (⟨e.1, e.2.2⟩, ⟨e.1, e.2.1⟩)⟩
end Qinv

namespace Equiv
  variable {A : Type u} {B : Type v}

  hott definition intro (f : A → B) (g : B → A) (H : g ∘ f ~ idfun) (G : f ∘ g ~ idfun) : A ≃ B :=
  ⟨f, (⟨g, H⟩, ⟨g, G⟩)⟩

  hott definition forward (e : A ≃ B) : A → B := e.fst
  hott instance forwardCoe : CoeFun (A ≃ B) (λ _, A → B) := ⟨forward⟩

  hott definition left  (e : A ≃ B) : B → A := e.2.1.1
  hott definition right (e : A ≃ B) : B → A := e.2.2.1

  hott definition leftForward  (e : A ≃ B) : e.left    ∘ e.forward ~ id := e.2.1.2
  hott definition forwardRight (e : A ≃ B) : e.forward ∘ e.right   ~ id := e.2.2.2

  hott lemma leftRight (e : A ≃ B) : e.left ~ e.right :=
  λ x, ap e.left (e.forwardRight x)⁻¹ ⬝ e.leftForward (e.right x)

  hott lemma forwardLeft (e : A ≃ B) : e.forward ∘ e.left ~ idfun :=
  begin apply Qinv.rinvInv; apply e.forwardRight; apply e.leftForward end

  hott lemma rightForward (e : A ≃ B) : e.right ∘ e.forward ~ idfun :=
  begin apply Qinv.linvInv; apply e.forwardRight; apply e.leftForward end

  hott definition symm (f : A ≃ B) : B ≃ A :=
  Qinv.toEquiv (Qinv.sym (Qinv.ofBiinv f.1 f.2))

  hott instance : @Symmetric (Type u) (· ≃ ·) := ⟨@Equiv.symm⟩

  hott lemma eqvInj (e : A ≃ B) (x y : A) (p : e.forward x = e.forward y) : x = y :=
  begin
    transitivity; symmetry; apply e.leftForward;
    transitivity; apply ap e.left;
    exact p; apply e.leftForward
  end

  hott lemma eqvLeftInj (e : A ≃ B) (x y : B) (p : e.left x = e.left y) : x = y :=
  begin
    transitivity; symmetry; apply e.forwardLeft;
    transitivity; apply ap e.forward;
    exact p; apply e.forwardLeft
  end

  hott lemma eqvRightInj (e : A ≃ B) (x y : B) (p : e.right x = e.right y) : x = y :=
  begin
    transitivity; symmetry; apply e.forwardRight;
    transitivity; apply ap e.forward;
    exact p; apply e.forwardRight
  end
end Equiv

namespace Equiv
  hott definition ideqv (A : Type u) : A ≃ A :=
  ⟨idfun, (⟨idfun, idp⟩, ⟨idfun, idp⟩)⟩

  hott instance : @Reflexive (Type u) (· ≃ ·) := ⟨ideqv⟩

  hott lemma inveqv {A : Type u} {a b : A} : (a = b) ≃ (b = a) :=
  ⟨Id.inv, (⟨Id.inv, Id.invInv⟩, ⟨Id.inv, Id.invInv⟩)⟩

  hott definition biinvTrans {A : Type u} {B : Type v} {C : Type w}
    {f : A → B} {g : B → C} (e₁ : biinv f) (e₂ : biinv g) : biinv (g ∘ f) :=
  (⟨e₁.1.1 ∘ e₂.1.1, λ x, ap e₁.1.1 (e₂.1.2 (f x)) ⬝ e₁.1.2 x⟩,
   ⟨e₁.2.1 ∘ e₂.2.1, λ x, ap g (e₁.2.2 (e₂.2.1 x)) ⬝ e₂.2.2 x⟩)

  hott definition trans {A : Type u} {B : Type v} {C : Type w}
    (f : A ≃ B) (g : B ≃ C) : A ≃ C :=
  ⟨g.1 ∘ f.1, biinvTrans f.2 g.2⟩

  hott instance : @Transitive (Type u) (· ≃ ·) := ⟨@trans⟩

  hott definition idtoiff {A B : Type u} (p : A = B) : A ↔ B :=
  begin induction p; reflexivity end

  hott definition transport {A : Type u} (B : A → Type v) {a b : A} (p : a = b) : B a → B b :=
  begin induction p; apply idfun end

  section
    variable {A : Type u} {B : A → Type v} {a b : A} (p : a = b)
    hott abbrev subst : B a → B b := transport B p
  end

  hott definition transportconst {A B : Type u} : A = B → A → B :=
  transport idfun

  hott definition happlyEqv {A : Type u} {B : Type v} {f g : A ≃ B}
    (p : f = g) : f.forward ~ g.forward :=
  begin induction p; reflexivity end

  hott instance {A : Type u} : @Rewrite A A A Id Id Id := ⟨@Id.trans A⟩

  hott instance {A : Type u} {B : Type v} (ρ : A → B → Type w) : Rewrite ρ Id ρ :=
  ⟨λ a _ _ R p => transport (ρ a) p R⟩

  hott instance {A : Type u} {B : Type v} (ρ : A → B → Type w) : Rewrite Id ρ ρ :=
  ⟨λ _ _ c p R => transport (ρ · c) p⁻¹ R⟩

  hott instance : Rewrite Equiv.{u, v} Equiv.{v, w} Equiv.{u, w} := ⟨@trans⟩

  hott definition depPath {A : Type u} (B : A → Type v) {a b : A} (p : a = b) (u : B a) (v : B b) :=
  transport B p u = v

  notation u " =[" P ", " p "] " v => depPath P p u v
  notation u " =[" p "] " v        => depPath _ p u v

  hott definition depPath.refl {A : Type u} (B : A → Type v) {a : A} (u : B a) : u =[idp a] u :=
  idp u

  hott instance {A : Type u} (B : A → Type v) (a : A) :
    @Reflexive (B a) (depPath B (idp a)) :=
  ⟨depPath.refl B⟩

  hott lemma JTrans {A : Type} {a : A} (B : Π x, a = x → Type v)
    {b c : A} (p : a = b) (q : b = c) (w : B a (idp a)) :
      J₁ B w (p ⬝ q) = J₁ (λ x r, B x (p ⬝ r)) (transport (B b) (Id.rid _)⁻¹ (@Id.rec A a B w b p)) q :=
  begin induction p; induction q; reflexivity end

  hott definition compInvCancelCoh {A : Type u} {a b : A} {B : a = b → Type v} (p : a = b) (w : B p) :
    transport B (Id.cancelInvComp p p) (transport (λ r, B (r ⬝ p)) (Id.compInv p)⁻¹ w) = w :=
  begin induction p; reflexivity end

  hott definition pathoverOfEq {A : Type u} {B : Type v} {a b : A} {a' b' : B}
    (p : a = b) (q : a' = b') : a' =[λ _, B, p] b' :=
  begin induction p; apply q end

  hott theorem transportForwardAndBack {A : Type u} {B : A → Type v}
    {x y : A} (p : x = y) (u : B x) : transport B p⁻¹ (transport B p u) = u :=
  begin induction p; reflexivity end

  hott theorem transportBackAndForward {A : Type u} {B : A → Type v}
    {x y : A} (p : x = y) (u : B y) : transport B p (transport B p⁻¹ u) = u :=
  begin induction p; reflexivity end

  hott corollary idtoeqvLinv {A B : Type u} (p : A = B) :
    transportconst p⁻¹ ∘ transportconst p ~ idfun :=
  by intro; apply transportForwardAndBack

  hott corollary idtoeqvRinv {A B : Type u} (p : A = B) :
    transportconst p ∘ transportconst p⁻¹ ~ idfun :=
  by intro; apply transportBackAndForward

  hott definition idtoeqv {A B : Type u} (p : A = B) : A ≃ B :=
  Equiv.intro (transportconst p) (transportconst p⁻¹) (idtoeqvLinv p) (idtoeqvRinv p)

  hott theorem transportcom {A : Type u} {B : A → Type v} {a b c : A} (p : a = b) (q : b = c)
    (x : B a) : transport B (p ⬝ q) x = transport B q (transport B p x) :=
  begin induction p; induction q; reflexivity end

  hott definition depSymm {A : Type u} {B : A → Type v} {a b : A}
    (p : a = b) {u : B a} {v : B b} (q : u =[p] v) : v =[p⁻¹] u :=
  begin induction p; exact q⁻¹ end

  hott definition depTrans {A : Type u} {B : A → Type v}
    {a b c : A} {p : a = b} {q : b = c} {u : B a} {v : B b} {w : B c}
    (r : u =[p] v) (s : v =[q] w) : u =[p ⬝ q] w :=
  transportcom p q u ⬝ ap (transport B q) r ⬝ s

  infix:60 " ⬝′ " => depTrans

  hott definition depPathTransSymm {A : Type u} {B : A → Type v} {a b c : A} {p : a = b} {q : c = b}
    {x : B a} {y : B c} (η : x =[p ⬝ q⁻¹] y) : x =[p] transport B q y :=
  begin induction p; induction q; exact η end

  hott definition depPathTransSymmCoh {A : Type u} {B : A → Type v} {a b c : A} {p : a = b} {q : c = b}
    {x : B a} {y : B c} : Π (η : x =[p ⬝ q⁻¹] y), depPathTransSymm η ⬝′ depSymm q (idp _) = η :=
  begin induction p; induction q; intro (η : x = y); induction η; apply idp end

  hott definition apd {A : Type u} {B : A → Type v} {a b : A}
    (f : Π x, B x) (p : a = b) : transport B p (f a) = f b :=
  begin induction p; reflexivity end

  hott lemma apdInv {A : Type u} {B : A → Type v} {a b : A}
    (f : Π x, B x) (p : a = b) : apd f p⁻¹ = depSymm p (apd f p) :=
  begin induction p; reflexivity end

  hott theorem apdFunctoriality {A : Type u} {B : A → Type v} {a b c : A}
    (f : Π x, B x) (p : a = b) (q : b = c) :
    @apd A B a c f (p ⬝ q) = apd f p ⬝′ apd f q :=
  begin induction p; induction q; reflexivity end

  hott definition depPathMap {A : Type u} {B : A → Type v} {δ : A → Type w} {a b : A}
    {p : a = b} {u : B a} {v : B b} (g : Π x, B x → δ x) (q : u =[p] v) : g a u =[p] g b v :=
  begin induction p; induction q using Id.casesOn; reflexivity end

  hott definition depPathMap' {A : Type u} {B : Type v} {C : A → Type w} {D : B → Type k}
    {a b : A} {p : a = b} {u : C a} {v : C b} (f : A → B)
    (g : Π x, C x → D (f x)) (q : u =[p] v) : g a u =[ap f p] g b v :=
  begin induction p; induction q using Id.casesOn; apply idp end

  hott definition transportSquare {A : Type u} (B : A → Type v) {a b : A}
    {p q : a = b} (r : p = q) (u : B a) : transport B p u = transport B q u :=
  begin induction r; reflexivity end

  notation "transport²" => transportSquare

  hott abbrev substSquare {A : Type u} {B : A → Type v} {a b : A} {p q : a = b}
    (r : p = q) (u : B a) : transport B p u = transport B q u :=
  transport² B r u

  notation "subst²" => substSquare

  hott theorem transportComp {A : Type u} {B : Type v}
    (C : B → Type w) {x y : A} (f : A → B) (p : x = y) (u : C (f x)) :
    transport (C ∘ f) p u = transport C (ap f p) u :=
  begin induction p; reflexivity end

  hott theorem transportToTransportconst {A : Type u} (B : A → Type v) {a b : A}
    (p : a = b) (u : B a) : transport B p u = transportconst (ap B p) u :=
  begin induction p; reflexivity end

  hott theorem transportconstOverComposition {A B C : Type u} (p : A = B) (q : B = C) (x : A) :
    transportconst (p ⬝ q) x = transportconst q (transportconst p x) :=
  by apply transportcom

  hott theorem transportComposition {A : Type u} {a x₁ x₂ : A}
    (p : x₁ = x₂) (q : a = x₁) : transport (a = ·) p q = q ⬝ p :=
  begin induction p; symmetry; apply Id.rid end

  hott theorem transportCompositionRev {A : Type u} {a x₁ x₂ : A}
    (p : x₁ = x₂) (q : x₁ = a) : transport (· = a) p q = p⁻¹ ⬝ q :=
  begin induction p; reflexivity end

  hott theorem transportCharacterization {A : Type u} {B : A → Type v} {C : A → Type w} {a b : A}
    (φ : B a → C a) (p : a = b) : transport (λ x, B x → C x) p φ = transport C p ∘ φ ∘ transport B p⁻¹ :=
  begin induction p; reflexivity end

  hott theorem transportOverFamily {A : Type u} {x y : A} {B C : A → Type v}
    (f : Π x, B x → C x) (p : x = y) (u : B x) : transport C p (f x u) = f y (transport B p u) :=
  begin induction p; reflexivity end

  hott definition biapd {A : Type u} {B : A → Type v} {C : A → Type w} {a b : A} {u : B a} {v : B b}
    (f : Π x, B x → C x) (p : a = b) (q : u =[p] v) : f a u =[p] f b v :=
  begin induction p; exact ap (f a) q end

  hott definition apd₂ {A : Type u} {B : A → Type v} {a b : A} {p q : a = b}
    (f : Π x, B x) (r : p = q) : apd f p =[λ s, transport B s (f a) = f b, r] apd f q :=
  begin induction r; reflexivity end

  hott lemma rewriteComp {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} (h : r = p ⬝ q) : p⁻¹ ⬝ r = q :=
  begin induction p; apply h end

  hott lemma invRewriteComp {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} (h : p⁻¹ ⬝ r = q) : r = p ⬝ q :=
  begin induction p; apply h end

  hott lemma compRewrite {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} (h : p = r ⬝ q⁻¹) : p ⬝ q = r :=
  begin induction q; exact Id.rid p ⬝ h ⬝ Id.rid r end

  hott lemma invCompRewrite {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} (h : p ⬝ q = r) : p = r ⬝ q⁻¹ :=
  begin induction q; exact (Id.rid p)⁻¹ ⬝ h ⬝ (Id.rid r)⁻¹ end

  hott lemma cancelHigherConjLeft {A : Type u} {a b : A} {p : a = b} (ν κ : p = p) : κ⁻¹ ⬝ ν ⬝ κ = ν :=
  begin transitivity; symmetry; apply Id.assoc; apply rewriteComp; apply Whiskering.comm end

  hott lemma cancelHigherConjRight {A : Type u} {a b : A} {p : a = b} (ν κ : p = p) : κ ⬝ ν ⬝ κ⁻¹ = ν :=
  begin symmetry; apply invCompRewrite; apply Whiskering.comm end

  hott corollary cancelDoubleConjLeftLeft {A : Type u} {a b : A} {p q : a = b}
    (ν : p = p) (κ : p = q) (ε : q = p) : ε⁻¹ ⬝ (κ⁻¹ ⬝ ν ⬝ κ) ⬝ ε = ν :=
  begin induction ε; transitivity; apply Id.rid; apply cancelHigherConjLeft end

  hott corollary cancelDoubleConjRightRight {A : Type u} {a b : A} {p q : a = b}
    (ν : q = q) (κ : p = q) (ε : q = p) : ε ⬝ (κ ⬝ ν ⬝ κ⁻¹) ⬝ ε⁻¹ = ν :=
  begin induction ε; transitivity; apply Id.rid; apply cancelHigherConjRight end

  hott corollary cancelDoubleConjRightLeft {A : Type u} {a b : A} {p q : a = b}
    (ν : q = q) (κ : q = p) (ε : q = p) : ε ⬝ (κ⁻¹ ⬝ ν ⬝ κ) ⬝ ε⁻¹ = ν :=
  begin induction ε; transitivity; apply Id.rid; apply cancelHigherConjLeft end

  hott corollary cancelDoubleConjLeftRight {A : Type u} {a b : A} {p q : a = b}
    (ν : q = q) (κ : p = q) (ε : p = q) : ε⁻¹ ⬝ (κ ⬝ ν ⬝ κ⁻¹) ⬝ ε = ν :=
  begin induction ε; transitivity; apply Id.rid; apply cancelHigherConjRight end

  hott definition idConjIfComm {A : Type u} {a b : A} (p : a = b) (q : a = a) (r : b = b) :
    p ⬝ r = q ⬝ p → q⁻¹ ⬝ p ⬝ r = p :=
  begin intro ε; transitivity; symmetry; apply Id.assoc; apply rewriteComp; exact ε end

  hott definition idConjRevIfComm {A : Type u} {a b : A} (p : a = b) (q : a = a) (r : b = b) :
    p ⬝ r = q ⬝ p → q ⬝ p ⬝ r⁻¹ = p :=
  begin intro ε; symmetry; apply invCompRewrite; exact ε end

  hott lemma mapWithHomotopy {A : Type u} {B : Type v} (f g : A → B) (H : f ~ g) {a b : A} (p : a = b) :
    ap f p = H a ⬝ ap g p ⬝ (H b)⁻¹ :=
  begin apply invCompRewrite; symmetry; apply homotopySquare end

  hott definition pathoverFromTrans {A : Type u} {a b c : A}
    (p : b = c) (q : a = b) (r : a = c) (η : q ⬝ p = r) : q =[p] r :=
  begin induction η; apply transportComposition end

  hott lemma transportInvCompComp {A : Type u} {a b : A} (p : a = b) (q : a = a) :
    transport (λ x, x = x) p q = p⁻¹ ⬝ q ⬝ p :=
  begin induction p; symmetry; apply Id.rid end

  hott theorem mapFunctoriality {A : Type u} {B : Type v}
    {a b c : A} (f : A → B) {p : a = b} {q : b = c} :
    ap f (p ⬝ q) = ap f p ⬝ ap f q :=
  begin induction p; reflexivity end

  hott corollary mapFunctoriality₃ {A : Type u} {B : Type v}
    {a b c d : A} (f : A → B) {p : a = b} {q : b = c} {r : c = d} :
    ap f (p ⬝ q ⬝ r) = ap f p ⬝ ap f q ⬝ ap f r :=
  begin induction p; induction q; reflexivity end

  hott corollary mapFunctoriality₄ {A : Type u} {B : Type v}
    {a b c d e : A} (f : A → B) {p : a = b} {q : b = c} {r : c = d} {s : d = e} :
    ap f (p ⬝ q ⬝ r ⬝ s) = ap f p ⬝ ap f q ⬝ ap f r ⬝ ap f s :=
  begin induction p; induction q; induction r; reflexivity end

  hott corollary mapFunctoriality₅ {A : Type u} {B : Type v}
    {a b c d e f : A} (g : A → B) {p : a = b} {q : b = c} {r : c = d} {s : d = e} {t : e = f} :
    ap g (p ⬝ q ⬝ r ⬝ s ⬝ t) = ap g p ⬝ ap g q ⬝ ap g r ⬝ ap g s ⬝ ap g t :=
  begin induction p; induction q; induction r; induction s; reflexivity end

  hott lemma transportOverContrMap {A : Type u} {B : Type v} {a b : A} {c : B}
    (f : A → B) (p : a = b) (q : f a = c) :
    transport (λ x, f x = c) p q = ap f p⁻¹ ⬝ q :=
  begin induction p; reflexivity end

  hott lemma transportOverInvContrMap {A : Type u} {B : Type v} {a b : A} {c : B}
    (f : A → B) (p : a = b) (q : c = f a) :
    transport (λ x, c = f x) p q = q ⬝ ap f p :=
  begin induction p; symmetry; apply Id.rid end

  hott lemma transportOverInvolution {A : Type u} {a b : A} (f : A → A) (p : a = b) (q : f a = a) :
    transport (λ x, f x = x) p q = ap f p⁻¹ ⬝ q ⬝ p :=
  begin induction p; symmetry; apply Id.rid end

  hott lemma transportOverHmtpy {A : Type u} {B : Type v} {a b : A} (f g : A → B) (p : a = b) (q : f a = g a) :
    transport (λ x, f x = g x) p q = ap f p⁻¹ ⬝ q ⬝ ap g p :=
  begin induction p; symmetry; apply Id.rid end

  hott lemma idmap {A : Type u} {a b : A} (p : a = b) : ap idfun p = p :=
  begin induction p; reflexivity end

  hott lemma constmap {A : Type u} {B : Type v} {a b : A} {c : B}
    (p : a = b) : ap (λ _, c) p = idp c :=
  begin induction p; reflexivity end

  hott theorem transportOverDhmtpy {A : Type u} {B : A → Type v} {a b : A}
    (f g : Π x, B x) (p : a = b) (q : f a = g a) :
    transport (λ x, f x = g x) p q = (apd f p)⁻¹ ⬝ ap (transport B p) q ⬝ apd g p :=
  begin induction p; symmetry; transitivity; apply Id.rid; apply idmap end

  hott theorem mapOverComp {A : Type u} {B : Type v} {C : Type w} {a b : A}
    (f : A → B) (g : B → C) (p : a = b) :
    @ap A C a b (g ∘ f) p = ap g (ap f p) :=
  begin induction p; reflexivity end

  section
    variable {A : Type u} {B : Type v} {C : B → Type w} (f : A → B) {a b : A} {u : C (f a)} {v : C (f b)} (p : a = b)

    hott definition pathOverAp : (u =[C, ap f p] v) → (u =[C ∘ f, p] v) :=
    begin induction p; exact idfun end

    hott definition pathUnderAp : (u =[C ∘ f, p] v) → (u =[C, ap f p] v) :=
    begin induction p; exact idfun end

    hott lemma pathOverApCoh : pathOverAp f p ∘ @pathUnderAp A B C f a b u v p ~ idfun :=
    begin intro; induction p; reflexivity end

    hott lemma pathUnderApCoh : pathUnderAp f p ∘ @pathOverAp A B C f a b u v p ~ idfun :=
    begin intro; induction p; reflexivity end
  end

  hott theorem apdOverComp {A : Type u} {B : Type v} {C : B → Type w} {a b : A} (f : Π x, C x) (g : A → B)
    (p : a = b) : apd (λ x, f (g x)) p = pathOverAp g p (apd f (ap g p)) :=
  begin induction p; reflexivity end

  hott theorem apdOverConstantFamily {A : Type u} {B : Type v} {a b : A}
    (f : A → B) (p : a = b) : apd f p = pathoverOfEq p (ap f p) :=
  begin induction p; reflexivity end

  hott definition reflPathover {A : Type u} {B : Type v} {a : A} {x y : B} (p : x =[λ _, B, idp a] y) : x = y := p

  hott lemma pathoverInv {A : Type u} {B : Type v} (a : A) {x y : B} (p : x = y) :
    reflPathover (pathoverOfEq (idp a) p) = p :=
  begin induction p; reflexivity end

  hott definition pathoverOfEqInj {A : Type u} {B : Type v} {a b : A} {a' b' : B}
    (r : a = b) (p q : a' = b') (η : pathoverOfEq r p = pathoverOfEq r q) : p = q :=
  begin induction r; apply η end

  hott definition transportImpl {A : Type u} (B : A → Type v)
    (C : A → Type w) {a b : A} (p : a = b) (φ : B a → C a) :
    transport (λ x, B x → C x) p φ = λ x, transport C p (φ (transport B p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott theorem transportOverConstFamily {A : Type u} {B : Type v}
    {a b : A} (p : a = b) (b : B) : transport (λ _, B) p b = b :=
  begin induction p; reflexivity end

  hott theorem transportOverPi {A : Type u} {B : Type v}
    (B : A → B → Type w) {a b : A} (p : a = b) (u : Π y, B a y) :
    transport (λ x, Π y, B x y) p u = (λ y, @transport A (λ x, B x y) a b p (u y)) :=
  begin induction p; reflexivity end

  hott theorem transportOverSig {A : Type u} {B : Type v}
    (C : A → B → Type w) {a b : A} (p : a = b) (u : Σ y, C a y) :
    transport (λ x, Σ y, C x y) p u = ⟨u.1, transport (C · u.1) p u.2⟩ :=
  begin induction p; reflexivity end

  hott theorem transportOverProduct {A : Type u} (F : A → Type v) (G : A → Type w) {a b : A}
    (p : a = b) {w : F a × G a} : transport (λ x, F x × G x) p w = (transport F p w.1, transport G p w.2) :=
  begin induction p; reflexivity end

  hott lemma transportOverFunction {A : Type u} {B : Type v}
    {a : A} {b : B} (f g : A → B) (p : f = g) (q : f a = b) :
    transport (λ (f' : A → B), f' a = b) p q =
    @ap (A → B) B g f (λ (f' : A → B), f' a) p⁻¹ ⬝ q :=
  begin induction p; reflexivity end

  hott lemma transportOverOperation {A B : Type u} (φ : A → A → A) (p : A = B) :
    transport (λ A, A → A → A) p φ = λ x y, transport idfun p (φ (transport idfun p⁻¹ x) (transport idfun p⁻¹ y)) :=
  begin induction p; reflexivity end

  hott lemma transportOverFunctor {A B : Type u} (M : Type u → Type v) (N : Type u → Type w)
    (φ : M A → N A) (p : A = B) : transport (λ A, M A → N A) p φ = λ x, transport N p (φ (transport M p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott lemma transportOverMorphism {A B : Type u} (φ : A → A) (p : A = B) :
    transport (λ A, A → A) p φ = λ x, transport idfun p (φ (transport idfun p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott lemma transportOverOperationPointwise {A B : Type u} (φ : A → A → A) (p : A = B) {x y : B} :
      transport (λ A, A → A → A) p φ x y
    = transport idfun p (φ (transport idfun p⁻¹ x) (transport idfun p⁻¹ y)) :=
  begin induction p; reflexivity end

  hott lemma transportOverMorphismPointwise {A B : Type u} (φ : A → A) (p : A = B) {x : B} :
    transport (λ A, A → A) p φ x = transport idfun p (φ (transport idfun p⁻¹ x)) :=
  begin induction p; reflexivity end

  hott definition bimap {A : Type u} {B : Type v} {C : Type w} {a b : A} {a' b' : B}
    (f : A → B → C) (p : a = b) (q : a' = b') : f a a' = f b b' :=
  begin induction p; induction q; reflexivity end

  hott lemma bimapReflLeft {A : Type u} {B : Type v} {C : Type w}
    {a : A} {a' b' : B} (f : A → B → C) (p : a' = b') :
    bimap f (idp a) p = ap (f a) p :=
  begin induction p; reflexivity end

  hott lemma bimapReflRight {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' : B} (f : A → B → C) (p : a = b) :
    bimap f p (idp a') = ap (f · a') p :=
  begin induction p; reflexivity end

  hott theorem bimapCharacterization {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' b' : B} (f : A → B → C) (p : a = b) (q : a' = b') :
    bimap f p q = @ap A C a b (f · a') p ⬝ ap (f b) q :=
  begin induction p; induction q; reflexivity end

  hott theorem bimapCharacterization' {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' b' : B} (f : A → B → C) (p : a = b) (q : a' = b') :
    bimap f p q = ap (f a) q ⬝ @ap A C a b (f · b') p :=
  begin induction p; induction q; reflexivity end

  hott theorem bimapInv {A : Type u} {B : Type v} {C : Type w} {a b : A} {a' b' : B}
    (f : A → B → C) (p : a = b) (q : a' = b') : (bimap f p q)⁻¹ = bimap f p⁻¹ q⁻¹ :=
  begin induction p; induction q; reflexivity end

  hott theorem bimapComp {A : Type u} {B : Type v} {C : Type w}
    {a b : A} {a' b' : B} (f : A → B → C) (p : a = b) (q : a' = b') :
    ap (f · a') p = ap (f a) q ⬝ bimap f p q⁻¹ :=
  begin
    induction p; symmetry; transitivity; apply ap; transitivity;
    apply bimapReflLeft; apply Id.mapInv; apply Id.compInv
  end

  hott lemma transportBimap₁ {A : Type u} {B : Type v} {a₁ a₂ : A} {b₁ b₂ : B}
    (f : A → B → Type w) (p : a₁ = a₂) (q : b₁ = b₂) (u : f a₁ b₁) :
    transportconst (bimap f p q) u = transport (f · b₂) p (transport (f a₁) q u) :=
  begin induction p; induction q; reflexivity end

  hott lemma transportBimap₂ {A : Type u} {B : Type v} {a₁ a₂ : A} {b₁ b₂ : B}
    (f : A → B → Type w) (p : a₁ = a₂) (q : b₁ = b₂) (u : f a₁ b₁) :
    transportconst (bimap f p q) u = transport (f a₂) q (transport (f · b₁) p u) :=
  begin induction p; induction q; reflexivity end

  hott definition transportDiag₁ {A : Type u} (B : A → A → Type v) {a b : A} {p : a = b} (w : B a a) :
    transport (λ x, B x x) p w = transport (B b) p (transport (B · a) p w) :=
  begin induction p; reflexivity end

  hott definition transportDiag₂ {A : Type u} (B : A → A → Type v) {a b : A} {p : a = b} (w : B a a) :
    transport (λ x, B x x) p w = transport (B · b) p (transport (B a) p w) :=
  begin induction p; reflexivity end

  hott definition bimapBicom {A : Type u} {B : Type v} {C : Type w} {D : Type k}
    (f : D → A) (g : D → B) (h : A → B → C) {x y : D} (p : x = y) :
    ap (λ x, h (f x) (g x)) p = bimap h (ap f p) (ap g p) :=
  begin induction p; reflexivity end

  hott theorem mapOverAS {A : Type u} {a b : A} (f : A → A → A) (g : A → A) (p : a = b) :
    ap (AS f g) p = @bimap A A A a b (g a) (g b) f p (ap g p) :=
  begin induction p; reflexivity end

  hott lemma liftedHapply {A : Type u} (B : A → Type v) (C : A → Type w)
    {a b : A} (p : a = b) (f : B a → C a) (g : B b → C b)
    (q : transport (λ x, B x → C x) p f = g) :
    Π x, transport C p (f x) = g (transport B p x) :=
  begin induction p; induction q; intro x; reflexivity end

  hott statement identityEqv {A : Type u} : A ≃ Identity A :=
  begin
    existsi Identity.elem; apply Prod.mk <;> existsi Identity.elim <;> intro x;
    { reflexivity }; { induction x; reflexivity }
  end

  hott definition eqvEqEqv {A B C : Type u} (p : A ≃ B) (q : B = C) : A ≃ C :=
  transport (Equiv A) q p

  hott corollary apComHmtpy {A : Type u} {B : Type v} {f g : A → B}
    (H : f ~ g) {a b : A} (p : a = b) : (f a = f b) = (g a = g b) :=
  bimap Id (H a) (H b)

  hott lemma apdComHmtpy {A : Type u} {B : A → Type v} {f g : Π x, B x} (H : f ~ g)
    {a b : A} (p : a = b) : (f a =[B, p] f b) = (g a =[B, p] g b) :=
  bimap Id (ap (transport B p) (H a)) (H b)

  hott definition conjugateOver {A : Type u} {B : A → Type v} {C : A → Type w}
    {φ ψ : Π x, B x → C x} (H : Π x, φ x ~ ψ x) {a b : A} {u : B a} {v : B b}
    {p : a = b} (q : φ a u =[C, p] φ b v) : ψ a u =[C, p] ψ b v :=
  begin induction p; exact (H a u)⁻¹ ⬝ q ⬝ H a v end

  hott lemma biapdWithHomotopy {A : Type u} {B₁ : A → Type v} {B₂ : A → Type w}
    {φ ψ : Π x, B₁ x → B₂ x} (H : Π x, φ x ~ ψ x) {a b : A} {u : B₁ a} {v : B₁ b}
    (p : a = b) (q : u =[B₁, p] v) : biapd φ p q = conjugateOver (λ x y, (H x y)⁻¹) (biapd ψ p q) :=
  begin
    induction p; induction q using J₁; symmetry; transitivity;
    apply ap (· ⬝ _); apply Id.rid; apply Id.invComp
  end

  hott lemma biapdIdfun {A : Type u} {B : A → Type v} {a b : A}
    {u : B a} {v : B b} {p : a = b} (q : u =[B, p] v) : biapd (λ _, idfun) p q = q :=
  begin induction p; apply idmap end

  hott lemma comBiapd {A : Type u} {B₁ : A → Type v} {B₂ : A → Type w} {B₃ : A → Type k}
    (ψ : Π x, B₂ x → B₃ x) (φ : Π x, B₁ x → B₂ x) {a b : A} {u : B₁ a} {v : B₁ b}
    (p : a = b) (q : u =[B₁, p] v) : biapd (λ x, ψ x ∘ φ x) p q = biapd ψ p (biapd φ p q) :=
  begin induction p; apply mapOverComp end

  hott lemma apdDiag {A : Type u} {B : A → Type v} {C : A → Type w} (f : Π x, B x) (φ : Π x, B x → C x)
    {a b : A} (p : a = b) : apd (λ x, φ x (f x)) p = biapd φ p (apd f p) :=
  begin induction p; reflexivity end

  hott definition bimapΩ {A : Type u} {B : Type v} {C : Type w} (f : A → B → C) {a : A} {b : B} :
    Π {n : ℕ}, Ωⁿ(A, a) → Ωⁿ(B, b) → Ωⁿ(C, f a b)
  | Nat.zero   => f
  | Nat.succ _ => bimapΩ (bimap f)

  hott definition conjugateΩ {A : Type u} {a b : A} (p : a = b) {n : ℕ} : Ωⁿ(A, a) → Ωⁿ(A, b) :=
  transport (λ x, Ωⁿ(A, x)) p

  hott lemma baseEquivΩ {A : Type u} {a b : A} (p : a = b) {n : ℕ} : Ωⁿ(A, a) ≃ Ωⁿ(A, b) :=
  transport (λ x, Ωⁿ(A, a) ≃ Ωⁿ(A, x)) p (ideqv (Ωⁿ(A, a)))

  hott instance {A : Type u} {a b : A} {n : ℕ} : HPow (Ωⁿ(A, a)) (a = b) (Ωⁿ(A, b)) :=
  ⟨λ p α, conjugateΩ α p⟩

  hott lemma conjugateRewriteΩ {A : Type u} {a b : A} (p : a = b) {n : ℕ}
    (α : Ωⁿ(A, a)) (β : Ωⁿ(A, b)) : α = β^p⁻¹ → α^p = β :=
  begin induction p; apply idfun end

  hott lemma conjugateRewriteInvΩ {A : Type u} {a b : A} (p : a = b) {n : ℕ}
    (α : Ωⁿ(A, a)) (β : Ωⁿ(A, b)) : α^p = β → α = β^p⁻¹ :=
  begin induction p; apply idfun end

  hott theorem apConjugateΩ {A : Type u} {B : Type v} (f : A → B) {a b : A}
    (p : a = b) (n : ℕ) (α : Ωⁿ(A, a)) : apΩ f (α^p) = (apΩ f α)^(ap f p) :=
  begin induction p; reflexivity end

  hott theorem conjugateTransΩ {A : Type u} {a b c : A} (p : a = b) (q : b = c)
    (n : ℕ) (α : Ωⁿ(A, a)) : α^(p ⬝ q) = (α^p)^q :=
  begin induction p; reflexivity end

  hott lemma conjugateRevRightΩ {A : Type u} {a b : A} (p : a = b)
    (n : ℕ) (α : Ωⁿ(A, a)) : (α^p)^p⁻¹ = α :=
  begin induction p; reflexivity end

  hott lemma conjugateRevLeftΩ {A : Type u} {a b : A} (p : a = b)
    (n : ℕ) (α : Ωⁿ(A, b)) : (α^p⁻¹)^p = α :=
  begin induction p; reflexivity end

  hott definition LoopOver {A : Type u} (B : A → Type v) {a : A} (b : B a) : Π (n : ℕ), Ωⁿ(A, a) → Type v
  | Nat.zero,   x => B x
  | Nat.succ n, α => @LoopOver (a = a) (λ p, b =[p] b) (idp a) (idp b) n α

  macro:max "Ω" n:superscript "(" τ:term ", " ε:term ", " η:term ")" : term => do
    `(@LoopOver _ $τ _ $ε $(← Meta.Notation.parseSuperscript n) $η)

  macro:max "Ω" "[" n:term "]" "(" τ:term ", " ε:term ", " η:term ")" : term => do
    `(@LoopOver _ $τ _ $ε $n $η)

  @[app_unexpander LoopOver]
  def loopOverUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $B $b $n $α) => `(Ω[$n]($B, $b, $α))
  | _                 => throw ()

  hott definition apdΩ {A : Type u} {B : A → Type v} (f : Π x, B x)
    {a : A} : Π {n : ℕ} (α : Ωⁿ(A, a)), Ωⁿ(B, f a, α)
  | Nat.zero   => f
  | Nat.succ _ => apdΩ (apd f)

  hott definition conjugateOverΩ {A : Type u} {B : A → Type v} {a : A} {b₁ b₂ : B a}
    {n : ℕ} {α : Ωⁿ(A, a)} (p : b₁ = b₂) : Ωⁿ(B, b₁, α) → Ωⁿ(B, b₂, α) :=
  transport (λ x, Ωⁿ(B, x, α)) p

  hott definition biapdΩ {A : Type u} {B₁ : A → Type v} {B₂ : A → Type w} (φ : Π x, B₁ x → B₂ x) {a : A} {b : B₁ a} :
    Π (n : ℕ) (α : Ωⁿ(A, a)), Ωⁿ(B₁, b, α) → Ωⁿ(B₂, φ a b, α)
  | Nat.zero,   x => φ x
  | Nat.succ n, α => @biapdΩ (a = a) (λ p, b =[p] b) (λ p, φ a b =[p] φ a b) (biapd φ) (idp a) (idp b) n α

  hott definition overApΩ {A : Type u} {B : Type v} (C : B → Type w) (f : A → B) {a : A} {b : C (f a)} :
    Π (n : ℕ) (α : Ωⁿ(A, a)) (β : Ωⁿ(C, b, apΩ f α)), Ωⁿ(C ∘ f, b, α)
  | Nat.zero,   x, y => y
  | Nat.succ n, α, β => @biapdΩ (a = a) (λ p, b =[C, ap f p] b) (λ p, b =[C ∘ f, p] b)
                          (pathOverAp f) (idp a) (idp b) n α
                            (@overApΩ (a = a) (f a = f a) (λ p, b =[C, p] b) (ap f) (idp a) (idp b) n α β)

  hott definition underApΩ {A : Type u} {B : Type v} (C : B → Type w) (f : A → B) {a : A} {b : C (f a)} :
    Π (n : ℕ) (α : Ωⁿ(A, a)) (β : Ωⁿ(C ∘ f, b, α)), Ωⁿ(C, b, apΩ f α)
  | Nat.zero,   x, y => y
  | Nat.succ n, α, β => @underApΩ (a = a) (f a = f a) (λ p, b =[C, p] b) (ap f) (idp a) (idp b) n α
                          (@biapdΩ (a = a) (λ p, b =[C ∘ f, p] b) (λ p, b =[C, ap f p] b)
                            (pathUnderAp f) (idp a) (idp b) n α β)

  hott definition fillΩ {A : Type u} {B : A → Type v} {a b : A} {u : B a} {n : ℕ}
    {α : Ωⁿ(A, a)} (p : a = b) : Ωⁿ(B, u, α) → Ωⁿ(B, transport B p u, α^p) :=
  begin induction p; fapply idfun end

  hott definition fillHaeΩ {A : Type u} {B : A → Type v} {a b : A} {u : B a} {n : ℕ}
    {α : Ωⁿ(A, a)} (p : a = b) : Ωⁿ(B, transport B p u, α^p) → Ωⁿ(B, u, α) :=
  begin induction p; fapply idfun end

  hott definition fillConjugateΩ {A : Type u} {B : A → Type v} {a b : A} {u : B b} {n : ℕ}
    {α : Ωⁿ(A, a)} (p : a = b) : Ωⁿ(B, u, α^p) → Ωⁿ(B, transport B p⁻¹ u, α) :=
  λ β, fillHaeΩ p (conjugateOverΩ (transportBackAndForward p u)⁻¹ β)

  hott definition fillConjugateRevΩ {A : Type u} {B : A → Type v} {a b : A} {u : B a} {n : ℕ}
    {α : Ωⁿ(A, b)} (p : a = b) : Ωⁿ(B, transport B p u, α) → Ωⁿ(B, u, α^p⁻¹) :=
  begin induction p; fapply idfun end

  hott definition apdConjugateΩ {A : Type u} {B : A → Type v} (f : Π x, B x) {a b : A} (p : a = b) {n : ℕ}
    (α : Ωⁿ(A, a)) : apdΩ f (α^p) = conjugateOverΩ (apd f p) (fillΩ p (apdΩ f α)) :=
  begin induction p; reflexivity end

  hott definition revΩ {A : Type u} {a : A} : Π {n : ℕ}, Ωⁿ⁺¹(A, a) → Ωⁿ⁺¹(A, a)
  | Nat.zero,   p => p⁻¹
  | Nat.succ n, α => @revΩ (a = a) (idp a) n α

  hott definition comΩ {A : Type u} {a : A} : Π {n : ℕ}, Ωⁿ⁺¹(A, a) → Ωⁿ⁺¹(A, a) → Ωⁿ⁺¹(A, a)
  | Nat.zero,   p, q => p ⬝ q
  | Nat.succ n, α, β => @comΩ (a = a) (idp a) n α β

  hott theorem assocΩ {A : Type u} {a : A} : Π {n : ℕ} (α β γ : Ωⁿ⁺¹(A, a)), comΩ α (comΩ β γ) = comΩ (comΩ α β) γ
  | Nat.zero,   p, q, r => Id.assoc p q r
  | Nat.succ n, α, β, γ => @assocΩ (a = a) (idp a) n α β γ

  open GroundZero.Types.Id (idΩ)

  hott theorem ridΩ {A : Type u} {a : A} : Π {n : ℕ} (α : Ωⁿ⁺¹(A, a)), comΩ α (idΩ a (n + 1)) = α
  | Nat.zero,   p => Id.rid p
  | Nat.succ n, α => @ridΩ (a = a) (idp a) n α

  hott theorem lidΩ {A : Type u} {a : A} : Π {n : ℕ} (α : Ωⁿ⁺¹(A, a)), comΩ (idΩ a (n + 1)) α = α
  | Nat.zero,   p => Id.lid p
  | Nat.succ n, α => @lidΩ (a = a) (idp a) n α

  hott theorem revrΩ {A : Type u} {a : A} : Π {n : ℕ} (α : Ωⁿ⁺¹(A, a)), comΩ α (revΩ α) = idΩ a (n + 1)
  | Nat.zero,   p => Id.compInv p
  | Nat.succ n, α => @revrΩ (a = a) (idp a) n α

  hott theorem revlΩ {A : Type u} {a : A} : Π {n : ℕ} (α : Ωⁿ⁺¹(A, a)), comΩ (revΩ α) α = idΩ a (n + 1)
  | Nat.zero,   p => Id.invComp p
  | Nat.succ n, α => @revlΩ (a = a) (idp a) n α

  hott lemma idrevΩ {A : Type u} {a : A} : Π {n : ℕ}, revΩ (idΩ a (n + 1)) = idΩ a (n + 1)
  | Nat.zero   => idp (idp a)
  | Nat.succ n => @idrevΩ (a = a) (idp a) n

  hott theorem involΩ {A : Type u} {a : A} : Π {n : ℕ} (α : Ωⁿ⁺¹(A, a)), revΩ (revΩ α) = α
  | Nat.zero,   p => Id.invInv p
  | Nat.succ n, α => @involΩ (a = a) (idp a) n α

  hott lemma comDistribΩ {A : Type u} {a b : A} (p : a = b) {n : ℕ}
    (α β : Ωⁿ⁺¹(A, a)) : comΩ (α^p) (β^p) = (comΩ α β)^p :=
  begin induction p; reflexivity end

  hott lemma revConjugateΩ {A : Type u} {a b : A} (p : a = b) {n : ℕ}
    (α : Ωⁿ⁺¹(A, a)) : revΩ (α^p) = (revΩ α)^p :=
  begin induction p; reflexivity end

  hott corollary abelianComΩ {A : Type u} {a : A} : Π {n : ℕ} (α β : Ωⁿ⁺²(A, a)), comΩ α β = comΩ β α
  | Nat.zero,   p, q => Whiskering.comm p q
  | Nat.succ n, α, β => @abelianComΩ (a = a) (idp a) n α β

  hott example {A : Type u} {a : A} (n : ℕ) : Ωⁿ⁺¹(A, a) ≃ Ωⁿ(Ω¹(A, a), idΩ a 1) :=
  by apply ideqv

  hott theorem altDefΩ {A : Type u} {a : A} : Π (n : ℕ), Ωⁿ⁺¹(A, a) ≃ Ω¹(Ωⁿ(A, a), idΩ a n)
  | Nat.zero   => ideqv (a = a)
  | Nat.succ n => @altDefΩ (a = a) (idp a) n

  section
    variable {A : Type u} {a : A} (n : ℕ)

    hott abbrev outΩ : Ωⁿ⁺¹(A, a) → Ω¹(Ωⁿ(A, a), idΩ a n) := (altDefΩ n).forward
    hott abbrev inΩ  : Ω¹(Ωⁿ(A, a), idΩ a n) → Ωⁿ⁺¹(A, a) := (altDefΩ n).left
  end

  hott lemma altDefIdΩ {A : Type u} {a : A} : Π (n : ℕ), altDefΩ n (idΩ (idp a) n) = idp (idΩ a n)
  | Nat.zero   => idp (idp a)
  | Nat.succ n => @altDefIdΩ (a = a) (idp a) n

  hott lemma comInvTwice₁ {A : Type u} {a b x y : A} (p : x = a) (q : y = b) (r : a = b) : r = p⁻¹ ⬝ (p ⬝ r ⬝ q⁻¹) ⬝ q :=
  begin induction p; induction r; symmetry; apply Id.invComp end

  hott lemma comInvTwice₂ {A : Type u} {a b x y : A} (p : a = x) (q : b = y) (r : a = b) : r = p ⬝ (p⁻¹ ⬝ r ⬝ q) ⬝ q⁻¹ :=
  begin induction p; induction r; symmetry; apply Id.compInv end

  -- HoTT 2.11.1
  hott theorem apQinvOfQinv {A : Type u} {B : Type v} (φ : A → B) (H : qinv φ) {a b : A} : qinv (@ap A B a b φ) :=
  begin
    fapply Sigma.mk; intro ε; exact (H.2.2 _)⁻¹ ⬝ ap H.1 ε ⬝ H.2.2 _; apply Prod.mk;
    { intro ε; transitivity; apply comInvTwice₁ (H.2.1 (φ a)) (H.2.1 (φ b));
      transitivity; apply ap (_ ⬝ · ⬝ _);
      transitivity; apply ap (_ ⬝ · ⬝ _); symmetry; apply idmap;
      transitivity; symmetry; apply mapWithHomotopy (φ ∘ H.1);
      transitivity; symmetry; apply mapOverComp φ (φ ∘ H.1);
      transitivity; apply mapOverComp (H.1 ∘ φ) φ;
      transitivity; apply ap (ap φ); apply mapWithHomotopy; apply H.2.2;
      transitivity; apply mapFunctoriality₃; apply ap (_ ⬝ · ⬝ _);
      transitivity; apply ap (ap φ); apply idmap; apply mapFunctoriality₃;
      transitivity; apply ap (_ ⬝ · ⬝ _);
      transitivity; apply bimap (λ p q, _ ⬝ (p ⬝ _ ⬝ _) ⬝ q) <;> apply Id.mapInv;
      symmetry; apply comInvTwice₂; symmetry; transitivity; symmetry; apply idmap;
      transitivity; apply mapWithHomotopy; intro; symmetry; apply H.2.1;
      apply bimap (_ ⬝ · ⬝ ·); apply mapOverComp; apply Id.invInv };
    { intro ε; symmetry; transitivity; symmetry; apply idmap;
      transitivity; apply mapWithHomotopy; intro; symmetry; apply H.2.2;
      apply bimap (_ ⬝ · ⬝ ·); apply mapOverComp; apply Id.invInv }
  end

  hott corollary apBiinvOfBiinv {A : Type u} {B : Type v} (φ : A → B) (H : biinv φ) {a b : A} : biinv (@ap A B a b φ) :=
  Qinv.toBiinv _ (apQinvOfQinv φ (Qinv.ofBiinv _ H))

  hott corollary apEquivOnEquiv {A : Type u} {B : Type v} (φ : A ≃ B) {a b : A} : (a = b) ≃ (φ a = φ b) :=
  ⟨ap φ, apBiinvOfBiinv φ.1 φ.2⟩

  hott corollary apRightOnEquiv {A : Type u} {B : Type v} (φ : A ≃ B) {a b : B} : (a = b) ≃ (φ.right a = φ.right b) :=
  apEquivOnEquiv φ.symm

  hott corollary apLeftOnEquiv {A : Type u} {B : Type v} (φ : A ≃ B) {a b : B} : (a = b) ≃ (φ.left a = φ.left b) :=
  Equiv.trans (apEquivOnEquiv φ.symm) (idtoeqv (bimap _ (φ.leftRight _) (φ.leftRight _))⁻¹)

  hott corollary revEquiv {A : Type u} {a b : A} (p q : a = b) : (p = q) ≃ (p⁻¹ = q⁻¹) :=
  apEquivOnEquiv inveqv

  hott theorem rewriteCompEquiv {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} : (r = p ⬝ q) ≃ (p⁻¹ ⬝ r = q) :=
  begin induction p; reflexivity end

  hott theorem compRewriteEquiv {A : Type u} {a b c : A}
    {p : a = b} {q : b = c} {r : a = c} : (p = r ⬝ q⁻¹) ≃ (p ⬝ q = r) :=
  begin
    transitivity; apply rewriteCompEquiv;
    transitivity; apply revEquiv; apply transport (· ≃ _);
    apply bimap; symmetry; transitivity; apply Id.explodeInv;
    apply ap (_ ⬝ ·); apply Id.invInv; symmetry; apply Id.invInv;
    symmetry; transitivity; apply inveqv; apply rewriteCompEquiv
  end

  hott theorem cancelRightEquiv {A : Type u} {a b c : A}
    {p q : a = b} {r : b = c} : (p ⬝ r = q ⬝ r) ≃ (p = q) :=
  begin induction r; apply idtoeqv; apply bimap <;> apply Id.rid end

  hott theorem cancelLeftEquiv {A : Type u} {a b c : A}
    {p : a = b} {q r : b = c} : (p ⬝ q = p ⬝ r) ≃ (q = r) :=
  begin induction p; apply ideqv end

  hott lemma loopApEquiv {A : Type u} {B : Type v} (φ : A ≃ B) {a : A} : Π (n : ℕ), Ωⁿ(A, a) ≃ Ωⁿ(B, φ a)
  | Nat.zero   => φ
  | Nat.succ n => @loopApEquiv (a = a) (φ a = φ a) (apEquivOnEquiv φ) (idp a) n

  hott corollary addEquivΩ₁ {A : Type u} {a : A} (n : ℕ) : Π (m : ℕ), Ωⁿ⁺ᵐ(A, a) ≃ Ωⁿ(Ωᵐ(A, a), idΩ a m)
  | Nat.zero   => ideqv (Ωⁿ(A, a))
  | Nat.succ m => addEquivΩ₁ n m

  hott corollary addEquivΩ₂ {A : Type u} {a : A} (n : ℕ) : Π (m : ℕ), Ωⁿ⁺ᵐ(A, a) ≃ Ωᵐ(Ωⁿ(A, a), idΩ a n)
  | Nat.zero   => ideqv (Ωⁿ(A, a))
  | Nat.succ m => Equiv.trans (addEquivΩ₂ n m) (Equiv.trans (loopApEquiv (altDefΩ n) _) (baseEquivΩ (altDefIdΩ _)))

  hott definition idOverΩ {A : Type u} {B : A → Type v} {a : A} (b : B a) : Π (n : ℕ), Ωⁿ(B, b, idΩ a n)
  | Nat.zero   => b
  | Nat.succ n => @idOverΩ (a = a) (λ p, b =[B, p] b) (idp a) (idp b) n

  hott theorem altDefOverΩ {A : Type u} {B : A → Type v} {a : A} {b : B a} :
    Π (n : ℕ) (α : Ωⁿ⁺¹(A, a)), Ωⁿ⁺¹(B, b, α) ≃ Ω¹(λ β, Ωⁿ(B, b, β), idOverΩ b n, outΩ n α)
  | Nat.zero,   p => ideqv (b =[p] b)
  | Nat.succ n, α => @altDefOverΩ (a = a) (λ p, b =[B, p] b) (idp a) (idp b) n α

  section
    variable {A : Type u} {B : A → Type v} {a : A} {b : B a} (n : ℕ) (α : Ωⁿ⁺¹(A, a))

    hott abbrev outOverΩ : Ωⁿ⁺¹(B, b, α) → Ω¹(λ β, Ωⁿ(B, b, β), idOverΩ b n, outΩ n α) := (altDefOverΩ n α).forward
    hott abbrev inOverΩ  : Ω¹(λ β, Ωⁿ(B, b, β), idOverΩ b n, outΩ n α) → Ωⁿ⁺¹(B, b, α) := (altDefOverΩ n α).left
  end

  hott theorem apIdΩ {A : Type u} {B : Type v} (f : A → B) {a : A} : Π {n : ℕ}, apΩ f (idΩ a n) = idΩ (f a) n
  | Nat.zero   => idp (f a)
  | Nat.succ n => @apIdΩ (a = a) (f a = f a) (ap f) (idp a) n

  hott theorem apRevΩ {A : Type u} {B : Type v} (f : A → B) {a : A} :
    Π {n : ℕ} (α : Ωⁿ⁺¹(A, a)), apΩ f (revΩ α) = revΩ (apΩ f α)
  | Nat.zero,   p => Id.mapInv f p
  | Nat.succ n, α => @apRevΩ (a = a) (f a = f a) (ap f) (idp a) n α

  hott theorem apFunctorialityΩ {A : Type u} {B : Type v} (f : A → B) {a : A} :
    Π {n : ℕ} (α β : Ωⁿ⁺¹(A, a)), apΩ f (comΩ α β) = comΩ (apΩ f α) (apΩ f β)
  | Nat.zero,   _, _ => mapFunctoriality f
  | Nat.succ n, α, β => @apFunctorialityΩ (a = a) (f a = f a) (ap f) (idp a) n α β

  hott corollary apFunctorialityΩ₃ {A : Type u} {B : Type v} (f : A → B) {a : A} {n : ℕ}
    (α β γ : Ωⁿ⁺¹(A, a)) : apΩ f (comΩ (comΩ α β) γ) = comΩ (comΩ (apΩ f α) (apΩ f β)) (apΩ f γ) :=
  begin transitivity; apply apFunctorialityΩ; apply ap (comΩ · _); apply apFunctorialityΩ end

  section
    variable {A : Type u} {a b : A} (p : a = b) {n : ℕ}

    hott lemma conjugateIdΩ : idΩ a n ^ p = idΩ b n :=
    begin induction p; reflexivity end

    hott lemma conjugateRevΩ (α : Ωⁿ⁺¹(A, a)) : revΩ α ^ p = revΩ (α ^ p) :=
    begin induction p; reflexivity end

    hott lemma conjugateComΩ (α β : Ωⁿ⁺¹(A, a)) : comΩ α β ^ p = comΩ (α ^ p) (β ^ p) :=
    begin induction p; reflexivity end
  end

  hott lemma transportOverHmtpyΩ {A : Type u} {B : Type v} (f : A → B) {a b : A} {n : ℕ}
    (p : a = b) (α : Ωⁿ(B, f a)) : transport (λ x, Ωⁿ(B, f x)) p α = conjugateΩ (ap f p) α :=
  by apply transportComp (λ y, Ωⁿ(B, y)) f

  hott theorem bimapCharacterizationΩ₁ {A : Type u} {B : Type v} {C : Type w} (f : A → B → C) {a : A} {b : B} :
    Π {n : ℕ} (α : Ωⁿ⁺¹(A, a)) (β : Ωⁿ⁺¹(B, b)), bimapΩ f α β = comΩ (apΩ (f · b) α) (apΩ (f a) β)
  | Nat.zero,   _, _ => bimapCharacterization f _ _
  | Nat.succ n, α, β => @bimapCharacterizationΩ₁ (a = a) (b = b) (f a b = f a b) (bimap f) (idp a) (idp b) n α β

  hott theorem bimapCharacterizationΩ₂ {A : Type u} {B : Type v} {C : Type w} (f : A → B → C) {a : A} {b : B} :
    Π {n : ℕ} (α : Ωⁿ⁺¹(A, a)) (β : Ωⁿ⁺¹(B, b)), bimapΩ f α β = comΩ (apΩ (f a) β) (apΩ (f · b) α)
  | Nat.zero,   _, _ => bimapCharacterization' f _ _
  | Nat.succ n, α, β => @bimapCharacterizationΩ₂ (a = a) (b = b) (f a b = f a b) (bimap f) (idp a) (idp b) n α β

  hott lemma apEqIdp {A : Type u} {B : Type v} (f : A → B)
    {a : A} (p : a = a) (H : Π x, f x = f a) : ap f p = idp (f a) :=
  mapWithHomotopy _ _ H p ⬝ ap (_ ⬝ · ⬝ _) (constmap _) ⬝ idConjRevIfComm _ _ _ (Id.rid _)⁻¹

  hott lemma apEqIdΩ {A : Type u} {B : Type v} (f : A → B) {a : A} :
    Π {n : ℕ} (α : Ωⁿ(A, a)) (H : Π x, f x = f a), apΩ f α = idΩ (f a) n
  | Nat.zero,   x, H => H x
  | Nat.succ n, α, H => @apEqIdΩ (a = a) (f a = f a) (ap f) (idp a) n α (λ p, apEqIdp f p H)
end Equiv

inductive Resize (A : Type u) : Type (max u v)
| intro : A → Resize A

hott definition Resize.elim {A : Type u} : Resize A → A
| Resize.intro w => w

hott theorem Resize.equiv (A : Type u) : A ≃ Resize.{u, v} A :=
Equiv.intro Resize.intro Resize.elim idp idp

end GroundZero.Types
