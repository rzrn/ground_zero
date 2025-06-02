import GroundZero.HITs.Interval
import GroundZero.HITs.Merely

open GroundZero.Types.Id (ap)
open GroundZero.HITs.Interval
open GroundZero.Proto (idfun)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types

namespace GroundZero
namespace Theorems.Equiv

universe u v w w' w''

hott remark uniqDoesNotAddNewPaths {A : Type u} (a b : ∥A∥)
  (p : a = b) : HITs.Merely.uniq a b = p :=
propIsSet HITs.Merely.uniq _ _ _ _

hott lemma propEquiv {A : Type u} (H : prop A) : A ≃ ∥A∥ :=
propEquivLemma H HITs.Merely.uniq HITs.Merely.elem (HITs.Merely.rec H id)

hott lemma propFromEquiv {A : Type u} : A ≃ ∥A∥ → prop A :=
begin
  intro ⟨f, (⟨g, A⟩, _)⟩ a b; transitivity;
  exact (A a)⁻¹; symmetry; transitivity; exact (A b)⁻¹;
  apply ap g; exact HITs.Merely.uniq (f b) (f a)
end

hott definition hmtpyRewrite {A : Type u} (f : A → A) (H : f ~ id) (x : A) : H (f x) = ap f (H x) :=
begin have p := (Theorems.funext H)⁻¹; induction p; symmetry; apply Equiv.idmap end

hott theorem qinvImplsIshae {A : Type u} {B : Type v} (f : A → B) : qinv f → ishae f :=
begin
  intro ⟨g, ⟨ε, η⟩⟩; let ε' := λ b, (ε (f (g b)))⁻¹ ⬝ (ap f (η (g b)) ⬝ ε b);
  existsi g; existsi η; existsi ε'; intro x; symmetry; transitivity;
  { apply ap (λ p, _ ⬝ (ap f p ⬝ _)); apply hmtpyRewrite (g ∘ f) };
  apply rewriteComp; transitivity; apply ap (· ⬝ _); symmetry; apply mapOverComp (g ∘ f);
  symmetry; apply @homotopySquare A B (f ∘ g ∘ f) f (λ x, ε (f x)) (g (f x)) x (η x)
end

hott corollary respectsEquivOverFst {A : Type u} {B : Type v}
  (φ : A ≃ B) (C : A → Type w) : (Σ x, C x) ≃ (Σ x, C (φ.left x)) :=
begin
  fapply Sigma.replaceIshae; apply qinvImplsIshae; existsi φ.1;
  apply Prod.mk; apply φ.leftForward; apply φ.forwardLeft
end

hott definition fibEq {A : Type u} {B : Type v} (f : A → B) {y : B} {a b : A} (p : f a = y) (q : f b = y) :
  (Σ (γ : a = b), ap f γ ⬝ q = p) → @Id (fib f y) ⟨a, p⟩ ⟨b, q⟩ :=
begin
  intro ⟨γ, r⟩; fapply Sigma.prod; exact γ; transitivity; apply transportOverContrMap;
  transitivity; apply ap (· ⬝ p); apply Id.mapInv; apply rewriteComp; exact r⁻¹
end

hott theorem ishaeImplContrFib {A : Type u} {B : Type v}
  (f : A → B) : ishae f → Π y, contr (fib f y) :=
begin
  intro ⟨g, η, ε, τ⟩ y; existsi ⟨g y, ε y⟩; intro ⟨x, p⟩; apply fibEq;
  existsi (ap g p)⁻¹ ⬝ η x; transitivity;
  apply ap (· ⬝ p); apply mapFunctoriality;
  transitivity; apply ap (_ ⬝ · ⬝ p); apply τ;
  transitivity; symmetry; apply Id.assoc; transitivity;
  { apply ap (· ⬝ _); transitivity; apply Id.mapInv;
    apply ap; symmetry; apply mapOverComp };
  apply rewriteComp; transitivity; apply ap (_ ⬝ ·);
  symmetry; apply idmap; apply homotopySquare
end

hott lemma compQinv₁ {A : Type u} {B : Type v} {C : Type w}
  (f : A → B) (g : B → A) (H : isQinv f g) :
  @qinv (C → A) (C → B) (f ∘ ·) :=
begin
  existsi (g ∘ ·); apply Prod.mk <;> intro <;>
  apply Theorems.funext <;> intro; apply H.1; apply H.2
end

hott lemma compQinv₂ {A : Type u} {B : Type v} {C : Type w}
  (f : A → B) (g : B → A) (H : isQinv f g) :
  @qinv (B → C) (A → C) (· ∘ f) :=
begin
  existsi (· ∘ g) <;> apply Prod.mk <;> intro G <;>
  apply Theorems.funext <;> intro <;>
  apply ap G; apply H.2; apply H.1
end

hott lemma linvContr {A : Type u} {B : Type v} (f : A → B) (H : qinv f) : contr (linv f) :=
begin
  apply contrRespectsEquiv;
  { apply Equiv.symm; apply Sigma.respectsEquiv;
    intro g; symmetry; apply @Theorems.full A (λ _, A) (g ∘ f) };
  apply ishaeImplContrFib; apply qinvImplsIshae;
  fapply compQinv₂; exact H.1; exact H.2
end

hott lemma rinvContr {A : Type u} {B : Type v} (f : A → B) (H : qinv f) : contr (rinv f) :=
begin
  apply contrRespectsEquiv;
  { apply Equiv.symm; apply Sigma.respectsEquiv;
    intro g; symmetry; apply @Theorems.full B (λ _, B) (f ∘ g) };
  apply ishaeImplContrFib; apply qinvImplsIshae;
  fapply compQinv₁; exact H.1; exact H.2
end

hott statement productContr {A : Type u} {B : Type v} (h : contr A) (g : contr B) : contr (A × B) :=
begin existsi (h.1, g.1); intro p; fapply Product.prod; apply h.2; apply g.2 end

hott theorem biinvProp {A : Type u} {B : Type v} (f : A → B) : prop (biinv f) :=
begin
  apply lemContr; intro g; apply productContr;
  { apply linvContr; apply Qinv.ofBiinv; assumption };
  { apply rinvContr; apply Qinv.ofBiinv; assumption }
end

hott corollary equivHmtpyLem {A : Type u} {B : Type v}
  (f g : A ≃ B) (H : f.forward ~ g.forward) : f = g :=
begin fapply Sigma.prod; apply Theorems.funext; exact H; apply biinvProp end

hott corollary equivNType₁ {A : Type u} {B : Type v} {n : ℕ₋₂} :
  is-(n + 1)-type B → is-(n + 1)-type (A ≃ B) :=
begin
  intro H; apply ntypeRespectsSigma; apply piRespectsImpl; exact H;
  intro; apply propIsNType; apply biinvProp
end

hott lemma symmSymmIdfun (A : Type u) (B : Type v) : @Equiv.symm A B ∘ Equiv.symm ~ idfun :=
begin intro f; apply equivHmtpyLem; intro x; reflexivity; end

hott lemma symmQinv (A : Type u) (B : Type v) : qinv (@Equiv.symm A B) :=
begin existsi @Equiv.symm B A; constructor <;> apply symmSymmIdfun end

hott corollary equivInvEquiv (A : Type u) (B : Type v) : (A ≃ B) ≃ (B ≃ A) :=
begin existsi Equiv.symm; apply Qinv.toBiinv; apply symmQinv end

hott corollary equivNType₂ {A : Type u} {B : Type v} {n : ℕ₋₂} :
  is-(n + 1)-type A → is-(n + 1)-type (A ≃ B) :=
begin
  intro H; apply ntypeRespectsEquiv;
  apply equivInvEquiv; apply equivNType₁; exact H
end

hott corollary propEquivProp {A B : Type u} (G : prop B) : prop (A ≃ B) :=
begin intros f g; apply equivHmtpyLem; intro x; apply G end

hott exercise propExercise (π : Type u) : prop π ≃ (π ≃ ∥π∥) :=
begin
  existsi @propEquiv π; apply Prod.mk <;> existsi propFromEquiv;
  { intro x; apply propIsProp };
  { intro f; apply equivHmtpyLem;
    intro x; apply HITs.Merely.uniq }
end

hott lemma lemContrInv {A : Type u} (H : prop A) (x : A) : contr A := ⟨x, H x⟩

hott proposition lemContrEquiv {A : Type u} : (prop A) ≃ (A → contr A) :=
begin
  apply propEquivLemma; apply propIsProp; apply functionToContr;
  apply lemContrInv; apply lemContr
end

hott definition contrToType {A : Type u} {B : A → Type v}
  (H : contr A) : (Σ x, B x) → B H.1 :=
λ w, transport B (H.2 w.1)⁻¹ w.2

hott definition typeToContr {A : Type u} {B : A → Type v}
  (H : contr A) : B H.1 → (Σ x, B x) :=
λ u, ⟨H.1, u⟩

-- HoTT 3.20
hott theorem contrFamily {A : Type u} {B : A → Type v} (H : contr A) : (Σ x, B x) ≃ B H.1 :=
begin
  existsi contrToType H; apply Prod.mk <;>
  existsi @typeToContr A B H <;> intro x;
  { fapply Sigma.prod; apply H.2; apply transportBackAndForward };
  { transitivity; apply ap (transport B · x);
    apply propIsSet (contrImplProp H) _ _ _ (idp _);
    reflexivity }
end

hott lemma propset.Id (A B : Prop) (H : A.1 = B.1) : A = B :=
Sigma.prod H (propIsProp _ _)

hott corollary hsetEquiv {A : Type u} {B : Type v} (g : hset B) : hset (A ≃ B) :=
begin
  fapply hsetRespectsSigma;
  { apply piHset; intro x; assumption };
  { intro x; apply propIsSet; apply biinvProp }
end

hott corollary zeroEquiv.hset (A B : 0-Type) : hset (A ≃₀ B) :=
begin apply hsetEquiv; apply zeroEqvSet.forward; exact B.2 end

hott lemma contrQinvFib {A : Type u} {B : Type v} {f : A → B} (e : qinv f) (b : B) : contr (Σ a, b = f a) :=
begin apply contrRespectsEquiv; apply respectsEquivOverFst (Qinv.toEquiv (Qinv.sym e)) (Id b); apply singl.contr end

hott lemma propQinvFib {A : Type u} {B : Type v} {f : A → B} (e : qinv f) (b : B) : prop (Σ a, b = f a) :=
contrImplProp (contrQinvFib e b)

hott definition corrRev {A : Type u} {B : Type v} : Corr A B → Corr B A :=
λ w, ⟨λ a b, w.1 b a, (w.2.2, w.2.1)⟩

hott definition corrOfQinv {A : Type u} {B : Type v} : (Σ f, @qinv A B f) → Corr A B :=
begin
  intro w; existsi (λ a b, b = w.1 a); apply Prod.mk <;> intros;
  apply contrRespectsEquiv; apply Sigma.hmtpyInvEqv; apply singl.contr;
  apply contrQinvFib; exact w.2
end

hott definition qinvOfCorr {A : Type u} {B : Type v} : Corr A B → (Σ f, @qinv A B f) :=
begin
  intro w; fapply Sigma.mk; intro a; apply (w.2.1 a).1.1;
  fapply Sigma.mk; intro b; apply (w.2.2 b).1.1; apply Prod.mk;
  { intro b; apply ap Sigma.fst ((w.2.1 (w.2.2 b).1.1).2 ⟨b, (w.2.2 b).1.2⟩) };
  { intro a; apply ap Sigma.fst ((w.2.2 (w.2.1 a).1.1).2 ⟨a, (w.2.1 a).1.2⟩) }
end

section
  variable {A : Type u} {B : Type v} (e : Σ f, @qinv A B f)

  hott example : (qinvOfCorr (corrOfQinv e)).1   = e.1   := by reflexivity
  hott example : (qinvOfCorr (corrOfQinv e)).2.1 = e.2.1 := by reflexivity
end

hott definition pathOver {A : Type u} (B : A → Type v) {a b : A} (p : a = b) (u : B a) (v : B b) :=
Σ (φ : Π x y, x = y → B x → B y), φ a b p u = v × Π x, φ x x (idp x) ~ idfun

hott theorem pathOverCharacterization {A : Type u} {B : A → Type v} {a b : A}
  (p : a = b) (u : B a) (v : B b) : (u =[p] v) ≃ pathOver B p u v :=
begin
  fapply Sigma.mk; { intro q; existsi @transport A B; apply Prod.mk; exact q; intro; apply idp };
  apply Qinv.toBiinv; fapply Sigma.mk; { intro ω; induction p; apply (ω.2.2 a u)⁻¹ ⬝ ω.2.1 };
  apply Prod.mk;
  { induction p; intro ω; fapply Sigma.prod;
    { apply Theorems.funext; intro x;
      apply Theorems.funext; intro y;
      apply Theorems.funext; intro η;
      induction η; apply Theorems.funext (λ w, (ω.2.2 x w)⁻¹) };
    transitivity; apply transportOverProduct; apply Product.prod;
    transitivity; apply transportOverContrMap;
    { transitivity; apply ap (· ⬝ _);
      transitivity; apply Id.mapInv; apply ap Id.inv;
      transitivity; apply mapToHapply₄;
      transitivity; apply ap (happly · _);
      apply happlyFunextPt₃; apply happlyFunextPt; apply Id.invCompCancel };
    { transitivity; apply transportOverPi; apply Theorems.funext; intro;
      transitivity; apply transportOverPi; apply Theorems.funext; intro;
      transitivity; apply transportOverContrMap;
      transitivity; apply Id.rid;
      transitivity; apply Id.mapInv;
      transitivity; apply ap Id.inv;
      transitivity; apply mapToHapply₄;
      transitivity; apply ap (happly · _);
      apply happlyFunextPt₃; apply happlyFunextPt; apply Id.invInv } };
  { induction p; reflexivity }
end

hott theorem replaceIshaeUnderPi {A : Type u} {B : Type v} {C : A → Type w}
  (g : B → A) (e : ishae g) : (Π x, C x) ≃ (Π x, C (g x)) :=
begin
  fapply Sigma.mk; intro φ x; exact φ (g x); fapply Qinv.toBiinv;
  fapply Sigma.mk; intro ψ y; exact transport C (e.2.2.1 y) (ψ (e.1 y)); apply Prod.mk;
  { intro ψ; apply Theorems.funext; intro;
    transitivity; apply Equiv.transportSquare; symmetry; apply e.2.2.2;
    transitivity; symmetry; apply Equiv.transportComp; apply apd };
  { intro φ; apply Theorems.funext; intro; apply apd }
end

hott corollary replaceQinvUnderPi {A : Type u} {B : Type v} {C : A → Type w}
  (g : B → A) : qinv g → (Π x, C x) ≃ (Π x, C (g x)) :=
replaceIshaeUnderPi g ∘ qinvImplsIshae g

end Theorems.Equiv
end GroundZero
