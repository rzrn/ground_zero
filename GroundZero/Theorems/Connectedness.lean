import GroundZero.Theorems.Univalence
import GroundZero.HITs.Trunc

open GroundZero.HITs.Interval (happly)
open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types
open GroundZero.HITs

universe u v w

namespace GroundZero
namespace Theorems

hott def conn {A : Type u} {B : Type v} (n : ℕ₋₂) (f : A → B) :=
Π (b : B), contr ∥fib f b∥ₙ

hott def isConnected (n : ℕ₋₂) (A : Type u) :=
contr ∥A∥ₙ

notation "is-" n "-connected" => isConnected n

namespace Connectedness
  hott proposition isProp {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} : prop (conn n f) :=
  begin apply piProp; intro; apply contrIsProp end

  -- HoTT Book Lemma 7.5.14
  hott lemma isQinv {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} (c : conn n f) : @qinv ∥A∥ₙ ∥B∥ₙ (Trunc.ap f) :=
  begin
    fapply Sigma.mk; apply Trunc.rec;
    { intro b; exact Trunc.ap Sigma.fst (c b).1 };
    { apply Trunc.uniq };

    apply Prod.mk;
    { fapply Trunc.ind;
      { intro y; transitivity; apply ap (Trunc.ap _);
        apply Trunc.recβrule; induction (c y).1;
        { case elemπ w =>
          transitivity; apply ap (Trunc.ap f); apply Trunc.recβrule;
          transitivity; apply Trunc.recβrule; apply ap Trunc.elem; exact w.2 };
        { apply hlevel.cumulative; apply Trunc.uniq } };
      { intro; apply hlevel.cumulative; apply Trunc.uniq } };
    { fapply Trunc.ind;
      { intro x; transitivity; apply ap (Trunc.rec _ _);
        apply Trunc.recβrule; transitivity; apply Trunc.recβrule;
        transitivity; apply ap; apply (c (f x)).2 (Trunc.elem ⟨x, idp (f x)⟩);
        apply Trunc.recβrule };
      { intro; apply hlevel.cumulative; apply Trunc.uniq } }
  end

  hott corollary induce {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} (c : conn n f) : ∥A∥ₙ ≃ ∥B∥ₙ :=
  ⟨Trunc.ap f, Qinv.toBiinv _ (isQinv c)⟩

  hott def com {A : Type u} {B : Type v} {n : ℕ₋₂} (f : A → B)
    (P : B → n-Type) : (Π b, (P b).1) → (Π a, (P (f a)).1) :=
  λ s a, s (f a)

  hott lemma connImplQinv {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B}
    (c : conn n f) (P : B → n-Type) : qinv (com f P) :=
  begin
    fapply Sigma.mk; intros s b; apply Trunc.rec _ _ (c b).1; intro w;
    apply transport (λ b, (P b).1) w.2; apply s; exact (P b).2; apply Prod.mk;
    { intro s; apply Theorems.funext; intro a; transitivity;
      apply ap (Trunc.rec _ _); apply (c (f a)).2; apply Trunc.elem;
      exact ⟨a, idp (f a)⟩; apply Trunc.recβrule };
    { intro s; apply Theorems.funext; intro b; induction (c b).1;
      { case elemπ w =>
        transitivity; apply ap (Trunc.rec _ _); apply (c b).2 (Trunc.elem w);
        transitivity; apply Trunc.recβrule; apply apd s w.2 };
      { apply hlevel.cumulative; apply (P b).2 } }
  end

  hott lemma rinvImplConn {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B}
    (s : Π (P : B → n-Type), rinv (com f P)) : conn n f :=
  begin
    let P : B → n-Type := λ b, ⟨∥fib f b∥ₙ, Trunc.uniq n⟩; intro b; fapply Sigma.mk;
    apply (s P).1 (λ a, Trunc.elem ⟨a, idp (f a)⟩); fapply Trunc.ind;
    { intro ⟨a, w⟩; induction w; apply happly ((s P).2 (λ a, Trunc.elem ⟨a, idp (f a)⟩)) a };
    { intro; apply hlevel.cumulative; apply Trunc.uniq }
  end

  hott lemma rinvComProp {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} :
    prop (Π (P : B → n-Type), rinv (com f P)) :=
  begin
    apply lemProp; intro s; apply piProp; intro P; apply contrImplProp;
    apply Equiv.rinvContr; apply connImplQinv; apply rinvImplConn; exact s
  end

  -- HoTT Book Lemma 7.5.7
  hott corollary induct {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} :
    (conn n f) ≃ (Π (P : B → n-Type), rinv (com f P)) :=
  begin
    apply propEquivLemma; apply Connectedness.isProp; apply rinvComProp; intro c P;
    exact (Qinv.toBiinv _ (connImplQinv c P)).2; apply rinvImplConn
  end

  hott lemma apComHapply {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} (P : B → n-Type)
    {φ ψ : Π b, (P b).1} (p : φ = ψ) : ap (com f P) p = funext (λ a, happly p (f a)) :=
  begin induction p; symmetry; apply funextId end

  hott lemma fibCom {A : Type u} {B : Type v} {n : ℕ₋₂} (f : A → B) (P : B → (hlevel.succ n)-Type)
    {s : Π a, (P (f a)).1} (w₁ w₂ : fib (com f P) s) :=
  calc (w₁ = w₂) ≃ Σ (p : w₁.1 = w₂.1), transport (λ r, com f P r = s) p w₁.2 = w₂.2
                 : Sigma.sigmaPath,
                 ≃ Σ (p : w₁.1 = w₂.1), (ap (com f P) p)⁻¹ ⬝ w₁.2 = w₂.2
                 : Sigma.respectsEquiv (λ _, idtoeqv (ap (· = _) (transportOverContrMap _ _ _ ⬝
                                                                  ap (· ⬝ _) (Id.mapInv _ _)))),
                 ≃ Σ (p : w₁.1 = w₂.1), ap (com f P) p ⬝ w₂.2 = w₁.2
                 : Sigma.respectsEquiv (λ _, Equiv.trans rewriteCompEquiv.symm inveqv),
                 ≃ Σ (p : w₁.1 = w₂.1), ap (com f P) p = w₁.2 ⬝ w₂.2⁻¹
                 : Sigma.respectsEquiv (λ _, compRewriteEquiv.symm),
                 ≃ Σ (H : w₁.1 ~ w₂.1), ap (com f P) (funext H) = w₁.2 ⬝ w₂.2⁻¹
                 : Equiv.respectsEquivOverFst full _,
                 ≃ Σ (H : w₁.1 ~ w₂.1), happly (ap (com f P) (funext H)) = happly (w₁.2 ⬝ w₂.2⁻¹)
                 : Sigma.respectsEquiv (λ _, apEquivOnEquiv Theorems.full),
                 ≃ Σ (H : w₁.1 ~ w₂.1), (λ a, H (f a)) = (happly w₁.2).trans (happly w₂.2).symm
                 : Sigma.respectsEquiv
                    (λ H, idtoeqv (bimap _ (ap happly (apComHapply P (funext H)) ⬝ happlyFunext _ _ _ ⬝
                                            funext (λ a, happly (happlyFunext _ _ _) (f a)))
                                           (Interval.happlyCom _ _ ⬝ ap _ (Interval.happlyRev _)))),
                 ≃ fib (com f (λ b, ⟨w₁.1 b = w₂.1 b, (P b).2 _ _⟩))
                       (λ a, happly w₁.2 a ⬝ (happly w₂.2 a)⁻¹)
                 : ideqv _

  -- HoTT Book Lemma 8.6.1
  hott corollary indTrunc {A : Type u} {B : Type v} {n : ℕ₋₂} {f : A → B} (c : conn n f) :
    Π (k : ℕ) (P : B → (n + hlevel.ofNat k)-Type w), is-(hlevel.predPred k)-truncated (com f P)
  | Nat.zero,   P => Equiv.ishaeImplContrFib _ (Equiv.qinvImplsIshae _ (connImplQinv c P))
  | Nat.succ k, P => λ s w₁ w₂, ntypeRespectsEquiv _ (fibCom f P w₁ w₂).symm (indTrunc c k _ _)

  hott lemma connImplTerminalConn {A : Type u} {n : ℕ₋₂} (a : A) (c : is-(hlevel.succ n)-connected A) : @conn 𝟏 A n (λ _, a) :=
  begin
    apply rinvImplConn; intro P;

    let Q : Trunc (hlevel.succ n) A → n-Type :=
    Trunc.rec P (Equiv.ntypeIsSuccNType n);

    let r := λ a b, contrImplProp c (Trunc.elem a) (Trunc.elem b);
    let s := λ a b, (Trunc.recβrule _ _ _)⁻¹ ⬝ ap Q (r a b) ⬝ Trunc.recβrule _ _ _;

    fapply Sigma.mk; intro r b; exact transport Sigma.fst (s a b) (r ★);
    intro φ; apply funext; apply Unit.ind; transitivity;
    apply ap (transport _ · _); transitivity; apply ap (· ⬝ _);
    transitivity; apply ap (_ ⬝ ap Q ·); show _ = idp (Trunc.elem a);
    apply propIsSet; apply contrImplProp; apply c;
    apply Id.rid; apply Id.invComp; reflexivity
  end
end Connectedness

end Theorems
end GroundZero
