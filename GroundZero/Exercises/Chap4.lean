import GroundZero.Theorems.Functions
import GroundZero.Theorems.Equiv
import GroundZero.Types.Product
import GroundZero.Theorems.Nat
import GroundZero.Types.Sigma
import GroundZero.HITs.Circle

import GroundZero.Exercises.Chap2

open GroundZero.Types
open GroundZero.Proto
open GroundZero

universe u v w k u' v' w' k'

-- exercise 4.1

namespace «4.1»
  open GroundZero.Types.Equiv (biinv idtoeqv transport)
  open GroundZero.Structures (prop)
  open GroundZero.Types.Id (ap)

  hott definition Adjoint {A : Type u} {B : Type v} (f : A → B) :=
  Σ (g : B → A) (η : g ∘ f ~ idfun) (ε : f ∘ g ~ idfun), (Π x, ap f (η x) = ε (f x)) × (Π y, ap g (ε y) = η (g y))

  hott lemma adjointIdfun (A : Type u) : Adjoint (@idfun A) ≃ (Π (x : A), idp x = idp x) :=
  begin
    apply Equiv.trans; apply @Sigma.assoc (A → A) (λ g, g ~ idfun) (λ w, Σ (ε : w.1 ~ idfun), (Π x, ap idfun (w.2 x) = ε x) × (Π y, ap w.1 (ε y) = w.2 (w.1 y)));
    apply Equiv.trans; apply Theorems.Equiv.contrFamily;
    apply Structures.contrRespectsEquiv; apply Sigma.respectsEquiv;
    intro; apply Equiv.trans; apply Equiv.inveqv;
    apply Theorems.full; apply singl.contr;
    show (Σ (ε : idfun ~ idfun), (Π x, idp x = ε x) × (Π y, ap idfun (ε y) = idp y)) ≃ _;

    apply Equiv.trans; apply Sigma.respectsEquiv; intro; symmetry; apply Sigma.const;
    apply Equiv.trans; apply @Sigma.assoc (idfun ~ idfun) (λ ε, Π x, idp x = ε x) (λ w, Π y, ap idfun (w.1 y) = idp y);
    apply Equiv.trans; apply Theorems.Equiv.contrFamily;
    apply Structures.contrRespectsEquiv; apply Sigma.respectsEquiv;
    intro; apply Theorems.full; apply singl.contr; reflexivity
  end

  hott theorem adjointIdtoeqv {A B : Type u} (p : A = B) :
    Adjoint (idtoeqv p) ≃ (Π (x : A), idp x = idp x) :=
  begin induction p; apply adjointIdfun end

  -- not a mere proposition if, for example, A = S²
  hott theorem adjointIfInh {A B : Type u} (f : A → B) :
    biinv f → Adjoint f ≃ (Π (x : A), idp x = idp x) :=
  begin
    intro e; apply transport (Adjoint · ≃ _);
    apply ap Sigma.fst (idtoeqvua ⟨f, e⟩);
    apply adjointIdtoeqv
  end
end «4.1»

-- exercise 4.2

namespace «4.2»
  open GroundZero.Types.Equiv (Corr transport)
  open GroundZero.Types.Id (ap)
  open GroundZero.Structures
  open GroundZero.Types (Id)

  variable {A : Type u} {B : Type v}

  hott example : Corr A B ≃ (A ≃ B) :=
  Theorems.Equiv.biinvEquivCorr

  hott definition isequiv (f : A → B) := Σ (ρ : Corr A B), Π x, ρ.1 x (f x)

  hott theorem «4.2.i» (f : A → B) : qinv f → isequiv f :=
  begin
    intro e; existsi Theorems.Equiv.corrOfQinv ⟨f, e⟩;
    intro; show _ = _; reflexivity
  end

  hott theorem «4.2.ii» (f : A → B) : isequiv f → qinv f :=
  begin
    intro w; apply transport qinv _ (Theorems.Equiv.qinvOfCorr w.1).2;
    apply Theorems.funext; intro x; exact ap Sigma.fst ((w.1.2.1 x).2 ⟨f x, w.2 x⟩);
  end

  hott definition corrPath {f : A → B} (e : isequiv f) {a : A} {b : B} :=
  λ r, contrImplProp (e.1.2.1 a) ⟨f a, e.2 a⟩ ⟨b, r⟩

  hott definition F {f : A → B} (e : isequiv f) {a : A} {b : B} : e.1.1 a b → f a = b :=
  λ r, ap Sigma.fst (corrPath e r)

  hott definition G {f : A → B} (e : isequiv f) {a : A} {b : B} : f a = b → e.1.1 a b :=
  λ p, transport (e.1.1 a) p (e.2 a)

  hott lemma isequivRel {f : A → B} (e : isequiv f) {a : A} {b : B} : (e.1.1 a b) ≃ (f a = b) :=
  begin
    existsi F e; apply Qinv.toBiinv; existsi G e; apply Prod.mk;
    { intro p; induction p; transitivity; apply ap (ap _); apply Id.invComp; reflexivity };
    { intro w; show transport _ _ _ = _; transitivity; symmetry;
      apply Equiv.transportComp (e.1.1 a) Sigma.fst (corrPath e w);
      exact Equiv.apd Sigma.snd (corrPath e w) }
  end

  hott theorem «4.2.iii» (f : A → B) : prop (isequiv f) :=
  begin
    intro e₁ e₂; fapply Sigma.prod;
    { fapply Sigma.prod; apply Theorems.funext; intro; apply Theorems.funext; intro;
      apply ua; transitivity; apply isequivRel; symmetry; apply isequivRel;
      apply productProp <;> apply piProp <;> intro <;> apply contrIsProp };
    { transitivity; apply Equiv.transportOverPi; apply Theorems.funext;
      intro a; transitivity; apply Equiv.transportToTransportconst;
      transitivity; apply ap (Equiv.transportconst · _);
      transitivity; apply Equiv.mapOverComp Sigma.fst (λ (φ : A → B → Type _), φ a (f a));
      transitivity; apply ap (ap _); apply Sigma.mapFstOverProd;
      transitivity; apply Theorems.mapToHapply₂; apply Theorems.happlyFunextPt₂;
      transitivity; apply uaβ; show G e₂ (F e₁ (Sigma.snd e₁ a)) = Sigma.snd e₂ a;
      transitivity; symmetry; apply Equiv.transportComp (e₂.1.1 a) Sigma.fst (corrPath _ _);
      transitivity; apply transport²; apply Id.invComp; reflexivity }
  end
end «4.2»

-- exercise 4.3

namespace «4.3»
  open GroundZero.Types.Equiv (transport ideqv idtoeqv)
  open GroundZero.Theorems.Functions
  open GroundZero.Types.Id

  variable {A : Type u} {B : Type v} (f : A → B)

  hott theorem embdOfIshae (e : ishae f) : isEmbedding f :=
  begin
    intro x y; fapply Qinv.toBiinv; fapply Sigma.mk;
    { intro p; exact (e.2.1 x)⁻¹ ⬝ ap e.1 p ⬝ (e.2.1 y) }; apply Prod.mk;
    { intro p; transitivity; apply Equiv.mapFunctoriality;
      transitivity; apply ap (· ⬝ _); apply Equiv.mapFunctoriality;
      transitivity; apply Equiv.bimap (λ p q, p ⬝ _ ⬝ q);
      apply Id.mapInv; symmetry; apply Id.invInv;
      symmetry; transitivity; symmetry; apply Equiv.idmap;
      transitivity; apply @Equiv.mapWithHomotopy B B idfun (f ∘ e.1) (λ x, (e.2.2.1 x)⁻¹);
      transitivity; apply Equiv.bimap (λ p q, p ⬝ _ ⬝ q);
      apply ap; symmetry; apply e.2.2.2;
      apply ap (·⁻¹⁻¹); symmetry; apply e.2.2.2;
      apply ap (_ ⬝ · ⬝ _); apply Equiv.mapOverComp };
    { intro p; induction p; transitivity; apply ap (· ⬝ _);
      apply Id.rid; apply Id.invComp }
  end

  hott lemma embdOfQinv : qinv f → isEmbedding f :=
  embdOfIshae f ∘ Theorems.Equiv.qinvImplsIshae f

  hott corollary qinvIdEqv (e : qinv f) {a b : A} : (a = b) ≃ (f a = f b) :=
  ⟨ap f, embdOfQinv f e a b⟩

  hott corollary qinvEqvLeft (e : qinv f) {C : Type w} (g h : C → A) : (g ~ h) ≃ (f ∘ g ~ f ∘ h) :=
  begin apply Structures.equivFunext; intro; apply qinvIdEqv f e end

  hott theorem «4.1.1» (e : qinv f) : qinv f ≃ (Π (x : A), x = x) :=
  begin
    apply Equiv.trans; apply Sigma.respectsEquiv;
    intro g; apply Equiv.trans; apply Equiv.prodEquiv;

    apply Equiv.trans; apply qinvEqvLeft e.1 ⟨f, ⟨e.2.2, e.2.1⟩⟩;
    apply Equiv.trans; apply transport (· ∘ g ~ _ ≃ _) (Theorems.funext e.2.2)⁻¹;
    apply ideqv; apply Equiv.trans; symmetry; apply Theorems.full;
    apply Equiv.inveqv; apply ideqv;
    symmetry; apply Sigma.const; apply Equiv.trans;
    apply @Sigma.assoc (B → A) (λ g, e.1 = g) (λ w, w.1 ∘ f ~ idfun);
    apply Equiv.trans; apply Theorems.Equiv.contrFamily; apply singl.contr;

    apply Structures.equivFunext; intro x;
    apply Equiv.trans; apply qinvIdEqv f e;
    apply transport (· = _ ≃ _); symmetry; apply e.2.1;
    apply Equiv.symm; apply qinvIdEqv f e
  end
end «4.3»

-- exercise 4.4

namespace «4.4»
  open GroundZero.Types.Equiv (apd transport biinv ideqv)
  open GroundZero.Theorems.Functions
  open GroundZero.Types.Id

  hott lemma bisigmaComm (A : Type u) (B : Type v) (C : A → B → Type w) : (Σ x y, C x y) ≃ (Σ y x, C x y) :=
  ⟨λ w, ⟨w.2.1, w.1, w.2.2⟩, Qinv.toBiinv _ ⟨λ w, ⟨w.2.1, w.1, w.2.2⟩, (idp, idp)⟩⟩

  hott definition mapProd {A : Type u} {A' : Type u'} {B : A → Type v} {B' : A' → Type v'}
    (f : A → A') (g : Π x, B x → B' (f x)) : (Σ x, B x) → (Σ y, B' y) :=
  λ w, ⟨f w.1, g w.1 w.2⟩

  hott lemma transportEmbd {A : Type u} {B : A → Type v} {a b : A} (p : a = b) : isEmbedding (transport B p) :=
  begin
    induction p; intro x y; apply transport biinv;
    show idfun = _; apply Theorems.funext; intro q;
    induction q; reflexivity; exact (ideqv (x = y)).2
  end

  hott corollary transportEmbdEqv {A : Type u} {B : A → Type v} {a b : A}
    (p : a = b) {x y : B a} : (x = y) ≃ (transport B p x = transport B p y) :=
  ⟨ap (transport B p), transportEmbd p x y⟩

  hott lemma mapProdFiber {A : Type u} {A' : Type u'} {B : A → Type v} {B' : A' → Type v'}
    (f : A → A') (g : Π x, B x → B' (f x)) (w' : Σ y, B' y) :
    fib (mapProd f g) w' ≃ Σ (e : fib f w'.1), fib (g e.1) (transport B' e.2⁻¹ w'.2) :=
  begin
    transitivity; apply Sigma.respectsEquiv.{_, _, max u' v'}; intro; apply Sigma.sigmaPath;
    transitivity; symmetry; apply Sigma.assoc;
    transitivity; apply Sigma.respectsEquiv.{_, _, max v u' v'}; intro x;
    apply bisigmaComm (B x) (f x = w'.1) (λ y p, transport B' p (g x y) = w'.2);
    transitivity; apply @Sigma.assoc A (λ x, f x = w'.1) (λ e, Σ (y : B e.1), transport B' e.2 (g e.1 y) = w'.2);
    apply Sigma.respectsEquiv; intro e; apply Sigma.respectsEquiv; intro;
    transitivity; apply transportEmbdEqv e.2⁻¹; apply transport (· = _ ≃ _ = _);
    symmetry; apply Equiv.transportForwardAndBack; reflexivity
  end

  variable {A : Type u} {B : Type v} {C : Type w} (f : A → B) (g : B → C) (b : B)

  hott definition naturalMap : fib (g ∘ f) (g b) → fib g (g b) :=
  λ w, ⟨f w.1, w.2⟩

  hott theorem «4.4.i» : fib (naturalMap f g b) ⟨b, idp (g b)⟩ ≃ fib f b :=
  begin
    apply Equiv.trans; apply @mapProdFiber A B (λ x, g (f x) = g b) (λ y, g y = g b) f (λ _, idfun) ⟨b, idp (g b)⟩;
    apply transport (@Sigma _ · ≃ _); apply Theorems.funext;
    intro e; symmetry; apply ap (fib idfun);
    transitivity; apply Equiv.transportOverContrMap;
    transitivity; apply Id.rid; apply ap (ap g); apply Id.invInv;
    apply Equiv.trans; apply Sigma.respectsEquiv;
    { intro; apply Equiv.trans; apply Sigma.hmtpyInvEqv;
      apply Structures.contrEquivUnit.{_, 0}; apply singl.contr };
    apply Equiv.trans; apply Sigma.const; apply Structures.unitProdEquiv;
  end

  hott theorem «4.4.ii» (c : C) : fib (g ∘ f) c ≃ Σ (w : fib g c), fib f w.1 :=
  begin
    apply Equiv.symm; apply Equiv.trans;
    apply @Sigma.assoc (fib g c) (λ _, A) (λ w, f w.2 = w.1.1);
    apply Equiv.trans; fapply Theorems.Equiv.respectsEquivOverFst;

    exact (Σ (a : A) (b : B), g b = c);
    { fapply Sigma.mk;
      { intro w; existsi w.2; existsi w.1.1; exact w.1.2 };
      apply Qinv.toBiinv; fapply Sigma.mk;
      { intro w; existsi ⟨w.2.1, w.2.2⟩; exact w.1 };
      apply Prod.mk <;> intro <;> reflexivity };

    apply Equiv.trans; symmetry; apply Sigma.assoc;
    apply Sigma.respectsEquiv; intro a;
    apply Equiv.trans; symmetry; apply Sigma.assoc;
    apply Equiv.trans; apply Sigma.respectsEquiv;
    intro b; apply Sigma.const (g b = c) (f a = b);

    fapply Sigma.mk; intro w; exact ap g w.2.2 ⬝ w.2.1; apply Qinv.toBiinv; fapply Sigma.mk;
    { intro p; existsi f a; existsi p; reflexivity }; apply Prod.mk; intro; reflexivity;
    { intro w; fapply Sigma.prod; exact w.2.2; transitivity;
      apply Equiv.transportOverProduct; apply Equiv.bimap Prod.mk;
      { transitivity; apply Equiv.transportOverContrMap; transitivity;
        apply ap (· ⬝ _); apply Id.mapInv; apply Id.invCompCancel };
      { transitivity; apply Equiv.transportOverInvContrMap; apply Equiv.idmap } }
  end
end «4.4»

-- exercise 4.5

namespace «4.5.i»
  open GroundZero.Types.Equiv (biinv transport)
  open GroundZero.Types.Id (ap)

  variable {A : Type u} {B : Type v} {C : Type w} {D : Type k}

  variable (f : A → B) (g : B → C) (h : C → D)

  hott lemma lem1 : qinv (g ∘ f) → qinv (h ∘ g) → qinv (h ∘ g ∘ f) :=
  λ e₁ e₂, ⟨e₁.1 ∘ g ∘ e₂.1, (λ d, ap h (e₁.2.1 (g (e₂.1 d))) ⬝ e₂.2.1 d,
                              λ a, ap (e₁.1 ∘ g) (e₂.2.2 (f a)) ⬝ e₁.2.2 a)⟩

  hott lemma lem2 : qinv (g ∘ f) → qinv (h ∘ g) → qinv f :=
  λ e₁ e₂, transport qinv (Theorems.funext (λ a, e₂.2.2 (f a))) (Qinv.com (Qinv.sym e₂) (lem1 f g h e₁ e₂))

  hott lemma lem3 : qinv (g ∘ f) → qinv (h ∘ g) → qinv h :=
  λ e₁ e₂, transport qinv (Theorems.funext (λ c, ap h (e₁.2.1 c)))
                          (@Qinv.com _ _ _ (h ∘ g ∘ f) _ (lem1 f g h e₁ e₂) (Qinv.sym e₁))

  hott lemma lem4 : qinv (g ∘ f) → qinv (h ∘ g) → qinv g :=
  λ e₁ e₂, transport qinv (Theorems.funext (λ b, (lem3 f g h e₁ e₂).2.2 (g (f ((lem2 f g h e₁ e₂).1 b))) ⬝ ap g ((lem2 f g h e₁ e₂).2.1 b)))
                          (Qinv.com (Qinv.sym (lem3 f g h e₁ e₂)) (@Qinv.com _ _ _ (h ∘ g ∘ f) _ (lem1 f g h e₁ e₂) (Qinv.sym (lem2 f g h e₁ e₂))))
end «4.5.i»

namespace «4.5.ii»
  open GroundZero.Types.Equiv (transport)
  open GroundZero.Theorems.Functions
  open GroundZero.Types.Id (ap)
  open «4.5.i»

  hott lemma idfunEmbd {A : Type u} {f : A → A} (H : f ~ idfun) : isEmbedding f :=
  transport isEmbedding (Theorems.funext H)⁻¹ (λ a b, Qinv.toBiinv _ ⟨idfun, (Equiv.idmap, Equiv.idmap)⟩)

  hott theorem embdOfQinv {A : Type u} {B : Type v} {f : A → B} (e : qinv f) : isEmbedding f :=
  begin
    intro a b; apply Qinv.toBiinv; apply lem2 (ap f) (ap e.1) (ap f) <;>
    { apply transport qinv; apply Theorems.funext; intro; apply Equiv.mapOverComp;
      apply Qinv.ofBiinv; apply idfunEmbd; (first | exact e.2.1 | exact e.2.2) };
  end
end «4.5.ii»

-- exercise 4.6

namespace «4.6»
  open GroundZero.Types.Equiv (transport ideqv)
  open GroundZero.Types.Id (ap)
  open GroundZero.Structures
  open GroundZero.HITs

  hott definition idtoqinv {A B : Type u} : A = B → Σ (f : A → B), qinv f :=
  λ p, transport (λ X, Σ (f : A → X), qinv f) p ⟨idfun, ⟨idfun, (idp, idp)⟩⟩

  -- 4.6.i

  section
    variable (uaq : Π (A B : Type u), qinv (@idtoqinv A B))

    hott lemma lem1 {A B X : Type u} (p : A = B) : (X → A) ≃ (X → B) :=
    transport (λ Y, (X → A) ≃ (X → Y)) p (ideqv (X → A))

    hott lemma lem2 {A B X : Type u} (e : A ≃ B) : (X → A) ≃ (X → B) :=
    lem1 ((uaq A B).1 ⟨e.1, Qinv.ofBiinv _ e.2⟩)
  end

  -- then proceed exactly as in book

  -- 4.6.ii

  section
    variable (uaq : Π (A B : Type), qinv (@idtoqinv A B))
    open Circle (base loop rot)

    hott definition negBoolQinv : qinv not :=
    ⟨not, (negNeg, negNeg)⟩

    hott definition universeNotASet : ¬(hset Type) :=
    let φ : Σ (f : 𝟐 → 𝟐), qinv f := ⟨not, negBoolQinv⟩;
    let ψ : Σ (f : 𝟐 → 𝟐), qinv f := ⟨idfun, Qinv.ideqv⟩;

    λ ε, let p : 𝟐 = 𝟐 := (uaq 𝟐 𝟐).1 φ;
    let f : idtoqinv p = φ := (uaq 𝟐 𝟐).2.1 φ;
    let g : idtoqinv p = ψ := ap idtoqinv (ε _ _ p (idp 𝟐));
    ffNeqTt (Interval.happly (ap Sigma.fst (f⁻¹ ⬝ g)) true)

    hott definition loopNeqRefl : loop ≠ idp base :=
    begin
      intro H; apply universeNotASet uaq;
      intros A B p q; apply (KIffSet Type).left;
      apply Circle.loopEqReflImplsUip; assumption
    end

    hott lemma rotNeqIdp : rot ≠ idp :=
    λ H, loopNeqRefl uaq (Interval.happly H base)

    hott lemma notTrivLoop : ¬(prop (Π (x : S¹), x = x)) :=
    begin intro H; apply loopNeqRefl uaq; exact Interval.happly (H rot idp) base end

    open «4.3»

    hott theorem «4.6.ii» : Σ (A B : Type) (f : A → B), ¬prop (qinv f) :=
    begin
      existsi S¹; existsi S¹; existsi idfun; intro H; apply notTrivLoop uaq;
      apply propRespectsEquiv; apply «4.1.1»; exact Qinv.ideqv; assumption
    end
  end

  -- 4.6.iii

  section
    variable (uaq : Π (A B : Type u), qinv (@idtoqinv A B))

    hott lemma cohQinvIdtoqinv {A B : Type u} (p : A = B) :
      (λ x, ap (idtoqinv p).2.1 ((idtoqinv p).2.2.1 x)) = (λ x, (idtoqinv p).2.2.2 ((idtoqinv p).2.1 x)) :=
    begin induction p; reflexivity end

    hott lemma cohQinv {A B : Type u} (f : A → B) (e : qinv f) :=
    transport (λ w, (λ x, ap w.2.1 (w.2.2.1 x)) = (λ x, w.2.2.2 (w.2.1 x)))
      ((uaq A B).2.1 ⟨f, e⟩) (cohQinvIdtoqinv _)
  end

  section
    variable (uaq : Π (A B : Type), qinv (@idtoqinv A B))
    open Circle (rot)

    hott theorem «4.6.iii» : 𝟎 :=
    begin apply rotNeqIdp uaq; symmetry; apply @cohQinv uaq S¹ S¹ idfun ⟨idfun, (idp, rot)⟩ end
  end
end «4.6»

-- exercise 4.7

namespace «4.7»
  open GroundZero.Types.Equiv (biinv transport)
  open GroundZero.Theorems.Functions
  open GroundZero.Types.Id

  hott theorem embdEqvDef {A : Type u} {B : Type v} (f : A → B) :
    isEmbedding f ↔ injective f × Π x, biinv (@ap A B x x f) :=
  begin
    apply Prod.mk;
    { intro e; apply Prod.mk;
      { intro x y; exact (e x y).2.1 };
      { intro x; exact e x x } };
    { intro w x y; fapply Qinv.toBiinv; let ε := λ x, Qinv.ofBiinv _ (w.2 x);
      fapply Sigma.mk;
      { intro p; exact transport (λ y, f x = f y → x = y) (w.1 x y p) (ε x).1 p }; apply Prod.mk;
      { intro p; transitivity; apply ap (ap f); transitivity;
        apply HITs.Interval.happly; apply Equiv.transportCharacterization;
        apply Equiv.transportComposition; transitivity;
        apply ap (λ q, ap f ((ε x).1 q ⬝ _));
        apply Equiv.transportOverInvContrMap;
        transitivity; apply Equiv.mapFunctoriality;
        transitivity; apply ap (· ⬝ _); apply (ε x).2.1;
        transitivity; apply ap (_ ⬝ · ⬝ _); apply Id.mapInv;
        apply Id.cancelInvComp };
      { intro p; show transport (λ y, f x = f y → x = y) _ _ _ = _;
        transitivity; apply HITs.Interval.happly; apply Equiv.transportCharacterization;
        transitivity; apply Equiv.transportComposition;
        transitivity; apply ap (· ⬝ _);
        transitivity; apply ap (ε x).1;
        transitivity; apply Equiv.transportOverInvContrMap;
        symmetry; apply Equiv.mapFunctoriality;
        apply (ε x).2.2; apply Id.cancelInvComp } }
  end
end «4.7»

-- exercise 4.8

namespace «4.8»
  open GroundZero.Theorems.Functions
  open GroundZero.Types.Equiv
  open GroundZero.Structures
  open GroundZero.Theorems

  hott lemma injOutOfBoolChar {B : Type u} : (Σ (f : 𝟐 → B), injective f) ≃ (Σ (w : B × B), w.1 ≠ w.2) :=
  begin
    fapply Sigma.mk;
    { intro w; existsi (w.1 false, w.1 true);
      intro p; apply ffNeqTt; apply w.2; exact p };
    fapply Qinv.toBiinv; fapply Sigma.mk;
    { intro w; existsi Bool.elim w.1.1 w.1.2;
      intro b₁ b₂ p; match b₁, b₂ with
      | false, false => { reflexivity }
      | false, true  => { apply explode; apply w.2; exact p }
      | true,  false => { apply explode; apply w.2; exact p⁻¹ }
      | true,  true  => { reflexivity } };
    apply Prod.mk;
    { intro w; apply Sigma.prod; apply notIsProp; reflexivity };
    { intro b; apply Sigma.prod;
      { repeat (first | apply boolIsSet | apply piProp; intro) };
      { apply Theorems.funext; intro b; induction b using Bool.casesOn <;> reflexivity } }
  end

  hott lemma embdOutOfBoolChar {B : Type u} :
    (𝟐 ↪ B) ≃ (Σ (w : B × B), w.1 ≠ w.2 × contr (w.1 = w.1) × contr (w.2 = w.2)) :=
  begin
    fapply Sigma.mk;
    { intro w; existsi (w.1 false, w.1 true); fapply (_, _, _);
      { intro p; apply ffNeqTt; apply (w.2 false true).1.1; exact p };
      { apply contrRespectsEquiv; apply w.eqv;
        existsi idp false; intro; apply boolIsSet };
      { apply contrRespectsEquiv; apply w.eqv;
        existsi idp true; intro; apply boolIsSet } };
    fapply Qinv.toBiinv; fapply Sigma.mk;
    { intro w; existsi Bool.elim w.1.1 w.1.2; intro b₁ b₂; apply Qinv.toBiinv;
      match b₁, b₂ with
      | false, false => { fapply Sigma.mk; intro; reflexivity; apply Prod.mk;
                          { intro; apply contrImplProp; apply w.2.2.1 };
                          { intro; apply boolIsSet } }
      | false, true  => { fapply Sigma.mk; intro p; apply explode; apply w.2.1 p; apply Prod.mk;
                          { intro p; apply explode; apply w.2.1 p };
                          { intro; apply explode; apply ffNeqTt; assumption } }
      | true,  false => { fapply Sigma.mk; intro p; apply explode; apply w.2.1 p⁻¹; apply Prod.mk;
                          { intro p; apply explode; apply w.2.1 p⁻¹ };
                          { intro; apply explode; apply ffNeqTt; symmetry; assumption } }
      | true,  true  => { fapply Sigma.mk; intro; reflexivity; apply Prod.mk;
                          { intro; apply contrImplProp; apply w.2.2.2 };
                          { intro; apply boolIsSet } } };
    apply Prod.mk;
    { intro w; apply Sigma.prod; apply productProp; apply notIsProp;
      apply productProp <;> apply contrIsProp; reflexivity };
    { intro b; apply Sigma.prod;
      { apply piProp; intro; apply piProp; intro; apply Equiv.biinvProp };
      { apply Theorems.funext; intro b; induction b using Bool.casesOn <;> reflexivity } }
  end
end «4.8»

-- exercise 4.9

hott example {A : Type u} {B : A → Type v} {f g : Π x, B x} : (f = g) ≃ (f ~ g) :=
Theorems.full -- see “Structures.lean” for this kind of proof
