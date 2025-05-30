import GroundZero.Algebra.Group.Symmetric
import GroundZero.HITs.Setquot

open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.HITs
open GroundZero

namespace GroundZero.Algebra
universe u v w

namespace Group
  hott def leftAction (G : Group) (A : Type u) :=
  Σ (φ : G.carrier → A → A), (Π x, φ G.e x = x) × (Π g h x, φ g (φ h x) = φ (G.φ g h) x)
  infix:20 " ⮎ " => leftAction

  hott def leftAction.id {G : Group} {A : Type u} (H : Structures.hset A)
    (φ ψ : G ⮎ A) (p : φ.1 ~ ψ.1) : φ = ψ :=
  begin
    fapply Sigma.prod; apply Theorems.funext; exact p;
    apply productProp; apply piProp; intro; apply H;
    apply piProp; intro; apply piProp; intro; apply piProp; intro; apply H
  end

  hott def rightAction (G : Group) (A : Type u) :=
  Σ (φ : A → G.carrier → A), (Π x, φ x G.e = x) × (Π g h x, φ (φ x g) h = φ x (G.φ g h))
  infix:20 " ⮌ " => rightAction

  variable {G : Group}

  section
    variable {A : Type u}

    hott def rightAction.associated : (G ⮎ A) → (G ⮌ A) :=
    λ ⟨φ, (p, q)⟩, ⟨λ x g, φ (G.ι g) x, (begin
      intro x; transitivity; apply ap (φ · x);
      symmetry; apply unitInv; apply p
    end, begin
      intros g h x; transitivity;
      apply q; apply ap (φ · x);
      symmetry; apply invExplode
    end)⟩

    hott def orbit (φ : G ⮎ A) (x : A) :=
    GroundZero.Algebra.im (φ.1 · x)

    hott def Orb (φ : G ⮎ A) (x : A) :=
    (orbit φ x).subtype

    hott def orbitᵣ (φ : G ⮌ A) (x : A) :=
    GroundZero.Algebra.im (φ.1 x)

    hott def Orbᵣ (φ : G ⮌ A) (x : A) :=
    (orbitᵣ φ x).subtype
  end

  hott def S.ap {A : 0-Type} : S A ⮎ A.1 :=
  ⟨λ f x, f.1 x, (idp, λ ⟨g, G⟩ ⟨h, G⟩ x, idp (g (h x)))⟩

  hott def leftAction.cut {A : Type u} (φ : G.subgroup) :
    (G ⮎ A) → (Subgroup G φ ⮎ A) :=
  λ ⟨φ, (p, q)⟩, ⟨λ ⟨g, G⟩ x, φ g x, (p, λ ⟨g, G⟩ ⟨h, G⟩, q g h)⟩

  hott def leftAction.eqv {A : Type u} (φ : G ⮎ A) (n m : A) :=
  ∥(Σ g, φ.1 g n = m)∥

  hott def leftAction.refl {A : Type u} (φ : G ⮎ A) {a : A} : φ.eqv a a :=
  begin apply HITs.Merely.elem; existsi G.e; apply φ.2.1 end

  hott def leftAction.symm {A : Type u} (φ : G ⮎ A)
    {a b : A} : φ.eqv a b → φ.eqv b a :=
  begin
    apply HITs.Merely.lift;
    intro ⟨g, p⟩; existsi G.ι g;
    transitivity; apply ap; exact Id.inv p;
    transitivity; apply φ.2.2;
    transitivity; apply ap (φ.1 · a);
    apply G.mulLeftInv; apply φ.2.1
  end

  hott def leftAction.trans {A : Type u} (φ : G ⮎ A)
    {a b c : A} : φ.eqv a b → φ.eqv b c → φ.eqv a c :=
  begin
    apply HITs.Merely.lift₂; intro ⟨g, p⟩ ⟨h, q⟩;
    existsi G.φ h g; transitivity; symmetry; apply φ.2.2;
    transitivity; apply ap; exact p; exact q
  end

  hott def leftAction.rel {A : Type u} (φ : G ⮎ A) : hrel A :=
  λ n m, ⟨φ.eqv n m, HITs.Merely.uniq⟩

  hott def leftAction.eqrel {A : Type u} (φ : G ⮎ A) : eqrel A :=
  ⟨leftAction.rel φ, (λ _, φ.refl, λ _ _, φ.symm, λ _ _ _, φ.trans)⟩

  hott def orbit.subset {A : Type u} (φ : G ⮎ A) {a b : A}
    (p : φ.eqv a b) : orbit φ a ⊆ orbit φ b :=
  begin intros c G; apply φ.trans; apply φ.symm p; exact G end

  hott def Orbits {A : Type u} (φ : G ⮎ A) :=
  Relquot φ.eqrel

  hott def transitive {A : Type u} (φ : G ⮎ A) :=
  Π a b, ∥(Σ g, φ.fst g a = b)∥

  hott def free {A : Type u} (φ : G ⮎ A) :=
  Π x g h, φ.fst g x = φ.fst h x → g = h

  hott def regular {A : Type u} (φ : G ⮎ A) :=
  Π a b, contr (Σ g, φ.fst g a = b)

  inductive Marked (A : Type u) (β : Type v)
  | elem : A → Marked A β
  | comp : β → Marked A β → Marked A β

  section
    private structure Fga.aux (A : Type u) (G : Group) :=
    (val : Marked A G.carrier)

    attribute [nothott] Fga.aux Fga.aux.mk Fga.aux.recOn Fga.aux.rec Fga.aux.val

    def Fga (A : Type u) (G : Group) := Fga.aux A G
  end

  namespace Fga
    variable {A : Type u}

    def elem : A → Fga A G := aux.mk ∘ Marked.elem

    def φ (g : G.carrier) (x : Fga A G) : Fga A G :=
    Fga.aux.mk (Marked.comp g x.val)

    axiom unit  : Π (x : Fga A G), φ G.e x = x
    axiom assoc : Π (g h : G.carrier) (x : Fga A G), φ g (φ h x) = φ (G.φ g h) x

    axiom ens : Structures.hset (Fga A G)

    section
      variable (ψ : G ⮎ A)

      @[nothott] def rec.aux (H : Structures.hset A) : Marked A G.carrier → A
      | Marked.elem x   => x
      | Marked.comp g x => ψ.1 g (aux H x)

      def rec (H : Structures.hset A) : Fga A G → A := rec.aux ψ H ∘ @aux.val A G
    end

    attribute [hottAxiom] Fga elem φ unit assoc ens rec

    attribute [irreducible] Fga

    hott def act : G ⮎ Fga A G :=
    ⟨φ, (unit, assoc)⟩
  end Fga

  hott def pact {A : Type u} : G ⮎ G.carrier × A :=
  ⟨λ g ⟨h, x⟩, (G.φ g h, x),
   (λ ⟨g, x⟩, Product.prod (G.oneMul g) (idp x),
    λ g h ⟨f, x⟩, Product.prod (Id.inv (G.mulAssoc g h f)) (idp x))⟩

  hott def regular.mk {A : Type u} (H : Structures.hset A)
    (φ : G ⮎ A) : transitive φ → free φ → regular φ :=
  begin
    intros f g a b; fapply HITs.Merely.rec _ _ (f a b);
    { apply contrIsProp };
    { intro p; existsi p;
      intro q; fapply Sigma.prod;
      { apply g a; transitivity; exact p.2;
        symmetry; exact q.2 };
      { apply H } }
  end

  hott def regular.elim {A : Type u}
    (φ : G ⮎ A) : regular φ → transitive φ × free φ :=
  begin
    intro H; apply Prod.mk;
    { intros a b; apply HITs.Merely.elem; exact (H a b).1 };
    { intros x g h p;
      apply @ap (Σ g, φ.fst g x = φ.fst h x) G.carrier
                ⟨g, p⟩ ⟨h, Id.refl⟩ Sigma.fst;
      apply contrImplProp; apply H }
  end

  hott def regularIsProp {A : Type u} (φ : G ⮎ A) : prop (regular φ) :=
  begin apply piProp; intro; apply piProp; intro; apply contrIsProp end

  hott def transitiveIsProp {A : Type u} (φ : G ⮎ A) : prop (transitive φ) :=
  begin apply piProp; intro; apply piProp; intro; apply HITs.Merely.uniq end

  hott def freeIsProp {A : Type u} (φ : G ⮎ A) : prop (free φ) :=
  begin apply piProp; intro; apply piProp; intro; apply piProp; intro; apply piProp; intro; apply G.hset end

  hott def regular.eqv {A : Type u} (H : Structures.hset A)
    (φ : G ⮎ A) : regular φ ≃ transitive φ × free φ :=
  begin
    apply propEquivLemma; apply regularIsProp;
    apply productProp; apply transitiveIsProp; apply freeIsProp;
    apply regular.elim; intro w; apply regular.mk H φ w.1 w.2
  end
end Group

end GroundZero.Algebra
