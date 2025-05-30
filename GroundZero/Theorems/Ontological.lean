import GroundZero.Proto
open Lean.TSyntax.Compat

/-
  Some emendations of Gödel’s Ontological proof.
  * https://appearedtoblogly.files.wordpress.com/2011/05/anderson-anthony-c-22some-emendations-of-gc3b6dels-Ontological-proof22.pdf

  A New Small Emendation of Gödel’s Ontological Proof.
  * https://www.jstor.org/stable/20016426

  Gödel’s Ontological proof is formalized here using 𝒜𝒪′₀ system (see last paper).
  Since only FOL used in this formalization, the definition of a God-like
  is encoded as an inference rule (gd₁) and an axiom (gd₂).
  Moreover, it is interesting that positivity of a property can be viewed
  as a quantifier of a special kind, because its type is the same
  as the type of the universal quantifier: (ι → wff) → wff.
-/

namespace GroundZero.Theorems.Ontological
  universe u

  -- individuals
  variable {ι : Type u}

  inductive wff (ι : Type u)
  | P        : (ι → wff ι) → wff ι   -- positive
  | «forall» : (ι → wff ι) → wff ι   -- for all
  | G        : ι → wff ι             -- God-like
  | impl     : wff ι → wff ι → wff ι -- implication
  | box      : wff ι → wff ι         -- necessary
  | false    : wff ι                 -- falsehood
  open wff (P G)
  -- property
  def prop (ι : Type u) := ι → wff ι

  macro "⋀ " is:Lean.explicitBinders ", " e:term : term =>
    Lean.expandExplicitBinders ``wff.«forall» is e

  infixr:20 " ⇒ " => wff.impl
  prefix:max "□" => wff.box

  notation "⊥" => wff.false

  def not (φ : wff ι) := φ ⇒ ⊥
  prefix:max (priority := high) "¬" => not

  def diam (φ : wff ι) := ¬□¬φ
  prefix:max "◇" => diam

  def «exists» (φ : prop ι) := ¬(⋀ x, ¬(φ x))

  macro "⋁ " is:Lean.explicitBinders ", " e:term : term =>
    Lean.expandExplicitBinders ``«exists» is e

  def or (φ ψ : wff ι) := ¬φ ⇒ ψ
  infixl:60 (priority := high) " ∨ " => or

  def and (φ ψ : wff ι) := ¬(φ ⇒ ¬ψ)
  infixl:70 (priority := high) " ∧ " => and

  def iff (φ ψ : wff ι) := (φ ⇒ ψ) ∧ (ψ ⇒ φ)
  infix:20 " ⇔ " => iff

  def subset (φ ψ : prop ι) := ⋀ x, φ x ⇒ ψ x
  infix:55 " ⊆ " => subset

  def equal (φ ψ : prop ι) := ⋀ x, φ x ⇔ ψ x
  infix:50 " ≡ " => equal

  def compl (φ : prop ι) : prop ι := λ x, ¬(φ x)

  inductive deriv : wff ι → Type u
  -- classical propositional calculus
  | mp   : Π φ ψ, deriv (φ ⇒ ψ) → deriv φ → deriv ψ
  | ak   : Π φ ψ, deriv (φ ⇒ ψ ⇒ φ)
  | ac   : Π φ ψ, deriv ((¬φ ⇒ ¬ψ) ⇒ (ψ ⇒ φ))
  | as   : Π φ ψ ξ, deriv ((φ ⇒ ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ))
  -- classical predicate logic
  | gen  : Π (φ : prop ι), (Π x, deriv (φ x)) → deriv (⋀ x, φ x)
  | ap   : Π (x : ι) (φ : prop ι), deriv ((⋀ y, φ y) ⇒ φ x)
  | dis  : Π (φ ψ : prop ι), deriv ((⋀ x, φ x ⇒ ψ x) ⇒ (⋀ x, φ x) ⇒ (⋀ y, ψ y))
  | triv : Π (φ : wff ι), deriv (φ ⇒ ⋀ x, φ)
  -- S5 modal logic
  | nec  : Π φ, deriv φ → deriv □φ
  | K    : Π φ ψ, deriv (□(φ ⇒ ψ) ⇒ □φ ⇒ □ψ)
  | T    : Π φ, deriv (□φ ⇒ φ)
  | «5»  : Π φ, deriv (◇φ ⇒ □◇φ)
  -- Ontological logic
  | gd₁  : Π x, (Π (φ : prop ι), deriv (P φ ⇔ □(φ x))) → deriv (G x)
  | gd₂  : Π (x : ι) (φ : prop ι), deriv (G x ⇒ P φ ⇔ □(φ x))
  | wkc  : Π (φ ψ : prop ι), deriv (□(φ ≡ ψ) ⇒ P φ ⇔ P ψ)
  | pimp : Π (φ ψ : prop ι), deriv (P φ ⇒ □(φ ⊆ ψ) ⇒ ¬(P (compl ψ)))
  | gp   : deriv (P G)
  open deriv

  prefix:10 "⊢ " => deriv

  hott def I (φ : wff ι) : ⊢ φ ⇒ φ :=
  begin apply mp; apply mp; apply as φ (φ ⇒ φ) φ; apply ak; apply ak end

  hott def lem (φ : wff ι) : ⊢ φ ∨ ¬φ := I ¬φ

  def true : wff ι := ¬⊥
  notation "⊤" => true

  hott def true.intro : @deriv ι ⊤ := I ⊥

  hott def mp₂ (φ ψ ξ : wff ι) : (⊢ φ ⇒ ψ ⇒ ξ) → (⊢ φ) → (⊢ ψ) → (⊢ ξ) :=
  begin intros p q r; apply mp ψ; apply mp φ; exact p; exact q; exact r end

  hott def impl.intro (φ ψ : wff ι) (h : ⊢ ψ) : ⊢ φ ⇒ ψ :=
  begin apply mp; apply ak; assumption end

  hott def S {φ ψ ξ : wff ι} (f : ⊢ φ ⇒ ψ ⇒ ξ) (g : ⊢ φ ⇒ ψ) : ⊢ φ ⇒ ξ :=
  begin apply mp₂; apply as φ ψ ξ; exact f; exact g end

  hott def AS {φ ψ ξ : wff ι} (f : ⊢ φ ⇒ ψ ⇒ ξ) : ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ ξ) :=
  begin apply mp; apply as; exact f end

  -- https://en.wikipedia.org/wiki/Hypothetical_syllogism#Proof
  hott def impl.comp (φ ψ ξ : wff ι) : ⊢ (ψ ⇒ ξ) ⇒ (φ ⇒ ψ) ⇒ (φ ⇒ ξ) :=
  begin
    apply mp ((ψ ⇒ ξ) ⇒ (φ ⇒ ψ ⇒ ξ));
    apply AS; apply impl.intro;
    apply as; apply ak
  end

  hott def hypsyll (φ ψ ξ : wff ι) : (⊢ ψ ⇒ ξ) → (⊢ φ ⇒ ψ) → (⊢ φ ⇒ ξ) :=
  begin apply mp₂; apply impl.comp end

  -- https://en.wikipedia.org/wiki/Hilbert_system#Some_useful_Theorems_and_their_proofs
  hott def impl.symm (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ξ) :=
  begin
    apply mp ((φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ψ));
    apply mp ((φ ⇒ ψ ⇒ ξ) ⇒ (ψ ⇒ φ ⇒ ψ) ⇒ (ψ ⇒ φ ⇒ ξ));
    apply as; apply hypsyll _ ((φ ⇒ ψ) ⇒ (φ ⇒ ξ)) _;
    apply impl.comp; apply as; apply impl.intro; apply ak
  end

  hott def impl.trans (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ ξ) ⇒ (φ ⇒ ξ) :=
  begin apply mp; apply impl.symm; apply impl.comp end

  hott def impl.symm₂ (φ ψ ξ ζ : wff ι) : ⊢ (φ ⇒ ψ ⇒ ζ ⇒ ξ) ⇒ (ζ ⇒ ψ ⇒ φ ⇒ ξ) :=
  begin
    apply hypsyll; apply impl.symm;
    fapply hypsyll; exact (ψ ⇒ φ ⇒ ζ ⇒ ξ);
    apply mp; apply impl.comp; apply impl.symm; apply impl.symm
  end

  hott def impl.apply (φ ψ : wff ι) : ⊢ φ ⇒ (φ ⇒ ψ) ⇒ ψ :=
  begin apply mp; apply impl.symm; apply I end

  hott def dneg.intro (φ : wff ι) : ⊢ φ ⇒ ¬¬φ :=
  by apply impl.apply

  hott def dneg.elim (φ : wff ι) : ⊢ ¬¬φ ⇒ φ :=
  begin apply mp; apply ac; apply dneg.intro end

  hott def explode (φ : wff ι) : ⊢ ⊥ ⇒ φ :=
  begin apply mp; apply ac; apply impl.intro; apply true.intro end

  hott def contradiction (φ ψ : wff ι) : ⊢ φ ⇒ ¬φ ⇒ ψ :=
  begin
    apply mp; apply impl.symm;
    apply AS; apply impl.intro; apply explode
  end

  hott def contraposition (φ ψ : wff ι) : ⊢ (φ ⇒ ψ) ⇒ (¬ψ ⇒ ¬φ) :=
  begin apply mp; apply impl.symm; apply impl.comp end

  hott def contraposition₁ (φ ψ : wff ι) : ⊢ (φ ⇒ ¬ψ) ⇒ ψ ⇒ ¬φ :=
  begin apply hypsyll; apply ac; apply mp; apply impl.trans; apply dneg.elim end

  hott def contraposition₂ (φ ψ : wff ι) : ⊢ (¬φ ⇒ ψ) ⇒ ¬ψ ⇒ φ :=
  begin apply hypsyll; apply ac; apply mp; apply impl.comp; apply dneg.intro end

  hott def or.swap (φ ψ : wff ι) : ⊢ φ ∨ ψ ⇒ ψ ∨ φ :=
  begin apply hypsyll; apply ac; apply AS; apply impl.intro; apply dneg.intro end

  hott def or.inl (φ ψ : wff ι) : ⊢ φ ⇒ φ ∨ ψ :=
  by apply contradiction

  hott def or.inr (φ ψ : wff ι) : ⊢ ψ ⇒ φ ∨ ψ :=
  begin apply hypsyll; apply or.swap; apply or.inl end

  hott def and.intro (φ ψ : wff ι) : ⊢ φ ⇒ ψ ⇒ φ ∧ ψ :=
  begin
    apply mp; apply impl.symm;
    apply mp; apply impl.symm₂; apply I
  end

  hott def and.symm (φ ψ : wff ι) : ⊢ φ ∧ ψ ⇒ ψ ∧ φ :=
  begin apply mp; apply contraposition; apply contraposition₁ end

  hott def and.pr₁ (φ ψ : wff ι) : ⊢ φ ∧ ψ ⇒ φ :=
  begin
    apply mp; apply contraposition₂;
    apply mp; apply impl.symm; apply contradiction
  end

  hott def and.pr₂ (φ ψ : wff ι) : ⊢ φ ∧ ψ ⇒ ψ :=
  begin apply hypsyll; apply and.pr₁; exact φ; apply and.symm end

  hott def iff.intro (φ ψ : wff ι) (f : ⊢ φ ⇒ ψ) (g : ⊢ ψ ⇒ φ) : ⊢ φ ⇔ ψ :=
  begin apply mp₂; apply and.intro; exact f; exact g end

  hott def iff.left {φ ψ : wff ι} (H : ⊢ φ ⇔ ψ) : ⊢ φ ⇒ ψ :=
  begin apply mp; apply and.pr₁; exact (ψ ⇒ φ); exact H end

  hott def iff.right {φ ψ : wff ι} (H : ⊢ φ ⇔ ψ) : ⊢ ψ ⇒ φ :=
  begin apply mp; apply and.pr₂; exact (φ ⇒ ψ); exact H end

  hott def iff.symm {φ ψ : wff ι} (H : ⊢ φ ⇔ ψ) : ⊢ ψ ⇔ φ :=
  begin apply mp; apply and.symm; exact H end

  hott def iff.antcdtsubst {φ ψ ξ : wff ι} (f : ⊢ φ ⇔ ψ) (g : ⊢ ξ ⇒ φ) : ⊢ ξ ⇒ ψ :=
  begin apply hypsyll; apply iff.left f; exact g end

  hott def iff.consqsubst {φ ψ ξ : wff ι} (f : ⊢ φ ⇔ ψ) (g : ⊢ φ ⇒ ξ) : ⊢ ψ ⇒ ξ :=
  begin apply hypsyll; exact g; apply iff.right f end

  hott def iff.antcdtiff {φ ψ ξ : wff ι} (H : ⊢ φ ⇔ ψ) : ⊢ (ξ ⇒ φ) ⇔ (ξ ⇒ ψ) :=
  begin
    apply iff.intro; apply mp; apply impl.comp; apply iff.left H;
    apply mp; apply impl.comp; apply iff.right H
  end

  hott def iff.consqiff {φ ψ ξ : wff ι} (H : ⊢ φ ⇔ ψ) : ⊢ (φ ⇒ ξ) ⇔ (ψ ⇒ ξ) :=
  begin
    apply iff.intro; apply mp; apply impl.trans; apply iff.right H;
    apply mp; apply impl.trans; apply iff.left H
  end

  hott def dneg (φ : wff ι) : ⊢ φ ⇔ ¬¬φ :=
  begin apply iff.intro; apply dneg.intro; apply dneg.elim end

  hott def contrapos₁ (φ ψ : wff ι) : ⊢ (φ ⇒ ψ) ⇔ (¬ψ ⇒ ¬φ) :=
  begin apply iff.intro; apply contraposition; apply ac end

  hott def contrapos₂ (φ ψ : wff ι) : ⊢ (φ ⇒ ¬ψ) ⇔ (ψ ⇒ ¬φ) :=
  begin apply iff.intro <;> apply contraposition₁ end

  hott def contrapos₃ (φ ψ : wff ι) : ⊢ (¬φ ⇒ ψ) ⇔ (¬ψ ⇒ φ) :=
  begin apply iff.intro <;> apply contraposition₂ end

  hott def dedup (φ ψ : wff ι) : ⊢ (φ ⇒ φ ⇒ ψ) ⇒ (φ ⇒ ψ) :=
  begin apply mp; apply mp; apply impl.symm; apply as; apply I end

  hott def dup (φ ψ : wff ι) : ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ φ ⇒ ψ) :=
  by apply ak

  hott def impl.negdef₁ (φ ψ : wff ι) : ⊢ ¬(φ ⇒ ψ) ⇒ (φ ∧ ¬ψ) :=
  begin
    apply mp; apply contraposition;
    apply mp; apply impl.comp; apply dneg.elim
  end

  hott def impl.negdef₂ (φ ψ : wff ι) : ⊢ (φ ∧ ¬ψ) ⇒ ¬(φ ⇒ ψ) :=
  begin
    apply mp; apply contraposition;
    apply mp; apply impl.comp; apply dneg.intro
  end

  hott def impl.negdef (φ ψ : wff ι) : ⊢ ¬(φ ⇒ ψ) ⇔ (φ ∧ ¬ψ) :=
  begin apply iff.intro; apply impl.negdef₁; apply impl.negdef₂ end

  hott def rot₁ (φ ψ ξ : wff ι) : ⊢ (¬ξ ⇒ φ ⇒ ¬ψ) ⇒ (φ ⇒ ψ ⇒ ξ) :=
  begin
    apply hypsyll; apply mp; apply impl.comp;
    exact (¬ξ ⇒ ¬ψ); apply ac; apply impl.symm
  end

  hott def rot₂ (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (¬ξ ⇒ φ ⇒ ¬ψ) :=
  begin
    apply hypsyll; apply impl.symm;
    apply mp; apply impl.comp;
    apply contraposition
  end

  hott def curry (φ ψ ξ : wff ι) : ⊢ (φ ∧ ψ ⇒ ξ) ⇒ (φ ⇒ ψ ⇒ ξ) :=
  begin apply hypsyll; apply rot₁; apply contraposition₂ end

  hott def uncurry (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (φ ∧ ψ ⇒ ξ) :=
  begin apply hypsyll; apply contraposition₂; apply rot₂ end

  hott def or.neg (φ ψ : wff ι) : ⊢ ¬(φ ∨ ψ) ⇔ (¬φ) ∧ ¬ψ :=
  begin
    apply iff.intro;
    { apply mp; apply contraposition;
      apply mp; apply impl.comp; apply dneg.elim };
    { apply mp; apply contraposition;
      apply mp; apply impl.comp; apply dneg.intro }
  end

  hott def or.triv (φ : wff ι) : ⊢ φ ∨ φ ⇒ φ :=
  begin
    apply mp; apply ac; apply iff.antcdtsubst;
    apply iff.symm; apply or.neg;
    apply mp; apply dedup; apply and.intro
  end

  hott def absurd (φ : wff ι) : ⊢ (¬φ ⇒ φ) ⇒ φ :=
  by apply or.triv

  hott def indep (φ ψ : wff ι) : ⊢ (¬φ ⇒ ψ) ⇒ (φ ⇒ ψ) ⇒ ψ :=
  begin
    apply iff.consqsubst; apply contrapos₃;
    apply mp; apply curry; apply mp₂; apply impl.trans;
    exact (¬ψ ⇒ ψ); apply mp; apply uncurry;
    apply impl.trans; apply absurd
  end

  hott def or.elim (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ξ) ⇒ (ψ ⇒ ξ) ⇒ (φ ∨ ψ ⇒ ξ) :=
  begin
    apply mp; apply impl.symm₂; apply mp; apply curry;
    apply mp₂; apply impl.trans; exact (¬φ ⇒ ξ);
    apply mp; apply uncurry; apply impl.trans; apply indep
  end

  hott def boximpl (φ ψ : wff ι) (H : ⊢ φ ⇒ ψ) : ⊢ □φ ⇒ □ψ :=
  begin apply mp; apply K; apply nec; exact H end

  hott def diamimpl (φ ψ : wff ι) (H : ⊢ φ ⇒ ψ) : ⊢ ◇φ ⇒ ◇ψ :=
  begin
    apply mp; apply contraposition; apply boximpl;
    apply mp; apply contraposition; exact H
  end

  hott def boxcongr (φ ψ : wff ι) (H : ⊢ φ ⇔ ψ) : ⊢ □φ ⇔ □ψ :=
  begin apply iff.intro; apply boximpl; apply iff.left H; apply boximpl; apply iff.right H end

  hott def negiff (φ ψ : wff ι) (H : ⊢ φ ⇔ ψ) : ⊢ ¬φ ⇔ ¬ψ :=
  begin
    apply iff.intro; apply mp; apply contraposition; apply iff.right H;
    apply mp; apply contraposition; apply iff.left H
  end

  hott def impl.comp₃ (φ ψ ξ θ : wff ι) : ⊢ (φ ⇒ ψ ⇒ ξ) ⇒ (θ ⇒ φ) ⇒ (θ ⇒ ψ) ⇒ (θ ⇒ ξ) :=
  begin
    apply mp; apply impl.symm; apply mp; apply curry;
    apply hypsyll; apply as; apply mp; apply uncurry; apply impl.trans
  end

  hott def and.impl (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ) ⇒ (φ ⇒ ξ) ⇒ (φ ⇒ ψ ∧ ξ) :=
  begin apply mp; apply impl.comp₃; apply and.intro end

  hott def or.assoc₁ (φ ψ ξ : wff ι) : ⊢ (φ ∨ ψ) ∨ ξ ⇒ φ ∨ (ψ ∨ ξ) :=
  begin
    apply mp₂; apply or.elim;
    { apply mp₂; apply or.elim; { apply or.inl };
      { apply hypsyll; apply or.inr; apply or.inl } };
    { apply hypsyll; apply or.inr; apply or.inr }
  end

  hott def or.assoc₂ (φ ψ ξ : wff ι) : ⊢ φ ∨ (ψ ∨ ξ) ⇒ (φ ∨ ψ) ∨ ξ :=
  begin
    apply mp₂; apply or.elim;
    { apply hypsyll; apply or.inl; apply or.inl };
    { apply mp₂; apply or.elim;
      { apply hypsyll; apply or.inl; apply or.inr };
      { apply or.inr } }
  end

  hott def or.assoc (φ ψ ξ : wff ι) : ⊢ (φ ∨ ψ) ∨ ξ ⇔ φ ∨ (ψ ∨ ξ) :=
  begin apply iff.intro; apply or.assoc₁; apply or.assoc₂ end

  hott def and.assoc₁ (φ ψ ξ : wff ι) : ⊢ (φ ∧ ψ) ∧ ξ ⇒ φ ∧ (ψ ∧ ξ) :=
  begin
    apply mp₂; apply and.impl;
    { apply hypsyll; apply and.pr₁; exact ψ; apply and.pr₁ };
    { apply mp₂; apply and.impl;
      { apply hypsyll; apply and.pr₂; exact φ; apply and.pr₁ };
      { apply and.pr₂ } }
  end

  hott def and.assoc₂ (φ ψ ξ : wff ι) : ⊢ φ ∧ (ψ ∧ ξ) ⇒ (φ ∧ ψ) ∧ ξ :=
  begin
    apply mp₂; apply and.impl;
    { apply mp₂; apply and.impl; { apply and.pr₁ };
      { apply hypsyll; apply and.pr₁; exact ξ; apply and.pr₂ } };
    { apply hypsyll; apply and.pr₂; exact ψ; apply and.pr₂ }
  end

  hott def and.assoc (φ ψ ξ : wff ι) : ⊢ (φ ∧ ψ) ∧ ξ ⇔ φ ∧ (ψ ∧ ξ) :=
  begin apply iff.intro; apply and.assoc₁; apply and.assoc₂ end

  hott def prodpimp (φ ψ : prop ι) : ⊢ P φ ∧ □(φ ⊆ ψ) ⇒ ¬(P (compl ψ)) :=
  begin apply mp; apply uncurry; apply pimp end

  hott def impl.pr₁ (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ ∧ ξ) ⇒ (φ ⇒ ψ) :=
  begin apply mp; apply impl.comp; apply and.pr₁ end

  hott def impl.pr₂ (φ ψ ξ : wff ι) : ⊢ (φ ⇒ ψ ∧ ξ) ⇒ (φ ⇒ ξ) :=
  begin apply mp; apply impl.comp; apply and.pr₂ end

  hott def subset.refl (φ : prop ι) : ⊢ φ ⊆ φ :=
  begin apply gen; intro x; apply I end

  hott def prop.dneg (φ : prop ι) : ⊢ compl (compl φ) ≡ φ :=
  begin apply gen; intro x; apply iff.symm; apply Ontological.dneg end

  hott def thm1 (φ : prop ι) : ⊢ P φ ⇒ ◇(⋁ x, φ x) :=
  begin
    apply mp; apply ac; apply iff.consqsubst; apply dneg;
    apply iff.consqsubst; apply boxcongr; apply dneg;
    apply iff.antcdtsubst; apply negiff; apply mp; apply wkc;
    exact compl (compl φ); apply nec; apply prop.dneg;
    apply hypsyll; apply prodpimp; exact G;
    apply mp₂; apply and.impl; apply impl.intro; apply gp;
    apply mp; apply K; apply nec;
    apply mp; apply dis; apply gen; intro x; apply ak
  end

  hott def perfneg (φ : prop ι) : ⊢ P φ ⇒ ¬(P (compl φ)) :=
  begin
    apply hypsyll; apply prodpimp φ φ;
    apply mp; apply mp; apply impl.symm; apply and.intro;
    apply nec; apply subset.refl
  end

  hott def thm2 : @deriv ι ◇(⋁ x, G x) :=
  begin apply mp; apply thm1; apply gp end

  -- Anselm’s principle
  hott def anselm (x : ι) : ⊢ G x ⇒ □(G x) :=
  begin
    apply mp₂; apply as; exact P G;
    apply mp; apply impl.pr₁; exact (□(G x) ⇒ P G);
    apply gd₂; apply impl.intro; apply gp
  end

  -- https://plato.stanford.edu/entries/actualism/proofBF.html
  hott def boxdiam (φ : wff ι) : ⊢ φ ⇒ □◇φ :=
  begin
    fapply hypsyll; exact ◇φ; apply «5»;
    fapply hypsyll; exact ¬□¬φ;
    apply mp; apply contraposition; apply I;
    apply mp; apply contraposition₁; apply T
  end

  hott def diamboximplbox (φ : wff ι) : ⊢ ◇□φ ⇒ □φ :=
  begin
    apply mp; apply contraposition₂; apply iff.antcdtsubst;
    apply boxcongr; apply negiff; apply boxcongr; apply iff.symm; apply dneg;
    apply iff.consqsubst; apply negiff; apply boxcongr;
    apply iff.symm; apply dneg; apply «5»
  end

  hott def diambox (φ : wff ι) : ⊢ ◇□φ ⇒ φ :=
  begin apply hypsyll; apply T; apply diamboximplbox end

  hott def dr (φ ψ : wff ι) (H : ⊢ ◇φ ⇒ ψ) : ⊢ φ ⇒ □ψ :=
  begin apply hypsyll; apply boximpl; exact H; apply boxdiam end

  hott def kdiam (φ ψ : wff ι) : ⊢ □(φ ⇒ ψ) ⇒ ◇φ ⇒ ◇ψ :=
  begin
    apply iff.antcdtsubst; apply contrapos₁;
    apply hypsyll; apply K; apply mp; apply K;
    apply nec; apply contraposition
  end

  hott def barcan (φ : prop ι) : ⊢ (⋀ x, □(φ x)) ⇒ □(⋀ x, φ x) :=
  begin
    apply dr; fapply mp; exact ⋀ x, (◇(⋀ x, □(φ x)) ⇒ φ x);
    apply mp₂; apply impl.trans; exact (⋀ x, ◇(⋀ y, □(φ y))) ⇒ ⋀ x, φ x;
    apply dis; apply mp; apply impl.trans; apply triv;
    apply gen; intro x; apply hypsyll; apply diambox;
    fapply mp; exact □ ((⋀ y, □(φ y)) ⇒ □(φ x));
    apply kdiam; apply nec; apply ap;
  end

  -- https://plato.stanford.edu/entries/actualism/proofCBF.html
  hott def cbf (φ : prop ι) : ⊢ □(⋀ x, φ x) ⇒ ⋀ x, □(φ x) :=
  begin
    fapply mp; exact ⋀ x, □(⋀ y, φ y) ⇒ □(φ x);
    fapply hypsyll; exact ((⋀ x, □(⋀ y, φ y)) ⇒ ⋀ x, □(φ x));
    apply mp; apply impl.trans; apply triv;
    apply dis; apply gen; intro x; apply mp; apply K; apply nec; apply ap
  end

  hott def bfdiam (φ : prop ι) : ⊢ (⋁ x, ◇(φ x)) ⇒ ◇(⋁ x, φ x) :=
  begin
    apply mp; apply contraposition;
    apply iff.consqsubst; apply boxcongr; apply dneg;
    fapply hypsyll; exact (⋀ x, □¬(φ x));
    apply mp; apply dis; apply gen;
    { intro x; apply dneg.intro }; apply cbf
  end

  hott def cbfdiam (φ : prop ι) : ⊢ ◇(⋁ x, φ x) ⇒ ⋁ x, ◇(φ x) :=
  begin
    apply mp; apply contraposition;
    apply iff.antcdtsubst; apply boxcongr; apply dneg;
    apply hypsyll; apply barcan;
    apply mp; apply dis; apply gen;
    { intro x; apply dneg.elim }
  end

  hott def exdis (φ ψ : prop ι) (H : Π x, ⊢ φ x ⇒ ψ x) : ⊢ (⋁ x, φ x) ⇒ (⋁ x, ψ x) :=
  begin
    apply mp; apply contraposition; apply mp; apply dis;
    apply gen; intro x; apply mp; apply contraposition; apply H
  end

  hott def excbf (φ : prop ι) : ⊢ (⋁ x, □(φ x)) ⇒ □(⋁ x, φ x) :=
  begin
    apply dr; apply mp₂; apply impl.trans; exact (⋁ x, ◇□(φ x));
    apply cbfdiam; apply exdis; intro x; apply diambox
  end

  hott def thm3 : @deriv ι (◇(⋁ x, G x) ⇒ □(⋁ x, G x)) :=
  begin
    apply hypsyll; apply excbf; fapply hypsyll; exact ◇(⋁ x, □(G x));
    apply mp₂; apply impl.trans; exact ⋁ x, ◇□(G x);
    apply cbfdiam; apply exdis; intro x;
    apply hypsyll; apply anselm; apply diambox;
    apply diamimpl; apply exdis; apply anselm
  end

  hott def «Gödel» : @deriv ι □(⋁ x, G x) :=
  begin apply mp; apply thm3; apply thm2 end

  hott def univ : prop ι := λ _, ⊤
  notation "𝒰" => univ

  hott def univ.poscompl : @deriv ι ¬(P (compl 𝒰)) :=
  begin
    apply mp₂; apply pimp; exact G;
    apply gp; apply nec; apply gen;
    intro x; apply impl.intro; apply true.intro
  end

  hott def gnecimpl {a b : ι} (f : ⊢ G a) (g : ⊢ G b) (φ : prop ι) : ⊢ □(φ a) ⇒ φ b :=
  begin
    apply mp₂; fapply impl.apply (P φ ∨ ¬(P φ));
    apply lem; apply mp₂; apply or.elim;
    { apply mp; apply curry; apply hypsyll; apply T;
      apply hypsyll; apply iff.left;
      apply mp; apply gd₂; exact g; apply and.pr₁ };
    { apply mp; apply curry; apply hypsyll;
      apply explode; apply mp; apply uncurry;
      apply mp; apply contraposition; apply iff.right;
      apply mp; apply gd₂; exact f }
  end

  hott def boxbox (φ : wff ι) : ⊢ □φ ⇒ □□φ :=
  begin apply dr; apply diamboximplbox end

  hott def gimplperfbox (φ : prop ι) (x : ι) : ⊢ G x ⇒ P φ ⇒ □(P φ) :=
  begin
    apply mp; apply curry; apply mp₂;
    apply impl.trans; exact G x ∧ □(φ x);
    apply mp₂; apply and.impl; apply and.pr₁;
    apply mp; apply uncurry; apply hypsyll;
    apply and.pr₁; exact □(φ x) ⇒ P φ; apply gd₂;
    apply mp₂; apply impl.trans;
    exact □(G x) ∧ □□(φ x); apply mp₂; apply and.impl;
    { apply hypsyll; apply anselm; apply and.pr₁ };
    { apply hypsyll; apply boxbox; apply and.pr₂ };
    apply mp; apply uncurry; apply hypsyll; apply K;
    apply mp; apply K; apply nec;
    apply hypsyll; apply and.pr₂; exact P φ ⇒ □(φ x); apply gd₂
  end

  hott def extriv (φ : wff ι) : ⊢ (⋁ x, φ) ⇒ φ :=
  begin
    apply mp; apply ac; apply mp₂; apply impl.trans;
    exact (⋀ x, ¬φ); apply triv; apply hypsyll; apply dneg.intro;
    apply mp; apply dis; apply gen; intro x; apply I
  end

  hott def perfectivebox (φ : prop ι) : ⊢ P φ ⇒ □(P φ) :=
  begin
    fapply mp; exact (⋁ x, G x); apply hypsyll; apply extriv; apply exdis;
    intro x; apply gimplperfbox; apply mp; apply T; exact «Gödel»
  end

  hott def tautbox {φ : wff ι} (H : ⊢ φ) : ⊢ φ ⇒ □φ :=
  begin apply impl.intro; apply nec; exact H end

end GroundZero.Theorems.Ontological
