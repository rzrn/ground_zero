import GroundZero.Theorems.Classical
import GroundZero.Algebra.Ring

open GroundZero.Types GroundZero.Proto
open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Theorems
open GroundZero.HITs

namespace GroundZero.Algebra
  universe u v

  -- this is exactly directed graph
  hott def Orgraph : Type (max u v + 1) :=
  @Alg.{0, 0, u, v} ⊥ 𝟏 (λ _, 2)

  hott def Orgraph.rel (Γ : Orgraph) (x y : Γ.carrier) : Prop := Alg.rel Γ ★ (x, y, ★)
  hott def Orgraph.ρ (Γ : Orgraph.{u}) (x y : Γ.carrier) : Type v := (Γ.rel x y).1

  hott def Orgraph.prop (Γ : Orgraph.{u}) (x y : Γ.carrier) : prop (Γ.ρ x y) := (Γ.rel x y).2

  class reflexive (Γ : Orgraph) :=
  (refl : Π x, Γ.ρ x x)

  hott def eqImplReflRel (Γ : Orgraph) [reflexive Γ] (a b : Γ.carrier) : a = b → Γ.ρ a b :=
  begin intro p; induction p; apply reflexive.refl end

  class symmetric (Γ : Orgraph) :=
  (symm : Π x y, Γ.ρ x y → Γ.ρ y x)

  class transitive (Γ : Orgraph) :=
  (trans : Π x y z, Γ.ρ x y → Γ.ρ y z → Γ.ρ x z)

  class equivalence (Γ : Orgraph) extends reflexive Γ, symmetric Γ, transitive Γ

  class antisymmetric (Γ : Orgraph) :=
  (asymm : Π x y, Γ.ρ x y → Γ.ρ y x → x = y)

  class order (Γ : Orgraph) extends reflexive Γ, antisymmetric Γ, transitive Γ

  hott def Overring.κ (T : Overring) : Orgraph :=
  ⟨T.1, (λ z, explode z, T.2.2)⟩

  class connected (Γ : Orgraph) :=
  (total : Π x y, ∥Γ.ρ x y + Γ.ρ y x∥)

  class total (Γ : Orgraph) extends order Γ, connected Γ

  class orfield (T : Overring) extends field T.τ, total T.κ :=
  (leOverAdd : Π (x y z : T.carrier), x ≤ y → x + z ≤ y + z)
  (leOverMul : Π (x y : T.carrier), 0 ≤ x → 0 ≤ y → 0 ≤ (x * y))

  noncomputable instance (T : Overring) [H : orfield T] : OfNat T.carrier (Nat.succ Nat.zero) := ⟨H.tohasOne.one⟩

  hott def majorant {Γ : Orgraph} (φ : Γ.subset) (M : Γ.carrier) :=
  Π x, x ∈ φ → Γ.ρ x M

  hott def minorant {Γ : Orgraph} (φ : Γ.subset) (m : Γ.carrier) :=
  Π x, x ∈ φ → Γ.ρ m x

  hott def exact {Γ : Orgraph} (φ : Γ.subset) (x : Γ.carrier) :=
  x ∈ φ × minorant φ x

  hott def coexact {Γ : Orgraph} (φ : Γ.subset) (x : Γ.carrier) :=
  x ∈ φ × majorant φ x

  hott def majorized {Γ : Orgraph} (φ : Γ.subset) := ∥Σ M, majorant φ M∥
  hott def minorized {Γ : Orgraph} (φ : Γ.subset) := ∥Σ m, minorant φ m∥

  hott def exactness   {Γ : Orgraph} (φ : Γ.subset) := ∥Σ M, exact φ M∥
  hott def coexactness {Γ : Orgraph} (φ : Γ.subset) := ∥Σ M, coexact φ M∥

  hott def bounded {Γ : Orgraph} (φ : Γ.subset) :=
  majorized φ × minorized φ

  hott def Majorant {Γ : Orgraph} (φ : Γ.subset) : Γ.subset :=
  ⟨majorant φ, begin
    intro; apply piProp;
    intro; apply piProp;
    intro; apply Γ.prop
  end⟩

  hott def Minorant {Γ : Orgraph} (φ : Γ.subset) : Γ.subset :=
  ⟨minorant φ, begin
    intro; apply piProp;
    intro; apply piProp;
    intro; apply Γ.prop
  end⟩

  hott def oneGtZero (T : Overring) [orfield T] : T.ρ 0 1 :=
  begin
    fapply GroundZero.HITs.Merely.rec _ _ (@connected.total T.κ _ _ _);
    change T.carrier; exact 0; change T.carrier; exact 1; apply T.κ.prop;
    { intro z; induction z using Sum.casesOn; assumption; apply explode;
      apply @field.nontrivial T.τ _; apply @antisymmetric.asymm T.κ;
      assumption; apply Equiv.transport; apply ring.minusOneSqr;
      apply orfield.leOverMul <;>
      { apply Equiv.transport (λ i, T.ρ i (-1));
        apply @Group.mulRightInv T.τ⁺; change T.carrier; exact 1;
        apply Equiv.transport; apply T.τ⁺.oneMul;
        apply orfield.leOverAdd; assumption } }
  end

  hott def leOverAddLeft (T : Overring) [orfield T] (a b c : T.carrier) (p : a ≤ b) : c + a ≤ c + b :=
  begin apply Equiv.transportconst; apply Equiv.bimap <;> apply T.τ.addComm; apply orfield.leOverAdd; exact p end

  hott def ineqAdd (T : Overring) [orfield T] {a b c d : T.carrier} (p : a ≤ b) (q : c ≤ d) : a + c ≤ b + d :=
  begin apply @transitive.trans T.κ; apply orfield.leOverAdd; exact p; apply leOverAddLeft; exact q end

  hott def leOverSubRight (T : Overring) [orfield T] (a b c : T.carrier) (p : a + c ≤ b + c) : a ≤ b :=
  begin
    apply Equiv.transport (λ w, w ≤ b); symmetry; apply @Group.cancelRight T.τ⁺ a c;
    apply Equiv.transport (λ w, (a + c) - c ≤ w); symmetry; apply @Group.cancelRight T.τ⁺ b c;
    apply orfield.leOverAdd; assumption
  end

  hott def leOverSubLeft (T : Overring) [orfield T] (a b c : T.carrier) (p : c + a ≤ c + b) : a ≤ b :=
  begin
    apply leOverSubRight T a b c; apply Equiv.transport (λ w, w ≤ b + c); apply T.τ.addComm;
    apply Equiv.transport (λ w, c + a ≤ w); apply T.τ.addComm; assumption
  end

  hott def subLeIfAddGe (T : Overring) [orfield T] {a b c : T.carrier} (p : a ≤ c + b) : a - b ≤ c :=
  begin
    apply leOverSubRight T (a - b) c b; apply Equiv.transport (λ w, w ≤ c + b);
    apply @Group.cancelLeft T.τ⁺; assumption
  end

  hott def subLeIfAddGeRev (T : Overring) [orfield T] {a b c : T.carrier} (p : a ≤ b + c) : a - b ≤ c :=
  begin apply subLeIfAddGe; apply Equiv.transport (λ w, a ≤ w); apply T.τ.addComm; assumption end

  hott def addLeIfSubGe (T : Overring) [orfield T] {a b c : T.carrier} (p : a ≤ b - c) : a + c ≤ b :=
  begin
    apply leOverSubRight T (a + c) b (-c); apply Equiv.transport (λ w, w ≤ b - c);
    apply @Group.cancelRight T.τ⁺; assumption
  end

  hott def subGeIfAddLe (T : Overring) [orfield T] {a b c : T.carrier} (p : a + c ≤ b) : a ≤ b - c :=
  begin
    apply leOverSubRight T a (b - c) c; apply Equiv.transport (λ w, a + c ≤ w);
    apply @Group.cancelLeft T.τ⁺; assumption
  end

  hott def subGeIfAddLeRev (T : Overring) [orfield T] {a b c : T.carrier} (p : c + a ≤ b) : a ≤ b - c :=
  begin apply subGeIfAddLe; apply Equiv.transport (λ w, w ≤ b); apply T.τ.addComm; assumption end

  hott def addLeIfSubGeRev (T : Overring) [orfield T] {a b c : T.carrier} (p : a ≤ b - c) : c + a ≤ b :=
  begin apply Equiv.transport (λ w, w ≤ b); apply T.τ.addComm; apply addLeIfSubGe; assumption end

  hott def subGeZeroIfLe (T : Overring) [orfield T] {a b : T.carrier} (p : a ≤ b) : 0 ≤ b - a :=
  begin apply subGeIfAddLe; apply Equiv.transport (λ w, w ≤ b); symmetry; apply T.τ⁺.oneMul; assumption end

  hott def leIfSubGeZero (T : Overring) [orfield T] {a b : T.carrier} (p : 0 ≤ b - a) : a ≤ b :=
  begin apply Equiv.transport (λ w, w ≤ b); apply T.τ⁺.oneMul; apply addLeIfSubGe T p end

  hott def ltOverAdd (T : Overring) [orfield T] (a b c : T.carrier) (p : a < b) : a + c < b + c :=
  begin
    apply Prod.mk; intro q; apply p.1;
    apply Equiv.transportconst; apply Equiv.bimap;
    symmetry; apply @Group.cancelRight T.τ⁺ a c;
    symmetry; apply @Group.cancelRight T.τ⁺ b c;
    apply ap (λ x, x - c) q; apply orfield.leOverAdd; exact p.2
  end

  hott def ltOverAddLeft (T : Overring) [orfield T] (a b c : T.carrier) (p : a < b) : c + a < c + b :=
  begin apply Equiv.transportconst; apply Equiv.bimap <;> apply T.τ.addComm; apply ltOverAdd; exact p end

  hott def strictIneqTransRight (T : Overring) [orfield T] {a b c : T.carrier} (p : a < b) (q : b ≤ c) : a < c :=
  begin
    apply Prod.mk; intro r; apply p.1; apply @antisymmetric.asymm T.κ; apply p.2;
    apply Equiv.transport (T.ρ b); exact Id.inv r; assumption;
    apply @transitive.trans T.κ; exact p.2; exact q
  end

  hott def strictIneqTransLeft (T : Overring) [orfield T] {a b c : T.carrier} (p : a ≤ b) (q : b < c) : a < c :=
  begin
    apply Prod.mk; intro r; apply q.1; apply @antisymmetric.asymm T.κ; apply q.2;
    apply Equiv.transport (λ x, T.ρ x b); exact r; assumption;
    apply @transitive.trans T.κ; exact p; exact q.2
  end

  hott def strictIneqTrans (T : Overring) [orfield T] {a b c : T.carrier} (p : a < b) (q : b < c) : a < c :=
  strictIneqTransLeft T p.2 q

  hott def strictIneqAdd (T : Overring) [orfield T] {a b c d : T.carrier} (p : a < b) (q : c < d) : a + c < b + d :=
  begin apply strictIneqTrans; apply ltOverAdd; exact p; apply ltOverAddLeft; exact q end

  hott def strictIneqAddLeft (T : Overring) [orfield T] {a b c d : T.carrier} (p : a ≤ b) (q : c < d) : a + c < b + d :=
  begin apply strictIneqTransLeft; apply orfield.leOverAdd; exact p; apply ltOverAddLeft; exact q end

  hott def strictIneqAddRight (T : Overring) [orfield T] {a b c d : T.carrier} (p : a < b) (q : c ≤ d) : a + c < b + d :=
  begin apply strictIneqTransRight; apply ltOverAdd; exact p; apply leOverAddLeft; exact q end

  hott def minusInvSign (T : Overring) [orfield T] (a b : T.carrier) (p : a ≤ b) : -a ≥ -b :=
  begin
    fapply GroundZero.HITs.Merely.rec _ _ (@connected.total T.κ _ _ _);
    change T.carrier; exact -b; change T.carrier; exact -a; apply T.κ.prop;
    { intro ih; induction ih; assumption;
      match @Classical.lem _ (a = b) (T.hset _ _) with | Sum.inl r₁ => _ | Sum.inr r₂ => _;
      apply eqImplReflRel T.κ; symmetry; apply ap T.τ.neg r₁;
      apply explode; apply (_ : T.σ 0 0).1; reflexivity;
      apply Equiv.transportconst; apply Equiv.bimap;
      apply @Group.mulRightInv T.τ⁺; exact a;
      apply @Group.mulRightInv T.τ⁺; exact b;
      apply strictIneqAddRight; exact (r₂, p);
      assumption }
  end

  hott def invMinusSign (T : Overring) [orfield T] (a b : T.carrier) (p : -a ≤ -b) : a ≥ b :=
  begin apply Equiv.transportconst; apply Equiv.bimap <;> apply @Group.invInv T.τ⁺; apply minusInvSign; assumption end

  hott def geIfMinusLe (T : Overring) [orfield T] (a b : T.carrier) (p : -a ≤ b) : a ≥ -b :=
  begin
    apply invMinusSign; apply Equiv.transport (λ c, -a ≤ c);
    symmetry; apply @Group.invInv T.τ⁺; assumption
  end

  hott def geMinusIfLe (T : Overring) [orfield T] (a b : T.carrier) (p : a ≤ -b) : -a ≥ b :=
  begin
    apply invMinusSign; apply Equiv.transport (λ c, c ≤ -b);
    symmetry; apply @Group.invInv T.τ⁺; assumption
  end

  -- or complete at top
  class complete (Γ : Orgraph) :=
  (sup : Π (φ : Γ.subset), φ.inh → majorized φ → exactness (Majorant φ))

  -- or complete at bottom
  class cocomplete (Γ : Orgraph) :=
  (inf : Π (φ : Γ.subset), φ.inh → minorized φ → coexactness (Minorant φ))

  hott def supremumUniqueness {Γ : Orgraph} [total Γ] (φ : Γ.subset) : prop (Σ M, exact (Majorant φ) M) :=
  begin
    intros p q; apply Sigma.prod; apply Structures.productProp;
    apply Ens.prop; apply piProp; intro; apply piProp; intro; apply Γ.prop; apply antisymmetric.asymm;
    { apply p.2.2; apply q.2.1 }; { apply q.2.2; apply p.2.1 }
  end

  hott def infimumUniqueness {Γ : Orgraph} [total Γ] (φ : Γ.subset) : prop (Σ M, coexact (Minorant φ) M) :=
  begin
    intros p q; apply Sigma.prod; apply Structures.productProp;
    apply Ens.prop; apply piProp; intro; apply piProp; intro; apply Γ.prop; apply antisymmetric.asymm;
    { apply q.2.2; apply p.2.1 }; { apply p.2.2; apply q.2.1 }
  end

  hott def Neg {T : Prering} (φ : T.subset) : T.subset :=
  ⟨λ a, T.neg a ∈ φ, λ a, Ens.prop (T.neg a) φ⟩

  hott def Neg.inh {T : Prering} [ring T] {φ : T.subset} : φ.inh → (Neg φ).inh :=
  begin
    apply HITs.Merely.lift; intro ⟨x, H⟩;
    existsi T.neg x; apply Equiv.transport (· ∈ φ);
    symmetry; apply @Group.invInv T⁺; assumption
  end

  hott def Neg.negInh {T : Prering} {φ : T.subset} : (Neg φ).inh → φ.inh :=
  begin apply HITs.Merely.lift; intro ⟨x, H⟩; existsi T.neg x; apply H end

  hott def Neg.majorant {T : Overring} [orfield T] {φ : T.subset} (x : T.carrier) :
    @minorant T.κ φ x → @majorant T.κ (@Neg T.τ φ) (T.τ.neg x) :=
  begin
    intros H x p; apply invMinusSign;
    apply Equiv.transport (λ y, T.ρ y (T.τ.neg x)); symmetry;
    apply @Group.invInv T.τ⁺; apply H; exact p
  end

  hott def Neg.negMajorant {T : Overring} [orfield T] {φ : T.subset} (x : T.carrier) :
    @minorant T.κ (@Neg T.τ φ) x → @Algebra.majorant T.κ φ (T.τ.neg x) :=
  begin
    intro H; intros x p; apply invMinusSign;
    apply Equiv.transport (λ y, T.ρ y (T.τ.neg x)); symmetry;
    apply @Group.invInv T.τ⁺; apply H; apply Equiv.transport (· ∈ φ);
    symmetry; apply @Group.invInv T.τ⁺; exact p
  end

  hott def Neg.minorant {T : Overring} [orfield T] {φ : T.subset} (x : T.carrier) :
    @Algebra.majorant T.κ φ x → @Algebra.minorant T.κ (@Neg T.τ φ) (T.τ.neg x) :=
  begin
    intro H x p; apply invMinusSign;
    apply Equiv.transport (T.ρ (T.τ.neg x)); symmetry;
    apply @Group.invInv T.τ⁺; apply H; exact p
  end

  hott def Neg.negMinorant {T : Overring} [orfield T] {φ : T.subset} (x : T.carrier) :
    @Algebra.majorant T.κ (@Neg T.τ φ) x → @Algebra.minorant T.κ φ (T.τ.neg x) :=
  begin
    intro H x p; apply invMinusSign;
    apply Equiv.transport (T.ρ (T.τ.neg x)); symmetry;
    apply @Group.invInv T.τ⁺; apply H; apply Equiv.transport (· ∈ φ);
    symmetry; apply @Group.invInv T.τ⁺; exact p
  end

  hott def Neg.majorized {T : Overring} [orfield T] {φ : T.subset} : @Algebra.minorized T.κ φ → @Algebra.majorized T.κ (@Neg T.τ φ) :=
  begin apply HITs.Merely.lift; intro H; existsi T.τ.neg H.1; apply Neg.majorant; exact H.2 end

  hott def Neg.minorized {T : Overring} [orfield T] {φ : T.subset} : @Algebra.majorized T.κ φ → @Algebra.minorized T.κ (@Neg T.τ φ) :=
  begin apply HITs.Merely.lift; intro H; existsi T.τ.neg H.1; apply Neg.minorant; exact H.2 end

  section
    variable {T : Overring} [orfield T] (φ : T.subset)

    hott def negMinorantEqMajorantNeg.forward : @Neg T.τ (@Minorant T.κ φ) ⊆ @Majorant T.κ (@Neg T.τ φ) :=
    begin intros x H y G; apply invMinusSign; apply H; assumption end

    hott def negMinorantEqMajorantNeg.backward : @Majorant T.κ (@Neg T.τ φ) ⊆ @Neg T.τ (@Minorant T.κ φ) :=
    begin
      intros x H y G; apply invMinusSign; apply Equiv.transport;
      symmetry; apply @Group.invInv T.τ⁺; apply H; apply Equiv.transport (· ∈ φ);
      symmetry; apply @Group.invInv T.τ⁺; assumption
    end

    hott def negMinorantEqMajorantNeg : @Neg T.τ (@Minorant T.κ φ) = @Majorant T.κ (@Neg T.τ φ) :=
    begin
      apply Ens.ssubset.asymm <;> intros x H;
      apply negMinorantEqMajorantNeg.forward; assumption;
      apply negMinorantEqMajorantNeg.backward; assumption
    end

    hott def negMajorantEqMinorantNeg.forward : @Neg T.τ (@Majorant T.κ φ) ⊆ @Minorant T.κ (@Neg T.τ φ) :=
    begin intros x H y G; apply invMinusSign; apply H; assumption end

    hott def negMajorantEqMinorantNeg.backward : @Minorant T.κ (@Neg T.τ φ) ⊆ @Neg T.τ (@Majorant T.κ φ) :=
    begin
      intros x H y G; apply invMinusSign; apply Equiv.transport (λ z, z ≤ T.τ.neg y);
      symmetry; apply @Group.invInv T.τ⁺; apply H; apply Equiv.transport (· ∈ φ);
      symmetry; apply @Group.invInv T.τ⁺; assumption
    end

    hott def negMajorantEqMinorantNeg : @Neg T.τ (@Majorant T.κ φ) = @Minorant T.κ (@Neg T.τ φ) :=
    begin
      apply Ens.ssubset.asymm <;> intros x H;
      apply negMajorantEqMinorantNeg.forward; assumption;
      apply negMajorantEqMinorantNeg.backward; assumption
    end
  end

  hott def orfieldCocompleteIfComplete {T : Overring} [orfield T] (H : complete T.κ) : cocomplete T.κ :=
  begin
    constructor; intros φ p q; fapply HITs.Merely.rec _ _ (@complete.sup T.κ _ _ _ _);
    change T.τ.subset; exact Neg φ; apply HITs.Merely.uniq;
    intro r; apply HITs.Merely.elem; existsi T.τ.neg r.1; apply Prod.mk;
    apply negMinorantEqMajorantNeg.backward; exact r.2.1;
    apply Neg.negMajorant; apply Equiv.transport (λ φ, minorant φ r.1);
    symmetry; apply negMinorantEqMajorantNeg; exact r.2.2;
    apply Neg.inh; assumption; apply Neg.majorized; assumption
  end

  hott def orfieldCompleteIfCocomplete {T : Overring} [orfield T] (H : cocomplete T.κ) : complete T.κ :=
  begin
    constructor; intros φ p q; fapply HITs.Merely.rec _ _ (@cocomplete.inf T.κ _ _ _ _);
    change T.τ.subset; exact Neg φ; apply HITs.Merely.uniq;
    intro r; apply HITs.Merely.elem; existsi T.τ.neg r.1; apply Prod.mk;
    apply negMajorantEqMinorantNeg.backward; exact r.2.1;
    apply Neg.negMinorant; apply Equiv.transport (λ φ, majorant φ r.1);
    symmetry; apply negMajorantEqMinorantNeg; exact r.2.2;
    apply Neg.inh; assumption; apply Neg.minorized; assumption
  end

  class dedekind (T : Overring) extends orfield T, complete T.κ

  hott def gtIfGtZero (T : Overring) [orfield T] {a b : T.carrier} (H : 0 ≤ b - a) : a ≤ b :=
  begin apply Equiv.transport (λ c, c ≤ b); apply T.τ⁺.oneMul; apply addLeIfSubGe; exact H end
end GroundZero.Algebra
