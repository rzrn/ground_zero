import GroundZero.Types.Ens

open GroundZero.Types GroundZero.Structures
open GroundZero.HITs.Interval (happly)
open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero

/-
  Magma, semigroup, monoid, group, abelian group.
  * HoTT 6.11
-/

namespace GroundZero.Algebra
  universe u v u' v' w

  hott definition zeroeqv {A : Type u} (H : hset A) : 0-Type :=
  ⟨A, zeroEqvSet.left H⟩

  hott definition algop (deg : ℕ) (A : Type u) :=
  vect A deg → A

  hott definition algrel (deg : ℕ) (A : Type u) :=
  vect A deg → Prop

  section
    variable {ι : Type u} {υ : Type v} (deg : ι + υ → ℕ)

    hott definition Algebra (A : Type w) :=
    (Π i, algop  (deg (Sum.inl i)) A) × -- Algebraic operations
    (Π i, algrel (deg (Sum.inr i)) A)   -- relations

    hott definition Alg := Σ (A : 0-Type), Algebra deg A.1

    hott definition Algebra.hset {A : Type w} (H : hset A) : hset (Algebra deg A) :=
    begin
      apply prodHset;
      { apply piHset; intro; apply piHset; intro; apply H };
      { apply piHset; intro; apply piHset; intro; apply Theorems.Equiv.propsetIsSet }
    end
  end

  section
    variable {ι : Type u} {υ : Type v} {deg : ι + υ → ℕ}

    section
      variable (A : Alg deg)

      hott abbreviation Alg.carrier := A.1.1
      hott abbreviation Alg.op      := A.2.1
      hott abbreviation Alg.rel     := A.2.2
      hott abbreviation Alg.zero    := A.1
      hott abbreviation Alg.subset  := Ens A.carrier
      hott abbreviation Alg.univ    := Ens.univ A.carrier

      hott definition Alg.hset : hset A.carrier :=
      zeroEqvSet.forward A.1.2
    end

    hott definition mapping (Γ Λ : Alg deg) :=
    Γ.carrier → Λ.carrier

    infix:51 " →ᴬ " => mapping

    hott definition respects {Γ Λ : Alg deg} (f : Γ.carrier → Λ.carrier) :=
    (Π i v, f (Γ.op i v) = Λ.op i (v.map f)) ×
    (Π i v, Γ.rel i v = Λ.rel i (v.map f))

    hott definition respects.prop {Γ Λ : Alg deg}
      (f : Γ →ᴬ Λ) : prop (respects f) :=
    begin
      apply productProp <;> apply piProp <;> intro <;> apply piProp <;> intro;
      apply Alg.hset; apply Theorems.Equiv.propsetIsSet
    end

    hott definition respects.comp {Γ Λ Δ : Alg deg} {f : Γ →ᴬ Λ} {g : Λ →ᴬ Δ} :
      respects g → respects f → respects (g ∘ f) :=
    begin
      intros p q; apply Prod.mk <;> intros;
      { transitivity; apply ap g; apply q.1;
        transitivity; apply p.1;
        apply ap; apply vect.comp };
      { transitivity; apply q.2;
        transitivity; apply p.2;
        apply ap; apply vect.comp }
    end

    hott definition Hom (Γ Λ : Alg deg) :=
    Σ (φ : Γ →ᴬ Λ), respects φ

    hott definition Hom.ap {Γ Λ : Alg deg} : Hom Γ Λ → (Γ →ᴬ Λ) := Sigma.fst

    hott definition Hom.comp {Γ Λ Δ : Alg deg} (g : Hom Λ Δ) (f : Hom Γ Λ) : Hom Γ Δ :=
    ⟨g.1 ∘ f.1, respects.comp g.2 f.2⟩

    infix:60 " ⋅ " => Hom.comp

    hott definition Hom.id (Γ : Alg deg) : Hom Γ Γ :=
    begin
      existsi Proto.idfun; apply Prod.mk <;> intros i v <;> symmetry;
      apply Id.ap (Γ.op i);  apply vect.id;
      apply Id.ap (Γ.rel i); apply vect.id
    end

    hott definition Hom.funext {Γ Λ : Alg deg} :
      Π {f g : Hom Γ Λ}, f.ap ~ g.ap → f = g :=
    begin
      intro ⟨f, F⟩ ⟨g, G⟩ p; fapply Sigma.prod;
      apply Theorems.funext; exact p; apply respects.prop
    end

    hott definition idhom {Γ Λ : Alg deg} {f g : Hom Γ Λ} : f = g → f.ap ~ g.ap :=
    begin intro p; induction p; apply Homotopy.id end

    hott definition Hom.hset {Γ Λ : Alg deg} : hset (Hom Γ Λ) :=
    begin
      fapply hsetRespectsSigma;
      { apply piHset; intro; apply Λ.hset };
      { intro f; apply propIsSet; apply respects.prop }
    end

    hott definition Iso (Γ Λ : Alg deg) :=
    Σ (φ : Γ →ᴬ Λ), respects φ × biinv φ

    notation:51 A " ≅ " B => Iso A.1 B.1

    section
      variable {Γ Λ : Alg deg}

      hott definition Iso.ap : Iso Γ Λ → (Γ →ᴬ Λ) := Sigma.fst

      hott definition Iso.eqv : Iso Γ Λ → Γ.carrier ≃ Λ.carrier :=
      λ φ, ⟨φ.ap, φ.2.2⟩

      hott definition Iso.ofEquiv : Π (φ : Γ.carrier ≃ Λ.carrier), respects φ.1 → Iso Γ Λ :=
      λ ⟨φ, q⟩ p, ⟨φ, (p, q)⟩

      hott definition Iso.ofHom : Π (φ : Hom Γ Λ), biinv φ.ap → Iso Γ Λ :=
      λ ⟨φ, p⟩ q, ⟨φ, (p, q)⟩

      hott lemma Iso.ext {φ ψ : Iso Γ Λ} : φ.ap ~ ψ.ap → φ = ψ :=
      begin
        intro p; fapply Sigma.prod; apply Theorems.funext p;
        apply productProp; apply respects.prop;
        apply Theorems.Equiv.biinvProp
      end

      hott lemma Iso.eqIffEqEqv (φ ψ : Iso Γ Λ) : φ.eqv = ψ.eqv → φ = ψ :=
      begin intro p; apply Iso.ext; apply happly; apply Id.ap Sigma.fst p end

      hott definition Iso.hom (φ : Iso Γ Λ) : Hom Γ Λ :=
      ⟨φ.ap, φ.2.1⟩

      hott lemma Iso.hset : hset (Iso Γ Λ) :=
      begin
        apply hsetRespectsSigma;
        { apply piHset; intro; apply Λ.hset };
        { intro x; apply propIsSet;
          apply productProp; apply respects.prop;
          apply Theorems.Equiv.biinvProp }
      end
    end

    hott definition Iso.refl (Γ : Alg deg) : Iso Γ Γ :=
    begin
      fapply Iso.ofEquiv; reflexivity; apply Prod.mk <;> intros i v;
      { apply Id.ap (Γ.op i);  symmetry; apply vect.id };
      { apply Id.ap (Γ.rel i); symmetry; apply vect.id }
    end

    hott definition Iso.symm {Γ Λ : Alg deg} : Iso Γ Λ → Iso Λ Γ :=
    begin
      intro f; have μ := Equiv.forwardLeft f.eqv;
      existsi f.eqv.left; apply Prod.mk;
      { apply Prod.mk <;> intros i v;
        { symmetry; transitivity; { symmetry; apply f.eqv.leftForward };
          transitivity; apply Id.ap f.eqv.left; apply f.2.1.1;
          apply Id.ap (f.eqv.left ∘ Λ.op i); transitivity;
          apply vect.comp; apply vect.idfunc; apply μ };
        { transitivity; apply Id.ap (Λ.rel i);
          transitivity; symmetry; apply vect.idfunc (f.ap ∘ f.eqv.left);
          apply μ; symmetry; apply vect.comp; symmetry; apply f.2.1.2 } };
      { apply Prod.mk <;> existsi f.ap; apply μ; apply f.eqv.leftForward }
    end

    hott definition Iso.trans {Γ Λ Δ : Alg deg} : Iso Γ Λ → Iso Λ Δ → Iso Γ Δ :=
    begin
      intros f g; existsi g.ap ∘ f.ap; apply Prod.mk;
      { apply respects.comp; exact g.2.1; exact f.2.1 };
      { apply Equiv.biinvTrans; exact f.2.2; exact g.2.2 }
    end

    hott instance : @Reflexive  (Alg deg) Iso := ⟨Iso.refl⟩
    hott instance : @Symmetric  (Alg deg) Iso := ⟨@Iso.symm _ _ _⟩
    hott instance : @Transitive (Alg deg) Iso := ⟨@Iso.trans _ _ _⟩

    hott lemma Algebra.ext {A B : Type w} (p : A = B) :
      Π (Γ : Algebra deg A) (Λ : Algebra deg B),
        (Π i, Γ.1 i =[p] Λ.1 i) → (Π i, Γ.2 i =[p] Λ.2 i) → Γ =[p] Λ :=
    begin
      intro ⟨Γ₁, Γ₂⟩ ⟨Λ₁, Λ₂⟩ ε δ; induction p;
      apply Product.prod <;> apply Theorems.funext <;>
      intro; apply ε; apply δ
    end

    hott lemma transportOverZeroPath : Π {A B : 0-Type} (C : Type u → Type v) (p : A.1 = B.1) (u : C A.1),
      transport (C ∘ Sigma.fst) (zeroPath p) u = @transport (Type u) C A.1 B.1 p u :=
    begin
      intro ⟨A, F⟩ ⟨B, G⟩ C (p : A = B) u; induction p;
      have ρ : F = G := ntypeIsProp 0 F G; induction ρ;
      transitivity; apply Equiv.transportToTransportconst; transitivity;
      apply Id.ap (λ p, transportconst (Id.ap (C ∘ Sigma.fst) p) u);
      apply zeroPathRefl; reflexivity
    end

    hott theorem Alg.ext {Γ Λ : Alg deg} (p : Γ.carrier = Λ.carrier)
      (μ : Π i, Γ.op i  =[algop  (deg (Sum.inl i)), p] Λ.op i)
      (η : Π i, Γ.rel i =[algrel (deg (Sum.inr i)), p] Λ.rel i) : Γ = Λ :=
    begin
      fapply Sigma.prod; apply zeroPath; exact p;
      transitivity; apply transportOverZeroPath (Algebra deg) p;
      apply Algebra.ext <;> assumption
    end

    hott lemma equivCompSubst {A B : Type u} (φ : A ≃ B) :
      φ.1 ∘ transportconst (ua φ)⁻¹ = id :=
    begin
      apply Theorems.funext; intro x;
      transitivity; apply Id.ap φ.1;
      apply uaβrev; apply Equiv.forwardLeft
    end

    hott lemma uaPreservesOp {Γ Λ : Alg deg} :
      Π (φ : Iso Γ Λ) (i : ι), Γ.op i =[ua φ.eqv] Λ.op i :=
    begin
      intro ⟨φ, (p, q)⟩ i; apply Id.trans;
      apply transportOverFunctor (λ A, vect A (deg (Sum.inl i))) id;
      apply Theorems.funext; intro v;
      transitivity; apply uaβ;
      transitivity; apply p.1; apply Id.ap;
      transitivity; apply vect.subst;
      transitivity; apply Id.ap (vect.map · v);
      apply equivCompSubst ⟨φ, q⟩; apply vect.id
    end

    hott lemma uaPreservesRel {Γ Λ : Alg deg} :
      Π (φ : Iso Γ Λ) (i : υ), Γ.rel i =[algrel (deg (Sum.inr i)), ua φ.eqv] Λ.rel i :=
    begin
      intro ⟨φ, (p, q)⟩ i; apply Id.trans;
      apply transportOverFunctor (λ A, vect A (deg (Sum.inr i))) (λ _, Prop);
      apply Theorems.funext; intro v;
      transitivity; apply ap (subst (ua ⟨φ, q⟩));
      transitivity; apply p.2; apply Id.ap (Λ.rel i);
      transitivity; apply vect.subst;
      transitivity; apply Id.ap (vect.map · v);
      apply equivCompSubst ⟨φ, q⟩; apply vect.id; change transport _ _ _ = _;
      transitivity; apply Equiv.transportToTransportconst;
      transitivity; apply Id.ap (transportconst · (Λ.rel i v));
      apply constmap; reflexivity
    end

    hott theorem Alg.ua {Γ Λ : Alg deg} (φ : Iso Γ Λ) : Γ = Λ :=
    Alg.ext (GroundZero.ua φ.eqv) (uaPreservesOp φ) (uaPreservesRel φ)

    hott lemma Alg.eqcar {Γ Λ : Alg deg} : Γ = Λ → Γ.carrier = Λ.carrier :=
    λ p, @Id.ap (0-Type) (Type _) _ _ Sigma.fst (Id.ap Sigma.fst p)

    hott lemma Alg.uaext : Π {Γ Λ : Alg deg} (φ : Iso Γ Λ), GroundZero.ua φ.eqv = Alg.eqcar (Alg.ua φ) :=
    begin
      intro ⟨⟨A, f⟩, (Γ₁, Γ₂)⟩ ⟨⟨B, g⟩, (Λ₁, Λ₂)⟩ φ;
      symmetry; change Id.ap _ _ = _; transitivity; apply Id.ap;
      apply Sigma.mapFstOverProd; apply Sigma.mapFstOverProd
    end

    hott lemma Alg.inj {Γ Λ : Alg deg} {φ ψ : Iso Γ Λ} (p : Alg.ua φ = Alg.ua ψ) : φ = ψ :=
    begin
      apply Iso.eqIffEqEqv; transitivity; symmetry; apply idtoeqvua;
      transitivity; apply Id.ap; apply Alg.uaext;
      transitivity; apply Id.ap (Equiv.idtoeqv ∘ Alg.eqcar);
      exact p; transitivity; apply Id.ap Equiv.idtoeqv;
      symmetry; apply Alg.uaext; apply idtoeqvua
    end

    hott definition Alg.id {Γ Λ : Alg deg} (p : Γ = Λ) : Iso Γ Λ :=
    begin induction p; reflexivity end

    hott lemma transportOverProd {A : Type u} {B : A → Type v} {u v : Sigma B}
      (p₁ p₂ : u.1 = v.1) (q : transport B p₁ u.2 = v.2) (ε : p₁ = p₂) :
      Sigma.prod p₁ q = Sigma.prod p₂ (@transport (u.1 = v.1)
        (λ p, transport B p u.2 = v.2) p₁ p₂ ε q) :=
    begin induction ε; reflexivity end

    hott lemma Alg.uaβrefl {Γ : Alg deg} : Alg.ua (Iso.refl Γ) = Id.refl :=
    begin
      change Alg.ext _ _ _ = _;
      change Sigma.prod _ _ = _;
      transitivity; apply transportOverProd;
      transitivity; transitivity; apply transportOverProd;
      apply uaidp; apply Id.ap (Sigma.prod Id.refl);
      change _ = Id.refl; apply propIsSet;
      apply ntypeIsProp; apply Sigma.prodRefl;
      transitivity; apply Id.ap (Sigma.prod Id.refl);
      change _ = Id.refl; apply Algebra.hset;
      apply zeroEqvSet.forward Γ.1.2;
      apply Sigma.prodRefl
    end

    hott corollary Alg.rinv {Γ Λ : Alg deg} (p : Γ = Λ) : Alg.ua (Alg.id p) = p :=
    begin induction p; apply Alg.uaβrefl end

    hott corollary Alg.linv {Γ Λ : Alg deg} {φ : Iso Γ Λ} : Alg.id (Alg.ua φ) = φ :=
    begin apply Alg.inj; apply Alg.rinv end

    /--
      Related:

      “Universal Algebra in HoTT”
      Andreas Lynge and Bas Spitters
      * https://github.com/andreaslyn/hott-classes
      * http://www.ii.uib.no/~bezem/abstracts/TYPES_2019_paper_7

      “Isomorphism is equality”
      Thierry Coquand, Nils Anders Danielsson
      * https://www.sciencedirect.com/science/article/pii/S0019357713000694

      “Universal Algebra in UniMath”
      Gianluca Amato, Marco Maggesi, Maurizio Parton, Cosimo Perini Brogi
      * https://hott-uf.github.io/2020/HoTTUF_2020_paper_13.pdf

      “Formalization of universal Algebra in Agda”
      Emmanuel Gunther, Alejandro Gadea, and Miguel Pagano
      * https://www.sciencedirect.com/science/article/pii/S1571066118300768

      “Universal Algebra in type theory”
      Venanzio Capretta
      * https://link.springer.com/chapter/10.1007/3-540-48256-3_10
    -/
    hott theorem Alg.univalence {Γ Λ : Alg deg} : Iso Γ Λ ≃ (Γ = Λ) :=
    begin existsi Alg.ua; apply Prod.mk <;> existsi Alg.id; apply Alg.linv; apply Alg.rinv end
  end

  hott definition Magma : Type (u + 1) :=
  @Alg.{0, 0, u, 0} 𝟏 ⊥ (λ _, 2)

  open GroundZero.Proto (explode)

  namespace Magma
    hott definition intro {A : Type u} (H : hset A) (φ : A → A → A) : Magma :=
    ⟨zeroeqv H, (λ _ (a, b, _), φ a b, explode)⟩

    hott definition φ (M : Magma) : M.carrier → M.carrier → M.carrier :=
    λ x y, M.op ★ (x, y, ★)

    hott definition isCommutative (M : Magma) :=
    Π a b, M.φ a b = M.φ b a

    hott definition isAssociative (M : Magma) :=
    Π a b c, M.φ (M.φ a b) c = M.φ a (M.φ b c)

    hott definition isLeftUnital (M : Magma) :=
    Σ e, Π a, M.φ e a = a

    hott definition isRightUnital (M : Magma) :=
    Σ e, Π a, M.φ a e = a

    hott definition isUnital (M : Magma) :=
    Σ e, Π a, M.φ e a = a × M.φ a e = a

    hott definition isLeftInvertible (M : Magma) (e : M.carrier) :=
    Σ (ι : M →ᴬ M), Π a, M.φ (ι a) a = e

    hott definition isRightInvertible (M : Magma) (e : M.carrier) :=
    Σ (ι : M →ᴬ M), Π a, M.φ a (ι a) = e

    hott definition isGroup (M : Magma) :=
    M.isAssociative × Σ (w : M.isLeftUnital), M.isLeftInvertible w.1

    hott lemma unitalProp (M : Magma) : prop M.isUnital :=
    begin
      intro w₁ w₂; fapply Sigma.prod; transitivity;
      symmetry; apply (w₂.2 w₁.1).1; apply (w₁.2 _).2;
      apply piProp; intro; apply productProp <;> apply M.hset
    end

    hott lemma assocProp (M : Magma) : prop M.isAssociative :=
    by repeat (first | apply M.hset | apply piProp; intro)
  end Magma

  namespace Premonoid
    hott definition signature : 𝟐 + ⊥ → ℕ
    | Sum.inl false => 0
    | Sum.inl true  => 2
    | Sum.inr h     => explode h
  end Premonoid

  hott definition Premonoid : Type (u + 1) :=
  Alg.{0, 0, u, 0} Premonoid.signature

  namespace Premonoid
    hott definition e (M : Premonoid) : M.carrier :=
    M.op false ★

    hott definition φ (M : Premonoid) : M.carrier → M.carrier → M.carrier :=
    λ x y, M.op true (x, y, ★)

    hott definition magma (M : Premonoid) : Magma :=
    begin
      existsi M.1; apply Prod.mk;
      { intro; exact M.op true };
      { apply explode }
    end
  end Premonoid

  namespace Pregroup
    inductive Arity : Type
    | nullary | unary | binary
    open Arity

    hott definition signature : Arity + ⊥ → ℕ
    | Sum.inl nullary => 0
    | Sum.inl unary   => 1
    | Sum.inl binary  => 2
    | Sum.inr h       => explode h
  end Pregroup

  hott definition Pregroup : Type (u + 1) :=
  Alg.{0, 0, u, 0} Pregroup.signature

  namespace Pregroup
    hott definition intro {A : Type u} (H : hset A)
      (φ : A → A → A) (ι : A → A) (e : A) : Pregroup :=
    ⟨zeroeqv H, (λ | Arity.nullary => λ _, e
                   | Arity.unary   => λ (a, _), ι a
                   | Arity.binary  => λ (a, b, _), φ a b,
                 λ i, explode i)⟩

    hott definition e (G : Pregroup) : G.carrier :=
    G.op Arity.nullary ★

    hott definition ι (G : Pregroup) : G →ᴬ G :=
    λ x, G.op Arity.unary (x, ★)

    hott definition φ (G : Pregroup) : G.carrier → G.carrier → G.carrier :=
    λ x y, G.op Arity.binary (x, y, ★)

    hott definition magma (G : Pregroup) : Magma :=
    begin
      existsi G.1; apply Prod.mk;
      { intro; exact G.op Arity.binary };
      { apply explode }
    end

    hott definition premonoid (G : Pregroup) : Premonoid :=
    begin
      existsi G.1; apply Prod.mk;
      { exact λ | false => G.op Arity.nullary
                | true  => G.op Arity.binary };
      { intro x; apply explode x }
    end

    variable (G : Pregroup)

    hott definition isAssociative :=
    Π a b c, G.φ (G.φ a b) c = G.φ a (G.φ b c)

    hott definition isLeftUnital  := Π a, G.φ G.e a = a
    hott definition isRightUnital := Π a, G.φ a G.e = a

    hott definition isLeftInvertible := Π a, G.φ (G.ι a) a = G.e

    hott definition isCommutative := Π a b, G.φ a b = G.φ b a

    hott definition isGroup := G.isAssociative × G.isLeftUnital × G.isRightUnital × G.isLeftInvertible

    hott definition isAbelian := G.isGroup × G.isCommutative
  end Pregroup

  hott def Group := Σ (M : Magma), M.isGroup

  namespace Group
    variable (G : Group)

    hott abbreviation carrier := G.1.carrier
    hott abbreviation subset  := G.1.subset
    hott abbreviation hset    := G.1.hset
    hott abbreviation magma   := G.1

    hott abbreviation φ := G.1.φ
    hott abbreviation e := G.2.2.1.1
    hott abbreviation ι := G.2.2.2.1

    hott definition mulAssoc : Π a b c, G.φ (G.φ a b) c = G.φ a (G.φ b c) := G.2.1

    hott definition oneMul (a : G.carrier) : G.φ G.e a = a := G.2.2.1.2 a

    hott definition mulLeftInv : Π a, G.φ (G.ι a) a = G.e := G.2.2.2.2

    hott definition isCommutative := G.1.isCommutative

    hott definition Hom (G H : Group) := Algebra.Hom G.1 H.1

    hott definition intro {A : Type u} (H : Structures.hset A)
      (φ : A → A → A) (ι : A → A) (e : A)
      (α : Π a b c, φ (φ a b) c = φ a (φ b c))
      (β : Π a, φ e a = a) (γ : Π a, φ (ι a) a = e) : Group :=
    ⟨Magma.intro H φ, (α, ⟨⟨e, β⟩, ⟨ι, γ⟩⟩)⟩
  end Group

  hott definition Abelian := Σ (M : Magma), M.isGroup × M.isCommutative

  namespace Abelian
    variable (G : Abelian)

    hott abbreviation carrier := G.1.carrier
    hott abbreviation subset  := G.1.subset
    hott abbreviation hset    := G.1.hset
    hott abbreviation magma   := G.1

    hott definition group : Group := ⟨G.1, G.2.1⟩

    hott abbreviation φ := G.1.φ
    hott abbreviation e := G.2.1.2.1.1
    hott abbreviation ι := G.2.1.2.2.1

    hott definition mulAssoc : Π a b c, G.φ (G.φ a b) c = G.φ a (G.φ b c) := G.2.1.1

    hott definition oneMul (a : G.carrier) : G.φ G.e a = a := G.2.1.2.1.2 a

    hott definition mulLeftInv : Π a, G.φ (G.ι a) a = G.e := G.2.1.2.2.2

    hott definition mulComm : Π a b, G.φ a b = G.φ b a := G.2.2

    hott definition Hom (G H : Abelian) := Algebra.Hom G.1 H.1

    hott definition intro {A : Type u} (H : Structures.hset A)
      (φ : A → A → A) (ι : A → A) (e : A)
      (α : Π a b c, φ (φ a b) c = φ a (φ b c))
      (β : Π a, φ e a = a) (γ : Π a, φ (ι a) a = e)
      (δ : Π a b, φ a b = φ b a) : Abelian :=
    ⟨Magma.intro H φ, ((α, ⟨⟨e, β⟩, ⟨ι, γ⟩⟩), δ)⟩
  end Abelian
end GroundZero.Algebra
