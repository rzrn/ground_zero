import GroundZero.Algebra.Group.Isomorphism
import GroundZero.Algebra.Group.Free

open GroundZero.Types.Equiv (biinv transport)
open GroundZero.Types.Id (ap)
open GroundZero.Structures
open GroundZero.Types
open GroundZero.Proto
open GroundZero.HITs
open GroundZero

/-
  Group presentation, presentation of every group.
  * https://en.wikipedia.org/wiki/presentation_of_a_group#Definition

  Abelianization (as factor group).
  * https://groupprops.subwiki.org/wiki/abelianization
  * https://ncatlab.org/nlab/show/abelianization

  Free abelian group.
  * https://en.wikipedia.org/wiki/Free_abelian_group
-/

namespace GroundZero.Algebra

namespace Group
  variable {G : Group}

  universe u v

  hott definition Closure.set (G : Group.{u}) (x : Group.subset.{u, v} G) : G.subset :=
  Ens.smallest.{u, v, max u v} (λ φ, G.isSubgroup φ × G.isNormal φ × x ⊆ φ)

  hott definition Closure.sub (φ : G.subset) : φ ⊆ Closure.set G φ :=
  begin intros x G y H; apply H.2.2; assumption end

  hott lemma Closure.subTrans {φ : G.subset} {ψ : G.normal} : φ ⊆ ψ.set → Closure.set G φ ⊆ ψ.set :=
  begin
    intros H x G; apply G; apply Prod.mk;
    exact ψ.1.2; apply Prod.mk; exact ψ.2; exact H
  end

  hott lemma Closure.elim (φ : G.normal) :
    Closure.set G φ.set ⊆ φ.set :=
  Closure.subTrans (Ens.ssubset.refl φ.set)

  hott definition Closure (x : G.subset) : G.normal :=
  ⟨begin
    fapply Group.subgroup.mk; exact Closure.set G x;
    { intro y ⟨G, H⟩; apply G.1 };
    { intro a b G H y F; apply F.1.2.1;
      apply G y; assumption; apply H y; assumption };
    { intro a H y G; apply G.1.2.2; apply H y; assumption }
  end,
  begin intros g h G y H; apply H.2.1; apply G y; assumption end⟩

  section
    variable {ε : Type u} (R : (F ε).subset)
    hott definition Presentation :=
    (F ε)\(Closure R)

    hott definition Presentation.carrier :=
    factorLeft (F ε) (Closure R)

    hott definition Presentation.one : Presentation.carrier R :=
    (Presentation R).e
  end

  hott lemma Presentation.sound {A : Type u}
    {R : (F A).subset} {x : F.carrier A} (H : x ∈ R) :
      @Factor.incl (F A) _ x = Presentation.one R :=
  begin apply Factor.sound; apply Closure.sub; assumption end

  hott definition commutators (G : Group) : G.subset :=
  GroundZero.Algebra.im (λ (a, b), commutator a b)

  hott definition Abelianization (G : Group) :=
  G\Closure (commutators G)
  postfix:max "ᵃᵇ" => Abelianization

  hott definition Abelianization.elem : G.carrier → (Abelianization G).carrier :=
  Factor.incl

  hott theorem abelComm : (Abelianization G).isCommutative :=
  begin
    intro (a : Relquot _) (b : Relquot _);
    apply @commutes (Abelianization G); induction a;
    { case elemπ a =>
      induction b;
      { case elemπ b =>
        apply Factor.sound; intros y H; apply H.2.2; apply Merely.elem;
        existsi (a, b); reflexivity };
      apply Relquot.set; apply propIsSet; apply Relquot.set };
      apply Relquot.set; apply propIsSet; apply Relquot.set
  end

  section
    variable {H : Group} (ρ : H.isCommutative)

    hott theorem commutators.toKer (f : Hom G H) : commutators G ⊆ (ker f).set :=
    begin
      intro x; fapply HITs.Merely.rec; apply Ens.prop;
      intro ⟨(a, b), q⟩; change _ = _; apply calc
        f.1 x = f.1 (G.φ (G.φ a b) (G.φ (G.ι a) (G.ι b)))             : ap f.1 (Id.inv q),
              = H.φ (f.1 (G.φ a b)) (f.1 (G.φ (G.ι a) (G.ι b)))       : homoMul f _ _,
              = H.φ (f.1 (G.φ a b)) (H.φ (f.1 (G.ι a)) (f.1 (G.ι b))) : ap _ (homoMul f _ _),
              = H.φ (f.1 (G.φ a b)) (H.φ (f.1 (G.ι b)) (f.1 (G.ι a))) : ap _ (ρ _ _),
              = H.φ (f.1 (G.φ a b)) (f.1 (G.φ (G.ι b) (G.ι a)))       : ap _ (homoMul f _ _)⁻¹,
              = f.1 (G.φ (G.φ a b) (G.φ (G.ι b) (G.ι a)))             : Id.inv (homoMul f _ _),
              = f.1 (G.φ (G.φ (G.φ a b) (G.ι b)) (G.ι a))             : ap f.1 (Id.inv (G.mulAssoc _ _ _)),
              = f.1 (G.φ (G.φ a (G.φ b (G.ι b))) (G.ι a))             : @ap G.carrier H.carrier _ _ (λ x, f.1 (G.φ x (G.ι a))) (G.mulAssoc a b (G.ι b)),
              = f.1 (G.φ (G.φ a G.e) (G.ι a))                         : @ap G.carrier H.carrier _ _ (λ x, f.1 (G.φ (G.φ a x) (G.ι a))) (mulRightInv b),
              = f.1 (G.φ a (G.ι a))                                   : @ap G.carrier H.carrier _ _ (λ x, f.1 (G.φ x (G.ι a))) (G.mulOne a),
              = f.1 G.e                                               : ap f.1 (mulRightInv a),
              = H.e                                                   : homoUnit f
    end
  end

  hott definition commutators.toClosureKer {H : Group} (ρ : H.isCommutative) (f : Hom G H) :
    Ens.ssubset (Closure.set G (commutators G)) (ker f).set :=
  Closure.subTrans (commutators.toKer ρ f)

  hott definition Abelianization.rec {G A : Group} (ρ : A.isCommutative)
    (f : Hom G A) : Gᵃᵇ.carrier → A.carrier :=
  begin
    fapply Factor.lift; exact f; intros x H;
    apply commutators.toClosureKer ρ; assumption
  end

  hott definition Abelianization.homomorphism {G A : Group} (ρ : A.isCommutative) (f : Hom G A) : Hom Gᵃᵇ A :=
  mkhomo (Abelianization.rec ρ f) (begin
    intro (a : Relquot _) (b : Relquot _);
    induction a; induction b; apply homoMul;
    apply A.hset; apply propIsSet; apply A.hset;
    apply A.hset; apply propIsSet; apply A.hset
  end)

  hott definition FAb (A : Type u) := Abelianization (F A)

  hott definition FAb.elem {A : Type u} : A → (FAb A).carrier :=
  Abelianization.elem ∘ F.elem

  hott definition FAb.rec {A : Group} (ρ : A.isCommutative)
    {ε : Type v} (f : ε → A.carrier) : (FAb ε).carrier → A.carrier :=
  Abelianization.rec ρ (F.homomorphism f)

  hott definition FAb.homomorphism {A : Group} (ρ : A.isCommutative)
    {ε : Type v} (f : ε → A.carrier) : Hom (FAb ε) A :=
  Abelianization.homomorphism ρ (F.homomorphism f)

  hott definition normalFactor (φ : G.normal) : G\φ ≅ G\Closure φ.set :=
  Factor.iso (Closure.sub φ.set) (Closure.elim φ)

  hott definition F.homomorphism.encode :
    G.carrier → im.carrier (@F.homomorphism G G.carrier id) :=
  λ x, ⟨x, HITs.Merely.elem ⟨F.elem x, idp _⟩⟩

  hott theorem F.homomorphism.iso :
    G ≅ Im (@F.homomorphism G G.carrier id) :=
  begin
    fapply mkiso; exact F.homomorphism.encode;
    { intros x y; fapply Sigma.prod;
      reflexivity; apply HITs.Merely.uniq };
    { apply Prod.mk <;> existsi Sigma.fst;
      { intro; reflexivity };
      { intro; fapply Sigma.prod;
        reflexivity; apply HITs.Merely.uniq } }
  end

  hott theorem Presentation.univ :
    Σ (R : (F G.carrier).subset), G ≅ Presentation R :=
  begin
    existsi (ker (F.homomorphism id)).set;
    apply Iso.trans F.homomorphism.iso;
    apply Iso.trans firstIsoTheorem;
    apply normalFactor
  end
end Group

end GroundZero.Algebra
