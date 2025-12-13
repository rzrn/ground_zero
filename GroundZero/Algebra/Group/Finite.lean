import GroundZero.Algebra.Group.Basic
import GroundZero.Theorems.Nat

open GroundZero.Types.Equiv (transport)
open GroundZero.Types.Id (ap)
open GroundZero.Types
open GroundZero.Proto

namespace GroundZero
universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

namespace Types.Coproduct
  hott def respectsEquivLeft (e : A ≃ B) : C + A ≃ C + B := begin
    apply Equiv.trans; apply Types.Coproduct.symm;
    apply Equiv.trans; apply Types.Nat.equivAddition;
    assumption; apply Types.Coproduct.symm
  end

  hott def eqvVariants (e : C + A ≃ C + B) (x : A) :
    (Σ y, e (Sum.inr x) = Sum.inr y) +
    (Σ y, e (Sum.inr x) = Sum.inl y) :=
  match e (Sum.inr x) with
  | Sum.inr a => Sum.inl ⟨a, Id.refl⟩
  | Sum.inl b => Sum.inr ⟨b, Id.refl⟩

  hott def Diff (f : B → A) : Type (max u v) :=
  Σ (x : A), Π y, ¬(x = f y)

  hott def Diff.inl : Diff (@Sum.inl A B) → B :=
  λ | ⟨Sum.inl x, p⟩ => explode (p x Id.refl)
    | ⟨Sum.inr x, p⟩ => x

  hott def Empty.lift : Proto.Empty.{u} → Proto.Empty.{v} :=
  λ z, explode z

  hott def Diff.inr : B → Diff (@Sum.inl A B) :=
  λ x, ⟨Sum.inr x, λ y p, explode (@Types.Coproduct.inr.encode.{u, v} A B x (Sum.inl y) p)⟩

  hott def ldiff : Diff (@Sum.inl A B) ≃ B :=
  begin
    existsi Diff.inl; apply Prod.mk <;> existsi Diff.inr;
    { intro ⟨x, p⟩; induction x using Sum.casesOn;
      { apply explode; fapply p; assumption; reflexivity };
      { fapply Types.Sigma.prod; reflexivity;
        { apply Structures.piProp; intro;
          apply Structures.notIsProp } } };
    { intro; reflexivity }
  end

  hott def left : (A + B) + C → A + (B + C)
  | Sum.inl (Sum.inl a) => Sum.inl a
  | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
  | Sum.inr c           => Sum.inr (Sum.inr c)

  hott def right : A + (B + C) → (A + B) + C
  | Sum.inl a           => Sum.inl (Sum.inl a)
  | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
  | Sum.inr (Sum.inr c) => Sum.inr c

  hott def rightLeft : right ∘ left ~ @id ((A + B) + C)
  | Sum.inl (Sum.inl a) => Id.refl
  | Sum.inl (Sum.inr b) => Id.refl
  | Sum.inr c           => Id.refl

  hott def leftRight : left ∘ right ~ @id (A + (B + C))
  | Sum.inl a           => Id.refl
  | Sum.inr (Sum.inl b) => Id.refl
  | Sum.inr (Sum.inr c) => Id.refl

  hott def assoc : (A + B) + C ≃ A + (B + C) :=
  ⟨left, (⟨right, rightLeft⟩, ⟨right, leftRight⟩)⟩

  hott def zero : 𝟎 + A → A
  | Sum.inl h => explode h
  | Sum.inr x => x

  hott def empty : 𝟎 + A ≃ A :=
  begin
    existsi zero; apply Prod.mk <;> existsi Sum.inr <;> intro x;
    { induction x using Sum.casesOn;
      apply explode; assumption;
      reflexivity };
    { reflexivity }
  end
end Types.Coproduct

namespace Types.Product
  hott def destroy : 𝟎 × A ≃ 𝟎 := begin
    existsi Prod.fst; apply Prod.mk <;>
    existsi explode <;> intro x;
    apply explode x.1;
    apply explode x
  end

  hott def split : (A + B) × C → (A × C) + (B × C)
  | (Sum.inl a, c) => Sum.inl (a, c)
  | (Sum.inr b, c) => Sum.inr (b, c)

  hott def join : (A × C) + (B × C) → (A + B) × C
  | Sum.inl (a, c) => (Sum.inl a, c)
  | Sum.inr (b, c) => (Sum.inr b, c)

  hott def splitJoin : split ∘ join ~ @id ((A × C) + (B × C))
  | Sum.inl (a, c) => Id.refl
  | Sum.inr (b, c) => Id.refl

  hott def joinSplit : join ∘ split ~ @id ((A + B) × C)
  | (Sum.inl a, c) => Id.refl
  | (Sum.inr b, c) => Id.refl

  hott def distribRight : (A + B) × C ≃ (A × C) + (B × C) :=
  ⟨split, (⟨join, joinSplit⟩, ⟨join, splitJoin⟩)⟩

  hott def distribLeft : A × (B + C) ≃ (A × B) + (A × C) :=
  begin
    apply Equiv.trans; apply Types.Product.comm;
    apply Equiv.trans; apply distribRight;
    apply Equiv.trans; apply Types.Nat.equivAddition; apply comm;
    apply Types.Coproduct.respectsEquivLeft; apply comm
  end

  hott def left  (w : (A × B) × C) : A × (B × C) := (w.1.1, (w.1.2, w.2))
  hott def right (w : A × (B × C)) : (A × B) × C := ((w.1, w.2.1), w.2.2)

  hott def assoc : (A × B) × C ≃ A × (B × C) :=
  begin existsi left; apply Prod.mk <;> existsi right <;> apply idp end
end Types.Product

namespace Algebra

namespace Finite
  hott def plus : Π (n m : ℕ), Finite n + Finite m ≃ Finite (n + m)
  | Nat.zero,   m => Equiv.trans Types.Coproduct.empty (Equiv.idtoeqv (ap Finite (Theorems.Nat.zeroPlus m)⁻¹))
  | Nat.succ n, m => calc
    Finite (Nat.succ n) + Finite m ≃ Finite n + (𝟏 + Finite m) : Types.Coproduct.assoc,
                                   ≃ Finite n + (Finite m + 𝟏) : Types.Coproduct.respectsEquivLeft Types.Coproduct.symm,
                                   ≃ (Finite n + Finite m) + 𝟏 : Equiv.symm Types.Coproduct.assoc,
                                   ≃ Finite (n + m) + 𝟏        : Types.Nat.equivAddition 𝟏 (plus n m),
                                   ≃ Finite (Nat.succ (n + m)) : Equiv.ideqv _,
                                   ≃ Finite (Nat.succ n + m)   : Equiv.idtoeqv (ap Finite (Theorems.Nat.succPlus n m)⁻¹)

  hott def mul : Π (n m : ℕ), Finite n × Finite m ≃ Finite (n * m)
  | Nat.zero,   m => Equiv.trans Types.Product.destroy (Equiv.idtoeqv (ap Finite (Theorems.Nat.zeroMul m)⁻¹))
  | Nat.succ n, m => calc
    Finite (Nat.succ n) × Finite m ≃ (Finite n × Finite m) + (𝟏 × Finite m) : Types.Product.distribRight,
                                   ≃ Finite (n * m) + (𝟏 × Finite m)        : Types.Nat.equivAddition _ (mul n m),
                                   ≃ Finite (n * m) + Finite m              : Types.Coproduct.respectsEquivLeft (Structures.prodUnitEquiv _),
                                   ≃ Finite (n * m + m)                     : plus _ _,
                                   ≃ Finite (Nat.succ n * m)                : Equiv.idtoeqv (ap Finite (Theorems.Nat.mulSucc n m)⁻¹)
end Finite

namespace Group
  class fin (G : Pregroup) :=
  (eqv : Σ n, G.carrier ≃ Finite n)

  def ord (G : Pregroup) [fin G] := (@fin.eqv G _).1

  hott def coset {G : Group}
    (h : G.carrier) (φ : G.subset) : Ens G.carrier :=
  ⟨λ x, Σ y, (y ∈ φ) × (x = G.φ h y), begin
    intro x ⟨a, p⟩ ⟨b, q⟩; fapply Types.Sigma.prod;
    fapply mulCancelLeft; exact h;
    transitivity; exact p.2⁻¹; exact q.2;
    apply Structures.productProp;
    apply Ens.prop; apply G.hset
  end⟩

  hott def coset.intro {G : Group} {a b : G.carrier}
    {φ : G.subset} : b ∈ φ → G.φ a b ∈ coset a φ :=
  begin intro p; existsi b; apply Prod.mk; assumption; reflexivity end

  hott def coset.triv {G : Group}
    (h : G.carrier) (φ : G.subgroup) : h ∈ coset h φ.set :=
  begin existsi G.e; apply Prod.mk; apply φ.unit; symmetry; apply G.mulOne end

  hott def coset.assoc {G : Group} {a b : G.carrier}
    (φ : G.subgroup) : coset a (coset b φ.set) = coset (G.φ a b) φ.set :=
  begin
    apply Ens.ext; intro x; apply Prod.mk;
    { intro ⟨y, ⟨⟨z, ⟨p, q⟩⟩, r⟩⟩; apply transport (· ∈ coset (G.φ a b) φ.set);
      symmetry; transitivity; { transitivity; exact r; apply ap (G.φ a); exact q };
      symmetry; apply G.mulAssoc; apply coset.intro p };
    { intro ⟨y, p⟩; apply transport (· ∈ coset a (coset b φ.set));
      symmetry; transitivity; exact p.2; apply G.mulAssoc;
      apply coset.intro; apply coset.intro; exact p.1 }
  end

  section
    variable {G : Group.{u}} (φ : Group.subgroup.{u, max u v} G)

    hott def coset.idem {x : G.carrier} : x ∈ φ.set → coset x φ.set = φ.set :=
    begin
      intro p; apply Ens.ext; intro y; apply Prod.mk;
      { intro ⟨z, q⟩; apply transport (· ∈ φ.set); exact q.2⁻¹;
        apply φ.mul; exact p; exact q.1 };
      { intro q; existsi G.φ (G.ι x) y; apply Prod.mk;
        { apply φ.mul; { apply φ.inv; exact p }; exact q };
        { transitivity; { symmetry; apply G.oneMul };
          symmetry; transitivity; { symmetry; apply G.mulAssoc };
          apply ap (G.φ · y); apply mulRightInv } }
    end

    hott def coset.uniq {x g₁ g₂ : G.carrier} :
      x ∈ coset g₁ φ.set → x ∈ coset g₂ φ.set → coset g₁ φ.set = coset g₂ φ.set :=
    begin
      intro ⟨x₁, p⟩ ⟨x₂, q⟩; transitivity;
      apply ap (coset · φ.set); apply calc
         g₁ = G.φ g₁ G.e               : (G.mulOne g₁)⁻¹,
            = G.φ g₁ (G.φ x₁ (G.ι x₁)) : ap (G.φ g₁) (mulRightInv x₁)⁻¹,
            = G.φ (G.φ g₁ x₁) (G.ι x₁) : (G.mulAssoc _ _ _)⁻¹,
            = G.φ (G.φ g₂ x₂) (G.ι x₁) : ap (G.φ · (G.ι x₁)) (p.2⁻¹ ⬝ q.2),
            = G.φ g₂ (G.φ x₂ (G.ι x₁)) : G.mulAssoc _ _ _;
      transitivity; { symmetry; apply coset.assoc };
      apply ap; apply @coset.idem.{u, v} _ G φ;
      apply φ.mul; exact q.1; apply φ.inv; exact p.1
    end
  end

  hott def coset.all {G : Group} (φ : G.subgroup) : G.subset :=
  Ens.sunion (λ s, Σ y, s = coset y φ.set)

  hott def coset.total {G : Group} (φ : G.subgroup) :
    G.carrier → (coset.all φ).subtype :=
  begin
    intro x; existsi x; apply HITs.Merely.elem;
    existsi coset x φ.fst; apply Prod.mk;
    apply coset.triv; existsi x; reflexivity
  end

  hott def coset.repr (G : Group) (φ : G.subgroup) :
    G.carrier ≃ (coset.all φ).subtype :=
  begin
    existsi coset.total φ; apply Prod.mk <;> existsi Sigma.fst;
    { intro; reflexivity };
    { intro ⟨x, p⟩; fapply Types.Sigma.prod;
      reflexivity; apply Ens.prop }
  end
end Group

end Algebra

end GroundZero
