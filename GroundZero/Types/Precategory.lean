import GroundZero.Theorems.Functions
import GroundZero.Theorems.Equiv

open GroundZero.Theorems.Functions
open GroundZero.Types.Id (ap)
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Theorems

namespace GroundZero.Types
universe u v

record Precategory : Type (max u v + 1) :=
(obj   : Type u)
(hom   : obj → obj → Type v)
(set   : Π (x y : obj), hset (hom x y))
(id    : Π {a : obj}, hom a a)
(com   : Π {a b c : obj}, hom b c → hom a b → hom a c)
(lu    : Π {a b : obj} (f : hom a b), com id f = f)
(ru    : Π {a b : obj} (f : hom a b), com f id = f)
(assoc : Π {a b c d : obj} (f : hom a b) (g : hom b c) (h : hom c d), com h (com g f) = com (com h g) f)

section
  variable (A : Precategory)

  instance : Reflexive  A.hom := ⟨λ _, A.id⟩
  instance : Transitive A.hom := ⟨λ _ _ _ p q, A.com q p⟩
end

namespace Precategory
  hott abbreviation compose {A : Precategory} {a b c : A.obj} (g : hom A b c) (f : hom A a b) : hom A a c :=
  A.com g f

  local infix:60 " ∘ " => compose

  hott definition hasInv(A : Precategory) {a b : A.obj} (f : hom A a b) :=
  Σ (g : hom A b a), (f ∘ g = id A) × (g ∘ f = id A)

  hott definition iso (A : Precategory) (a b : A.obj) :=
  Σ (f : hom A a b), hasInv A f

  hott definition idiso (A : Precategory) {a : A.obj} : iso A a a :=
  ⟨id A, ⟨id A, (lu A (id A), lu A (id A))⟩⟩

  noncomputable instance (A : Precategory) : Reflexive (iso A) := ⟨@idiso A⟩

  hott definition idtoiso (A : Precategory) {a b : A.obj} (p : a = b) : iso A a b :=
  begin induction p; reflexivity end

  hott definition invProp (A : Precategory) {a b : A.obj} (f : hom A a b) : prop (hasInv A f) :=
  begin
    intro ⟨g', (H₁, H₂)⟩ ⟨g, (G₁, G₂)⟩;
    fapply Sigma.prod; apply calc
        g' = id A ∘ g'    : (lu _ _)⁻¹
       ... = (g ∘ f) ∘ g' : ap (compose · g') G₂⁻¹
       ... = g ∘ (f ∘ g') : (assoc _ _ _ _)⁻¹
       ... = g ∘ id A     : ap (compose g) H₁
       ... = g            : ru _ _;
    apply productProp <;> apply set
  end

  hott definition op (A : Precategory) : Precategory :=
  ⟨A.obj, λ a b, hom A b a, λ a b, set A b a, id A,
   λ p q, A.com q p, λ p, A.ru p, λ p, A.lu p, λ f g h, (A.assoc h g f)⁻¹⟩

  hott definition Path (A : Type u) (H : groupoid A) : Precategory :=
  ⟨A, Id, H, idp _, λ p q, q ⬝ p, Id.rid, Id.lid, λ f g h, (Id.assoc f g h)⁻¹⟩

  hott definition univalent (A : Precategory) :=
  Π a b, biinv (@idtoiso A a b)

  hott definition isGroupoidIfUnivalent (A : Precategory) : univalent A → groupoid A.obj :=
  begin
    intros H a b; change hset (a = b); apply hsetRespectsEquiv;
    symmetry; existsi idtoiso A; apply H; apply hsetRespectsSigma;
    apply A.set; intro; apply propIsSet; apply invProp
  end

  record Functor (A B : Precategory) :=
  (apo   : A.obj → B.obj)
  (apf   : Π {a b : A.obj}, hom A a b → hom B (apo a) (apo b))
  (apid  : Π (a : A.obj), apf (@id A a) = id B)
  (apcom : Π {a b c : A.obj} (f : hom A b c) (g : hom A a b), apf (f ∘ g) = apf f ∘ apf g)

  instance (A B : Precategory) : CoeFun (Functor A B) (λ _, A.obj → B.obj) := ⟨Functor.apo⟩

  section
    variable {A B : Precategory} (F : Functor A B)

    hott definition isFaithful := Π a b, injective  (@Functor.apf A B F a b)
    hott definition isFull     := Π a b, surjective (@Functor.apf A B F a b)
  end

  section
    variable {A B C : Precategory}

    hott definition Functor.com (F : Functor B C) (G : Functor A B) : Functor A C :=
    ⟨F.apo ∘ G.apo, F.apf ∘ G.apf, λ x, ap F.apf (G.apid x) ⬝ F.apid (G x),
     λ f g, ap F.apf (G.apcom f g) ⬝ F.apcom (G.apf f) (G.apf g)⟩
  end

  record Natural {A B : Precategory} (F G : Functor A B) :=
  (com : Π x, hom B (F x) (G x))
  (nat : Π {a b : A.obj} (f : hom A a b), com b ∘ F.apf f = G.apf f ∘ com a)

  section
    variable (A B : Precategory) (F G : Functor A B)
    instance : CoeFun (Natural F G) (λ _, Π x, hom B (F x) (G x)) := ⟨Natural.com⟩
  end

  section
    variable {A B : Precategory}

    hott definition idn (F : Functor A B) : Natural F F :=
    ⟨λ _, id B, λ f, lu B (F.apf f) ⬝ (ru B (F.apf f))⁻¹⟩

    hott definition Natural.vert {F G H : Functor A B} (ε : Natural G H) (η : Natural F G) : Natural F H :=
    ⟨λ x, ε x ∘ η x, λ {a b} f, (assoc B _ _ _)⁻¹ ⬝ ap (B.com (ε b)) (η.nat f) ⬝ assoc B _ _ _ ⬝
                                ap (B.com · (η a)) (ε.nat f) ⬝ (assoc B _ _ _)⁻¹⟩
  end

  section
    variable {A B C : Precategory} {F₁ F₂ : Functor B C} {G₁ G₂ : Functor A B}

    hott definition Natural.horiz (ε : Natural F₁ F₂) (η : Natural G₁ G₂) : Natural (F₁.com G₁) (F₂.com G₂) :=
    ⟨λ x, ε (G₂ x) ∘ F₁.apf (η x), λ f, ap (C.com · _) (ε.nat _) ⬝ (assoc C _ _ _)⁻¹ ⬝ ap (C.com _ ·) (ε.nat _) ⬝
                                        assoc C _ _ _ ⬝ ap (C.com · _) ((F₂.apcom _ _)⁻¹ ⬝ ap F₂.apf (η.nat _) ⬝
                                        F₂.apcom _ _) ⬝ (assoc C _ _ _)⁻¹ ⬝ ap (C.com _) (ε.nat _)⁻¹⟩
  end

  hott definition isProduct (A : Precategory) (a b c : A.obj) :=
  Σ (i : hom A c a) (j : hom A c b),
    ∀ (x : A.obj) (f₁ : hom A x a) (f₂ : hom A x b),
      contr (Σ (f : hom A x c), i ∘ f = f₁ × j ∘ f = f₂)

  hott definition isCoproduct (A : Precategory) (a b c : A.obj) :=
  isProduct (op A) a b c
end Precategory

end GroundZero.Types
