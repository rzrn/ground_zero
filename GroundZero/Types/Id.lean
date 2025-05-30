import GroundZero.Proto

namespace GroundZero.Types
universe u v

hott remark UIP {A : Type u} {a b : A} (p q : Eq a b) : Eq p q := Eq.refl p

section
  variable (A : Sort u)

  instance : @Reflexive  A Eq := ⟨@Eq.refl  A⟩
  instance : @Symmetric  A Eq := ⟨@Eq.symm  A⟩
  instance : @Transitive A Eq := ⟨@Eq.trans A⟩
end

inductive Id {A : Type u} : A → A → Type u
| idp (a : A) : Id a a

attribute [induction_eliminator] Id.casesOn
export Id (idp)

infix:50 (priority := high) " = " => Id

/- fails!
hott example {A : Type u} {a b : A} (p q : a = b) : p = q :=
begin cases p; cases q; apply idp end
-/

hott definition J₁ {A : Type u} {a : A} (B : Π (b : A), a = b → Type v)
  (Bidp : B a (idp a)) {b : A} (p : a = b) : B b p :=
@Id.casesOn A a B b p Bidp

hott definition J₂ {A : Type u} {b : A} (B : Π (a : A), a = b → Type v)
  (Bidp : B b (idp b)) {a : A} (p : a = b) : B a p :=
begin induction p; apply Bidp end

namespace Id
  @[match_pattern] abbrev refl {A : Type u} {a : A} : a = a := idp a

  hott definition symm {A : Type u} {a b : A} (p : a = b) : b = a :=
  begin induction p; apply idp end

  hott definition trans {A : Type u} {a b c : A}
    (p : a = b) (q : b = c) : a = c :=
  begin induction p; apply q end

  noncomputable instance (A : Type u) : Reflexive  (@Id A) := ⟨@idp A⟩
  noncomputable instance (A : Type u) : Symmetric  (@Id A) := ⟨@symm A⟩
  noncomputable instance (A : Type u) : Transitive (@Id A) := ⟨@trans A⟩

  hott definition inv {A : Type u} {a b : A} (p : a = b) : b = a := symm p

  infixl:60 " ⬝ " => trans
  postfix:max "⁻¹" => symm

  hott lemma JSymm {A : Type} {a b : A} (B : Π x, b = x → Type v)
    (p : a = b) (w : B b (idp b)) : J₁ B w p⁻¹ = J₂ (λ x q, B x q⁻¹) w p :=
  begin induction p; reflexivity end

  hott definition lid {A : Type u} {a b : A} (p : a = b) : idp a ⬝ p = p :=
  begin induction p; reflexivity end

  hott definition rid {A : Type u} {a b : A} (p : a = b) : p ⬝ idp b = p :=
  begin induction p; reflexivity end

  hott definition compInv {A : Type u} {a b : A} (p : a = b) : p ⬝ p⁻¹ = idp a :=
  begin induction p; reflexivity end

  hott definition invComp {A : Type u} {a b : A} (p : a = b) : p⁻¹ ⬝ p = idp b :=
  begin induction p; reflexivity end

  hott remark reflTwice {A : Type u} {a b : A} (p : a = b) : idp a ⬝ p ⬝ idp b = p :=
  by apply rid

  hott definition explodeInv {A : Type u} {a b c : A} (p : a = b) (q : b = c) : (p ⬝ q)⁻¹ = q⁻¹ ⬝ p⁻¹ :=
  begin induction p; induction q; reflexivity end

  hott definition invInv {A : Type u} {a b : A} (p : a = b) : (p⁻¹)⁻¹ = p :=
  begin induction p; reflexivity end

  hott lemma invEqIfEqInv {A : Type u} {a b : A} {p : a = b} {q : b = a} : p⁻¹ = q → p = q⁻¹ :=
  begin induction p; intro η; induction η; reflexivity end

  hott lemma eqEnvIfInvEq {A : Type u} {a b : A} {p : a = b} {q : b = a} : p = q⁻¹ → p⁻¹ = q :=
  λ η => @invEqIfEqInv A b a p⁻¹ q⁻¹ (invInv p ⬝ η) ⬝ invInv q

  hott definition assoc {A : Type u} {a b c d : A} (p : a = b) (q : b = c) (r : c = d) : p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r :=
  begin induction p; reflexivity end

  hott definition ap {A : Type u} {B : Type v} {a b : A} (f : A → B) (p : a = b) : f a = f b :=
  begin induction p; reflexivity end

  hott lemma invInj {A : Type u} {a b : A} {p q : a = b} (α : p⁻¹ = q⁻¹) : p = q :=
  (invInv p)⁻¹ ⬝ ap (·⁻¹) α ⬝ invInv q

  hott corollary cancelCompInv {A : Type u} {a b c : A} (p : a = b) (q : b = c) : (p ⬝ q) ⬝ q⁻¹ = p :=
  (assoc p q q⁻¹)⁻¹ ⬝ ap (trans p) (compInv q) ⬝ rid p

  hott corollary cancelInvComp {A : Type u} {a b c : A} (p : a = b) (q : c = b) : (p ⬝ q⁻¹) ⬝ q = p :=
  (assoc p q⁻¹ q)⁻¹ ⬝ ap (trans p) (invComp q) ⬝ rid p

  hott corollary compInvCancel {A : Type u} {a b c : A} (p : a = b) (q : a = c) : p ⬝ (p⁻¹ ⬝ q) = q :=
  assoc p p⁻¹ q ⬝ ap (· ⬝ q) (compInv p)

  hott corollary invCompCancel {A : Type u} {a b c : A} (p : a = b) (q : b = c) : p⁻¹ ⬝ (p ⬝ q) = q :=
  assoc p⁻¹ p q ⬝ ap (· ⬝ q) (invComp p)

  hott theorem mapInv {A : Type u} {B : Type v} {a b : A} (f : A → B) (p : a = b) : ap f p⁻¹ = (ap f p)⁻¹ :=
  begin induction p; reflexivity end

  hott definition transCancelLeft {A : Type u} {a b c : A}
    (r : a = b) (p q : b = c) : r ⬝ p = r ⬝ q → p = q :=
  begin intro μ; induction r; exact μ end

  hott definition transCancelRight {A : Type u} {a b c : A} (r : b = c) (p q : a = b) : p ⬝ r = q ⬝ r → p = q :=
  begin
    intro μ; induction r; transitivity; { symmetry; apply rid };
    symmetry; transitivity; { symmetry; apply rid }; exact μ⁻¹
  end

  section
    variable {A : Type u} {B : Type v} {a b : A} {p q : a = b}

    hott definition ap2 (f : A → B) (r : p = q) : ap f p = ap f q := ap (ap f) r
    notation "ap²" => ap2

    hott definition ap3 {α β : p = q} (f : A → B) (r : α = β) : ap² f α = ap² f β := ap (ap² f) r
    notation "ap³" => ap3

    hott definition ap4 {α β : p = q} {r s : α = β} (f : A → B) (ε : r = s) : ap³ f r = ap³ f s := ap (ap³ f) ε
    notation "ap⁴" => ap4
  end

  hott lemma compReflIfEq {A : Type u} {a b : A} (p q : a = b) : p = q → p⁻¹ ⬝ q = idp b :=
  begin intro A; induction A; apply invComp end

  hott lemma eqIfCompRefl {A : Type u} {a b : A} (p q : a = b) : p⁻¹ ⬝ q = idp b → p = q :=
  begin intro α; induction p; exact α⁻¹ end

  class isPointed (A : Type u) := (point : A)

  hott definition pointOf (A : Type u) [isPointed A] : A := isPointed.point

  hott definition Pointed := Σ (A : Type u), A

  macro "Type⁎" : term => `(Pointed)
  macro "Type⁎" n:(ppSpace level:max) : term => `(Pointed.{$n})

  section
    open Lean.PrettyPrinter.Delaborator

    @[delab app.GroundZero.Types.Id.Pointed]
    def delabPointed : Delab :=
    Meta.Notation.delabCustomSort `(Type⁎) (λ n, `(Type⁎ $n))
  end

  abbrev Pointed.space : Type⁎ u → Type u := Sigma.fst
  abbrev Pointed.point : Π (A : Type⁎ u), A.space := Sigma.snd

  hott definition Pointed.Map (A B : Type⁎) :=
  Σ (f : A.space → B.space), f A.point = B.point

  notation "Map⁎" => Pointed.Map

  namespace Pointed.Map
    variable {A B : Type⁎} (φ : Map⁎ A B)

    hott abbreviation ap : A.space → B.space      := φ.fst
    hott abbreviation id : φ.ap A.point = B.point := φ.snd
  end Pointed.Map

  hott definition Loop {B : Type u} (b : B) : ℕ → Type u
  | Nat.zero   => B
  | Nat.succ n => Loop (idp b) n

  macro:max "Ω" n:superscript "(" τ:term ")" : term => do
    `(Loop (pointOf $τ) $(← Meta.Notation.parseSuperscript n))

  macro:max "Ω" n:superscript "(" τ:term ", " ε:term ")" : term => do
    `(@Loop $τ $ε $(← Meta.Notation.parseSuperscript n))

  macro:max "Ω" "[" n:term "]" "(" τ:term ")" : term => do
    `(Loop (pointOf $τ) $n)

  macro:max "Ω" "[" n:term "]" "(" τ:term ", " ε:term ")" : term => do
    `(@Loop $τ $ε $n)

  section
    open Lean Lean.PrettyPrinter.Delaborator

    def isPointOf (e : Expr) := e.isAppOfArity' `GroundZero.Types.Id.pointOf 2

    @[delab app.GroundZero.Types.Id.Loop]
    def delabLoop : Delab := whenPPOption Lean.getPPNotation do {
      let ε ← SubExpr.getExpr;
      guard (ε.isAppOfArity' `GroundZero.Types.Id.Loop 3);

      let B   ← SubExpr.withNaryArg 0 delab;
      let b   ← SubExpr.withNaryArg 1 delab;
      let dim ← SubExpr.withNaryArg 2 delab;

      match dim.raw.isNatLit? with
      | some k => let sup ← Meta.Notation.mkSupNumeral dim k;
                  if isPointOf (ε.getArg! 1) then `(Ω$sup($B)) else `(Ω$sup($B, $b))
      | none   => if isPointOf (ε.getArg! 1) then `(Ω[$dim]($B)) else `(Ω[$dim]($B, $b))
    }
  end

  hott definition idΩ {B : Type u} (b : B) : Π n, Ωⁿ(B, b)
  | Nat.zero   => b
  | Nat.succ n => idΩ (idp b) n

  hott definition apΩ {A : Type u} {B : Type v} (f : A → B) {a : A} : Π {n : ℕ}, Ωⁿ(A, a) → Ωⁿ(B, f a)
  | Nat.zero   => f
  | Nat.succ _ => apΩ (ap f)
end Id

hott definition Not (A : Type u) : Type u := A → (𝟎 : Type)
hott definition Neq {A : Type u} (a b : A) := Not (Id a b)

namespace Not
  prefix:90 (priority := high) "¬" => Not
  infix:50 (priority := high) " ≠ " => Neq

  hott definition absurd {A : Type u} {B : Type v} (h : A) (g : ¬A) : B :=
  nomatch (g h)

  hott definition univ : (𝟎 : Type u) → (𝟎 : Type v) :=
  λ e, nomatch e
end Not

namespace Whiskering
  open GroundZero.Types.Id (ap)

  variable {A : Type u} {a b c : A}

  hott definition rwhs {p q : a = b} (ν : p = q) (r : b = c) : p ⬝ r = q ⬝ r :=
  begin induction r; apply (Id.rid p) ⬝ ν ⬝ (Id.rid q)⁻¹ end

  infix:60 " ⬝ᵣ " => rwhs

  hott definition lwhs {r s : b = c} (q : a = b) (κ : r = s) : q ⬝ r = q ⬝ s :=
  begin induction q; exact (Id.lid r) ⬝ κ ⬝ (Id.lid s)⁻¹ end

  infix:60 " ⬝ₗ " => lwhs

  variable {p q : a = b} {r s : b = c}

  hott definition horizontalComp₁ (ν : p = q) (κ : r = s) := (ν ⬝ᵣ r) ⬝ (q ⬝ₗ κ)
  infix:65 " ⋆ " => horizontalComp₁

  hott definition horizontalComp₂ (ν : p = q) (κ : r = s) := (p ⬝ₗ κ) ⬝ (ν ⬝ᵣ s)
  infix:65 " ⋆′ " => horizontalComp₂

  hott lemma compUniq (ν : p = q) (κ : r = s) : ν ⋆ κ = ν ⋆′ κ :=
  begin induction p; induction r; induction ν; induction κ; reflexivity end

  hott lemma loop₁ {a : A} {ν κ : idp a = idp a} : ν ⬝ κ = ν ⋆ κ :=
  begin
    apply Id.symm; transitivity; apply ap (· ⬝ _);
    apply Id.reflTwice; apply ap (ν ⬝ ·); apply Id.reflTwice
  end

  hott lemma loop₂ {a : A} {ν κ : idp a = idp a} : ν ⋆′ κ = κ ⬝ ν :=
  begin
    transitivity; apply ap (· ⬝ _); apply Id.reflTwice;
    apply ap (κ ⬝ ·); apply Id.reflTwice
  end

  hott theorem «Eckmann–Hilton argument» {a : A} (ν κ : idp a = idp a) : ν ⬝ κ = κ ⬝ ν :=
  loop₁ ⬝ compUniq ν κ ⬝ loop₂

  hott corollary comm {a b : A} {p : a = b} (ν κ : p = p) : ν ⬝ κ = κ ⬝ ν :=
  begin induction p; apply «Eckmann–Hilton argument» end
end Whiskering

end GroundZero.Types
