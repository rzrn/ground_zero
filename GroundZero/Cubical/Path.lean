import GroundZero.HITs.Interval

open GroundZero.Types.Equiv (transport apd)
open GroundZero.HITs.Interval (i₀ i₁ seg)
open GroundZero.Types GroundZero.HITs
open GroundZero.Types.Id (ap)
open GroundZero.Proto (idfun)

/-
  * Coercions.
  * Basic path lemmas: refl, symm, cong, funext...
  * Connections.
  * Singleton contractibility, J elimination rule.
  * PathP.
-/

namespace GroundZero.Cubical
universe u v w

inductive Path (A : Type u) : A → A → Type u
| lam (f : I → A) : Path A (f 0) (f 1)

hott abbreviation LineP (σ : I → Type u) := Π (i : I), σ i

hott abbreviation Line (A : Type u) := I → A

hott definition Line.refl {A : Type u} (a : A) : Line A := λ _, a

hott definition decode {A : Type u} {a b : A} (p : a = b) : Path A a b :=
Path.lam (Interval.elim p)

hott definition elim {A : Type u} {a b : A} (p : Path A a b) : I → A :=
@Path.casesOn A (λ _ _ _, I → A) a b p (@idfun (I → A))

hott definition encode {A : Type u} {a b : A} (p : Path A a b) : a = b :=
@Path.casesOn A (λ a b _, a = b) a b p (ap · seg)

hott lemma encodeDecode {A : Type u} {a b : A} (p : a = b) : encode (decode p) = p :=
by apply Interval.recβrule

hott lemma transportFunext {A : Type u} {B : Type v} {C : B → Type w} {f g : A → B} (H : f ~ g) {x : A}
  (u : C (f x)) : transport (λ (f : A → B), C (f x)) (Theorems.funext H) u = transport C (H x) u :=
begin
  transitivity; apply Equiv.transportComp; apply ap (transport _ · _);
  transitivity; apply Theorems.mapToHapply; apply Interval.happly; apply Theorems.happlyFunext
end

hott lemma decodeEncode {A : Type u} {a b : A} (p : Path A a b) : decode (encode p) = p :=
begin
  induction p using Path.casesOn; symmetry; transitivity; symmetry;
  apply apd Path.lam; apply Theorems.funext; apply Interval.mapExt;

  transitivity; apply Equiv.transportDiag₁ (λ (f g : I → A), Path A (f 0) (g 1));
  transitivity; apply transportFunext; apply @transportFunext I A (Path A · _)
end

hott corollary equivPath {A : Type u} (a b : A) : Path A a b ≃ (a = b) :=
Equiv.intro encode decode decodeEncode encodeDecode

hott corollary ofDecode {A : Type u} {a b : A} (p q : a = b) : decode p = decode q → p = q :=
(equivPath a b).eqvLeftInj p q

hott corollary ofEncode {A : Type u} {a b : A} (p q : Path A a b) : encode p = encode q → p = q :=
(equivPath a b).eqvInj p q

hott definition Path.compute {A : Type u} {a b : A} (p : Path A a b) : I → A :=
Interval.rec a b (encode p)

infix:60 " @ " => Path.compute

macro "<" is:Lean.Parser.Term.binderIdent+ ">" e:term : term =>
  Array.foldrM (λ i e, `(Path.lam (λ ($i : I), $(⟨e⟩)))) e (Array.map (λ s => ⟨s⟩) is)

namespace Path

hott definition coe.forward (B : I → Type u) (i : I) (x : B i₀) : B i :=
Interval.ind x (transport B seg x) (idp _) i

hott definition coe.back (B : I → Type u) (i : I) (x : B i₁) : B i :=
Interval.ind (transport B seg⁻¹ x) x (begin
  apply Id.trans; symmetry; apply Equiv.transportcom;
  transitivity; apply ap (transport B · x);
  apply Id.invComp; reflexivity
end) i

hott definition coe (i k : I) (B : I → Type u) : B i → B k :=
coe.forward (λ i, B i → B k) i (coe.forward B k)

hott definition coeInv (i k : I) (B : I → Type u) : B i → B k :=
coe.back (λ i, B i → B k) i (coe.back B k)

notation "coe⁻¹" => coeInv

hott definition refl {A : Type u} (a : A) : Path A a a := <_> a
hott instance (A : Type u) : Reflexive (Path A) := ⟨refl⟩

hott definition rfl {A : Type u} {a : A} : Path A a a := <_> a

hott definition symm {A : Type u} {a b : A} (p : Path A a b) : Path A b a :=
coe 1 0 (λ i, Path A b (p @ i)) rfl

hott instance (A : Type u) : Symmetric (Path A) := ⟨@symm A⟩

hott definition neg : I → I := Interval.elim seg⁻¹

prefix:65 "−" => neg

hott example {A : Type u} {a b : A} (p : Path A a b) : Path A b a :=
<i> p @ −i

hott definition homotopy {A : Type u} {B : A → Type v} (f g : Π x, B x) :=
Π x, Path (B x) (f x) (g x)
infix:50 " ~′ " => homotopy

hott definition homotopyEquality {A : Type u} {B : A → Type v}
  {f g : Π x, B x} (p : f ~′ g) : f ~ g :=
λ x, encode (p x)

hott definition funext {A : Type u} {B : A → Type v}
  {f g : Π x, B x} (p : f ~′ g) : Path (Π x, B x) f g :=
<i> λ x, (p x) @ i

hott definition apf {A : Type u} {B : Type v} {a b : A}
  (f : A → B) (p : Path A a b) : Path B (f a) (f b) :=
<i> f (p @ i)

hott definition coerce {A : Type u} (B : A → Type v) {a b : A} (p : Path A a b) : B a → B b :=
coe 0 1 (λ i, B (p @ i))

section
  variable {A B : Type u} (p : Path (Type u) A B)

  hott definition trans     : A → B := coe   0 1 (λ i, p @ i)
  hott definition transNeg  : B → A := coe   1 0 (λ i, p @ i)
  hott definition transBack : A → B := coe⁻¹ 0 1 (λ i, p @ i)
end

notation "trans⁻¹" => transBack

hott definition transK {A B : Type u} (p : Path (Type u) A B) (x : A) :
  Path A x (transNeg p (trans p x)) :=
<i> coe i 0 (λ i, p @ i) (coe 0 i (λ i, p @ i) x)

hott definition idtoeqv {A B : Type u} (p : Path (Type u) A B) : A ≃ B :=
trans (<i> A ≃ p @ i) (Equiv.ideqv A)

section
  variable {A : Type u} {a b : A} (p : Path A a b)

  hott definition testEta : Path (Path A a b) p p := Path.rfl

  hott definition face₀ : A := p @ 0
  hott definition face₁ : A := p @ 1

  hott definition compTest₀ : Path A (p @ 0) a := Path.rfl
  hott definition compTest₁ : Path A (p @ 1) b := Path.rfl

  -- fails, because this requires −(−i) ≡ i
  --hott definition symmTest : Path (Path A a b) (p⁻¹)⁻¹ p := rfl
end

hott definition com {A : Type u} {a b c : A} (p : Path A a b) (q : Path A b c) : Path A a c :=
coerce (Path A a) q p

-- this will be replaced by a more general version in future
hott definition kan {A : Type u} {a b c d : A}
  (bottom : Path A b c) (left : Path A b a) (right : Path A c d) : Path A a d :=
com (com (symm left) bottom) right

hott definition kanOp {A : Type u} {a b : A} (p : Path A a a) (q : Path A a b) : Path A b b :=
kan p q q

hott definition intervalContrLeft  (i : I) : Path I i₀ i := coe 0 i (Path I i₀) rfl
hott definition intervalContrRight (i : I) : Path I i₁ i := coe 1 i (Path I i₁) rfl

section
  variable {A : Type u} {a b : A} (p : Path A a b)

  hott definition connAnd : LineP (λ i, Path A a (p @ i)) := λ i, <j> p @ i ∧ j
  hott definition connOr  : LineP (λ i, Path A (p @ i) b) := λ i, <j> p @ i ∨ j
end

hott definition singl {A : Type u} (a : A) := Σ (x : A), Path A a x
hott definition eta   {A : Type u} (a : A) : singl a := ⟨a, refl a⟩

hott lemma encodeRefl {A : Type u} (a : A) : encode (refl a) = idp a :=
by apply Equiv.constmap

hott corollary decodeIdp {A : Type u} (a : A) : decode (idp a) = refl a :=
ap decode (encodeRefl a)⁻¹ ⬝ decodeEncode (refl a)

hott lemma encodeApf {A : Type u} {B : Type v} {a b : A} (f : A → B) (p : Path A a b) :
  encode (apf f p) = ap f (encode p) :=
Equiv.mapOverComp _ _ _ ⬝ ap (ap f) (Interval.recβrule _ _ _)

hott lemma decodeAp {A : Type u} {B : Type v} {a b : A} (f : A → B) (p : a = b) :
  apf f (decode p) = decode (ap f p) :=
ofEncode _ _ (encodeApf _ _ ⬝ ap (ap f) (encodeDecode _) ⬝ (encodeDecode _)⁻¹)

hott definition rev {A : Type u} {a b : A} (p : Path A a b) : Path A b a :=
<i> p @ −i

hott lemma apNegSeg : ap neg seg = seg⁻¹ :=
Structures.propIsSet Interval.intervalProp _ _ _ _

hott lemma encodeRev {A : Type u} {a b : A} (p : Path A a b) : encode (rev p) = (encode p)⁻¹ :=
Equiv.mapOverComp _ _ _ ⬝ ap (ap _) apNegSeg ⬝ Interval.recβruleRev _ _ _

hott lemma decodeRev {A : Type u} {a b : A} (p : a = b) : (<i> (decode p) @ −i) = decode p⁻¹ :=
ofEncode _ _ (encodeRev _ ⬝ ap _ (encodeDecode _) ⬝ (encodeDecode _)⁻¹)

hott lemma coerceβ {A : Type u} (B : A → Type v) {a : A} (u : B a) : coerce B (refl a) u = u :=
begin
  transitivity; apply Equiv.transportComp B; transitivity; apply ap (transport _ · _);
  transitivity; apply Interval.recβrule; apply Equiv.constmap; reflexivity
end

section
  variable {A : Type u} {a b : A}

  hott lemma coerceReflDecode (p : a = b) : coerce (Path A a) (decode p) (refl a) = decode p :=
  begin
    induction p; transitivity; apply ap (coerce _ · _); apply decodeIdp;
    transitivity; apply coerceβ; symmetry; apply decodeIdp
  end

  hott corollary coerceRefl (p : Path A a b) : coerce (Path A a) p (refl a) = p :=
  begin
    transitivity; apply ap (coerce _ · _); symmetry; apply decodeEncode;
    transitivity; apply coerceReflDecode; apply decodeEncode
  end

  hott lemma coerceComRevDecode (p : a = b) : coerce (Path A · b) (decode p) (decode p) = refl b :=
  begin
    induction p; transitivity; apply ap (coerce _ · _); apply decodeIdp;
    transitivity; apply coerceβ; apply decodeIdp
  end

  hott corollary coerceComRev (p : Path A a b) : coerce (Path A · b) p p = refl b :=
  begin transitivity; apply ap (coerce _ · _); symmetry; apply decodeEncode; apply coerceComRevDecode end
end

section
  variable {A : Type u} {a b : A} (p : Path A a b)

  hott corollary coml : com (refl a) p = p := by apply coerceRefl
  hott corollary comr : com p (refl b) = p := by apply coerceβ
end

section
  variable {A : Type u} {B : A → Type v} {a b : A}

  hott lemma coerceDecode (p : a = b) (u : B a) : transport B p u = coerce B (decode p) u :=
  begin induction p; symmetry; transitivity; apply ap (coerce B · _); apply decodeIdp; apply coerceβ end

  hott corollary transportEncode (p : Path A a b) (u : B a) : transport B (encode p) u = coerce B p u :=
  begin transitivity; apply coerceDecode; apply ap (coerce _ · _); apply decodeEncode end
end

hott definition meet {A : Type u} {a b : A} (p : Path A a b) : LineP (λ i, Path A a (p @ i)) :=
Interval.ind (refl a) p
(begin
  apply Id.trans; apply Equiv.transportComp; transitivity; apply ap (transport _ · _);
  apply Interval.recβrule; transitivity; apply transportEncode; apply coerceRefl
end)

hott definition join {A : Type u} {a b : A} (p : Path A a b) : LineP (λ i, Path A (p @ i) b) :=
Interval.ind p (refl b)
(begin
  apply Id.trans; apply Equiv.transportComp (Path A · b); transitivity; apply ap (transport _ · _);
  apply Interval.recβrule; transitivity; apply transportEncode; apply coerceComRev
end)

/-
This doesn’t pass typechecking.

hott definition J {A : Type u} {a : A} {C : Π (b : A), Path A a b → Type u}
  (h : C a (refl a)) (b : A) (p : Path A a b) : C b (<i> p @ i) :=
coe 0 1 (λ i, C (p @ i) (connAnd p i)) h i₁

hott definition J {A : Type u} {a : A} {C : Π (b : A), Path A a b → Type u}
  (h : C a (refl a)) (b : A) (p : Path A a b) : C b (<i> p @ i) :=
transport (<i> C (p @ i) (<j> p @ i ∧ j)) h
-/

hott definition J {A : Type u} {a : A} (C : Π b, Path A a b → Type v)
  (H : C a (refl a)) {b : A} (p : Path A a b) : C b p :=
trans (<i> C (p @ i) (meet p i)) H

end Path

hott definition PathP (σ : I → Type u) (a : σ 0) (b : σ 1) :=
Path (σ 1) (transport σ seg a) b

hott definition PathP.lam (σ : I → Type u) (f : Π i, σ i) : PathP σ (f 0) (f 1) :=
Path.lam (Interval.elim (apd f seg))

end GroundZero.Cubical
