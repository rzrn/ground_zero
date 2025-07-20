import GroundZero.Algebra.Group.Homotopy
import GroundZero.HITs.Circle

open GroundZero.HITs.Interval
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types.Id
open GroundZero.Theorems
open GroundZero.Types

namespace GroundZero
namespace HITs

universe u v w

namespace HigherSphere
  open GroundZero.HITs.Suspension (north south merid σ suspΩ)
  open GroundZero.Proto (idfun)

  hott definition base : Π {n : ℕ}, Sⁿ
  | Nat.zero   => false
  | Nat.succ _ => north

  hott definition diag : Π (n : ℕ), Ω¹(S¹) → Ωⁿ⁺¹(Sⁿ⁺¹)
  | Nat.zero   => idfun
  | Nat.succ n => suspΩ ∘ diag n

  hott definition surf (n : ℕ) : Ωⁿ⁺¹(Sⁿ⁺¹) :=
  diag n Circle.loop

  hott definition rec (B : Type u) (b : B) : Π (n : ℕ), Ωⁿ⁺¹(B, b) → Sⁿ⁺¹ → B
  | Nat.zero   => Circle.rec b
  | Nat.succ n => λ ε, Suspension.rec b b (rec (b = b) (idp b) n ε)

  hott theorem recβrule₁ {B : Type u} (b : B) : Π {n : ℕ} (α : Ωⁿ⁺¹(B, b)), rec B b n α base = b
  | Nat.zero,   _ => idp _
  | Nat.succ _, _ => idp _

  hott lemma σComApRec {B : Type u} (b : B) (n : ℕ) (ε : Ωⁿ⁺²(B, b)) :
    ap (rec B b (n + 1) ε) ∘ σ ~ rec (b = b) (idp b) n ε :=
  begin
    intro x; transitivity; apply mapFunctoriality;
    transitivity; apply bimap; apply Suspension.recβrule;
    transitivity; apply Id.mapInv; apply ap;
    apply Suspension.recβrule; transitivity; apply ap (_ ⬝ ·);
    apply ap; apply recβrule₁; apply Id.rid
  end

  hott theorem recβrule₂ {B : Type u} (b : B) : Π (n : ℕ) (α : Ωⁿ⁺¹(B, b)),
    conjugateΩ (recβrule₁ b α) (apΩ (rec B b n α) (surf n)) = α
  | Nat.zero,   _ => Circle.recβrule₂ _ _
  | Nat.succ n, _ =>
  begin
    show apΩ (ap _) (conjugateΩ _ _) = _;
    transitivity; apply apConjugateΩ; transitivity; apply ap (conjugateΩ _);
    transitivity; symmetry; apply comApΩ _ σ; apply apWithHomotopyΩ;
    apply σComApRec; transitivity; symmetry; apply conjugateTransΩ;
    transitivity; apply ap (conjugateΩ _); symmetry; apply conjugateRevRightΩ;
    apply recβrule₁; transitivity; symmetry; apply conjugateTransΩ;
    transitivity; apply ap (conjugateΩ _); apply recβrule₂ _ n; apply abelianΩ
  end

  hott lemma recConjugateΩ {A : Type u} {a b : A} (p : a = b)
    (n : ℕ) (α : Ωⁿ⁺¹(A, a)) : rec A b n (α^p) ~ rec A a n α :=
  begin induction p; reflexivity end

  hott theorem recComMapΩ {A : Type u} {B : Type v} (φ : A → B) (a : A) :
    Π (n : ℕ) (α : Ωⁿ⁺¹(A, a)), φ ∘ rec A a n α ~ rec B (φ a) n (apΩ φ α)
  | Nat.zero,   _ => Circle.recComMap _ _ _
  | Nat.succ n, α =>
  begin
    fapply Suspension.ind; reflexivity; reflexivity; intro x;
    apply Id.trans; apply Equiv.transportOverHmtpy;
    transitivity; apply ap (· ⬝ _); apply Id.rid;
    transitivity; apply bimap;
    { transitivity; apply mapInv; apply ap;
      transitivity; apply mapOverComp;
      transitivity; apply ap (ap φ); apply Suspension.recβrule;
      apply recComMapΩ (ap φ) _ n };
    { apply Suspension.recβrule };
    apply invComp
  end

  hott theorem idfunRecΩ : Π (n : ℕ), rec Sⁿ⁺¹ base n (surf n) ~ idfun
  | Nat.zero   => Circle.map.nontrivialHmtpy
  | Nat.succ n =>
  begin
    fapply Suspension.ind; reflexivity; apply merid base; intro x;
    apply Id.trans; apply Equiv.transportOverHmtpy;
    transitivity; apply ap (· ⬝ _); apply Id.rid;
    transitivity; apply bimap;
    { transitivity; apply mapInv; apply ap;
      transitivity; apply Suspension.recβrule;
      transitivity; apply @recConjugateΩ (base = base);
      transitivity; symmetry; apply recComMapΩ σ;
      apply ap σ; apply idfunRecΩ n };
    { apply idmap };
    apply Suspension.σRevComMerid
  end

  hott lemma σRecΩ (n : ℕ) : rec (@Id Sⁿ⁺² base base) (idp base) n (surf (n + 1)) ~ σ :=
  begin
    transitivity; apply recConjugateΩ;
    transitivity; symmetry; apply recComMapΩ σ;
    apply Homotopy.rwhs; apply idfunRecΩ
  end

  hott theorem mapExtΩ {B : Type u} : Π (n : ℕ) (φ : Sⁿ⁺¹ → B), rec B (φ base) n (apΩ φ (surf n)) ~ φ
  | Nat.zero   => λ _ _, (Circle.mapExt _ _)⁻¹
  | Nat.succ n =>
  begin
    intro φ; fapply Suspension.ind; reflexivity; apply ap φ (merid base);
    intro x; apply Id.trans; apply Equiv.transportOverHmtpy;
    transitivity; apply ap (· ⬝ _); transitivity; apply Id.rid;
    transitivity; apply mapInv; transitivity; apply ap;
    transitivity; apply Suspension.recβrule; dsimp [apΩ];
    symmetry; apply recComMapΩ (ap φ) (idp base);
    symmetry; apply mapInv φ; transitivity; symmetry;
    apply mapFunctoriality φ; apply ap (ap φ);
    transitivity; apply ap (·⁻¹ ⬝ _); apply σRecΩ;
    apply Suspension.σRevComMerid
  end

  hott corollary constRecΩ (n : ℕ) : rec Sⁿ⁺¹ base n (idΩ base (n + 1)) ~ (λ _, base) :=
  begin
    transitivity; apply Homotopy.Id; apply ap (rec Sⁿ⁺¹ base n); symmetry;
    apply constmapΩ (n + 1) (surf n); apply mapExtΩ n (λ _, base)
  end

  -- Direct proof of universal property of Sⁿ⁺¹.
  hott theorem mapLoopEqvΩ {B : Type u} : Π (n : ℕ), (Sⁿ⁺¹ → B) ≃ (Σ (x : B), Ωⁿ⁺¹(B, x))
  | Nat.zero   => Circle.mapLoopEqv
  | Nat.succ n =>
  begin
    fapply Sigma.mk; intro φ; exact ⟨φ base, apΩ φ (surf (n + 1))⟩; apply Qinv.toBiinv;
    fapply Sigma.mk; intro w; exact rec B w.1 (n + 1) w.2; apply Prod.mk;
    { intro; fapply Sigma.prod; reflexivity; apply recβrule₂ };
    { intro φ; apply Theorems.funext; apply mapExtΩ }
  end

  hott definition ofMap {A : Type u} {a : A} {n : ℕ} : Map⁎ ⟨Sⁿ⁺¹, base⟩ ⟨A, a⟩ → Ωⁿ⁺¹(A, a) :=
  λ φ, conjugateΩ φ.2 (apΩ φ.1 (surf n))

  hott definition toMap {A : Type u} {a : A} {n : ℕ} : Ωⁿ⁺¹(A, a) → Map⁎ ⟨Sⁿ⁺¹, base⟩ ⟨A, a⟩ :=
  λ ε, ⟨rec A a n ε, recβrule₁ a ε⟩

  hott theorem loopSphere {A : Type u} (a : A) : Π (n : ℕ), Map⁎ ⟨Sⁿ⁺¹, base⟩ ⟨A, a⟩ ≃ Ωⁿ⁺¹(A, a)
  | Nat.zero   => Circle.loopCircle a
  | Nat.succ n =>
  begin
    fapply Equiv.intro; exact ofMap; exact toMap;
    { intro ⟨φ, (H : φ base = a)⟩; induction H using J₁;
      fapply Sigma.prod; apply Theorems.funext; apply mapExtΩ;
      transitivity; apply transportOverContrMap; transitivity; apply Id.rid;
      transitivity; apply mapInv; transitivity; apply ap;
      transitivity; apply Theorems.mapToHapply; apply happly;
      apply Theorems.happlyFunext; reflexivity };
    { intro ε; apply recβrule₂ a (n + 1) ε }
  end

  hott definition indBias (n : ℕ) (B : Sⁿ⁺¹ → Type u) (b : B base) (ε : Ωⁿ⁺¹(B, b, surf n)) :=
  rec (Σ x, B x) ⟨base, b⟩ n (sigmaProdΩ (surf n) ε)

  hott example (n : ℕ) (B : Sⁿ⁺¹ → Type u) (b : B base)
    (ε : Ωⁿ⁺¹(B, b, surf n)) (x : Sⁿ⁺¹) : (indBias n B b ε x).1 = x :=
  begin
    transitivity; apply recComMapΩ;
    transitivity; apply ap (rec _ _ _ · _);
    apply apFstProdΩ; apply idfunRecΩ
  end

  -- this (longer) proof computes better than the previous one
  hott lemma indBiasPath : Π (n : ℕ) (B : Sⁿ⁺¹ → Type u)
    (b : B base) (ε : Ωⁿ⁺¹(B, b, surf n)), Π x, (indBias n B b ε x).1 = x
  | Nat.zero =>
  begin
    intro B b ε; fapply Circle.ind; reflexivity; apply Id.trans;
    transitivity; apply transportOverInvolution; apply ap (· ⬝ _);
    transitivity; apply Id.rid; transitivity; apply mapInv; apply ap;
    transitivity; apply mapOverComp;
    transitivity; apply ap (ap Sigma.fst);
    dsimp [indBias]; apply Circle.recβrule₂;
    apply Sigma.mapFstOverProd; apply invComp
  end
  | Nat.succ n =>
  begin
    intro B b ε; fapply Suspension.ind; reflexivity; exact merid base;
    intro x; apply Id.trans; apply transportOverInvolution;
    transitivity; apply ap (· ⬝ _); transitivity; apply Id.rid;
    transitivity; apply mapInv; apply ap;
    transitivity; apply mapOverComp;
    transitivity; apply ap (ap Sigma.fst); dsimp [indBias]; apply Suspension.recβrule;
    transitivity; apply recComMapΩ; transitivity; apply ap (rec _ _ _ · _);
    apply @apFstProdΩ Sⁿ⁺² B ⟨base, b⟩ (n + 2) (surf (n + 1)) ε;
    apply σRecΩ; apply Suspension.σRevComMerid
  end

  hott definition ind (n : ℕ) (B : Sⁿ⁺¹ → Type u) (b : B base) (ε : Ωⁿ⁺¹(B, b, surf n)) : Π x, B x :=
  λ x, transport B (indBiasPath n B b ε x) (indBias n B b ε x).2

  hott theorem indβrule₁ : Π (n : ℕ) (B : Sⁿ⁺¹ → Type u) (b : B base) (α : Ωⁿ⁺¹(B, b, surf n)), ind n B b α base = b
  | Nat.zero,   _, _, _ => idp _
  | Nat.succ _, _, _, _ => idp _

  hott definition mult {n : ℕ} {a b : Sⁿ⁺¹} (α : Ωⁿ⁺¹(Sⁿ⁺¹, a)) (β : Ωⁿ⁺¹(Sⁿ⁺¹, b)) : Ωⁿ⁺¹(Sⁿ⁺¹, rec Sⁿ⁺¹ a n α b) :=
  apΩ (rec Sⁿ⁺¹ a n α) β

  hott corollary recCompΩ {n : ℕ} {a b : Sⁿ⁺¹} (α : Ωⁿ⁺¹(Sⁿ⁺¹, a)) (β : Ωⁿ⁺¹(Sⁿ⁺¹, b)) :
    rec Sⁿ⁺¹ a n α ∘ rec Sⁿ⁺¹ b n β ~ rec Sⁿ⁺¹ (rec Sⁿ⁺¹ a n α b) n (mult α β) :=
  by apply recComMapΩ

  hott definition rotε {n : ℕ} : Π x, Ωⁿ⁺¹(∥Sⁿ⁺¹∥ₙ₊₁, x) :=
  Trunc.ind
    (ind n _ (apΩ Trunc.elem (surf n))
      (match n with
      | Nat.zero   => Equiv.transportOverHmtpy _ _ _ _ ⬝ ap (· ⬝ _ ⬝ _) (Id.mapInv _ _) ⬝
                      ap (· ⬝ apΩ Trunc.elem (surf Nat.zero)) (Id.invComp _)
      | Nat.succ n => loopOverHSet (λ _, hsetLoop (Trunc.uniq _) _)))
    (λ _, levelStableΩ _ (Trunc.uniq _))

  hott definition code {n : ℕ} : Sⁿ⁺² → Type :=
  rec Type ∥Sⁿ⁺¹∥ₙ₊₁ (n + 1)
    (conjugateΩ (uaidp ∥Sⁿ⁺¹∥ₙ₊₁)
                (apΩ ua (sigmaProdΩ (funextΩ idfun rotε)
                                    (loopOverProp (λ _, Equiv.biinvProp _)))))

  hott lemma codeHLevel {n : ℕ} : Π (x : Sⁿ⁺²), is-(n + 1)-type (code x) :=
  ind _ _ (Trunc.uniq _) (loopOverProp (λ _, ntypeIsProp _))

  hott definition encode {n : ℕ} : Π (x : Sⁿ⁺²), ∥base = x∥ₙ₊₁ → code x :=
  λ x, Trunc.rec (λ ε, transport code ε |base|ₙ₊₁) (codeHLevel x)
end HigherSphere

namespace Sphere
  open GroundZero.HITs.Suspension (σ)

  hott definition base : S² := HigherSphere.base

  hott definition surf : idp base = idp base :=
  HigherSphere.surf 1

  section
    variable {B : Type u} (b : B) (ε : idp b = idp b)

    hott definition rec : S² → B := HigherSphere.rec B b 1 ε

    hott corollary recβrule₁ : rec b ε base = b := idp b

    hott corollary recβrule₂ : ap² (rec b ε) surf = ε :=
    HigherSphere.recβrule₂ b 1 ε
  end

  hott definition cup : S¹ → S¹ → S² :=
  Circle.rec (λ _, base) (Theorems.funext σ)
end Sphere

namespace Glome
  hott definition base : S³ := HigherSphere.base

  hott definition surf : idp (idp base) = idp (idp base) :=
  HigherSphere.surf 2

  section
    variable {B : Type u} (b : B) (ε : idp (idp b) = idp (idp b))

    hott definition rec : S³ → B := HigherSphere.rec B b 2 ε

    hott corollary recβrule₁ : rec b ε base = b := idp b

    hott corollary recβrule₂ : ap³ (rec b ε) surf = ε :=
    HigherSphere.recβrule₂ b 2 ε
  end
end Glome

end HITs
end GroundZero
