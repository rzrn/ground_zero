import GroundZero.Structures
open GroundZero.Types.Equiv
open GroundZero.Structures
open GroundZero.Types.Id
open GroundZero.Types

/-
  See Appendix A in “On the homotopy groups of spheres in homotopy type theory”, Guillaume Brunerie.
  https://arxiv.org/abs/1606.05916

  Directed version is given in the “A Type-Theoretical Definition of Weak ω-Categories”, Eric Finster, Samuel Mimram.
  * https://arxiv.org/abs/1706.02866
  * https://github.com/ericfinster/catt.io
  * https://github.com/ericfinster/catt
  * https://github.com/smimram/catt
  * https://github.com/thibautbenjamin/catt
-/

universe u v

def Array.push₂ {A : Type u} (α : Array A) (x y : A) := (α.push x).push y
def Array.tail  {A : Type u} (α : Array A) := α.extract 1 α.size

namespace GroundZero

hott definition Con.bundle (A : Type u) : ℕ → Σ (X : Type (u + 1)), X → Type (u + 1)
| Nat.zero   => ⟨𝟏, λ _, 𝟏⟩
| Nat.succ n => ⟨Σ (w : (Con.bundle A n).1), (Con.bundle A n).2 w → Type⁎ u,
                 λ T, Σ (Δ : (Con.bundle A n).2 T.1) (y : (T.2 Δ).1), (T.2 Δ).2 = y⟩

/-- Type of *contractible contexts* used to define the coherence operations. -/
hott definition Con (A : Type u) (n : ℕ) :=
(Con.bundle A n).1

/-- Reflection of contractible context into our type theory. -/
hott definition Con.ref {A : Type u} {n : ℕ} (Γ : Con A n) :=
(Con.bundle A n).2 Γ

macro:max atomic("ǀ" noWs) Γ:term noWs "ǀ" : term => `(Con.ref $Γ)

-- Reflection of a contractible context is truly contractible.
hott lemma Con.contr (A : Type u) : Π (n : ℕ) (Γ : Con A n), contr ǀΓǀ
| Nat.zero,   _ => unitIsContr
| Nat.succ n, Γ => contrRespectsSigma (Con.contr A n Γ.1) (λ _, singl.contr _)

hott definition idcon (A : Type u) {n : ℕ} {Γ : Con A n} : ǀΓǀ :=
(Con.contr A n Γ).1

section
  variable {A : Type u}

  hott definition Con.nil : Con A 0      := ★
  hott definition Ref.nil : ǀ@Con.nil Aǀ := ★

  variable {n : ℕ} {Γ : Con A n}

  hott definition Con.cons (T : ǀΓǀ → Type u) (u : Π Δ, T Δ) : Con A (n + 1) :=
  ⟨Γ, λ Δ, ⟨T Δ, u Δ⟩⟩

  variable {T : ǀΓǀ → Type u} {u : Π Δ, T Δ}
  hott definition Ref.cons (Δ : ǀΓǀ) (x : T Δ) (p : u Δ = x) : ǀCon.cons T uǀ :=
  ⟨Δ, ⟨x, p⟩⟩
end

section
  variable {A : Type u} {n : ℕ} (ε : A → Con A n) (C : Π (a : A), ǀε aǀ → Type v) (c : Π (a : A), C a (idcon A))

  hott definition Coh : Π a Δ, C a Δ :=
  λ a Δ, transport (C a) ((Con.contr A n (ε a)).2 Δ) (c a)

  hott lemma cohβ (a : A) : Coh ε C c a (idcon A) = c a :=
  begin
    transitivity; apply ap (transport _ · _); show _ = idp _;
    apply propIsSet; apply contrImplProp; apply Con.contr; reflexivity
  end
end

section
  open Lean Lean.Elab

  abbrev natLit := mkLit ∘ Literal.natVal
  abbrev sigfst := mkProj ``Sigma 0
  abbrev sigsnd := mkProj ``Sigma 1

  elab tag:"coh " σs:many1(bracketedBinder) ", " σ:term : term => do {
    Term.elabBinders σs fun con => do {
      let C    ← Term.elabType σ;
      let lctx ← MonadLCtx.getLCtx;

      let mut tele := con.toList;
      let fv       := tele.head!;
      let fvdecl   := lctx.getFVar! fv
      let A        := fvdecl.type;

      let some l₁ := (← Meta.inferType A).sortLevel!.dec | throwErrorAt σs[0]! "expected to be a Type";
      let some l₂ := (← Meta.inferType C).sortLevel!.dec | throwErrorAt σ "expected to be a Type";

      let ref     := mkApp (mkConst ``Con.ref  [l₁]) A;
      let conCons := mkApp (mkConst ``Con.cons [l₁]) A;
      let refCons := mkApp (mkConst ``Ref.cons [l₁]) A;

      let mut Δ := mkApp (mkConst ``Con.nil [l₁]) A;
      let mut δ := mkApp (mkConst ``Ref.nil [l₁]) A;

      let mut k := 0;

      let mut fvs : Array Expr := #[];
      let mut evs : Array Expr := #[];

      tele := tele.tail!;

      while !tele.isEmpty do {
        if tele.length < 2 then throwErrorAt σs.back!
          "contractible context expected to be in the form “... (b : A) (p : u = b)”";

        let b₁ := tele.head!;
        let b₂ := tele.tail!.head!;
        let T  := (lctx.getFVar! b₁).type;
        let U  := (lctx.getFVar! b₂).type;

        unless (U.isAppOfArity ``GroundZero.Types.Id 3)
          do throwErrorAt σs[2 * k + 2]!
            "expected to be a path type";

        let #[_, u, y] := U.getAppArgs | unreachable!;
        unless (← Meta.isDefEq y b₁)
          do throwErrorAt σs[2 * k + 2]!
            "expected to be in the form “... = {← Meta.ppExpr b₁}”";

        let ρ' := mkApp2 ref (natLit k) Δ;
        let Δ' := mkLambda `Δ BinderInfo.default ρ' (Expr.replaceFVars T fvs evs);
        let u' := mkLambda `Δ BinderInfo.default ρ' (Expr.replaceFVars u fvs evs);

        δ := mkApp7 refCons (natLit k) Δ Δ' u' δ b₁ b₂;
        Δ := mkApp4 conCons (natLit k) Δ Δ' u';

        k := k + 1;

        evs := evs.map (·.instantiate #[sigfst (mkBVar 0)]);

        fvs := fvs.push₂ b₁ b₂;
        evs := evs.push₂ (sigfst (sigsnd (mkBVar 0))) (sigsnd (sigsnd (mkBVar 0)));

        tele := tele.tail!.tail!;
      }

      Meta.withNewBinderInfos #[(fvdecl.fvarId, BinderInfo.default)] do {
        let ρ := mkApp2 ref (natLit k) Δ;
        let C := (← instantiateMVars C).replaceFVars fvs evs;

        let idcon := mkApp3 (mkConst ``idcon [l₁]) A (natLit k) Δ;
        let apcoh := (← Meta.mkLambdaFVars #[fv] (mkLambda `Δ BinderInfo.default ρ C))
                     |> mkApp4 (mkConst ``Coh [l₁, l₂]) A (natLit k)
                               (← Meta.mkLambdaFVars #[fv] Δ);

        let idc ← Meta.mkForallFVars #[fv] (mkLet `Δ ρ idcon C);
        return (← mkApp3 apcoh (mkBVar (2 * k + 2)) (mkBVar (2 * k + 1)) δ
               |> Meta.mkLambdaFVars con.tail)
               |>.replaceFVar fv (mkBVar 0)
               |> mkLambda fvdecl.userName fvdecl.binderInfo fvdecl.type
               |> mkLambda `ε BinderInfo.default idc
      };
    }
  }
end

namespace Example
  hott definition rev {A : Type u} {a b : A} (p : a = b) : b = a :=
  (coh (a : A) (b : A) (p : a = b), b = a) idp a b p

  hott definition com {A : Type u} {a b c : A} (p : a = b) (q : b = c) : a = c :=
  (coh (a : A) (b : A) (p : a = b) (c : A) (q : b = c), a = c) idp a b p c q

  hott definition invol {A : Type u} {a b : A} (p : a = b) : p = rev (rev p) :=
  (coh {a : A} {b : A} (p : a = b), p = rev (rev p)) (λ x, idp (idp x)) p

  -- p⁻¹ is defined directly in terms of J rule
  hott remark revRev {A : Type u} {a b : A} (p : a = b) : rev p = p⁻¹ :=
  (coh {a : A} {b : A} (p : a = b), rev p = p⁻¹) (λ x, idp (idp x)) p

  hott definition lu {A : Type u} {a b : A} (p : a = b) : com (idp a) p = p :=
  (coh {a : A} {b : A} (p : a = b), com (idp a) p = p) (λ x, idp (idp x)) p

  hott definition ru {A : Type u} {a b : A} (p : a = b) : com p (idp b) = p :=
  (coh {a : A} {b : A} (p : a = b), com p (idp b) = p) (λ x, idp (idp x)) p

  hott definition assoc {A : Type u} {a b c d : A} (p : a = b) (q : b = c) (r : c = d) : p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r :=
  (coh {a : A} {b : A} (p : a = b) {c : A} (q : b = c) {d : A} (r : c = d), p ⬝ (q ⬝ r) = (p ⬝ q) ⬝ r) (λ x, idp (idp x)) p q r

  variable (A : Type u) (a : A)
  #success assoc (idp a) (idp a) (idp a) ≡ idp (idp a)
end Example

end GroundZero
