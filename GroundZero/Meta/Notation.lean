import Lean.Parser import Lean.Parser.Command
import Lean.Elab.Command import Lean.PrettyPrinter
import Lean.Elab.DeclUtil

import Lean.Elab.PreDefinition

open Lean.Parser Lean.Parser.Term Lean.Elab.Command
open Lean.PrettyPrinter.Delaborator

namespace GroundZero.Meta.Notation

open Lean in def delabCustomSort (t₀ : Delab) (t : Syntax.Level → Delab) : Delab :=
whenPPOption Lean.getPPNotation do {
  let ε ← SubExpr.getExpr; let n := ε.constLevels!.get! 0;
  if n.isZero then t₀ else t (n.quote max_prec)
}

@[app_unexpander Nat.succ]
def natSuccUnexpander : Lean.PrettyPrinter.Unexpander
| `($_ $n) => `($n + 1)
| _        => throw ()

@[app_unexpander Eq]
def revertDefaultEq : Lean.PrettyPrinter.Unexpander
| `($t $a $b) => `($t $a $b)
| _           => throw ()

@[delab sort]
def revertDefaultProp : Delab := do {
  match (← delabSort) with
  | `(Prop) => `(Sort 0)
  | stx     => return stx
}

macro "variables " vs:(ppSpace bracketedBinder)* : command => `(variable $vs*)

syntax "Π " many1(ppSpace (binderIdent <|> bracketedBinder)) ", " term : term
macro_rules | `(Π $xs*, $y) => `(∀ $xs*, $y)

-- https://github.com/leanprover-community/mathlib4/blob/f8593acbc38a592e6eeda6ce0d26383798de1b32/Mathlib/Util/Delaborators.lean#L79-L90
@[delab forallE]
def delabPi : Delab := whenPPOption Lean.getPPNotation do {
  match (← delabForall) with
  | `($group:bracketedBinder → Π $groups*, $body) => `(Π $group $groups*, $body)
  | `($group:bracketedBinder → $body)             => `(Π $group, $body)
  | stx                                           => pure stx
}

macro "λ " xs:(ppSpace funBinder)+ ", " f:term : term => `(fun $xs* => $f)

@[delab lam]
def delabLambda : Delab := whenPPOption Lean.getPPNotation do {
  match (← delabLam) with
  | `(fun $group:funBinder => λ $groups:funBinder*, $body) => `(λ $group $groups*, $body)
  | `(fun $group:funBinder => $body)                       => `(λ $group, $body)
  | stx                                                    => pure stx;
}

section
  open Lean.TSyntax.Compat

  @[delab app.Sigma]
  def delabSig : Delab := whenPPOption Lean.getPPNotation do {
    match (← delabSigma) with
    | `($group:bracketedExplicitBinders × Σ $groups*, $body) => `(Σ $group:bracketedExplicitBinders $groups*, $body)
    | `($group:bracketedExplicitBinders × $body)             => `(Σ $group:bracketedExplicitBinders, $body)
    | stx                                                    => pure stx
  }
end

macro "begin " ts:sepBy(tactic, ";", "; ", allowTrailingSep) i:"end" : term =>
  `(by { $[($ts:tactic)]* }%$i)

declare_syntax_cat superscriptNumeral
syntax "⁰" : superscriptNumeral
syntax "¹" : superscriptNumeral
syntax "²" : superscriptNumeral
syntax "³" : superscriptNumeral
syntax "⁴" : superscriptNumeral
syntax "⁵" : superscriptNumeral
syntax "⁶" : superscriptNumeral
syntax "⁷" : superscriptNumeral
syntax "⁸" : superscriptNumeral
syntax "⁹" : superscriptNumeral

def parseSupNumeral : Lean.Syntax → Nat
| `(superscriptNumeral| ⁰) => 0
| `(superscriptNumeral| ¹) => 1
| `(superscriptNumeral| ²) => 2
| `(superscriptNumeral| ³) => 3
| `(superscriptNumeral| ⁴) => 4
| `(superscriptNumeral| ⁵) => 5
| `(superscriptNumeral| ⁶) => 6
| `(superscriptNumeral| ⁷) => 7
| `(superscriptNumeral| ⁸) => 8
| `(superscriptNumeral| ⁹) => 9
| _                        => 0

declare_syntax_cat subscriptNumeral
syntax "₀" : subscriptNumeral
syntax "₁" : subscriptNumeral
syntax "₂" : subscriptNumeral
syntax "₃" : subscriptNumeral
syntax "₄" : subscriptNumeral
syntax "₅" : subscriptNumeral
syntax "₆" : subscriptNumeral
syntax "₇" : subscriptNumeral
syntax "₈" : subscriptNumeral
syntax "₉" : subscriptNumeral

def parseSubNumeral : Lean.Syntax → Nat
| `(subscriptNumeral| ₀) => 0
| `(subscriptNumeral| ₁) => 1
| `(subscriptNumeral| ₂) => 2
| `(subscriptNumeral| ₃) => 3
| `(subscriptNumeral| ₄) => 4
| `(subscriptNumeral| ₅) => 5
| `(subscriptNumeral| ₆) => 6
| `(subscriptNumeral| ₇) => 7
| `(subscriptNumeral| ₈) => 8
| `(subscriptNumeral| ₉) => 9
| _                      => 0

def parseNumber (φ : Lean.Syntax → Nat) (stx : Array Lean.Syntax) :=
let ns := stx.reverse.mapIdx fun i s => φ s * (10 ^ i)
let n  := Array.foldl (· + ·) 0 ns
Lean.Syntax.mkNumLit (toString n)

def parseSupNumber := parseNumber parseSupNumeral
def parseSubNumber := parseNumber parseSubNumeral

declare_syntax_cat superscriptChar

syntax "ᵃ" : superscriptChar syntax "ᵇ" : superscriptChar
syntax "ᶜ" : superscriptChar syntax "ᵈ" : superscriptChar
syntax "ᵉ" : superscriptChar syntax "ᶠ" : superscriptChar
syntax "ᵍ" : superscriptChar syntax "ʰ" : superscriptChar
syntax "ⁱ" : superscriptChar syntax "ʲ" : superscriptChar
syntax "ᵏ" : superscriptChar syntax "ˡ" : superscriptChar
syntax "ᵐ" : superscriptChar syntax "ⁿ" : superscriptChar
syntax "ᵒ" : superscriptChar syntax "ᵖ" : superscriptChar
syntax "ʳ" : superscriptChar syntax "ˢ" : superscriptChar
syntax "ᵗ" : superscriptChar syntax "ᵘ" : superscriptChar
syntax "ᵛ" : superscriptChar syntax "ʷ" : superscriptChar
syntax "ˣ" : superscriptChar syntax "ʸ" : superscriptChar

syntax "ᴬ" : superscriptChar syntax "ᴮ" : superscriptChar
syntax "ᴰ" : superscriptChar syntax "ᴱ" : superscriptChar
syntax "ᴳ" : superscriptChar syntax "ᴴ" : superscriptChar
syntax "ᴵ" : superscriptChar syntax "ᴶ" : superscriptChar
syntax "ᴷ" : superscriptChar syntax "ᴸ" : superscriptChar
syntax "ᴹ" : superscriptChar syntax "ᴺ" : superscriptChar
syntax "ᴼ" : superscriptChar syntax "ᴾ" : superscriptChar
syntax "ᴿ" : superscriptChar syntax "ᵀ" : superscriptChar
syntax "ᵁ" : superscriptChar syntax "ⱽ" : superscriptChar
syntax "ᵂ" : superscriptChar

def parseSupChar : Lean.Syntax → Char
| `(superscriptChar| ᵃ) => 'a' | `(superscriptChar| ᵇ) => 'b'
| `(superscriptChar| ᶜ) => 'c' | `(superscriptChar| ᵈ) => 'd'
| `(superscriptChar| ᵉ) => 'e' | `(superscriptChar| ᶠ) => 'f'
| `(superscriptChar| ᵍ) => 'g' | `(superscriptChar| ʰ) => 'h'
| `(superscriptChar| ⁱ) => 'i' | `(superscriptChar| ʲ) => 'j'
| `(superscriptChar| ᵏ) => 'k' | `(superscriptChar| ˡ) => 'l'
| `(superscriptChar| ᵐ) => 'm' | `(superscriptChar| ⁿ) => 'n'
| `(superscriptChar| ᵒ) => 'o' | `(superscriptChar| ᵖ) => 'p'
| `(superscriptChar| ʳ) => 'r' | `(superscriptChar| ˢ) => 's'
| `(superscriptChar| ᵗ) => 't' | `(superscriptChar| ᵘ) => 'u'
| `(superscriptChar| ᵛ) => 'v' | `(superscriptChar| ʷ) => 'w'
| `(superscriptChar| ˣ) => 'x' | `(superscriptChar| ʸ) => 'y'
| `(superscriptChar| ᴬ) => 'A' | `(superscriptChar| ᴮ) => 'B'
| `(superscriptChar| ᴰ) => 'D' | `(superscriptChar| ᴱ) => 'E'
| `(superscriptChar| ᴳ) => 'G' | `(superscriptChar| ᴴ) => 'H'
| `(superscriptChar| ᴵ) => 'I' | `(superscriptChar| ᴶ) => 'J'
| `(superscriptChar| ᴷ) => 'K' | `(superscriptChar| ᴸ) => 'L'
| `(superscriptChar| ᴹ) => 'M' | `(superscriptChar| ᴺ) => 'N'
| `(superscriptChar| ᴼ) => 'O' | `(superscriptChar| ᴾ) => 'P'
| `(superscriptChar| ᴿ) => 'R' | `(superscriptChar| ᵀ) => 'T'
| `(superscriptChar| ᵁ) => 'U' | `(superscriptChar| ⱽ) => 'V'
| `(superscriptChar| ᵂ) => 'W' | _                     => 'A'

declare_syntax_cat subscriptChar

syntax "ₐ" : subscriptChar syntax "ₑ" : subscriptChar
syntax "ₕ" : subscriptChar syntax "ᵢ" : subscriptChar
syntax "ⱼ" : subscriptChar syntax "ₖ" : subscriptChar
syntax "ₗ" : subscriptChar syntax "ₘ" : subscriptChar
syntax "ₙ" : subscriptChar syntax "ₒ" : subscriptChar
syntax "ₚ" : subscriptChar syntax "ᵣ" : subscriptChar
syntax "ₛ" : subscriptChar syntax "ₜ" : subscriptChar
syntax "ᵤ" : subscriptChar syntax "ᵥ" : subscriptChar
syntax "ₓ" : subscriptChar

def parseSubChar : Lean.Syntax → Char
| `(subscriptChar| ₐ) => 'a' | `(subscriptChar| ₑ) => 'e'
| `(subscriptChar| ₕ) => 'h' | `(subscriptChar| ᵢ) => 'i'
| `(subscriptChar| ⱼ) => 'j' | `(subscriptChar| ₖ) => 'k'
| `(subscriptChar| ₗ) => 'l' | `(subscriptChar| ₘ) => 'm'
| `(subscriptChar| ₙ) => 'n' | `(subscriptChar| ₒ) => 'o'
| `(subscriptChar| ₚ) => 'p' | `(subscriptChar| ᵣ) => 'r'
| `(subscriptChar| ₛ) => 's' | `(subscriptChar| ₜ) => 't'
| `(subscriptChar| ᵤ) => 'u' | `(subscriptChar| ᵥ) => 'v'
| `(subscriptChar| ₓ) => 'x' | _                   => 'a'

def parseIdent (φ : Lean.Syntax → Char) (stx : Array Lean.Syntax) :=
String.mk (Array.map φ stx).toList |> Lean.Name.str Lean.Name.anonymous

def parseSubIdent := parseIdent parseSubChar
def parseSupIdent := parseIdent parseSupChar

declare_syntax_cat superscript
syntax (name := superscriptNumber) many1(superscriptNumeral) : superscript
syntax (name := superscriptIdent)  many1(superscriptChar)    : superscript

syntax:65 superscript:65 "⁺" superscript:66 : superscript
syntax:65 superscript:65 "⁻" superscript:66 : superscript
syntax:max "⁽" superscript "⁾"              : superscript

partial def parseSuperscript : Lean.Syntax → Lean.MacroM Lean.Term
| `(superscriptNumber| $stx*)   => return parseSupNumber stx
| `(superscriptIdent| $stx*)    => return Lean.mkIdent (parseSupIdent stx)
| `(superscript| $stx₁ ⁺ $stx₂) => do `(HAdd.hAdd $(← parseSuperscript stx₁) $(← parseSuperscript stx₂))
| `(superscript| $stx₁ ⁻ $stx₂) => do `(HSub.hSub $(← parseSuperscript stx₁) $(← parseSuperscript stx₂))
| `(superscript| ⁽$stx⁾)        => parseSuperscript stx
| stx                           => Lean.Macro.throwError "invalid superscript"

declare_syntax_cat subscript
syntax (name := subscriptNumber) many1(subscriptNumeral) : subscript
syntax (name := subscriptIdent)  many1(subscriptChar)    : subscript

syntax:65 subscript:65 "₊" subscript:66 : subscript
syntax:65 subscript:65 "₋" subscript:66 : subscript
syntax:max "₍" subscript "₎"            : subscript

partial def parseSubscript : Lean.Syntax → Lean.MacroM Lean.Term
| `(subscriptNumber| $stx*)   => return parseSubNumber stx
| `(subscriptIdent| $stx*)    => return Lean.mkIdent (parseSubIdent stx)
| `(subscript| $stx₁ ₊ $stx₂) => do `(HAdd.hAdd $(← parseSubscript stx₁) $(← parseSubscript stx₂))
| `(subscript| $stx₁ ₋ $stx₂) => do `(HSub.hSub $(← parseSubscript stx₁) $(← parseSubscript stx₂))
| `(subscript| ₍$stx₎)        => parseSubscript stx
| stx                         => Lean.Macro.throwError "invalid subscript"

section
  open Lean

  variable {M : Type → Type} [Monad M] [MonadError M] [MonadQuotation M]

  def delabSupNumeral : Nat → M Syntax
  | 0 => `(superscriptNumeral| ⁰)
  | 1 => `(superscriptNumeral| ¹)
  | 2 => `(superscriptNumeral| ²)
  | 3 => `(superscriptNumeral| ³)
  | 4 => `(superscriptNumeral| ⁴)
  | 5 => `(superscriptNumeral| ⁵)
  | 6 => `(superscriptNumeral| ⁶)
  | 7 => `(superscriptNumeral| ⁷)
  | 8 => `(superscriptNumeral| ⁸)
  | 9 => `(superscriptNumeral| ⁹)
  | _ => throwError "invalid numeral"

  def mkSuperscriptNumber (si : SourceInfo) :=
  λ stx => Lean.Syntax.node si `GroundZero.Meta.Notation.superscriptNumber #[stx]

  def mkManyNumeral (si : SourceInfo) :=
  Syntax.node si `null

  def mkSupNumeralOfDigits (si : SourceInfo) (xs : Array Nat) : M Syntax :=
  mkSuperscriptNumber si <$> mkManyNumeral si <$> xs.mapM delabSupNumeral

  def revDigitsOf : Nat → List Nat
  | Nat.zero   => []
  | Nat.succ k => (Nat.succ k % 10) :: revDigitsOf (Nat.succ k / 10)

  def digitsOf : Nat → List Nat
  | 0 => [0]
  | n => (revDigitsOf n).reverse

  def mkSupNumeral (stx : Syntax) (n : Nat) : M (TSyntax `superscript) :=
  TSyntax.mk <$> mkSupNumeralOfDigits stx.getHeadInfo (digitsOf n).toArray
end

namespace Record
  open Lean

  def expandBinderIdent : Syntax → CommandElabM Name
  | `(Lean.binderIdent| $i:ident) => return i.getId
  | stx                           => throwErrorAt stx "expected ident"

  def expandBEBinder : Syntax → TSyntax `term × TSyntaxArray `Lean.binderIdent
  | `(bracketedExplicitBinders| ($[$xs]* : $t)) => (t, xs)
  | _                                           => default

  def withImplicits {α : Type} (xs : Array Expr) (k : MetaM α) : MetaM α :=
  do {
    let mut lctx ← getLCtx;
    for x in xs do {
      if (lctx.get! x.fvarId!).binderInfo.isExplicit then {
        lctx := lctx.setBinderInfo x.fvarId! BinderInfo.implicit;
      }
    }
    Meta.withLCtx' lctx k
  }

  def declAccessor (tname fname : Name) (t e : Expr) (lparams : List Name) : Elab.Command.CommandElabM Unit :=
  do {
    let bvar ← Elab.Term.mkFreshBinderName;

    let lam ← liftTermElabM <|
      Meta.forallTelescope t λ xs _ =>
      do mkAppN (mkConst tname (lparams.map Level.param)) xs
      |> (mkLambda bvar BinderInfo.default · e)
      |> Meta.mkLambdaFVars xs
      |> withImplicits xs;

    let typ ← liftTermElabM (Meta.inferType lam);
    Elab.Command.liftCoreM <| addAndCompile <| Declaration.defnDecl {
      name        := tname ++ fname,
      levelParams := lparams,
      type        := typ,
      value       := lam,
      hints       := ReducibilityHints.abbrev,
      safety      := DefinitionSafety.safe
    }
  }

  abbrev sigfst := mkProj ``Sigma 0
  abbrev sigsnd := mkProj ``Sigma 1

  elab "record " id:declId sig:optDeclSig " :=" ppSpace fields:(ppSpace bracketedExplicitBinders)+ : command =>
  do {
    unless (fields.size > 0) do throwErrorAt id "empty record is disallowed";

    let (e, is) := expandBEBinder fields.back!;

    let term ← if is.size > 1 then `(Σ $(fields.pop)* ($is.pop* : $e), $e)
                              else `(Σ $(fields.pop)*, $e);
    elabCommand (← `(def $id $sig := $term));
    if (← get).messages.hasErrors then return;

    let ns ← getCurrNamespace;
    let tname := ns ++ (id.raw.getArg 0).getId;

    let ci ← getConstInfo tname;

    let ids ← fields.flatMapM λ stx =>
      Array.mapM expandBinderIdent
        (expandBEBinder stx).2;

    let mut acc := mkBVar 0;
    for ident in ids.pop do {
      declAccessor tname ident ci.type (sigfst acc) ci.levelParams;
      acc := sigsnd acc;
    }
    declAccessor tname ids.back! ci.type acc ci.levelParams
  }
end Record

namespace Defeq
  open Lean

  def elabTypeSpec {ks : SyntaxNodeKinds} :=
  Option.mapM (λ (stx : TSyntax ks), Elab.Term.elabType stx.raw[1])

  elab "#success " σ₁:term tag:" ≡ " σ₂:term τ:(typeSpec)? : command =>
  Elab.Command.runTermElabM fun _ => do {
    let T  ← elabTypeSpec τ;
    let τ₁ ← Elab.Term.elabTermEnsuringType σ₁ T;
    let τ₂ ← Elab.Term.elabTermEnsuringType σ₂ T;

    Elab.Term.synthesizeSyntheticMVarsNoPostponing;
    let τ₁ ← Elab.Term.levelMVarToParam (← instantiateMVars τ₁);
    let τ₂ ← Elab.Term.levelMVarToParam (← instantiateMVars τ₂);

    unless (← Meta.isDefEqGuarded τ₁ τ₂) do throwErrorAt tag s!"{← Meta.ppExpr τ₁} ≠ {← Meta.ppExpr τ₂}"
  }

  elab "#failure " σ₁:term tag:" ≡ " σ₂:term τ:(typeSpec)? : command =>
  Elab.Command.runTermElabM fun _ => do {
    let T  ← elabTypeSpec τ;
    let τ₁ ← Elab.Term.elabTermEnsuringType σ₁ T;
    let τ₂ ← Elab.Term.elabTermEnsuringType σ₂ T;

    Elab.Term.synthesizeSyntheticMVarsNoPostponing;
    let τ₁ ← Elab.Term.levelMVarToParam (← instantiateMVars τ₁);
    let τ₂ ← Elab.Term.levelMVarToParam (← instantiateMVars τ₂);

    if (← Meta.isDefEqGuarded τ₁ τ₂) then throwErrorAt tag s!"{← Meta.ppExpr τ₁} ≡ {← Meta.ppExpr τ₂}"
  }
end Defeq

end GroundZero.Meta.Notation
