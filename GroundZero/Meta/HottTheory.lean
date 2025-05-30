import Lean.Elab

open Lean.Parser
open Lean.Parser.Command
open Lean Lean.Elab Lean.Elab.Command

/-
  Original implementation:
  https://github.com/gebner/hott3/blob/master/src/hott/init/meta/support.lean
-/

universe u v w

macro "run_cmd " σs:doSeq : command => `(#eval show CommandElabM Unit from do $σs)

section
  variable {A : Type} {M : Type → Type}

  def Lean.Expr.forConstsM [Monad M] (e : Expr) (f : Name → M Unit) : M Unit :=
  e.foldConsts (pure ()) (λ n eff => do { f n; eff })
end

def Lean.ConstantInfo.isAxiomInfo : ConstantInfo → Bool
| .axiomInfo _ => true
| _            => false

/--
  Dummy type used to track axioms inconsistent with Lean by default (i.e. univalence).

  HoTT checker rules out singleton elimination and some other principles at all
  allowing us to use these axioms safely, but without special track it remains possible
  to prove `False` *outside* of HoTT scope (nevertheless, leaving HoTT scope still consistent).
  This is why we are adding additional hypothesis `[GroundZero]` to each such axiom
  so that it becomes impossible to derive contradiction (we believe) without it,
  thus making *both* (HoTT and non-HoTT) scopes consistent (we believe).

  To be convenient to use, `[GroundZero]` instance is automatically added
  to the scope variables of an each HoTT definition as well as to the parameters
  of an each `hott axiom` so that HoTT-related axiom can be used under HoTT scope
  almost the same way as ordinary axiom in the ordinary scope
  (except for the need to write sometimes additional “_”).
-/
@[class] axiom GroundZero : Type

namespace GroundZero.Meta.HottTheory

def typeOf (c : Name) : MetaM Expr := do {
  let some info := (← getEnv).constants.find? c
    | throwError "unknown identifier “{c}”";
  return info.type
}

def isProof (e : Expr) : MetaM Bool :=
Expr.isProp <$> Meta.inferType e

def hasLargeElim (type : Name) : MetaM Bool := do {
  let typeFormerIsProp ← Meta.forallTelescopeReducing (← typeOf type) (λ xs e => return Expr.isProp e);
  let elimIsProp ← Meta.forallTelescopeReducing (← typeOf (type ++ `rec)) (λ xs e => isProof e);
  return (typeFormerIsProp ∧ ¬elimIsProp)
}

section
  @[inline] def guardb {f : Type → Type u} [Alternative f] (b : Bool) : f Unit :=
  if b then pure () else failure

  run_cmd { let xs := [``Eq, ``HEq, ``False, ``True, ``And, ``Iff, ``Acc, ``Subsingleton];
            liftTermElabM <| xs.forM (λ n => hasLargeElim n >>= guardb) }

  run_cmd { let ys := [``Or, ``Exists, ``Subtype, ``Quot];
            liftTermElabM <| ys.forM (λ n => hasLargeElim n >>= guardb ∘ not) }
end

def renderChain : List Name → String :=
String.intercalate " <- " ∘ List.map toString

def checkLargeElim (tag : Syntax) (chain : List Name) (name : Name) : MetaM Unit :=
do if (← hasLargeElim name) then throwErrorAt tag "uses large eliminator: {renderChain chain}"

initialize hottDecls : SimplePersistentEnvExtension Name NameSet ←
registerSimplePersistentEnvExtension {
  name          := `hottDecls
  addEntryFn    := NameSet.insert
  addImportedFn := mkStateFromImportedEntries NameSet.insert {}
}

initialize nothott   : TagAttribute ← registerTagAttribute `nothott "Marks a defintion as unsafe for HoTT"
initialize hottAxiom : TagAttribute ← registerTagAttribute `hottAxiom "(Potentially) unsafely marks a definition as safe for HoTT"

initialize prohibitedAxioms : SimpleScopedEnvExtension Name NameSet ←
registerSimpleScopedEnvExtension { addEntry := NameSet.insert, initial := NameSet.empty };

def unsafeDecls :=
[`Lean.ofReduceBool, `Lean.ofReduceNat, `Quot.lift, `Quot.ind, `Quot.rec, `Classical.choice]

def checked? (decl : Name) : MetaM Bool := do {
  let env         ← getEnv;
  let checked    := (hottDecls.getState env).contains decl;
  let markedSafe := hottAxiom.hasTag env decl;

  pure (checked ∨ markedSafe)
}

def checkNotNotHoTT (tag : Syntax) (env : Environment) (decl : Name) : MetaM Unit :=
do if nothott.hasTag env decl ∨ unsafeDecls.contains decl then
  throwErrorAt tag "marked as [nothott]: {decl}"

partial def checkDeclAux (chain : List Name) (tag : Syntax) (name : Name) : MetaM Unit := do {
  let checkExpr (e : Expr) := e.forConstsM λ n => checkDeclAux (n :: chain) tag n;

  let env ← getEnv;
  if ¬(← checked? name) then {
    checkNotNotHoTT tag env name;
    match env.find? name with
    | some (ConstantInfo.recInfo v)    => List.forM v.all (checkLargeElim tag chain)
    | some (ConstantInfo.opaqueInfo v) => checkExpr v.value
    | some info                        => info.value?.forM checkExpr
    | none                             => throwError "unknown identifier “{name}”"
  } else return ()
}

def checkDecl (tag : Syntax) (name : Name) := do {
  checkDeclAux [name] tag name;

  let env ← getEnv; let prohibited := prohibitedAxioms.getState env;
  if ¬prohibited.isEmpty then {
    let (_, s) := ((CollectAxioms.collect name).run env).run {};

    s.axioms.forM λ n => do if prohibited.contains n then
      throwErrorAt tag "“{n}” is prohibited in the current scope."
  }
}

def defTok := leading_parser
    "def "         <|> "definition " <|> "theorem "   <|> "lemma "
<|> "proposition " <|> "corollary "  <|> "principle " <|> "claim "
<|> "statement "   <|> "paradox "    <|> "remark "    <|> "exercise "

/-- `reducible` and `inline` attributes are automatically added to abbreviations. -/
def abbrevTok := leading_parser "abbrev " <|> "abbreviation "

/-- Checks declaration without modifying environment. -/
def exampleTok := leading_parser "example " <|> "counterexample "

/-- Adds axiom with an additional `[GroundZero]` hypothesis
    or adds given declaration and marks it as `[hottAxiom]`. -/
def axiomTok := leading_parser "axiom "

/-- Checks whether given declarations are consistent with HoTT. -/
def checkTok := leading_parser "check "

/--
  Prohibits usage of given axioms in the current scope.

  Motivated by:
  * https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/intuitionistic.20logic/near/224368423
  * https://github.com/leanprover-community/mathlib/issues/10954
-/
def prohibitTok := leading_parser "prohibit "

/--
  Adds opaque definition and checks it or marks it as `[hottAxiom]` if needed.
  Used to define higher constructors of HITs.
-/
def opaqueTok := leading_parser "opaque "

/--
  Provides an evidence of compatibility of the given declaration with HoTT environment.
  Correctness of implementation is leaved up to user.
-/
def implTok := leading_parser "implementation "

def declDef      := leading_parser ppIndent optDeclSig >> declVal >> optDefDeriving
def decl         := leading_parser (defTok <|> abbrevTok) >> declId >> declDef
def declExample  := leading_parser exampleTok >> declDef
def declCheck    := leading_parser checkTok >> Parser.many1 Parser.ident
def declProhibit := leading_parser prohibitTok >> Parser.many1 Parser.ident
def declAxiom    := leading_parser axiomTok >> declId >> ppIndent declSig >>
                    Parser.optional (declVal >> optDefDeriving)
def declOpaque   := leading_parser opaqueTok >> Parser.optional "axiom " >> declId >>
                    ppIndent declSig >> Parser.optional declValSimple
def declImpl     := leading_parser implTok >> Parser.ident >> Term.leftArrow >> Parser.ident

/--
  Adds declaration and throws an error whenever it uses singleton elimination and/or
  any other principle (i.e. global choice) inconsistent with HoTT.
-/
def hottPrefix := leading_parser "hott "

def hottDeclMods := leading_parser
  optional docComment >>
  optional Term.«attributes» >>
  optional visibility >>
  optional «unsafe» >>
  optional («partial» <|> «nonrec»)

@[command_parser] def hott :=
leading_parser hottDeclMods >> hottPrefix >> (decl <|> declExample <|> declCheck <|> declAxiom <|> declOpaque <|> declProhibit <|> declImpl)

def checkAndMark (tag : Syntax) (name : Name) : CommandElabM Unit := do {
  liftTermElabM (checkDecl tag name);
  modifyEnv (λ env => hottDecls.addEntry env name)
}

def markHoTTAxiom (name : Name) : CommandElabM Unit :=
liftTermElabM (Term.applyAttributes name #[{name := `hottAxiom}])

def axiomInstBinder := mkNode ``Term.instBinder #[mkAtom "[", mkNullNode, mkIdent ``GroundZero, mkAtom "]"]
def axiomBracketedBinderF : TSyntax ``Term.bracketedBinderF := ⟨axiomInstBinder.raw⟩

def withHoTTScope {A : Type} : CommandElabM A → CommandElabM A :=
withScope (λ scope => {scope with varDecls := scope.varDecls.insertAt! 0 axiomBracketedBinderF,
                                  varUIds  := scope.varUIds.insertAt!  0 Name.anonymous})

def defHoTT (tag declMods declId declDef : Syntax) : CommandElabM Name := do {
  let ns ← getCurrNamespace;
  let declName := ns ++ declId[0].getId;

  withHoTTScope <| declDef.setKind ``Command.definition
  |>.setArgs (Array.append #[mkAtom "def ", declId] declDef.getArgs)
  |> (mkNode ``Command.declaration #[declMods, ·])
  |> elabDeclaration;

  return declName
}

def defAndCheck (tag declMods declId declDef : Syntax) : CommandElabM Name := do {
  let declName ← defHoTT tag declMods declId declDef;
  if (← getEnv).contains declName then checkAndMark tag declName
  return declName
}

def abbrevAttrs : Array Attribute :=
#[{name := `inline}, {name := `reducible}]

@[command_elab «hott»] def elabHoTT : CommandElab :=
λ stx => do {
  let #[hottMods, _, cmd] := stx.getArgs | throwError "incomplete declaration";

  let #[commentMod, attrs, visibilityMod, unsafeMod, recMod] := hottMods.getArgs | throwError "invalid syntax";
  let mods := mkNode ``Command.declModifiers #[commentMod, attrs, visibilityMod, mkNode ``Command.«noncomputable» #[], unsafeMod, recMod];

  if cmd.isOfKind ``decl then do {
    let #[tok, declId, declDef] := cmd.getArgs | throwError "invalid declaration";
    let declName ← defAndCheck declId mods declId declDef;
    if tok.isOfKind ``abbrevTok then liftTermElabM (Term.applyAttributes declName abbrevAttrs)
  }

  if cmd.isOfKind ``declExample then withoutModifyingEnv do {
    let #[tok, declDef] := cmd.getArgs | throwError "invalid example";
    let declId := mkNode ``declId #[mkIdentFrom tok `_example, mkNullNode];
    discard (defAndCheck tok mods declId declDef)
  }

  if cmd.isOfKind ``declCheck then do {
    let #[_, decls] := cmd.getArgs | throwError "invalid “check” statement";
    decls.getArgs.forM (λ stx => resolveGlobalConstNoOverload stx >>= checkAndMark stx)
  }

  if cmd.isOfKind ``declAxiom then do {
    let #[_, declId, declSig, declDef] := cmd.getArgs | throwError "invalid “axiom” statement";

    if declDef.isNone then do {
      let modifiedSig := declSig.modifyArg 0 (·.modifyArgs (·.insertAt! 0 axiomInstBinder));
      cmd.setKind ``Command.«axiom»
      |>.setArgs #[mkAtom "axiom ", declId, modifiedSig]
      |> (mkNode ``Command.declaration #[mods, ·])
      |> elabDeclaration
    } else do {
      let optDecl := (declSig.setKind ``optDeclSig).modifyArg 1 (mkNullNode #[·]) ;
      let declName ← declDef.modifyArgs (·.insertAt! 0 optDecl)
                     |> defHoTT declId mods declId;
      markHoTTAxiom declName
    }
  }

  if cmd.isOfKind ``declOpaque then do {
    let #[tok, axiom?, declId, declSig, declVal] := cmd.getArgs | throwError "invalid “opaque” statement";

    withHoTTScope <| cmd.setKind ``Command.«opaque»
    |>.setArgs #[mkAtom "opaque ", declId, declSig, declVal]
    |> (mkNode ``Command.declaration #[mods, ·])
    |> elabDeclaration;

    let ns ← getCurrNamespace; let declName := ns ++ declId[0].getId;
    if axiom?.isNone then checkAndMark tok declName else markHoTTAxiom declName
  }

  if cmd.isOfKind ``declProhibit then do {
    let #[_, decls] := cmd.getArgs | throwError "invalid “prohibit” statement";

    let env ← getEnv;
    decls.getArgs.forM λ stx => do {
      let n ← resolveGlobalConstNoOverload stx;

      if ¬(env.constants.find! n).isAxiomInfo then
        throwErrorAt stx "“{n}” expected to be an axiom.";

      setEnv (prohibitedAxioms.addLocalEntry env n)
    }
  }

  if cmd.isOfKind ``declImpl then do {
    let #[_, implOfStx, _, implFnStx] := cmd.getArgs | throwError "invalid “implementation” statement";

    let implOfName ← resolveGlobalConstNoOverload implOfStx;
    let implFnName ← resolveGlobalConstNoOverload implFnStx

    -- see https://github.com/leanprover/lean4/blob/fcb30c269bdbca7eac75fc5c5d62841db3d2f592/src/Lean/Compiler/ImplementedByAttr.lean#L13-L30
    if implOfName = implFnName then {
      throwError "invalid `hott implementation` argument “{implOfStx}”, function cannot be implemented by itself"
    }

    let implOfDecl ← getConstInfo implOfName;
    let implFnDecl ← getConstInfo implFnName;

    unless implOfDecl.levelParams.length = implFnDecl.levelParams.length do {
      throwError "invalid `hott implementation` argument “{implFnStx}”, “{implFnStx}” has {implFnDecl.levelParams.length} universe level parameter(s), but “{implOfStx}” has {implOfDecl.levelParams.length}"
    }

    let implOfType := implOfDecl.type
    let implFnType ← implOfDecl.levelParams.map mkLevelParam
                     |> Core.instantiateTypeLevelParams implFnDecl
                     |> liftCoreM;

    unless ← liftTermElabM (Meta.isDefEq implOfType implFnType) do {
      throwError "invalid `hott implementation` argument “{implFnStx}”, “{implFnStx}” has type{indentExpr implFnType}\nbut “{implOfStx}” has type{indentExpr implOfType}"
    };

    checkAndMark implFnStx implFnName; modifyEnv (λ env => hottDecls.addEntry env implOfName)
  }
}

end GroundZero.Meta.HottTheory
