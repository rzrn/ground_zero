import GroundZero.Structures

namespace GroundZero
universe u v w

namespace Types

inductive W {A : Type u} (B : A → Type v) : Type (max u v)
| sup : Π (a : A), (B a → W B) → W B

attribute [induction_eliminator] W.casesOn

open W (sup)

section
  open Lean Lean.Parser.Term Lean.TSyntax.Compat Lean.PrettyPrinter

  macro "W" xs:explicitBinders ", " y:term : term =>
  expandExplicitBinders ``W xs y

  open Lean.PrettyPrinter.Delaborator

  @[delab app.GroundZero.Types.W]
  def delabW : Delab := whenPPOption Lean.getPPNotation do {
    guard $ (← SubExpr.getExpr).getAppNumArgs == 2;

    SubExpr.withAppArg do {
      if (← SubExpr.getExpr).isLambda then {
        let t ← SubExpr.withBindingDomain delab;

        withBindingBodyUnusedName fun x =>
          do `(W ($x:ident : $t), $(← delab))
      } else {
        let b ← SubExpr.getExpr;
        let x ← getUnusedName `x b;
        let y ← delab (Expr.app b (mkFVar ⟨x⟩));
        `(W $(mkIdent x):ident, $y)
      }
    }
  }
end

end Types

namespace Types.W
  open Proto Types.Id Types.Equiv Structures HITs.Interval

  variables {A : Type u} {B : A → Type v}

  hott definition ind₂ {C : (W x, B x) → (W x, B x) → Type w}
    (c : Π (a₁ a₂ : A) (f₁ : B a₁ → W x, B x) (f₂ : B a₂ → W x, B x),
           (Π b₁ b₂, C (f₁ b₁) (f₂ b₂)) → C (sup a₁ f₁) (sup a₂ f₂)) :
    Π w₁ w₂, C w₁ w₂
  | sup a₁ f₁, sup a₂ f₂ => c a₁ a₂ f₁ f₂ (λ b₁ b₂, ind₂ c (f₁ b₁) (f₂ b₂))

  hott lemma isProp : prop A → prop (W x, B x) :=
  begin
    intro H; apply ind₂; intro a₁ a₂; induction H a₁ a₂; intro f₁ f₂ G;
    apply ap (sup a₁); apply Theorems.funext; intro; apply G
  end

  hott definition propDecode (H : prop A) : (W x, B x) → (Σ x, ¬(B x))
  | sup a f => ⟨a, λ b, let w := propDecode H (f b);
                        w.2 (transport B (H a w.1) b)⟩

  hott definition propEncode : (Σ x, ¬(B x)) → (W x, B x) :=
  λ w, sup w.1 (λ b, explode (w.2 b))

  hott lemma propEquivSig (H : prop A) : (W x, B x) ≃ (Σ x, ¬(B x)) :=
  begin
    apply propEquivLemma; apply isProp; exact H;
    apply sigProp; exact H; intro; apply notIsProp;
    exact propDecode H; exact propEncode
  end

  hott definition propDecodeDec (H : Π x, dec (B x)) : (W x, B x) → (Σ x, ¬(B x))
  | sup a f => Coproduct.elim (λ b, propDecodeDec H (f b)) (λ nb, ⟨a, nb⟩) (H a)

  hott definition propDecodeNeg : (W x, B x) → ¬(Π x, B x)
  | sup a f, g => propDecodeNeg (f (g a)) g

  hott lemma negDecode : ¬(W x, B x) → ¬(Σ x, ¬(B x)) :=
  λ nw w, nw (propEncode w)

  hott lemma negEncode : ¬(Σ x, ¬(B x)) → ¬(W x, B x) :=
  λ nw (sup a f), nw ⟨a, λ b, negEncode nw (f b)⟩

  hott theorem negEquiv : ¬(W x, B x) ≃ ¬(Σ x, ¬(B x)) :=
  propEquivLemma (λ _, notIsProp _) (λ _, notIsProp _) negDecode negEncode
end Types.W

end GroundZero
