import GroundZero.Algebra.Group.Basic
open GroundZero.Types

namespace GroundZero.Algebra

namespace Group
  hott definition Aut.carrier (G : Group) := G ≅ G

  hott definition Aut (G : Group) : Group :=
  @Group.intro (G ≅ G) Iso.hset (λ φ ψ, Iso.trans ψ φ) Iso.symm (Iso.refl G.1)
    (λ ⟨f, ⟨f', e₁⟩⟩ ⟨g, ⟨g', e₂⟩⟩ ⟨h, ⟨h', e₂⟩⟩, Iso.ext (λ _, idp _))
    (λ ⟨f, ⟨f', e₁⟩⟩, Iso.ext (λ _, idp _))
    (λ ⟨f, ⟨(η₁, η₂), (⟨g, μ₁⟩, μ₂)⟩⟩, Iso.ext (λ _, μ₁ _))
end Group

end GroundZero.Algebra
