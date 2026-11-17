import ZInQKernel.OneProof.H.TailQ

/-!
Private post-algebraization wiring prototype. These are conditional tail lemmas:
they assume an actual algebraic graph object and an algebraic projection
isomorphism. They neither supply those objects nor prove GAGAMorphism.
All point carriers are the original identity-embedding CPts/cptObj carriers.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (CPts cptObj)

set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bGraphScout

/-- Extract the actual scheme morphism from a concrete graph and its projection isomorphism.
The hypothesis is point matching on that graph, not an assumed algebraic map A→B. -/
theorem exists_scheme_realization_of_concrete_graphIso (A B : AbVar ℂ)
    (G : Over (Spec (.of ℂ))) (p : G ⟶ A.X) (q : G ⟶ B.X) [IsIso p]
    (F : CPts A (RingHom.id ℂ) → CPts B (RingHom.id ℂ))
    (hgraph : ∀ t : cptObj (RingHom.id ℂ) ⟶ G, F (t ≫ p) = t ≫ q) :
    ∃ f : A.X ⟶ B.X, ∀ P : CPts A (RingHom.id ℂ), F P = P ≫ f := by
  refine ⟨inv p ≫ q, ?_⟩
  intro P
  have h := hgraph (P ≫ inv p)
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using h

/-- The exact pointwise conclusion of unchanged TailQ.GAGAMorphism follows by substitution,
AFTER the concrete algebraic graph and projection isomorphism have been supplied. -/
theorem exact_gagaWitness_of_concrete_graphIso (A B : AbVar ℂ) (g : ℕ)
    (Λ : Submodule ℤ (Fin g → ℂ))
    (φ : BPAnalytic.Torus Λ ≃+ Additive (CPts A (RingHom.id ℂ)))
    (ψ : (Fin g → ℂ) → CPts B (RingHom.id ℂ))
    (F : CPts A (RingHom.id ℂ) → CPts B (RingHom.id ℂ))
    (hF : ∀ z, F (Additive.toMul (φ (BPAnalytic.proj Λ z))) = ψ z)
    (G : Over (Spec (.of ℂ))) (p : G ⟶ A.X) (q : G ⟶ B.X) [IsIso p]
    (hgraph : ∀ t : cptObj (RingHom.id ℂ) ⟶ G, F (t ≫ p) = t ≫ q) :
    ∃ f : A.X ⟶ B.X, ∀ z,
      ψ z = Additive.toMul (φ (BPAnalytic.proj Λ z)) ≫ f := by
  obtain ⟨f, hf⟩ := exists_scheme_realization_of_concrete_graphIso A B G p q F hgraph
  exact ⟨f, fun z => (hF z).symm.trans (hf _)⟩

end ZInQ.Contrib.CloudB3W17bGraphScout
