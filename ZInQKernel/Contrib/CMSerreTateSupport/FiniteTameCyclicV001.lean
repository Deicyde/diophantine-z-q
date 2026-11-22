import ZInQKernel.Contrib.CMSerreTateSupport.DiscreteExtensionV003
import ZInQKernel.Contrib.CMSerreTateSupport.TameCyclicV002

/-!
# Inertia modulo wild inertia is cyclic over a finite extension of a discretely valued field

Combines discreteness of a valuation ring of a finite extension of a DVR-valued field with the
tame character: for a finite group of automorphisms satisfying the inertia conditions, the
kernel of the tame character is exactly its set of wild elements and the quotient is cyclic.
-/

noncomputable section
set_option autoImplicit false

namespace WildTameCharacter

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

theorem tame_quotient_cyclic_of_finiteDimensional [FiniteDimensional K M]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring M) (hw : w.comap (algebraMap K M) = O)
    (G : Subgroup (M ≃ₐ[K] M)) [Finite G]
    (hG : ∀ σ ∈ G, Preserves w σ ∧ ∀ u : M, w.valuation u = 1 → Cong w (σ u) u) :
    ∃ (π : M) (hπ0 : π ≠ 0), IsCyclic (G ⧸ (tameCharacter G hG hπ0).ker) ∧
      ∀ σ : G, σ ∈ (tameCharacter G hG hπ0).ker ↔ IsWild w (σ : M ≃ₐ[K] M) := by
  obtain ⟨π, hπ0, hπ⟩ := exists_uniformizer_of_finiteDimensional O w hw
  exact ⟨π, hπ0, tameQuotient_isCyclic G hG hπ0, mem_ker_tameCharacter_iff G hG hπ0 hπ⟩

end WildTameCharacter
