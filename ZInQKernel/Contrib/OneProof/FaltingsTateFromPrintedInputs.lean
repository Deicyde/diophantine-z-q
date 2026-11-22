import ZInQKernel.Contrib.OneProof.TateGraph
import ZInQKernel.Contrib.OneProof.TateRationalDescent
import ZInQKernel.Contrib.OneProof.FaltingsFromPrintedInputs

/-! # The integral Tate homomorphism theorem from three existing research inputs -/

noncomputable section
open PkgI3.AbVar
open scoped CategoryTheory.MonObj TensorProduct

namespace ZInQ.Contrib.TateFiniteApproximation

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

private theorem rational_ranges_for_subrepresentations {K : Type} [Field K] [NumberField K]
    (C : PkgI3.AbVar K) (hGR : SemistabAssembly.GaudronRemondThm14AnSS)
    (g : ℕ) (h : ℝ) (hd : C.dim = (g : WithBot ℕ∞)) (hh : SemistabAssembly.IsAnStableHeightSS C h)
    (U : Subrepresentation (C.galRep ℓ)) :
    ∃ r, LinearMap.range (rationalEndAction ℓ C r) = U.toSubmodule := by
  obtain ⟨ξ, hξ⟩ := exists_endomorphism_with_rational_range (ℓ := ℓ) C hGR g h hd hh U.toSubmodule
    (fun σ x hx => U.apply_mem_toSubmodule σ hx)
  obtain ⟨r, hr⟩ := exists_rationalEndAction ℓ C ξ
  exact ⟨r, hr ▸ hξ⟩

set_option maxHeartbeats 1000000 in
/-- The integral Tate conjecture for two abelian varieties follows from the
isogeny bound and a stable height for their product. -/
theorem faltingsTate_at_of_isogeny_bound {K : Type} [Field K] [NumberField K]
    (A B : PkgI3.AbVar K)
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (g : ℕ) (height : ℝ) (hdim : (tateProduct A B).dim = (g : WithBot ℕ∞))
    (hheight : ZInQ.SemistabAssembly.IsAnStableHeightSS (tateProduct A B) height) :
    Function.Injective (tateHomZl ℓ A B) ∧
      Set.range (tateHomZl ℓ A B) = {f | IsGalEquivariant f} := by
  let C := tateProduct A B
  let := semisimple_endomorphism_algebra C ℚ_[ℓ]
  have HH := OneProof.HomFreeC.homFreeFiniteNF uniformizationLeafAll_proof
    CloudB3W16Torsion.mumfordTorsionAlgClosed_proof K A B
  refine ⟨HH.2.2.2 ℓ (Nat.cast_ne_zero.mpr hℓ.out.ne_zero),
    Set.Subset.antisymm (PkgI3.range_tateHomZl_subset A B ℓ) ?_⟩
  intro f hf
  apply tateHomZl_mem_range_of_rational ℓ A B f
  apply exists_tateHomQl_of_endomorphism_ranges ℓ A B
  · exact rational_ranges_for_subrepresentations ℓ C hGR g height hdim hheight
  · intro σ x
    have h : f ∘ₗ A.galT σ = B.galT σ ∘ₗ f := LinearMap.ext (hf σ)
    exact LinearMap.congr_fun (by
      change f.baseChange ℚ_[ℓ] ∘ₗ (A.galT σ).baseChange ℚ_[ℓ] =
        (B.galT σ).baseChange ℚ_[ℓ] ∘ₗ f.baseChange ℚ_[ℓ]
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h]) x

/-- The exact integral Faltings Tate statement, reduced to the isogeny bound
and existence of real stable heights. -/
theorem faltingsTate_of_isogeny_bound
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (hheight : ∀ (K : Type) [Field K] [NumberField K] (C : PkgI3.AbVar K),
      ∃ (g : ℕ) (height : ℝ), C.dim = (g : WithBot ℕ∞) ∧
        ZInQ.SemistabAssembly.IsAnStableHeightSS C height) : PkgI3.FaltingsTate := by
  intro K _ _ A B ℓ _
  obtain ⟨g, height, hg, hh⟩ := hheight K (tateProduct A B)
  exact faltingsTate_at_of_isogeny_bound ℓ A B hGR g height hg hh


/-- The exact r9b field follows from the same three printed inputs as r9a. -/
theorem faltingsTate_of_existing_leaves (hGR : SemistabAssembly.GaudronRemondThm14AnSS)
    (hD : GroupLawNeron.NeronSchemeExtensionDedekind) (hR : SZRaynaud.SilverbergZarhinThm35) :
    PkgI3.FaltingsTate :=
  faltingsTate_of_isogeny_bound hGR (stable_height_witness_of_existing_leaves hD hR)

end ZInQ.Contrib.TateFiniteApproximation
