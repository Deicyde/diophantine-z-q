import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.MarkedAnalyticTransport

/-!
# Transport every entry of the original marked height witness

The field, dimension, determinant section, section index and all the squared norms
come from the given Néron model. The new section is its actual Hodge pullback.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open NumberField
open scoped CategoryTheory.MonObj Obj

namespace ZInQ.Contrib.IsogenyDegree

open ZInQ.DefFaltings ZInQ.H5Glue ZInQ.HeightGlue ZInQ.HeightDict
open ZInQ.HeightFix (IsPrintedMetricSq)
open ZInQ.R3Residual (IsAnMetricSq isAnMetricSq_iff)

variable {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
  {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The integral and analytic data in the live Néron-height witness give the
printed height data on the open model without changing the value of any term. -/
theorem markedHeightWitness_openIso (hT35 : ZInQ.LeafPush2.UniformizationExists)
    {g : ℕ} (hg : A.dim = (g : WithBot ℕ∞))
    (G N : GroupModel A L) (hN : N.IsNeronModel) (j : G.G ⟶ N.G)
    [IsMonHom j] [IsOpenImmersion j.left] [IsIso ((Over.pullback (jL L)).map j)]
    (eta : N.hodgeSpace g) (heta : eta ∈ printedDetLattice N g) (hz : eta ≠ 0)
    (hi : secIndex (printedDetLattice N g) eta ≠ 0)
    (r : (L →+* ℂ) → ℝ) (hr : ∀ τ, IsAnMetricSq N τ eta (r τ)) :
    let eta' := hodgeMap G N j g eta
    eta' ∈ printedDetLattice G g ∧ eta' ≠ 0 ∧
      secIndex (printedDetLattice G g) eta' = secIndex (printedDetLattice N g) eta ∧
      ∀ τ, IsPrintedMetricSq G τ eta' (r τ) := by
  obtain ⟨g', M, rfl⟩ := neronMetrizable_of_t35 hT35 K A L N hN
  obtain ⟨τ₀⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨Φ₀, hΦ₀, -⟩ := M.arch τ₀
  have hg' : A.dim = (g' : WithBot ℕ∞) := uniformizationDim_of_t35 hT35 K A L M.model τ₀ g' _ Φ₀
    (M.hodge.periods_discrete τ₀) (M.hodge.periods_isZLattice τ₀) hΦ₀
  have e : g = g' := by
    have h := hg.symm.trans hg'
    exact_mod_cast h
  subst g'
  let E := hodgeMap G M.model j g
  have hInj : Function.Injective E := (hodgeMapBijective K A L G M.model j inferInstance g).1
  have hNZ : E eta ≠ 0 := fun h => hz (hInj (h.trans (map_zero E).symm))
  rw [printedDetLattice_eq] at heta hi
  refine ⟨?_, hNZ, ?_, ?_⟩
  · rw [printedDetLattice_eq]
    exact hodgeMap_detLattice G M.model j g eta heta
  · rw [printedDetLattice_eq G, printedDetLattice_eq M.model]
    exact (secIndex_hodgeMap_openIso G M.model j g eta).symm
  · intro τ
    apply (isAnMetricSq_iff hT35 G g hg τ (E eta) hNZ (r τ)).mp
    exact markedAnMetricSq_openIso hT35 hg G M j eta heta hz hi τ (r τ) (hr τ)

#print axioms markedHeightWitness_openIso

end ZInQ.Contrib.IsogenyDegree
