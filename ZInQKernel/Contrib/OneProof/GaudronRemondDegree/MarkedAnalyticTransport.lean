import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.MarkedPrintedTransport
import ZInQKernel.Contrib.OneProof.AnalyticStableHeight

/-! # The literal analytic squared norms on the original and open models -/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open scoped Obj

namespace ZInQ.Contrib.IsogenyDegree

open ZInQ.DefFaltings ZInQ.H5Glue ZInQ.R3Residual

variable {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The literal analytic metric at a specified embedding is transported to the actual
pullback of the marked section, with no renormalization. -/
theorem markedAnMetricSq_openIso (hT35 : ZInQ.LeafPush2.UniformizationExists)
    {g : ℕ} (hg : A.dim = (g : WithBot ℕ∞))
    (G : GroupModel A L) (M : MetrizedModel A L g) (j : G.G ⟶ M.model.G)
    [IsMonHom j] [IsOpenImmersion j.left] [IsIso ((Over.pullback (jL L)).map j)]
    (eta : M.model.hodgeSpace g) (heta : eta ∈ M.model.detLattice g) (hz : eta ≠ 0)
    (hi : secIndex (M.model.detLattice g) eta ≠ 0) (τ : L →+* ℂ) (r : ℝ)
    (hr : IsAnMetricSq M.model τ eta r) :
    IsAnMetricSq G τ (hodgeMap G M.model j g eta) r := by
  let e := hodgeMap G M.model j g
  have hinj : Function.Injective e := (hodgeMapBijective K A L G M.model j inferInstance g).1
  have hz' : e eta ≠ 0 := fun h => hz (hinj (h.trans (map_zero e).symm))
  have hOld := (isAnMetricSq_iff hT35 M.model g hg τ eta hz r).mp hr
  have hNew := (markedPrintedMetricSq_openIso G M j eta heta hz hi τ r).mp hOld
  exact (isAnMetricSq_iff hT35 G g hg τ (e eta) hz' r).mpr hNew

#print axioms markedAnMetricSq_openIso

end ZInQ.Contrib.IsogenyDegree
