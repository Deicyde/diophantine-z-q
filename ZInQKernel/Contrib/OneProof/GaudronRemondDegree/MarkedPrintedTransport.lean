import ZInQKernel.Contrib.OneProof.GaudronRemondDegree.MarkedMetrizedTransport
import ZInQKernel.Contrib.OneProof.PrintedStableHeight

/-! # Transfer the printed squared norm of the marked section on the actual open subgroup -/

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open scoped Obj

namespace ZInQ.Contrib.IsogenyDegree

open ZInQ.DefFaltings ZInQ.H5Glue
open ZInQ.HeightFix (IsPrintedMetricSq isPrintedMetricSq_iff)

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- For the actual open group immersion and the actual section pullback the printed
measure has the same total squared norm. No change of section or normalization. -/
theorem markedPrintedMetricSq_openIso {g : ℕ} (G : GroupModel A L) (M : MetrizedModel A L g)
    (j : G.G ⟶ M.model.G) [IsMonHom j] [IsOpenImmersion j.left]
    [IsIso ((Over.pullback (jL L)).map j)]
    (eta : M.model.hodgeSpace g) (heta : eta ∈ M.model.detLattice g) (hz : eta ≠ 0)
    (hi : secIndex (M.model.detLattice g) eta ≠ 0) (τ : L →+* ℂ) (r : ℝ) :
    IsPrintedMetricSq M.model τ eta r ↔ IsPrintedMetricSq G τ (hodgeMap G M.model j g eta) r := by
  let W := markedOpenMetrized G M j eta heta hz hi
  let e := hodgeMap G M.model j g
  have hinj : Function.Injective e := (hodgeMapBijective K A L G M.model j inferInstance g).1
  have hz' : e eta ≠ 0 := fun h => hz (hinj (h.trans (map_zero e).symm))
  change IsPrintedMetricSq M.model τ eta r ↔ IsPrintedMetricSq W.model τ (e eta) r
  rw [isPrintedMetricSq_iff M τ eta hz r, isPrintedMetricSq_iff W τ (e eta) hz' r]
  exact Iff.of_eq (congrArg (fun x : ℝ => r = x) (markedOpen_torusMetricSq G M j eta heta hz hi τ).symm)

#print axioms markedPrintedMetricSq_openIso

end ZInQ.Contrib.IsogenyDegree
