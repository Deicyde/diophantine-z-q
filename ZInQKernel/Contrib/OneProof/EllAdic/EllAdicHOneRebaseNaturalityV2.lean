import ZInQKernel.Contrib.OneProof.EllAdic.EllAdicHOneRebaseV1
import ZInQKernel.Contrib.OneProof.EllAdic.EtaleHOneKernelRebaseV1
import ZInQKernel.Contrib.OneProof.EllAdic.PadicEtaleHOneLinearV1
import ZInQKernel.Contrib.OneProof.EllAdic.PadicEtaleHOneFiniteSquareV1

/-!
# Naturality of the integral pro-étale/étale comparison under scheme isomorphisms

`ellAdicHOne_actualEtale_equiv S p : H¹_proet(S, ℤ_p) ≃+ lim_n H¹_et(S, ℤ/pⁿ)` (from Stacks 099V)
commutes with pullback along any scheme isomorphism `σ : S ≅ T`:

* `ellAdicHOne_actualEtale_equiv_rebase`: coordinatewise, from the finite comparison square
  `smallEtaleResidueHOneForward_rebase` and injectivity of the finite comparison;
* `ellAdicHOne_actualEtale_equiv_rebase_ker`: as an equality of compatible families;
* `ellAdicHOne_actualEtale_linearEquiv_rebase`: the same for the `ℤ_p`-linear comparison.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

set_option maxHeartbeats 4000000 in
/-- **Naturality, coordinatewise.** -/
theorem ellAdicHOne_actualEtale_equiv_rebase {S T : Scheme.{u}} (σ : S ≅ T) (p : ℕ)
    [Fact p.Prime] (x : T.EllAdicCohomology p 1) (n : ℕ) :
    (ellAdicHOne_actualEtale_equiv S p (ellAdicHOne_rebase σ p x)).1 n =
      etaleResidueHOne_rebase σ p n ((ellAdicHOne_actualEtale_equiv T p x).1 n) := by
  apply (smallEtaleResidueHOneForward_bijective S p n).1
  rw [ellAdicHOne_actualEtale_equiv_apply, smallEtaleResidueHOneForward_rebase,
    ellAdicHOne_actualEtale_equiv_apply]
  exact ellAdicHOne_rebase_projection σ p n x

set_option maxHeartbeats 4000000 in
/-- **Naturality, on compatible families.** -/
theorem ellAdicHOne_actualEtale_equiv_rebase_ker {S T : Scheme.{u}} (σ : S ≅ T) (p : ℕ)
    [Fact p.Prime] (x : T.EllAdicCohomology p 1) :
    ellAdicHOne_actualEtale_equiv S p (ellAdicHOne_rebase σ p x) =
      etaleResidueHOneKernel_rebase σ p (ellAdicHOne_actualEtale_equiv T p x) :=
  Subtype.ext (funext fun n => (ellAdicHOne_actualEtale_equiv_rebase σ p x n).trans
    (etaleResidueHOneKernel_rebase_coordinate σ p (ellAdicHOne_actualEtale_equiv T p x) n).symm)

set_option maxHeartbeats 4000000 in
/-- **Naturality of the linear comparison.** For any `ℤ_p`-module structures on the two integral
pro-étale groups, the linear comparison is the additive one on elements. -/
theorem ellAdicHOne_actualEtale_linearEquiv_rebase {S T : Scheme.{u}} (σ : S ≅ T) (p : ℕ)
    [Fact p.Prime] [Module ℤ_[p] (S.EllAdicCohomology p 1)]
    [Module ℤ_[p] (T.EllAdicCohomology p 1)] (x : T.EllAdicCohomology p 1) :
    ellAdicHOne_actualEtale_linearEquiv S p (ellAdicHOne_rebase σ p x) =
      etaleResidueHOneKernel_rebase σ p (ellAdicHOne_actualEtale_linearEquiv T p x) := by
  rw [ellAdicHOne_actualEtale_linearEquiv_apply, ellAdicHOne_actualEtale_linearEquiv_apply]
  exact ellAdicHOne_actualEtale_equiv_rebase_ker σ p x

end RC53.EllAdic
