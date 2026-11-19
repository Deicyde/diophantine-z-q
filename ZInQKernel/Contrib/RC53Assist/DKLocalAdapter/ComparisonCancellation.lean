import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.LocalDuality
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.GlobalModelToRaw

/-!
# Cancellation of the fixed local comparison transports

This combines the raw actual local comparison with its two specified
transport maps. The cone quasi-isomorphism and exact adjoint square are
explicit transport obligations here. Once their proofs are supplied,
the actual condition comparison and scoped torsion-free dual exactness
cancel the maps and give quasi-isomorphy of the literal canonical adjoint.

No supplied local duality, derived isomorphism or central self-duality is
used. This conditional cancellation does not itself prove either of the
remaining transport obligations.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.DKLocalAdapter

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.IntegralDuality
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.InnerLimitArith

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- The literal canonical map follows from the two exact transport obligations,
not an assumed quasi-isomorphism of that literal map. -/
theorem literalCanonicalComparison_quasiIso_of_transport
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint) (hloc : MilneLocalFiniteness)
    (hcone : QuasiIso (GHom.toCC (actualConeToLiteral (S := S) W w hloc)))
    (hsquare :
      GHom.toCC (ActualSelfDual.localSelfDualComparison K w (W.baseChange (w.adicCompletion K)) hM) =
        GHom.toCC (ghomComp (ghomComp (actualConeToLiteral (S := S) W w hloc)
          (literalLocalSelfDualComparison (S := S) W w hM))
          (dualHom (actualConditionToLiteral (S := S) W w hloc) 2))) :
    QuasiIso (GHom.toCC (literalLocalSelfDualComparison (S := S) W w hM)) := by
  apply rawDuality_quasiIso_of_comparisons 2
    (literalLocalSelfDualComparison (S := S) W w hM)
    (actualConeToLiteral (S := S) W w hloc)
    (actualConditionToLiteral (S := S) W w hloc)
    hcone (actualConditionToLiteral_quasiIso (S := S) W w hloc)
    (actualCondition_term_torsionFree W w)
    (integralCondition_term_torsionFree (S := S) W w)
  rw [← hsquare]
  exact actual_local_comparison_quasiIso_of_print K w
    (W.baseChange (w.adicCompletion K)) hM hF hH

end ZInQ.Contrib.RC53Assist.DKLocalAdapter
