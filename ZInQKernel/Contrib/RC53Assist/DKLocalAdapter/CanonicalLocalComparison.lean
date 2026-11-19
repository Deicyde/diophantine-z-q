import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.AdjointSquare
import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.ConeComparison
import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.ComparisonCancellation

/-!
# The literal canonical local comparison from the arithmetic transports

The exact cone transport and adjoint commuting square are now proved maps,
not premises. They cancel the actual condition comparison and its scoped
torsion-free dual from the arithmetic raw comparison. The result concerns
the literal canonical trace-cup adjoint, with no local quasi-isomorphism,
replacement model, derived isomorphism or self-duality assumption supplied.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.DKLocalAdapter

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Manuscript.RC.LambdaCoef

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- The actual literal canonical comparison is quasi-isomorphic from the cited arithmetic inputs.
Both exact transport obligations are filled by their proved suppliers. -/
theorem literalCanonicalComparison_quasiIso
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint) (hloc : MilneLocalFiniteness) :
    QuasiIso (GHom.toCC (literalLocalSelfDualComparison (S := S) W w hM)) := by
  apply literalCanonicalComparison_quasiIso_of_transport (S := S) W w hM hF hH hloc
    (actualConeToLiteral_quasiIso (S := S) W w hloc)
  rw [← GHom.toCC_comp, ← GHom.toCC_comp, Category.assoc]
  exact localSelfDualComparison_commutingSquare (S := S) W w hloc hM

end ZInQ.Contrib.RC53Assist.DKLocalAdapter
