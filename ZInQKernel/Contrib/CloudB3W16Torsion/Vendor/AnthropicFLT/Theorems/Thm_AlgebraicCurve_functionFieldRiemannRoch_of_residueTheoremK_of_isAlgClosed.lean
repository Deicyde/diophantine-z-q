/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisorUniformizer
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_LocalResidue
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RiemannRochRows
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed

set_option backward.isDefEq.respectTransparency false

theorem AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F]
    (hRTK : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.solution
