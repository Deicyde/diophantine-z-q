import ZInQKernel.Contrib.RC53Assist.IntegralDuality.GlobalModelToRaw
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.GlobalDualityEvaluation
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.ActualGlobalCohomology
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralCompactTrace

/-!
# The integral global duality map for the actual central Tate coefficients

The proved topology, coefficient perfectness and cohomological support
supply every ordinary hypothesis of the general global-duality bridge.
The global adjoint has the same fixed evaluation formula with strict or
Kummer local conditions, because both local-condition entries are zero.
The general cited global result therefore applies to the literal map of
the central pairing. No global quasi-isomorphism, supplied model comparison,
derived isomorphism or central self-duality is an input.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The strict pairing uses the same actual central integral coefficient form. -/
abbrev centralStrictIntegralPairData (D : GenuineKummerData K E₀ hZ) :
    SelPairData (centralStrictIntegralSelData D) (centralStrictIntegralSelData D) :=
  strictPairData ℤ_[2] (GKS K D.S) (fun v : Places K D.S => Gloc K v.1)
    (fun v => locMap K D.S v.1) (centralIntegralBeta D)
    integralBeta_galois integralBeta_continuous

/-- The full truncated trace target is literally independent of the local conditions. -/
theorem centralGlobalTraceTarget_eq_strict (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D) :
    (centralIntegralPairDataTrunc D I).toSelPairData.resE =
      (centralStrictIntegralPairData D).resE := rfl

/-- The actual global map equals its strict-data version, including its local cup term and sign. -/
theorem centralGlobalDualityMap_eq_strict (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D)
    (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0) :
    GHom.toCC (globalDualityMap (centralIntegralPairDataTrunc D I).toSelPairData tr htr) =
      GHom.toCC (globalDualityMap (centralStrictIntegralPairData D) tr htr) := by
  apply GHom.toCC_ext
  intro i a
  apply dualCx_ext
  intro c
  obtain ⟨b, y⟩ := c
  erw [globalDualityMap_evaluation, globalDualityMap_evaluation]
  rfl

/-- General integral global duality applies to the fixed actual map; ordinary arithmetic hypotheses are supplied. -/
theorem centralRawGlobalDuality_quasiIso (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D)
    (hprint : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (htrace : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr) :
    QuasiIso (GHom.toCC (globalDualityMap
      (centralIntegralPairDataTrunc D I).toSelPairData tr htr)) := by
  let : IsModuleTopology ℤ_[2] (TateS K D.S (centralCurve D)) :=
    tate_isModuleTopology (K := K) (S := D.S) (W := centralCurve D)
  let Qs := centralStrictIntegralPairData D
  let trS : (coneCx Qs.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2] := tr
  have htrS : ∀ z, trS ((coneCx Qs.resE).d 2 3 rfl z) = 0 := htr
  have htS : InducesIsoH3 (C := coneCx Qs.resE) trS := htrace
  rw [centralGlobalDualityMap_eq_strict D I tr htr]
  change QuasiIso (GHom.toCC (globalDualityMap Qs trS htrS))
  exact strictRawGlobalDuality_quasiIso K D.S
    (TateS K D.S (centralCurve D)) (TateS K D.S (centralCurve D))
    (centralIntegralBeta D)
    (integralBeta_galois (K := K) (S := D.S) (W := centralCurve D))
    (integralBeta_continuous (K := K) (S := D.S) (W := centralCurve D))
    hprint hK D.hSfin h2
    (integralBeta_bijective (K := K) (S := D.S) (W := centralCurve D))
    (centralIntegralBeta_flip_bijective D)
    trS htrS htS
    (centralGlobalIntegralCohomology_finite D hglob h2)
    (centralCompactIntegralCohomology_finite D hglob hloc h2)
    ⟨0, 2, centralGlobalIntegralCohomology_outside D hglob hglobal hK h2⟩
    ⟨0, 3, centralCompactIntegralCohomology_outside D hglob hloc hglobal hlocal hK h2⟩

/-- A fixed actual global duality map, with its trace facts, is constructed from the two general cited results. -/
theorem exists_centralGlobalDuality_of_literature (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D)
    (h541 : NekovarIntegralCompactTopCohomology) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S) :
    ∃ tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2],
      ∃ htr : ∀ z, tr ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0,
        InducesIsoH3 tr ∧ QuasiIso (GHom.toCC (globalDualityMap
          (centralIntegralPairDataTrunc D I).toSelPairData tr htr)) := by
  obtain ⟨tr, htr, ht⟩ := exists_centralIntegralCompactTrace D I h541 hK h2
  exact ⟨tr, htr, ht, centralRawGlobalDuality_quasiIso D I h543
    hglob hloc hglobal hlocal hK h2 tr htr ht⟩

end ZInQ.Contrib.RC53Assist.IntegralDuality
