import ZInQKernel.Contrib.RC53Assist.IntegralDuality.QuasiIsoTracePullbackGCx
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.IntegralTraceLocality
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralCompactTrace

/-!
# Actual local coefficient traces from one global compact trace

The full trace pulled back from the truncated global target is composed
with the genuine pure finite-place inclusion. The cited coefficient
locality supplies an isomorphism on degree-three cohomology of this same
map. The proved trace-pullback theorem consequently gives the local
degree-two trace isomorphism, with both shifted signs removed. No local
trace perfection or Kummer orthogonality is supplied as a hypothesis.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.Calibration
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The actual restricted cyclotomic complex at a finite place of the central support. -/
abbrev centralLocalCyclotomicCx (D : GenuineKummerData K E₀ hZ) (v : Places K D.S) : GCx ℤ_[2] :=
  localCx ℤ_[2] (GKS K D.S) (fun w : Places K D.S => Gloc K w.1)
    (fun w => locMap K D.S w.1) (IntegralTate1 K D.S) v

/-- The local functional is the pure-local restriction of this same global trace. -/
def centralLocalIntegralTrace (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D)
    (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (v : Places K D.S) : (centralLocalCyclotomicCx D v).X 2 →ₗ[ℤ_[2]] ℤ_[2] :=
  shiftDownTrace (integralLocalToCompactTarget K D.S v)
    (trOfTrunc (centralIntegralPairDataTrunc D I) tr)

/-- The functional evaluates exactly on the pure finite-place component in the truncated target. -/
theorem centralLocalIntegralTrace_apply (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D)
    (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (v : Places K D.S) (c : (centralLocalCyclotomicCx D v).X 2) :
    centralLocalIntegralTrace D I tr v c =
      tr ((0, (truncSub (centralIntegralPairDataTrunc D I).EL (3 - 1)).mkQ (Pi.single v c)) :
        (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3) := rfl

/-- The same global trace induces local degree-two isomorphisms from the general coefficient locality result. -/
theorem centralLocalIntegralTrace_isTopTraceIso (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D) (h541 : NekovarIntegralCompactLocality)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl z) = 0)
    (htrace : InducesIsoH3 (C := coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE) tr)
    (v : Places K D.S) :
    IsTopTraceIso ((centralLocalCyclotomicCx D v).d 1 2 rfl)
      ((centralLocalCyclotomicCx D v).d 2 3 rfl) (centralLocalIntegralTrace D I tr v) := by
  let Q := centralIntegralPairDataTrunc D I
  let trF : (integralCompactTarget K D.S).X 3 →ₗ[ℤ_[2]] ℤ_[2] := trOfTrunc Q tr
  have hbF : ∀ z, trF ((integralCompactTarget K D.S).d 2 3 rfl z) = 0 :=
    trOfTrunc_kills Q tr htr
  have hiF : InducesIsoH3 (C := integralCompactTarget K D.S) trF :=
    (inducesIsoH3_trOfTrunc_iff Q tr).2 htrace
  exact shiftDown_isTopTraceIso_comp_of_quasiIsoAt (integralLocalToCompactTarget K D.S v)
    ((h541 K hK D.S D.hSfin h2).2 v) trF hbF hiF

end ZInQ.Contrib.RC53Assist.IntegralDuality
