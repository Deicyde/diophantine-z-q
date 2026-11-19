import ZInQKernel.Contrib.RC53Assist.IntegralDuality.IntegralCompactTrace
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.ActualConsumer

/-!
# The cited compact trace fills the actual central trace slot

The full coefficient cone of the actual central pairing is literally the
compact cyclotomic target. Its trace is constructed from the general
coefficient top-cohomology statement, then the existing cone projection
makes it descend to the truncated local target. The descent preserves the
trace isomorphism and annihilation of boundaries, with the exact cone signs.

Local truncated isotropy is still separate data needed to name the pairing.
It is not used as an arithmetic proof of the trace, nor is local or global
Kummer self-duality asserted here.
-/

noncomputable section

set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The full trace target is exactly the specified coefficient cone, not a replacement. -/
theorem centralIntegralPairDataTrunc_fullTarget (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D) :
    coneCx (centralIntegralPairDataTrunc D I).resE = integralCompactTarget K D.S := rfl

/-- An actual trace with both required properties is supplied from the general cited coefficient result. -/
theorem exists_centralIntegralCompactTrace (D : GenuineKummerData K E₀ hZ)
    (I : CentralIntegralTruncIsotropy D)
    (h541 : NekovarIntegralCompactTopCohomology) (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S) :
    ∃ tr : (coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2],
      (∀ y, tr ((coneCx (centralIntegralPairDataTrunc D I).toSelPairData.resE).d 2 3 rfl y) = 0) ∧
      InducesIsoH3 tr := by
  let Q := centralIntegralPairDataTrunc D I
  obtain ⟨tr0, htr0, hiso0⟩ :=
    exists_integralCompactTrace (S := D.S) h541 hK D.hSfin h2
  let tr : (coneCx Q.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2] := tr0
  have ht : ∀ y, tr ((coneCx Q.resE).d 2 3 rfl y) = 0 := htr0
  have hi : InducesIsoH3 tr := hiso0
  exact ⟨Q.trT tr ht, Q.trT_kills tr ht, (inducesIsoH3_trT_iff Q tr ht).2 hi⟩

end ZInQ.Contrib.RC53Assist.IntegralDuality
