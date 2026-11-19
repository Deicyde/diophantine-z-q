import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.GlobalTraceLeaf
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.ActualGlobalDuality

/-!
# A fixed arithmetic global trace and its coherent local restrictions

The general cyclotomic top-cohomology result supplies a boundary-annihilating
trace for the actual pairing whose isotropy is constructed from Milne's
local input. One such trace is fixed here, rather than supplied as additional
data. Its global-duality and finite-place coefficient trace properties are
proved from the existing general literature inputs and arithmetic support.

No local Kummer quasi-isomorphism or retained self-duality is asserted here.
The chosen trace gives fixed data for the final same-map arithmetic binding.
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
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Manuscript.RC.SelmerComplex

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (D : GenuineKummerData K E₀ hZ) (hM : MilneLocalDualityPrint)
  (h541 : NekovarIntegralCompactLocality) (hK : IsTotallyComplex K)
  (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)

include h541 hK h2

/-- Actual trace existence from the general coefficient result and constructed isotropy. -/
theorem exists_constructedCentralGlobalTrace :
    ∃ tr : (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2],
      (∀ z, tr ((coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).d 2 3 rfl z) = 0) ∧
        InducesIsoH3 (C := coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE) tr :=
  exists_centralIntegralCompactTrace D (centralIntegralTruncIsotropy_of_print D hM)
    h541.to_topCohomology hK h2

/-- One fixed trace on the actual target; neither its functional nor its properties are premises. -/
def chosenCentralGlobalTrace :
    (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2] :=
  (exists_constructedCentralGlobalTrace D hM h541 hK h2).choose

/-- The same chosen trace kills every actual target boundary. -/
theorem chosenCentralGlobalTrace_boundary (z :
    (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 2) :
    chosenCentralGlobalTrace D hM h541 hK h2
      ((coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).d 2 3 rfl z) = 0 :=
  (exists_constructedCentralGlobalTrace D hM h541 hK h2).choose_spec.1 z

/-- The same chosen trace induces the genuine top coefficient isomorphism. -/
theorem chosenCentralGlobalTrace_inducesIsoH3 :
    InducesIsoH3 (C := coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE)
      (chosenCentralGlobalTrace D hM h541 hK h2) :=
  (exists_constructedCentralGlobalTrace D hM h541 hK h2).choose_spec.2

/-- Every local coefficient trace is the restriction of this one fixed global trace. -/
def chosenCentralLocalTrace (v : Places K D.S) :
    (centralLocalCyclotomicCx D v).X 2 →ₗ[ℤ_[2]] ℤ_[2] :=
  centralLocalTrace_of_print D hM (chosenCentralGlobalTrace D hM h541 hK h2) v

/-- The same chosen local restrictions have the unsigned top-degree trace property. -/
theorem chosenCentralLocalTrace_top (v : Places K D.S) :
    IsTopTraceIso ((centralLocalCyclotomicCx D v).d 1 2 rfl)
      ((centralLocalCyclotomicCx D v).d 2 3 rfl)
      (chosenCentralLocalTrace D hM h541 hK h2 v) :=
  centralLocalTrace_of_print_isTopTraceIso D hM h541 hK h2
    (chosenCentralGlobalTrace D hM h541 hK h2)
    (chosenCentralGlobalTrace_boundary D hM h541 hK h2)
    (chosenCentralGlobalTrace_inducesIsoH3 D hM h541 hK h2) v

/-- The literal global map for these fixed data is quasi-isomorphic from the general global theorem. -/
theorem chosenCentralGlobalMap_quasiIso (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo) :
    QuasiIso (GHom.toCC (globalDualityMap (centralIntegralPairing_of_print D hM).toSelPairData
      (chosenCentralGlobalTrace D hM h541 hK h2)
      (chosenCentralGlobalTrace_boundary D hM h541 hK h2))) :=
  centralRawGlobalDuality_quasiIso D (centralIntegralTruncIsotropy_of_print D hM) h543
    hglob hloc hglobal hlocal hK h2
    (chosenCentralGlobalTrace D hM h541 hK h2)
    (chosenCentralGlobalTrace_boundary D hM h541 hK h2)
    (chosenCentralGlobalTrace_inducesIsoH3 D hM h541 hK h2)

end ZInQ.Contrib.RC53Assist.DKLocalAdapter
