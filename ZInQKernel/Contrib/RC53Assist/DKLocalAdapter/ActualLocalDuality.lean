import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.CanonicalLocalComparison
import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.CentralTraceComparisonBinding
import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.ChosenGlobalTrace

/-!
# Arithmetic local duality for the actual constructed central pairing

The raw comparison, exact cone transport and exact adjoint square supply
the literal canonical comparisons from the cited Milne inputs. The proved
trace transfer and shift/finite-product binding give the unchanged central
local-duality map for the specified global trace. The global trace's local
coefficient properties come from the general cyclotomic locality theorem.

No local quasi-isomorphism, orthogonality witness, arbitrary model comparison,
derived self-isomorphism or central self-duality is an input. The literature
statements remain explicit Prop parameters, not newly declared axioms.
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
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Manuscript.RC.SelmerComplex
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The literal original central local-duality map is quasi-isomorphic from the cited arithmetic inputs. -/
theorem centralLocalDuality_quasiIso_of_literature
    (D : GenuineKummerData K E₀ hZ) (hM : MilneLocalDualityPrint)
    (hF : MilneFiniteLocalDualityPrint) (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (hloc : MilneLocalFiniteness) (h541 : NekovarIntegralCompactLocality)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr : (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht : InducesIsoH3 (C := coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE) tr) :
    QuasiIso (GHom.toCC (localDualityMap (centralIntegralPairing_of_print D hM).toSelPairData tr htr)) := by
  apply (centralLocalDuality_quasiIso_iff_canonical D hM hH h541 hK h2 tr htr ht).2
  intro v
  exact literalCanonicalComparison_quasiIso (S := D.S) (centralCurve D) v.1 hM hF hH hloc

/-- The formerly named arithmetic leaf has an inhabitant from the exact same-map suppliers. -/
theorem centralLocalDualityRemainingLeaf_of_literature
    (D : GenuineKummerData K E₀ hZ) (hM : MilneLocalDualityPrint)
    (hF : MilneFiniteLocalDualityPrint) (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (hloc : MilneLocalFiniteness) (h541 : NekovarIntegralCompactLocality)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr : (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht : InducesIsoH3 (C := coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE) tr) :
    CentralLocalDualityRemainingLeaf D hM tr htr :=
  centralLocalDuality_quasiIso_of_literature D hM hF hH hloc h541 hK h2 tr htr ht

/-- Local duality for the fixed chosen trace, with its trace facts constructed rather than supplied. -/
theorem chosenCentralLocalMap_quasiIso
    (D : GenuineKummerData K E₀ hZ) (hM : MilneLocalDualityPrint)
    (hF : MilneFiniteLocalDualityPrint) (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (hloc : MilneLocalFiniteness) (h541 : NekovarIntegralCompactLocality)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S) :
    QuasiIso (GHom.toCC (localDualityMap (centralIntegralPairing_of_print D hM).toSelPairData
      (chosenCentralGlobalTrace D hM h541 hK h2)
      (chosenCentralGlobalTrace_boundary D hM h541 hK h2))) :=
  centralLocalDuality_quasiIso_of_literature D hM hF hH hloc h541 hK h2
    (chosenCentralGlobalTrace D hM h541 hK h2)
    (chosenCentralGlobalTrace_boundary D hM h541 hK h2)
    (chosenCentralGlobalTrace_inducesIsoH3 D hM h541 hK h2)

end ZInQ.Contrib.RC53Assist.DKLocalAdapter
