import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.CentralLocalMap
import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.LocalTraceTransport

/-!
# The exact central local family and its canonical comparisons

The local comparison with the restriction of the specified global trace
is definitionally the given-trace comparison on the same ordinary cone.
The boundary and isotropy proof terms do not change its map. The local
coefficient trace isomorphism is supplied by the general coefficient
locality theorem and the actual global trace properties.

The canonical-versus-given trace theorem and the exact shift/product
binding consequently reduce the literal central local-duality map to the
family of literal canonical comparisons. This is an equivalence only;
no member of that family is assumed or claimed proved here.
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
open ZInQ.Contrib.RC53Assist.DKLocalAdapter.LocalTraceTransport
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.CalibrationIntegral
open ZInQ.Manuscript.RC.SelmerComplex
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The original central family map is exactly the given-trace wrapper on the same literal data. -/
theorem centralLocalTraceComparison_eq_givenTrace
    (D : GenuineKummerData K E₀ hZ) (hM : MilneLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr : (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht : InducesIsoH3 (C := coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE) tr)
    (v : Places K D.S) :
    GHom.toCC (centralLocalTraceComparison D (centralIntegralTruncIsotropy_of_print D hM) tr v) =
      GHom.toCC (literalLocalComparisonWithTrace (S := D.S) (centralCurve D) v.1 hM hH
        (centralLocalIntegralTrace D (centralIntegralTruncIsotropy_of_print D hM) tr v)
        (centralLocalIntegralTrace_isTopTraceIso D (centralIntegralTruncIsotropy_of_print D hM)
          h541 hK h2 tr htr ht v)) := rfl

/-- The fixed given-global-trace member is quasi-isomorphic exactly when the literal canonical member is. -/
theorem centralLocalTraceComparison_quasiIso_iff_canonical
    (D : GenuineKummerData K E₀ hZ) (hM : MilneLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr : (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht : InducesIsoH3 (C := coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE) tr)
    (v : Places K D.S) :
    QuasiIso (GHom.toCC (centralLocalTraceComparison D (centralIntegralTruncIsotropy_of_print D hM) tr v)) ↔
      QuasiIso (GHom.toCC (literalLocalSelfDualComparison (S := D.S) (centralCurve D) v.1 hM)) := by
  rw [centralLocalTraceComparison_eq_givenTrace D hM hH h541 hK h2 tr htr ht v]
  exact literalLocalComparisonWithTrace_quasiIso_iff (S := D.S) (centralCurve D) v.1 hM hH
    (centralLocalIntegralTrace D (centralIntegralTruncIsotropy_of_print D hM) tr v)
    (centralLocalIntegralTrace_isTopTraceIso D (centralIntegralTruncIsotropy_of_print D hM)
      h541 hK h2 tr htr ht v)

/-- The literal old central local-duality map reduces to the exact canonical family.
This equivalence does not supply a quasi-isomorphism for any family member. -/
theorem centralLocalDuality_quasiIso_iff_canonical
    (D : GenuineKummerData K E₀ hZ) (hM : MilneLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr : (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht : InducesIsoH3 (C := coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE) tr) :
    QuasiIso (GHom.toCC (localDualityMap (centralIntegralPairing_of_print D hM).toSelPairData tr htr)) ↔
      ∀ v : Places K D.S,
        QuasiIso (GHom.toCC (literalLocalSelfDualComparison (S := D.S) (centralCurve D) v.1 hM)) := by
  rw [centralLocalDuality_quasiIso_iff_of_print D hM tr htr]
  constructor
  · intro h v
    exact (centralLocalTraceComparison_quasiIso_iff_canonical D hM hH h541 hK h2 tr htr ht v).1 (h v)
  · intro h v
    exact (centralLocalTraceComparison_quasiIso_iff_canonical D hM hH h541 hK h2 tr htr ht v).2 (h v)

end ZInQ.Contrib.RC53Assist.DKLocalAdapter
