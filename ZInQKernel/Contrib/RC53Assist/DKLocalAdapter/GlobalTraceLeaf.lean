import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.Adapter
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.CentralLocalTrace

/-!
# The restricted local traces for the constructed integral pairing

The isotropy witness is constructed from the genuine Kummer classes.
Every finite-place coefficient trace is the restriction of the same
specified global compact trace. The general coefficient locality theorem
supplies its degree-two trace isomorphism; no Kummer local-orthogonality
hypothesis is used for that coefficient statement.

The last declaration names the remaining arithmetic quasi-isomorphism
without supplying an inhabitant or assuming it in any proved theorem.

References: `diophantine_zq.tex`, lines 3413–3463;
Nekovář, *Selmer complexes*, 5.4.1, pp. 125–126, and 6.3.1.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.DKLocalAdapter

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.SwitchInputs
open ZInQ.Contrib.RC53Assist.IntegralDuality
open ZInQ.Contrib.RC53Assist.Calibration
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual
open scoped Classical

variable {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- Kind: definition; the finite-place restriction of one given global
compact trace for the constructed integral Kummer pairing. No independent
local trace is chosen (tex 3413–3463; Nekovář 5.4.1). -/
def centralLocalTrace_of_print (D : GenuineKummerData K E₀ hZ)
    (hM : MilneLocalDualityPrint)
    (tr : (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (v : Places K D.S) : (centralLocalCyclotomicCx D v).X 2 →ₗ[ℤ_[2]] ℤ_[2] :=
  centralLocalIntegralTrace D (centralIntegralTruncIsotropy_of_print D hM) tr v

/-- Kind: proved theorem; the restricted coefficient trace is evaluated
on the literal pure local component of the same truncated global target
(tex 3413–3463; Nekovář 5.4.1). -/
theorem centralLocalTrace_of_print_apply (D : GenuineKummerData K E₀ hZ)
    (hM : MilneLocalDualityPrint)
    (tr : (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (v : Places K D.S) (c : (centralLocalCyclotomicCx D v).X 2) :
    centralLocalTrace_of_print D hM tr v c =
      tr ((0, (truncSub (centralIntegralPairing_of_print D hM).EL (3 - 1)).mkQ (Pi.single v c)) :
        (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3) := rfl

/-- Kind: proved theorem from an explicit general coefficient literature
parameter; the same given global trace yields the actual local degree-two
trace isomorphism. The parameter concerns cyclotomic coefficient locality,
not the Kummer local duality map (tex 3413–3463; Nekovář 5.4.1). -/
theorem centralLocalTrace_of_print_isTopTraceIso (D : GenuineKummerData K E₀ hZ)
    (hM : MilneLocalDualityPrint) (h541Locality : NekovarIntegralCompactLocality)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S)
    (tr : (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).d 2 3 rfl z) = 0)
    (ht : InducesIsoH3 (C := coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE) tr)
    (v : Places K D.S) :
    IsTopTraceIso ((centralLocalCyclotomicCx D v).d 1 2 rfl)
      ((centralLocalCyclotomicCx D v).d 2 3 rfl) (centralLocalTrace_of_print D hM tr v) :=
  centralLocalIntegralTrace_isTopTraceIso D (centralIntegralTruncIsotropy_of_print D hM)
    h541Locality hK h2 tr htr ht v

/-- Kind: definition of an unproved arithmetic goal, not a supplied
hypothesis or a claimed theorem. Its map is the literal local duality map
of the constructed integral pairing and the specified global trace. The
remaining step is transport of the actual local Kummer comparison to this
same map (tex 3413–3463; Nekovář 6.3.1). -/
def CentralLocalDualityRemainingLeaf (D : GenuineKummerData K E₀ hZ)
    (hM : MilneLocalDualityPrint)
    (tr : (coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).X 3 →ₗ[ℤ_[2]] ℤ_[2])
    (htr : ∀ z, tr ((coneCx (centralIntegralPairing_of_print D hM).toSelPairData.resE).d 2 3 rfl z) = 0) : Prop :=
  QuasiIso (GHom.toCC (localDualityMap (centralIntegralPairing_of_print D hM).toSelPairData tr htr))

end ZInQ.Contrib.RC53Assist.DKLocalAdapter
