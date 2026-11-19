import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.ActualLocalDuality
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.RetainedAssembly

/-!
# The exact retained central Kummer duality from cited arithmetic inputs

The isotropy, one fixed global trace, its local coefficient trace properties,
and the literal local-duality quasi-isomorphism are all constructed from the
specified arithmetic inputs. The existing global map and retained comparisons
then give the original homotopy-equivalence consumer. The hom map is the same
traced Selmer cup pulled back through the retained comparison on both sides.

No hdual, local-duality premise, supplied trace or isotropy, model comparison,
derived self-isomorphism or desired homotopy equivalence is assumed. The cited
literature predicates remain explicit Prop parameters and are not new axioms.
The finiteness proof for the main consumer is itself supplied from the existing
arithmetic theorem. All torsion and nonminimal relation disks are retained.
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
open ZInQ.Contrib.RC53Assist.CalibrationShape
open ZInQ.Contrib.RC53Assist.InnerLimitArith
open ZInQ.Manuscript.RC.SelmerComplex
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- The actual retained quasi-isomorphism has no local-duality or trace premise. -/
theorem arithmeticRetainedCentralCupDualityMap_quasiIso
    (D : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S) :
    QuasiIso (retainedCentralCupDualityMap D hfinite (centralIntegralTruncIsotropy_of_print D hM)
      (chosenCentralGlobalTrace D hM h541 hK h2)
      (chosenCentralGlobalTrace_boundary D hM h541 hK h2)) :=
  retainedCentralCupDualityMap_quasiIso_of_local D hfinite (centralIntegralTruncIsotropy_of_print D hM)
    h543 hglob hloc hglobal hlocal hK h2
    (chosenCentralGlobalTrace D hM h541 hK h2)
    (chosenCentralGlobalTrace_boundary D hM h541 hK h2)
    (chosenCentralGlobalTrace_inducesIsoH3 D hM h541 hK h2)
    (chosenCentralLocalMap_quasiIso D hM hF hH hloc h541 hK h2)

/-- The original retained homotopy equivalence exists with its hom map fixed by the same traced cup. -/
theorem arithmeticRetainedCentralHomotopyEquiv
    (D : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S) :
    ∃ e : HomotopyEquiv (centralRetainedGCx D hfinite).toCC
      (dualCx (centralRetainedGCx D hfinite) 3).toCC,
      e.hom = retainedCentralCupDualityMap D hfinite (centralIntegralTruncIsotropy_of_print D hM)
        (chosenCentralGlobalTrace D hM h541 hK h2)
        (chosenCentralGlobalTrace_boundary D hM h541 hK h2) :=
  retainedCentralHomotopyEquiv_of_local D hfinite (centralIntegralTruncIsotropy_of_print D hM)
    h543 hglob hloc hglobal hlocal hK h2
    (chosenCentralGlobalTrace D hM h541 hK h2)
    (chosenCentralGlobalTrace_boundary D hM h541 hK h2)
    (chosenCentralGlobalTrace_inducesIsoH3 D hM h541 hK h2)
    (chosenCentralLocalMap_quasiIso D hM hF hH hloc h541 hK h2)

/-- The exact original consumer for any existing finiteness witness, from literature only. -/
theorem integralCentralKummerDuality_of_literature_with_finiteness
    (D : GenuineKummerData K E₀ hZ)
    (hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex D).homology n))
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S) :
    IntegralCentralKummerDuality D hfinite := by
  obtain ⟨e, _⟩ := arithmeticRetainedCentralHomotopyEquiv D hfinite hM hF hH h541 h543
    hglob hloc hglobal hlocal hK h2
  exact ⟨e⟩

/-- The original consumer with finiteness constructed internally from the existing arithmetic theorem. -/
theorem integralCentralKummerDuality_of_literature
    (D : GenuineKummerData K E₀ hZ)
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint)
    (h541 : NekovarIntegralCompactLocality) (h543 : NekovarIntegralGlobalDuality)
    (hglob : MilneGlobalFiniteness) (hloc : MilneLocalFiniteness)
    (hglobal : MilneGlobalDimensionTwo) (hlocal : MilneLocalDimensionTwo)
    (hK : IsTotallyComplex K)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ D.S) :
    IntegralCentralKummerDuality D (centralCohomologyFinite D hloc hglob h2) :=
  integralCentralKummerDuality_of_literature_with_finiteness D (centralCohomologyFinite D hloc hglob h2)
    hM hF hH h541 h543 hglob hloc hglobal hlocal hK h2

end ZInQ.Contrib.RC53Assist.DKLocalAdapter
