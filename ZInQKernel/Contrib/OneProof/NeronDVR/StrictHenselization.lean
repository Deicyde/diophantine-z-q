import ZInQKernel.Contrib.OneProof.NeronDVR.Henselian
import ZInQKernel.Contrib.OneProof.NeronDVR.ValuationBase
import ZInQKernel.Contrib.OneProof.NeronDedekind
import ZInQKernel.Contrib.OneProof.NeronBaseChangeStrictHenselization

/-!
# Néron existence over a strict henselization

The model on a strict henselization is constructed from Néron existence
over a henselian DVR. The remaining geometric descent is the group-scheme
case of Bosch–Lütkebohmert–Raynaud, *Néron Models* (1990), §6.5 Corollary 3,
pp. 158–159, with the input ring taken to be the strict henselization.
-/

open CategoryTheory AlgebraicGeometry

namespace NeronDVR

open ZInQ.Contrib.GroupLawNeron

/-- For every valuation DVR and abelian variety over its fraction field, the base
change to the fraction field of its strict henselization has a Néron model. -/
theorem exists_neron_model_strict_henselization
    {K : Type} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (P : ValuationSubring E)
      (hP : P.comap (algebraMap K E) = O), GapSHPair.IsSHSep O P hP ∧
        ∃ N : Over (Spec (CommRingCat.of P)), CToPrinted.IsNeronModelOver P E N ∧
          Nonempty ((Over.pullback (genMap P E)).obj N ≅ (A.baseChange E).X) := by
  obtain ⟨w, hw⟩ := GapSHPair.exists_comap_eq (Ω := AlgebraicClosure K) O
  let E := GapSHPair.inertiaField (K := K) w
  let P := GapSHPair.wE (K := K) w
  have hP := GapSHPair.hE_eq w hw
  have hSH := GapSHPair.isSHSep_inertia w hw
  have : IsDiscreteValuationRing P := hSH.1.1
  have : HenselianLocalRing P := hSH.1.2.1
  exact ⟨E, inferInstance, inferInstance, P, hP, hSH,
    exists_neron_model_henselian P E (A.baseChange E)⟩

/-- BLR §6.5 Corollary 3, pp. 158–159, for an abelian variety and its trivial
torsor, with the extended valuation ring a strict henselization. The
conclusion retains the existence of the descended model and its generic
identification. -/
def NeronDescentFromStrictHenselization : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (E : Type) [Field E] [Algebra K E] (P : ValuationSubring E)
    (hP : P.comap (algebraMap K E) = O), GapSHPair.IsSHSep O P hP →
    ∀ (A : PkgI3.AbVar K) (N : Over (Spec (CommRingCat.of P))),
      CToPrinted.IsNeronModelOver P E N →
      Nonempty ((Over.pullback (genMap P E)).obj N ≅ (A.baseChange E).X) →
      ∃ M : Over (Spec (CommRingCat.of O)), CToPrinted.IsNeronModelOver O K M ∧
        Nonempty ((Over.pullback (genMap O K)).obj M ≅ A.X)

/-- Local existence over any DVR follows from descent from a strict henselization. -/
theorem neronSchemeExtensionDVR_of_strictHenselizationDescent
    (descend : NeronDescentFromStrictHenselization) : NeronSchemeExtensionDVR := by
  apply neronSchemeExtensionDVR_of_valuationSubring
  intro K _ O _ A
  obtain ⟨E, _, _, P, hP, hSH, N, hN, eN⟩ := exists_neron_model_strict_henselization O A
  exact descend K O E P hP hSH A N hN eN

/-- Dedekind-domain existence follows from descent from strict henselizations. -/
theorem neronSchemeExtensionDedekind_of_strictHenselizationDescent
    (descend : NeronDescentFromStrictHenselization) : NeronSchemeExtensionDedekind :=
  NeronExtDedekind.neronSchemeExtensionDedekind_of_dvr
    (neronSchemeExtensionDVR_of_strictHenselizationDescent descend)

end NeronDVR
