import ZInQKernel.Contrib.OneProof.FaltingsFromIsogenyBound
import ZInQKernel.Contrib.OneProof.H.TailZ98

/-! # Faltings semisimplicity from three existing research inputs -/

namespace ZInQ.Contrib.TateFiniteApproximation

/-- The stable height of A exists under the existing Néron-model existence
and Silverberg–Zarhin semistable reduction inputs. -/
theorem stable_height_witness_of_existing_leaves (hD : GroupLawNeron.NeronSchemeExtensionDedekind)
    (hR : SZRaynaud.SilverbergZarhinThm35) (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) :
    ∃ (g : ℕ) (height : ℝ), A.dim = (g : WithBot ℕ∞) ∧ ZInQ.SemistabAssembly.IsAnStableHeightSS A height := by
  have hE := GroupLawNeron.neronSchemeExtensionExists_of_dedekind hD
  have hT := CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hU := AvSplit.Final.h38 uniformizationLeafAll_proof hT
  have hSS := SSFaltings.semistableReductionThmIF_of_raynaud (SZRaynaud.raynaudSemistable_of_sz35 hR)
    hT OneProof.MulEtale.mulEtaleAbelianScheme_proof (GapNeron.neronSchemeModelExistsNF hE)
    (ReductGlue.semistableLocalGlobal_leaf GapBLR.neronLocalizesDVR_proved)
  exact GRUniformQuasiInverse.exists_anStableHeightSS (NeronC.neronModelExists_of_extension hE)
    (SSFaltings.semistableReductionThm_of_IF hSS) hU ChevFree.semiAbelianDescendsPerfect_proof K A

/-- The exact r9a field follows from three other fields in OpenResearchLeaves72. -/
theorem faltingsSemisimple_of_existing_leaves (hGR : SemistabAssembly.GaudronRemondThm14AnSS)
    (hD : GroupLawNeron.NeronSchemeExtensionDedekind) (hR : SZRaynaud.SilverbergZarhinThm35) :
    PkgI3.FaltingsSemisimple := by
  intro K _ _ A ℓ _
  obtain ⟨g, h, hd, hh⟩ := stable_height_witness_of_existing_leaves hD hR K A
  exact faltingsSemisimple_at_of_isogeny_bound A ℓ hGR g h hd hh

end ZInQ.Contrib.TateFiniteApproximation
