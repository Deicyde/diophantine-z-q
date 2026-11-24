import ZInQKernel.Contrib.OneProof.SSFaltings
import ZInQKernel.Contrib.OneProof.GaudronRemondSection9

/-! # ss-faltings: R21 through Gaudron–Rémond §9 over Faltings' invariance

bost-gr9 (fold-b112) routes R21 through `ZInQ.BostGR9.r21_of_grBost'`, which reads SS1 and SS2
(`SemistableNeronBaseChange`, SGA 7 IX Cor. 3.3) only through TailY's identification of the kernel's stable height
with the height of a semistable Néron model. Here the same proofs with Faltings' invariance
(`ZInQ.SSFaltings.FaltingsSemistableHeightBC`, Faltings 1983) in place of SS2, through
`ZInQ.SSFaltings.isStableFaltingsHeight_iffF` and `stableFaltingsHeight_ne_botF` (task ss-faltings,
docs/research/ss-faltings.md). No `sorry`, no `axiom`. -/

namespace ZInQ.SSFaltings

open ZInQ.DefFaltings ZInQ.H5Neron ZInQ.HeightSplit

/-- **R21 from GR §9** (`ZInQ.BostGR9.r21_of_grBost` with `hF` in place of SS2). -/
theorem r21_of_grBostF (hB : GRBostBound) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hF : FaltingsSemistableHeightBC)
    (hU : AnalyticUniformizationUnique) (hD : MetrizedDimUnique) : R21_Bost := by
  intro K _ _ A g hg
  by_cases ht : stableFaltingsHeight A = ⊤
  · rw [ht]; exact le_top
  obtain ⟨x, hx⟩ := exists_real_of_ne _ ht (stableFaltingsHeight_ne_botF hN1 hSS1 hF hU hD A)
  rw [hx]
  exact EReal.coe_le_coe_iff.mpr (hB K A g hg x ((isStableFaltingsHeight_iffF hN1 hF hSS1 A x).mpr hx))

/-- `r21_of_grBostF` with `MetrizedDimUnique` discharged (the shape of `ZInQ.BostGR9.r21_of_grBost'`). -/
theorem r21_of_grBostF' (hB : GRBostBound) (hN1 : NeronModelExists)
    (hSS1 : SemistableReductionThm) (hF : FaltingsSemistableHeightBC)
    (hU : AnalyticUniformizationUnique) : R21_Bost :=
  r21_of_grBostF hB hN1 hSS1 hF hU metrizedDimUnique

end ZInQ.SSFaltings
