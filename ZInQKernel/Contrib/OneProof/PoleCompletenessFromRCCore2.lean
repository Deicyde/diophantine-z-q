import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCCore
import ZInQKernel.Contrib.PoleRC.MordellWeilM

/-!
# Theorem 5.2 from Theorem 5.3 without Mordell's theorem as a hypothesis

Lane R5-mw (fork issue #83). `poleCompleteness_of_restrictedConverse_core`
(`PoleCompletenessFromRCCore.lean`) assumes the textbook statement `MordellWeil` (every elliptic
curve over `ℚ` has finitely generated `E(ℚ)`), but its proof uses it only at the curves `E_ℓ` of
Theorem 5.3, through `crm_of_restrictedConverse`. Mordell's theorem for `E_ℓ` is proved in
`ZInQKernel/Contrib/PoleRC/MordellWeilM.lean` (`mordellWeil_curve`, for every rational `ℓ ≠ 0`),
so the hypothesis leaves the assembly:

* `poleCompleteness_of_restrictedConverse_coreM`: the core theorem with the narrowed hypothesis
  `MordellWeilM` (Mordell's theorem at the curves of Theorem 5.3) in place of `MordellWeil`;
* `poleCompleteness_of_restrictedConverse_core2`: the same with `MordellWeilM` discharged by
  `mordellWeilM`. What remains is exactly the manuscript's citations at this point: Theorem 5.3
  itself, Lemma 5.4 (the interface `Lemma54At` for the Selmer predicate `SelmerCorankOne`) and
  Lemma 5.5's rank assertion (`KolyvaginRankOne`: BCDT Theorem A with Kolyvagin Theorem 1).
-/

namespace ZInQ.Manuscript.PoleRC

/-- **Theorem 5.2 from Theorem 5.3** (`diophantine_zq.tex` lines 1019–1121), with Mordell's theorem
assumed only at the curves `E_ℓ` of Theorem 5.3 (`MordellWeilM`), the simultaneous construction
(`Simul.matrixRealization`), the dimension-three count (`dimThreeCount`) and the complete 2-descent
(`descentGlueM`) proved. -/
theorem poleCompleteness_of_restrictedConverse_coreM (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hK : KolyvaginRankOne) (hMW : MordellWeilM) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_crm_glue
    (crm_of_restrictedConverse_M SelmerCorankOne hRC h54 hK hMW descentGlueM)
    Simul.matrixRealization dimThreeCount

/-- **Theorem 5.2 from Theorem 5.3, Lemma 5.4 and Lemma 5.5** (`diophantine_zq.tex`
lines 1019–1121): `poleCompleteness_of_restrictedConverse_core` without its `MordellWeil`
hypothesis, Mordell's theorem for `E_ℓ` being proved (`mordellWeilM`). -/
theorem poleCompleteness_of_restrictedConverse_core2 (SelmerCorankOne : WeierstrassCurve ℚ → Prop)
    (hRC : RestrictedConverse SelmerCorankOne) (h54 : Lemma54At SelmerCorankOne)
    (hK : KolyvaginRankOne) : Manuscript.PoleCompleteness :=
  poleCompleteness_of_restrictedConverse_coreM SelmerCorankOne hRC h54 hK mordellWeilM

end ZInQ.Manuscript.PoleRC
