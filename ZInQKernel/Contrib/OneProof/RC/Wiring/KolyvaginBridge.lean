import ZInQKernel.Contrib.CloudB3RC53.Prints.Kolyvagin

/-!
# Kolyvagin's Theorem 1 on the main route from its printed statement

The §5 route's hypothesis `PoleS12.KolyvaginThm1` (not used by the Theorem 5.3 headline, whose
Kolyvagin input is `Prints.kolyvagin`), the case `r = 1` of Kolyvagin's Theorem 1, takes the
premise `IsModular E`, which is not Kolyvagin's: Theorem 1 of the print (MPIM preprint MPI/90-69
(1990), pp. 4–5) assumes a weak Weil parametrization `X₀(N) → E` with `N` the conductor (p. 3).
The manuscript passes from BCDT's modularity directly to that hypothesis (tex 1092–1093).

* `kolyvaginThm1_of_weilParam` (PROVED): the main route's hypothesis follows from the gap
  `ModularToWeakWeil` (a modular curve has a weak Weil parametrization; GLUE, which the manuscript
  carries out for `E_ℓ` at tex 1779–1788) and Kolyvagin's Theorem 1 with its own premise
  (`KolyvaginThm1WeilParam`), both in
  `CloudB3RC53/Prints/Kolyvagin.lean`. The analytic rank one of the hypothesis is the print's case
  `r = 1` (`analyticRank_one_iff`).
* `kolyvaginRankOne_of_weilParam` (PROVED): the main route's `KolyvaginRankOne` from BCDT's
  Theorem A, the gap and the print, through `kolyvaginRankOne_of_printed`.

Classification: PROVED from `ModularToWeakWeil` (GLUE; the manuscript carries it out for `E_ℓ` at
tex 1779–1788) and `KolyvaginThm1WeilParam`.
Both state the parametrization through its analytic model, so they are faithful to the manuscript
and the print only modulo the translation between an algebraic `X₀(N) → E` over `ℚ` and those
analytic data, an unproved GLUE step (see their docstrings).
-/

namespace ZInQ.Manuscript.PoleS12

open ZInQ.Contrib.CloudB3RC53

/-- **The main route's Kolyvagin hypothesis from the gap `ModularToWeakWeil` and Kolyvagin's
printed Theorem 1** (PROVED): the modular curve has the weak Weil parametrization that Kolyvagin's
Theorem 1 assumes, and the analytic rank one of the hypothesis is the print's case `r = 1`. -/
theorem kolyvaginThm1_of_weilParam (hG : ModularToWeakWeil) (hK : KolyvaginThm1WeilParam) :
    KolyvaginThm1 := by
  intro E hE hM hA
  obtain ⟨hr, hsha⟩ := hK E hE (hG E hE hM) 1 le_rfl ((analyticRank_one_iff E).2 hA)
  exact ⟨by simpa using hr, hsha⟩

/-- **The main route's `KolyvaginRankOne` from BCDT's Theorem A, the gap and Kolyvagin's printed
Theorem 1** (PROVED, through `kolyvaginRankOne_of_printed`). -/
theorem kolyvaginRankOne_of_weilParam (hB : BCDTThmA) (hG : ModularToWeakWeil)
    (hK : KolyvaginThm1WeilParam) : ZInQ.Manuscript.PoleRC.KolyvaginRankOne :=
  kolyvaginRankOne_of_printed hB (kolyvaginThm1_of_weilParam hG hK)

end ZInQ.Manuscript.PoleS12
