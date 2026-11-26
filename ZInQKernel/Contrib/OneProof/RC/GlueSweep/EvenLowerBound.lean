import ZInQKernel.Contrib.OneProof.RC.Even.EvenSource
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Bridges
import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Kato
import ZInQKernel.Contrib.CloudB3RC53.Prints
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.AnaForward

/-!
# Lane RC22 (glue sweep), even share: modularity and the forward rank-zero theorem for lane RC11

Lane RC11 (`ZInQKernel/Contrib/OneProof/RC/Even/`) states the lower bound (E.9) of Appendix E
(`evenLowerBound_of_evenScalar32`, tex 7777–7786) and the zero criterion for `L_*`
(`CentralNormalization.lstar_ne_zero_iff`, tex 1825–1830) with two hypotheses that the
integration tree now discharges:

* `hfwd : ForwardRankZero E` — the forward rank-zero theorem for the twists (`lem:forward-rank`,
  tex 1086–1108). The manuscript's proof is: modularity (BCDT Theorem A), Kolyvagin's Theorem 1 at
  `r = 0`, and the Kummer sequence. The first two are the shared printed leaf `Prints.bcdt` and
  the cited statement `Prints.kolyvagin` (GLUE); the Kummer step is
  `KummerCorankZero.kummerCorankZero_proof` (PROVED by the
  other group in `CloudB3RC53/KummerCorankZero`); lane RC22's `Ana.forwardRank_zero_of_prints`
  combines them for one curve. So `ForwardRankZero E` holds for every elliptic `E` from `Prints`
  alone (`forwardRankZero_of_prints`, applied to the twists). Lane RC9's route through Kato's
  Corollary 14.3 (`forward_rank_zero_twist`, the route named in RC11's docstring) gives the same
  (`forwardRankZero_of_kato`).
* `hcont : ∀ h ≠ 0, ∃ F, IsLContinuation (qtwist E h) F` — an entire continuation of every
  `L(E^{(h)}, s)` ("by modularity"). From the shared leaf `BCDTThmA` (every elliptic curve over
  `ℚ` is modular: a `Γ₀(N)` cusp form with the same `q`-expansion), the cusp form's Mathlib
  `L`-function is entire (vendored Tau Ceti `CuspForm.differentiable_L`) and agrees with
  `L(E, s)` on `Re s > 2` (`CuspForm.LSeries_qExpansion_coeff_eq`, width one for `Γ₀(N)`); lane
  RC8's GLUE `HasseConvergence` (absolute convergence on `Re s > 3/2`) and RC8's identity-theorem
  step `eqOn_LSeries_of_forall_summable` move the agreement to `Re s > 3/2`
  (`exists_isLContinuation_of_isModular`, `twistContinuation_of_bcdt`). The twists of an elliptic
  curve are elliptic (lane RC8's `qtwist_isElliptic`).

Bridges (consumer statements with the hypotheses removed):
* `evenLowerBound_of_evenScalar32_of_prints` — (E.9) from (3.2), `Prints` and `HasseConvergence`;
* `evenLowerBound_of_appE_of_prints` — (E.9) from Appendix E's outputs, `Prints`, `HasseConvergence`;
* `lstar_ne_zero_iff_of_bcdt` — `L_*(h) ≠ 0 ↔ ord_{s=1} L(E^{(h)}, s) = 0` without a given
  continuation.

All results here are `PROVED` (standard axioms) from the named remaining hypotheses.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Even

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53

/-- **An entire continuation of `L(E, s)` from modularity** (PROVED, from lane RC8's GLUE
`HasseConvergence`). If `E/ℚ` is elliptic and modular in the tree's sense (`PoleS12.IsModular`:
a weight-two cusp form `f` on `Γ₀(N)` whose `q`-expansion coefficients are the Dirichlet
coefficients of `L(E, s)`), then Mathlib's `L`-function of `f` is an entire continuation of
`L(E, s)` from `Re s > 3/2`. Used for the hypothesis `hcont` ("every continuation of
`L(E^{(h)}, s)` exists by modularity", tex 1779, 7782–7785) of lane RC11's
`evenLowerBound_of_evenScalar32`, `EvenPhaseData.E11` and `EvenPhaseData.minimum`. Ingredients:
`CuspForm.differentiable_L`, `CuspForm.LSeries_qExpansion_coeff_eq` (vendored Tau Ceti),
`strictWidthInfty_Gamma0` (Mathlib), lane RC8's `eqOn_LSeries_of_forall_summable`. -/
theorem exists_isLContinuation_of_isModular (hH : PrintsAnalytic.HasseConvergence)
    {E : WeierstrassCurve ℚ} (hE : E.IsElliptic) (hM : PoleS12.IsModular E) :
    ∃ F : ℂ → ℂ, IsLContinuation E F := by
  obtain ⟨N, hN, f, hf⟩ := hM
  have : NeZero N := ⟨hN.ne'⟩
  have hdiff : Differentiable ℂ (ModularForm.L two_pos f) := CuspForm.differentiable_L two_pos f
  refine ⟨ModularForm.L two_pos f, PrintsAnalytic.isLContinuation_iff.mpr ⟨hdiff, ?_⟩⟩
  refine PrintsAnalytic.eqOn_LSeries_of_forall_summable (σ₀ := 2) hdiff (fun s hs => ?_) (hH E hE)
  have hs' : ((2 : ℤ) : ℝ) / 2 + 1 < s.re := by norm_num; linarith
  have h := CuspForm.LSeries_qExpansion_coeff_eq two_pos f hs'
  simp only [CongruenceSubgroup.strictWidthInfty_Gamma0, Complex.ofReal_one, Complex.one_cpow,
    one_mul] at h
  rw [← h]
  exact LSeries_congr (fun {n} hn => hf n (Nat.pos_of_ne_zero hn)) s

/-- **Every twist `L(E^{(h)}, s)`, `h ≠ 0`, has an entire continuation** (PROVED, from the shared
printed leaf `PoleS12.BCDTThmA` (the blueprint's `Prints.bcdt`) and lane RC8's GLUE
`HasseConvergence`). This is exactly lane RC11's hypothesis `hcont` (tex 1779; used at tex
7782–7785 and 8136–8142). The twist is elliptic by lane RC8's `qtwist_isElliptic`, modular by
BCDT, and `exists_isLContinuation_of_isModular` applies. -/
theorem twistContinuation_of_bcdt (hB : PoleS12.BCDTThmA) (hH : PrintsAnalytic.HasseConvergence)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ h : ℤ, h ≠ 0 → ∃ F : ℂ → ℂ, IsLContinuation (qtwist E (h : ℚ)) F := by
  intro h hh
  have hd : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  have hE' : (qtwist E (h : ℚ)).IsElliptic := PrintsAnalytic.qtwist_isElliptic hd
  exact exists_isLContinuation_of_isModular hH hE' (hB _ hE')

/-- **The forward rank-zero theorem for the twists, from the shared prints** (PROVED; discharges
lane RC11's hypothesis `ForwardRankZero E`, `lem:forward-rank`, tex 1086–1108, used at tex
7777–7786). For elliptic `E` and `h ≠ 0`: `E^{(h)}` is elliptic (lane RC8's `qtwist_isElliptic`)
and modular (`Prints.bcdt`); `ord_{s=1} L(E^{(h)}, s) = 0` gives rank zero and finite `Ш`
(Kolyvagin's Theorem 1 at `r = 0`, `Prints.kolyvagin`), and the Kummer sequence in rank zero
(`CloudB3RC53.KummerCorankZero.kummerCorankZero_proof`, PROVED) gives
`corank_{ℤ₂} Sel_{2^∞}(E^{(h)}/ℚ) = 0`; for one curve this is lane RC22's
`Ana.forwardRank_zero_of_prints`, applied here to `E^{(h)}`. This is the manuscript's own proof of
the lemma ("Modularity follows from BCDT. Apply Kolyvagin's Theorem 1 … The ordinary Kummer
sequence gives the corank assertion", tex 1092–1103). -/
theorem forwardRankZero_of_prints (P : Prints) (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ZInQ.Manuscript.RC.Even.ForwardRankZero E := by
  intro h hh hL
  have hd : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  exact ZInQ.Manuscript.RC.GlueSweep.Ana.forwardRank_zero_of_prints P
    (PrintsAnalytic.qtwist_isElliptic hd) hL

/-- **The forward rank-zero theorem for the twists, through Kato** (PROVED; the route named in
lane RC11's docstring of `ForwardRankZero`: lane RC9's `forward_rank_zero_twist`, from Kato's
Corollary 14.3 (`KatoCor14_3`, PRINT, Astérisque 295, p. 235) and `Prints.bcdt`; tex 1104–1108,
"Independently, the `r = 0` finiteness assertion follows directly from Kato's Corollary 14.3").
`forwardRankZero_of_prints` needs no Kato leaf. -/
theorem forwardRankZero_of_kato (P : Prints) (hK : ZInQ.Manuscript.RC.PrintsArith.KatoCor14_3)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] : ZInQ.Manuscript.RC.Even.ForwardRankZero E := by
  intro h hh hL
  have hd : (h : ℚ) ≠ 0 := by exact_mod_cast hh
  exact (ZInQ.Manuscript.RC.PrintsArith.forward_rank_zero_twist P hK E (h : ℚ)
    (PrintsAnalytic.qtwist_isElliptic hd) hL).2.2

/-- **(E.9) from (3.2), with the forward rank-zero theorem and the continuations discharged**
(tex 7777–7786; PROVED from `EvenScalar32 E N L` (lane RC11's (3.2)), the shared printed leaves
`Prints` and lane RC8's GLUE `HasseConvergence`). Consumer: lane RC11's
`evenLowerBound_of_evenScalar32` (hypotheses `hfwd`, `hcont` removed). Dischargers:
`forwardRankZero_of_prints` (Kolyvagin, BCDT, `kummerCorankZero_proof`) and
`twistContinuation_of_bcdt`. -/
theorem evenLowerBound_of_evenScalar32_of_prints (P : Prints)
    (hH : PrintsAnalytic.HasseConvergence) {E : WeierstrassCurve ℚ} [E.IsElliptic] {N : ℕ}
    {L : ZInQ.Manuscript.RC.Even.CentralNormalization E}
    (h32 : ZInQ.Manuscript.RC.Even.EvenScalar32 E N L) :
    ZInQ.Manuscript.RC.Even.EvenLowerBound E L :=
  ZInQ.Manuscript.RC.Even.evenLowerBound_of_evenScalar32 h32 (forwardRankZero_of_prints P E)
    (twistContinuation_of_bcdt P.bcdt hH E)

/-- **(E.9) from Appendix E's outputs** (tex 1845–1966 then 7777–7786; PROVED from lane RC11's
ELLIOT outputs `AppEOutputs E N L`, `N ≠ 0`, the shared `Prints` and lane RC8's GLUE
`HasseConvergence`): lane RC11's `evenScalar32_of_appE` followed by
`evenLowerBound_of_evenScalar32_of_prints`. -/
theorem evenLowerBound_of_appE_of_prints (P : Prints) (hH : PrintsAnalytic.HasseConvergence)
    {E : WeierstrassCurve ℚ} [E.IsElliptic] {N : ℕ} (hN : N ≠ 0)
    {L : ZInQ.Manuscript.RC.Even.CentralNormalization E}
    (h : ZInQ.Manuscript.RC.Even.AppEOutputs E N L) :
    ZInQ.Manuscript.RC.Even.EvenLowerBound E L :=
  evenLowerBound_of_evenScalar32_of_prints P hH (ZInQ.Manuscript.RC.Even.evenScalar32_of_appE hN h)

/-- **`L_*(h) ≠ 0` exactly when `ord_{s=1} L(E^{(h)}, s) = 0`, with no continuation given**
(tex 1825–1830, 1841–1843; PROVED from `PoleS12.BCDTThmA` (`Prints.bcdt`) and lane RC8's GLUE
`HasseConvergence`). Consumer: lane RC11's `CentralNormalization.lstar_ne_zero_iff` (hypothesis
`hF : IsLContinuation (qtwist E h) F` removed; discharger `twistContinuation_of_bcdt`). -/
theorem lstar_ne_zero_iff_of_bcdt (hB : PoleS12.BCDTThmA) (hH : PrintsAnalytic.HasseConvergence)
    {E : WeierstrassCurve ℚ} [E.IsElliptic] (L : ZInQ.Manuscript.RC.Even.CentralNormalization E)
    {h : ℤ} (hh : h ≠ 0) : L.Lstar h ≠ 0 ↔ AnalyticRank (qtwist E (h : ℚ)) 0 := by
  obtain ⟨F, hF⟩ := twistContinuation_of_bcdt hB hH E h hh
  exact L.lstar_ne_zero_iff hh hF

end ZInQ.Manuscript.RC.GlueSweep.Even
