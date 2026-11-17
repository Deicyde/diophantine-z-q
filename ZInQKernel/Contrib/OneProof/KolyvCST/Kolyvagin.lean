import ZInQKernel.Contrib.OneProof.PoleS12.Leaves

/-!
# Kolyvagin's Theorem 1 as the manuscript cites it: both analytic ranks `r = 0` and `r = 1`

Task kolyv-cst-printed (fork issue #83, after pc-from-rc and pc-s12). No proofs of literature
theorems: this file states and bridges.

The manuscript (`diophantine_zq.tex`, Lemma 5.5 `lem:forward-rank`, L1086–1109) cites
`\cite[Theorem 1, pp. 4–5]{kolyvagin}` (L1093) "whose statement includes both `r = 0` and
`r = 1`", after modularity `\cite[Theorem A]{bcdt}` (L1092). pc-s12 stated only the `r = 1` case
(`PoleS12.KolyvaginThm1`). The proof of Theorem 5.3 also uses the `r = 0` case
(L2386, L7626, L7780, L8267: "the forward rank-zero theorem"). This file adds:

* `AnalyticRank E r`: `ord_{s=1} L(E, s) = r`, over Mathlib's `WeierstrassCurve.LSeries`, in the
  convention of `Manuscript.AnalyticRankOne` (`analyticRank_one_iff`).
* `KolyvaginThm1Printed` (printed leaf, as cited): a modular elliptic curve `E/ℚ` with analytic
  rank `r ≤ 1` has `rank E(ℚ) = r` and finite `Ш(E/ℚ)` (`SelmerTwoPower.sha`).
* `kolyvaginThm1_of_printed`: pc-s12's `KolyvaginThm1` (the `r = 1` case) is a consequence.
* `ForwardRank` (Lemma 5.5, first sentence) from `BCDTThmA` and `KolyvaginThm1Printed`
  (`forwardRank_of_printed`), and `KolyvaginRankOne` from it (`kolyvaginRankOne_of_forwardRank`).
* `KummerCorank` (textbook GLUE, not proved: the Kummer sequence for `E[2^∞]`), and
  `ForwardCorank` (Lemma 5.5, second sentence: `corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = r`) from
  `ForwardRank`, `MordellWeil` and `KummerCorank` (`forwardCorank_of`).

Known issue (docs/research/kolyv-cst-printed.md §5): Kolyvagin's hypothesis "modular" is, in the
print as an earlier audit reports it, a weak Weil parametrization `X₀(N) → E` with `N` the
conductor; `PoleS12.IsModular` (written fresh by pc-s12) is the `L`-series form. The Lean
statements over `IsModular` are therefore consequences of Kolyvagin's Theorem 1 together with BCDT
Theorem A (which gives geometric modularity of every `E/ℚ`), not of Kolyvagin's theorem alone.
-/

namespace ZInQ.Manuscript.KolyvCST

open ZInQ.Manuscript.PoleRC ZInQ.Manuscript.PoleS12 ZInQ.Manuscript.SelmerTwoPower

/-- **`ord_{s=1} L(E, s) = r`**: some entire function agrees with Mathlib's `L`-series of `E`
(`WeierstrassCurve.LSeries`, the Euler product of the local factors of a minimal model) on
`Re s > 3/2` and vanishes to order exactly `r` at `s = 1`. For `r = 1` this is
`Manuscript.AnalyticRankOne` (`analyticRank_one_iff`); for `r = 0` it says that the continuation
does not vanish at `s = 1`. An entire function is determined by its values on `Re s > 3/2`, so the
order does not depend on the choice of `F`. -/
def AnalyticRank (E : WeierstrassCurve ℚ) (r : ℕ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ (∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s) ∧
    analyticOrderAt F 1 = r

theorem analyticRank_one_iff (E : WeierstrassCurve ℚ) :
    AnalyticRank E 1 ↔ AnalyticRankOne E := by
  simp only [AnalyticRank, AnalyticRankOne, Nat.cast_one]

/-- **Kolyvagin, Theorem 1, as the manuscript cites it** (printed leaf; tex L1093
`\cite[Theorem 1, pp. 4–5]{kolyvagin}`, "whose statement includes both `r = 0` and `r = 1`";
bibitem L11163–11166: V. A. Kolyvagin, "On the Mordell–Weil group and the Shafarevich–Tate group
of modular elliptic curves", MPIM preprint MPI/90-69 (1990), Theorems 1–5, pp. 4–5). For a
modular elliptic curve `E/ℚ` with `ord_{s=1} L(E, s) = r ≤ 1`: `rank E(ℚ) = r` and `Ш(E/ℚ)` is
finite.

Clause check (docs/research/kolyv-cst-printed.md §1): every clause is **UNVERIFIED (pending
reading)**; not read in the print for this task (no network). An earlier audit in this
repository (docs/theorem-application-audit/evidence/parallel-forward-modularity-report.md, A020)
reports reading printed p. 4: "rank(E) = analytic-rank(E) and finite Sha(E) whenever
analytic-rank(E) ≤ 1", for `E/ℚ` modular in the sense of a weak Weil parametrization
`X₀(N) → E` (printed p. 3). Here "modular" is `PoleS12.IsModular` (the `L`-series form; Known
issue), `rank` is `Module.rank ℤ E(ℚ)`, `Ш` is Tau Ceti's Shafarevich–Tate group with the
conditions at every place of `ℚ` (`SelmerTwoPower.sha`). -/
def KolyvaginThm1Printed : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E → ∀ r : ℕ, r ≤ 1 → AnalyticRank E r →
    Module.rank ℤ E.toAffine.Point = r ∧ Finite (sha E)

/-- pc-s12's `KolyvaginThm1` (the case `r = 1`) is a consequence of `KolyvaginThm1Printed`. -/
theorem kolyvaginThm1_of_printed (h : KolyvaginThm1Printed) : KolyvaginThm1 := by
  intro E hE hM hA
  have := h E hE hM 1 le_rfl ((analyticRank_one_iff E).mpr hA)
  simpa using this

/-- **Lemma 5.5 (`lem:forward-rank`, tex L1086–1088), first sentence.** For an elliptic curve
`A/ℚ` with `ord_{s=1} L(A, s) = r ≤ 1`: `rank A(ℚ) = r` and `Ш(A/ℚ)` is finite. The manuscript
proves it from BCDT Theorem A and Kolyvagin Theorem 1 (L1092–1093); `forwardRank_of_printed`. -/
def ForwardRank : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ r : ℕ, r ≤ 1 → AnalyticRank E r →
    Module.rank ℤ E.toAffine.Point = r ∧ Finite (sha E)

/-- **Lemma 5.5, first sentence, from the two prints** (tex L1092–1093). -/
theorem forwardRank_of_printed (hB : BCDTThmA) (hK : KolyvaginThm1Printed) : ForwardRank :=
  fun E hE r hr hA => hK E hE (hB E hE) r hr hA

/-- pc-from-rc's `KolyvaginRankOne` from `ForwardRank`. -/
theorem kolyvaginRankOne_of_forwardRank (h : ForwardRank) : KolyvaginRankOne :=
  fun E hE hA => by simpa using (h E hE 1 le_rfl ((analyticRank_one_iff E).mpr hA)).1

/-- **The Kummer sequence for `E[2^∞]`, corank form** (textbook GLUE, not proved; Silverman,
*The Arithmetic of Elliptic Curves*, X.4, with `E[m]` replaced by `E[2^∞]`: the exact sequence
`0 → E(ℚ) ⊗ ℚ₂/ℤ₂ → Sel_{2^∞}(E/ℚ) → Ш(E/ℚ)[2^∞] → 0`, which the manuscript invokes at
L1097–1102 as "the ordinary Kummer sequence"). If `E(ℚ)` is finitely generated of rank `r` and
`Ш(E/ℚ)` is finite, then `corank_{ℤ₂} Sel_{2^∞}(E/ℚ) = r`: the sequence splits because
`(ℚ₂/ℤ₂)^r` is divisible, giving `Sel_{2^∞} ≅ (ℚ₂/ℤ₂)^r × Ш[2^∞]`. ELLIOT (provenance (a)) for the
deduction, textbook for the sequence. -/
def KummerCorank : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ r : ℕ, AddGroup.FG E.toAffine.Point →
    Module.rank ℤ E.toAffine.Point = r → Finite (sha E) → Z2Corank (selmerTwoPower E) r

/-- **Lemma 5.5 (`lem:forward-rank`, tex L1089), second sentence**: for an elliptic curve `A/ℚ`
with `ord_{s=1} L(A, s) = r ≤ 1`, `corank_{ℤ₂} Sel_{2^∞}(A/ℚ) = r`. The `r = 0` case is the
"forward rank-zero theorem" of the proof of Theorem 5.3 (tex L2386, L7626, L7780, L8267). -/
def ForwardCorank : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic → ∀ r : ℕ, r ≤ 1 → AnalyticRank E r →
    Z2Corank (selmerTwoPower E) r

/-- **Lemma 5.5, second sentence**, from the first, Mordell–Weil and the Kummer sequence
(tex L1097–1102). -/
theorem forwardCorank_of (hF : ForwardRank) (hMW : MordellWeil) (hKum : KummerCorank) :
    ForwardCorank := fun E hE r hr hA =>
  have h := hF E hE r hr hA
  hKum E hE r (hMW E hE) h.1 h.2

/-- **Lemma 5.5 in full, from the printed leaves and the textbook glue.** -/
theorem forwardRank_and_corank_of_printed (hB : BCDTThmA) (hK : KolyvaginThm1Printed)
    (hMW : MordellWeil) (hKum : KummerCorank) : ForwardRank ∧ ForwardCorank :=
  ⟨forwardRank_of_printed hB hK, forwardCorank_of (forwardRank_of_printed hB hK) hMW hKum⟩

end ZInQ.Manuscript.KolyvCST
