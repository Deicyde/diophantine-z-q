# period-odd (fleet summary)

**Verdict: target met.** `CdTwistedPeriodOdd` is not proved and is no longer needed. In Lean, with standard axioms:

`ZInQ.PeriodOdd.grossZagierFormulaCd_of_etaW32 : GrossZagierModuliOptCd → EtaW32Character → GZHL3.GrossZagierFormulaCd`

(`ZInQKernel/Contrib/OneProof/PeriodOdd.lean`). So `hL3` in route A rests on two printed leaves only: gz-optimal's
Gross–Zagier leaf and cd-optimal's eta-quotient law. No new leaf, no new glue.

**Idea.** cd-optimal's `Λ_d ⊆ L` plus Gaussian classification leave two cases. In the first, `C_d` is optimal
(route A as before). In the second, `Λ_d = k(1+i)L` and the 2-isogenous `E'_d : y² = x³ + 4d²x` is optimal. gz-optimal's
leaf already covers `E'_d` (every short model with the L-function of `C_d`), and the explicit 2-isogeny
`(x, y) ↦ (x − d²/x, y(x²+d²)/x²)` transports the Heegner point and torsion back to `C_d`.

**What compiles** (`lake build ZInQKernel.Contrib.OneProof.PeriodOdd`; axioms `[propext, Classical.choice, Quot.sound]`):
- `PeriodOdd/LFunction.lean`: `L(E'_d) = L(C_d)` for Mathlib's L-function. The ingredients are a character-sum
  identity and minimality at 2 from `c₄`.
- `PeriodOdd/Isogeny.lean`: `℘` split over `L' = L ⊔ (h+L)`, `℘_L(h) = 0`, and the group law, giving
  `φ(weierPt C_d L z) = weierPt E'_d L' z`. Also: `L'` is a period lattice of `E'_d`, and `φ` is defined over `ℚ`.
- `PeriodOdd/NeZero.lean`: `Λ_f ≠ 0` for every weight-2 newform. A `Γ₀(N)`-invariant Eichler integral would be a
  weight-0 modular form; Mathlib's `eq_const_of_weight_zero` makes it constant, so `f = 0`.
- `PeriodOdd.lean`: `lattice_cases`, `core_isog`, `cd_or_ePrime_optimal`, and the main theorem.
- `scratch/period-odd/MainEdit.lean`: `ZInQ.FrozenTarget` with `hL3` replaced by the two leaves (standard axioms).
- `#discharges` output and `autofold.json` (field `grossZagierFormulaCd`) are recorded. The dry run needs the
  `C_d` split of `hL3` folded first, as for cd-optimal.

**What remains.** `CdTwistedPeriodOdd` and gz-optimal's `CdOptimal` (`C_d` itself is optimal) are open but off the
route; the status is in report §4. Report: `docs/research/period-odd.md`.
