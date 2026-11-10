# gt-dense2 report

Task: finish gt-dense. The goal was to prove `ZInQ.GreenTaoDense` from the vendored Green–Tao library
(`GreenTaoVendor`, merged from `wip/gt-import` at 90d1e0c) and add main-theorem variants without
that hypothesis. **Status: done.** Everything builds with no sorry.

## Leaves (table of .fleet/gt-dense.md, updated)

| article / plan item | Lean name | status |
|---|---|---|
| plan §4.4 window lemma (step 1) | `ZInQ.GreenTaoDense.frequently_window_of` (`External/GreenTaoDense/Window.lean`), `ZInQ.GreenTaoDense.frequently_window` (`External/GreenTaoDense.lean`) | proved |
| plan §4.4 dyadic decomposition | `card_filter_range_le_sum_windows`, `card_filter_range_le_add_Ioc` | proved |
| plan §4.4 Bertrand modulus selection | `exists_prime_scale_near`, `card_window_le_card_quarter`, `exists_prime_modulus_of_frequently_window` | proved |
| plan §4.4 Chebyshev bounds | not needed (Mathlib `Chebyshev.pi_ge`) | — |
| plan §4.1 A-weight | `wTrickedSetWeight`, `_nonneg`, `_le`, `_pos_iff` (`External/GreenTaoDense/SetWeight.lean`) | proved |
| plan §4.5 extraction | `containsAP_of_wTrickedSetWeight_offDiagMass_pos` (`SetWeight.lean`) | proved |
| plan §4.3 density selection | `exists_reducedResidue_setWeight_mean_lower_bound` (`SetWeight.lean`) | proved |
| plan §4.2 transference | `HasPrimeModulusSubweightCounts`, `hasPrimeModulusSubweightCounts_of_orderedRemoval_of_linearForms` (`External/GreenTaoDense/PrimeModulusTransference.lean`) | proved |
| plan §4.2 transference, closed | `hasPrimeModulusSubweightCounts` (same file) | proved |
| plan §4.5 assembly | `containsAP_of_frequently_window` (`External/GreenTaoDense/Assembly.lean`) | proved |
| bridge | `ZInQ.greenTaoDense : ZInQ.GreenTaoDense` (`External/GreenTaoDense.lean`) | proved |
| step 3 | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeDensity`, `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_goodPrimeDensity` (`ZInQKernel/MainGreenTao.lean`) | proved |

The three drafts typechecked unchanged against the finished library. They were moved with `git mv`,
with no edits to their contents. They keep their Apache-2.0 headers, which name the source files, the
upstream commit and the change. `scratch/gt-dense/draft/` is deleted.

`ZInQKernel/MainGreenTao.lean` imports `ZInQKernel.Main` and `ZInQKernel.External.GreenTaoDense`.
Its two theorems apply the `_of_greenTaoDense` and `_of_certifiedRankSel_greenTaoDense` variants of
`Main.lean` to `ZInQ.greenTaoDense`. `Main.lean` is unchanged and does not import the vendored library.

## Checks

- `lake build ZInQKernel`: success (9847 jobs). It took 5 min 22 s of wall time and also built the
  vendored library, whose own build times are in `.fleet/gt-import.md`.
- `python3 scripts/check_target.py`: "FrozenTarget matches lean/Frozen/BoundedIntegerPolynomial.lean".
- `#print axioms` on `ZInQ.greenTaoDense`, `..._of_goodPrimeDensity` and
  `..._of_certifiedRankSel_goodPrimeDensity` gives only `[propext, Classical.choice, Quot.sound]` for each.
- None of the new files has `sorry`, `axiom` or `native_decide`.

## Build times of the new modules

These are lake's times from the full build. Most of each time goes to loading Mathlib and the vendored library.

| module | time |
|---|---|
| External.GreenTaoDense.Window | 8.7 s |
| External.GreenTaoDense.SetWeight | 6.1 s (`lake env lean` on its own, 6.8 GB peak) |
| External.GreenTaoDense.PrimeModulusTransference | 6.7 s |
| External.GreenTaoDense.Assembly | 7.0 s (on its own: 6.1 s, 6.9 GB) |
| External.GreenTaoDense (root, bridge) | 6.8 s |
| MainGreenTao | 4.2 s |

In the first lake run, SetWeight was reported at 163 s, but that run also built the vendored modules it
depends on. Run on its own, SetWeight takes 6 s.

## Statement corrections

None beyond those already listed in `.fleet/gt-dense.md`. Those were deviations from the plan, not
from the target: `GreenTaoDense` is proved exactly as stated in `Hypotheses/GreenTao.lean`.

## Lemmas added beyond the leaves

None in this run.

## Problems / not done

None. The vendored library and lake still print deprecation, linter and "module system" warnings.
These are warnings only.

## Suggestions

- The main theorem now needs three hypotheses: `SixContactMin`, `CertifiedRank` (or `CertifiedRankSel`)
  and `GoodPrimeDensity`. These use `exists_bounded_integer_polynomial_defining_integers_of_goodPrimeDensity`.
  The blueprint can mark `GreenTaoDense` as proved (`lean: ZInQ.greenTaoDense`).
