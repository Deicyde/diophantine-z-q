# gt-dense report (partial)

Task: prove `ZInQ.GreenTaoDense` from the vendored Ilin proof of Green–Tao, following
`docs/research/gt-dense.md`. Log: `scratch/gt-dense/log.md`.

**Status: partial.** Step 1 is done and in the build. Steps 2–6 are written as drafts in
`scratch/gt-dense/draft/` and typecheck against the vendored modules that were already ported. They
are not in the build because the gt-import report (`.fleet/gt-import.md` on `wip/gt-import`) never
appeared: I waited from 2026-11-09 23:17 to 2026-11-10 04:17, checking every ten minutes, and
`wip/gt-import` stayed at "GreenTao port batch 2" throughout. Steps 3 (the `Main.lean` variants)
and 4 (final build and axiom checks of `ZInQ.greenTaoDense`) are therefore not done.

## Leaves

| article / plan item | Lean name | status |
|---|---|---|
| plan §4.4 window lemma (step 1) | `ZInQ.GreenTaoDense.frequently_window_of` (`External/GreenTaoDense/Window.lean`), `ZInQ.GreenTaoDense.frequently_window` (`External/GreenTaoDense.lean`) | proved |
| plan §4.4 dyadic decomposition | `card_filter_range_le_sum_windows`, `card_filter_range_le_add_Ioc` | proved |
| plan §4.4 Bertrand modulus selection | `exists_prime_scale_near`, `card_window_le_card_quarter`, `exists_prime_modulus_of_frequently_window` | proved |
| plan §4.4 Chebyshev bounds | not needed (Mathlib `Chebyshev.pi_ge` used directly; see below) | — |
| plan §4.1 A-weight | `wTrickedSetWeight`, `_nonneg`, `_le`, `_pos_iff` (draft `SetWeight.lean`) | draft, typechecks |
| plan §4.5 extraction | `containsAP_of_wTrickedSetWeight_offDiagMass_pos` (draft `SetWeight.lean`) | draft, typechecks |
| plan §4.3 density selection | `exists_reducedResidue_setWeight_mean_lower_bound` (draft `SetWeight.lean`) | draft, typechecks |
| plan §4.2 transference | `HasPrimeModulusSubweightCounts`, `hasPrimeModulusSubweightCounts_of_orderedRemoval_of_linearForms` (draft `PrimeModulusTransference.lean`) | draft, typechecks |
| plan §4.2 transference, closed | `hasPrimeModulusSubweightCounts` | draft, not checked (needs the unported Sieve/Hypergraph modules) |
| plan §4.5 assembly | `containsAP_of_frequently_window` (draft `Assembly.lean`) | draft, typechecks |
| bridge | `ZInQ.greenTaoDense` (draft `Bridge.lean`) | draft, not checked |
| step 3 | `exists_bounded_integer_polynomial_defining_integers_of_goodPrimeDensity`, `..._of_certifiedRankSel_goodPrimeDensity` | not done |

"Typechecks" means `lean` accepted the file against the oleans that `wip/gt-import` had already built
(`Submission.Primes.*`, `Submission.GreenTao.*` up to `FinalTransferenceAssembly`). The assembly
was checked in one concatenated file together with the drafts it uses.

## Statement corrections and deviations from the plan

- **Window lemma: Chebyshev's upper bound is not needed.** The plan (§3 step 1) uses a fixed
  number `J` of dyadic windows and bounds the tail by `π(Y) ≪ Y / log Y`. Instead I take
  `J = log₂ ⌊√N⌋`. Every window then has `Z_j ≥ ⌊√N⌋`, so `log Z_j ≥ log N / 3`. The tail
  `[0, N/2^J]` has at most `2√N + 2` elements, so it is bounded trivially. Only Mathlib's lower bound
  `Chebyshev.pi_ge` is used. The constant is `c₁ = c log 2 / 24`.
- `frequently_window_of` states the density hypothesis unfolded, so that `Window.lean` imports only
  Mathlib. `frequently_window` in the root module is the statement for
  `ZInQ.PrimesRelUpperDensityPos`.
- The window transfer is one lemma, `exists_prime_modulus_of_frequently_window`. It outputs a prime
  `q ≥ Q₀` with `X = W⌊q/8⌋ ≥ Q₀` and `(c₁/6) X / log X ≤ |A ∩ (X/4, X]|`, which is what the
  assembly consumes.
- The assembly needs no copy of `chebyshev_wTrick_lower_bound` with a general constant. The vendored
  lemma is linear in `α`, so it is applied with `α' = 4 α c₂ / log 2`. The density passed to the
  transference is `δ = α c₂ / 32` with `c₂ = c₁ / 6`.
- Layout: the plan put the adapted files under `ThirdParty/GreenTao/GreenTaoDense/`. As the task
  requires, they will live under `ZInQKernel/External/GreenTaoDense/` (namespace
  `ZInQ.GreenTaoDense`, with `open Submission.GreenTao`). The adapted files carry an Apache-2.0
  header that names the source files and commit and states the modification.

## Problems

- The gt-import library did not reach a buildable state during this run, so nothing that imports it
  is in the build.

## Next agent

1. Once `wip/gt-import` reports that `GreenTaoVendor` builds, run `git merge origin/wip/gt-import`.
2. Move `scratch/gt-dense/draft/{SetWeight,PrimeModulusTransference,Assembly}.lean` to
   `ZInQKernel/External/GreenTaoDense/`. In `PrimeModulusTransference.lean`, `import Submission`
   (or the three modules `Submission.GreenTao.FinalTransferenceAssembly`,
   `Submission.Sieve.StandardCyclicLinearForms`,
   `Submission.Hypergraph.SourceFullBundleRemovalAssembly`).
3. Import `ZInQKernel.External.GreenTaoDense.Assembly` from the root `External/GreenTaoDense.lean`,
   and append the contents of `draft/Bridge.lean` inside its `namespace ZInQ.GreenTaoDense`.
4. Add the two `Main.lean` variants: `..._of_greenTaoDense hH hCR greenTaoDense hD` and
   `..._of_certifiedRankSel_greenTaoDense hH hCRS greenTaoDense hD`. `Main` then imports the
   vendored library; budget the build time.
5. Run `lake build ZInQKernel`, `python3 scripts/check_target.py`, and `#print axioms` on
   `ZInQ.greenTaoDense` and the new variants.
