[`T10Etale.T10_TateDualityLocal`](../../ZInQKernel/Contrib/OneProof/T10Narrow.lean) restricts T10 to finite extensions `F/ℚ_p` and sets `ℓ = p`. It asks for the same `ℤ_p`-linear isomorphism
`H¹(A_F̄, ℤ_p) ≃ Hom_{ℤ_p}(T_p A, ℤ_p)`, intertwining `galH` with the contragredient Tate action, for every abelian variety `A/F`. It drops arbitrary ground fields and independent coefficient primes, including positive characteristic and its comparison between algebraic and separable closures. The manuscript's application is to a surface; the Lean consumers retain arbitrary dimension. A proof of the existing row is sufficient: `T10Etale.t10Local_of_tateDuality` instantiates it at `(F,p)` using `DeRhamPrint.natCast_p_ne_zero` for the invertibility condition.

## Census

Base: `7c092f8c3753f783037df1d31a7253feb70fa323`. The census follows the theorem types and proof terms from `ZInQ.OneProof.frozenTarget` and includes bundle constructor types. Importing a module is not a proof dependency. The scan can stop at dependency packages because none can reference a constant defined in `ZInQKernel`. [census.md](../../scratch/t10-narrow/census.md) lists each reader, forwarding declaration and instance. [census-output.txt](../../scratch/t10-narrow/census-output.txt) records three projection reads and eight Scholze readers; `dual_of_H1` is the only actual application. The manuscript's auxiliary field `K` from `lem:de-rham-descent` does not instantiate the old T10 binder `K`: the application is over the field of definition `F`.

## Readers and bypass

The eight live Scholze readers are re-proved with suffix `_loc` in [T10NarrowReaders.lean](../../ZInQKernel/Contrib/OneProof/T10NarrowReaders.lean). Only `dual_of_H1_loc` applies the narrowed input; it uses the same `DeRhamPrint.toKer A`, `milneE` and `milneE_comm`. Two adjacent readers, the older-input compatibility theorem and the surface specialization, also have local versions. [ReaderExamples.lean](../../scratch/t10-narrow/ReaderExamples.lean) recovers each original statement by applying the corresponding local theorem to `t10Local_of_tateDuality hT`.

The generated chain copies the added bundle and the affected forwarders from TailZ87, NOSNarrowChain and TailZ91–93. Its new bundle is `HDec.HSyn.OpenAddedLeaves29_t10`, and its H top is `HDec.HSyn.sixContactMin_of_open86_t10`. For integration, import `ZInQKernel.Contrib.OneProof.T10NarrowChain`, then substitute these two names for `OpenAddedLeaves28` and `sixContactMin_of_open86` in the headline. The dry run reproduces that substitution in `ZInQ.OneProof.frozenTarget_t10`. The bypass cannot be done with an autofold discharge: the implication goes from the general statement to the local one.

**VERIFIED in Lean.** The [dry run](../../scratch/t10-narrow/dryrun-output.txt) reaches the general statement below `sixContactMin_of_open86` and `frozenTarget`. It reaches only the local statement below their `_t10` copies. The implication, all ten readers, the chain, and the dry-run headline use only `propext`, `Classical.choice`, and `Quot.sound`. The [discharge log](../../scratch/t10-narrow/discharges-output.txt) examined 15,257 theorems against the old headline and reported 347 matches, none for the general T10 row.

To replay against a build of the base, run `python3 scratch/t10-narrow/gen_bypass.py`, then use
`scratch/t10-narrow/serial_lean.py` with `--cache-base 7c092f8c3` and the three scratch checks
`Census.lean`, `ReaderExamples.lean`, and `DryRun.lean` (give their repository-relative paths).
The helper invokes `lake env lean` serially and checks host load and available memory before each invocation.

## Count and proposed kinds row

| Reading | Before | After |
|---|---:|---:|
| Strict (H, LEAF / GLUE) | 5 / 24 | 5 / 24 |
| Strictest (H, LEAF / GLUE) | 5 / 24 | 5 / 24 |
| Total headline open entries | 33 | 33 |

The [proposed TSV row](../../scratch/t10-narrow/kinds-row.tsv) is `added / t10TateDualityLocal / consequence / GLUE / GLUE`, pending review. It replaces `t10TateDuality` and records the generality dropped above. The [generator output](../../scratch/t10-narrow/generator-output.txt) records the validation and the project's strict and strictest count functions. The dry run checks that the other 32 headline entries have identical types.

## Known issues

- **VERIFIED (recorded page reading).** The manuscript cites Milne, *Abelian Varieties* v2.0, Part I, Thm 12.1(a), p. 55. The previous page reading recorded in `docs/one-proof/kinds.tsv` also locates Galois compatibility in Rem. 12.5, p. 56, stated without proof. The notes are unrefereed; whether they can qualify as a literature leaf is open. The old 1986 Thm 15.1(a) locator remains UNVERIFIED and is not used here. No mathematical error was found in the cited local identification.
- **VERIFIED (definition); SPECULATIVE (route to formalization).** Mathlib's `Scheme.EllAdicCohomology` uses cohomology of the continuous `ℤ_p` coefficient sheaf on the big pro-étale site. Mathlib flags agreement with classical étale cohomology as future work. The smallest comparison needed here is a natural `ℤ_p`-linear equivalence in degree one for the geometric abelian variety,
  `H¹_proét(A_F̄, ℤ_p) ≃ limₙ H¹_ét(A_F̄, ℤ/pⁿ)`, compatible with transport by `1 × Spec(σ⁻¹)`. Bhatt–Scholze, *The pro-étale topology for schemes*, §5.6 (locator UNVERIFIED) suggests the comparison; the dictionary to Mathlib's site, coefficient modules and transport is on the spot, provenance (c). A formal proof would need finite-coefficient site comparison and the passage to the inverse limit. In degree one the obstruction `lim¹ H⁰` vanishes because `A_F̄` is connected and the constant `ℤ/pⁿ` sections have surjective transition maps. Combined with the classical identification and its naturality under the division covers, this comparison would give `T10_TateDualityLocal`. The equivariance argument to formalize is that transport of a division cover conjugates translation by a torsion point to translation by its Galois conjugate; pulling back on homomorphisms gives the inverse in the contragredient formula. This is site and cohomology infrastructure, beyond the specialization and bypass.
- The manuscript uses the rational dual identification. The integral form is already the project's input; `milneE` base changes it to `ℚ_p` using finite freeness, and `milneE_comm` transports equivariance. The restriction introduces no canonicality requirement beyond the old existential formulation. Functoriality of `galH` is outside this check.

## Manuscript check

The checks use the manuscript and the repository's existing source audit; no new primary-source reading was done.

| `diophantine_zq.tex` | Verdict | Check |
|---|---|---|
| L10939–10941 | OK | If `F/K` and `K/ℚ_ℓ` are finite then `F/ℚ_ℓ` is finite. The manuscript uses `g = 2`; the route's transport lemmas work for every `g`. |
| L10953–10957 | OK | The step applies the filtered de Rham comparison to the proper smooth rigid analytification, with the corrigendum. The Lean transport keeps the existing Scholze input as a hypothesis. |
| L10958–10959 | OK | The coherent comparison on the differential forms respects the filtered complex and gives the filtered de Rham comparison. |
| L10959–10961 | OK | The finite coefficient comparison is compatible with reduction of coefficients; `p` is invertible in the characteristic-zero field `F`. The Lean proof of the nonzero cast is `DeRhamPrint.natCast_p_ne_zero`. |
| L10962–10965 | OK | Naturality supplies Galois compatibility before passing to the limit and rational coefficients. These are comparisons of classical étale cohomology; the separate comparison to Mathlib's pro-étale cohomology remains open. |
| L10966–10972 | OK | The local Galois-equivariant identification has the cited Milne theorem and the accompanying equivariance remark as its classical input. The Lean base change gives `H¹_ét ≃ V_p(A)^∨`; dualizing and using finite-dimensional double duality yields the orientation used in the manuscript. |
| L10973–10975 | OK | The transfer of de Rhamness to the Tate module uses closure under duals; the forwarders reuse the existing Lean proof of this step. |
| L10996–10997 | OK | The jumps for the dual Tate representation are `0,1` with multiplicities `g,g`; the manuscript states the Tate-module weights with `ℚ_ℓ(1)` of weight `-1`. |
