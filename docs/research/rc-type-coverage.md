# Coefficient support of an odd theta stage

**The type refinement and the arithmetic handoff are conditional on the actual sieve presentation.** The refined stage type has prime support exactly `m₁.primeFactors ∪ Scoeff`. It retains the old labels by projection, realizes every refined type outside any finite exclusion, and detects the radicals of its full support. The unchanged formwise and realization interfaces can use this type. The actual stage join is a scoped stop on this base: `AppF.ThetaStage` and `ThetaCoeff.Lift` do not record the Eichler level or the exact list of Fourier sieves, and the abstract `ThetaStage.Good` need not accept all primes outside that support.

Changing the modulus while keeping the **identical** old Galois character cannot supply the radical hypothesis at a newly covered prime. If a sieve prime was `T.Good` for the old type, `ThetaCoeff.no_good_mem_stationary` rules out its inclusion in any support detected by that character. This is an exact obstruction even if one can lift all the old CRT representatives to the larger modulus. The construction uses the existing `stageChar` at the enlarged fixed modulus; its projection is the old character on all of `GalQ`. The generic coefficient dictionary works with the refined alphabet and keeps the same sign and pair bits. No particular offending prime of the actual source can be identified without the missing sieve list.

## The two supports

`coefficientSupport S N late = {2, S.ℓ₀} ∪ N.primeFactors ∪ S.m.primeFactors ∪ late`.

| Piece | Source |
| --- | --- |
| `2` | The local Schwartz condition (tex 8517–8534, 9473–9476). |
| `S.ℓ₀` | The detecting prime of `AppF.ThetaStage`; the nonzero norm at this prime is part of the stage source (tex 8462–8463, 8551–8561, 9471–9476). `Stages.PrimeStage.p` records the prime on the selection side, and `LabelData.ℓ₀ θ` records it on the address side. Identifying them with this lift's `S.ℓ₀` is a stage join. |
| `N.primeFactors` | Primes of the conductor used as the Eichler level (tex 6835–6836, 8464–8474, 8498–8508). `ThetaStage.X` is only a finite type; it has no level index. `N` here is not `LevelSetup`'s common weight-two level. |
| `S.m.primeFactors` | `AppF.ThetaStage.m = |h_*|` by the interpretation of the field; the lift uses this `m` in `Lift.aθ` (tex 8536–8549, 8968–8981, 9475–9476). The outer stage data have `W.hstar`, but the tree does not link that value to the lift's `S.m`. |
| `late` | Exactly the primes at which the source undergoes an additional zero-or-retain Fourier sieve (tex 8427–8428, 9477–9479). `Divisions.support` records vanishing at primes rejected by `S.Good`, but neither it nor the stage nor the lift records which sieves were applied. Neither the stage sequence's exclusion set nor the stationary label tests identify that list (tex 9481–9483). |

For a stage with `S.ℓ₀ = D.ℓ₀ θ`, the initial `m₁`, positivity, divisibility by eight, and the moving-prime primality and coprimality are exactly the inputs of `LabelData.T₁ θ`. The refined stationary modulus is `m₁ * ∏ p ∈ (Scoeff \ insert S.ℓ₀ m₁.primeFactors), p`. Thus it adds only missing primes, leaves the moving bit separate, and can also repair a missing Eichler or extraction prime if the original modulus omitted one. The stationary support passed to `windowModel`, `commonSpace` or `buildWithFormwiseInertia` is the new modulus's prime-factor set. Old label-only primes already in `m₁` stay there; they do not become coefficient sieves. The active pool belongs in `avoid`, rather than in the stationary support. These modulus and domain calculations are on-the-spot (c).

## Lean statements and handoff

In the table, `T` is `coveredType`, `χ` is `coveredChar`, `Σ` is `T.m.primeFactors`, and `T₁` is the original `stageTypeData m₁ … S.ℓ₀ …`.

| Theorem or constructor | Statement and consumer |
| --- | --- |
| `mem_coefficientSupport` | Membership is equivalent to equality to 2 or the moving prime, or membership in the prime factors of the Eichler level, `S.m`, or the exact sieve list. |
| `prime_of_mem_coefficientSupport` | If the moving prime and the named sieves are prime, every member of `Scoeff` is prime; used for the modulus product. |
| `dvd_fixedModulus`, `fixedModulus_pos`, `moving_coprime` | The old stationary modulus divides the refined one; the refined one is positive; the moving prime is still coprime to it. These supply projection, the type modulus, and CRT for the moving bit. |
| `coveredType`, `coveredType_primeFactors` | Construct the type with the existing CRT `classes` and sign fields; `Σ = m₁.primeFactors ∪ Scoeff`. Use `Σ` itself for `hlevel` by reflexivity. |
| `good_not_mem_support`, `fresh_outside_support` | `T.Good q → q ∉ Scoeff`; additionally `q ∉ U` gives `q ∉ Scoeff ∪ U`. Supplies the missing exclusion for `hseed`, `hexcl` and `good_hecke` on the tested domain. |
| `good_iff_old_good_and_outside` | `T.Good q ↔ T₁.Good q ∧ q ∉ Scoeff`. The refinement adds exactly the coefficient exclusions to the original good-prime domain. |
| `stage_good` | If all primes outside `Scoeff` are recognized by `S.Good`, then `∀ p, T.Good p → S.Good p`. Supplies `thetaData`'s domain implication and the stage side of `Window`. |
| `project_type_of_good`, `project_sign`, `project_realization` | The projection returns the old type on good primes, preserves sign for all labels, and takes any refined prime realization to a realization of its projected graph by the same primes. |
| `isTypeChar_covered`, `project_coveredChar` | `IsTypeChar T χ`; applying the projection to `χ g` gives `stageChar m₁ S.ℓ₀ g` on all Galois elements. |
| `openTypeKernel_covered`, `detects_radicals_covered`, `two_mem_type_support` | `OpenTypeKernel χ`, `TypeDetectsRadicals χ Σ`, and `2 ∈ Σ`, for the existing window constructors. |
| `exists_good_of_type` | For each refined type and finite `avoid`, there is a good prime of that type outside `avoid`. The good-prime test is nonempty even after finite exclusions, and the dictionary retains its usual CRT and Dirichlet realization. |
| `old_good`, `test_coprime_old` | If `old ≠ 0` and `old.primeFactors ⊆ Scoeff`, then `∀ q, T.Good q → q.Coprime old` and `∀ q, Test T avoid q → q.Coprime old`. |
| `levelSetup`, `test_coprime_common` | Given the old-level support, `4 ∣ old`, common level `old * ∏ p ∈ P.pool, p` nonzero, and `P.pool ⊆ avoid`, construct the original `LevelSetup` and its ambient coprimality test. `realize_of_stage` accepts that setup and copies its `old_good` into the resulting `BlockLevels`. |
| `inertiaOn_of_atLevel`, `window_hseed` | From the existing `AtLevel` attachment and retained levels, inertia is trivial at every seed coordinate in `InertiaOn` and in every subset seed required by `windowModel`'s exact `hseed`. The latter constructor passes trace invariance to `buildWithFormwiseInertia`. |
| `window_hexcl` | From `AtLevel`, the same lattice, its stable trace and determinant translates, and the coefficient local ring, the excluded-prime Fourier identity holds on the original lattice with an integral diamond translate. `window_good_hecke` already combines this formwise argument with the ambient one and supplies `FormwiseHecke`; its excluded branch has the domain of `thetaData`'s `hexcl`. |
| `unchanged_char_cannot_detect` | If an old `IsTypeChar T₁ χ₁` has an old good prime in a proposed support, then `¬ TypeDetectsRadicals χ₁ support`. Explains why enlarging only the modulus is insufficient. |

No new structure or named proposition is assumed as a theorem input. The sieve list and its primality are data of the operation, not coverage or a Fourier identity. `hstage` refers only to the stage's own accepted domain and the actual support (tex 8424–8428, 9471–9479); it asserts nothing about `TypeData`, and must hold even when the old type misses a support prime. The old-level bound is the finite statement that the primes in the actual modular level occur in `Scoeff` (tex 8421–8428, 8938–8981). It says nothing about type coprimality, Frobenius, or the Hecke relation. `AtLevel` is the existing coordinate attachment, independent of the new type coverage construction.

## Remaining inputs

| Remaining input | Manuscript and owner |
| --- | --- |
| The same-lift annotation: actual Eichler `N` and finite sieve list (exactly the primes of the actual zero-or-retain operations), `S.m = W.hstar.natAbs`, and `S.ℓ₀ = D.ℓ₀ θ` at the selected stage. Include `∀ p, p.Prime → p ∉ Scoeff → S.Good p`; `Divisions.support` runs in the other direction and cannot provide it. | Tex 6835–6836, 8462–8474, 8496–8566, 8424–8428, 9471–9483. **Stage join / PMLocal**, with the actual sieve choices from **ELLIOT** where they are not specified in the source presentation. Small finite annotation and comparison once the actual lift is constructed; the adelic stage and lift themselves are substantial existing work. |
| If the refined intrinsic type is used in the common address alphabet, present the common modulus as a multiple of the refined stationary modulus, retain the even modulus and splitting tests, and join the actual filters and readings. An existing common modulus need not already be divisible by a new sieve prime. | Tex 2016–2029, 2162–2163, 10288–10322, 10525–10538. **Address / stage-support lanes**. Small modulus and projection comparison; the actual filter and reading identifications remain their separate inputs. |
| Actual old level, its support bound and `4 ∣ old`; the pool, budget, `common` and `avoid` choice, and the same lift `E` and divisions `D`. The common phase `η`, its evaluation and order, and odd unary parity `hodd`. | Tex 8421–8428, 8938–8985, 9447–9455, 9471–9489, 9491–9555, 9618–9646. **Old stage law** for the actual level and phase; **stage join** for tests; **existing division inputs** for depth and support. Arithmetic handoff is proved once these data are supplied. |
| The weighted old transformation `hOld`, moving Fourier operators `hSieve`, rank-one unary transformation `hUnary`, and ordinary theta multiplier and cusp law `hθ`. | Tex 8623–8637, 8914–8988, 9497–9555, 9618–9625, 9647–9648. **Old stage law lane** for the substantial local Weil specialization; **ELLIOT / missing theory** for the finite moving multiplier/cusp calculation, rank-one Poisson specialization and small ordinary theta package. |
| Coefficient rings and embedding `κ`, an inventory `X` with occurrence levels, `SpansOverComplex X κ`, and the intrinsic attachments `SourceAttachment` (cusp inertia, polynomial and good recursion, Eisenstein pair, continuity). These give `AtLevel` when invoking `realize_of_stage`. | Tex 9647–9668, 9754–9797. **ELLIOT / constituent comparison** for the substantial spanning and coefficient comparison, **existing Carayol specialization** and **Eisenstein form/slash lanes** for the source attachments. |
| The model's `R₀, B`, Frobenius choices and `hfrob`, lattice continuity and finiteness assumptions, coefficient injection and embedding, local ring, maximal ideal containing 2 and closedness, and the two-fresh coefficient identity. | Tex 9638–9668, 9688–9695, 9741–9750. **Existing coefficient and Frobenius interfaces** and **two-fresh lane**. Type kernel and radical inputs are proved here. |
| To invoke all of `thetaData`: `B ≤ W + 1`, `S.ap = ap`, `hcore` for the same integral source, exact signed recurrence `hsigned`, integral phase `hphase`, `hexp` on its tested domain, ambient operators and determinant coefficient comparison, and `StageValuation`. The finite-window construction supplies expansions on the window only. | Tex 9083–9093, 9447–9459, 9618–9674, 9712–9745. **Stage join / exact recurrence and valuation inputs**, **ELLIOT** for remaining lift comparisons. Exact characteristic-zero recurrence and a genuine full tested-domain expansion do not follow from modulus coverage. |

## Known issues

- There is no actual sieve list to recover on this base. The rejection predicate alone can also exclude unrelated primes; intrinsic coefficient vanishing cannot distinguish an applied sieve from coefficients that were already zero.
- The unchanged character obstruction is a limitation of a conductor-only update. The same obstruction applies to an unchanged common alphabet if it cannot see a genuinely new coordinate. No manuscript or cited-source error was established by this work. No new printed leaves or source locators from memory are used.
- Old analytic and full-domain realization hypotheses are still required. The type removes the support contradiction; it does not produce the old theta transformation or make zero-extended seeds into actual forms outside the window.

## Manuscript check

- 2016–2025 — **OK**: the types read the unit squareclasses at the fixed coefficient support, including modulo eight and the current reduction prime. A fixed modulus with those primes is allowed and, for a new sieve prime, its new squareclass coordinate is required. Projection recovers the older labels.
- 2026–2029, 9481–9483 — **OK**: stationary label tests can refine the alphabet without changing the coefficient source.
- 6835–6836, 8462–8474, 8496–8566, 8968–8981 — **unverified**: these specify the geometric support and extraction; the base does not link the level and extracted data to the exact sieve presentation of a single lift.
- 8421–8428, 8938–8981 — **unverified**: the actual modular level bound remains an input from the old stage law.
- 9471–9480 — **gap filled**: the type excludes precisely the displayed coefficient primes in addition to the preexisting label modulus; the exact list and stage `Good` identification still need to come from the actual source.
- 9491–9555, 9618–9648 — **unverified**: the old-level arithmetic is available to the existing realization; its transformation and division inputs are separate.
- 9660–9674 — **gap filled**: the unchanged `T.Good q` and `q ∉ U` imply the coefficient exclusion needed by the formwise branch, including when `q ∈ avoid`.
- 9745–9750 — **gap filled**: the actual support can be included in the prime-factor support used by the Kummer proof, and the refined character detects all of its radicals; the two-fresh identity remains separate.
- 9754–9797 — **unverified**: the unchanged realization still needs the actual constituent space and attachments.
- 9955–9974 — **OK**: refining the finite modulus leaves the CRT and Dirichlet input to the generic realization in force; the same realizing primes project to the old graph.
- 10525–10538 — **unverified**: this is a single-stage result, and no claim is made about stabilizing a family of sieve lists on an ultrafilter.

Verification: both new Lean files passed `lake env lean -j1` in sequence. The 26 theorem audits and three definition audits reported only `propext`, `Classical.choice`, and `Quot.sound`. No new print was added.
