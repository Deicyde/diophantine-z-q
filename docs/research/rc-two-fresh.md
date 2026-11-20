`TwoFresh.h2fresh` is the coefficientwise vanishing argument of `buildConstituentModel` for the actual odd-stage forms (tex 9741–9745). For every good `U` with `U.card + 1 ≤ B`, every `g, h : GalQ` and every `n ≠ 0`, the coefficient of `t(g)t(h) F_U` belongs to `m`. The conclusion uses the constructor's own lattice stability proofs. The actual source, Fourier comparisons and constituent data are named inputs.

Fix the stage for the whole budget. At each positive index choose two distinct good Frobenius primes outside `S ∪ U ∪ n.primeFactors`. The two Hecke formulas give the coefficient at `q₂ * (q₁ * n)`. The existing odd-stage bound at that index pays for both the normalization in (O.9) and the additional division by two in (O.11), since both new primes occur to odd exponent outside `U`. The unary terms have no coefficient there. The resulting integer-two divisibility of the coefficient of `H_U` passes to `F_U` and then to `m`. All lifts at distinct test primes give a dense subset of the product Galois group; the preimage of `m` under the continuous double trace coefficient is closed.

## Statements

Here `raw_U(n) = TL η U a n`, with a list of the distinct primes of `U`, and `n_U = δ + |U|`. Equalities involving a negative power of two take place in `K`, with the inclusion of `O` understood.

| Lean theorem | Statement |
| --- | --- |
| `fresh_squarefree_weight` | If `q₁,q₂` are distinct primes outside `U`, each prime to `n ≠ 0`, then `2 ≤ (oddPart (q₂ * (q₁ * n)) ∖ U).card` and `oddPart (q₂ * (q₁ * n)) ⊈ U`. |
| `ne_unary_of_oddPart` | If `n ≠ 0` and `oddPart n ⊈ U`, then `n ≠ (∏ p ∈ J, p) * k ^ 2` for every subset `J ⊆ U` of primes and every `k`. |
| `map_TL` (private, provenance (c)) | Applying a ring map to `TL η U a n` commutes with applying it to the phase and source coefficients. |
| `dvd_of_stage_dvd` (private, provenance (c)) | For `k ≤ M`, if the image of `x` in `O ⧸ (2^M)` is divisible by `2^k`, then `2^k ∣ x` in `O`. |
| `fresh_normalizations` | At a valid `OddStageSource` with `R ≥ 2` and `U` good for that stage and within its budget, weight at least two outside `U` gives one `c : O` with `2^(-n_U) raw_U(n) = 4c` and `2^(-n_U-1) raw_U(n) = 2c`. The lift uses `k = max(0, n_U + 2) ≤ M`; extra powers of two when `n_U + 2 < 0` go into `c`. |
| `two_hecke_coeff` | At distinct primes `q₁,q₂` neither dividing `n`, the two `HeckeFourier` formulas give `coeff n (T₁ (T₂ F)) = coeff (q₂ * (q₁ * n)) F`. The order of trace application is the order used by the constructor. |
| `dense_twoFreshTests` (product argument, provenance (c)) | Pairs of all Frobenius lifts at distinct good primes outside any finite `A` are dense in `GalQ × GalQ`. |
| `continuous_twoTraces` (provenance (c)) | For any fixed `v : Λ`, `ContinuousOperators ρ Λ` makes `(g,h) ↦ tV ρ g (tV ρ h v)` jointly continuous into `I → K`. At a coordinate with `vᵢ ≠ 0`, this is the product of the two singly tested coordinates divided by `vᵢ`; at a zero coordinate it is constant. |
| `h2fresh` | For the named data below, the exact `h2fresh` binder of `buildConstituentModel`: `∀ U, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g h n, n ≠ 0 → coeff n ⟨tV ρ g (tV ρ h (F U)), _⟩ ∈ m`, with the nested witnesses from `stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops`. |

## Named hypotheses

| Data in `h2fresh` | Type and expected supplier |
| --- | --- |
| `B`, `F : Finset ℕ → Λ` | Shared constructor's budget and the `rc-theta-coeff` lattice family, with `F_U = θ H_U` on its window. |
| `ops : GoodOperators T avoid frob ρ Λ`, `coeff : ℕ → Λ →ₗ[O] O`, `D : ∀ U, DeterminantFourierData ops m (F U)`, `hD : ∀ U, (D U).coeff = coeff` | Constructor types; `rc-theta-coeff` supplies the operators and Fourier data. Only `ops.trace_eq` and `(D U).hecke_eq` via `hD` are used from these structures. The diamond congruence hypothesis is not needed. |
| `hcont : ContinuousOperators ρ Λ`, `hcoeff : ∀ n, Continuous (coeff n)`, `hΛ : Λ.FG` | Constructor types; the continuous constituent representations and Fourier lattice comparisons of `rc-theta-coeff`. |
| `hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q`, `hunr : UnramifiedConstituents T avoid ρ` | Existing chosen Frobenius and the ambient constituent attachment, also used by `rc-theta-coeff`. They allow any Frobenius lift at a test prime to be compared with the chosen one. |
| `hm2 : (2 : O) ∈ m`, `hm : IsClosed (m : Set O)`, `integral_inclusion : Function.Injective (algebraMap O K)`, `[CharZero K]` | Shared coefficient valuation ring and field. The inclusion is the same type as `O12.FourierData.integral_inclusion`. The topology and lattice typeclasses are the constructor's usual ones. |
| `S : Finset ℕ`, `hlevel : T.m.primeFactors ∪ avoid ⊆ S` | Shared stationary support including the ambient Hecke exclusions. Use the actual stage's full coefficient support among the exclusions, including the moving prime and sieves (tex 9471–9483). |
| `a, η : ℕ → O`, `δ : ℤ`, `ap`, `Good`, `adm`, `WU, R, M`, `hR : 2 ≤ R`, `hstage` | Same source and phase as the readings. `hstage` is `OddStageSource O WU R M δ (stageReduction O M ∘ η) Good adm ap (stageReduction O M ∘ a)` with the compositions written pointwise. Existing Appendix G stage choice supplies the depth and precision; `rc-theta-coeff` supplies the comparison to the actual lifted source at that stage. |
| `hwindow` | Each constructor-eligible `U` with `F U ≠ 0` has `U.card ≤ WU` and all its members satisfy stage `Good`. Supplied by the `rc-theta-coeff` window and extension by zero. If the stage and constructor good predicates are identical and the whole constructor budget is used, take `WU = B - 1`. |
| `H : Finset ℕ → ℕ → O`, `theta_mod_two` | On the constructor's range and positive indices, `2 ∣ coeff n (F U) - H U n`. Same as `O12.ThetaData.theta_mod_two`, on the explicit `F, coeff`. The coefficient family and its comparison come from `rc-theta-coeff`; the O.12 readings only consume them. |
| `H_off_unary` | On nonzero forms in that range, for every duplicate-free list `J` representing `U` and every `n` with `oddPart n ⊈ U`, there is `b : O` with image `2^(-n_U-1) TL η J a n` in `K` and `2 ∣ H U n - b`. This is the `O12.ThetaData.H_off_unary` comparison restricted to the forms where the stage is used. The constructed `H_U` should satisfy equality there when both sides use the same exact lift of the source. |

## Known issues

- The two fresh test primes must avoid the prime factors of the Fourier index, as specified at tex 9712–9717. Avoiding only `S ∪ U` would allow a fresh prime already to divide `n), in which case it need not increase the squarefree weight and a Hecke term can survive. The proof makes the extra finite exclusion separately at each index, at the same stage.
- Chebotarev gives density for all Frobenius lifts; the selected lift at each prime alone need not be dense. The constituent unramifiedness comparison already in `TraceLimits` transfers the two Hecke identities to all test lifts.
- As noted by the O.12 proof, the common ambient Hecke and unramifiedness domain can be smaller than the fresh domain for an individual form. Two-trace vanishing only needs primes outside the fixed ambient excluded set and survives that additional finite avoidance. The stronger formwise comparison needed for the readings remains separate.
- No error was found in the checked arithmetic with those exclusions and the manuscript's full-two-torsion, matching-parity convention. No additional printed statement is used. Construction of the named theta data and use of the two readings remain separate.

## Manuscript check

- Tex 9450–9455, 10208–10213 — OK: fix the operator budget and `R ≥ 2` before the choice of a valid stage.
- Tex 9471–9489, 9491–9497 — OK: exclude the full coefficient support, use split-prime weight and `n_U = δ + |U|` in matching parity, and apply the operators to the actual source.
- Tex 9558–9561, 9570–9584, 9607–9617 and 10214–10233 — OK: `Odd.O9_odd_stage` pays for the normalized bound `min(R, ω(r))` at every index; `OddStageSource.precision` justifies lifting from precision `M` at the power required here.
- Tex 9618–9636 — OK: the unary correction is supported at exponents `(∏ J) * k^2`, and on their complement the division in (O.11) is by the integer two. The exact coefficient comparison is named, with its allowed precision error.
- Tex 9638–9648, 9672 — OK: theta multiplication is congruent to the identity modulo the ideal of the integer two; reduction of the model is coefficient by coefficient modulo `m`.
- Tex 9649–9654, 9660–9668 — OK: use the supplied lattice, continuity, Frobenius trace identification and good Hecke formula; the formula is applied to the entire lattice, including the first Hecke translate.
- Tex 9712–9717 — OK: use distinct test primes avoiding the index and level, applying the Hecke formula twice and choosing a new avoidance set at each index.
- Tex 9741–9743 — OK: under the exclusions at tex 9712–9717, the test primes give two distinct members of the squarefree kernel outside `U`, so the unary correction is absent.
- Tex 9744 — OK: the weight bound and precision are uniform over the fixed budget, and the cutoff `R ≥ 2` is enough for the needed divisibility even at indices of unbounded weight.
- Tex 9745 — gap filled: product density follows by excluding the first prime in the second open set; scalar multiplication gives joint continuity, and the preimage of the closed ideal contains the dense pairs.

## Verification

Both `Stage.lean` and `Main.lean` compile with `lake env lean -j1` on the pinned toolchain. The nine theorem-specific `#print axioms` commands, including those for the private helpers, each report `[propext, Classical.choice, Quot.sound]`. The main conclusion matches the constructor's binder verbatim apart from whitespace.

During dependency setup, replacement compiler commands overlapped with earlier commands that had not exited. This violated the one-process limit for the run. The overlapping jobs were stopped and the final checks used one sequential driver.
