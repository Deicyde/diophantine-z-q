# Genuine theta coefficients for the trace model

For one actual stage and a fixed finite pool of good primes, the lifted theta expansions supply the integral coefficient family, the good Hecke and diamond operators, and the determinant Fourier data for `buildConstituentModel`. The weight-two realization at tex 9647–9654 is an ELLIOT (uncited) input. The call to the existing constructor checks, but its stationary-support hypothesis forces the pool to be empty. The scoped stop for a nonempty pool is the formwise inertia and constructor change described below.

All six files under `ZInQKernel/Contrib/OneProof/RC/ThetaCoeff/` compile individually with `lake env lean`. The 72 declaration audits report only `propext`, `Classical.choice`, and `Quot.sound`.

## Known issues

- Tex 9660–9668: integrality of a good Hecke image does not by itself show that it lies in the module spanned by diamond translates. Close the generating set under both good Hecke and diamond operators, then use the finite Fourier-coordinate injection to establish finiteness for that module.
- Tex 9649 specifies a finite constituent space for fixed stage and set. The bounded cardinality of the sets does not give a finite union of level primes across all such sets. The finite pool in this lane gives a local family for a fixed set and its subsets (or any fixed finite collection of sets); it does not produce a simultaneous finite constituent space for every bounded good set.
- Existing constructor mismatch (tex 9745–9750): `buildConstituentModel` uses one `avoid` for both the good-operator tests and stationary Kummer support. The common-level good tests must omit the added level primes, but the text detects radicals at those primes using the added bits, separately from the stationary type. In `no_good_mem_stationary` the independent-bit Frobenius theorem shows that a good prime cannot belong to a support detected by the stationary type. With every pool prime dividing the common level, this forces the pool to be empty if the existing constructor’s coverage hypotheses hold. The minimal repair is a local inertia statement: for `W ⊆ U`, inertia away from `S_stationary ∪ U` fixes the trace orbit of `F_W`. This is enough to feed the existing supported-character classification, while the good-operator test set may still omit the whole pool. The required equality is `redTrace (g * σ) W = redTrace g W` for every `g` and such inertia element `σ`. It suffices that the constituent coordinates occurring in `F_W` be unramified at the prime in question. The analytic identification of those coordinates with their formwise levels is still needed.

## Statements and constructor arguments

All statements use integer division, and the residual conclusions are coefficientwise. The Fourier coordinate at zero for the constituent space is a dummy zero; no assertion about Eisenstein constant terms is used.

| Declaration | Statement and use |
| --- | --- |
| `Lift.H_reduce`, `Lift.aθ_reduce` | The weighted geometric norm sums, and their extraction at `m*n`, reduce to `S.H` and `S.aθ`. These tie the eventual `F` to the Brandt stage. |
| `raw_dvd`, `B_spec` | The ordered product of the manuscript's operators is divisible by `2^max(0,n_U)`; `2^max(0,n_U) B_U[n] = 2^max(0,-n_U) raw_U[n]`. This constructs the `B_U` block for `F`. |
| `mem_subscripts`, `Lift.unary_off` | The subscripts are exactly the squarefree numbers with prime factors in `U`; `Θ_j[n]=0` if no `k` has `n=j k²`. Supplies positive subscripts and the support part of `D`. |
| `Hnum_dvd`, `HU_spec` | For every index the unary-subtracted numerator is divisible by integer two and equals `2 H_U[n]`. Multiplication by ordinary theta defines `FourierF`. |
| `GoodRec.degeneracy` | The scalar recursion commutes with the coefficient dilation at every `d>0` coprime to the test prime. Used for `D.hecke_eq`. |
| `eisenstein_pow`, `eisenstein_at_prime`, `eisenstein_rec` | The divisor sum at `q^t` is `∑_{i=0}^t α(q)^(t-i)(q β(q))^i`; at `q` it is `α(q)+qβ(q)`; the full recursion has diamond scalar `α(q)β(q)`. Used for `D.hecke_eq` and the Eisenstein trace. |
| `EigenSource.zero`, `EigenSource.goodRec` | The dummy zero coefficient is zero and the scalar recursion holds on each normalized underlying source; used in `coefK` and `D.hecke_eq`. |
| `Basis.eval_zero`, `Basis.coefK_injective`, `diagonalOp_apply` | The evaluation at the dummy index is zero, positive expansion is injective, and the scalar linear map acts coordinate by coordinate. Used in `coefK` and `ops`. |
| `Basis.diamond_mul`, `Basis.commute`, `Basis.hecke_eval` | Diamond actions compose, commute with good Hecke, and the constituent sum has the good Fourier formula. Used for `ops` and `D.hecke_eq`. |
| `Basis.mem_seed`, `Basis.diamond_mem`, `Basis.hecke_mem`, `Basis.integral` | The span contains each seed, is stable under both kinds of translate, and has integral coefficients once every seed's diamond translates do. Supplies `Λ` and the operator domains. |
| `Basis.coeff_spec`, `Basis.hspec`, `Basis.heckeFourier` | The restriction maps into `O`, agrees after inclusion with characteristic-zero evaluation (in particular at positive indices), and satisfies `HeckeFourier` over `O`. Supplies `coeff`, `hspec`, and `D.hecke_eq`. |
| `Basis.finite`, `Basis.hcoeff` | A finite set of Fourier rows detects the constituent space and hence the integral lattice is finite over `O`; each coefficient is continuous in the induced topology. Supplies `hΛ` and `hcoeff`. |
| `Blocks.vector_eval`, `Blocks.coeff_F`, `Blocks.hzero` | The seed realizes `θH_U` on the finite pool with the same integral coefficients, and is zero on non-good sets. Supplies `F` and `hzero`. |
| `Blocks.c_spec`, `Blocks.diamond_vector`, `Blocks.diamond_eval`, `Blocks.integral_seed` | Twice the correction scalar equals `B_U[j](ψ_U(u)-χ_j(u))`; the diamond translate is `ψ_U(u) F_U + ∑ c_j θΘ_j`. Its coefficients are the images of the displayed integral expression. Supplies the integral seed proof for `coeff`. |
| `Attachment.good`, `Blocks.ops`, `Blocks.hcont` | Good Frobenius trace and determinant are `a_q` and `qχ(q)`; their lattice actions match the Hecke and scaled diamond actions. Continuity comes from matrix entries and unramifiedness from the attachment. Supplies `ρ`, `ops`, `hcont`, `hunr`. |
| `Blocks.determinant`, `Blocks.hD` | Modulo `m`, the determinant discrepancy has expansion `∑ r c_j θΘ_j`; off a unary subscript the reduced coefficient of `θΘ_j` vanishes. All sets use the same coefficients. Supplies `D`, `hD`. |
| `no_good_mem_stationary`, `Blocks.pool_empty_of_stationary_cover` | A good added prime has an independent bit, so cannot be detected by the stationary type. The existing `hlevel` therefore forces the pool to be empty. |
| `Blocks.test_ne_two` | A test prime cannot be two because the common level is a multiple of four. Used for `D.correction`. |
| `Blocks.trace_mul_of_seed_unramified`, `Blocks.inertia_le_consN_of_seed` | If inertia acts trivially on the nonzero constituent coordinates of the relevant forms, it fixes their trace orbits and belongs to the active constituent subgroup. This is the local interface for repairing the existing constructor’s stationary-support argument. |
| `Blocks.build` | Conditional adapter to `buildConstituentModel`, taking `hdiam`, `read`, and `h2fresh`, along with the constructor's stationary-support hypotheses. |

Proof helpers (on-the-spot, provenance (c), for the steps not in the manuscript):

| Declaration | Statement and use |
| --- | --- |
| `lift_dvd`, `TL_reduce`, `TL_support`, `exponent_le` | Lift divisibility by `2^k` modulo `2^M` for `k ≤ M`; reduction commutes with the ordered operator product; vanishing on multiples of a sieved prime is preserved by the product at other primes; `max(0,n_U+1) ≤ M`. Used for `F`. |
| `raw_off`, `unaryWeight_odd`, `raw_shell`, `unary_shell` | If the odd-support set of the index is not a subset of `U`, the raw coefficient has one extra factor of two. The unary weight is odd for odd positive arguments. On a good unary shell the difference of the raw coefficients at `j k²` and `j` weighted by `η(k)χ₋₄(k)^i k` is divisible by `2^max(0,n_U+1)`; the unary coefficient at `j k²` equals that same weight. Used for `F`. |
| `mul_divide`, `B_bad`, `div_two_of_raw`, `B_off`, `sum_unary_off` | Multiplying the chosen quotient by its divisor recovers the numerator; `B_U` vanishes at indices divisible by a sieved prime; a raw coefficient difference divisible by `2^max(0,n_U+1)` gives a `B_U` difference divisible by two; off unary support `B_U` is even and the unary sum vanishes. Used for `F`. |
| `eisenstein_mult`, `hpoly_succ`, `hpoly_rec` | The divisor sum is multiplicative. For the homogeneous sum `h_t(x,y)` of degree `t`, `h_(t+1)=x^(t+1)+y h_t` and `(x+y)h_(t+1)=h_(t+2)+xy h_t`. Used for `D.hecke_eq`. |
| `Window.admissible`, `intUnit_sign`, `DiamondCharacters.sign` | A subset inherits the pool's budget and stage goodness; an integer unit maps to either sign; the unary character equals the block character or its negative at each diamond. Used for `F` and integrality of `coeff`. |
| `twoPower_reduce`, `DiamondCharacters.ψ_reduce`, `DiamondCharacters.det_scalar` | A two-power root of unity, the block character, and the block character multiplied by an odd prime all have residue one modulo `m`. Used for `D.correction`. |
| `coeff_timesTheta`, `eval_smul_O`, `diamond_smul_O` | After multiplying by ordinary theta, twice the form equals the original block minus its unary sum; coefficient evaluation and the diamond action preserve scalar multiplication by `O`. Used for `coeff` and `D.correction`. |

## Stated inputs and provenance

| Input | Tex | Kind |
| --- | --- | --- |
| `Lift`: geometric stage, class correspondence and masses, lifts of the weights and `P_M`, finite norm sums and phase; unary parity | 8476–8621, 9083–9089, 9618–9625 | Definition/data of the stage. The identification with the finite-precision stage and actual local weights is supplied. |
| `Divisions`: recurrence and support of the finite-precision source, depth valid for the budget, zero and exact sieve for the lift | 9077–9098, 9471–9483, 9578–9584, 10208–10233 | ELLIOT and existing App F/G inputs. The recurrence is provided by `AppF.ThetaStage.oddStageSource` with its stated source hypotheses. |
| `Window`, `DiamondCharacters` and coefficient field/ring/topology | 8422–8424, 9497–9555, 9618–9625, 9638–9655, 9696–9698 | Definitions and data of the construction. The common level is for the specified finite pool. |
| `Basis`, cusp recursion in `EigenSource`, and `Blocks` | 9548–9555, 9620–9625, 9647–9654, 9662–9664, 9754–9771 | ELLIOT (uncited). The membership input is the membership of the actual blocks, with the computed coefficients and characters, in the chosen characteristic-zero constituent basis. |
| Cuspidal attachment in `Attachment` | 9773–9797 | PRINT as cited: Carayol, §§0.3–0.7, Théorème A, pp. 409–411 (manuscript locator, print not independently checked; no new leaf). Uses arithmetic Frobenius with the two duals of the manuscript. |
| Eisenstein attachment in `Attachment` | 9653–9654, 9762–9767 | ELLIOT (uncited). Continuous unramified characters with good Frobenius values `α(q)` and `qβ(q)` are supplied as the diagonal summands. |
| `hfrob`, `hchi`, `htyp`, stationary radical coverage, `hdiam`, `read`, `h2fresh` | 9663–9668, 9688–9695, 9741–9750, 9905–9953 | Inherited constructor or sibling hypotheses, with the stationary support issue above. |
| Unramifiedness of the nonzero coordinates of the active subforms in `Blocks.inertia_le_consN_of_seed` | 9497–9555, 9745–9757 | The formwise level input for the suggested repair (ELLIOT, uncited level calculation). The lemma needs it only at the inertia prime in question. |

The uncited product/constituent assertion has no citation at 9647–9654 or in 8496–8620. The theta-source proof does invoke Weil later (from 8626, including 8953); those references concern the transformation of the Schwartz theta source, not the weight-two constituent decomposition. The unary Poisson statement at 9623 has no locator. The minimal missing analytic interface is `Basis` plus `Blocks` for the explicitly constructed series at the common level. Constructing it from first principles would require characteristic-zero half-integral weight theta and level theory, weight-two newform/oldform and Eisenstein theory, and passage to the finite complete coefficient field.

## Manuscript check

- 8476–8494, 8598–8621 — OK: use the lifted `P_M`, weights, and integer mass factors.
- 9077–9098 — OK: use the Brandt recurrence only at its stated precision, and retain the exact coprimality sieve.
- 9447–9455, 9491–9496 — OK: use the actual stage at a fixed budget and the ordinary integer operator product.
- 9497–9555 — unverified: the half-integral weight level and character calculations enter as block data.
- 9558–9617 — gap filled: use the existing (O.9) and shell results and lift divisibility out of the precision quotient.
- 9618–9625 — unverified: the unary character and modularity are input; its positive squareclass support is checked from its coefficients.
- 9626–9636 — gap filled: the shell congruence, off-shell bound, and exact sieve give integer division at every index.
- 9638–9646 — OK: coefficientwise reduction suffices; no saturation is used.
- 9647–9654 — unverified: multiplication by ordinary theta is computed coefficientwise; modularity and constituent membership are ELLIOT inputs.
- 9655–9660 — OK: the integral sign correction follows from the integral quadratic ratio.
- 9660–9662 — gap filled: pass the newform recursion through degeneracy and sum over the constituents; prove the Eisenstein recursion from its divisor sum.
- 9663–9668 — gap filled: span the good Hecke and diamond translates, prove integral finite coordinate detection and coefficient continuity, and use the existing limit argument.
- 9705–9729 — OK: reduce the undivided theta corrections and the scalar multiple of `F_U`, then use the existing fresh-trace determinant argument.
- 9745–9750 — OK: the support is stationary support union the active set. The current global constructor's stronger stationary coverage hypothesis cannot generally be satisfied by the common good-test avoidance set.
- 9754–9771 — unverified: the analytic assignment of constituents and old multiplicities is input.
- 9773–9797 — unverified against the print: use the good characteristic polynomial with the manuscript's normalization.
