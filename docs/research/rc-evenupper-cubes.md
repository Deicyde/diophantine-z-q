The realized-cube clause of `PreLeaves.even_upper` is proved on the exact data used by the auxiliary factor. For `A = symbolFamily P hS`, `T = evenTypes W.S hS.1` and `W' = withPartitionCertificate W hS A`, `rc11Inputs_of_sourceFamily` produces `EvenUpperRC11Inputs W'` from the genuine sources, their App F comparisons and (3.2) at `N₀ ℓ = CST.newformLevel (Ecurve ℓ)`. It takes no cube premise. `evenUpper33b_of_sourceFamily` applies the existing RC11 consumer with App E's scalar output; `fullUpper33b_of_sourceFamily` also proves the nonvanishing assertion in the displayed (3.3b).

There are two entry points. The compatibility entry point `rc11Inputs_of_genuineSources` consumes the existing `PreparedGenuineEvenSource` (`hG`) and the requested zero extension outside `PreparedType`. It supplies `hc` and uses `sourceUnit_type_prepared_of_zero_unprepared` for `hactive`. The entry point for the actual merged family instead proves (3.3a) directly from each `EvenSource` at its fixed depth. Its active type test is `HasReference`, which follows from a value-one observation because the no-reference branch is identically zero. The same test applies to the contracted value-one graph of a partition certificate. A bridge to `PreparedGenuineEvenSource` on prepared types alone would leave the wider domain of the installed predicate unhandled; the direct route needs no claim that every active reference type is prepared.

At the base `d`, the forest certificate gives a nonzero terminal polynomial. Use `one_symbol_address` and realize its new vertices by distinct primes congruent to 1 modulo `T.m * (8 * N₀ ℓ * ∏ p ∈ W.S, p)`, with the original prime representatives fixed. At each address the construction records `h x = d * Q x`, with `Q 0 = 1`, the original primes dividing `h x`, the same total type, and no primes in `W.S`. The factor `Q x` is a unit square at each prime of `2N₀`; the linear activations supply the square relation required by `BinaryFamily`. At a nonzero address, `symb_eq` reads the realized graph, then `symb_primeConfig` reads the graph on the prime factors of `|h x|`. This is the same source because the total type did not change. The construction itself does not use corank zero. The boolean scalar comparison downstream does.

## Statements

All declarations are in `ZInQ.Manuscript.RC.EvenUpperCubes`. In this table, the installed data and common type alphabet are `W'`, `T`, and `A` defined above. A positive level and support coverage mean `0 < N₀ ℓ` and `∀ p : ℕ, p.Prime → p ∣ N₀ ℓ → p ∈ W.S`.

| Declaration | Statement and role in the RC11 adapter |
| --- | --- |
| `fixedLevel_eq_newformLevel` | For a genuine newform of `Ecurve ℓ` of level `N`, `N₀ ℓ = N`. Supplies the level identification for `hl` and `hc`. |
| `curveLevel_and_support` | `SupportSpec W`, positivity of `ℓ`, `ModularNewform` and `HasseConvergence` give `CurveLevel ℓ` and level support coverage. Supplies `hl` and makes every stationary prime coprime to the level for `hc`. |
| `realized_cubes_with_total` | For type data, one coefficient reading with fixed-set factorization and coefficient rules, residue-one type zero, a prime support set, and a negative squarefree support-avoiding base with a partition certificate and good prime factors coprime to the level: every dimension `b ≥ 1` occurs. The cube is based at `d`, factors as `d * Q x` with the displayed congruence, preserves old prime divisibility and total type, and has negative, support-avoiding, value-one addresses away from zero. Arithmetic construction for `hc`. |
| `partitionCertificate_iff` | At every signed parameter, the installed certificate on any table is equivalent to `SourcePartitionable W T A` on the same table. Supplies `hp` at `W'`, by associating the conjunctions. |
| `evenTypes_typ_one` | Residue one modulo the support modulus has type zero in the concrete squareclass alphabet. Supplies the residue class condition for `hc`. |
| `sourceCubesAt_of_reading` | At a partitionable base of `W'`, if the symbol of its total type is the specified coefficient reading with fixed-set factorization and coefficient rules, then positive level and level support give a cube of dimension at least any requested dimension, with old primes, equal total types and `SourceUnit W' T A` at every nonzero address. Local construction of `hc`. |
| `sourceCubeInputs_of_genuineSources` | `hG`, zero extension outside `PreparedType`, coefficient rules on prepared types, positive level and level support give `SourceCubeInputs W' T A`. Supplies exactly `hc` to `rc11Inputs_of_preparedGenuineSources`. |
| `rc11Inputs_of_genuineSources` | The same genuine prepared-source, zero-extension and coefficient-rule inputs, with the existing modularity and convergence inputs and (3.2) at `N₀ ℓ), give `EvenUpperRC11Inputs W'`. Derives `hactive`, `hl`, `hp`, and `hc` in the existing adapter. |
| `sourceRules_of_realizations` | The existing `BudgetRealization` for each reference source and each budget gives `SourceRules hS P`: the fixed-set comparison and all three graph rules on that very reading. Supplies the App F inputs used in `hc` and (3.3a). |
| `sourceCubeInputs_of_sourceFamily` | `SourceRules hS P`, positive level, and level support give `SourceCubeInputs W' T A` on the entire installed partition predicate. This supplies `hc` without the prepared-only zero extension. |
| `units33a_of_sourceFamily` | Central-value agreement and `SourceRules hS P` give a single `C₀` for `Units33a W' (SourceUnit W' T A) C₀`. This supplies (3.3a) directly, instead of the prepared-only `hactive` route. |
| `sourceConsequences_of_sourceFamily` | Central-value agreement, `SourceRules hS P`, positive `ℓ`, `ModularNewform`, `HasseConvergence` and (3.2) at `N₀ ℓ` give `SourceConsequenceInputs W' T A`, including level, normalization, exact partitionability, (3.2), (3.3a) and cubes. |
| `rc11Inputs_of_sourceFamily` | The same premises produce `EvenUpperRC11Inputs W'`, with the witnesses `SourceUnit W' T A` and `N₀ ℓ`. |
| `evenUpper33b_of_sourceFamily` | On the same data and same source, with `AppEOutputs` for (3.2) and the existing `Prints`, the old RC11 consumer gives `∃ C₁, EvenUpper33b W' C₁`. |
| `fullUpper33b_of_sourceFamily` | With the same source, analytic inputs and `AppEOutputs`, and the existing `KolyvaginThm1Printed` for the forward corank-zero implication, the full comparison gives `∃ C₁, Upper33b W' C₁`, including nonvanishing. |

## Remaining hypotheses

| Input | Owner and scope |
| --- | --- |
| `SupportSpec W` and `0 < ℓ` | Original data. The support consists of primes and contains 2, 3 and all primes of `ℓ`. The base containment is the one in `PreDataSpec.support_base`. This is a hypothesis about the original data, with no assertion about the upper estimate. |
| `ModularNewform`, `HasseConvergence` | Existing analytic print and convergence glue. They identify the level of the functional equation; the newform is already in the modularity print. No separate level-support or conductor-equality hypothesis remains. The proof uses the least-level divisibility theorem and the existing prime-square comparison from GlueSweep, without formalizing all conductor exponents. |
| `P : SourceFamily W C`, `C.Lstar = W.Lstar` | App E genuine source and original central normalization. Each source provides its own form, negative reference, phase-removed coefficients and attained minimum on its fixed filter. These data contain no prime graph comparison or nonzero-address cube. The alternative compatibility theorem takes the existing `PreparedGenuineEvenSource` instead for the prepared types, with its separately requested zero extension, Waldspurger Corollary 2, ellipticity, twist continuation and (E.9). |
| `SourceRules hS P` | App F coefficient rules and fixed-set factorization on the exact reading. This is the comparison for individual finite graphs and testing prime sets; it asserts neither a graph extension nor any scalar bound. The same `BudgetRealization` input as the auxiliary-factor assembly supplies it. The prepared-only adapter needs just the graph rules on prepared types alongside the fixed-set factorization already in `hG`. |
| `EvenScalar32 (Ecurve ℓ) (N₀ ℓ) C`, or `Even.AppEOutputs (Ecurve ℓ) (N₀ ℓ) C` for the output theorem | App E / (3.2). Supplies the common cleared scalar and corank-zero central comparisons; neither a unit estimate nor cubes are built into this premise. The existing App E implication is reused. |
| Existing `Prints` (legacy numerical consumer), or `KolyvaginThm1Printed` (full displayed result) | Shared analytic layer, downstream of the RC11 input. Used by the existing corank calculation at unit addresses, with BCDT and the original central normalization. No new print is introduced. |

These are smaller proof obligations than the leaf: source construction, local coefficient comparisons, and (3.2) do not assert even the cube clause individually. Together they supply the full leaf by proof, including (3.3a) and realized cubes. This is a reduction of mathematical obligations, not a converse implication from the legacy existential leaf to its new hypotheses. The legacy leaf could choose level zero and an arbitrary unit predicate; the proof now supplies a positive level of the genuine functional equation and binds the predicate to the actual normalized coefficients.

## Known issues

- Tex 2360–2361 and 10131–10132 ask for nonempty units at every total type, including negative filters of root number minus one. There is no nonzero reference in such a filter. This is the previously recorded manuscript error in `docs/research/rc-aux-inputs.md`.
- The prepared type for the rough companion requires signed residue 1 modulo 8 (tex 10096–10098). The merged `symbolFamily` is zero at types without a negative reference, not at every type outside that residue branch. The installed partition predicate is genuinely broader; the direct theorem keeps it, while the compatibility theorem explicitly states its extra zero-extension premise.
- `TypeData.classes` abstractly supplies some reduced class realizing each type; that field alone does not identify the class of residue one. The concrete `evenTypes` uses the squareclass quotient, so the type of that residue is zero.
- `EvenUpper33b` in the old wiring is the inequality. The manuscript also states nonvanishing; `Upper33b` and the full output theorem retain it.
- The level-zero reading of the legacy leaf noted in `RC/Wiring/EvenUpper3.lean` is excluded by `level_pos_of_bcdt`. A general strengthened CRT prescription would fail if a level prime were an old prime and an independent Legendre bit there had to be nontrivial. Here support coverage and base avoidance establish the necessary disjointness.

## Manuscript check

- Tex 1779–1784, 1974–1975 — gap filled: identify the least matching cusp form level with the newform's level and prove its prime support using the existing modularity and local coefficient comparisons.
- Tex 1832–1843, 1864–1873, 1941–1949 — unverified: the App E scalar construction remains an input; the family here satisfies the stated sign and local squareclass requirements.
- Tex 2015–2028, 2031–2046 — OK: the existing squareclass type keeps the full class at two and the relations between coordinates; type-zero additions preserve the sum.
- Tex 2068–2089, 7793–7810, 10079–10094 — OK: value one is the least-depth test on the fixed filter and the same square identity gives the unit valuation and nonvanishing.
- Tex 2102–2149, 9884–9976 — unverified: the same-source App F realizations remain inputs; the existing comparison/theta consumers give their graph consequences.
- Tex 2151–2174 — gap filled: for the stronger arithmetic progression used in a level-preserving cube, prove coprimality of the old primes to its modulus before applying CRT and Dirichlet.
- Tex 2176–2185, 2295–2316 — OK: installed forest certificates give nonzero terminal polynomials; the empty-graph unit case is handled by the direct coefficient estimate.
- Tex 2222–2238, 2318–2322, 10107–10110 — gap filled: pass from the stationary abstract extension to the signed parameters, keep every old prime, check the binary relations and read the same source at every nonzero address.
- Tex 2323–2341, 10111–10129 — OK: the existing Boolean comparison and valuation transfer consume the realized cubes. At a unit address the central comparison uses the existing forward corank-zero implication.
- Tex 10096–10105 — OK: the residue 7 condition is stated for the negative rough companion, not imposed on every even source.
- Tex 2360–2361, 10131–10132 — error: literal preparation at every total type includes the vanishing filters described above.

The on-the-spot steps (provenance (c)) are the Lean predicate reassociation and active-type check, grouping finitely many source constants, and the explicit products, casts, and prime-factor identities that retain the support and total type in the CRT construction. The congruence with the full support product is a sufficient choice of progression for the manuscript's local requirements. The level proof combines the existing newform and local (a_{p^2}) results; no new literature claim or printed-form leaf is needed.

## Verification

Each of the three Lean modules compiled individually with `lake env lean -j1`. The separate `scratch/rc-evenupper-cubes/Axioms.lean` check reports exactly `propext`, `Classical.choice` and `Quot.sound` for each of the 15 theorems listed above. The per-theorem results are recorded in `scratch/rc-evenupper-cubes/log.md`.
