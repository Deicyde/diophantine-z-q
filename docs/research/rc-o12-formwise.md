For the actual theta seeds on a finite window, the formwise comparisons reduce to intrinsic level bounds, the existing cuspidal good attachment at those levels, and the identification of each Eisenstein constituent with its normalized Dirichlet pair. From these inputs, `seed_unramified` supplies `hseed`, `seed_fourier` supplies `hexcl`, and `window_good_hecke` gives the `good_hecke` field. The Fourier proof constructs the local diamond translate in the **same** integral lattice as the ambient tests, by dividing the determinant action by the unit `q`.

The scoped stop is the modular realization input: the existing `Blocks` only records a common level, and `Attachment` and the cuspidal source recursion only give comparisons in the ambient test domain. They do not determine lower levels for the same coordinates, or certify the old-level specialization of the cuspidal attachment and recursion. The new structures record precisely those missing comparisons. There is no new printed leaf. The finite window still has a zero extension outside its pool; the result does not establish compatible realizations there.

## Statements

In the table, `N₀` is the old level, `N_i` the level of coordinate `i` including its dilation, and `a_i, χ_i` the underlying cuspidal or Eisenstein source data. The seed is `Blocks.seed U`, the vector underlying `Blocks.F U`.

| Declaration | Statement and use |
| --- | --- |
| `seed_level_dvd` | If coordinate `i` of the seed at `U` is nonzero, then `N_i ∣ N₀ · ∏ U`. Uses the bounds on `θB_U` and individual `θΘ_J` before dividing by two. Supplies the support calculation for **hseed** and **hexcl**. |
| `seed_level_coprime` | On a nonzero coordinate, a good `q ∉ U` is prime to `N_i`. Supplies the level guard for **hseed** and **hexcl**. |
| `EisensteinCharacters.frob_values` | At arithmetic Frobenius for an odd prime `q` prime to the level, the two Eisenstein characters have values `α(q)` and `qβ(q)`. Supplies the good trace and determinant for **hexcl**. |
| `EisensteinCharacters.inertia_values` | At such a prime both Eisenstein characters have value one on inertia. Supplies the Eisenstein part of **hseed**. |
| `good_values` | At good arithmetic Frobenius prime to `N_i`, the same attachment has trace `a_i(q)` and determinant `qχ_i(q)`. Uses ambient data off `avoid`, the same Carayol comparison for the cuspidal source at the excluded primes, and the divisor sum and character calculation for Eisenstein. Supplies **hexcl**. |
| `seed_good_polynomial` | For a nonzero coordinate of the seed at `U` and good `q ∉ U`, the characteristic polynomial of arithmetic Frobenius is `X² − a_i(q)X + qχ_i(q)`. This is the polynomial comparison underlying **hexcl**. |
| `seed_unramified` | If `V ⊆ U` and `q ∉ U` is good, inertia at any prime over `q` acts trivially on each coordinate occurring in the seed at `V`. This supplies **hseed**, in particular with the additional guard `q ∉ support` of the constructor. |
| `seed_good_recursion` | At a good `q ∉ U`, the scalar recursion `GoodRec` with `a_i(q), χ_i(q)` holds on the dilated coefficients of each occurring coordinate. Supplies **hexcl**. |
| `seed_fourier_over_field` | For the seed, coefficient `n` of the arithmetic Frobenius trace equals coefficient `qn` of the seed plus, if `q ∣ n`, coefficient `n/q` of the determinant translate. This is **hexcl** over the coefficient field. |
| `odd_unit` | An odd natural number maps to a unit in a local coefficient ring whose maximal ideal contains two. Supplies the integral diamond witness for **hexcl**. |
| `seed_fourier` | For a good `q ∉ U`, there is a vector `diamondF` in the seed lattice with `q • diamondF = d(Fr_q) F_U` and coordinate `χ_i(q) F_U(i)`. For every index `n`, the integral trace coefficient equals `F_U[qn] + q·diamondF[n/q]`, with the second term zero if `q ∤ n`. This supplies **hexcl** at each excluded good prime. |
| `windowModelOfLevels`, `window_good_hecke` | The first builds the existing window model with **hseed** supplied. The second applies `formwiseHecke_of_ambient` with `seed_fourier` in the excluded case, giving **good_hecke** for that model's Fourier data. |

The private Eisenstein helpers `weight_mod`, `odd_coprime_pow_two`, `twist_frob` and `twist_inertia` give, respectively, the finite reductions of the weight twist, coprimality with powers of two, and the values `q` at arithmetic Frobenius and `1` on inertia. These and the finite sum, coordinate support and unit arguments are on-the-spot (c).

## Remaining hypotheses

| Input | TeX and owner |
| --- | --- |
| `BlockLevels.oldLevel`, `old_good`, `level`, `degree_dvd`, `b_level`, `unary_level` | 9471–9483, 9497–9555, 9620–9625, 9670–9674, 9754–9760. **ELLIOT** in the same block realization: an old level prime to the stage's good primes, with the level of each dilated constituent dividing `N₀ · ∏ U` on `θB_U` and `N₀ · J` on the unary block. This is the missing level information, including the fixed and moving sieves. Deriving it from the Fourier series alone needs the half-integral weight level calculation, the theta product, and decomposition into a basis respecting degeneracies (large theory absent here). No conductor equality or ramification-at-added-prime assertion is needed. |
| `AtLevel.cusp_unramified`, `cusp_polynomial` | 9745–9750, 9762–9769, 9773–9797. **Existing print and ELLIOT application comparison**: at good excluded primes prime to the coordinate's level, apply the existing good Carayol attachment to the same underlying cuspidal source and the same representation. The remaining specialization is that the attachment of the common realization is that intrinsic attachment. The current data only give this at ambient tests. No statement about ramified representations is used. |
| `AtLevel.cusp_recursion` | 9660–9662, 9762–9767. **ELLIOT**: the normalized source has the usual eigenform Fourier recurrence at those same good excluded primes. This is the pre-degeneracy recurrence on the original coefficient and character functions. The extension of the recursion to old copies is proved. An unconditional construction would require a characteristic-zero weight-two Hecke interface for the realized newform (substantial missing theory). |
| `AtLevel.eis_pair` and its `EisensteinCharacters` data | 9652–9654, 9762–9767. **ELLIOT**: identify the same Eisenstein representation with the diagonal pair of the two underlying Dirichlet characters, with the coefficient image of the 2-adic cyclotomic twist on the second. The moduli divide the coordinate level and the zero extensions agree with the original source functions `α, β`. This is a realization comparison only; inertia and Frobenius values are proved. |
| Existing stage, common realization, coefficient ring and Frobenius choices | 8476–8621, 9077–9098, 9447–9455, 9618–9668, 9773–9797. **Inherited inputs**: `Lift` and `Divisions` for the actual stage (weights from `rc-pm`); `Window`, `Basis`, `DiamondCharacters`, `Blocks` and `Attachment` for the same forms and representations; arithmetic `hfrob`; the coefficient field, local integral ring, residue maximal ideal containing two, and embedding and topology used by the constructor. The Fourier lemma only uses the inclusion, local ring and maximal ideal, and trace/determinant lattice stability; the window supplies stability by the existing ambient argument. |
| Type and two fresh traces for the window constructor | 9663–9668, 9741–9750, 9932–9944. **Inherited inputs**: `R₀` and budget, open type kernel and `IsTypeChar`, stationary radical coverage and inclusion of the type modulus primes and two in the stationary support, plus `h2fresh` on the same coefficient lattice (sibling `rc-two-fresh`). No condition puts `avoid` inside stationary support. |
| Compatible full tested domain and remaining (O.12) inputs | 9649–9654, 9670–9704, 9754–9892, 9919–9926. **Sibling lanes**: `rc-o12-realize` for compatibility across tested sets; `rc-o12-stage-val` for the valuation and phase comparison; the local lanes for the ramified blocks and the bad-prime coefficient comparison. These are needed downstream for the original global `Inputs`, not to prove the formwise comparisons. |

## Known issues

- No manuscript error was established in the steps checked. The common-level interface lacks the lower-level data used by the manuscript; assuming the ambient Hecke test domain contains every formwise good prime would be an interface error.
- The zero index of `Basis.eval` is the existing dummy zero. The Fourier comparison asserts no Eisenstein constant term.
- The Carayol locator is taken from tex 9778; the print and locator were not independently checked (UNVERIFIED). The same trace and determinant normalization as the existing `Attachment` is used.
- The finite pool cannot cover all budgeted good sets. Algebraic validity for the zero extension does not identify it with any actual form.

## Manuscript check

- 9471–9483, 9670–9674 — unverified: the fixed and moving level primes are avoided by the modeled good domain via `old_good`.
- 9497–9555, 9620–9625 — unverified: the intrinsic theta level and unary degeneracy bounds enter as `BlockLevels`.
- 9629–9634, 9647–9654 — gap filled: the coordinate support of the divided combination lies in the union of the block supports; retaining the analytic realization itself is an input.
- 9652–9654, 9762–9767 — gap filled: the normalized character pair gives the two good Frobenius values and trivial inertia by the cyclotomic calculation.
- 9660–9662 — gap filled: the good recursion on each active dilated coordinate sums to the Fourier formula even at a prime outside the ambient test domain.
- 9663–9668, 9719–9721 — gap filled: determinant stability and the odd unit `q` place the local diamond translate of the seed in the original integral lattice.
- 9745–9750 — gap filled: check trivial inertia on the active coordinates of each subset seed; the existing Kummer argument consumes this comparison.
- 9754–9760, 9921–9923 — gap filled: the active-coordinate level bounds retain the dilation and omit `q` for each subset seed not using `q`; the local classification at a prime in the set is outside this proof.
- 9767–9769 — OK: the operators here act on the given common basis and same attachments; no independent decomposition or descent of those operators is required.
- 9773–9797 — unverified against the print: the already-used cuspidal good polynomial is applied with the manuscript's arithmetic Frobenius normalization, conditional on the same attachment comparison at the intrinsic level.

All five new Lean files compile with `lake env lean`. The 16 theorem audits and the window constructor audit print only `propext`, `Classical.choice`, and `Quot.sound`.
