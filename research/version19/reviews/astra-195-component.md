# Component review of the printed 195-coordinate construction

Reviewed 16 November 2026. This report checks the printed transformation and the coefficient-height formula. It does not accept the release or re-audit the inherited arithmetic theorem.

The inspected manuscript is `C:/Users/glaze/Documents/Codex/2026-11-02/lo/work/version19-250-draft-20261116/quartic_v19.tex`, SHA256 `388eb3e876cb3d3357bc7471fb2d9fdf6dd34e4a4130d1a89c266615004239eb`. All manuscript line numbers below refer to this file. It remains unchanged. The earlier eight exposition proposals remain unapplied.

## Result

No discrepancy or remaining mathematical gap was found in either requested component.

- All 175 printed quadratic rows match the pinned final source, with the same signs.
- All 64 entries of the printed matrix match; its determinant is exactly the printed nonzero rational number.
- All 186 nonzero Laurent weights and all 64 nonzero final parameter weights match. The input and retained unit have weight zero.
- The full chain passes exact checks: 182 initial balancing identities, 176 primitive-basis identities and 175 final Laurent identities. The deleted square row becomes an identity; the inverse guard remains literally `1 - x_77 x_78`.
- All 54 rational components in the three redundant-equation blocks match the displayed field relations up to nonzero rational row factors. The retained reference rows give the two printed contradictions on the putative S = T = 0 stratum.
- Independent expansion of the printed rows gives 2965 parameter-separated terms, 2956 coordinate monomials, degree four, and coefficient one on x_1^4. The exact height formula holds for every integer N >= 1.

The new checker `verify_printed195.py` uses only the Python standard library. It reads the mathematical TeX expressions themselves and ignores the `% V19-ROW` JSON comments. It imports or executes no code from Jose, Carbon, the assembler or the previous checkers. Data files are read as inert JSON and bound to the existing source manifest for commit `cd474ee67104586c9d71885a7c95e8a21f12ca0c`.

## Locations checked

| Manuscript lines | Assertion | Check |
|---|---|---|
| 146–188 | Three curve equations are redundant, including the exceptional reference stratum | Field identities, 54 physical row components, exact retained-row substitution |
| 189–209 | Parent source, balancing, row basis and two coordinate constants | Parent digest, 182 balancing identities, 176 basis identities, determinant |
| 211–245 | Affine change, guarded elimination and rational-solution correspondence | Exact affine substitutions, weight tables, row multipliers, deleted identity and retained guard |
| 247–268 | Support, height, degree and content | Expansion of printed rows, all profile sign and dominance tests |
| 924–960 | Printed 8 by 8 matrix | All entries, row order, coordinate scalings and determinant |
| 961–977 | Laurent powers and compaction | All 186 listed nonzero weights, three exceptional unit/power coordinates and all 195 index correspondences |
| 978–986 | Parameter balancing and reference to inert factors | All 64 listed nonzero weights and all recorded row shifts |
| 1122–2077 | Complete printed 195-coordinate table | Parsed 175 rows, compared each to source, independently expanded |
| 7761–7767 and 7830–7833 | Inherited allowed range | The 196-coordinate parent explicitly takes integer N >= 1 |

## Transformation proof

### Deleting the six components loses no equation

The field is Q(rho), rho^2 = 2, with D = 11 - 6rho. With F = f^2 and G = g^2, put U = h^2 - f + Df^3 and V = k^2 - g + Dg^3. The secant and tangent equations give

\[
 h^2-k^2=(f-g)s(h-k)=(f-g)\{1-D(f^2+fg+g^2)\},
\]

so U = V. Subtracting `(1-DF)` times the first primary ratio equation from h times the second gives kappa S U = 0. The alternate calculation gives lambda T V = 0. Since kappa and lambda are nonzero and S,T are not both zero, the field property gives U = V = 0. No f, g, h, k, S or T was divided out.

The checker reconstructs f,h,g,k,s from the literal parent coordinates for blocks 1, 3 and 4. The scales are 1, 2 and 4. The label pairs are `(x_29 + rho x_30, x_31 + rho x_32)`, `(x_37 + rho x_38, x_39 + rho x_40)` and `(x_41 - 1 + rho x_42, x_43 - 1 + rho x_44)` respectively. Each reciprocal-square field element uses twice the second physical square coordinate, as required by squaring a + rho b. This checks the actual coefficient conventions instead of inferring them from names.

For each block it compares the two square equations, the secant and tangent equations, four ratio equations and the removed curve equation, two rational components apiece. The resulting 54 nonzero rational component factors are recorded in `redundant-block-components.json`.

For S = T = 0, set x_17 = x_18 = x_151 = x_152 = 0 in the unchanged unbalanced reference rows. The first pair is an invertible linear system and forces

\[
 x_{15}=-15248/14161,\qquad x_{16}=-79808/127449.
\]

The retained square equations force x_64 = x_15^2 + 2x_16^2 and x_65 = x_15 x_16. Substitution in the third reference pair gives exactly

\[
 1399113877520/928557,\qquad866355785474/928557,
\]

both nonzero. These calculations use no removed curve row. This closes the exceptional-stratum premise before any deletion.

### Balancing, the matrix and coordinate maps

The parent table has the exact digest printed at lines 192 and 7828. Under A = 149C^2 and the source's coordinate powers of C, every one of its 182 rows becomes its balanced row after the recorded nonzero scalar and C-power normalization. Deleting the six named curve components gives exactly the pinned 176-row balanced table.

The printed matrix is applied to the two reference-square rows followed by the three reference pairs, in that order. Exact rational elimination gives

\[
 \det M=1/214450708242592116705963714180667354532074632082.
\]

The two coordinate substitutions are old x_76 = new x_76 / 3813373161796 and old x_90 = new x_90 / 3813373161796. Applying the matrix, these coordinate substitutions and each recorded primitive row multiplier reproduces all 176 primitive rows, with their source signs. The unaffected rows are included in this comparison.

The affine substitution at lines 214–216 agrees term for term with the source certificate. Its linear part is triangular with diagonal entries one. Direct expansion gives the two centered square equations and both simplified detector combinations at lines 219–225.

For the Laurent step, x_77 = w^-1, x_78 = w and x_79 = w^2 are the three special substitutions. Every other old coordinate is w^a_i y_j(i), using precisely the printed a_i. All old indices above 79 decrease by one. Substituting these maps into every centered primitive row, applying the recorded nonzero rational factor and w power, then setting y_j = C^k_j x_j and applying the recorded C-power shift, reproduces every printed final row on the unit relation. This is an equality in the Laurent polynomial ring, not a test at sample points.

There is one necessary distinction in this check. In the Laurent ring where x_77 = w^-1 and x_78 = w, the guard is identically zero. Consequently the checker separately verifies that the original guard and final printed guard are both exactly `1 - x_77 x_78`, with the same sign. The removed square equation becomes zero after x_79 = w^2, as required. Thus unit-ring equality cannot hide an omitted nonvanishing condition.

Every rational solution of the final table has w != 0 because of this literal guard. Since C = 149^N != 0, all C and w powers used in the maps are invertible. One can undo the parameter scaling, restore the unique removed coordinate w^2, undo the affine map and the two constant coordinate scalings, and use invertibility of M to recover the original rows. Conversely every original solution maps forward. The input is fixed throughout. Combined with the deletion proof above, this proves the claimed full rational-solution correspondence, including exceptional coordinate values.

## Height and support for all allowed parameters

Write each coefficient of the independently expanded printed quartic as

\[
 p_m(C)=a_{m,0}+a_{m,1}C+a_{m,2}C^2.
\]

The expansion contains exactly 2956 nonzero profiles and 2965 nonzero parameter-separated terms. It also agrees with the independently pinned `polynomial-family.json`; the latter was used only for comparison, not to generate the profiles. The complete profiles are recorded in `coefficient-profiles.json`.

For every profile, let epsilon be the sign of its highest nonzero coefficient. The checker expands epsilon p_m(149+t). Every coefficient is nonnegative and the constant coefficient is strictly positive, with minimum 1 across all profiles. Hence p_m(C) is nonzero and retains that sign for every real C >= 149. In particular none of the 2956 coordinate monomials disappears for an allowed N.

Put

\[
 K=126616122944180358034867798936.
\]

The coefficients of both x_74 x_75 x_77 and x_77 x_87 x_88 x_91 are exactly -K, independent of C. The coefficient of x_77^2 x_101^2 is exactly 22201C^2. These are explicit witnesses for both lower bounds in the claimed maximum.

For N = 1,2,3,4,5, evaluation of every coefficient profile at C = 149^N gives maximum absolute value K. These five evaluations exhaust the small integer-parameter range. The crossover is strict:

\[
 149^{12}=119738888098469732352733201
 < K
 <2658323054674126527963029795401=149^{14}.
\]

For the entire remaining range, the checker expands both

\[
 22201(149^6+t)^2+p_m(149^6+t),\qquad
 22201(149^6+t)^2-p_m(149^6+t)
\]

for each of the 2956 profiles. All coefficients in all 5912 expansions are nonnegative. Therefore |p_m(C)| <= 22201C^2 for every real C >= 149^6. The explicit positive profile 22201C^2 attains this bound. For every integer N >= 6, C = 149^N lies in that range and 22201C^2 = 149^(2N+2). Together with the five small cases and the witnesses above, this proves exactly

\[
 H\left(\sum_{i=1}^{175}q_i(149^N)^2\right)
 =\max\{K,149^{2N+2}\}\qquad(N\in\mathbb Z,\ N\ge1).
\]

The integer restriction is inherited explicitly from the parent at manuscript lines 7762 and 7832 and from the primitive-basis source. Five sample values would not by themselves control an interval of real N. This proof uses those values only for the five allowed small integers, and uses coefficient-wise inequalities for the unbounded remainder. The numerical crossover N = 6 concerns height; it does not give an effective defining threshold.

Only the printed input-square row contains x_1; it contains x_1^2 with coefficient one. Its square gives coefficient one on x_1^4, independently of N. No other row contributes to that monomial. All coefficients are integers after the allowed specialization. Thus degree four and integer content one follow for every allowed N.

## Source binding and reproducibility

All inert input files used are under `C:/Users/glaze/Documents/Codex/2026-11-02/lo/work/version19-draft-20261116/finite-verification/source/`. Each is checked against `finite-verification/download-manifest.json` at commit `cd474ee67104586c9d71885a7c95e8a21f12ca0c`. The complete paths, sizes and SHA256 digests are in `verification.json`.

The main source bindings are:

| Source | SHA256 |
|---|---|
| `quartic195_20261116_v45.tex` | `ced8683918d265d6fd4d3bb9157b1178013a6beab6a90f5c2f848076d05fa2c7` |
| `primitive_quadratic_bases_20261115_v40.tex` | `52d4afde0ecfb798a80d772d3b4029f309c544a91c812567c76f4891071f6f9a` |
| `quartic196_redundancy_20261115_v40.tex` | `475c3b28e24938f2aa59e3fa1ff517be21985947ad9ff8433d4317ab53eecf98` |
| `primitive_basis196_v40/transform.json` | `680f3e346dc168de563d82e60ed5b858b1100c7e44719e46eaf7c24966e022ac` |
| `primitive_basis196_v40/quadratic.json` | `381ea54e77505a8d9b452b2afab42bd052beb0fb4dbd0804f63f2f609efbb275` |
| `affine_laurent195_v45/transformation.json` | `5ac9fdcb6becd504d5e698373f52a5bddc99afe9c93614705b07efd3ff4f4e2f` |
| `affine_laurent195_v45/quadratic-family.json` | `304f94843c1a4ac94fcd5f1295fee8b532e7f0424e638314d892c556e2fbfdf9` |
| `affine_laurent195_v45/polynomial-family.json` | `99d3844d334a16502053bef55e4f6e0a4e3e08daa786737f22aa09c619069084` |

Run the new checker with Python 3 from any directory. It writes only its three evidence files under this `195-review` directory. It verifies the manuscript hash before and after checking. A mismatch, an unparsed printed term, a changed source digest, a failed row identity or a failed coefficient inequality aborts rather than producing a passing report.

## Scope limits

This component review does not re-prove the 196-coordinate parent's Diophantine equivalence, the Busy Beaver lower bound N_BB >= 54, or the strict Busy Beaver coefficient bound. It establishes the printed 195 transformation and exact coefficient formula that those inputs consume. It does not evaluate a Busy Beaver value, identify an effective defining threshold, check all 250-coordinate arithmetic arguments, or accept a release. It also does not check final public packaging or PDF layout. No manuscript, assembler, table, PDF, repository or relay file was edited, and no GitHub or provider call was made.
