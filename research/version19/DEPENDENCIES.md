# Version 19 source and consumer map

The new material is Part I of `manuscripts/quartic_v19.tex`. The complete
Version 18 argument follows it. TeX labels below locate statements independently
of page changes during typesetting. The release manifest binds the final source
and PDF. This map describes the application contracts to be reviewed; it is not
an independent acceptance record.

| Unit | Available input | Construction and exact consumer |
| --- | --- | --- |
| 195 reduction, `v19:195-reduction` | The retained 196-variable system, its rational solution characterization and integer range `N >= 1`; Brox's three pinned reduction notes | The redundant curve components, primitive equation basis, affine change and guarded Laurent substitution yield the 175 printed rows in `v19:195-rows`. The inverse substitutions preserve the input coordinate and both directions of rational solvability. |
| 195 coefficient bound, `v19:195-fixed` | The complete printed rows and the retained Busy Beaver parameter theorem | With `C = 149^N`, the exact height is `max(126616122944180358034867798936, 149^(2N+2))`. Specializing `N = BB(2^1000)` preserves the parent defining property and its strict `BB(2^2000)` upper bound. The parameter is fixed, not a quantified coordinate. |
| Effective sums, `v19:sum-height` | The integral Weierstrass equations and formal-group valuation identities displayed in the proof | The argument separates formal and nonformal points and bounds the heights of the required sums. The finite valuation normalization and its residue-degree weight are stated explicitly. These estimates feed `v19:250-pole-input`. |
| Contact height, `v19:reflected-height` | The retained five-contact supplier `q214:height-supplier`, including its H0 domain and H4.2 bound | The defined radical `M_5` is compared with `M_S`; positive monotone factors justify substitution. The maps `2+1/t` and `2+1/(2-t)` have the displayed excluded domains. Their radical supports and fixed exceptional prime factor give the reflected ten-contact inequality used in soundness. |
| Additive detectors, `v19:250-construction` and `v19:250-local` | The retained 214-coordinate parent, its 212-coordinate additive rewriting, and Carbon's supplied detector data | The manuscript derives the trace and second-shift identities, local divisibilities and nonvanishing guards. The standalone interface check compares all 188 printed parent rows and reconstructs both aggregate identities. |
| Soundness, `v19:250-soundness` | The preceding local extraction and explicit height inequalities | The common integer parameter is set to `N = 10220`; the displayed rational and integer inequalities exclude noninteger inputs. All fixed exceptional contacts and the scalar exponent are handled in the proof. The finite checker verifies the numerical threshold inequalities but does not replace the height argument. |
| Completeness, `v19:250-completeness` | The retained simultaneous parameter and witness constructions | The proof chooses witnesses on the same nonzero guard chart and satisfies all additive shifts simultaneously. Its stated integer range includes `N = 10220`. No converse is inferred from a one-way algebraic substitution. |
| Explicit table, `v19:250-maps`, `v19:250-rows`, `v19:250-fixed` | Carbon's 247-to-244 Laurent certificate and six-coordinate ladder | All 216 Laurent identities, three deleted identity rows and six guards are checked. The ladder exponents are `449, 1277, 2555, 5110, 10220, 20441`. The resulting 222 quadratic residuals expand to the exact 3,362-term table and the plain-algebra expression. |

## Application conventions and coverage

1. **Source versions.** Brox's 195 sources are fixed at commit
   `cd474ee67104586c9d71885a7c95e8a21f12ca0c`. The selected original input bytes,
   including Carbon's construction data, are listed in `construction/INPUTS.json`.
   The retained parent is the frozen Version 18 manuscript.
2. **Carriers.** The input and witnesses range over the rationals. The family
   parameter `N` is a fixed positive integer and `C = 149^N`; it is not another
   existential variable. Polynomial coefficients after specialization are integers.
3. **Domains.** Guard equations certify every divided coordinate is nonzero.
   The five- and ten-contact exclusions are stated before their height estimates.
   The separate argument on the potential zero reference stratum supplies the
   needed alternative rather than assuming a denominator is nonzero.
4. **Maps and direction.** The printed coordinate maps and primitive row
   operations preserve the distinguished input. Both forward and inverse maps
   are part of the rational-solution correspondence; clearing a Laurent unit
   is used only on the guarded domain.
5. **Normalizations and constants.** Field coordinates, residue-degree height
   weights, scalar exponents, primitive row factors and the nine nonunit
   coordinate constants are printed. The reflected radical comparison retains
   its fixed exceptional prime. These constants are not discarded as asymptotic
   error terms.
6. **Quantifiers and uniformity.** One input-independent family parameter is
   selected. Completeness supplies simultaneous witnesses for every integer
   input. The explicit construction uses the proved fixed threshold `10220`,
   while the 195 specialization uses the retained ineffective family threshold
   bounded by the stated Busy Beaver convention.
7. **Output identity.** The finite checks parse the actual printed 175 and 222
   rows, expand their squares, and compare the resulting coefficients with the
   supplied tables. The plain-text parser reconstructs the same explicit
   polynomial coefficient by coefficient.
8. **Consumers.** The two final quartic theorems consume these complete
   correspondences and the retained arithmetic foundations. The old results
   remain proof dependencies and historical records; no previous manuscript is
   rewritten or relabeled.
9. **Review boundary.** Finite checks establish the identities, support and
   numerical inequalities they enumerate. The arithmetic implications and the
   assembled source/PDF pair require the genuine Protocol B decisions on the
   final PR revision. Those decisions are recorded with the release, including
   any limitations actually reported by the reviewers.
