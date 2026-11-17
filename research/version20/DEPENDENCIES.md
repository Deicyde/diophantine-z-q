# Version 20 source and consumer map

This map concerns `manuscripts/quartic_v20.tex`. Its new Part I contains the
247-variable construction; Part II retains the 195 and 250 constructions.
The source/PDF hashes are in `RELEASE-MANIFEST.json`. This is an application
record for review, not an independent acceptance record.

| Unit | Available input | Construction and exact consumer |
| --- | --- | --- |
| Starting system, `v20:normalization` | The retained `v19:250-maps`, its 216 unbalanced quadratic rows, and `v19:250-soundness` and `v19:250-completeness` at `N = 10220` | Replacing the last ladder coordinate in the first 216 printed 250 rows by `A` identifies the exact 244-coordinate system. At `A = 149^20441` it has rational witnesses exactly for integer inputs. No other ladder coordinate occurs in these rows. |
| Rational normalization, `v20:normalization` | Carbon's normalization certificate, whose source hash matches the released Version 19 table | The manuscript specifies every diagonal coordinate scaling and every entry of the 216 by 216 row matrix. The scalings are nonzero and fix input 1. The block determinants prove invertibility; the independent checker also checks both products with the supplied inverse. All 216 resulting quadratic rows are compared exactly. |
| Ladder and permutation, `v20:ladder` | The normalized rows, in which only row 61 uses `A` | Three equations have the unique values `149^5110`, `149^10220`, `149^20441`. The complete permutation fixes the input and these three coordinates. Both maps are invertible over the rationals, as consumed by `v20:247-fixed`. |
| Explicit polynomial, `v20:247-rows` and `v20:247-fixed` | The 219 printed integer quadratic rows and the preceding equivalences | A zero of their squared sum over the rationals is a simultaneous zero. Conversely, integer-input witnesses extend by the ladder and both invertible maps. Exact expansion gives 3,385 monomials, all 247 variables, content one and coefficient one at `x1^4`. The largest coefficient is the constant `149^10220 + 298442980098761875927809873 < 2^73780`. |
| Decimal presentation | The same expanded coefficient dictionary | The specified canonical one-line notation has 96,712 ASCII bytes. The independent renderer and PR145's measuring script agree byte for byte with the supplied expression. The size convention affects the record classification, not the defining property. |
| Retained 195 reduction, `v19:195-reduction` | Brox's three reduction notes and the retained 196 system | The 175 printed rows and their input-preserving rational equivalence are unchanged. The secant calculation is now written without an implicit division by its possibly zero slope. The nonzero constants are identified as the ratio scales. |
| Retained Busy Beaver specialization, `v19:195-fixed` | The complete 195 rows and the retained parameter theorem | The single specialization `C = 149^BB(2^1000)` is unchanged, as is the strict coefficient bound `BB(2^2000)`. It is described as a polynomial with Busy Beaver coefficients, not as a quantified family. |
| Effective sums, `v19:sum-height` | The displayed integral Weierstrass equation and its invariant differential | A short formal-log homomorphism argument now justifies additivity on positive-valuation parameters, including residue characteristic 2. The resulting height estimate is consumed in `v19:250-soundness`, not in the local pole-identity input. |
| Retained soundness and completeness, `v19:250-soundness` and `v19:250-completeness` | The local extraction, five/ten-contact estimates, simultaneous witness construction and proved threshold `N = 10220` | Only the scalar lower bound `c >= 149^L_N` and the displayed height bound are needed. The former overstrong divisibility citation is replaced by that actual lower bound. The resulting equivalence supplies the starting system for the new 247 theorem. |
| Retained 214 to 212 step, `v19:250-construction` | The displayed parent equations | Coordinates 119 and 120 and rows 64 and 65 are identified explicitly. Their other occurrences are only in the four replaced rows, not in any supposedly unchanged row. The Version 20 checker rejects unmapped deleted coordinates. |
| Retained 244/250 tables, `v19:250-maps` and `v19:250-rows` | The retained Laurent certificate and ladder | The Version 20 checker explicitly verifies that input 1 is absent from the nonzero exponent weights and eliminated powers, and compares the actual printed exponent table to the certificate. The old released checker remains unchanged. |

## Application conventions

1. **Source versions.** The six new original data files are pinned in
   `construction/INPUTS.json`. The previous source and its Brox inputs remain
   pinned under `research/version19/`; no upstream producer is executed.
2. **Carriers.** Every coordinate map is over the rationals. Row operations
   have fixed rational coefficients. The specialized quadratic rows, and hence
   their squared sum, have integer coefficients.
3. **Domains.** The new scaling and row operations have no variable-dependent
   denominators. The older Laurent substitutions retain all their nonzero
   guard equations. No guard is inferred merely from a one-way substitution.
4. **Coverage and direction.** Every rational input and every witness tuple
   for the starting system can be transported forward. Every zero of the
   final squared sum transports back. The three ladder variables have unique
   forced values. There is no exceptional input chart in this new step.
5. **Normalization.** The row matrix is not orthogonal, so its squared sum
   need not equal the old squared sum as a polynomial. Its invertibility gives
   equality of simultaneous zero sets, which is exactly what is consumed.
   Input 1 is fixed by the diagonal scaling and the permutation.
6. **Quantifiers.** `N = 10220` is fixed for the explicit polynomial. The
   retained 195 polynomial has a different fixed Busy Beaver parameter; it
   is not another existential variable. Neither construction changes the
   arithmetic existence theorem's quantifiers.
7. **Output identity.** The checker parses the actual printed rows, expands
   them and compares every coefficient. It also parses both scaling tables,
   the row matrix, the permutation and the retained exponent-weight table.
8. **Affected consumers.** The new theorem consumes the retained 250
   soundness/completeness arguments. The four explanatory corrections are
   localized as above. No older theorem statement, 195 row or released file
   is changed. Unchanged historical approvals are evidence of their original
   scopes, not new acceptance of this manuscript.
9. **Review boundary.** Original local Fable reviews of the new proof,
   corrected passages and printed tables, the final wording acknowledgment,
   and the source/PDF/build record are retained in `reviews/`. Their exact
   hashes and scopes are listed in the release manifest. No Carbon review of
   this manuscript draft is asserted. The final Protocol B decisions, including
   scope limitations or owner overrides, must be recorded separately; these
   local reviews do not establish protected acceptance.
