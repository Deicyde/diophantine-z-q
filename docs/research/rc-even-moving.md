The moving input is discharged: `movingStep` proves the existing `MovingStepLaw` for the actual difference at level `M * p`, and `evenMovingSieve` supplies `EvenMovingSieveLaw P U` for any fixed good set. The resulting `evenWeightTwo_from_unary` and `evenExpansion_from_unary` have no moving-law premise. The fixed expansion still needs the separate unary law and, for lattice transfer, the existing common-place coordinate comparison.

The analytic step only needs an odd prime and `4 ∣ M`; the existing iteration uses freshness to control level support. The character at the new level is the old character pulled back and multiplied by `primeCharacter`. At odd unit representatives this character is the Kronecker symbol `(p/n)`. It has value 1 at −1 and square 1 on every unit. The proof uses quadratic reciprocity for the former formula and the finite-field quadratic character and the character modulo 4 for the latter facts.

The key comparison is for the quotient of the actual theta values. Replace the two matrices by right translates with the same positive prime lower-right entry; Dirichlet's theorem supplies such an entry in the common progression. This replacement only translates the argument in the period-one theta law. Resummation at the right cusp uses the same prime denominator for both matrices. Completing the square cancels the Fourier phase, and changing the Gauss numerator by `p` gives the Legendre factor. The two principal complex powers scale by the same positive factor. Triangular matrices are handled directly by periodicity. This computes the sign needed for weight 3/2 without assuming a general classical multiplier formula.

For the `U_(p²)` translates, use the existing integral conjugation and permutation. Two applications of the dilation comparison turn each conjugate into the old matrix with integral translations on the left and right. Each comparison uses the same lower-right entry modulo the level, so the two quadratic factors cancel. The rational cusp change of coordinates separately transports boundedness, including for each member of the finite sum.

## Lean results

| File | Theorems and the input supplied |
| --- | --- |
| `Character.lean` | `kronecker_of_odd` removes the 2-part, `primeCharacter_int` evaluates the concrete character at a unit, and `primeCharacter_nat`, `primeCharacter_neg_one`, `primeCharacter_sq` prove the all-unit formula, parity and quadratic identity. |
| `Affine.lean` | `affine_det`, `affine_map_pos`, and `affinePoint_coe` identify the positive affine matrix action. `affinePoint_holo` and `affinePoint_cusps` supply holomorphy and the bound at every cusp under this substitution. |
| `Matrices.lean` | `det_eq`, `sl_coord`, and `mem_level_iff` express the determinant, action and level. `scaleLower_entries` and `scale_smul` give the dilation conjugation and `scalePoint_coe` identifies the dilate. `rightT_entries` and `leftT_entries` give integral translation of columns and rows. |
| `PrimeGauss.lean` | `quadraticFourier_zero_eq_gauss` rewrites the finite quadratic sum using the square-root counts in the finite field. `quadraticFourier_prime_scale` gives the Legendre factor. `theta_right_cusp` cancels the finite Fourier phase in the Poisson resummation at the common prime denominator. |
| `Theta.lean` | `theta_double_im`, `theta_nonzero` and `theta_periodic` give basic theta facts. `thetaMultiplier_rightT`, `thetaMultiplier_leftT`, and `thetaMultiplier_triangular` compute the translation and triangular cases. `theta_prime_formula`, `cpow_nat_mul` and `theta_scale_prime` prove the comparison at prime denominator. `thetaMultiplier_scale` gives the exact comparison for all the required matrices. |
| `Dilation.lean` | `Vp_eq_scale` and `unitCharacter_d` identify the existing function and its character evaluated on a matrix. `Vp_threeHalves` proves the three fields of the law for the actual `Vp`. |
| `Translate.lean` | `unscalePoint_coe`, `Up_eq_affine`, `two_scale_unscale`, and `scalePoint_inj` connect the actual summands to the two dilation conjugations. `upSquare_terms` gives the permuted arguments, exact theta multipliers and character residues. `Up_holo` and `Up_cusps` transfer holomorphy and bounding; `upSquare_threeHalves` supplies the preservation law for the sum. |
| `Assembly.lean` | `sub_smul_threeHalves` handles scalar subtraction. `movingStep` proves the original statement, and `evenMovingSieve` iterates it. `evenWeightTwo_from_unary` assembles the weight-two form with the individual block characters; `exists_evenForm` supplies the form used in `evenExpansion_from_unary`, which transfers the expansion at every positive index. |

These are GLUE proofs. No new structure or proposition is taken as a hypothesis. The project’s count and pinned statements are unchanged.

## Remaining inputs

- `EvenUnaryStageLaw P hS i j` for the matching parity shells (tex 9548–9555, 9618–9625): unary transformation, owned by the separate unary task.
- A compatible complex embedding of the coefficient place and the comparison of constituent coordinates to those of the same assembled form (tex 9649–9655, 9754–9764): constituent construction, owned by the lead. The common choice for all tested sets remains a separate budget input.

## Known issues

Manuscript error inherited from the base audit (tex 8162–8167): the proposed integer multipliers omit the factor of the base coefficient. The explicit factored formula at tex 8168–8176 accounts for it. The fresh-prime calculation does not use the recurrence shorthand.

The earlier notes point to Shimura, *On modular forms of half integral weight*, §1, for the classical theta multiplier. The section locator is **UNVERIFIED** in this pass. The proof here uses the existing checked Poisson resummation and Mathlib’s checked quadratic reciprocity, Gauss sum, and primes-in-progression theorems.

## Manuscript check

- Tex 9484–9496 — OK: the moving product for the full two-torsion case is the finite product of the actual difference operators.
- Tex 9497–9508 — OK: integral dilation conjugation and its fractional linear action.
- Tex 9509–9512 — gap filled: the exact theta quotient comparison proves the prescribed quadratic factor, and cubing retains it.
- Tex 9514–9532 — OK: the normalized rational translates have the stated conjugates, permuted by the residue calculation.
- Tex 9533–9540 — gap filled: equality of the characters and the exact theta multipliers in the finite sum.
- Tex 9541–9542 — gap filled: the triangular cases and boundedness at every cusp are covered.
- Tex 9543–9546 — OK: the existing Fourier calculation includes zero and the induction raises the level by just the new prime.
- Tex 9548–9555 and 9618–9625 — unverified: the separate unary transformation is an input.
- Tex 9626–9632 and 9647–9648 — OK: the existing fixed assembly uses the actual theta products and the prescribed divided series.
- Tex 9649–9655 and 9754–9764 — unverified: constituent coordinates are supplied by the model, separately from this moving calculation.
- Tex 8162–8167 — error: inherited normalization error described above.

## Verification

VERIFIED: the serial Lake build of `EvenMoving.Assembly` and direct `lake env lean -j1` checks of each of the eight new modules succeeded. [The scratch audit](../../scratch/rc-even-moving/Audit.lean) checked all 48 named theorems, plus 20 generated private helpers. Its [printed output](../../scratch/rc-even-moving/axioms.txt) uses only `propext`, `Classical.choice`, and `Quot.sound`. See also [the sizing and results log](../../scratch/rc-even-moving/log.md).
