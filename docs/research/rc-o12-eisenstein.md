The Eisenstein branch of \(\mathrm{(O.12)}\) is proved for a ramified weight-two constituent given by its ordered Dirichlet pair and divisor-sum expansion. On every positive index, including multiples of \(p\), the shift has scalar \(\chi_1(p)\) if \(\chi_2\) is ramified, and \(p\chi_2(p)\) if \(\chi_1\) is ramified. The scalar is unchanged on each degeneracy \(f(q^d)\) with \(p\nmid d\). It is exactly the arithmetic Frobenius entry on the inertia-fixed line. The assembled action supplies the Eisenstein coordinates of \(\mathrm{(O.12)}\)'s `LocalBlocks.newLine` and `FourierData.UpAtOne`. No printed leaf is added.

## Normalization

`ZInQKernel/Contrib/OneProof/RC/AddressGenuine/Constituents.lean:264–267` calls the Eisenstein representation the sum of the two characters, but the field `ρ` does not encode the characters, their order, or a twist. Arithmetic Frobenius is explicit at 288–291 and in `ZInQKernel/Contrib/OneProof/RC/O12/Local.lean:33–41`. For the ordered expansion \(a_n=\sum_{ud=n}\chi_1(u)\chi_2(d)d\), the two Galois characters are \(\chi_1^{\rm Gal}\) and \(\chi_2^{\rm Gal}\epsilon_2\), where \(\chi^{\rm Gal}\) is the Dirichlet character on the action on roots of unity and \(\epsilon_2\) is the 2-adic cyclotomic character. At a good \(q\) the divisor sum at \(q\) is \(\chi_1(q)+q\chi_2(q)\); the product of the two entries is \(q\chi_1(q)\chi_2(q)\). This matches the arithmetic normalization in tex 9793–9797 and the determinant convention for Eisenstein constituents in tex 10358–10360. At \(p\) the cyclotomic factor is trivial on inertia and takes value \(p\) on arithmetic Frobenius. The ramified Frobenius entry is evaluated on the given lift \(\phi\); no evaluation at a nonunit of its Dirichlet character is used for that entry.

`CharacterPair` uses the conductor moduli: the unramified character and the away-from-\(p\) part have moduli prime to \(p\). The ramified character is the product of the two factors lifted to their product modulus, using the quadratic character of \((\mathbb Z/p)^\times\) for the nontrivial conductor-one local factor. That is the unique nontrivial quadratic character of this cyclic group. The bit specifying the order of the divisor sum also specifies which Galois line receives the twist. The order of the matrix basis is always unramified first.

## Statements

All names below are in `ZInQ.Manuscript.RC.O12Eisenstein`. Let \(S\) be the selected active ramified Eisenstein coordinates and \(\pi_S\) their projection. Write \(a_n(v)\) for the positive coefficient read using `X.coefK` and `A.index`, and \(\lambda_i\) for the divisor-sum scalar on coordinate \(i\).

| Lean theorem | Statement and use |
| --- | --- |
| `divisorCoeff_mul_of_right_zero` | For prime \(p\) and \(n>0\), if \(\chi_2(p)=0\), then \(a_{pn}=\chi_1(p)a_n\). Operator scalar and Fourier shift. |
| `divisorCoeff_mul_of_left_zero` | For prime \(p\) and \(n>0\), if \(\chi_1(p)=0\), then \(a_{pn}=p\chi_2(p)a_n\). Operator scalar and Fourier shift. |
| `dirichlet_apply_prime_eq_zero` | For prime \(p\) dividing the modulus, the Dirichlet character vanishes at \(p\) under its zero extension. Applies the two recurrences to the ramified factor. |
| `degenerate_mul` | For \(d\) prime to \(p\), if \(a_{pn}=\lambda a_n\) on positive indices, then the same holds for \(a_{n/d}\) when \(d\mid n\), extended by zero otherwise. Supplies the action on old degeneracies. |
| `cycChar_unitsMap` | Reduction of the mod-\(m\) cyclotomic character modulo a divisor \(d\mid m\) is the mod-\(d\) cyclotomic character. Used on the two factors of the ramified character. |
| `cycChar_eq_one_of_mem_inertia` | For \(p\nmid m\), the mod-\(m\) cyclotomic character is trivial on the inertia group of the chosen maximal ideal above \(p\). Supplies the unramified inertia values. |
| `weightTwist_frob`, `weightTwist_inertia` | Over \(K\) with \(\mathbb Z_2\to K\), the weight-two twist at \(\phi,\tau\) is \(p,1\), respectively, at odd \(p\). Supplies the Frobenius scale and preserves the inertia signs. |
| `quadraticDirichlet_inertia` | The Galois realization of the quadratic Dirichlet character takes value \(-1\) on the very \(\tau\) of `LocalPair`. The existing quadratic Gauss sum is compared with \(\sqrt{p^*}\). |
| `CharacterPair.coeff_mul` | The character pair in either order satisfies \(a_{pn}=\lambda a_n\) at every positive index. |
| `CharacterPair.unramLine_frob` | The unramified Galois character at \(\phi\) takes the value \(\lambda\) of the same divisor sum. Supplies the first Frobenius entry in `newLine`. |
| `CharacterPair.inertia_lines` | The Galois characters ordered unramified then ramified take values \(1,-1\) at \(\tau\). Supplies both inertia entries in `newLine`. |
| `Coordinate.local_matrices` | A single basis gives \(\operatorname{diag}(1,-1)\) at \(\tau\) and \(\operatorname{diag}(\lambda_i,\mu_i)\) at \(\phi\). Supplies both matrix clauses of `newLine`. |
| `Coordinate.column_shift` | On a coordinate column with value \(c\), scaling it to \(\lambda_i c\) gives \(a_{pn}\) at index \(n\). Allows an away-from-\(p\) degeneracy and a fixed normalization factor on the column. |
| `eisensteinUp_shift` | On the finite selected sum, its constructed operator has \(a_n(U_{p,S}v)=a_{pn}(v)\) at every positive \(n\). Proves the action without a supplied ambient operator. |
| `eisensteinUp_atOne` | On that sum, \(a_1(U_{p,S}v)=a_p(v)\). Supplies the positive Fourier comparison at one. |
| `project_up_eq` | A supplied ambient operator that commutes with \(\pi_S\) on active inputs and effects the Fourier shift on \(S\) satisfies \(\pi_SU_pv=U_{p,S}v\) on active inputs, if positive coefficients distinguish vectors on \(S\). Identifies an already supplied operator with the one constructed here. |
| `withEisensteinUp_project` | For the assembled ambient operator with any complementary action, \(\pi_SU_pv=U_{p,S}v\) for every \(v\). Supplies the match for the assembled operator without any assumed shift. |
| `newLine` | With the operator match from either of the preceding two theorems, gives the exact `LocalBlocks.newLine` result for every \(i\in S\): the two matrices and \(U_pv(i)=\lambda_i v(i)\) for every active-supported \(v\). |
| `upAtOne_projected` | With the same match, \(a_1(\pi_SU_pv)=a_p(\pi_Sv)\) for every active-supported \(v\). These are the Eisenstein contributions to the two sides of `FourierData.UpAtOne`. |
| `eisenstein_branch` | With a coordinate identification for every active ramified Eisenstein index, the assembled ambient action satisfies both conclusions simultaneously, for any independently supplied complementary action. |

Private theorems (on-the-spot, provenance (c)): `factorSum_at_mul` reindexes on factor pairs with first factor divisible by \(p\) and kills the other terms; `factorSum_swap` exchanges the factors. `weightTwist_mod` identifies the reduction of \(\epsilon_2\) with the finite cyclotomic character; `CharacterPair.unramified_value` evaluates the untwisted prime-to-\(p\) factor at arithmetic Frobenius. `sum_columns` expands a vector supported on a finite selected sum in its coordinate columns.

## Known issues

- The base interface has no Eisenstein tag or relation between `X.ρ` and a Dirichlet pair. Nor does `X.coefK` alone constrain the Fourier columns or identify the supplied `Up`. For the actual forms, the smallest input still needed here is a `Coordinate` for each selected index: a pair at its conductor moduli, its prime-to-\(p\) degeneracy and scaling, a basis identifying `X.ρ i` with the normalized character sum at every \(g\), and the positive divisor-sum expansion of that column. These are the identifications in the constituent decomposition; the proofs here do not construct the summands of the theta forms.
- When reusing an ambient `Up` rather than assembling it, its separation of the selected summand, its defining positive Fourier shift there, and injectivity of those coefficients on the selected sum identify it by `project_up_eq`. The base `LocalBlocks.preserves_ramified` alone only preserves the sum of all active ramified blocks; it does not imply this separation. The constructed operator gives the comparison without those additional ambient inputs.
- No conflicting normalization or manuscript arithmetic error was found. The cuspidal calculation and the Fourier comparison on the complementary coordinates are outside this result. No printed reference was used.

## Manuscript check

- Tex 9638–9668 — OK: the proof uses characteristic-zero coefficients before reduction; it does not need an integral projector.
- Tex 9647–9654 — gap filled: the pair is concretely realized on roots of unity, with the twist attached to the character weighted by the divisor.
- Tex 9754–9761 — OK: the calculation takes a primitive quadratic local factor at exponent one and retains away-from-\(p\) degeneracies; it does not construct the theta summands or act on the unary blocks from level prime to \(p\).
- Tex 9762–9771 — OK: the normalized pair is used on each of its degeneracy coordinates, with the same Galois and Fourier scalars.
- Tex 9773–9797 — OK: the arithmetic good-prime polynomial is consistent with the divisor-sum convention; the cited cuspidal comparison is outside the proof.
- Tex 9852–9861 — gap filled: the shift is \(a_n\mapsto a_{pn}\) on the Eisenstein coordinates, with the same scalar on each away-from-\(p\) degeneracy, proved from the divisor sum.
- Tex 9862–9864 — gap filled: split the factor-pair sum according to the ramified character's argument, and compare the resulting scalar with arithmetic Frobenius on the unramified line in each order.
- Tex 9866–9873 — gap filled: finite cyclotomic reduction and the quadratic Gauss sum determine the inertia values; the second Frobenius entry is the ramified character on the chosen lift.
- Tex 9891–9902 — OK: the projected shift at one supplies the corresponding piece of the characteristic-zero Fourier comparison before reduction.
- Tex 10358–10360 — OK: the normalized product of the two characters is the cyclotomic twist of their nebentypus.

## Verification

All three new files compile with `lake env lean -j1` against the pinned base, one Lean invocation at a time. Their 26 theorem checks, including private helpers, report only `propext`, `Classical.choice` and `Quot.sound`.
