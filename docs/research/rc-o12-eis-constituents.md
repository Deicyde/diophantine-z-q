# Eisenstein constituent identifications for (O.12)

Scoped stop: the two identifications required by `O12Eisenstein.eisenstein_branch` are derived from a primitive weight-two form, its realization in the model's basis, and good-prime data for the model representation. The actual primitive character-pair construction and its occurrence in the theta blocks of tex 9647–9654 and 9754–9771 are still missing. Given those inputs, `realized_branch` supplies the exact local matrix and scalar clause and the projected Fourier comparison at one. There is no new printed leaf.

Convention check: the second character of the ordered divisor sum carries the 2-adic cyclotomic twist; the matrix in (O.12) instead puts the unramified line first. The analytic degeneracy is the normalized substitution `f(dz)`, and the column scale is separate. The dummy index zero in the theta coefficient implementation is not an Eisenstein constant term. These differences of presentation are reconciled below. The arithmetic-Frobenius conventions in tex 9793–9797, 9862–9873 and 10358–10360 agree.

For the pair `E`, the level of the primitive form is the product of its two conductor moduli. At the common level `N`, `BaseForm.atLevel` constructs the actual modular form using the tree's analytic degeneracy map. If the source block has exponent at most one at `p`, its divisibility conditions force the degeneracy index to be prime to `p`, even if the ambient level itself has a higher exponent. The coefficient field of definition maps into both the complex and 2-adic fields. This lets `ColumnRealization.expansion` compare coefficients without positing an identification between those two target fields.

The representation comparison uses trace on the **primitive** good eigensystem. A degree-`d` copy can have zero coefficient at a good prime and still have the same good Hecke eigenvalue as its primitive form. Frobenius at any prime outside the fixed conductor, the pair conductors and the finite test exclusions is covered by the tree's density theorem. Unramifiedness of this coordinate compares any such lift with the model's chosen lift. Continuity then gives equality of traces everywhere. The tree's proved Brauer–Nesbitt theorem yields one basis over the model's coefficient field; the semisimplicity hypothesis on the supplied model representation cannot be read off from its traces alone.

## Statements

All names below are in `ZInQ.Manuscript.RC.O12EisConst`. Write $S = (\mathrm{active}\cap\mathrm{ramified})\cap\mathrm{eisenstein}$, $\pi_S$ for its projection and $a_n(v)$ for the model's positive coefficient reading.

| Declaration | Statement and use |
| --- | --- |
| `map_ramified` | Changing coefficients commutes with the construction of the ramified character (quadratic local factor times the prime to $p$ character). Private helper for the expansion. |
| `map_divisorCoeff` | Changing coefficients of both ordered characters commutes with the weight-two divisor sum. Private helper for the expansion. |
| `mapPair_coeff` | For every $n$, the coefficient of the transported pair is the image of $a_n(E)$. Ensures the pair used in `Coordinate.expansion` is the same pair used in `Coordinate.split`. |
| `coeff_one` | The primitive divisor sum at $1$ is $1$, in both orders. Checks the normalization of `BaseForm`. |
| `BaseForm.atLevel_character` | If $d\,\mathrm{level}(E)\mid N$, the genuine level raise $V_d E$ has the product character pulled back to the units at level $N$. Verifies level and character compatibility of the series used in `expansion`. |
| `BaseForm.atLevel_coeff` | For every $n>0$, the complex expansion of the scaled old copy is the image of $s a_{n/d}(E)$ if $d\mid n$, and zero otherwise. Gives the analytic step toward `expansion`. |
| `ColumnRealization.expansion` | The model coefficient of the coordinate column at $n>0$ equals $k(s)\,\mathrm{degenerate}(d,a(\mathrm{mapPair}(E,k)),n)$, where $k$ is the coefficient embedding. Supplies `Coordinate.expansion`. |
| `divisorCoeff_prime` | At a prime $q$, the ordered divisor sum is $\chi_1(q)+q\chi_2(q)$; comparison with the existing good Hecke formula of `ThetaCoeff.Hecke`. Private helper for the split. |
| `dirichlet_at_frob` | At arithmetic Frobenius prime to the modulus, the Galois character on roots of unity takes the Dirichlet value at $q$. Private helper for the split. |
| `weightTwist_at_frob` | At any genuine arithmetic Frobenius at an odd prime $q$, the weight-two twist takes value $q$. Supplies the good normalization with no choice of inertia at the test prime. |
| `normalizedRep_matrix` | The constructed `GL₂` homomorphism is diagonal at every $g$, in the unramified-first order. Gives the target matrix of `Coordinate.split`. |
| `normalizedRep_good` | At odd arithmetic Frobenius away from both moduli, trace is $a_q(E)$ and determinant is $q\chi_1(q)\chi_2(q)$ in both orders. Supplies the characteristic-zero good-prime comparison for the split. |
| `normalizedRep_semisimple` | The eigenspaces of the inertia flip split any invariant subspace into its coordinate axes; the remaining axes give an invariant complement. Supplies the target semisimplicity for Brauer–Nesbitt. |
| `continuous_dirichlet`, `continuous_normalizedTrace` | A finite Dirichlet character is locally constant since the stabilizer of a primitive root of unity is open. The normalized trace is continuous after also using the continuity of the cyclotomic character and its coefficient embedding. Private helpers for the split. |
| `RepInput.split` | A continuous semisimple model representation, unramified at the good tests and with the primitive good traces, is conjugate in one basis over $K$ to the normalized direct sum for all $g\in G_{\mathbb Q}$. Supplies `Coordinate.split`. |
| `degree_coprime_of_level` | If $d\,\mathrm{level}(E)\mid M$ and $p^2\nmid M$, then $d$ is prime to $p$. Supplies `Coordinate.degeneracy_coprime` from the original block level. |
| `realized_branch` | For each $i\in S$, there is one basis with inertia matrix $\operatorname{diag}(1,-1)$ and Frobenius matrix $\operatorname{diag}(\lambda_i,\mu_i)$, and the assembled $U_p v(i)=\lambda_i v(i)$ on active inputs. In addition $a_1(\pi_S U_p v)=a_p(\pi_S v)$ there. Applies the existing `eisenstein_branch` with `coordinates`, for any complementary operator. |
| `withEisensteinUp_complement` | The complementary projection of the assembled action is `other` applied to the complementary input and projected back. This leaves room for arbitrary action on old multiplicities. |
| `project_add_complement` | A vector is the sum of its two complementary projections. Private helper; used only in characteristic zero. |
| `withEisensteinUp_eq_ambient` | If an ambient operator commutes with the selected projection on active inputs and has the positive Fourier shift on the selected space, it agrees with the assembled operator on active inputs, provided the selected positive expansion is injective. Supplies the optional comparison to a previously supplied operator. |
| `withEisensteinUp_atOne_iff` | The full coefficient comparison at one is equivalent to the complementary comparison $a_1(\pi_{S^c}\,\mathrm{other}\,\pi_{S^c}v)=a_p(\pi_{S^c}v)$. Supplies the gluing statement for `FourierData.UpAtOne`. |

The character and level calculations beyond what is stated in the manuscript, the matrix construction, and the comparison of projections are on-the-spot, provenance (c). Chebotarev and Brauer–Nesbitt are existing proved results in the tree; the latter is used only for the representation isomorphism, which is stronger than the equality of scalar trace and determinant in tex 9767–9769.

## Remaining inputs

| Input | Tex | Owner and smallest needed statement |
| --- | --- | --- |
| `BaseForm` for the actual primitive pairs | 9647–9654, 9762–9764, 9862–9864 | ELLIOT, missing analytic theory (large). For the occurring ordered primitive pair of even product character with one factor ramified at $p$, the normalized series is in $M_2(\Gamma_1(m_1m_2),\chi_1\chi_2)$ with the positive coefficients $\sum_{ud=n}\chi_1(u)\chi_2(d)d$. This needs the weight-two convergence/transformation, behavior at the cusps, and identification of the expansion at infinity; no constant-term formula is used by this lane. The generic holomorphic Eisenstein construction in Mathlib assumes weight at least three, and the level-one weight-two series does not supply this result. |
| Actual selected coordinates and `ColumnRealization` | 9647–9654, 9754–9771 | ELLIOT and realization lane, missing constituent decomposition (large). For each selected active ramified Eisenstein index give its primitive pair, block level and its exponent bound, degeneracy index, nonzero scale, and common field of definition. Identify that actual basis column with the scaled $V_d E$ by compatible positive coefficients over the common field. A holomorphic weight-two form alone does not provide this basis or the labels. |
| `RepInput` and the coefficient topology | 9649–9654, 9660–9668, 9762–9771 | ELLIOT and model realization. Over the chosen characteristic-zero Hausdorff coefficient field with continuous $\mathbb Z_2\to K$, record for the same column semisimplicity, continuity of the trace, trivial inertia at the tests and trace equal to the primitive good Hecke eigenvalue on the chosen Frobenius outside a finite set. If the representations are defined by the two characters, the split attachment supplies semisimplicity; the bare existing model does not. No local matrix identity or determinant hypothesis on the abstract representation is used. |
| Complementary action and comparison, for full `LocalInput` | 9754–9761, 9852–9864, 9885–9902 | Realization/formwise lanes and existing cuspidal local work. Supply the action on the remaining coordinates and its Fourier comparison at one, along with the complementary ramified new-line and support conditions and trivial inertia on the active old sectors. Old $p$-degeneracies can mix and need no scalar $U_p$ for (O.12). The selected branch itself is valid with any `other`. |
| Comparison to an already given `Up`, if that route is used | 9852–9864, 9889–9902 | Realization lane. Supply separation on active inputs, the defining positive shift on the selected summand, and injectivity of its positive coefficients. It is unnecessary to assume these if one uses the assembled operator. |

The selected set is finite in the manuscript's fixed-stage finite-dimensional model. The theorem gets a finite index type from that realization and constructs the required finite subtype. At a good added prime, oddness and the choice of `LocalPair` come from the existing `TypeData.Good.ne_two` and `O12.localPair_exists`.

## Known issues

- The model's abstract `ρ` and `coefK` have neither Eisenstein tags nor their required relation. Good polynomial data alone cannot rule out a nonsplit extension with the same trace and determinant; that is the reason to require semisimplicity for recovery of the full representation.
- The inherited issue at tex 9660–9668 is that coefficientwise integrality of a good Hecke image does not show that the image belongs to the diamond-only span. The existing theta coefficient work closes the generator set under both operations. The finite-subtype branch here uses no integral projector.
- The existing stationary-support issue in `ThetaCoeff.Blocks.build` is independent of these identifications. The constructor with a single global avoid set is not used here.
- No Eisenstein normalization error was found. No new bibliographic locators are asserted.

## Manuscript check

- Tex 9638–9646 — OK: the constituent comparison takes place in characteristic zero and does not infer anything about an integral projector.
- Tex 9647–9654 — unverified: actual weight-two realization and its labeled Eisenstein decomposition remain inputs; the conditional analytic level raising and coefficient transport are proved.
- Tex 9660–9662 — gap filled: the existing good Hecke divisor-sum formula agrees with the analytic pair and with the normalized trace. Each old copy uses the same primitive eigenvalue.
- Tex 9663–9668 — gap filled: the trace comparison uses the dense set of genuine arithmetic Frobenius lifts, trivial good inertia and continuity; the inherited generator ambiguity is addressed by closing under both operations.
- Tex 9754–9761 — gap filled: an old degree divisible by $p$ would force $p^2$ into the level of the ramified block. The geometric identification of each block's level is supplied.
- Tex 9762–9771 — gap filled: good-prime agreement extends to all Galois elements, and semisimplicity makes it an isomorphism over the coefficient field. Membership of the actual theta blocks in the chosen basis is input.
- Tex 9793–9797 — OK: at good primes the Eisenstein polynomial has the same arithmetic normalization. The cuspidal comparison is outside this work.
- Tex 9852–9861 — OK: the needed shift on raised Eisenstein forms has no extra scaling from $V_d$. The cuspidal calculation and its prints are outside this work.
- Tex 9862–9864 — gap filled: the analytic degeneracy expansion and normalized Galois pair feed the existing ramified Eisenstein shift; existence of the primitive form is still input.
- Tex 9866–9873 — gap filled: the single recovered basis gives both matrices and the scalar on all retained Eisenstein copies.
- Tex 9885–9890 — OK: unramified blocks have zero inertia differences irrespective of the old multiplicity action; the complementary operator can be kept as a linear map.
- Tex 9891–9902 — gap filled: the characteristic-zero Fourier comparison at one is the sum of the selected and complementary comparisons.
- Tex 10358–10360 — OK: the normalized pair has determinant equal to the cyclotomic twist of the product nebentypus.

## Verification

`Forms.lean`, `Galois.lean` and `Branch.lean` compile individually with
`lake env lean -j1` at the pinned base, one Lean invocation at a time.
All 22 `#print axioms` checks, including private helpers, list only
`propext`, `Classical.choice` and `Quot.sound`.
