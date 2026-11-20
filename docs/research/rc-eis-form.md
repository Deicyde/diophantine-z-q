# Weight-two Eisenstein forms for the ramified theta constituents

Scoped stop: the normalized character-pair series has a convergent analytic expansion on the upper half plane. Its actual width-one Taylor coefficients at infinity, for every $n>0$, are $\sum_{d\mid n}\chi_1(n/d)\chi_2(d)d$ in the order used by the constituent model. The two remaining checks to construct `BaseForm` are the weight-two slash law with product character and boundedness at the other cusps, for a single choice of constant term. The split Galois attachment is unramified at the good primes and has the expected Frobenius polynomial and Fourier Hecke recursion. A labeled old line of a realized theta block gives exactly the model's `ColumnRealization`; actual labels and their block realizations remain inputs. No printed leaf is added.

The original basis orders the unramified line first. The Fourier order has the cyclotomic twist on the second character, even when that line is the unramified one. The weight-two lattice calculation uses Mathlib's Lipschitz identity and a finite sum of its translates weighted by the inverse of the second Fourier character. The degree $d$ old vector uses $f(dz)$, and its coefficient at $d$ is one. The comparison of an old copy with good Frobenius uses the **primitive** eigensystem, also when the old vector's actual coefficient at the test prime is zero. The zero at index zero of the arithmetic Hecke sequence is a dummy value, separate from the analytic constant $C$.

## Statements

New theorem names are in `ZInQ.Manuscript.RC.EisForm`. The “input” column refers to one of the three named inputs in `docs/research/rc-o12-eis-constituents.md`: **form**, **attachment**, or **occurrence**. Write $A(n)$ for the ordered divisor sum, $c$ and $k$ for the complex and model embeddings, and $f_C$ for the explicit function with constant $C$.

| Declaration | Statement | Input |
|---|---|---|
| `divisorCoeff_eq_sum_divisors` | The sum over factor pairs equals the sum over divisors $d$, with first argument $n/d$. | Form |
| `norm_divisorCoeff_le` | $\lVert A(n)\rVert\le n^2$ for complex Dirichlet characters. | Form |
| `summable_seriesCoeff`, `series_radius` (private) | The prescribed coefficient series converges absolutely for $\lVert r\rVert<1$; its formal analytic radius is at least one. | Form |
| `hasSum_series` | At every upper half plane point, the width-one series with coefficients $C,A(1),A(2),\ldots$ sums to $f_C$. | Form |
| `series_holo`, `series_periodic`, `series_boundedAtInfty` | $f_C$ is holomorphic, has period $1$ and is bounded at infinity. | Form |
| `coeff_of_hasSum` (private), `qExpansion_series` | Mathlib's width-one Taylor coefficients agree with a convergent expansion of a periodic holomorphic function bounded at infinity; in particular they equal $C,A(1),A(2),\ldots$ for $f_C$. | Form |
| `summable_lambertTerm` (private), `series_eq_lambert` | The two-index weighted sum is absolutely convergent; regrouping by $uv=n$ gives $f_C-C$. | Form |
| `primitive_ringHomComp` | Embedding the coefficient field into $\mathbb C$ preserves the conductor of a primitive character. | Form |
| `qParam_shift_pow`, `lipschitzRow_eq`, `gaussInv_ne_zero` (private) | Shifting $uz$ by $r/m_2$ gives additive Fourier phase $e^{2\pi i rv/m_2}$; the weighted row is its geometric Fourier sum times $(-2\pi i)^2\tau(\chi_2^{-1})$, which has nonzero Gauss factor for a primitive second character. | Form |
| `series_eq_lipschitz`, `pairSeries_eq_lipschitz` | The normalized sum of those weight-two lattice rows, with outer weight $\chi_1(u)$, equals $f_C-C$. This identifies both possible Fourier orders of the actual `CharacterPair` with their corresponding row constructions. | Form |
| `pairSeries_positive` | For either ordering of the actual `CharacterPair`, $[q^n]f_C=c(A(n))$ for $n>0$. | Form |
| `pairSeries_holo`, `pairSeries_boundedAtInfty` | The actual ordered-pair function inherits holomorphy and boundedness at infinity. | Form |
| `baseForm_of_modularity` | Primitivity of the two factors and the two analytic checks on the same $f_C$ produce the exact predecessor `BaseForm` at the product level with the product nebentypus. | Form, conditional |
| `divisorCoeff_eq_eisenstein` (private), `pair_goodRec` | The constituent coefficient is the existing arithmetic-function convolution and satisfies the good Fourier Hecke recursion with eigenvalue $A(q)$ and diamond scalar $\chi_1(q)\chi_2(q)$. | Attachment |
| `old_goodRec` | The degree $d$ sequence satisfies that same recursion if $d>0$ and $q\nmid d$. | Attachment |
| `weightTwist_eq_one_of_inertia` (private), `normalizedRep_unramified` | The weight twist is trivial on inertia at odd primes, and the split pair is trivial on all inertia groups at odd primes prime to both character conductors. | Attachment |
| `normalizedRep_goodAttachment` | At good arithmetic Frobenius, the characteristic polynomial is $X^2-A(q)X+q\chi_1(q)\chi_2(q)$, and its trace is the eigenvalue in the positive Fourier Hecke recursion. | Attachment |
| `baseForm_good_trace` | The primitive analytic coefficient at a good prime and the split Frobenius trace are the images under $c,k$ of the same $A(q)$. | Attachment |
| `continuous_finiteChar` (private), `continuous_splitTrace` | A finite Dirichlet Galois character is locally constant; if the embedding of $\mathbb Z_2$ is continuous, so is the split trace. | Attachment |
| `repInput_of_split_choice` | When the model uses the explicit split pair for a label, it has the predecessor's `RepInput` for any finite avoid set containing the pair-level prime factors. | Attachment |
| `atLevel_coeff_degree`, `scale_of_labeled_line` | The coefficient at $d$ of the scaled old copy is $c(s)$; a nonzero column in the complex old line whose coefficient at $d$ is $c(s)$ is precisely that scaled copy, with $s\ne0$. | Occurrence |
| `column_of_labeled_line` | A nonzero complex block column on the indicated old line, with compatible positive coefficient lifts, gives a nonzero scale over the common field, membership of the normalized copy in the block, and the exact `ColumnRealization` of the model label. | Occurrence |
| `realizedCoordinate_of_labeled_line` | With the source block level and its exponent bound, plus the attachment for the same label, the result is a predecessor `RealizedCoordinate`. Apply pointwise to the selected active ramified Eisenstein labels to use `realized_branch`. | Occurrence |

The analytic regrouping and estimates, the use of finite Fourier transform to normalize the lattice rows, the comparisons with the existing Hecke recursion, and the descent of the column scale are on-the-spot (c). The manuscript gives the constituent and Fourier conventions. No uncited weight-two modularity or decomposition is used as a printed theorem.

## Remaining hypotheses

| Exact input | Tex | Owner and size |
|---|---|---|
| The occurring ordered primitive characters (each primitive at its own conductor, even product) and the product-level slash check `PairSlashLaw E c C`: on `Gamma0 (pairLevel E)`, slash by a matrix is multiplication by the product character evaluated at its lower-right residue. | 9647–9654, 9762–9764, 9862–9864 | ELLIOT identifies the admissible pairs. Missing analytic theory, substantial: transform the weight-two character-weighted lattice rows, treating conditional changes of summation order. |
| `PairOtherCusps E c C`: for every cusp of `Gamma1 (pairLevel E)` other than infinity, the same $f_C$ is bounded there in weight two. `MissingModularity E c` is the existence of a **single** $C$ for these two checks. | 9647–9654, 9762–9764 | Missing analytic theory, substantial: estimates after moving each cusp to infinity. No prescribed closed formula for the constant is needed by the consumer. |
| For each selected label $i$ of the fixed stage and $U$, an actual block realized at common level $N$ (its subspace $W$), a nonzero complex column $f\in W$ belonging to the old line spanned by $V_dE$, $d>0$, the level divisibilities $d\,\mathrm{level}(E)\mid M\mid N$, and $p^2\nmid M$ for the ramified source block. | 9647–9654, 9754–9764 | The block realization lane supplies the actual forms, source levels and their embedding into the common space. The labeled characteristic-zero Eisenstein old-line decomposition of those blocks is an ELLIOT input / missing constituent theory (large). Block modularity by itself does not label the old copies. |
| The same actual column has a lift of each positive coefficient to the common field $D$, mapping to its complex coefficient under $c$ and to the model column coefficient $a_n(e_i)$ under $k$. | 9649–9654, 9762–9771 | ELLIOT/model realization (coefficient field and comparison for actual blocks; substantial). The lifts are for the independently given column $f$; they do not assume the divisor sum or a scale. |
| The characteristic-zero model assigns the explicit normalized pair to the same label, with a continuous coefficient embedding $\mathbb Z_2\to X.K$, the existing odd added-prime local pair for semisimplicity, and a finite avoid set containing the prime divisors of each selected pair level. Alternatively it supplies the original `RepInput` on the chosen label (continuity, semisimplicity, inertia triviality and the primitive good traces outside the finite exclusions). | 9649–9654, 9666–9668, 9762–9771 | ELLIOT/model realization (local integration). The good polynomial and unramifiedness for the explicit split choice are proved here; the abstract model's choice is not determined by its type. |

`PairSlashLaw` checks only transformation of an explicit function; it has no cusp bounds, analytic expansion or primitive-character data. `PairOtherCusps` checks only growth at the other cusps; it gives no transformation, coefficient formula, or primitive characters. Each is strictly less data than `BaseForm`. No theorem hypothesizes `MissingModularity` as a bundled form or a coefficient statement: it records the outstanding conjunction. The occurrence lemmas use existing types and ordinary subspace membership. In particular the complex line test alone omits the source-block membership, nonzero scale over $D$, common coefficient transport and model comparison that the conclusions supply.

## Known issues

- Inherited at tex 9660–9668: preservation of coefficientwise integrality by a good Hecke operator does not imply membership of its image in a span generated only by diamonds. The existing coefficient construction closes the generators under both operations. No integral projector is needed here.
- The weight-two level-one trivial/trivial pair is exceptional: $E_2$ is quasimodular. This lane concerns a pair with conductor divisible by the odd ramified prime and does not assign a primitive modular form to the level-one pair. The Fourier calculation by itself does not imply modularity.
- The word “primitive” in the predecessor interface means taking each Dirichlet character at its conductor and using the form at the product level. No larger classification of the Eisenstein space is proved here. Holomorphy of a theta block is not evidence for any particular occurrence.
- No new manuscript or cited-source error was found. No new bibliographic page or theorem number is asserted.

## Manuscript check

- Tex 9647–9648 — unverified: the actual multiplication and modularity of the theta blocks are with the block realization lane.
- Tex 9649–9654 — gap filled: once an actual block and its labeled old lines are supplied, the correct scales descend, and the explicit split Galois choice has the attachment required by the model. Actual basis labels and field realizations remain inputs.
- Tex 9660–9662 — OK: the divisor sum satisfies the stated positive Hecke recurrence for the primitive pair and its good old copies. This says nothing about membership in a diamond-only span.
- Tex 9663–9668 — gap filled: the Eisenstein trace is continuous and the split representation is unramified on the good tests. The inherited span issue requires the Hecke closure already used by the coefficient lane.
- Tex 9754–9761 — unverified: the geometric source levels and their exponent bounds remain inputs; a labeled degeneracy uses the source block level before passing to the common level.
- Tex 9762–9771 — gap filled: for the Eisenstein eigensystem, explicit arithmetic Frobenius gives the trace and determinant, and good old copies have the same eigensystem. Actual decomposition and model label assignment remain inputs.
- Tex 9852–9861 — unverified: the cuspidal Whittaker and multiplicity calculations are outside this work.
- Tex 9862–9864 — gap filled: the convergent positive expansion and good-prime character comparison are explicit; exact-level modularity still needs the two named analytic checks.
- Tex 9866–9873 — OK: the ordered coefficient convention gives precisely the attachment used by the existing unramified-first local matrix computation; the local matrix proof is inherited.
- Tex 10358–10360 — OK: the split determinant at arithmetic Frobenius uses the cyclotomic value times the product nebentypus, independent of old multiplicity.

## Verification

`Expansion.lean`, `Lipschitz.lean`, `Modularity.lean`, `Attachment.lean`
and `Occurrence.lean` each compile with `lake env lean -j1`, run serially
against the pinned base dependencies. All 36 `#print axioms` checks list
exactly `propext`, `Classical.choice` and `Quot.sound`.
