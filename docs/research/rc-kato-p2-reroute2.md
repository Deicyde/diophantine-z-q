# Correcting the dyadic Kato source

**Verdict: conditional reroute to (K15).** The corrected draft bounds the
full-open kernel for **all** primes of `N_K`. Its weight −1 condition follows
from the proved Hasse bound for the twisted Euler polynomial. Global torsion
is a separate deduction from primewise torsion, finite generation and the
dyadic Iwasawa ring. The new Appendix E adapters keep the previous output
types. They still need the geometric support triangle and the arithmetic
identifications of the cohomology and Euler system.

**Known source issue.** The application of Kato 2004, Theorem 13.4(1)(2), at
coefficient prime two in tex 1884–1893 and 7206–7241 has the proof gap
recorded in issue #168. In particular the manuscript's cyclotomic fixed-space
argument does not give the witness over ℚᵃᵇ required in Kato 1999. The reading
desk also found three errors in the earlier *transcription* of the 1999
result: it used dyadic-only localization, omitted purity as a hypothesis,
and asserted global torsion in the printed conclusion. None of these errors
is a claim about the truth of (K15).

**Lean verification.** All seven new modules elaborate with `lake env lean`.
The [audit](../../scratch/rc-kato-p2-reroute2/axioms.txt) covers 28
declarations, including private lemmas. It finds only `propext`,
`Classical.choice` and `Quot.sound`. It also checks that the retained
(K15) result has the old conclusion's exact type, that the two fixed
finite comparison formulations are definitionally equal, and that the
replacement declarations have no dependency on the superseded dyadic
bound or old Kato bundle. No audited module imports the frozen main module.

## The printed cut

**Locator:** Kato 1999, pp. 314-319, read (AI reading of the published pages).
The reading desk checked §§0.1, 0.4–0.7, Theorem 0.8 and the supporting
notation in §0.9. `Checked.KatoKodai99Thm08Print` remains a draft over
abstract cohomology (GLUE in the current tree). The three corrections
replace the corresponding rows in the [previous checklist](rc-kato-p2-reroute.md).

| Page check | Lean specialization |
| --- | --- |
| Index domain, §0.1 | Positive `N_K` divisible by 2 and coprime to `N'`; all positive multiples of `N_K` coprime to `N'`. |
| Norm step, (0.1.1) | `KodaiPrimeNorm`: for a repeated prime the multiplier is 1; for a new prime use `P_q(q⁻¹σ_q⁻¹)` with `P_q(t) = det(1 − φ_q t)` and arithmetic Frobenius. |
| Real sign, §§0.4–0.6 | Dimension one for the negative eigenspace of complex conjugation on the rational twist. |
| Irreducibility, §0.6 | `KodaiAbsIrred` over the cyclotomic tower, after arbitrary extension of coefficients. |
| Fixed space, §0.6(ii) | `KodaiUnipotent`: a `FixesAbelian` element has a one-dimensional rational fixed space. No free integral cokernel is required here. |
| Purity, §0.6(iii) and Example 0.6.2 | `KodaiPurity (-1) N_K P`: outside `N_K` the complex absolute value of each inverse Frobenius eigenvalue is `q^(-1/2)`. Lean equates its squared norm to `q^(-1)` on the roots of a common rational model of the reciprocal polynomial. The common model is appropriate for this application. |
| Class, §0.7 | Divisor parameter 1. The positive dyadic projections are the corestrictions of the supplied classes from `N_K·2^n` to `2^n`, with no degree scalar. |
| Generic nonvanishing | `GenericNonzero` tests the §0.7 class at every minimal prime. |
| Torsion, 0.8 | Torsion of the localized full `H²_𝔭` at each tested height-one prime away from two. Finite generation on p. 316 is used separately. |
| Length, 0.8, p. 316 and §0.9 | Length of `H²₀,𝔭` is bounded by the length of `Λ_𝔭/J(ξ)_𝔭`. The local target of the full open is the finite sum of `lim_n H²(ℚ_q ⊗ ℚ(ζ_(2^n)),T)` over every prime `q ∣ N_K` (divisor parameter 1). `KodaiFullOpen.H2zero` takes the kernel of the map to that sum. There is no bound in the print for the length of all `H²_𝔭`, and the former `kodai08AwayTwo_of_global` is outside the corrected route. |

The prior page check of Kato 2004 Prop. 8.12, p. 186, and (5.1.1),
p. 152, is already recorded in [the norm report](rc-kato812.md) (read,
AI reading of the published PDF). The symbol lies in `SL₂(ℤ)` or is an
integral combination of such symbols; the support for a symbol `a(A)`
also contains `prime(A)`. The printed smoother called `d` there is
`d_s` here. The two strict smoother inequalities belong to the draft
application.

## Established transport and remaining GLUE

On the Version 11 domain, take `N_K = 2Nd`, `N' = c·d_s`, and keep
`d = |h|` and `D = d·2^a` with the full odd filter. At every positive
smoother-coprime level use the same (K8) symbol, quadratic tensor transfer,
corestriction and smoother pair. On admissible multiples of `N_K`,
the fixed support and the support of `D` are already inverted in the
lower level. Thus Prop. 8.12 and the finite tensor/trace laws give the
formula on new primes. The repeated prime factor is 1.
`kodaiNorm_prime` gives the one-prime input from this older, more general
divisibility formula. The restricted `KatoXi` domain still supplies the
old reciprocity subfamily. Its intersection with `N_K ∣ m` lies in the
Kodai domain.

On descent to the dyadic tower the extra primes of the upper base level
were already in the omitted support. The earlier `kodai07_eq_retained`
therefore identifies the §0.7 class with the image of the retained class
without a scalar. The two Serre proofs still supply absolute irreducibility
and the rank-one fixed space over ℚᵃᵇ. Purity of the specialized polynomial
uses the Hasse bound to bound the twisted trace. Its arithmetic Frobenius
eigenvalues have product `q` and each norm at most `√q`, hence both norms
are exactly `√q`. The roots of the Euler polynomial are their reciprocals.
Identifying the polynomial with the action on the same Tate twist remains
part of the same Frobenius object comparison required in (0.1.1).

`kodai08_globalTorsion` uses the two sign maps from
`Λ = ℤ₂[Z/2][[X]]` to `ℤ₂[[X]]`. Adding the condition `X = 0` to each
sign gives a height-one prime away from 2. The sign maps are jointly
injective. Localization at these primes gives an annihilator on each sign;
clearing denominators preserves that sign. Combining the sign annihilators
gives a regular annihilator of each element, and a finite generating set
gives one regular annihilator of the entire full `H²`.

`KatoSupportComparison.onKernel` is the isomorphism
`ker(H²(C_j) → H²_loc,2)_𝔭 ≃ ker(H²(C_S) → ⊕_(q|N_K) H²_loc,q)_𝔭`.
Lean derives it from `KatoOddSupportCone`, the relevant exact fragment
of (K16) and the commuting restriction at two. A class in the kernel on
the full open has zero odd restriction, so lifts to the retained `H²` by
exactness. The lift is unique by injectivity; commutation gives its zero
restriction at two. Conversely exactness kills the odd restrictions of
a retained class and commutation kills its dyadic restriction. The class
index comparison still goes in the needed direction
`J_retained,𝔭 ⊆ J_full,𝔭`, by extending localized linear functionals.
This proves the transfer of the length bound and preserves the original
retained (K15) predicate. The kernel of the degree-two open restriction
is torsion by the same sign test and the localized injectivity; it no
longer has to be supplied as a separate condition.

| Input still supplied separately | Manuscript step, scope and size |
| --- | --- |
| `KodaiFullOpen`, `KodaiJStar`, `KodaiTower` | (K7)–(K8), §0.7, and (K16): object identifications and maps on the actual complexes and inverse limits. They give local terms and projections, with no torsion or index estimate. Actual cohomology and coefficient infrastructure remains substantial. |
| `KatoOddSupportCone` | (K16), tex 7257–7269: realize the restriction from the integral `j_*` comparison on the same twist. Show after localization that the cone has zero H¹ and its H² identifies with the odd local sum, compatibly with localization at two. The input only asks for that exact fragment. It has no Euler system, class or length bound. The tree has pieces of continuous cohomology and Selmer complexes, but no instance of this étale `j_*` support triangle. Estimate: several hundred lines once the actual tower and complexes are available; constructing those foundations is additional. |
| Finite generation of full `H²` | Kato 1999 p. 316, corresponding to tex 7243–7244. It is a separate module property and does not imply torsion (the ring itself is finite over itself). The ring argument is proved here, while finite generation of the actual inverse limit still needs the object identification. |
| `KatoH1Comparison` | (K7), §0.7 and tex 7243–7269: finite projection compatibility and extension of dual maps after clearing a denominator. It constrains maps on H¹ and gives no statement about H². Still needs the tower and finite presentation; estimate unchanged from the previous report. |
| `FixedKatoFiniteComparison` | (K12)–(K13), tex 7118–7142: the fixed-family comparison from `AppEK1/Comparison.lean`, with only the finite Euler-system data as its argument. Its reduction, trace, deck action and detection conditions are the same. This is one obligation; the preceding draft's `FixedRetainedFiniteComparison` name is not used at the corrected cut. It gives a finite anchor only. |
| `RetainedZeta`, `TwistTransfer`, `RetainedReciprocity`, real sign and generic nonvanishing | (K4)–(K13), tex 6904–7142, and tex 7210–7222. These are the existing finite classes, tensor and trace laws, reciprocity and nonzero/sign conditions. None makes an Iwasawa length assertion. Actual periods, the lattice and their compatibility with the same twist remain required. |
| `AppEFromKatoP2` | The construction after (K15) on the supplied constituents: positive complex, uniformly controlled local corrections and central calibration. It takes (K15) as an input and gives no proof of the source estimate. This replaces the corresponding conditional construction in the earlier draft. |

## Consumer swap and count

The [consumer inventory](../../scratch/rc-kato-p2-reroute2/consumers.md)
records the original signatures. All follow-up Lean files are new files
in `KatoP2/`; the corrected route is under `KatoP2.Checked`. Existing
modules are left intact. No integration into the statement registry or
frozen theorem is proposed in this patch.

| Consumer | Corrected supplier |
| --- | --- |
| Both `iw_thm13_4` fields, `KatoZetaLeaf`, and `KatoZetaInterface812.toOld` | These are outside the replacement declaration closure. Use the original separate finite Kato 2004 inputs; take the dyadic Iwasawa bound from the corrected 1999 draft and the transport. |
| Original `AppEFromKato` and `evenScalar32_of_kato`, and the preceding KatoP2 adapters | `Checked.AppEFromKatoP2`, `appEOutputs_of_katoP2`, and `evenScalar32_of_katoP2`, with the same outputs `AppEOutputs` and `EvenScalar32`. |
| Fixed Appendix E wrappers | `Checked.appEOutputs_of_katoP2_fixed` and `evenScalar32_of_katoP2_fixed`; same fixed form and scalar conclusions. |
| Glue sweep curve wrappers | `Checked.evenScalar32_of_katoP2_ecurve` and `evenLowerBound_of_katoP2_ecurve`; same (3.2) and (E.9) conclusions. |
| Finite norms and (E.1) | Reuse `dyadicNorm_of_retained`, `finiteNorm_of_retained` and `finite_e1_p2` from the previous pass. |
| Reciprocity and signed anchor on `KatoXi` | Reuse `RetainedReciprocity.z_ne_zero_of_L_ne_zero` and `anchored_weightedSum_nsmul_ne_zero_p2`; use `Checked.exists_nonzero_image_of_anchored_weightedSum_p2` and the shared comparison name for the finite detection. |
| Downstream callers that take `AppEOutputs` or `EvenScalar32` | No type or proof changes. |

**Δ registered LEAF = 0; Δ frozen hypotheses = 0.** Compared with the
preceding reroute, one draft source is replaced in place at the cut
(Δ draft sources = 0). Compared with the original dyadic cut,
this is −1 bundled old source input and +1 draft Kodai source. There
is no separate purity print and no additional finite comparison obligation.
At the abstract GLUE cut, one open support comparison is replaced by one
geometric exactness input. Finite generation of full H² is now explicit
(one module-property input); the deduction of global torsion is proved.

## Known issues

The theorem statement is still abstract: the actual étale towers, lattice
and Frobenius comparison, explicit reciprocity, geometric (K16) fragment
and post-(K15) construction have to be supplied. The route uses no
residual irreducibility condition or divisibility at a prime containing 2.
The all-prime kernel cannot be replaced by full H² or by the kernel of
only the dyadic restriction on the full open.

## Manuscript check

| Lines in `diophantine_zq.tex` | Verdict |
| --- | --- |
| 1884–1893, dyadic source | **error** — the cited 2004 proof does not justify the application at two as written; the corrected route uses 1999 0.8. |
| 6904–6929, (K4) and the symbol | **unverified** — still needs the comparison with the original arithmetic cohomology and the retained lattice. |
| 6931–6951, (K5)–(K6) | **OK** — the full odd conductor divides the family support and is prime to the smoothers. |
| 6953–6987, (K7) | **unverified** — the geometric inertia and integral `j_*` transfer comparison is still required. |
| 6990–7004, (K8) | **gap filled** — use all positive smoother-coprime levels and the same trace with full `D`, conditional on those arithmetic classes. |
| 7005–7023, (K9) | **gap filled** — the wider norm gives (0.1.1) on all admissible multiples, with the repeated-prime case included. |
| 7025–7034, dyadic descent | **gap filled** — the corestriction from the enlarged base agrees with the retained class, after identifying its projections. |
| 7036–7106, (K10), (E.1)–(E.2) | **gap filled** — the finite (E.1) supplier avoids the old bound; the infinite comparison remains a separate condition. |
| 7118–7142, (K12)–(K13) | **gap filled** — the finite anchor and its detection avoid the old bound, conditional on reciprocity and the one finite comparison. |
| 7143–7205, central specialization | **unverified** — the actual coefficients, period comparison and infinite specialization are separate inputs. |
| 7206–7214, application to the retained class | **gap filled** — apply the corrected print to the enlarged family and transport its class using §0.7 and the named maps. |
| 7215–7222, nonvanishing and real signs | **unverified** — the draft takes these properties of the actual supplied class and twist. |
| 7223–7225, purity | **gap filled** — hypothesis (iii) is explicit; the dyadic twisted reciprocal polynomial satisfies it with weight −1 once identified with the actual Frobenius polynomial. |
| 7226–7234, Galois image | **gap filled** — the earlier Lean proofs supply cyclotomic absolute irreducibility and the stronger fixed-space hypothesis over ℚᵃᵇ. |
| 7235–7241, (K15) | **gap filled** — the corrected cut proves the transfer from the actual all-prime kernel and deduces global torsion separately; the geometric cone and module identifications are still inputs. |
| 7243–7255, class index | **gap filled** — the transport uses the evaluation ideal of the supplied class; the degree-one object comparison and extension of dual maps are named conditions. |
| 7257–7278, (K16) | **unverified** — the exact fragment suffices in Lean, but the support triangle for the actual étale complexes has no supplier here. |
| 7280–7297, local factors | **unverified** — local control and central-value nonzero comparisons belong to the later Appendix E construction. |
| 7312–7315, unused good primes | **OK** — no unused factor is discarded merely because the fixed level meets the family support. |
| 7519–7787, positive complex and central calibration | **unverified** — the construction after (K15) is still a separate condition. |
