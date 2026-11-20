# Appendix E at the fixed curve: (K1) and (E.1)

Scoped stop before the completed class (K1). Lean proves the finite identity (E.1) from the norm on the retained classes, transitivity through the primitive index, and semilinearity of that transfer. The existing Appendix E antecedent does not provide the norm at every required index or identify its classes with genuine continuous cohomology. Consequently there is no `k1e1_fixed` or constructed `Z_F` on this branch.

## Known issues

- **Range mismatch (verified in the Lean interface):** the existential `Sig ⊇ Sbad` is chosen before the family. `es_euler` only applies with both levels in `KatoXi 2 Sig`, so it excludes any family for which an odd prime of `F` lies in `Sig`. In particular, a common odd conductor prime dividing the fixed level obstructs this application. The condition on local squareclasses only forces ramification at that prime to be common; it does not forbid it. The Σ of tex 6993 is for the twisted variable `m`; applying the existing narrow relation to `D*m` would be a range error. Tex 7089 instead cites Proposition 8.12; its required wider range is not part of the current interface.
- **Smoothing mismatch (verified in the Lean interface):** the single nonzero `s` is not tagged by `c,d_s` and does not identify the elements used at `F` with those of (K5). The abstract period constants `b χ` can absorb a nonzero scalar without changing the classes, so matching the numerical field `s` alone would not identify the smoothing. The family-dependent classes of (K5) and one lattice constant fixed before all families are not supplied.

## Sizing and exact scope

The support integer is `F = ∏ q ∈ fam.support, q`. For each constituent the odd conductor is
`d = |fam.h x|`; the full conductor in (K8) is `D = 2^a d` throughout. The reduced representative
on the cofinal tail is `d * 2^n` for `n ≥ max a 2`. If one uses the original index
`D * 2^n = d * 2^(a+n)`, passing to the reduced index needs the repeated-two norm, with no new
prime. Odd primes of `N₀ ℓ` can occur in all the primitive conductors and therefore in `F`; only
the **unused** primes are proved disjoint from `prime(2N₀ ℓ)`. A single-constituent family at any
odd squarefree parameter is an example of why common ramification is allowed.

For a chosen interface witness, the full-level norm is available from `es_euler` exactly on
`Disjoint fam.support Sig`. This condition suffices for both indices; when it fails, the finite
identity instead requires `FiniteNorm` at the two actual indices. The manuscript's family-specific
smoothing integers avoid all primes of `F`, so their exclusions do not themselves remove an
index of the selected family. The existing existential `Sig` lacks that guarantee. Also,
replacing `Sbad` by a larger set containing `F` would force those primes into `Sig` and does
not extend the norm. The report does not infer wider coverage from Kato's (13.1.1).

The finite computations are small: restore the prime support from the squarefree product,
identify the added primes, and push the Euler factors through the weighted group-ring map.
Inverse Shapiro, the norm formula, Mackey vanishing and continuous cochain functoriality already
exist. The new map lemmas identify which transfer and which coefficient action to use. The named
stop is the comparison with the **retained** classes. Its construction needs the integral
inertia condition from (K4)/(K7), its maps into the finite group cohomologies at a fixed support,
and the original lattice map at all precisions. The estimate of hundreds of lines for the map
compatibilities and possibly thousands for the arithmetic infrastructure is speculative; the
existing interface's own sizing also distinguishes this from constructing the regulator.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 6846–6867 (K1) | unverified | The retained class in the completed group and the lattice bound uniform before all families still need a realization. The finite algebra preserves the family index on the coefficient ring. |
| 6903–6929 (K4) | unverified | The fixed-image lattice and the common symbol combination are not fields of the existing interface. The single lattice inclusion, once realized, is what fixes the exponent before the family. |
| 6931–6952 (K5)–(K6) | unverified | The congruences and the valuation computation are already proved in `Even/Smoothing.lean`. The compatibility of the stated retained scalar with the cited construction was not independently rechecked, and the existing interface does not identify its scalar or classes with this choice. |
| 6953–6987 (K7) | unverified | The Mackey vanishing implication is in the tree. The realization from the integral étale inertia condition into the chosen ambient support is missing. |
| 6989–7024 (K8)–(K9) | unverified | The group-ring substitution is checked algebraically; the abstract interface does not give the untwisted input norm on this entire conductor range. The wider hypotheses of the cited Proposition 8.12 were not independently reread. |
| 7025–7035 | unverified | On the cofinal tail the dyadic part introduces no new prime; applying the repeated-two norm to the same genuine classes and in the required range remains part of the comparison. |
| 7036–7071 (K10) | gap filled | The basis map extends to an integral algebra map; inverse deck action transports to the stated twist, and evaluation composes the weights. Applying this to the specific family requires identifying its cyclotomic quotient and the Shapiro coefficients. |
| 7074–7084 | unverified | Finite coefficient pushforward commutes with a compatible quotient. The coherent arithmetic images, real tower identification and passage to completed cochains via the cited inverse-limit sequence have not been instantiated. |
| 7086–7088 | gap filled | Change of upper coefficients and the unnormalized norm after inverse Shapiro give corestriction on actual continuous cochains and on degree-one cohomology. Identifying the specific family coefficient map with this transfer still requires the finite cyclotomic coefficient identification. |
| 7089–7092 (E.1) | gap filled | Transitivity and semilinearity transport the norm equality with exactly the unused factors. The finite identity has explicit premises for those maps and for the norm; the genuine completed identity is unproved. |
| 7093–7107 (E.2) | gap filled | The finite basis formula retains both character factors, including a nontrivial character modulo four. At `n ≥ max a 2` the two modulus divisibilities are available; the arithmetic identification with the family characters remains to be supplied. |

## Lean statements

All declarations below are in `ZInQ.Manuscript.RC.AppEK1`; the module names are under
`ZInQKernel/Contrib/OneProof/RC/AppEK1/`.

| Declaration | Statement |
| --- | --- |
| `weightedMap_single` | The integral algebra map sends `single s r` to `single (bar s) (r * χ s)`. |
| `weightedMap_invDeck` | The map transports multiplication by `[g⁻¹]` to multiplication by `χ(g)[bar(g)⁻¹]` for a quadratic weight, on every input. |
| `weightedMap_comp` | Composing two weighted maps composes the deck maps and multiplies the pulled-back weights. |
| `specialize_familyMap` | Evaluation at `x` after the family map gives the scalar map with weight `χ₀ * x.comp ψ`. |
| `weightedMap_quotient` | A commuting square of deck maps gives a commuting square of coefficient maps if the weight factors through the smaller level. |
| `weightedMap_fullWeight_single` | The weight at a modulus divisible by `2^a` and `d` is the product of the pulled-back dyadic and odd weights. |
| `prime_of_mem_support`, `two_not_mem_support`, `supportProduct_ne_zero` | Every support member is prime, none is two, and the product is nonzero. |
| `primeFactors_supportProduct`, `oddConductor_dvd_supportProduct` | The product recovers the support, and the primitive odd conductor divides it. |
| `primeFactors_mul_two_pow` | At a nonzero modulus, multiplying by a positive power of two adds two to the prime support. |
| `katoXi_support_iff` | For `n > 0`, membership of `F * 2^n` in `KatoXi 2 Sig` is equivalent to disjointness of `fam.support` and `Sig`. |
| `addedPrimes_eq_unused` | For `n > 0`, the prime-factor difference between `F * 2^n` and `d * 2^n` is exactly `unusedPrimes fam.support (fam.h x)`. |
| `finiteNorm_of_isEulerSystem` | At a covered family `es_euler` supplies `FiniteNorm`, the tame norm at those two indices with the product over the unused primes. |
| `dyadicNorm_of_isEulerSystem` | At a fixed odd part, if both indices are covered, increasing a positive dyadic exponent introduces no Euler factor. |
| `finite_e1` | `FiniteNorm` on the retained elements, transitivity through the primitive level, and semilinearity of its transfer imply finite (E.1). Each scalar is the image of the original Euler factor under the full weighted map. |
| `anchored_weightedSum_nsmul_ne_zero` | For a covered index and a character with the indicated signed weights, a nonzero partial central value implies no nonzero natural number kills the signed deck sum in the original slot. |
| `inducedCoefficientMap_smul` | Postcomposition with an upper subgroup coefficient map intertwines the ambient right translation on coinduced functions. |
| `shapiroInv_coefficient_natural` | On continuous cochains with one transversal, inverse Shapiro commutes with the change of upper coefficients. |
| `weightedTransfer_cochains`, `weightedTransfer_H1` | The resulting Shapiro composite with the unnormalized norm equals change of upper coefficients followed by actual corestriction, on cochains and on `H¹`. |
| `tensorCoeffMap_tmul`, `tensorCoeffMap_smul` | Change of scalars in the coefficient tensor acts by the ring map on the pure coefficient factor and intertwines the transported Galois action; this induces `tensorCoeffH1`. |
| `mapAction_weightedMap_invDeck` | In that tensor representation the pushed-forward inverse deck unit has exactly the quadratic twist and quotient action of (K10). |
| `exists_nonzero_image_of_anchored_weightedSum` | Given `KatoFiniteComparison`, the anchored deck sum has nonzero image at some actual finite precision in continuous cohomology. |

`KatoFiniteComparison` states that `es.H m` maps to
`H¹_cont(ker(cycS_m), E(ℚ_S)[2^i])` at each cyclotomic index in the family tower and every
precision, with the actual restricted action. The maps commute with the multiplication-by-two
transition on torsion, the genuine nested corestriction, and the action of each ambient lift of
a deck element. If a class maps to zero at every precision, a power of two kills it in the original
module. This allows the torsion kernel of a fixed lattice change but preserves the signed-sum
anchor. The fixed specialization `FixedKatoFiniteComparison` uses `Ecurve ℓ` and the definitional
value `CST.newformLevel (Ecurve ℓ)` of `N₀ ℓ`. Neither proposition is installed as a print or as an
assumption of the headline.

The comparison would give genuine finite images of the same classes with their norm and
precision transitions, once the required norm range and retained smoothing are supplied. To
assemble (K1), one still has to identify the cyclotomic and real quotients in the ambient group,
realize the factorization of the binary family's actual characters, identify the coinduced
coefficient module with its finite group-ring tensor, and instantiate the completed limit.
Finite degree-zero groups give the Mittag--Leffler input to the cited limit argument. The
uniform exponent must come from the fixed lattice map of (K4). The final nonvanishing comparison
is restriction of the same weighted trace to the signed deck sum; nonvanishing of the raw
unweighted `es.z m` alone cannot prove nonvanishing after specialization.

## Verification

VERIFIED: all five source files compiled with `lake env lean`. The scratch harnesses
printed axioms for all 26 new theorems; each uses only axioms from
`propext`, `Classical.choice` and `Quot.sound`. The result log and compiler outputs are
in `scratch/rc-appE-k1/`. The successful dependency builds and checks were serialized.
The initial dependency build bypassed serialization and was stopped; see the build audit
in the results log.

The citations to Kato and Nekovář above are the locators given by the manuscript and
the existing interface. The source of the wider untwisted norm and the arithmetic use of
the completed inverse-limit sequence were not independently verified here.
