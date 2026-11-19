**Result.** The rectangular extension is injective. On the rational finite adèles, the product phase gives the upper generator and the Haar Fourier integral with the finite determinant normalization gives the Fourier generator, on and off the dual. Both identities hold for every table and specialize to \(Q_B/m\) and \(Q_0\) in their rectangular coordinates. The common normalized lifts and the two index product formulas then give the two `IntertwinesGenerators` instances with the same \(\mu\). The transport to the weighted table is proved for each lifted eigenpair. The actual local Weil operator model and the stage eigenpair remain inputs.

In Lean the two equations prior to the Weil scalar are
\[
J_a(T_n v)(x)=\mathbf e_f(-nQ(x))\,J_a(v)(x),\qquad
J_a(F v)(y)=\int J_a(v)(x)\,\mathbf e_f(B_Q(x,y))\,dx_Q .
\]
The first right side is the finite product from `adelic_phase`. In the second, the right side is zero off the polar dual even though the integral is over the whole adèlic space. For the inverse lifts, multiplication by the archimedean index cancels the finite Weyl index, and the translation scalar is one.

Write \(L=\widehat{\mathbb Z}^{\,3}\) in coordinates divided by the nonzero lattice step \(h\), and \(d_i=2a_i\), \(D=\prod_i d_i\). Then \(Q=\sum_i a_ix_i^2\) in those coordinates. In the original coordinates the coset center is \(h r_i/d_i\). The Haar determinant multiplier in rectangular coordinates is \(\prod_p\sqrt{|D|_p}=D^{-1/2}\). Equivalently, locally in the original coordinates \(\sqrt{|D/h^6|_p}\) multiplies a coordinate lattice volume of \(|h|_p^3\). The lifted upper generator at \(-n\) and the lifted Weyl with kernel \(\mathbf e_p(B_Q)\) give the positive phase and the negative discriminant pairing, respectively.

For the phase, if \(x_i=r_i/d_i+t_i\) with \(t_i\in\widehat{\mathbb Z}\), then \(Q(x)-Q(r/d)=\sum_i(a_it_i^2+r_it_i)\in\widehat{\mathbb Z}\). The rational representative gives \(\mathbf e_\infty(nQ(r/d))\) at finite argument \(-nQ(x)\). For the Fourier transform, the kernel on \(L\) is trivial exactly when \(d_i y_i\in\widehat{\mathbb Z}\) for all \(i\), including at two. Translating each coset to \(L\) gives zero off this dual, and on the dual it gives \(D^{-1/2}\) times the character at the two rational centers. This calculation uses neither the congruence subgroup nor the stage characters.

## Statements

All seven Lean files pass `lake env lean`. Each of the 53 new theorems has a `#print axioms` audit listing only `propext`, `Classical.choice` and `Quot.sound` or a subset. Names below are in `ZInQ.Manuscript.RC.Intertwine`. Rational representatives, prime factorization, quotient bookkeeping and the transport bookkeeping are on-the-spot (c).

| Theorem | Statement and role |
| --- | --- |
| `rationalPhase_add`, `rationalPhase_eq_one`, `rationalPhase_congr` | The negative rational exponential is additive into multiplication, has kernel \(\mathbb Z\), and depends only on a rational residue modulo \(\mathbb Z\). Phase and Fourier kernels. |
| `finitePhase_spec`, `finitePhase_add`, `finitePhase_eq_one`, `finitePhase_eq_product` | Evaluate the quotient character using any rational representative. It multiplies under addition, has the integral subring as kernel, and gives a product of rational phases when a finite sum represents its argument. Phase and Fourier kernels. |
| `center_mul`, `coset_dual` | \(d_i\) times a coordinate of the center is its integer representative; the entire translated lattice is in the polar dual. Geometry for both identities. |
| `phase_on_coset`, `annihilator_iff`, `pairing_on_coset` | On an occupied coset \(U(-n)\) is the literal finite twist. The polar character on the rectangular lattice is trivial exactly on its dual; there the translated-center phase is the negative product of the standard discriminant characters. |
| `rat_mem_at`, `diagonal_apply`, `rational_integral` | A rational is integral at a prime not dividing its denominator, the diagonal map evaluates by that rational at each prime, and a rational integral at all places is an integer. Arithmetic for the character. |
| `exists_local_fraction`, `prime_fraction_integral_elsewhere`, `localFraction_spec`, `localFraction_elsewhere` | Each local argument has a \(p\)-power-denominator fraction in \([0,1)\) modulo \(\mathbb Z_p\). This fraction is integral away from \(p\); the chosen fraction has both congruence properties. |
| `sum_localFraction_spec`, `rationalFiniteModel`, `finitePhase_local_product` | Summing the local fractions gives one rational representative on the restricted product. This constructs the arithmetic model and identifies its character as the product over the finitely many relevant places. |
| `coset_exists`, `coset_unique`, `residue_eq_some`, `residue_eq_none` | The cosets represent the entire dual uniquely; the residue map returns exactly the label of the coset or none off the dual. |
| `J_injective`, `J_twist` | The extension is injective and it sends the literal grid twist to multiplication by \(U(-n)\). |
| `polar_add`, `lattice_integral`, `integrable_coset`, `integrate_coset` | The polar argument is additive. The lattice character integrates to the volume on the dual and to zero elsewhere. Integrability survives translation to a coset, and the integral acquires precisely the center phase. |
| `J_mul_character`, `J_fourier` | The Fourier integrand is a finite sum over cosets. A normalized additive invariant measure makes the Haar Fourier integral on the extension agree everywhere with the extended grid Fourier transform. |
| `product_localNorm`, `localNorm_good`, `finiteVolume_eq` | The local determinant norms multiply to \(D^{-1}\), are one at the good primes, and their square roots give the literal complex grid Fourier coefficient. |
| `common_weyl_scalar`, `comparison` | Equal real indices and product one force equal finite Weil scalars. For actions given by the normalized Haar and phase operators, the two grid identities hold with \(\mu(S)=\gamma_\infty\), \(\mu(T_n)=1\). |
| `weighted_table_of_common_comparison` | For a single word, the common lift eigenpair gives both table equations with common reference scalar \(\lambda\prod_s\mu(s)\) and the specified old-character ratio. |
| `integralAdeles_open`, `integralAdeles_compact`, `rectangular_eq_pi`, `rectangular_open`, `rectangular_compact` | The integral adèles and their threefold rectangular product are compact open; the latter is the product of the three integral subgroups. Haar measure input. |
| `normalizedHaar_volume`, `continuous_finitePhase`, `integrable_latticeCharacter` | The scaled Haar measure has the exact coset volume. The finite character is continuous, and the lattice indicator times the character is integrable. |
| `adelic_annihilator_placewise` | The annihilator criterion is the local integral condition on \(d_i y_{p,i}\) at every prime and in every coordinate, including at two. |
| `adelic_fourier`, `adelic_phase`, `adelic_comparison`, `adelic_pair_comparison` | On the rational finite adèles, the normalized integral and the product of phases give the two generators. For a representation with those operator descriptions, this gives `IntertwinesGenerators` and injectivity, using the common lift and scalar for \(a\) and `referenceForm`. |

The only new structure used as a hypothesis is `IntegralModel I` (tex 8640–8642): rational elements of the integral subring are exactly integers, and every element is congruent to a rational modulo that subring. It supplies only rational congruences even when no Weil action has been specified; in particular it contains no lattice, quadratic form, operator, or eigenvector. For the rational finite adèles it is proved, rather than supplied as a remaining input. The generic measure hypotheses are additive invariance, measurability of the lattice, integrability of its bounded character, and its volume. They contain no Fourier comparison and are discharged by the concrete Haar model. In the model transport, evaluating a lifted generator as an integral or pointwise phase is an operator description on functions: it has no finite Fourier matrix, rectangular-grid identities, or character ratio. The eigenpair input at one word is read only in the transport step.

## Remaining hypotheses

The proved operator comparison uses Haar measure on the restricted product of the \(\mathbb Q_p\), normalized on \(L\) by the finite product of the prescribed local determinant factors. If an independently constructed restricted product of the local self-dual measures \(\nu_f\) is used to implement the Weyl operator, the smallest measure check needed in rectangular coordinates is
\[
\nu_f(L)=\operatorname{ofReal}(\texttt{finiteVolume}(a)).
\]
Here \(L\) is the single cylinder \(\prod_p\mathbb Z_p^3\); the right side is \(\prod_p\sqrt{|D|_p}\). This is a volume identity on one compact open subgroup (tex 8647, 8649–8650, 9004–9007), and needs only the cylinder normalization once a restricted product measure is defined. For a translation invariant measure finite on compacts, this suffices in `J_fourier` by translation and finite summation. No comparison on arbitrary measurable sets is needed. The separate restricted product of Weil operators has to act on the supplied class functions and agree with its stated generator descriptions; it is not constructed in this lane.

In `adelic_pair_comparison`, one uses \(a\) and `referenceForm` with the same inverse lifts, \(\mu(S)=\gamma_\infty\) and \(\mu(T_n)=1\). With the resulting comparisons, apply `weighted_table_of_common_comparison` to `stageGridWeight E ι a h` and an old-level word.

| Hypothesis | Exact content, manuscript lines, and owner |
| --- | --- |
| Input vectors and rectangular presentation | `StageGrid` for the fixed-sieved weight, including the given norm scaling, support and coset constancy; identify the resulting table extension with the class weights used by the local operators. Tex 8495–8604, 8665–8675, 8968–8976, 9021–9026, 9471–9479. **Sibling lane:** weight and PMLocal construction. |
| Model of the lifts | Use the same lifts of \(S^{-1}\) and \(T^{-n}\) in both representations, projecting to the indicated inverse generators. On the function model they act by \(U_Q(-n)\) and \((\prod_p\gamma_p(Q))\mathcal F_{Q,f}\); the reference uses its own \(Q_0\) but the same lifts. Central kernel acts by the same signs. Tex 8726–8807, 8996–9004. **Missing theory:** normalized local operator instances and their restricted product (several modules); actual Weil indices are out of scope. |
| Index normalization | \(\gamma_\infty(Q)=\gamma_\infty(Q_0)\) for the two positive ternary forms, and \(\gamma_\infty(Q)\prod_p\gamma_p(Q)=1\), likewise for \(Q_0\). These are scalar inputs; the one-place `WeilIndexAxioms` does not imply the global product formula. Tex 8731–8738, 8801–8807, 9000–9011. **Missing theory:** instantiate the existing Weil index data and the cited product formula. |
| Classwise depth and unit scaling | For each prescribed place and each fixed-sieved class, invariance by an open translation lattice \(L'_p\), \(p^{v_p(N_0)}Q((L'_p)^\vee)\subseteq\mathbb Z_p\), and \(f_p(ux)=\alpha_p(u)f_p(x)\) for units, with conductor at most the old depth. Include two and \(\alpha_p(-1)\) (the global character is even). Tex 8512–8515, 8525–8534, 8546–8556, 8571–8593, 8654–8685, 8837–8847, 8869–8884, 8925–8936, 9030–9036, 9471–9479. **Sibling lane:** local weights and scaling. **ELLIOT input:** match their depths to the specified old level, with no enlargement. |
| Spherical and class identifications | At each place outside the prescribed support, the entire integral local group fixes the reference and the identified class weight in compatible lifts; class isometries preserve the form and commute with the normalized operators. This includes good places where \(d\) is not a unit. Tex 8884–8886, 8938–8951, 8972–8976, 9030–9036. **Sibling lane:** class weights and lattices; **missing theory:** actual local operator model. |
| Character identifications | In the old character the ratio on positive representatives is \(\xi(d)=\prod_p\alpha_p(d)(m/d)\). Identify the individual odd and dyadic Hilbert contributions as in tex 8891–8915; use the conductors to descend to signed unit residues at the actual old level. The first input of `oldStageLaw_of_finiteAction` also needs `ξ.comp (ZMod.unitsMap Dₗ.old_dvd) = (Units.map κ).comp (bCharacter C ∅)`. Tex 8891–8936, 8978–8986, 9012–9015. **Missing theory:** individual local symbol values. **ELLIOT input:** identify the fixed-pool character at the chosen computational level. |

For a word with matrix in \(\Gamma_0(N_0)\), factor its inverse at prescribed places and use spherical invariance elsewhere. Multiply the class eigenvalues and sum the mass-weighted classes by linearity. The common comparison then transports the two lifted eigen-equations to the two tables with the same generator scalar product. This would give the literal `RelativeFiniteAction` at \(N_0\), consumed by `oldStageLaw_of_finiteAction`.

## Known issues

- The finite branch base does not contain the PMLocal construction. A spherewise finite support or the good-prime frame equation does not prove the fixed-sieved translation depth.
- Weil I.13–I.14, II.25–II.30 and III.41, Theorem 6 are manuscript locators and independently **UNVERIFIED** here. No new printed leaves.
- No manuscript error identified in this comparison.

## Manuscript check

- Tex 8495–8604, 8665–8675 and 9471–9479 — **unverified**: the class presentation and translation depth of the actual fixed-sieved weights are supplied separately.
- Tex 8640–8642 — **gap filled**: the rational finite character is computed as a finite product of negative local fractional-part characters, including the rational diagonal evaluation.
- Tex 8643–8647 — **gap filled**: the diagonal polar form determines the rectangular dual and the finite kernel, with the positive polar argument used at finite places.
- Tex 8649–8657 — **gap filled**: Haar translation makes each lattice integral vanish off the annihilator; its value on the annihilator is the normalized coset volume.
- Tex 8658–8685 and 8817–8936 — **unverified**: the specializations of class depth, unit scaling and Hilbert symbols at the old level still need the local inputs.
- Tex 8726–8807 — **unverified**: the normalized operator formulas on a common cover are the remaining operator model; the rectangular calculation evaluates their displayed phase and Fourier operators.
- Tex 8938–8951 and 8972–8976 — **unverified**: the good-prime and class isometry instances still need to be supplied.
- Tex 8996–8999, 9012–9015 — **OK**: the inherited inverse-word transport uses the inverse generators in reverse order and evaluates the stage character at the lower-right entry.
- Tex 9000–9004 and 9008–9011 — **unverified**: the equal real Weil index and global index products are used as scalar inputs; full adèlic theta invariance is not needed for the table comparison.
- Tex 9004–9007 and 9027–9029 — **gap filled**: for the rectangular polar determinant the finite product of measure factors equals the finite Fourier normalization.
- Tex 9021–9026 — **OK**: the comparison uses the supplied form after extraction and does not put a measure factor in any table coefficient.
- Tex 9030–9036 — **unverified**: the actual support, depth and character identifications after extraction are separate from the rectangular calculations.
