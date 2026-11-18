# Appendix E: half-integral weight twist

`HalfIntegral.halfIntegralTwist` proves the exact `AppE.HalfIntegralTwist`
proposition. The twist is cuspidal at level `N³`, with the same prime
support as `N`, character `(ψ * ν ^ 2).changeLevel`, and coefficients
`ν(n) a_f(n)` for every index. The proof uses the tree's actual theta
ratio, holomorphy, and all-cusp condition (tex 8097–8102).
`HalfIntegral.evenPhaseData_Ecurve` supplies this theorem as `hTw` to
the existing Appendix E assembly.

## Known issues

The translation-conjugacy identity requires the deep congruence condition
used in the twist. Membership of both matrices in `Γ₀(4)` alone does not
suffice. For example, at denominator 2 and with both shifts equal to 1/2,
the matrix `[1,0;4,1]` is conjugate to `[3,-1;4,-1]`. The latter has the
same action on theta as the inverse of the former, followed by an integer
translation. The S and T² transformations give squared multipliers
`1 + 4z` and `1 - 4(z + 1/2)`, respectively, wherever the theta ratios
have nonzero denominators. This restriction concerns the general
conjugacy formulation, not the manuscript's assertion at a sufficiently
deep level.

The manuscript's primitive character prescription needs to be read together
with the deletion of coefficients on the nonunits of the original modulus.
The primitive sum alone can keep some of those coefficients, for example
for the principal character at a prime whose inducing conductor is 1.
The finite Fourier weights at the original modulus implement both operations
in one sum. No source locator is used for this proof, and there is no new
printed-form leaf.

## Proof and theorem statements

Write `T(t) = [1,t;0,1]`, `e_C(x) = exp(2πix/C)`, and
`Q_C(a,n) = Σ_x e_C(ax²+nx)` on `ℤ/Cℤ`. The Fourier weight
`w_v(u) = (1/N) Σ_x v(x)e_N(-ux)` gives
`F_v(z) = Σ_u w_v(u) f(z+u/N)`. The sums and the original cusp condition
are used as stated in the tree. Statements below are in
`ZInQ.Manuscript.RC.HalfIntegral`.

| Theorem | Statement and role |
| --- | --- |
| `ratShift_cast` | The rational representative `u.val/N` casts to the real translation parameter. |
| `sum_translationWeights` | `Σ_u w_v(u)e_N(un) = v(n)` for any function on `ℤ/Nℤ`. This gives the required coefficient multiplier. |
| `translationWeights_unit` | `w_ν(d⁻²u) = ν(d)² w_ν(u)` for every unit `d`. This supplies the extra character in the modular law. |
| `translationWeights_primitive` | For primitive `ν`, `w_ν(u) = G(ν⁻¹)⁻¹ ν⁻¹(u)` with the positive standard additive character. This is the manuscript's translation formula at the conductor. |
| `hasSum_translationSum` | From an everywhere convergent width-one series with coefficients `a(n)` for `f`, the sum `F_v` has the convergent series with coefficients `v(n)a(n)`. |
| `qExpansion_translationSum` | When the cusp function of `F_v` is analytic at zero, its width-one `qExpansion` has coefficient `v(n)a(n)` under that same series hypothesis. This gives the equality in `HalfIntegralTwist`. |
| `translationSum_principal_prime` | For the principal character mod a prime `p`, `F_1(z) = f(z) − (1/p) Σ_u f(z+u/p)`. |
| `dirichlet_apply_primitive_sieve` | `ν(n) = ν.primitiveCharacter(n)` if `n` is coprime to `N`, and `0` otherwise. |
| `translateMatrix_smul` | The rational matrix `T(t)` acts as real translation by `t`. |
| `ratTranslate_cuspidal` | If `f` satisfies the tree's weighted limit at every integral cusp representative for a given weight, so does `z ↦ f(z+t)` for each rational `t`. |
| `coe_rat_map_smul` | Mapping the entries of an integral matrix to the rationals preserves its action on the upper half-plane. |
| `exists_translation_conjugate` | For `γ ∈ Γ₀(N³)`, with `v=d²u` in `ℤ/Nℤ`, there is `δ ∈ Γ₀(N)` with lower right entry congruent to `d` mod `N` and `T(u/N)γ=δT(v/N)`, using the chosen residue representatives. |
| `translate_differentiableOn` | Real translation preserves holomorphy on the upper half-plane. |
| `translationSum_cuspidal` | Any finite sum `F_v` of the specified translates satisfies the same all-cusp limits as `f`. |
| `quadraticFourier_even` | If `ad=1` modulo `C`, then `Q_C(a,2n)=e_C(-dn²)Q_C(a,0)`. |
| `quadraticFourier_unit_sq` | For any unit `s` mod `C`, `Q_C(as²,0)=Q_C(a,0)`. |
| `quadraticFourier_translate` | If `C=4m²k` and `a` is a unit mod `C`, then `Q_C(a+4mku,0)=Q_C(a,0)`. |
| `quadraticFourier_odd` | `Q_C(a,n)=0` for `C=4k>0` and `n` odd. |
| `jacobiTheta_mul_add_one` | For `Im τ > 0`, `θ_J(τ)θ_J(τ+1)=θ_J(2τ+1)²`, where `θ_J` is Mathlib's `jacobiTheta`. |
| `jacobiTheta_ne_zero_of_im_pos` | For `Im τ > 0`, `θ_J(τ)≠0`. This permits cancellation in the tree's theta ratio. |
| `jacobiTheta_rational_resum` | For `C>0` and `Im τ>0`, `θ_J(2a/C + τ/C²) = (-iτ)^(-1/2) Σ_n Q_C(a,n) exp(πin²(-1/τ))`, with the complex power as in Mathlib's functional equation. |
| `jacobiTheta_at_cusp` | For `C=4k>0`, `ad≡1 mod C`, and `t=z/2+d/(2C)`, `θ_J(2a/C − 2/[C(Cz+d)]) = (-i(-1/t))^(-1/2) Q_C(a,0) θ_J(2z)` on the upper half-plane. |
| `theta_ratio_translate` | If `4m² ∣ c` and `T(u/m)γ=δT(v/m)` for integral determinant-one `γ,δ`, then the theta ratio of `δ` at `z+v/m` equals that of `γ` at `z`. |
| `thetaTranslationCompatibility` | The same identity for the tree's `thetaMultiplier`, as the proposition `ThetaTranslationCompatibility`. |
| `translationSum_isHalfIntegralWeightCuspForm` | If `w` is a function mod `N` and `w_w(d⁻²u)=ν(d)²w_w(u)` for all units `d`, the sum `F_w` is a weight-`3/2` cusp form at `N³` of character `(ψν²).changeLevel`, assuming the original cusp form and theta compatibility. |
| `halfIntegralTwist_of_thetaTranslationCompatibility` | The exact existing `HalfIntegralTwist` follows from `ThetaTranslationCompatibility`, with `M=N³` and `f'=F_ν`. |
| `halfIntegralTwist` | For `N>0` with `4 ∣ N`, characters `ψ,ν` mod `N`, and a weight-`3/2` cusp form `f` of character `ψ`, there are `M>0`, `N ∣ M`, with the same prime divisors, and a cusp form `f'` of character `(ψν²).changeLevel` with `a_f'(n)=ν(n)a_f(n)` for every natural `n`. Supplies `HalfIntegralTwist` to `AppE.twist_mem_eigenspace`. |
| `primitive_twist` | For primitive `ν` mod `r` with `r ∣ N`, its conductor sum `G(ν⁻¹)⁻¹ Σ_u ν⁻¹(u) f(z+u/r)` is cuspidal at `N³`, with character `(ψ (ν.changeLevel)²).changeLevel` and coefficients `ν(n)a_f(n)` at all indices, before the sieve at the original modulus. |
| `evenPhaseData_Ecurve` | With the hypotheses of `AppE.evenPhaseData_Ecurve` except `hTw`, there exists `P : EvenPhaseData (Ecurve ℓ) L σ D₀` with `P.retained = {D \| S0Filter (2 * N₀).primeFactors D₀ D}` and `P.z = phase P.N P.η D₀`. Discharges `hTw` by applying the existing theorem. |

Local proof lemmas:

- `qParam_residueShift`: translating by `u/N` multiplies the monomial `qⁿ` by `e_N(un)`.
- `rat_translate_cuspCoordinates`: for rational `t` and integral `α`, factor `T(t)α = βg` with integral `β` of determinant one and upper triangular real `g`.
- `exp_int_sq_pi`, `summable_theta_norm`: `exp(πin²)` is `1` for even `n` and `−1` for odd `n`; the upper-half-plane Gaussian is absolutely summable.
- `shiftedGaussian`, `pos_im_neg_inv`, `tsum_even_odd`: `Σ_n exp(πiτ(n+x)²) = (-iτ)^(-1/2) jacobiTheta₂ x (-1/τ)` for nonzero `τ`; the map `τ ↦ -1/τ` preserves positive imaginary part; an absolutely convergent integer sum splits into even and odd indices.
- `theta_pos_im`, `coe_sl_smul`: `2z` has positive imaginary part for `z ∈ ℍ`; the action is `(az+b)/(cz+d)`.
- `J_of_c_zero`, `J_at_cusp`: the ratio is `1` for `c=0`; for `c=C=4k>0` it is `(-i(-1/t))^(-1/2) Q_C(a,0)` with `t=z/2+d/(2C)`.
- `conjugate_entries`, `theta_conjugate_pos`: `T(t)γ=δT(s)` gives `c_δ=c`, `a_δ=a+tc`, `d_δ+cs=d`; with `c>0` and the deep divisibility condition these identities give the theta ratio comparison.

The Poisson computation, the theta nonvanishing proof, the matrix
congruence and holomorphy/cusp arguments, and the coefficient sieve are
on-the-spot (provenance (c)). The positive-denominator formula uses
Mathlib's two-variable theta functional equation, with its existing
complex-power branch. The argument compares the power at literally
equal inputs and compares the quadratic sum by changing variables.
The cases `c=0` and `c<0` use integer translation and negation of the
two matrices, respectively. For the primitive sum, the coefficient
function mod `N` is the primitive character composed with reduction mod
`r`. Its values on units give the character in the transformation
law. Equality of the two convergent Fourier series identifies the sum
at `N` with the normalized Gauss sum at `r`. Mathlib's
`MulChar.star_eq_inv` identifies the inverse character there with the
complex conjugate character.

## Manuscript check

| Tex lines | Step | Verdict |
| --- | --- | --- |
| 8097–8099 | The coefficientwise twist has character `ψν²`. | gap filled — reindexing by `u ↦ d²u` supplies the square of the twisting character. The preexisting `twist_mem_eigenspace` uses this modularity for the good eigenvalues. |
| 8100 | The level introduces no new primes. | gap filled — `N³` is divisible by `N` and `4N²` and has the prime divisors of `N`. |
| 8101–8102 | The finite translation sum is modular. | gap filled — the theta ratios agree at the integral conjugates and each translate satisfies the all-cusp condition. |
| 8101–8102 | The primitive sum is normalized by a Gauss sum. | OK — Fourier inversion gives the stated primitive normalization. |
| 8101–8102 | The primitive inducing character gives the twist at the original modulus. | gap filled — coefficients on nonunits of the original modulus must be deleted; Fourier inversion at that modulus does the deletion. |
| 8104–8106 | Pass to a common level and use the full good-Hecke eigenspace. | OK — the existing Appendix E argument applies with `HalfIntegralTwist` supplied. |

## Verification

All nine new Lean files compiled individually with `lake env lean`. Each
of the 42 theorem checks issued by `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. No proof or printed-form
statement in the existing Appendix E or its dependencies was edited.
