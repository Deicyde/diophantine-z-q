# model-descent report

Task: the two-isogeny descent, torsion and rank of `E(K₀)` (blueprint `model/descent/`, all
articles except `coordinate-change.md` and `point-r-certificate.md`).
Root module `ZInQKernel/Model/Descent.lean` (imported from `ZInQKernel.lean`); modules in
`ZInQKernel/Model/Descent/`. All 13 leaves are proved, with no `sorry`, no `native_decide` and no
axioms. `#print axioms` on the main results gives only `propext, Classical.choice, Quot.sound`.
The finite computations (point counts mod 17 and 23, residues, the order-8 table) are `decide`.

**Main result: `ZInQ.mordellWeilE : MordellWeilE`** (`Descent/MordellWeil.lean`). Hypothesis MW
of the main theorem is now a theorem.

## Status

| article | Lean name(s) | status |
| --- | --- | --- |
| model/descent/kummer-map.md | `Descent.SqClass`, `Descent.SqClass.mk`, `Descent.sqc`, `Descent.kummer`, `Descent.phi`, `Descent.phi_equation`, `Descent.rescale`, `Descent.tZero` (Kummer.lean) | proved |
| model/descent/kummer-homomorphism.md | `Descent.kummer_add`, `Descent.kummerHom`, `Descent.kummer_neg`, `Descent.kummer_nsmul`, `Descent.kummer_zsmul`, `Descent.kummer_two_nsmul` | proved |
| model/descent/kummer-kernel.md | `Descent.kummer_eq_one_iff` | proved |
| model/descent/isogeny-doubling.md | `Descent.rescale_phi_phi`; for `E`: `phiHatE_phiE` (Index.lean) | proved |
| model/descent/first-descent-image.md | `kummer_range_E`, `card_kummer_range_E`, `descentGroup`, `card_descentGroup`, `descentGroup_eq` (the eight classes), `kummer_genT0`, `kummer_genTd`, `kummer_genTnegd`, `kummer_theta_symm_pointR` (FirstImage.lean) | proved |
| model/descent/second-descent-image.md | `kummer_E'_trivial` (SecondImage.lean) | proved |
| model/descent/descent-index.md | `index_two_E`, `index_two_genCurve`, `two_smul_range_eq_ker`, `mem_two_smul_iff_kummer_eq_one`, `kummer_range_eq_descentGroup`, `phiE_surjective`, `kummer_eq_one_iff_mem_range_phiHatE`, instance `finiteIndex_two_E` (Index.lean) | proved |
| model/descent/reduction-point-counts.md | `pointCounts_17_23` (`decide`), `pointCount_17`, `pointCount_23`, `card_point_shortCurve`, `card_point_17`, `card_point_23` (PointCounts.lean) | proved |
| model/descent/reduction-torsion.md | `red`, `redHom`, `red_add` (part 1), `eq_zero_of_red_eq_zero` (part 2), `addOrderOf_red`, `red_injOn_of_coprime`, `card_dvd_of_coprime` (Reduction.lean) | proved |
| model/descent/torsion.md | `two_nsmul_eq_zero_of_isOfFinAddOrder`, `isOfFinAddOrder_iff_two_nsmul_eq_zero`, `mem_torsion_E_iff`, `mem_torsion_C_iff`, `two_nsmul_eq_zero_of_isOfFinAddOrder_C` (Torsion.lean), `odd_prime_torsion_E` (OddTorsion.lean), `card_torsion_E`, `card_torsion_C` (RankOne.lean) | proved |
| model/descent/rank-one.md | `exists_generator_C (hMW)`, `exists_generator_E (hMW)`, `exists_generator_C'` (without hypothesis) (RankOne.lean) | proved |
| model/descent/odd-free-index.md | `odd_free_index` (OddIndex.lean) | proved |
| model/descent/mordell-weil-from-descent.md | `mordellWeilE : MordellWeilE` (MordellWeil.lean) | proved |

Also proved: the Kummer clause of `coordinate-change.md`, which model-field left open,
`α_{-δ²}(θ P) = α_{-d²}(P)`: `kummer_theta` (FirstImage.lean), from the generic
`Descent.kummer_scaleEquiv` (Kummer.lean).

## Statement corrections and choices

- **kummer-map.** `E_b` is model-field's `shortCurve b`. The notes' `curveB` would unfold to the
  same structure, so it was not introduced. Ellipticity is an instance argument
  `[(shortCurve b).IsElliptic]`. It implies `2 ≠ 0` and `b ≠ 0`
  (`two_ne_zero_of_isElliptic`, `ne_zero_of_isElliptic`), so there are no separate `char ≠ 2`
  and `b ≠ 0` hypotheses. The targets of `φ_b` and `λ_b` are given by equations:
  `phi (hb' : b' = -4 * b) : E_b → E_{b'}` and `rescale (hb'' : b'' = 16 * b) : E_{b''} ≃+ E_b`.
  This avoids casts between `shortCurve (-4 * (-4 * b))` and `shortCurve (16 * b)`.
  `sqc x` is the class of `x`, with the junk value `sqc 0 = 1`. `SqClass K` is a `def` with its own
  `CommGroup` instance: as an `abbrev` of the quotient, `rw [mul_comm]` failed on it.
- **isogeny-doubling.** Stated as `rescale _ (phi hb'' (phi hb' P)) = 2 • P` with
  `hb' : b' = -4b` and `hb'' : b'' = -4b'`.
- **second-descent-image.** `E' = shortCurve (4 * genD ^ 2)`. In the index proof
  `φ : E → E'` uses `4d² = -4·(-d²)`, and the dual uses `E_{-16d²}` with `-16d² = -4·(4d²) = 16·(-d²)`.
- **descent-index.** Stated for `(shortCurve (-genD ^ 2)).toAffine.Point`, which is defeq to
  `genCurve.toAffine.Point`, with the `genCurve` form `index_two_genCurve`. The "more precisely"
  clause is `kummer_range_eq_descentGroup` (the range of `kummerHom` is `descentGroup`) together
  with `two_smul_range_eq_ker`.
- **reduction-torsion.** The data `(p, r)` are replaced by a prime element `π` of `ℤ[s]` and a ring
  homomorphism `ρ : ℤ[s] →+* ZMod p` with kernel `(π)` (`hρ : ∀ a, ρ a = 0 ↔ π ∣ a`), plus
  `[Fact p.Prime]`. The article's `ρ(a + bs) = a + br` has kernel `(p, s - r)`, which is principal
  because `ℤ[s]` is a PID, so the article's data give such a pair. For the two primes used here
  the pair is explicit: `pi17 = 5 + 2s` with `rho17 : s ↦ 6`, and `pi23 = 5 - s` with `rho23 : s ↦ 5`.
  Instead of `A ∈ ℤ[s]` the statement takes `A ∈ K₀` integral at `π` (`VGe π 0 A`) and
  `Ā = res A`. "`W̃` elliptic" is the instance `[(shortCurve Ā).IsElliptic]`, which encodes
  `p ≠ 2` and `Ā ≠ 0`. "`T` of finite order prime to `p`" in part 2 is `n • T = 0` with `π ∤ n`,
  equivalently `p ∤ n` (`dvd_natCast_iff`). The corollaries "injective on finite subgroups of
  order prime to `p`" and "the order divides `#W̃(𝔽_p)`" are `red_injOn_of_coprime` and
  `card_dvd_of_coprime`.
- **torsion.** The statement is unchanged; the proof differs in one step. The odd part follows the
  article (reduction at 17 and 23). The two-primary part does not use reduction (`8 ∤ 20`).
  Instead, a point of order 4 would give `T = 2P ∈ E[2] \ {O}` with `α(T) = 1`, but
  `α(T) ∈ {-1, d, -d}` and these are not squares (`two_nsmul_eq_zero_of_four_nsmul_eq_zero`).
  This is shorter given the descent index.
- **rank-one.** Stated as `∃ S, ¬IsOfFinAddOrder S ∧ ∀ P, ∃! mT : ℤ × {T // 2 • T = 0},
  P = mT.1 • S + mT.2`, under `hMW : MordellWeilE` as in the article. `exists_generator_C'`
  drops the hypothesis using `mordellWeilE`.
- **odd-free-index.** Proved for every `S ∈ C(K₀)` and every `T` with `2 • T = 0`, not only the
  generator of the rank-one theorem. The proof does not need that `S` is a generator.
- **first-descent-image.** "Pairwise distinct" follows from `card_descentGroup = 8` together with
  `descentGroup_eq`, which lists the eight classes. Distinctness comes from the invariant
  `sqcInvariant : K₀ˣ/K₀ˣ² →* ℤ/2 × signs`, `x ↦ (v_d(x) mod 2, sign vector)`.

## Lemmas added beyond the leaves

- `Factor.lean`: `Zs.eq_unit_mul_genD_pow_mul_sq` and `eq_unit_mul_genD_pow_mul_sq` (if `v_π(x)`
  is even for all `π ≁ d` then `x = u dᵉ z²`), `sqc_unit_mem`, `sqc_mem_closure_of_even`,
  `even_vp_or_of_curve` (on `y² = x³ + Bx` with `v_π(B)` even, `v_π(x)` is even or
  `2 v_π(x) = v_π(B)`), `exists_eq_div_of_vp_eq_zero`, `vp_sq_add_four_eq_zero` (the mod-7
  argument), `descentGroup` and its generators, `sqc_pow`.
- `FirstImage.lean`: `Descent.SqClass.lift`, `unitInvariant`, `sqcInvariant`, `descentParam`
  (`(ℤ/2)³ →* K₀ˣ/K₀ˣ²`), `descentParam_injective`, `kummerE`, `even_vp_x_E`, `kummer_theta`.
- `SecondImage.lean`: `totallyPositive_x_E'`, `even_vp_x_E'`, `vp_genDZ_x_E'_ne_one`, `vp_two_eq`.
- `Residue.lean`: `VGe π k x` (`v_π(x) ≥ k` with `v(0) = ∞`) and its algebra, the residue map
  `res π ρ : K₀ → 𝔽_p` on the local ring with `res_add`, `res_mul`, `res_div`,
  `res_eq_zero_iff`, `res_toK0`, `exists_rep_of_vge`.
- `KernelReduction.lean` (formal group): `vieta_shortCurve` (Vieta from Mathlib's
  `addPolynomial_slope`), `sum_t_identity`, `tw_equation`, `vge_chord_slope`,
  `vge_tangent_slope`, `kernel_tangent_line`, `kernel_chord_line`, `kernel_third_point`,
  `kernel_add` (addition estimate), `level_of_not_vge`, `tCoord`, `nsmul_ne_zero_of_not_vge`
  (the kernel of reduction has no torsion prime to `p`).
- `Reduction.lean`: `slope_mul_add`, `add_of_red_opp`, `red_add_of_not_opp`, `red_add_of_slope`,
  `kernel_add_kernel`, `red_add_kernel`, `red_neg`, `kernel_bounds`.
- `OddTorsion.lean`: `pi17`, `pi23`, `rho17`, `rho23`, `rho17_eq_zero_iff`, `rho23_eq_zero_iff`,
  `res17_neg_genD_sq = -8`, `res23_neg_genD_sq = -13`, `prime_dvd_20`, `prime_dvd_24`.
- `RankOne.lean`: index lemmas `index_nsmul_range_congr` (transport along `≃+`),
  `nsmul_range_prod`, `index_nsmul_range_pi_int` (`[ℤⁿ : kℤⁿ] = kⁿ`), `card_two_torsion_C`.
- `Kummer.lean`: `Descent.kummer_rescale`, `Descent.kummer_scaleEquiv`, `Descent.mul_addX_eq`
  (`x₁x₂x₃ = (y₁ - ℓx₁)²`), `Descent.kummer_add_tZero`.

## Problems

- **Instance mismatch between `genCurve` and `shortCurve (-genD ^ 2)`.** Points of `genCurve`
  carry `K0`'s `instCommRing`; lemmas about `shortCurve b` use `Field.toCommRing`. The types are
  defeq, but `rw` fails across them, for `+`, `•`, `0` and `kummer` applied to `genCurve`
  points. Workarounds: state results on `(shortCurve (-genD ^ 2)).toAffine.Point` and pass them
  to `genCurve` statements by `exact` (e.g. `index_two_genCurve := index_two_E`), use term-mode
  `Eq.trans` chains (`kummer_genT0`), or retype with `let P' : (shortCurve …).toAffine.Point := P`
  (`odd_prime_torsion_E`, `odd_free_index`). The same holds for `curveC`.
- Some `field_simp` normal forms are unpredictable, for example with a determinant
  `x₁y₂ - x₂y₁` in a denominator. Pattern used: `generalize hD : … = D` to make it an atom, then
  `field_simp` and `linear_combination hD`.
- `lake build ZInQKernel` passes. Its only `sorry` warning is in `ZInQKernel/Main.lean`, which
  belongs to another task.

## Suggestions for the next agent / the lead

- **The MW hypothesis can be dropped from the main theorem:**
  `ZInQ.exists_bounded_integer_polynomial_defining_integers_of` can be applied to
  `mordellWeilE`, or its signature changed. `FrozenTarget` is unaffected. Whether to do so is the
  lead's decision.
- The blueprint leaves of `model/descent/` can be marked done, together with the Kummer clause of
  `coordinate-change.md` (`kummer_theta`).
- For Proposition 3.1 (generator), the remaining input is that `R` (equivalently `P₀ = θ⁻¹(2R)`)
  generates modulo torsion. `exists_generator_C'` gives `C(K₀) = ℤS ⊕ C[2]` and `odd_free_index`
  gives `R = mS + T` with `m` odd. `m = ±1` still needs the height search, which is not in this
  task.
- The reduction machinery (`Reduction.lean`) is generic in the prime `π` and the integral `A`. It
  can be reused for other primes, e.g. the point counts in `GoodPatternPrime` of
  `Hypotheses/PrimePattern.lean`, which concern the same curve.
