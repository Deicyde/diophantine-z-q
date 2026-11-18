import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalCommon

/-!
# GenusOdd: the local statement `LocalFactorK` and the local polynomial identities

`LocalFactorK` (GLUE, standard, local) gives Mathlib's local polynomial of `E/K` at a prime `𝔭` of
a number field `K` above `p` in terms of the local polynomial `L_p(T) = 1 − a_p T + b_p T²` of `E/ℚ`
at `p` and the splitting type of `𝔭`:

* `N𝔭 = p`, `𝔭` unramified (`K_𝔭 = ℚ_p`): `L_𝔭(T) = L_p(T)`;
* `N𝔭 = p`, `E` good at `p` (any ramification): `L_𝔭(T) = L_p(T)`;
* `N𝔭 = p²`, `𝔭` unramified: `L_𝔭(T²) = L_p(T) L_p(−T)`, i.e. for good `p`
  `L_𝔭(T) = 1 − (a_p² − 2p) T + p² T²` (`#Ẽ(𝔽_{p²}) = p² + 1 − (a_p² − 2p)`).

`GoodReductionOffLevel` (introduced as GLUE): a prime not dividing the level of the newform of `E` is
a prime of good reduction (Carayol: the level is the conductor). **PROVED** from lane RC8's printed
leaf `ModularNewform` (`goodReductionOffLevel_of_modularNewform`, `LevelGood.lean`). Clauses 1 and 2
of `LocalFactorK` are PROVED (`LocalClauses.lean`); its third clause is the GLUE
`LocalFactorInert`.

The power-series identities used in the comparison of Euler factors are PROVED here
(`invC_comp_C_mul_X`, `invC_mul`, `invC_expand_two`, and the three local identities
`localIdentity_split`, `localIdentity_inert`, `localIdentity_ramified`), as is a consistency check
of the inert clause against Mathlib's possible shapes of a local polynomial
(`inertShape_consistent`).
-/

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

/-- **The Euler factor of `E/K` at a prime of `K`, in terms of `a_p` and the splitting type**
(GLUE; standard local facts, Silverman *AEC* VII.5 and V.2 / Washington §4.3, Tate's algorithm
under unramified base change). Let `E/ℚ` be elliptic, `K` a number field, `v` a place of `ℚ` with
`p = natGenerator v`, `𝔭` a prime of `K` with `p ∈ 𝔭`, `L_p = localPolyQ E v`, `L_𝔭 = localPolyK E 𝔭`
(Mathlib's local polynomials from minimal models over `ℚ_v`, `K_𝔭`).

1. If `N𝔭 = p` and `𝔭² ∤ p` then `K_𝔭 ≅ ℚ_p` as valued fields, so `L_𝔭 = L_p`.
2. If `N𝔭 = p` and `E` has good reduction at `p`, a minimal model over `ℤ_p` with unit discriminant
   stays minimal over `𝓞_𝔭` with the same reduction over the same residue field `𝔽_p`, so
   `L_𝔭 = L_p`.
3. If `N𝔭 = p²` and `𝔭² ∤ p` (`K_𝔭/ℚ_p` unramified quadratic), a minimal model stays minimal with the
   same reduction type; for good reduction `#Ẽ(𝔽_{p²}) = p² + 1 − (a_p² − 2p)` (Frobenius
   characteristic polynomial `T² − a_p T + p`, eigenvalues squared), split multiplicative stays
   split, non-split becomes split over `𝔽_{p²}`, additive stays additive. In each case
   `L_𝔭(T²) = L_p(T) L_p(−T)`.
`expand ℤ 2 L` is `L(T²)` and `L.comp (C (-1) * X)` is `L(−T)`. Status: clauses 1 and 2 PROVED
(`localFactorK_clause_split`, `localFactorK_clause_good`); clause 3 is `LocalFactorInert` (GLUE);
`localFactorK_of_inert`. -/
def LocalFactorK : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ)),
    𝔭 ∈ primesAbove K (Rat.HeightOneSpectrum.natGenerator v) →
      (Ideal.absNorm 𝔭.asIdeal = Rat.HeightOneSpectrum.natGenerator v →
        UnramifiedOver 𝔭 (Rat.HeightOneSpectrum.natGenerator v) →
        localPolyK E 𝔭 = localPolyQ E v) ∧
      (Ideal.absNorm 𝔭.asIdeal = Rat.HeightOneSpectrum.natGenerator v → GoodAt E v →
        localPolyK E 𝔭 = localPolyQ E v) ∧
      (Ideal.absNorm 𝔭.asIdeal = Rat.HeightOneSpectrum.natGenerator v ^ 2 →
        UnramifiedOver 𝔭 (Rat.HeightOneSpectrum.natGenerator v) →
        expand ℤ 2 (localPolyK E 𝔭) = localPolyQ E v * (localPolyQ E v).comp (C (-1) * X))

/-- **Good reduction off the level** (GLUE, textbook: Carayol, the level of the newform of `E` is
the conductor `N_E`, and `p ∤ N_E` exactly when `E` has good reduction at `p`; with the newform of
level `N_E` and no lower level, `newformLevel E = N_E`). If `p = natGenerator v` does not divide
`newformLevel E`, the minimal model of `E` over `ℚ_v` has good reduction. Status: **PROVED** from
`ModularNewform` (`goodReductionOffLevel_of_modularNewform`, `LevelGood.lean`). -/
def GoodReductionOffLevel : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (v : HeightOneSpectrum (𝓞 ℚ)),
    ¬ Rat.HeightOneSpectrum.natGenerator v ∣ newformLevel E → GoodAt E v

/-! ### Inverses of local polynomials as complex power series -/

/-- `1 / P(T)` as a complex power series (Mathlib's `invOfUnit P 1` mapped to `ℂ`). -/
def invC (P : Polynomial ℤ) : PowerSeries ℂ :=
  PowerSeries.map (Int.castRingHom ℂ) (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1)

/-- `P` as a complex power series. -/
def polyC (P : Polynomial ℤ) : PowerSeries ℂ :=
  PowerSeries.map (Int.castRingHom ℂ) (P : PowerSeries ℤ)

theorem polyC_mul (P Q : Polynomial ℤ) : polyC (P * Q) = polyC P * polyC Q := by
  simp [polyC]

theorem polyC_mul_invC {P : Polynomial ℤ} (hP : P.coeff 0 = 1) : polyC P * invC P = 1 := by
  rw [polyC, invC, ← map_mul, PowerSeries.mul_invOfUnit, map_one]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP]
  rfl

/-- Uniqueness of the inverse (PROVED). -/
theorem invC_eq_of_mul {P : Polynomial ℤ} (hP : P.coeff 0 = 1) {F : PowerSeries ℂ}
    (hF : polyC P * F = 1) : invC P = F := by
  have h := polyC_mul_invC hP
  calc invC P = invC P * (polyC P * F) := by rw [hF, mul_one]
    _ = (polyC P * invC P) * F := by ring
    _ = F := by rw [h, one_mul]

theorem invC_one : invC 1 = 1 :=
  invC_eq_of_mul (by simp) (by simp [polyC])

/-- `1/(PQ) = (1/P)(1/Q)` (PROVED). -/
theorem invC_mul {P Q : Polynomial ℤ} (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) :
    invC (P * Q) = invC P * invC Q := by
  have hPQ : (P * Q).coeff 0 = 1 := by rw [Polynomial.mul_coeff_zero, hP, hQ, one_mul]
  apply invC_eq_of_mul hPQ
  rw [polyC_mul]
  calc polyC P * polyC Q * (invC P * invC Q) = (polyC P * invC P) * (polyC Q * invC Q) := by ring
    _ = 1 := by rw [polyC_mul_invC hP, polyC_mul_invC hQ, one_mul]

theorem coeff_comp_C_mul_X (P : Polynomial ℤ) (ε : ℤ) (n : ℕ) :
    (P.comp (C ε * X)).coeff n = ε ^ n * P.coeff n := by
  rw [comp_C_mul_X_coeff, mul_comm]

theorem polyC_comp_C_mul_X (P : Polynomial ℤ) (ε : ℤ) :
    polyC (P.comp (C ε * X)) = PowerSeries.rescale (ε : ℂ) (polyC P) := by
  ext n
  simp only [polyC]
  rw [PowerSeries.coeff_map, PowerSeries.coeff_rescale, PowerSeries.coeff_map,
    Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_comp_C_mul_X]
  simp

/-- `1/P(εT)` is `1/P` rescaled by `ε` (PROVED). -/
theorem invC_comp_C_mul_X {P : Polynomial ℤ} (hP : P.coeff 0 = 1) (ε : ℤ) :
    invC (P.comp (C ε * X)) = PowerSeries.rescale (ε : ℂ) (invC P) := by
  have h0 : (P.comp (C ε * X)).coeff 0 = 1 := by rw [coeff_comp_C_mul_X, pow_zero, one_mul, hP]
  apply invC_eq_of_mul h0
  rw [polyC_comp_C_mul_X, ← map_mul, polyC_mul_invC hP, map_one]

theorem polyC_expand_two (P : Polynomial ℤ) :
    polyC (expand ℤ 2 P) = (polyC P).subst (PowerSeries.X ^ 2 : PowerSeries ℂ) := by
  ext n
  rw [PowerSeries.coeff_subst_X_pow two_ne_zero]
  simp only [polyC, PowerSeries.coeff_map, Polynomial.coeff_coe, coeff_expand two_pos]
  split_ifs <;> simp

/-- `1/P(T²)` is `1/P` at `T²` (PROVED). -/
theorem invC_expand_two {P : Polynomial ℤ} (hP : P.coeff 0 = 1) :
    invC (expand ℤ 2 P) = (invC P).subst (PowerSeries.X ^ 2 : PowerSeries ℂ) := by
  have h0 : (expand ℤ 2 P).coeff 0 = 1 := by
    rw [coeff_expand two_pos, ite_eq_left_iff.mpr (fun h => absurd (dvd_zero 2) h), Nat.zero_div, hP]
  apply invC_eq_of_mul h0
  have ha : PowerSeries.HasSubst (PowerSeries.X ^ 2 : PowerSeries ℂ) :=
    PowerSeries.HasSubst.X_pow two_ne_zero
  rw [polyC_expand_two, ← PowerSeries.subst_mul ha, polyC_mul_invC hP]
  rw [← PowerSeries.coe_substAlgHom ha, map_one]

/-! ### The local identities

For the rational prime `p` write `L = L_p(E)`; `ε₁ = χ_{d₁}(p)`, `ε₂ = χ_{d₂}(p)` are the twisting
signs. The Euler factor of `E^{(d)}` at `p ∤ d` is `1/L(χ_d(p) T)` (lane RC18), and `1` at `p ∣ d`
(additive reduction of the twist at a prime of good reduction of `E`). -/

/-- **Split `p`** (PROVED): two primes `𝔭, 𝔭̄` of norm `p` with `L_𝔭 = L_{𝔭̄} = L` and
`χ(𝔭) = χ(𝔭̄) = ε = ε₁ = ε₂`: `(1/L(εT))² = 1/L(ε₁T) · 1/L(ε₂T)`, i.e. the Euler factor
`(1 − ε a_p T + p T²)^{-2}`. -/
theorem localIdentity_split (F : PowerSeries ℂ) {ε ε₁ ε₂ : ℂ} (h₁ : ε₁ = ε) (h₂ : ε₂ = ε) :
    PowerSeries.rescale ε F * PowerSeries.rescale ε F =
      PowerSeries.rescale ε₁ F * PowerSeries.rescale ε₂ F := by
  rw [h₁, h₂]

/-- **Inert `p`** (PROVED): one prime of norm `p²`, `χ(𝔭) = 1`, `L_𝔭(T²) = L(T) L(−T)`, and
`{ε₁, ε₂} = {1, −1}`: `1/L_𝔭(T²) = 1/L(ε₁T) · 1/L(ε₂T)`, i.e.
`(1 − (a_p² − 2p) T² + p² T⁴)^{-1} = (1 − a_p T + p T²)^{-1} (1 + a_p T + p T²)^{-1}`. -/
theorem localIdentity_inert {L Lp : Polynomial ℤ} (hL : Lp.coeff 0 = 1)
    (hexp : expand ℤ 2 L = Lp * Lp.comp (C (-1) * X)) {ε₁ ε₂ : ℤ}
    (hε : (ε₁ = 1 ∧ ε₂ = -1) ∨ (ε₁ = -1 ∧ ε₂ = 1)) :
    (invC L).subst (PowerSeries.X ^ 2 : PowerSeries ℂ) =
      PowerSeries.rescale (ε₁ : ℂ) (invC Lp) * PowerSeries.rescale (ε₂ : ℂ) (invC Lp) := by
  have hL0 : L.coeff 0 = 1 := by
    have h := congrArg (fun P : Polynomial ℤ => P.coeff 0) hexp
    simp only [coeff_expand two_pos, ite_eq_left_iff.mpr (fun h => absurd (dvd_zero 2) h), Nat.zero_div, Polynomial.mul_coeff_zero,
      coeff_comp_C_mul_X, pow_zero, one_mul, hL] at h
    simpa using h
  have hc : (Lp.comp (C (-1) * X)).coeff 0 = 1 := by
    rw [coeff_comp_C_mul_X, pow_zero, one_mul, hL]
  rw [← invC_expand_two hL0, hexp, invC_mul hL hc, invC_comp_C_mul_X hL]
  rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [PowerSeries.rescale_one]
  · simp [PowerSeries.rescale_one, mul_comm]

/-- **Ramified `p`** (PROVED): one prime of norm `p`, `L_𝔭 = L` (good reduction), `p` divides
exactly one of `d₁, d₂` (that twist has factor `1`), and `χ(𝔭)` is the sign `ε` of the other:
`1/L(εT) = 1/L(εT) · 1`. -/
theorem localIdentity_ramified (F : PowerSeries ℂ) (ε : ℂ) :
    PowerSeries.rescale ε F = PowerSeries.rescale ε F * 1 ∧
      PowerSeries.rescale ε F = 1 * PowerSeries.rescale ε F := by
  simp

/-! ### Consistency of the inert clause (LESSON 2)

Mathlib's local polynomial over `ℚ_p` has one of the shapes `1 − aT + pT²` (good), `1 − T`, `1 + T`,
`1`. For each, `L(T) L(−T)` is `Q(T²)` with `Q` again of one of Mathlib's shapes, now with `p²` in
place of `p`: `1 − (a² − 2p) T + p² T²`, `1 − T`, `1 − T`, `1`. So the third clause of
`LocalFactorK` never forces a polynomial that Mathlib's definition cannot produce. -/

/-- **The inert clause has a solution of Mathlib's shape** (PROVED). -/
theorem inertShape_consistent (a b : ℤ) :
    expand ℤ 2 (1 - C (a ^ 2 - 2 * b) * X + C (b ^ 2) * X ^ 2) =
      (1 - C a * X + C b * X ^ 2) * (1 - C a * X + C b * X ^ 2).comp (C (-1) * X) ∧
    expand ℤ 2 ((1 : Polynomial ℤ) - X) = (1 - X) * ((1 : Polynomial ℤ) - X).comp (C (-1) * X) ∧
    expand ℤ 2 ((1 : Polynomial ℤ) - X) = (1 + X) * ((1 : Polynomial ℤ) + X).comp (C (-1) * X) ∧
    expand ℤ 2 (1 : Polynomial ℤ) = 1 * (1 : Polynomial ℤ).comp (C (-1) * X) := by
  have hC : C (a ^ 2 - 2 * b) = C a ^ 2 - 2 * C b := by
    rw [C_sub, C_mul, C_pow]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hC]
    simp only [map_sub, map_add, map_mul, map_one, expand_C, expand_X, map_pow, map_ofNat,
      sub_comp, add_comp, mul_comp, one_comp, C_comp, X_comp, pow_comp, C_neg, C_1]
    ring
  · simp only [map_sub, map_one, expand_X, sub_comp, one_comp, X_comp, mul_comp, C_comp, C_neg,
      C_1]
    ring
  · simp only [map_sub, map_one, expand_X, add_comp, one_comp, X_comp, mul_comp, C_comp, C_neg,
      C_1]
    ring
  · simp

end ZInQ.Contrib.CloudB3RC53.GenusOdd
