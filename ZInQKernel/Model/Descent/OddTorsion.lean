import ZInQKernel.Model.Descent.PointCounts
import ZInQKernel.Model.Descent.Reduction

/-!
# No odd torsion in `E(K₀)`

Blueprint: `model/descent/torsion.md` (odd part), via `model/descent/reduction-torsion.md`.

The primes `π₁₇ = 5 + 2s` (norm `17`, `s ↦ 6`) and `π₂₃ = 5 - s` (norm `23`, `s ↦ 5`) of `ℤ[s]`
give reductions of `E : y² = x³ - d² x` to `y² = x³ - 8x` over `𝔽₁₇` (`20` points) and
`y² = x³ - 13x` over `𝔽₂₃` (`24` points). A point of odd prime order `q` reduces to a point of
order `q` at a prime `p ∈ {17, 23}` with `q ≠ p`, so `q ∣ 20` or `q ∣ 24`; choosing `p = 23` for
`q ∈ {5, 17}` and `p = 17` otherwise, this is impossible.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

/-! ### The primes above `17` and `23` -/

/-- `π₁₇ = 5 + 2s`. -/
def pi17 : Zs := ⟨5, 2⟩
/-- `π₂₃ = 5 - s`. -/
def pi23 : Zs := ⟨5, -1⟩

theorem prime_pi17 : Prime pi17 :=
  Zs.prime_of_natAbs_norm_prime (by rw [Zs.norm_eq]; simp [pi17]; norm_num)

theorem prime_pi23 : Prime pi23 :=
  Zs.prime_of_natAbs_norm_prime (by rw [Zs.norm_eq]; simp [pi23]; norm_num)

theorem six_mul_six_ZMod17 : (6 : ZMod 17) * 6 = (2 : ℤ) • 1 + (0 : ℤ) • 6 := by decide
theorem five_mul_five_ZMod23 : (5 : ZMod 23) * 5 = (2 : ℤ) • 1 + (0 : ℤ) • 5 := by decide

/-- `ℤ[s] → 𝔽₁₇`, `a + b s ↦ a + 6b`. -/
def rho17 : Zs →+* ZMod 17 := (QuadraticAlgebra.lift ⟨6, six_mul_six_ZMod17⟩).toRingHom
/-- `ℤ[s] → 𝔽₂₃`, `a + b s ↦ a + 5b`. -/
def rho23 : Zs →+* ZMod 23 := (QuadraticAlgebra.lift ⟨5, five_mul_five_ZMod23⟩).toRingHom

@[simp] theorem rho17_apply (z : Zs) : rho17 z = (z.re : ZMod 17) + (z.im : ZMod 17) * 6 := by
  simp [rho17, zsmul_eq_mul]

@[simp] theorem rho23_apply (z : Zs) : rho23 z = (z.re : ZMod 23) + (z.im : ZMod 23) * 5 := by
  simp [rho23, zsmul_eq_mul]

theorem rho17_eq_zero_iff (z : Zs) : rho17 z = 0 ↔ pi17 ∣ z := by
  constructor
  · intro h
    rw [rho17_apply] at h
    have h17 : ((17 : ℕ) : ℤ) ∣ z.re + z.im * 6 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 17).mp (by push_cast; exact h)
    obtain ⟨k, hk⟩ := h17
    push_cast at hk
    refine ⟨⟨5, -2⟩ * (k : Zs) + (z.im : Zs) * ⟨-2, 1⟩, ?_⟩
    ext <;> simp [pi17] <;> linarith
  · rintro ⟨c, rfl⟩
    rw [map_mul]
    have : rho17 pi17 = 0 := by rw [rho17_apply]; decide
    rw [this, zero_mul]

theorem rho23_eq_zero_iff (z : Zs) : rho23 z = 0 ↔ pi23 ∣ z := by
  constructor
  · intro h
    rw [rho23_apply] at h
    have h23 : ((23 : ℕ) : ℤ) ∣ z.re + z.im * 5 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 23).mp (by push_cast; exact h)
    obtain ⟨k, hk⟩ := h23
    push_cast at hk
    refine ⟨⟨5, 1⟩ * (k : Zs) - (z.im : Zs), ?_⟩
    ext <;> simp [pi23]; linarith
  · rintro ⟨c, rfl⟩
    rw [map_mul]
    have : rho23 pi23 = 0 := by rw [rho23_apply]; decide
    rw [this, zero_mul]

/-! ### The reductions of `E` -/

theorem neg_genD_sq_eq_toK0 : -genD ^ 2 = Zs.toK0 (-genDZ ^ 2) := by
  rw [map_neg, map_pow, toK0_genDZ]

theorem vge_neg_genD_sq (π : Zs) (hπ : Prime π) : VGe π 0 (-genD ^ 2) := by
  rw [neg_genD_sq_eq_toK0]; exact vge_toK0 hπ _

theorem res17_neg_genD_sq : res pi17 rho17 (-genD ^ 2) = -8 := by
  rw [neg_genD_sq_eq_toK0, res_toK0 prime_pi17 rho17 rho17_eq_zero_iff, map_neg, map_pow,
    rho17_apply]
  decide

theorem res23_neg_genD_sq : res pi23 rho23 (-genD ^ 2) = -13 := by
  rw [neg_genD_sq_eq_toK0, res_toK0 prime_pi23 rho23 rho23_eq_zero_iff, map_neg, map_pow,
    rho23_apply]
  decide

/-- A point of `E(K₀)` of prime order `q ≠ 17` has `q ∣ 20`. -/
theorem prime_dvd_20 {P : (shortCurve (-genD ^ 2)).toAffine.Point} {q : ℕ} (hq : q.Prime)
    (hq17 : q ≠ 17) (hP : addOrderOf P = q) : q ∣ 20 := by
  have hfin : IsOfFinAddOrder P := by
    rw [← addOrderOf_pos_iff, hP]; exact hq.pos
  have hp : ¬17 ∣ addOrderOf P := by
    rw [hP]; intro h
    exact hq17 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp h).symm
  have := addOrderOf_red prime_pi17 rho17 rho17_eq_zero_iff (vge_neg_genD_sq _ prime_pi17)
    res17_neg_genD_sq hfin hp
  rw [hP] at this
  rw [← this, ← card_point_17]
  exact addOrderOf_dvd_natCard _

/-- A point of `E(K₀)` of prime order `q ≠ 23` has `q ∣ 24`. -/
theorem prime_dvd_24 {P : (shortCurve (-genD ^ 2)).toAffine.Point} {q : ℕ} (hq : q.Prime)
    (hq23 : q ≠ 23) (hP : addOrderOf P = q) : q ∣ 24 := by
  have hfin : IsOfFinAddOrder P := by
    rw [← addOrderOf_pos_iff, hP]; exact hq.pos
  have hp : ¬23 ∣ addOrderOf P := by
    rw [hP]; intro h
    exact hq23 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp h).symm
  have := addOrderOf_red prime_pi23 rho23 rho23_eq_zero_iff (vge_neg_genD_sq _ prime_pi23)
    res23_neg_genD_sq hfin hp
  rw [hP] at this
  rw [← this, ← card_point_23]
  exact addOrderOf_dvd_natCard _

/-- `E(K₀)` has no point of odd prime order. -/
theorem odd_prime_torsion_E (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (P : genCurve.toAffine.Point)
    (h : q • P = 0) : P = 0 := by
  let P' : (shortCurve (-genD ^ 2)).toAffine.Point := P
  have h' : q • P' = 0 := h
  show P' = 0
  by_contra hP
  have : Fact q.Prime := ⟨hq⟩
  have hord : addOrderOf P' = q := addOrderOf_eq_prime h' hP
  by_cases hq5 : q = 5 ∨ q = 17
  · have hdvd := prime_dvd_24 hq (by omega) hord
    rcases hq5 with rfl | rfl <;> norm_num at hdvd
  · have hdvd := prime_dvd_20 hq (by omega) hord
    have h20 : q ∣ 2 ^ 2 * 5 := by norm_num; exact hdvd
    rcases (Nat.Prime.dvd_mul hq).mp h20 with h1 | h1
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h1))
    · exact hq5 (Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).mp h1))

end ZInQ
