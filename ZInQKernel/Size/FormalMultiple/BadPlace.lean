import ZInQKernel.Size.FormalMultiple.Reduction
import ZInQKernel.Size.FormalMultiple.Congruences
import ZInQKernel.Model.Descent.OddTorsion

/-!
# Reduction of `P₀` at the bad place

Blueprint: `size/formal-multiple/bad-place-reduction.md`.

`E : y² = x³ + A x` with `A = -d²`, `d = 75 - 53 s`.

1. At the prime `(d)`, with residue map `ρ = residueSeven : a + b s ↦ a + 3 b mod 7`:
   `ρ(A) = 0`, the coordinates of `P₀` are `d`-integral and reduce to `(2, 6)`, a nonsingular
   point of `y² = x³` over `𝔽₇`; hence `P₀ ∈ E₀((d))` (`genP0_mem_E0_d`).
2. At every other prime `π ∤ 2` (`π` not associated to `d`), `ρ(A) ≠ 0` for every residue map
   `ρ` with kernel `(π)`, so `E₀(π) = E(K₀)` (`E0_eq_top_of_ne_d`).

The finite part is `bad_place_congruences_zmod`.
-/

namespace ZInQ.Size

open WeierstrassCurve WeierstrassCurve.Affine

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem residueSeven_ker (a : Zs) : residueSeven a = 0 ↔ genDZ ∣ a := (genDZ_dvd_iff a).symm

theorem not_genDZ_dvd_two : ¬genDZ ∣ 2 := by
  rw [genDZ_dvd_iff, residueSeven_apply]; decide

/-- `ρ(A) = 0` at `(d)`. -/
theorem resK_genA_d : resK genDZ residueSeven (-genD ^ 2) = 0 := by
  rw [neg_genD_sq_eq_toK0, resK_toK0 prime_genDZ residueSeven residueSeven_ker,
    (residueSeven_ker _).mpr (dvd_neg.mpr (dvd_pow_self _ two_ne_zero))]

theorem genX0_mul : genX0 * Zs.toK0 8 = Zs.toK0 ⟨1641, -1160⟩ := by
  ext <;> simp [genX0]; norm_num

theorem genY0_mul : genY0 * Zs.toK0 32 = Zs.toK0 ⟨-123720, 87483⟩ := by
  ext <;> simp [genY0]; norm_num

theorem not_genDZ_dvd_eight : ¬genDZ ∣ (8 : Zs) := by
  rw [genDZ_dvd_iff, residueSeven_apply]; decide

theorem not_genDZ_dvd_thirtytwo : ¬genDZ ∣ (32 : Zs) := by
  rw [genDZ_dvd_iff, residueSeven_apply]; decide

theorem vge_genX0_d : VGe genDZ 0 genX0 := by
  have : genX0 = Zs.toK0 ⟨1641, -1160⟩ / Zs.toK0 8 := by
    rw [← genX0_mul, mul_div_cancel_right₀]; norm_num
  rw [this]
  have := (vge_toK0 prime_genDZ ⟨1641, -1160⟩).div prime_genDZ (y := Zs.toK0 8) (by norm_num)
  rwa [(vp_eq_zero_iff prime_genDZ (by norm_num)).mpr not_genDZ_dvd_eight, sub_zero] at this

theorem vge_genY0_d : VGe genDZ 0 genY0 := by
  have : genY0 = Zs.toK0 ⟨-123720, 87483⟩ / Zs.toK0 32 := by
    rw [← genY0_mul, mul_div_cancel_right₀]; norm_num
  rw [this]
  have := (vge_toK0 prime_genDZ ⟨-123720, 87483⟩).div prime_genDZ (y := Zs.toK0 32)
    (by norm_num)
  rwa [(vp_eq_zero_iff prime_genDZ (by norm_num)).mpr not_genDZ_dvd_thirtytwo, sub_zero] at this

/-- `P₀` reduces to `(2, 6)` at `(d)`. -/
theorem resK_genP0_d :
    resK genDZ residueSeven genX0 = 2 ∧ resK genDZ residueSeven genY0 = 6 := by
  obtain ⟨h1, h2, -, -, -, -, h8, h32⟩ := bad_place_congruences_zmod
  rw [resK_eq residueSeven residueSeven_ker not_genDZ_dvd_eight genX0_mul,
    resK_eq residueSeven residueSeven_ker not_genDZ_dvd_thirtytwo genY0_mul]
  rw [map_ofNat, map_ofNat]
  simp only [residueSeven_apply]
  push_cast at h1 h2 h8 h32 ⊢
  constructor
  · rw [div_eq_iff h8, h1]; ring
  · rw [div_eq_iff h32, h2]; ring

/-- `(2, 6)` is a nonsingular point of `y² = x³` over `𝔽₇`. -/
theorem nonsingular_two_six : (shortCurve (0 : ZMod 7)).toAffine.Nonsingular 2 6 := by
  obtain ⟨-, -, -, h62, h12, -⟩ := bad_place_congruences_zmod
  rw [nonsingular_iff, shortCurve_equation_iff]
  refine ⟨by rw [h62]; ring, Or.inr ?_⟩
  simp only [shortCurve_a₁, shortCurve_a₃, zero_mul]
  intro h; apply h12; linear_combination h

/-- **Part 1.** `P₀ ∈ E₀((d))`: its reduction at `(d)` is the nonsingular point `(2, 6)` of
`y² = x³` over `𝔽₇`. -/
theorem genP0_mem_E0_d :
    genP0 ∈ E0sub prime_genDZ residueSeven residueSeven_ker (vge_neg_genD_sq _ prime_genDZ) resK_genA_d
      not_genDZ_dvd_two := by
  change ¬VGe genDZ 0 genX0 ∨ (VGe genDZ 0 genX0 ∧ (shortCurve (0 : ZMod 7)).toAffine.Nonsingular
    (resK genDZ residueSeven genX0) (resK genDZ residueSeven genY0))
  refine Or.inr ⟨vge_genX0_d, ?_⟩
  rw [resK_genP0_d.1, resK_genP0_d.2]
  exact nonsingular_two_six

/-- The reduction of `P₀` at `(d)` is `(2, 6)`. -/
theorem redK_genP0_d :
    redK genDZ residueSeven (-genD ^ 2) 0 genP0 = .some 2 6 nonsingular_two_six := by
  have hns : (shortCurve (0 : ZMod 7)).toAffine.Nonsingular (resK genDZ residueSeven genX0)
      (resK genDZ residueSeven genY0) := by
    rw [resK_genP0_d.1, resK_genP0_d.2]; exact nonsingular_two_six
  refine (redK_some_of_ns _ vge_genX0_d hns).trans ?_
  simp only [Point.some.injEq]
  exact resK_genP0_d

/-- At a prime `π` not associated to `d`, `ρ(A) ≠ 0` for any residue map with kernel `(π)`. -/
theorem resK_genA_ne_zero {k : Type*} [Field k] {π : Zs} (hπ : Prime π) (ρ : Zs →+* k)
    (hρ : ∀ a, ρ a = 0 ↔ π ∣ a) (hd : ¬Associated π genDZ) :
    resK π ρ (-genD ^ 2) ≠ 0 := by
  rw [neg_genD_sq_eq_toK0, resK_toK0 hπ ρ hρ, ne_eq, hρ, dvd_neg]
  intro h
  exact hd (hπ.associated_of_dvd prime_genDZ (hπ.dvd_of_dvd_pow h))

/-- **Part 2.** At every prime `π ∤ 2` other than `(d)`, `E` has good reduction and
`E₀(π) = E(K₀)`. -/
theorem E0_eq_top_of_ne_d {k : Type*} [Field k] [DecidableEq k] {π : Zs} (hπ : Prime π)
    (ρ : Zs →+* k) (hρ : ∀ a, ρ a = 0 ↔ π ∣ a) (h2 : ¬π ∣ 2) (hd : ¬Associated π genDZ) :
    E0sub hπ ρ hρ (vge_neg_genD_sq _ hπ) rfl h2 = ⊤ :=
  E0_eq_top_of_good hπ ρ hρ (vge_neg_genD_sq _ hπ) rfl h2 (resK_genA_ne_zero hπ ρ hρ hd)

end ZInQ.Size
