import Mathlib

namespace FS5NoCM

variable {K : Type} [Field K]

local notation "M2" => Matrix (Fin 2) (Fin 2) K

theorem quat_comm_I (I J : M2) (hI : I * I = (2 : K) • 1) (hJI : J * I = -(I * J))
    (a b c d : K) :
    I * (a • 1 + b • I + c • J + d • (I * J)) - (a • 1 + b • I + c • J + d • (I * J)) * I =
      (2 * c) • (I * J) + (4 * d) • J := by
  have r1 : I * (I * J) = (2 : K) • J := by rw [← mul_assoc, hI, smul_mul_assoc, one_mul]
  have r2 : (I * J) * I = -((2 : K) • J) := by
    rw [mul_assoc, hJI, mul_neg, ← mul_assoc, hI, smul_mul_assoc, one_mul]
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hI, r1, r2, hJI]
  module

theorem quat_comm_J (I J : M2) (hI : I * I = (2 : K) • 1) (hJ : J * J = (-3 : K) • 1)
    (hJI : J * I = -(I * J)) (a b c d : K) :
    J * (a • 1 + b • I + c • J + d • (I * J)) - (a • 1 + b • I + c • J + d • (I * J)) * J =
      (-2 * b) • (I * J) + (6 * d) • I := by
  have r3 : (I * J) * J = (-3 : K) • I := by rw [mul_assoc, hJ, mul_smul_comm, mul_one]
  have r4 : J * (I * J) = (3 : K) • I := by
    rw [← mul_assoc, hJI, neg_mul, mul_assoc, hJ, mul_smul_comm, mul_one, neg_smul]; module
  simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hJ, r3, r4, hJI]
  module

/-- **A matrix commuting with `I` and `J` is scalar**, if `I² = 2`, `J² = −3`, `JI = −IJ` in
`M₂(K)` and `2` is not a square in `K` (then `1, I, J, IJ` is a `K`-basis of `M₂(K)`). -/
theorem commute_quat_scalar (I J : M2) (hI : I * I = (2 : K) • 1) (hJ : J * J = (-3 : K) • 1)
    (hJI : J * I = -(I * J)) (hns : ∀ r : K, r * r ≠ 2) (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (Y : M2) (hYI : I * Y = Y * I) (hYJ : J * Y = Y * J) : ∃ a : K, Y = a • (1 : M2) := by
  have r3 : (I * J) * J = (-3 : K) • I := by rw [mul_assoc, hJ, mul_smul_comm, mul_one]
  have hinj : Function.Injective (fun x : K => x • (1 : M2)) := smul_left_injective K one_ne_zero
  have hIns : ∀ s : K, I ≠ s • (1 : M2) := by
    intro s hs
    apply hns s
    apply hinj
    simp only
    rw [← hI, hs, smul_mul_smul_comm, mul_one]
  -- `(2c)•IJ + (4d)•J = 0 → c = 0 ∧ d = 0`
  have kill : ∀ c d : K, (2 * c) • (I * J) + (4 * d) • J = 0 → c = 0 ∧ d = 0 := by
    intro c d h
    have h' := congrArg (· * J) h
    simp only [add_mul, smul_mul_assoc, r3, hJ, zero_mul] at h'
    have hc : c = 0 := by
      by_contra hc
      have h6 : (-6 * c : K) ≠ 0 := mul_ne_zero (by
        rw [show (-6 : K) = -(2 * 3) by norm_num]; exact neg_ne_zero.mpr (mul_ne_zero h2 h3)) hc
      apply hIns ((-6 * c)⁻¹ * (12 * d))
      have : (-6 * c) • I = (12 * d) • (1 : M2) := by
        have e : (-6 * c) • I - (12 * d) • (1 : M2) =
            (2 * c) • (-3 : K) • I + (4 * d) • (-3 : K) • (1 : M2) := by module
        rw [h'] at e; exact sub_eq_zero.mp e
      rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ h6, one_smul]
    subst hc
    refine ⟨rfl, ?_⟩
    have : (-12 * d) • (1 : M2) = 0 := by
      have e : (-12 * d) • (1 : M2) = ((2 : K) * 0) • (-3 : K) • I + (4 * d) • (-3 : K) • (1 : M2) := by
        module
      rw [e]; exact h'
    have h12 : (-12 * d : K) = 0 := hinj (by simpa using this)
    have : (12 : K) ≠ 0 := by
      have : (12 : K) = 2 * 2 * 3 := by norm_num
      rw [this]; exact mul_ne_zero (mul_ne_zero h2 h2) h3
    have := mul_eq_zero.mp (show (-12 : K) * d = 0 from h12)
    rcases this with h | h
    · exact absurd (neg_eq_zero.mp h) ‹(12 : K) ≠ 0›
    · exact h
  let v : Fin 4 → M2 := ![1, I, J, I * J]
  have hsum : ∀ g : Fin 4 → K, ∑ i, g i • v i = g 0 • 1 + g 1 • I + g 2 • J + g 3 • (I * J) := by
    intro g; simp [Fin.sum_univ_four, v]
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [hsum] at hg
    have hI0 := quat_comm_I I J hI hJI (g 0) (g 1) (g 2) (g 3)
    rw [hg, mul_zero, zero_mul, sub_zero] at hI0
    obtain ⟨hg2, hg3⟩ := kill _ _ hI0.symm
    rw [hg2, hg3, zero_smul, zero_smul, add_zero, add_zero] at hg
    have hg1 : g 1 = 0 := by
      by_contra hg1
      apply hIns (-(g 1)⁻¹ * g 0)
      have hb : g 1 • I = -(g 0 • (1 : M2)) := eq_neg_of_add_eq_zero_right hg
      calc I = (g 1)⁻¹ • (g 1 • I) := by rw [smul_smul, inv_mul_cancel₀ hg1, one_smul]
        _ = (-(g 1)⁻¹ * g 0) • 1 := by rw [hb]; module
    rw [hg1, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := hinj (by simpa using hg)
    intro i; fin_cases i <;> assumption
  have hspan : Submodule.span K (Set.range v) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp [Module.finrank_matrix])
  have hY : Y ∈ Submodule.span K (Set.range v) := hspan ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hY
  rw [hsum] at hg
  subst hg
  have hI0 := quat_comm_I I J hI hJI (g 0) (g 1) (g 2) (g 3)
  rw [hYI, sub_self] at hI0
  obtain ⟨hg2, hg3⟩ := kill _ _ hI0.symm
  have hJ0 := quat_comm_J I J hI hJ hJI (g 0) (g 1) (g 2) (g 3)
  rw [hYJ, sub_self, hg3, mul_zero, zero_smul, add_zero] at hJ0
  have hg1 : g 1 = 0 := by
    have h' := congrArg (· * J) hJ0
    simp only [smul_mul_assoc, r3, zero_mul, smul_smul] at h'
    by_contra hg1
    apply hIns 0
    have hne : (-2 * g 1 * -3 : K) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h2) hg1) (neg_ne_zero.mpr h3)
    rw [zero_smul]
    exact (smul_eq_zero.mp h'.symm).resolve_left hne
  refine ⟨g 0, ?_⟩
  rw [hg1, hg2, hg3]; simp

section AdjRoot

open Polynomial

variable (d : ℚ)

/-- `X² − d` is irreducible over `ℚ` for `d < 0`. -/
theorem irred_sq_sub (hd : d < 0) : Irreducible (X ^ 2 - C d : ℚ[X]) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => by nlinarith [sq_nonneg b])

theorem monic_sq_sub : (X ^ 2 - C d : ℚ[X]).Monic := monic_X_pow_sub_C _ two_ne_zero

theorem finrank_adjRoot : Module.finrank ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) = 2 := by
  rw [(AdjoinRoot.powerBasis' (monic_sq_sub d)).finrank]
  exact natDegree_X_pow_sub_C

theorem finite_adjRoot : Module.Finite ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) :=
  (AdjoinRoot.powerBasis' (monic_sq_sub d)).finite

theorem root_sq : (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])) ^ 2 =
    algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X])) d := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C d : ℚ[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact sub_eq_zero.mp h

/-- For `d < 0`, `ℚ(√d)` (as `AdjoinRoot`, with its field structure) is a totally complex
quadratic number field. -/
theorem adjRoot_numberField (hd : d < 0) :
    letI : Fact (Irreducible (X ^ 2 - C d : ℚ[X])) := ⟨irred_sq_sub d hd⟩
    NumberField (AdjoinRoot (X ^ 2 - C d : ℚ[X])) ∧
      NumberField.IsTotallyComplex (AdjoinRoot (X ^ 2 - C d : ℚ[X])) := by
  let : Fact (Irreducible (X ^ 2 - C d : ℚ[X])) := ⟨irred_sq_sub d hd⟩
  have : CharZero (AdjoinRoot (X ^ 2 - C d : ℚ[X])) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X]))).injective
  have := finite_adjRoot d
  refine ⟨{}, ⟨fun v => ?_⟩⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  rintro ⟨φ, hφ, -⟩
  have h2 : (hφ.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X]))) ^ 2 = (d : ℝ) := by
    have := congrArg hφ.embedding (root_sq d)
    rwa [map_pow, eq_ratCast (algebraMap ℚ (AdjoinRoot (X ^ 2 - C d : ℚ[X]))) d,
      map_ratCast] at this
  have hd' : (d : ℝ) < 0 := by exact_mod_cast hd
  nlinarith [sq_nonneg (hφ.embedding (AdjoinRoot.root (X ^ 2 - C d : ℚ[X])))]

end AdjRoot

end FS5NoCM
