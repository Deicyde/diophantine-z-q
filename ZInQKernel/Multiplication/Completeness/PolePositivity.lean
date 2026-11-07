import ZInQKernel.Multiplication.Certificate.SlopePredicate

/-!
# Positivity and smallness of the pole input

For `R > 0` every factor `1 + R C²` of `W_g = ∏_j (1 + R C_{gj}²)` has both real embeddings
at least `1`, so `Θ = Tr ∑_g W_g⁻¹` is a sum of twelve reals in `(0, 1]`. For `R` small the
embeddings of `W_g` are at most `2^12`, so `Θ ≥ 12 / 2^12` and `R / Θ² < 1/2`.
-/

namespace ZInQ.Mult

open scoped BigOperators
open ZInQ.K0

/-- `Tr z = σ₊(z) + σ₋(z)`. -/
theorem trace_cast_eq_emb (z : K0) :
    ((QuadraticAlgebra.trace z : ℚ) : ℝ) = embPlus z + embMinus z := by
  rw [K0.trace_eq, embPlus_apply, embMinus_apply]; push_cast; ring

/-- The trace `Θ = Tr ∑_g W_g⁻¹` of the slope predicate as a function of `R` and the `C_{gj}`. -/
noncomputable abbrev poleTheta (R : ℚ) (C : Fin 6 → Fin 12 → K0) : ℚ :=
  traceTheta fun g => groupW R (C g)

/-- Bounds on a real embedding of `W`: `1 ≤ σ(W) ≤ (1 + R K)^12` when `σ(C_j)² ≤ K`. -/
theorem emb_groupW_bounds (σ : K0 →+* ℝ) {R : ℚ} (hR : 0 ≤ R) (C : Fin 12 → K0) {K : ℝ}
    (hK : ∀ j, σ (C j) ^ 2 ≤ K) :
    1 ≤ σ (groupW R C) ∧ σ (groupW R C) ≤ (1 + R * K) ^ 12 := by
  have hRr : (0 : ℝ) ≤ R := by exact_mod_cast hR
  have hfac : ∀ j, σ (1 + (R : K0) * C j ^ 2) = 1 + R * σ (C j) ^ 2 := by
    intro j; simp [map_ratCast]
  unfold groupW
  rw [map_prod]
  simp only [hfac]
  constructor
  · have := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin 12 => (1 : ℝ))
      (g := fun j => 1 + (R : ℝ) * σ (C j) ^ 2) (fun _ _ => zero_le_one)
      (fun j _ => by have := mul_nonneg hRr (sq_nonneg (σ (C j))); linarith)
    simpa using this
  · have := Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : Fin 12 => 1 + (R : ℝ) * K)
      (f := fun j => 1 + (R : ℝ) * σ (C j) ^ 2)
      (fun j _ => by have := mul_nonneg hRr (sq_nonneg (σ (C j))); linarith)
      (fun j _ => by have := mul_le_mul_of_nonneg_left (hK j) hRr; linarith)
    simpa using this

/-- The two real embeddings of `W_g` are at least `1`; in particular `W_g ≠ 0`. -/
theorem one_le_emb_groupW {R : ℚ} (hR : 0 ≤ R) (C : Fin 12 → K0) :
    1 ≤ embPlus (groupW R C) ∧ 1 ≤ embMinus (groupW R C) :=
  ⟨(emb_groupW_bounds embPlus hR C (K := ∑ j, embPlus (C j) ^ 2)
      fun j => Finset.single_le_sum (f := fun j => embPlus (C j) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).1,
   (emb_groupW_bounds embMinus hR C (K := ∑ j, embMinus (C j) ^ 2)
      fun j => Finset.single_le_sum (f := fun j => embMinus (C j) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).1⟩

theorem groupW_ne_zero {R : ℚ} (hR : 0 ≤ R) (C : Fin 12 → K0) : groupW R C ≠ 0 := by
  intro h
  have := (one_le_emb_groupW hR C).1
  rw [h, map_zero] at this
  linarith

/-- `Θ` as a sum of the twelve reals `σ(W_g)⁻¹`. -/
theorem poleTheta_cast (R : ℚ) (C : Fin 6 → Fin 12 → K0) :
    ((poleTheta R C : ℚ) : ℝ) =
      ∑ g, (embPlus (groupW R (C g)))⁻¹ + ∑ g, (embMinus (groupW R (C g)))⁻¹ := by
  rw [poleTheta, traceTheta, trace_cast_eq_emb, map_sum, map_sum]
  simp only [map_inv₀]

/-- `0 < Θ ≤ 12` for `R ≥ 0`. -/
theorem poleTheta_pos_le {R : ℚ} (hR : 0 ≤ R) (C : Fin 6 → Fin 12 → K0) :
    0 < poleTheta R C ∧ poleTheta R C ≤ 12 := by
  have h := poleTheta_cast R C
  have hp : ∀ g, 0 < (embPlus (groupW R (C g)))⁻¹ ∧ (embPlus (groupW R (C g)))⁻¹ ≤ 1 := fun g =>
    ⟨inv_pos.mpr (by linarith [(one_le_emb_groupW hR (C g)).1]),
      inv_le_one_of_one_le₀ (one_le_emb_groupW hR (C g)).1⟩
  have hm : ∀ g, 0 < (embMinus (groupW R (C g)))⁻¹ ∧ (embMinus (groupW R (C g)))⁻¹ ≤ 1 := fun g =>
    ⟨inv_pos.mpr (by linarith [(one_le_emb_groupW hR (C g)).2]),
      inv_le_one_of_one_le₀ (one_le_emb_groupW hR (C g)).2⟩
  have s1 : 0 < ∑ g, (embPlus (groupW R (C g)))⁻¹ :=
    Finset.sum_pos (fun g _ => (hp g).1) Finset.univ_nonempty
  have s2 : 0 < ∑ g, (embMinus (groupW R (C g)))⁻¹ :=
    Finset.sum_pos (fun g _ => (hm g).1) Finset.univ_nonempty
  have s3 : ∑ g, (embPlus (groupW R (C g)))⁻¹ ≤ 6 := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ : Fin 6 => (1 : ℝ))
      (fun g _ => (hp g).2)
  have s4 : ∑ g, (embMinus (groupW R (C g)))⁻¹ ≤ 6 := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (g := fun _ : Fin 6 => (1 : ℝ))
      (fun g _ => (hm g).2)
  constructor
  · have : (0 : ℝ) < poleTheta R C := by rw [h]; linarith
    exact_mod_cast this
  · have : ((poleTheta R C : ℚ) : ℝ) ≤ 12 := by rw [h]; linarith
    exact_mod_cast this

/-- The smallness statement in terms of `R`: there is `ρ > 0` such that `0 < R < ρ` gives
`0 < R / Θ² < 1/2`. -/
theorem pole_input_small_R (C : Fin 6 → Fin 12 → K0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ R : ℚ, 0 < R → (R : ℝ) < ρ →
      0 < R / poleTheta R C ^ 2 ∧ R / poleTheta R C ^ 2 < 1 / 2 := by
  set K : ℝ := 1 + ∑ g, ∑ j, (embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2) with hK
  have hKnn : 0 ≤ ∑ g, ∑ j, (embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2) :=
    Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun j _ => by positivity
  have hKpos : 0 < K := by linarith
  have hKp : ∀ g j, embPlus (C g j) ^ 2 ≤ K := by
    intro g j
    have h1 : embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2 ≤
        ∑ j, (embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2) :=
      Finset.single_le_sum (f := fun j => embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    have h2 : ∑ j, (embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2) ≤
        ∑ g, ∑ j, (embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2) :=
      Finset.single_le_sum (f := fun g => ∑ j, (embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ g)
    nlinarith [sq_nonneg (embMinus (C g j))]
  have hKm : ∀ g j, embMinus (C g j) ^ 2 ≤ K := by
    intro g j
    have h1 : embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2 ≤
        ∑ j, (embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2) :=
      Finset.single_le_sum (f := fun j => embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ j)
    have h2 : ∑ j, (embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2) ≤
        ∑ g, ∑ j, (embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2) :=
      Finset.single_le_sum (f := fun g => ∑ j, (embPlus (C g j) ^ 2 + embMinus (C g j) ^ 2))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ g)
    nlinarith [sq_nonneg (embPlus (C g j))]
  refine ⟨min (1 / K) (9 / 2097152), lt_min (by positivity) (by norm_num), ?_⟩
  intro R hR hRρ
  have hR1 : (R : ℝ) < 1 / K := lt_of_lt_of_le hRρ (min_le_left _ _)
  have hR2 : (R : ℝ) < 9 / 2097152 := lt_of_lt_of_le hRρ (min_le_right _ _)
  have hRK : (R : ℝ) * K ≤ 1 := by
    rw [lt_div_iff₀ hKpos] at hR1; linarith
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  -- each embedding of each `W_g` is at most `2^12`
  have hpow : (1 + (R : ℝ) * K) ^ 12 ≤ 4096 := by
    have : (1 + (R : ℝ) * K) ^ 12 ≤ 2 ^ 12 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 12
    linarith
  have hθlow : (3 / 1024 : ℝ) ≤ poleTheta R C := by
    rw [poleTheta_cast]
    have hp : ∀ g, (1 / 4096 : ℝ) ≤ (embPlus (groupW R (C g)))⁻¹ := fun g => by
      have hb := emb_groupW_bounds embPlus hR.le (C g) (hKp g)
      rw [one_div]
      exact inv_anti₀ (by linarith) (hb.2.trans hpow)
    have hm : ∀ g, (1 / 4096 : ℝ) ≤ (embMinus (groupW R (C g)))⁻¹ := fun g => by
      have hb := emb_groupW_bounds embMinus hR.le (C g) (hKm g)
      rw [one_div]
      exact inv_anti₀ (by linarith) (hb.2.trans hpow)
    have s1 := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin 6 => (1 / 4096 : ℝ))
      (fun g _ => hp g)
    have s2 := Finset.sum_le_sum (s := Finset.univ) (f := fun _ : Fin 6 => (1 / 4096 : ℝ))
      (fun g _ => hm g)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at s1 s2
    push_cast at s1 s2
    linarith
  have hθpos : (0 : ℝ) < poleTheta R C := by linarith
  constructor
  · have : (0 : ℝ) < R / (poleTheta R C : ℝ) ^ 2 := by positivity
    exact_mod_cast this
  · have : (R : ℝ) / (poleTheta R C : ℝ) ^ 2 < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      have : (9 / 1048576 : ℝ) ≤ (poleTheta R C : ℝ) ^ 2 := by nlinarith
      nlinarith
    rw [← Rat.cast_lt (K := ℝ)]; push_cast; exact this

/-- **Positivity and smallness of the pole input.** For `R₀ > 0`, `ℓ ≠ 0` and fixed
`C_{gj} ∈ K₀` there is `ε > 0` such that for `0 < |a| < ε`, with `R = ℓ² a² R₀`: both real
embeddings of every `W_g` are at least `1` (so `W_g ≠ 0`), `0 < Θ ≤ 12`, and
`0 < R / Θ² < 1/2`. -/
theorem pole_input_small (R0 ℓ : ℚ) (hR0 : 0 < R0) (hℓ : ℓ ≠ 0) (C : Fin 6 → Fin 12 → K0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : ℚ, a ≠ 0 → |(a : ℝ)| < ε →
      (∀ g, 1 ≤ embPlus (groupW (ℓ ^ 2 * a ^ 2 * R0) (C g)) ∧
          1 ≤ embMinus (groupW (ℓ ^ 2 * a ^ 2 * R0) (C g))) ∧
      (∀ g, groupW (ℓ ^ 2 * a ^ 2 * R0) (C g) ≠ 0) ∧
      0 < poleTheta (ℓ ^ 2 * a ^ 2 * R0) C ∧ poleTheta (ℓ ^ 2 * a ^ 2 * R0) C ≤ 12 ∧
      0 < ℓ ^ 2 * a ^ 2 * R0 / poleTheta (ℓ ^ 2 * a ^ 2 * R0) C ^ 2 ∧
      ℓ ^ 2 * a ^ 2 * R0 / poleTheta (ℓ ^ 2 * a ^ 2 * R0) C ^ 2 < 1 / 2 := by
  obtain ⟨ρ, hρ, hsmall⟩ := pole_input_small_R C
  have hc : (0 : ℝ) < (ℓ : ℝ) ^ 2 * R0 := by
    have : (0 : ℝ) < R0 := by exact_mod_cast hR0
    have : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ
    positivity
  refine ⟨min 1 (ρ / ((ℓ : ℝ) ^ 2 * R0)), lt_min one_pos (div_pos hρ hc), ?_⟩
  intro a ha haε
  have hRpos : 0 < ℓ ^ 2 * a ^ 2 * R0 := by positivity
  have hR0' : 0 ≤ ℓ ^ 2 * a ^ 2 * R0 := hRpos.le
  have hRρ : ((ℓ ^ 2 * a ^ 2 * R0 : ℚ) : ℝ) < ρ := by
    have h1 : |(a : ℝ)| < 1 := lt_of_lt_of_le haε (min_le_left _ _)
    have h2 : |(a : ℝ)| < ρ / ((ℓ : ℝ) ^ 2 * R0) := lt_of_lt_of_le haε (min_le_right _ _)
    have h3 : (a : ℝ) ^ 2 ≤ |(a : ℝ)| := by
      rw [← sq_abs]; nlinarith [abs_nonneg (a : ℝ)]
    rw [lt_div_iff₀ hc] at h2
    push_cast
    nlinarith
  obtain ⟨h1, h2⟩ := hsmall _ hRpos hRρ
  exact ⟨fun g => one_le_emb_groupW hR0' (C g), fun g => groupW_ne_zero hR0' (C g),
    (poleTheta_pos_le hR0' C).1, (poleTheta_pos_le hR0' C).2, h1, h2⟩

end ZInQ.Mult
