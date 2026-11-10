import ZInQKernel.Multiplication.Completeness.SlopeCompleteness
import ZInQKernel.Multiplication.Completeness.AP.PoleValuations
import ZInQKernel.Multiplication.Completeness.AP.WeakApprox

/-!
# Completeness of the slope certificate under field 2′

Route AP of `docs/research/nt-22p.md`, §3.2 ("The modified completeness argument"). The proof is
that of `slope_complete`, except for the choice of `q`: at an old prime `ℓ` where field 2′ uses
its second alternative (`F(t) > 0` and the hypotheses of Lemma P), `q` is chosen in the ball of
Lemma P(2) (`lemmaP_two_ball`) with `N = 23 v_ℓ(v) + v_ℓ(12) + 2`, instead of `v_ℓ(q) ≥ C_ℓ`;
weak approximation with residue targets (`weak_approx_targets`) provides such a `q`. Lemma P(3)
(inside `pole_input_valuations_AP`) then gives `v_ℓ(B) ≥ 4`. The sign is `η = 1` at such a
slope, since `F(t) > 0`.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

/-- **Completeness of the slope certificate under field 2′.** Assume pole completeness. For
`n₁, n₂ ∈ ℤ` and a slope `t` satisfying `GoodSlopeAP`,
`Slope(t, ℓ₀; c_*, c_* n₁, c_* n₂, c_* n₁ n₂)` holds. -/
theorem slope_complete_AP (hPC : PoleCompleteness) (n₁ n₂ : ℤ) {t : ℚ}
    {B₀ : ℝ} (ht : GoodSlopeAP B₀ t) :
    SlopePred t Syntax.ell (certShifts ![n₁, n₂, n₁ * n₂]) := by
  classical
  set n : Fin 3 → ℤ := ![n₁, n₂, n₁ * n₂] with hn
  set c := certShifts n with hc
  have hℓ0 : (Syntax.ell : ℚ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp one_le_ell)
  refine ⟨ht.not_mem_contactSet, ht.ne_one, hℓ0, ?_⟩
  -- the sign `η`
  set Fq := contactPoly t / (t - 1) ^ 8 with hFq
  have hFq0 : Fq ≠ 0 := div_ne_zero (contactPoly_ne_zero ht.not_mem_contactSet)
    (pow_ne_zero _ (sub_ne_zero.mpr ht.ne_one))
  obtain ⟨η, hη, hR0pos⟩ : ∃ η : ℚ, (η = 1 ∨ η = -1) ∧ 0 < slopeR0 η t := by
    rcases lt_or_gt_of_ne hFq0 with h | h
    · refine ⟨-1, Or.inr rfl, ?_⟩
      have : slopeR0 (-1) t = -Fq := by rw [slopeR0, hFq]; ring
      rw [this]; linarith
    · refine ⟨1, Or.inl rfl, ?_⟩
      have : slopeR0 1 t = Fq := by rw [slopeR0, hFq]; ring
      rw [this]; exact h
  set R0 := slopeR0 η t with hR0def
  -- the selected primes and the shifts
  obtain ⟨P, hPcard, hPmem⟩ := ht.few
  choose hfun hfun0 hfunc hfunM hfungood using exists_shift
  let sel : Fin 6 → ℕ := fun g => (P.toList[g.val]?).getD 0
  let h : Fin 6 → ℤ := fun g => hfun (sel g)
  let z : Fin 6 → Fin 3 → ℤ := fun g => ![n₁ * h g, n₂ * h g, n₁ * n₂ * h g]
  let D : Fin 6 → Fin 12 → K0 := fun g => testValues (h g) (z g) c
  have hsel : ∀ p ∈ P, ∃ g, sel g = p := by
    intro p hp
    have hmem : p ∈ P.toList := Finset.mem_toList.mpr hp
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
    have hi6 : i < 6 := lt_of_lt_of_le hi (by rw [Finset.length_toList]; exact hPcard)
    refine ⟨⟨i, hi6⟩, ?_⟩
    simp only [sel, List.getElem?_eq_getElem hi, Option.getD_some, hget]
  -- integrality above `S_b`
  have hD_old : ∀ p ∈ S_b, ∀ (π : Zs) (hπ : Prime π), π ∣ (p : Zs) →
      ∀ g j, Vge (vP π hπ) 0 (D g j) := by
    intro p hp π hπ hπp g j
    have hz : z g = fun i => n i * h g := by
      funext i; fin_cases i <;> rfl
    simp only [D]
    rw [hz]
    exact tests_integral_old n (h g) (hfunM _) (hfun0 _) (hfunc _) hp hπ hπp j
  -- precision at the selected primes
  have hD_sel : ∀ p : ℕ, p ∉ S_b → IsOddContactPrime t p →
      ∃ g, ∃ (π : Zs) (hπ : Prime π), π ∣ (p : Zs) ∧ ∀ j, Vge (vP π hπ) (prec j) (D g j) := by
    intro p hpS hodd
    obtain ⟨-, hgood, -⟩ := ht.contact p hpS hodd
    obtain ⟨g, hg⟩ := hsel p ((hPmem p).mpr ⟨hpS, hodd⟩)
    have : Fact p.Prime := ⟨hodd.1⟩
    have hp324 := le_of_not_mem_S_b hodd.1 hpS
    obtain ⟨r, hr, h1, h2, hd1, hd2⟩ := hfungood p hgood
    clear hfungood
    obtain ⟨π, hπ, hπr⟩ := exists_prime_residueAt r hr
    have hhg : h g = hfun p := by simp only [h, hg]
    refine ⟨g, π, hπ, (hπr p).mp (by simp), fun j => ?_⟩
    have := tests_precision_selected hp324 hr h1 h2 hπ hπr (h := h g) (by rw [hhg]; exact hfun0 p)
      (by rw [hhg]; exact hfunc p) (by rw [hhg]; exact hd1) (by rw [hhg]; exact hd2) n₁ n₂ j
    refine this.mono ?_
    unfold prec; split_ifs <;> norm_num
  -- the normalized tests and the positivity lemma
  set C : Fin 6 → Fin 12 → K0 := fun g => normTests R0 t (D g) with hC
  obtain ⟨ε, hε, hsmall⟩ := pole_input_small R0 (Syntax.ell : ℚ) hR0pos hℓ0 C
  -- the target `x₀ = R₀^{-1/2}` and the radius `δ`
  have hR0r : (0 : ℝ) < R0 := by exact_mod_cast hR0pos
  set x₀ : ℝ := 1 / Real.sqrt R0 with hx₀
  have hsq : Real.sqrt R0 * Real.sqrt R0 = R0 := Real.mul_self_sqrt hR0r.le
  have hsqpos : 0 < Real.sqrt R0 := Real.sqrt_pos.mpr hR0r
  have hx₀pos : 0 < x₀ := by positivity
  have hRx : (R0 : ℝ) * x₀ ^ 2 = 1 := by
    rw [hx₀, div_pow, one_pow, sq, hsq]; field_simp
  set δ : ℝ := min 1 (ε / (R0 * (2 * x₀ + 1))) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by positivity)
  -- the targets of the weak approximation at the old primes (field 2′)
  have htarget : ∀ p ∈ S_b, ∃ (m : ℤ) (k n : ℕ), ∀ q : ℚ, q ≠ 0 →
      padicNorm p (q - m / (p : ℚ) ^ k) ≤ (p : ℚ) ^ (-(n : ℤ)) →
      (OldBounds p t ∧ (Cp p : ℤ) ≤ padicValRat p q) ∨
        ∃ e : ℕ, padicValRat p (contactPoly t / (t - 1) ^ 8) = 2 * e ∧
          padicValRat p (t - 1) = -e ∧ (slopeA R0 q ≠ 0 →
            23 * (e : ℤ) + padicValNat p 12 + 2 ≤ padicValRat p (slopeA R0 q)) := by
    intro p hpS
    have : Fact p.Prime := ⟨prime_of_mem_S_b hpS⟩
    rcases ht.old p hpS with hold | ⟨hF, hP⟩
    · refine ⟨0, 0, Cp p, fun q hq0 hq => Or.inl ⟨hold, ?_⟩⟩
      simp only [Int.cast_zero, pow_zero, div_one, sub_zero] at hq
      exact (padicNorm_le_zpow_iff_ap hq0 _).mp hq
    · -- `F(t) > 0`, so `η = 1`
      have hη1 : η = 1 := by
        rcases hη with h | h
        · exact h
        · exfalso
          have hFqpos : 0 < Fq := div_pos hF (Even.pow_pos (by decide) (sub_ne_zero.mpr ht.ne_one))
          have : R0 = -Fq := by rw [hR0def, h, slopeR0, hFq]; ring
          linarith
      obtain ⟨hv1, hv2, -⟩ := lemmaP_one hP
      obtain ⟨m, k, M, hball⟩ := lemmaP_two_ball hP
        (23 * (padicValNat p t.den : ℤ) + padicValNat p 12 + 2)
      refine ⟨m, k, M, fun q hq0 hq => Or.inr ⟨padicValNat p t.den, ?_, hv2, fun ha => ?_⟩⟩
      · rw [slopeR0, one_mul] at hv1; exact hv1
      · have h := hball q hq
        have h1 : slopeR0 1 t = R0 := by rw [hR0def, hη1]
        rw [h1] at h
        exact (padicNorm_le_zpow_iff_ap ha _).mp h
  choose! tm tk tn htn using htarget
  obtain ⟨q, hq0, hqX, hqδ, hq_tgt, hq_sel'⟩ :=
    weak_approx_targets S_b P (fun p hp => prime_of_mem_S_b hp)
      (fun p hp => ((hPmem p).mp hp).2.1)
      (Finset.disjoint_left.mpr fun p hS hP => ((hPmem p).mp hP).1 hS) tm tk tn x₀ δ hδpos
      {x₀, -x₀}
  set a := slopeA R0 q with ha_def
  have hareal : (a : ℝ) = R0 * (x₀ - q) * (x₀ + q) := by
    rw [ha_def, slopeA]; push_cast
    linear_combination (-1 : ℝ) * hRx
  have ha0 : a ≠ 0 := by
    intro h0
    have : ((a : ℚ) : ℝ) = 0 := by rw [h0]; simp
    rw [hareal] at this
    rcases mul_eq_zero.mp this with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · exact hqX (by simp [show (q : ℝ) = x₀ by linarith])
    · exact hqX (by simp [show (q : ℝ) = -x₀ by linarith])
  have haε : |(a : ℝ)| < ε := by
    rw [hareal, abs_mul, abs_mul, abs_of_pos hR0r]
    have h1 : |x₀ - (q : ℝ)| < δ := by rw [abs_sub_comm]; exact hqδ
    have h2 : |x₀ + (q : ℝ)| < 2 * x₀ + 1 := by
      have : |(q : ℝ) - x₀| < 1 := lt_of_lt_of_le hqδ (min_le_left _ _)
      rw [abs_lt] at this ⊢; constructor <;> linarith
    have h3 : δ * (R0 * (2 * x₀ + 1)) ≤ ε := by
      have := min_le_right 1 (ε / (R0 * (2 * x₀ + 1)))
      rw [← hδ] at this
      rwa [le_div_iff₀ (by positivity)] at this
    calc (R0 : ℝ) * |x₀ - q| * |x₀ + q| < R0 * δ * (2 * x₀ + 1) :=
          mul_lt_mul' (mul_le_mul_of_nonneg_left h1.le hR0r.le) h2 (abs_nonneg _) (by positivity)
      _ ≤ ε := by linarith [h3]
  obtain ⟨-, hW, hΘpos, -, hBpos, hBhalf⟩ := hsmall a ha0 haε
  -- the valuations of the pole input
  have hℓv := fun (p : ℕ) (hp : p.Prime) => padicValRat_ell hp
  have hq_sel : ∀ p : ℕ, p ∉ S_b → IsOddContactPrime t p → 0 ≤ padicValRat p q :=
    fun p hpS hodd => hq_sel' p ((hPmem p).mpr ⟨hpS, hodd⟩)
  have hΘ0 : traceTheta (fun g => groupW (slopeR Syntax.ell a R0) (C g)) ≠ 0 := hΘpos.ne'
  have hq_old : ∀ p ∈ S_b, (OldBounds p t ∧ (Cp p : ℤ) ≤ padicValRat p q) ∨
      ∃ e : ℕ, padicValRat p (contactPoly t / (t - 1) ^ 8) = 2 * e ∧
        padicValRat p (t - 1) = -e ∧
        23 * (e : ℤ) + padicValNat p 12 + 2 ≤ padicValRat p (slopeA (slopeR0 η t) q) := by
    intro p hpS
    rcases htn p hpS q hq0 (hq_tgt p hpS) with h | ⟨e, h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨e, h1, h2, h3 ha0⟩
  obtain ⟨-, -, -, hS0, hsq'⟩ := pole_input_valuations_AP ht hη hℓ0 hℓv hq_old hq_sel ha0 D
    hD_old hD_sel hW hΘ0
  refine ⟨η, q, h, z, hη, ha0, fun g => ⟨hfun0 _, hfunc _⟩, hW, hΘ0, ?_⟩
  exact hPC _ hsq' hBpos hBhalf hS0

end ZInQ.Mult
