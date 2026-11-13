import ZInQKernel.Multiplication.Completeness.SelectedPrecision
import ZInQKernel.Multiplication.Completeness.SbIntegrality
import ZInQKernel.Multiplication.Completeness.PoleValuations
import ZInQKernel.Multiplication.Completeness.PolePositivity
import ZInQKernel.Multiplication.Completeness.WeakApproximation
import ZInQKernel.Multiplication.Completeness.ShiftChoice

/-!
# Completeness of the slope certificate for a true triple

Blueprint: `multiplication/completeness/slope-completeness.md`.

For a good slope `t` and `n₃ = n₁ n₂`: choose `η` with `R₀ > 0`; give each of the at most six odd
contact primes `p ∉ S_b` of `t` its own group, with the shift `h` of `shift_choice` for the two
reduced group orders at `p`, and give the remaining groups `h = 2c_*`; the tests are then
integral above `S_b` and precise at one place above each selected prime. With the normalized
tests fixed, the positivity lemma gives `ε`, weak approximation gives `q` with `0 < |a| < ε`, and
the valuation lemma shows that `B = R/Θ²` satisfies the hypotheses of pole completeness.

Besides pole completeness the proof uses `M₀ ≥ 1` (`one_le_M0_spec`), which the size chapter
proves (a successful formal multiple exists).
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

/-- The prime `(p, s - r)` of `ℤ[s]` is principal. -/
theorem exists_prime_residueAt {p : ℕ} [Fact p.Prime] (r : ZMod p) (hr : r ^ 2 = 2) :
    ∃ (π : Zs) (_ : Prime π), ∀ a, residueAt r hr a = 0 ↔ π ∣ a := by
  set I := RingHom.ker (residueAt r hr)
  have hmax : I.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (residueAt_surjective r hr)
  have hne : I ≠ ⊥ := by
    intro h
    have hp : ((p : ℕ) : Zs) ∈ I := by rw [RingHom.mem_ker]; simp
    rw [h, Ideal.mem_bot] at hp
    have := congrArg QuadraticAlgebra.re hp
    simp at this
    exact (Fact.out : p.Prime).ne_zero this
  refine ⟨Submodule.IsPrincipal.generator I,
    Submodule.IsPrincipal.prime_generator_of_isPrime I hne, fun a => ?_⟩
  rw [← RingHom.mem_ker, Submodule.IsPrincipal.mem_iff_generator_dvd]

theorem one_le_pointCount (p : ℕ) (a : ZMod p) : 1 ≤ pointCount p a := by
  unfold pointCount; omega

/-- For every prime `p` there is an admissible shift `h` (`h ≠ 0`, `h ≠ c_*`, `M₀ ∣ h`), adapted to
the two reduced group orders at `p` when `p` is a good slope prime. -/
theorem exists_shift (p : ℕ) :
    ∃ h : ℤ, h ≠ 0 ∧ h ≠ Syntax.cstar ∧ (Syntax.M0 : ℤ) ∣ h ∧
      (GoodSlopePrime p → ∃ (r : ZMod p) (_ : r ^ 2 = 2),
        (75 - 53 * r : ZMod p) ≠ 0 ∧ (75 + 53 * r : ZMod p) ≠ 0 ∧
        (pointCount p (-(75 - 53 * r) ^ 2) : ℤ) ∣ h ∧
        (pointCount p (-(75 + 53 * r) ^ 2) : ℤ) ∣ h - Syntax.cstar) := by
  have hcs : (Syntax.cstar : ℤ) = 4 * Syntax.M0 := by rw [Syntax.cstar_eq]; push_cast; ring
  have hM0 := one_le_M0_spec
  by_cases hgood : GoodSlopePrime p
  · obtain ⟨-, r, hr, h1, h2, hgcd⟩ := hgood
    obtain ⟨h, h0, hc, hM, hd1, hd2⟩ := shift_choice' Syntax.M0 _ _ hM0 (one_le_pointCount _ _)
      (one_le_pointCount _ _) hgcd
    refine ⟨h, h0, by rw [hcs]; exact hc, hM, fun _ => ⟨r, hr, h1, h2, hd1, by rw [hcs]; exact hd2⟩⟩
  · refine ⟨2 * Syntax.cstar, ?_, ?_, ?_, fun h => absurd h hgood⟩
    · rw [hcs]; omega
    · rw [hcs]; omega
    · rw [hcs]; exact ⟨8, by ring⟩

/-- The valuations of `ℓ₀`. -/
theorem padicValRat_ell {p : ℕ} (hp : p.Prime) :
    padicValRat p (Syntax.ell : ℚ) = if p ∈ S_b then (Ep p : ℤ) else 0 := by
  rw [padicValRat.of_nat, padicValNat_ell hp]
  split_ifs <;> simp

/-- **Completeness of the slope certificate for a true triple.** Assume pole completeness. For `n₁, n₂ ∈ ℤ` and a slope `t` satisfying conditions 1-4 of the slopes from the prime
pattern, `Slope(t, ℓ₀; c_*, c_* n₁, c_* n₂, c_* n₁ n₂)` holds. -/
theorem slope_complete (hPC : PoleCompleteness) (n₁ n₂ : ℤ) {t : ℚ}
    {B₀ : ℝ} (ht : GoodSlope B₀ t) :
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
  obtain ⟨q, hq0, hqX, hqδ, hq_old, hq_sel'⟩ :=
    weak_approx_q S_b P (fun p hp => prime_of_mem_S_b hp)
      (fun p hp => ((hPmem p).mp hp).2.1) Cp x₀ δ hδpos {x₀, -x₀}
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
  obtain ⟨-, -, -, hS0, hsq'⟩ := pole_input_valuations ht hη hℓ0 hℓv hq_old hq_sel ha0 D
    hD_old hD_sel hW hΘ0
  refine ⟨η, q, h, z, hη, ha0, fun g => ⟨hfun0 _, hfunc _⟩, hW, hΘ0, ?_⟩
  exact hPC _ hsq' hBpos hBhalf hS0

end ZInQ.Mult
