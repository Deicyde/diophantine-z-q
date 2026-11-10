import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! Probe for Lemma Q of docs/research/nt-prop0.md §2.3:
`Σ_ξ χ((ξ - e)(ξ - e')) = -1` for `e ≠ e'`, from `jacobiSum_nontrivial_inv`. -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem probe_sum_quadraticChar_mul_sub (hF : ringChar F ≠ 2) {e e' : F} (h : e ≠ e') :
    ∑ ξ : F, quadraticChar F ((ξ - e) * (ξ - e')) = -1 := by
  set χ := quadraticChar F
  have hc : e' - e ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  -- substitute ξ = e + (e' - e) t
  have hsub : ∑ ξ : F, χ ((ξ - e) * (ξ - e')) = ∑ t : F, χ ((e + (e' - e) * t - e) *
      (e + (e' - e) * t - e')) := by
    refine (Fintype.sum_bijective (fun t => e + (e' - e) * t) ?_ _ _ fun t => rfl).symm
    refine ⟨fun a b hab => ?_, fun ξ => ⟨(ξ - e) / (e' - e), ?_⟩⟩
    · simpa [hc] using hab
    · field_simp; ring
  have hterm : ∀ t : F, χ ((e + (e' - e) * t - e) * (e + (e' - e) * t - e')) =
      χ (-1) * (χ t * χ (1 - t)) := by
    intro t
    have : (e + (e' - e) * t - e) * (e + (e' - e) * t - e') = (e' - e) ^ 2 * ((-1) * (t * (1 - t))) := by
      ring
    rw [this, map_mul, quadraticChar_sq_one' hc, one_mul, map_mul, map_mul]
  rw [hsub, Finset.sum_congr rfl fun t _ => hterm t, ← Finset.mul_sum]
  have hJ : ∑ t : F, χ t * χ (1 - t) = -χ (-1) := by
    have := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
    rwa [(quadraticChar_isQuadratic F).inv, jacobiSum] at this
  rw [hJ, mul_neg, ← map_mul, neg_one_mul, neg_neg, map_one]

#print axioms probe_sum_quadraticChar_mul_sub
