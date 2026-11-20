import ZInQKernel.Contrib.OneProof.RC.KatoP2.Kodai08Checked
import ZInQKernel.Contrib.OneProof.RC.KatoP2.ExtendedNorm
import ZInQKernel.Contrib.CloudB3RC53.Hasse.Convergence
import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.HasseProof

/-! The inverse Frobenius purity condition follows from the tree's Hasse
bound and the quadratic character. The Frobenius object comparison is
the same one used for the Euler polynomial in (0.1.1). -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2.Checked

open PrintsArith Polynomial ZInQ.Contrib.CloudB3RC53

/-- At every good prime outside the base support, the inverse eigenvalues
of the arithmetic Frobenius polynomial of the twist have weight `−1`. -/
theorem kodaiPurity_of_quadratic {E : WeierstrassCurve ℚ} {D NK : ℕ}
    (χ : (ZMod D)ˣ →* ℤ_[2]ˣ) (hχ : ∀ u, χ u * χ u = 1) :
    KodaiPurity (-1) NK (twistedPoly E χ) := by
  intro q hq _
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨v, hv⟩ := ZInQ.Literature.exists_natGenerator_eq q
  have hB : Hasse.HasseBound := fun F _ _ W _ => WeilIsogeny.hasseBoundProved_proof F W
  have hA := Hasse.norm_lcoeff_prime_pow_le hB E v 1
  rw [hv] at hA
  have ha : |(E.LFunction q : ℝ)| ≤ 2 * √(q : ℝ) := by
    simpa [PrintsAnalytic.lcoeff, Complex.norm_intCast, one_add_one_eq_two] using hA
  have hc : (↑(χ (frobUnit D q)) : ℤ_[2]) = 1 ∨
      (↑(χ (frobUnit D q)) : ℤ_[2]) = -1 := by
    apply mul_self_eq_one_iff.mp
    rw [← Units.val_mul, hχ, Units.val_one]
  obtain ⟨e, he, heq⟩ : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      (e : ℤ_[2]) = ↑(χ (frobUnit D q)) := by
    rcases hc with h | h
    · exact ⟨1, Or.inl rfl, by simpa using h.symm⟩
    · exact ⟨-1, Or.inr rfl, by simpa using h.symm⟩
  let a : ℤ := E.LFunction q * e
  refine ⟨1 - C (a : ℚ) * X + C (q : ℚ) * X ^ 2, ?_, ?_⟩
  · have h₀ : algebraMap ℚ ℚ_[2] (a : ℚ) = (a : ℚ_[2]) :=
      map_intCast (algebraMap ℚ ℚ_[2]) a
    have h₁ : algebraMap ℤ_[2] ℚ_[2]
        (((E.LFunction q : ℤ) : ℤ_[2]) * (χ (frobUnit D q) : ℤ_[2])) = (a : ℚ_[2]) := by
      rw [← heq, ← Int.cast_mul]
      exact map_intCast (algebraMap ℤ_[2] ℚ_[2]) a
    have hq₀ : algebraMap ℚ ℚ_[2] (q : ℚ) = (q : ℚ_[2]) :=
      map_natCast (algebraMap ℚ ℚ_[2]) q
    have hq₁ : algebraMap ℤ_[2] ℚ_[2] (q : ℤ_[2]) = (q : ℚ_[2]) :=
      map_natCast (algebraMap ℤ_[2] ℚ_[2]) q
    simp only [twistedPoly, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one, Polynomial.map_C,
      h₀, h₁, hq₀, hq₁]
  · intro z hz
    have hasq : (a : ℝ) ^ 2 ≤ 4 * (q : ℤ) := by
      have ha' : |(a : ℝ)| ≤ 2 * √(q : ℝ) := by
        rcases he with h | h <;> simpa [a, h] using ha
      have hpow := pow_le_pow_left₀ (abs_nonneg _) ha' 2
      rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at hpow
      push_cast
      linarith
    obtain ⟨α, β, hsum, hprod, hα, hβ⟩ := Hasse.exists_roots_of_sq_le a (q : ℤ) hasq
    simp only [Int.cast_natCast] at hα hβ
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hr : 0 < √(q : ℝ) := Real.sqrt_pos.2 hqR
    have hsq := Real.sq_sqrt hqR.le
    have hnprod : ‖α‖ * ‖β‖ = (q : ℝ) := by
      rw [← norm_mul, hprod]
      simp
    have hnα : ‖α‖ = √(q : ℝ) := by
      apply le_antisymm hα
      by_contra! h
      have hh := mul_le_mul_of_nonneg_left hβ (norm_nonneg α)
      have hlt := mul_lt_mul_of_pos_right h hr
      nlinarith
    have hnβ : ‖β‖ = √(q : ℝ) := by
      apply le_antisymm hβ
      by_contra! h
      rw [hnα] at hnprod
      have hlt := mul_lt_mul_of_pos_left h hr
      nlinarith
    have hfact : (1 - α * z) * (1 - β * z) = 0 := by
      rw [show (1 - α * z) * (1 - β * z) =
          1 - (α + β) * z + (α * β) * z ^ 2 by ring, hsum, hprod]
      simpa [Polynomial.IsRoot] using hz
    have hnz : √(q : ℝ) * ‖z‖ = 1 := by
      rcases mul_eq_zero.mp hfact with h | h
      · have h' := congrArg norm ((sub_eq_zero.mp h).symm)
        simpa [norm_mul, hnα] using h'
      · have h' := congrArg norm ((sub_eq_zero.mp h).symm)
        simpa [norm_mul, hnβ] using h'
    have hprod' : (q : ℝ) * ‖z‖ ^ 2 = 1 := by
      have hh := congrArg (fun x : ℝ => x ^ (2 : ℕ)) hnz
      change (√(q : ℝ) * ‖z‖) ^ (2 : ℕ) = (1 : ℝ) ^ (2 : ℕ) at hh
      rwa [mul_pow, hsq, one_pow] at hh
    rw [zpow_neg_one]
    exact (mul_eq_one_iff_eq_inv₀ hqR.ne').1 (by simpa [mul_comm] using hprod')

end ZInQ.Manuscript.RC.KatoP2.Checked
