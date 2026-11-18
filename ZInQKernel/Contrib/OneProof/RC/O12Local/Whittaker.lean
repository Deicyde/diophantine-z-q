import ZInQKernel.Contrib.OneProof.RC.O12.Fourier
import ZInQKernel.Contrib.OneProof.RC.O12Local.Conductor

/-! The finite Whittaker comparison (tex 9841–9856). The normalization of
adelization is named here. The coefficient shift, including the auxiliary
right translation at primes away from (p), is proved from it. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Local

open Matrix

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

/-- At any other prime, the missing diagonal factor in the finite Whittaker
comparison is a level matrix with lower-right entry one. Provenance (c). -/
theorem away_diagonal_atK1 {p q : ℕ} [Fact q.Prime] (hp : p.Prime) (hqp : q ≠ p)
    (n : ℕ) :
    atK1 q n (upper (Units.mk0 (p : ℚ_[q]) (by exact_mod_cast hp.ne_zero)) 1 0) := by
  have hn : ‖(p : ℚ_[q])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((Nat.coprime_primes Fact.out hp).mpr hqp)
  refine ⟨?_, ?_, Or.inr ⟨?_, ?_⟩⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [upper, hn]
  · simp [upper, det_fin_two, hn]
  · simp [upper]
  · simp [upper]

/-- ELLIOT, tex 9841–9856: the Whittaker realization of vectors in the summand
under study. `away` records the away-from-(p) components of (a(n)).
At the other primes the element (a(p)) is a level matrix with lower right
entry one, and thus its right action on the Whittaker vector is trivial.
Only the evaluations of the additive character at the integral translations
in the coefficient-one calculation are needed. -/
structure WhittakerComparison (p : ℕ) (hp : p ≠ 0) (S : Set V)
    (H : V →ₗ[E] V) (coeff : O12.PosIndex → V → E) where
  Away : Type
  [awayGroup : Group Away]
  away : O12.PosIndex → Away
  away_one : away ⟨1, one_ne_zero⟩ = 1
  W : V → Matrix (Fin 2) (Fin 2) E → Away → E
  /-- The archimedean Whittaker function (y e^{-2pi y}) gives the factor (1/n). -/
  fourier : ∀ v ∈ S, ∀ n : O12.PosIndex,
    W v !![(n.val : E), 0; 0, 1] (away n) = coeff n v / (n.val : E)
  integral_translation : ∀ v ∈ S, ∀ b : Fin p,
    W v (!![1, (b.val : E); 0, 1] * !![(p : E), 0; 0, 1]) 1 =
      W v !![(p : E), 0; 0, 1] 1
  right_away : ∀ v ∈ S, ∀ g a, W v g (a * away ⟨p, hp⟩) = W v g a
  /-- Right translation realizes the local operator as the displayed finite sum. -/
  action_at_one : ∀ v ∈ S,
    W (H v) !![1, 0; 0, 1] 1 =
      ∑ b : Fin p, W v (!![1, 0; 0, 1] * !![(p : E), (b.val : E); 0, 1]) 1

attribute [instance] WhittakerComparison.awayGroup

/-- After the finite sum, translating the away components gives the Whittaker
coefficient at (p); its factor (1/p) cancels the number of cosets. -/
theorem WhittakerComparison.coeff_shift [CharZero E] {p : ℕ} {hp : p ≠ 0} {S : Set V}
    {H : V →ₗ[E] V} {coeff : O12.PosIndex → V → E}
    (D : WhittakerComparison p hp S H coeff) {v : V} (hv : v ∈ S) (hHv : H v ∈ S) :
    coeff ⟨1, one_ne_zero⟩ (H v) = coeff ⟨p, hp⟩ v := by
  have h1 := D.fourier (H v) hHv ⟨1, one_ne_zero⟩
  simp only [Nat.cast_one, div_one, D.away_one] at h1
  have hsum := O12.whittaker_sum (fun m => D.W v m 1) p 1 (by
    simpa only [one_mul] using D.integral_translation v hv)
  simp only [one_mul] at hsum
  have hpW := D.fourier v hv ⟨p, hp⟩
  have haway := D.right_away v hv !![(p : E), 0; 0, 1] 1
  rw [one_mul] at haway
  rw [← h1, D.action_at_one v hv, hsum, ← haway, hpW]
  field_simp [Nat.cast_ne_zero.mpr hp]

#print axioms away_diagonal_atK1
#print axioms WhittakerComparison.coeff_shift

end ZInQ.Manuscript.RC.O12Local
