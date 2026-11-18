import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Lattice
import Mathlib.Data.Nat.Prime.Basic

/-!
# The determinant calculation on Fourier coefficients

Tex 9655–9662 and 9719–9729. The output is stated in the coefficient ring.
To lift it to the abstract residual lattice requires a separate comparison.
-/

namespace ZInQ.Manuscript.RC.TraceLimits

variable {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M]

/-- The correction coefficient from a sign ratio is integrally divisible by two,
before reducing modulo the maximal ideal (tex 9655–9659). -/
theorem diamond_correction_integral (b ψ η : O) (h : η = ψ ∨ η = -ψ) :
    ∃ c : O, (2 : O) * c = b * (ψ - η) := by
  rcases h with rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨b * ψ, by ring⟩

/-- Fourier coefficient formula for the weight-two good Hecke operator (tex 9660–9662).
The second term is zero at an index not divisible by the prime. -/
def HeckeFourier (coeff : ℕ → M →ₗ[O] O) (Tq Dq : M →ₗ[O] M) (q : ℕ) : Prop :=
  ∀ n v, coeff n (Tq v) =
    coeff (q * n) v + if q ∣ n then (q : O) * coeff (n / q) (Dq v) else 0

/-- Reduced support of `θ B_U[J] Θ_J`, since `θ ≡ 1` (tex 9706–9708, 9725–9727). -/
def UnaryFourier (m : Ideal O) (coeff : ℕ → M →ₗ[O] O) (J : ℕ) (C : M) : Prop :=
  ∀ n, (∀ k : ℕ, n ≠ J * k ^ 2) → coeff n C ∈ m

/-- Multiplying an index by a prime outside the index and the unary subscript
puts the new index outside the unary support. -/
theorem fresh_mul_ne_unary {q n J : ℕ} (hq : q.Prime) (hn : ¬ q ∣ n) (hJ : ¬ q ∣ J)
    (k : ℕ) : q * n ≠ J * k ^ 2 := by
  intro e
  have hd : q ∣ J * k ^ 2 := e ▸ dvd_mul_right q n
  have hk : q ∣ k := hq.dvd_of_dvd_pow ((hq.dvd_mul.1 hd).resolve_left hJ)
  obtain ⟨a, rfl⟩ := hk
  apply hn
  refine ⟨J * a ^ 2, Nat.eq_of_mul_eq_mul_left hq.pos ?_⟩
  calc
    q * n = J * (q * a) ^ 2 := e
    _ = q * (q * (J * a ^ 2)) := by ring

/-- The coefficient at `n` of a good trace of a unary correction vanishes modulo
`𝔪` if the prime avoids `nJ` (tex 9725–9727). -/
theorem unary_fresh_trace (m : Ideal O) {coeff : ℕ → M →ₗ[O] O} {Tq Dq : M →ₗ[O] M}
    {q n J : ℕ} {C : M} (hq : q.Prime) (hn : ¬ q ∣ n) (hJ : ¬ q ∣ J)
    (hT : HeckeFourier coeff Tq Dq q) (hC : UnaryFourier m coeff J C) :
    coeff n (Tq C) ∈ m := by
  rw [hT n C, ite_eq_right hn, add_zero]
  exact hC _ (fresh_mul_ne_unary hq hn hJ)

/-- The diamond correction formula on the integral module (tex 9719–9724).
Here the error term includes the scalar `r ψ_U(r) - 1` times the original form. -/
def DiamondCorrection (m : Ideal O) (Dr : M →ₗ[O] M) (r : ℕ) (F : M)
    (J : Finset ℕ) (C : ℕ → M) : Prop :=
  ∃ (E : M) (a : ℕ → O), E ∈ m • (⊤ : Submodule O M) ∧
    (r : O) • Dr F - F = E + ∑ j ∈ J, a j • C j

/-- The determinant discrepancy after a good trace has coefficient at `n` in
`𝔪` whenever the trace prime avoids that index and all unary subscripts.
This is the coefficientwise step of tex 9719–9729. -/
theorem diamond_fresh_trace_coeff (m : Ideal O) {coeff : ℕ → M →ₗ[O] O}
    {Tq Dq Dr : M →ₗ[O] M} {q r n : ℕ} {F : M} {J : Finset ℕ} {C : ℕ → M}
    (hq : q.Prime) (hn : ¬ q ∣ n) (hJ : ∀ j ∈ J, ¬ q ∣ j)
    (hT : HeckeFourier coeff Tq Dq q) (hC : ∀ j ∈ J, UnaryFourier m coeff j (C j))
    (hD : DiamondCorrection m Dr r F J C) :
    coeff n (Tq ((r : O) • Dr F - F)) ∈ m := by
  obtain ⟨E, a, hE, hDE⟩ := hD
  rw [hDE, map_add, map_add]
  apply Ideal.add_mem
  · have h : Submodule.map ((coeff n).comp Tq) (m • (⊤ : Submodule O M)) ≤ m := by
      rw [Submodule.map_smul'']
      exact (smul_mono_right _ le_top).trans (by simp)
    exact h ⟨E, hE, rfl⟩
  · simp only [map_sum, map_smul]
    exact m.sum_mem fun j hj => m.smul_mem _ (unary_fresh_trace m hq hn (hJ j hj) hT (hC j hj))

#print axioms diamond_correction_integral
#print axioms fresh_mul_ne_unary
#print axioms unary_fresh_trace
#print axioms diamond_fresh_trace_coeff

end ZInQ.Manuscript.RC.TraceLimits
