import Mathlib

open Quaternion

namespace ZInQ.Contrib.CloudB3W13Trace

noncomputable section

private abbrev B6 := ℍ[ℚ, 2, -3]

private def qi : B6 := ⟨0, 1, 0, 0⟩
private def qj : B6 := ⟨0, 0, 1, 0⟩
private def qk : B6 := qi * qj

private theorem qi_qj_anticommute : qj * qi = -(qi * qj) := by
  ext <;> simp [qi, qj]

private theorem qj_qi_qj : qj * qi * qj = 3 • qi := by
  ext <;> norm_num [qi, qj]

private theorem qi_qj_qi : qi * qj * qi = -(2 • qj) := by
  ext <;> norm_num [qi, qj]

private theorem quaternion_decompose (x : B6) :
    x = (x.re : B6) + x.imI • qi + x.imJ • qj + x.imK • qk := by
  ext <;> simp [qi, qj, qk]

/-- The trace of every two-dimensional representation of `(2, -3 | ℚ)` is its reduced trace.

The `ℚ`-module and scalar-tower instances are the ordinary restriction-of-scalars data needed for
Mathlib's canonical `ℚ`-algebra structure on `Module.End K V`. -/
theorem quaternion_trace_dim_two
    (K V : Type*) [Field K] [CharZero K] [Algebra ℚ K]
    [AddCommGroup V] [Module K V] [Module ℚ V] [IsScalarTower ℚ K V]
    [SMulCommClass K ℚ V] [Module.Finite K V]
    (hdim : Module.finrank K V = 2)
    (ρ : ℍ[ℚ, 2, -3] →ₐ[ℚ] Module.End K V) (x : ℍ[ℚ, 2, -3]) :
    LinearMap.trace K V (ρ x) = algebraMap ℚ K (2 * x.re) := by
  have htr_i : LinearMap.trace K V (ρ qi) = 0 := by
    have hcycle := LinearMap.trace_mul_cycle K (ρ qj) (ρ qi) (ρ qj)
    rw [← map_mul, ← map_mul, qj_qi_qj, map_nsmul,
      ← map_mul, ← map_mul] at hcycle
    have hsq : qj * qj * qi = -(3 • qi) := by
      ext <;> norm_num [qi, qj]
    rw [hsq, map_neg, map_nsmul] at hcycle
    simp only [map_neg, map_nsmul] at hcycle
    norm_num [nsmul_eq_mul] at hcycle
    linear_combination (1 / 6 : K) * hcycle
  have htr_j : LinearMap.trace K V (ρ qj) = 0 := by
    have hcycle := LinearMap.trace_mul_cycle K (ρ qi) (ρ qj) (ρ qi)
    rw [← map_mul, ← map_mul, qi_qj_qi, map_neg, map_nsmul,
      ← map_mul, ← map_mul] at hcycle
    have hsq : qi * qi * qj = 2 • qj := by
      ext <;> norm_num [qi, qj]
    rw [hsq, map_nsmul] at hcycle
    simp only [map_neg, map_nsmul] at hcycle
    norm_num [nsmul_eq_mul] at hcycle
    linear_combination (-1 / 4 : K) * hcycle
  have htr_k : LinearMap.trace K V (ρ qk) = 0 := by
    have hcycle := LinearMap.trace_mul_comm K (ρ qi) (ρ qj)
    rw [← map_mul, ← map_mul, qi_qj_anticommute, map_neg] at hcycle
    have hcycle' : LinearMap.trace K V (ρ qk) = -LinearMap.trace K V (ρ qk) := by
      simpa [qk] using hcycle
    linear_combination (1 / 2 : K) * hcycle'
  have hscalar (q : ℚ) :
      ρ (q : B6) = algebraMap K (Module.End K V) (algebraMap ℚ K q) := by
    rw [show (q : B6) = algebraMap ℚ B6 q by rfl, ρ.commutes]
    ext v
    exact (IsScalarTower.algebraMap_smul K q v).symm
  have htrace_scalar (a : K) :
      LinearMap.trace K V (algebraMap K (Module.End K V) a) = 2 * a := by
    rw [Module.algebraMap_end_eq_smul_id, map_smul, LinearMap.trace_id, hdim]
    simp [mul_comm]
  conv_lhs => rw [quaternion_decompose x]
  simp [htr_i, htr_j, htr_k, hscalar, htrace_scalar]
  simp only [Algebra.smul_def, mul_zero, add_zero]

end

end ZInQ.Contrib.CloudB3W13Trace
