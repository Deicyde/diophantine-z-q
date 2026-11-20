import ZInQKernel.Contrib.OneProof.RC.X0Model.Chart
import ZInQKernel.Contrib.CloudB3RC53.Prints.CST
import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.PrincipalIdealDomain

/-! The two Heegner period lattices and their orientation, tex 2915–2916.
On-the-spot calculation (c). -/

noncomputable section

open ZInQ.Contrib.CloudB3RC53.CST UpperHalfPlane Complex
open scoped Pointwise

namespace ZInQ.Manuscript.RC.CMField2

/-- The formula for the chosen upper half-plane root when the leading coefficient is positive. -/
theorem coe_cmPoint_of_neg {A B d : ℤ} (hA : 0 < A) (hd : d < 0) :
    (cmPoint A B d : ℂ) =
      (-(B : ℂ) + Complex.I * (Real.sqrt (-(d : ℝ)) : ℂ)) / (2 * (A : ℂ)) := by
  have ha : (0 : ℝ) < A := by exact_mod_cast hA
  have hsq : 0 < Real.sqrt (-(d : ℝ)) := Real.sqrt_pos.2 (by exact_mod_cast neg_pos.mpr hd)
  have hz : 0 < ((-(B : ℂ) + Complex.I * (Real.sqrt (-(d : ℝ)) : ℂ)) /
      (2 * (A : ℂ))).im := by
    rw [show (2 : ℂ) * (A : ℂ) = ((2 * (A : ℝ) : ℝ) : ℂ) by norm_cast, Complex.div_ofReal_im]
    have h2A : (0 : ℝ) < 2 * (A : ℝ) := mul_pos (by norm_num) ha
    simpa [Complex.mul_im] using div_pos hsq h2A
  simp [cmPoint, hz]

/-- The middle coefficient is prime to the level. -/
theorem heegner_middle_coprime {N : ℕ} {d A B C : ℤ}
    (hcop : IsCoprime d (N : ℤ)) (hform : IsHeegnerForm N d A B C) :
    IsCoprime B (N : ℤ) := by
  obtain ⟨u, v, h⟩ := hcop
  obtain ⟨k, hk⟩ := hform.2.1
  refine ⟨u * B, v - 4 * u * k * C, ?_⟩
  rw [← hform.2.2.1, hk] at h
  linear_combination h

/-- Scaling the parameter gives the form [A/N,B,NC], with the same
discriminant and primitive coefficients. -/
theorem heegner_scaled_form {N : ℕ} [NeZero N] {d A B C : ℤ}
    (hcop : IsCoprime d (N : ℤ)) (hform : IsHeegnerForm N d A B C) :
    ∃ a : ℤ, A = (N : ℤ) * a ∧ IsHeegnerForm 1 d a B ((N : ℤ) * C) := by
  obtain ⟨a, ha⟩ := hform.2.1
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hap : 0 < a := by
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hN.le hn)) (ha ▸ hform.1)
  refine ⟨a, ha, hap, one_dvd a, ?_, ?_⟩
  · rw [← hform.2.2.1, ha]
    ring
  · let g := Int.gcd (Int.gcd a B : ℤ) ((N : ℤ) * C)
    change g = 1
    have hgAB : (g : ℤ) ∣ (Int.gcd a B : ℤ) := Int.gcd_dvd_left _ _
    have hgB : (g : ℤ) ∣ B := hgAB.trans (Int.gcd_dvd_right _ _)
    have hgA : (g : ℤ) ∣ A := by
      rw [ha]
      exact (hgAB.trans (Int.gcd_dvd_left _ _)).mul_left _
    have hgNC : (g : ℤ) ∣ (N : ℤ) * C := Int.gcd_dvd_right _ _
    have hgC : (g : ℤ) ∣ C := ((heegner_middle_coprime hcop hform).of_isCoprime_of_dvd_left
      hgB).dvd_of_dvd_mul_left hgNC
    have h1 := Int.dvd_gcd (Int.dvd_coe_gcd hgA hgB) hgC
    rw [hform.2.2.2] at h1
    exact Nat.dvd_one.mp h1

abbrev pairLattice {K : Type*} [Field K] (a : ℤ) (ω : K) : Submodule ℤ K :=
  Submodule.span ℤ ({(a : K), ω} : Set K)

private theorem int_mem_pairLattice {K : Type*} [Field K] (a : ℤ) (ω : K) :
    (a : K) ∈ pairLattice a ω := Submodule.subset_span (by simp)

private theorem omega_mem_pairLattice {K : Type*} [Field K] (a : ℤ) (ω : K) :
    ω ∈ pairLattice a ω := Submodule.subset_span (by simp)

/-- The oriented level ideal times the second lattice is the first lattice.
This is the equality of underlying ℤ-lattices, before comparing with the Picard group. -/
theorem heegner_pairLattice_mul {K : Type*} [Field K] {N A B C a : ℤ} (ω : K)
    (ha : A = N * a) (hcop : IsCoprime N B)
    (hω : ω ^ 2 + (B : K) * ω + (A : K) * (C : K) = 0) :
    pairLattice N ω * pairLattice a ω = pairLattice A ω := by
  have hmul : (N : K) * (a : K) = (A : K) := by
    simpa only [Int.cast_mul] using congrArg (fun z : ℤ => (z : K)) ha.symm
  have hs : (A : K) ∈ pairLattice N ω * pairLattice a ω := by
    rw [← hmul]
    exact Submodule.mul_mem_mul (int_mem_pairLattice N ω) (int_mem_pairLattice a ω)
  have hnω : (N : K) * ω ∈ pairLattice N ω * pairLattice a ω :=
    Submodule.mul_mem_mul (int_mem_pairLattice N ω) (omega_mem_pairLattice a ω)
  have hωω : ω * ω ∈ pairLattice N ω * pairLattice a ω :=
    Submodule.mul_mem_mul (omega_mem_pairLattice N ω) (omega_mem_pairLattice a ω)
  refine le_antisymm ?_ (Submodule.span_le.mpr ?_)
  · change Submodule.span ℤ ({(N : K), ω} : Set K) *
      Submodule.span ℤ ({(a : K), ω} : Set K) ≤ pairLattice A ω
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro z ⟨x, hx, y, hy, hz⟩
    change x * y = z at hz
    rw [← hz]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
    · rw [hmul]; exact int_mem_pairLattice A ω
    · rw [← zsmul_eq_mul]; exact (pairLattice A ω).smul_mem N (omega_mem_pairLattice A ω)
    · rw [mul_comm, ← zsmul_eq_mul]; exact (pairLattice A ω).smul_mem a (omega_mem_pairLattice A ω)
    · have hr : ω * ω = (-B) • ω + (-C) • (A : K) := by
        simp only [zsmul_eq_mul, Int.cast_neg]
        linear_combination hω
      rw [hr]
      exact (pairLattice A ω).add_mem
        ((pairLattice A ω).smul_mem _ (omega_mem_pairLattice A ω))
        ((pairLattice A ω).smul_mem _ (int_mem_pairLattice A ω))
  · intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hz | hz <;> rw [hz]
    · exact hs
    · have hb : (B : K) * ω ∈ pairLattice N ω * pairLattice a ω := by
        have he : (B : K) * ω = -(ω * ω) - C • (A : K) := by
          rw [zsmul_eq_mul]
          linear_combination hω
        rw [he]
        exact Submodule.sub_mem _ (Submodule.neg_mem _ hωω) (Submodule.smul_mem _ _ hs)
      obtain ⟨u, v, huv⟩ := hcop
      have hz : u • ((N : K) * ω) + v • ((B : K) * ω) = ω := by
        simp only [zsmul_eq_mul]
        have hh : (u : K) * (N : K) + (v : K) * (B : K) = 1 := by
          simpa only [Int.cast_mul, Int.cast_add, Int.cast_one] using congrArg (fun z : ℤ => (z : K)) huv
        linear_combination ω * hh
      have hh : u • ((N : K) * ω) + v • ((B : K) * ω) ∈ pairLattice N ω * pairLattice a ω :=
        Submodule.add_mem _ (Submodule.smul_mem _ _ hnω) (Submodule.smul_mem _ _ hb)
      rwa [hz] at hh

/-- The analytic scaling of a Heegner parameter is exactly the root
of the scaled form. -/
theorem dilate_cmPoint_eq {N : ℕ} [NeZero N] {A a B d : ℤ}
    (hA : 0 < A) (ha : A = (N : ℤ) * a) (hd : d < 0) :
    X0Model.dilate N (cmPoint A B d) = cmPoint a B d := by
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hap : 0 < a := by
    by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hN.le hn)) (ha ▸ hA)
  apply UpperHalfPlane.coe_injective
  change (N : ℂ) * (cmPoint A B d : ℂ) = (cmPoint a B d : ℂ)
  rw [coe_cmPoint_of_neg hA hd, coe_cmPoint_of_neg hap hd, ha, Int.cast_mul, Int.cast_natCast]
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast hap.ne'
  field_simp


end ZInQ.Manuscript.RC.CMField2
