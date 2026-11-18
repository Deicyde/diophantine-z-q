import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# One-dimensional rectangular theta products: lattice and phase arithmetic

These lemmas concern only the actual one-dimensional grid of real translates.
No square-grid distribution, multiplication identity or quotient constancy is
among the hypotheses of the lattice and automorphy calculations.
-/

noncomputable section

open Complex Set Function Finset
open scoped Real UpperHalfPlane BigOperators Topology

namespace RectangularThetaLattice

local notation "κ" => ((Real.pi : ℂ) * Complex.I)

/-- Multiplication of the upper-half-plane parameter by a positive degree. -/
def upTau (n : ℕ) (hn : 0 < n) (τ : ℍ) : ℍ :=
  ⟨(n : ℂ) * (τ : ℂ), by simpa using mul_pos (show (0 : ℝ) < n by exact_mod_cast hn) τ.im_pos⟩

/-- Division of the upper-half-plane parameter by a positive degree. -/
def downTau (n : ℕ) (hn : 0 < n) (τ : ℍ) : ℍ :=
  ⟨(τ : ℂ) / (n : ℂ), by simpa using div_pos τ.im_pos (show (0 : ℝ) < n by exact_mod_cast hn)⟩

lemma upTau_coe (n : ℕ) (hn : 0 < n) (τ : ℍ) : (upTau n hn τ : ℂ) = (n : ℂ) * τ := rfl
lemma downTau_coe (n : ℕ) (hn : 0 < n) (τ : ℍ) : (downTau n hn τ : ℂ) = (τ : ℂ) / n := rfl

/-- Exactly n real translates, rather than n² full-lattice translates. -/
def realProduct (n : ℕ) (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∏ b : Fin n, H (z + (b : ℂ) / (n : ℂ))

lemma realProduct_differentiable (n : ℕ) {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    Differentiable ℂ (realProduct n H) := by unfold realProduct; fun_prop

lemma quasi_nat_one {H : ℂ → ℂ} (h1 : ∀ z, H (z + 1) = -H z) (n : ℕ) (z : ℂ) :
    H (z + (n : ℂ)) = (-1 : ℂ) ^ n * H z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show z + ((n+1 : ℕ) : ℂ) = (z + (n : ℂ)) + 1 by push_cast; ring, h1, ih, pow_succ]
    ring

lemma sum_real_indices (n : ℕ) : (∑ b : Fin n, (b : ℂ)) = (n : ℂ) * ((n-1 : ℕ) : ℂ) / 2 := by
  have hh : (∑ b : Fin n, (b : ℕ)) * 2 = n * (n-1) := by
    rw [Fin.sum_univ_eq_sum_range (fun b : ℕ => b) n]
    exact Finset.sum_range_id_mul_two n
  have hc : (∑ b : Fin n, (b : ℂ)) * 2 = (n : ℂ) * ((n-1 : ℕ) : ℂ) := by exact_mod_cast hh
  linear_combination (1/2 : ℂ) * hc

lemma realProduct_one (n : ℕ) {H : ℂ → ℂ} (h1 : ∀ z, H (z + 1) = -H z) (z : ℂ) :
    realProduct n H (z + 1) = (-1 : ℂ) ^ n * realProduct n H z := by
  have hshift (b : Fin n) : H ((z + 1) + (b : ℂ) / n) = (-1 : ℂ) * H (z + (b : ℂ) / n) := by
    rw [show (z + 1) + (b : ℂ) / n = (z + (b : ℂ) / n) + 1 by ring, h1]
    ring
  unfold realProduct
  simp_rw [hshift]
  rw [Finset.prod_mul_distrib, Fin.prod_const]

/-- The exact τ automorphy of the one-dimensional real grid; the constant
phase is retained until the actual exponential identity is applied. -/
lemma realProduct_tau {n : ℕ} (hn : 0 < n) {H : ℂ → ℂ} (τ : ℍ)
    (hτ : ∀ z, H (z + (τ : ℂ)) = -cexp (-κ * (τ : ℂ) - 2 * κ * z) * H z) (z : ℂ) :
    realProduct n H (z + (τ : ℂ)) =
      -cexp (-κ * (n : ℂ) * (τ : ℂ) - 2 * κ * (n : ℂ) * z) * realProduct n H z := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hphase (b : Fin n) : H ((z + (τ : ℂ)) + (b : ℂ) / n) =
      cexp (κ - κ * (τ : ℂ) - 2 * κ * (z + (b : ℂ) / n)) * H (z + (b : ℂ) / n) := by
    rw [show (z + (τ : ℂ)) + (b : ℂ) / n = (z + (b : ℂ) / n) + (τ : ℂ) by ring, hτ]
    rw [show κ - κ * (τ : ℂ) - 2 * κ * (z + (b : ℂ) / n) =
      κ + (-κ * (τ : ℂ) - 2 * κ * (z + (b : ℂ) / n)) by ring, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have hsum : (∑ b : Fin n, (κ - κ * (τ : ℂ) - 2 * κ * (z + (b : ℂ) / n))) =
      κ + (-κ * (n : ℂ) * (τ : ℂ) - 2 * κ * (n : ℂ) * z) := by
    simp_rw [show ∀ b : Fin n, κ - κ * (τ : ℂ) - 2 * κ * (z + (b : ℂ) / n) =
      (κ - κ * (τ : ℂ) - 2 * κ * z) - (2 * κ / (n : ℂ)) * (b : ℂ) from fun b => by ring]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_real_indices]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
    field_simp [hnC]
    ring
  unfold realProduct
  simp_rw [hphase]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hsum, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- The zero divisor of the real-shift product is exactly the rectangular
lattice scaled by n. Integer residues are guarded before conversion. -/
theorem realProduct_zero_iff {n : ℕ} (hn : 0 < n) {H : ℂ → ℂ} (τ : ℍ)
    (hzero : ∀ z, H z = 0 ↔ ∃ a b : ℤ, z = (a : ℂ) + (b : ℂ) * (τ : ℂ)) (z : ℂ) :
    realProduct n H z = 0 ↔
      ∃ a b : ℤ, (n : ℂ) * z = (a : ℂ) + (b : ℂ) * ((n : ℂ) * (τ : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  simp only [realProduct, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨a,b,hab⟩ := (hzero _).mp hj
    refine ⟨(n : ℤ) * a - (j : ℕ), b, ?_⟩
    push_cast
    field_simp [hnC] at hab
    linear_combination hab
  · rintro ⟨a,b,hab⟩
    have hrem0 := Int.emod_nonneg (-a) hnZ.ne'
    have hremn := Int.emod_lt_of_pos (-a) hnZ
    let j : Fin n := ⟨((-a) % (n : ℤ)).toNat, by omega⟩
    have hj : (j : ℂ) = (((-a) % (n : ℤ) : ℤ) : ℂ) := by
      exact_mod_cast Int.toNat_of_nonneg hrem0
    have hdiv : (((-a) / (n : ℤ) : ℤ) : ℂ) * (n : ℂ) +
        (((-a) % (n : ℤ) : ℤ) : ℂ) = -(a : ℂ) := by exact_mod_cast Int.ediv_mul_add_emod (-a) n
    refine ⟨j,(hzero _).mpr ⟨-((-a)/(n : ℤ)),b,?_⟩⟩
    rw [hj]
    push_cast
    apply (mul_right_inj' hnC).mp
    field_simp [hnC]
    linear_combination hab + hdiv

/-- Exactly n imaginary-direction translates. -/
def imagProduct (n : ℕ) (τ : ℍ) (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∏ a : Fin n, H (z+(a : ℂ)*(τ : ℂ)/(n : ℂ))

lemma imagProduct_differentiable (n : ℕ) (τ : ℍ) {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    Differentiable ℂ (imagProduct n τ H) := by unfold imagProduct; fun_prop

lemma quasi_nat_tau {H : ℂ → ℂ} (τ : ℍ)
    (ht : ∀ z,H (z+(τ : ℂ))=-cexp (-κ*(τ : ℂ)-2*κ*z)*H z) (m : ℕ) (z : ℂ) :
    H (z+(m : ℂ)*(τ : ℂ)) = (-1 : ℂ)^m * cexp (-κ*(m : ℂ)^2*(τ : ℂ)-2*κ*(m : ℂ)*z)*H z := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show z+((m+1 : ℕ) : ℂ)*(τ : ℂ)=(z+(m : ℂ)*(τ : ℂ))+(τ : ℂ) by push_cast;ring,ht,ih]
    have he : (-κ*(τ : ℂ)-2*κ*(z+(m : ℂ)*(τ : ℂ)))+
      (-κ*(m : ℂ)^2*(τ : ℂ)-2*κ*(m : ℂ)*z)=
      -κ*((m+1 : ℕ) : ℂ)^2*(τ : ℂ)-2*κ*((m+1 : ℕ) : ℂ)*z := by push_cast;ring
    calc
      _ = (-1 : ℂ)^(m+1)*(cexp (-κ*(τ : ℂ)-2*κ*(z+(m : ℂ)*(τ : ℂ)))*
        cexp (-κ*(m : ℂ)^2*(τ : ℂ)-2*κ*(m : ℂ)*z))*H z := by rw [pow_succ];ring
      _ = _ := by rw [← Complex.exp_add,he]

lemma imagProduct_one (n : ℕ) (τ : ℍ) {H : ℂ → ℂ} (h1 : ∀ z,H (z+1)=-H z) (z : ℂ) :
    imagProduct n τ H (z+1)=(-1 : ℂ)^n*imagProduct n τ H z := by
  have hh (a : Fin n) : H ((z+1)+(a : ℂ)*(τ : ℂ)/n)=(-1 : ℂ)*H (z+(a : ℂ)*(τ : ℂ)/n) := by
    rw [show (z+1)+(a : ℂ)*(τ : ℂ)/n=(z+(a : ℂ)*(τ : ℂ)/n)+1 by ring,h1]
    ring
  unfold imagProduct
  simp_rw [hh]
  rw [Finset.prod_mul_distrib,Fin.prod_const]

lemma imagProduct_tau {n : ℕ} (hn : 0<n) (τ : ℍ) {H : ℂ → ℂ}
    (ht : ∀ z,H (z+(τ : ℂ))=-cexp (-κ*(τ : ℂ)-2*κ*z)*H z) (z : ℂ) :
    imagProduct n τ H (z+(τ : ℂ))=(-1 : ℂ)^n *
      cexp (-κ*(2*(n : ℂ)-1)*(τ : ℂ)-2*κ*(n : ℂ)*z)*imagProduct n τ H z := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  have hh (a : Fin n) : H ((z+(τ : ℂ))+(a : ℂ)*(τ : ℂ)/n) =
      (-1 : ℂ)*cexp (-κ*(τ : ℂ)-2*κ*(z+(a : ℂ)*(τ : ℂ)/n))*H (z+(a : ℂ)*(τ : ℂ)/n) := by
    rw [show (z+(τ : ℂ))+(a : ℂ)*(τ : ℂ)/n=(z+(a : ℂ)*(τ : ℂ)/n)+(τ : ℂ) by ring,ht]
    ring
  have hsum : (∑ a : Fin n,(-κ*(τ : ℂ)-2*κ*(z+(a : ℂ)*(τ : ℂ)/n)))=
      -κ*(2*(n : ℂ)-1)*(τ : ℂ)-2*κ*(n : ℂ)*z := by
    simp_rw [show ∀ a : Fin n,-κ*(τ : ℂ)-2*κ*(z+(a : ℂ)*(τ : ℂ)/n)=
      (-κ*(τ : ℂ)-2*κ*z)-(2*κ*(τ : ℂ)/(n : ℂ))*(a : ℂ) from fun a => by ring]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum,sum_real_indices]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [Nat.cast_sub (show 1≤n by omega),Nat.cast_one]
    field_simp [hnC]
    ring
  unfold imagProduct
  simp_rw [hh,Finset.prod_mul_distrib]
  rw [Fin.prod_const,← Complex.exp_sum,hsum]

/-- The imaginary rectangular grid has exactly the divided-period lattice zeros. -/
theorem imagProduct_zero_iff {n : ℕ} (hn : 0<n) (τ : ℍ) {H : ℂ → ℂ}
    (hzero : ∀ z,H z=0 ↔ ∃ a b : ℤ,z=(a : ℂ)+(b : ℂ)*(τ : ℂ)) (z : ℂ) :
    imagProduct n τ H z=0 ↔ ∃ a b : ℤ,z=(a : ℂ)+(b : ℂ)*(downTau n hn τ : ℂ) := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  have hnZ : (0 : ℤ)<n := by exact_mod_cast hn
  simp only [imagProduct,Finset.prod_eq_zero_iff,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj⟩
    obtain ⟨a,b,hab⟩ := (hzero _).mp hj
    refine ⟨a,(n : ℤ)*b-(j : ℕ),?_⟩
    rw [downTau_coe]
    push_cast
    field_simp [hnC] at hab ⊢
    linear_combination hab
  · rintro ⟨a,b,hab⟩
    have hrem0 := Int.emod_nonneg (-b) hnZ.ne'
    have hremn := Int.emod_lt_of_pos (-b) hnZ
    let j : Fin n := ⟨((-b)%(n : ℤ)).toNat,by omega⟩
    have hj : (j : ℂ)=(((-b)%(n : ℤ) : ℤ) : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hrem0
    have hdiv : (((-b)/(n : ℤ) : ℤ) : ℂ)*(n : ℂ)+(((-b)%(n : ℤ) : ℤ) : ℂ)=-(b : ℂ) := by
      exact_mod_cast Int.ediv_mul_add_emod (-b) n
    refine ⟨j,(hzero _).mpr ⟨a,-((-b)/(n : ℤ)),?_⟩⟩
    rw [downTau_coe] at hab
    rw [hj]
    push_cast
    field_simp [hnC] at hab ⊢
    linear_combination hab + (τ : ℂ)*hdiv

end RectangularThetaLattice
