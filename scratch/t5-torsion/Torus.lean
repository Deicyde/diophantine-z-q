import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Data.ZMod.Basic

/-!
# t5-torsion, part 2: `n`-torsion of a group uniformized by `E / Λ`

If `Φ : E → P` is a surjective homomorphism (written multiplicatively on `P`) with kernel a full
lattice `Λ` of the real space `E`, then `P` has exactly `n ^ dim_ℝ E` elements `x` with `xⁿ = 1`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace T5Torsion

open Module

section Torus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
  {P : Type*} [Group P] (Φ : E → P)

theorem map_nsmul_of_add (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (n : ℕ) (z : E) :
    Φ (n • z) = Φ z ^ n := by
  have h0 : Φ 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

theorem eq_iff_sub_mem (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
    (z w : E) : Φ z = Φ w ↔ z - w ∈ Λ := by
  rw [← hker]
  have h := hadd (z - w) w
  rw [sub_add_cancel] at h
  constructor
  · intro hzw
    rw [hzw] at h
    exact (mul_eq_right.mp h.symm)
  · intro h1
    rw [h, h1, one_mul]

/-- Membership in `Λ` through the coordinates in a `ℤ`-basis of `Λ`. -/
theorem mem_iff_repr {ι : Type*} (b : Basis ι ℤ Λ) (z : E) :
    z ∈ Λ ↔ ∀ i, (b.ofZLatticeBasis ℝ Λ).repr z i ∈ Set.range (algebraMap ℤ ℝ) := by
  conv_lhs => rw [← b.ofZLatticeBasis_span ℝ]
  exact (b.ofZLatticeBasis ℝ Λ).mem_span_iff_repr_mem ℤ z

/-- **Torsion of a uniformized group.** -/
theorem natCard_pow_eq_one (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w)
    (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ) (hsurj : Function.Surjective Φ) (n : ℕ) (hn : 0 < n) :
    Nat.card {x : P // x ^ n = 1} = n ^ finrank ℝ E := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  have : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  have : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  let ι := Module.Free.ChooseBasisIndex ℤ Λ
  let B := b.ofZLatticeBasis ℝ Λ
  have hBi (i : ι) : B i ∈ Λ := by
    rw [show B i = b i from b.ofZLatticeBasis_apply ℝ Λ i]
    exact (b i).2
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let zc : (ι → ZMod n) → E := fun c => ∑ i, (((c i).val : ℝ) / n) • B i
  have hrepr (c : ι → ZMod n) (i : ι) : B.repr (zc c) i = ((c i).val : ℝ) / n := by
    simp [zc, Finsupp.single_apply]
  let f : (ι → ZMod n) → {x : P // x ^ n = 1} := fun c => ⟨Φ (zc c), by
    rw [← map_nsmul_of_add Φ hadd, hker, mem_iff_repr Λ b]
    intro i
    refine ⟨((c i).val : ℤ), ?_⟩
    rw [map_nsmul, Finsupp.smul_apply, hrepr, nsmul_eq_mul]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_natCast]
    field_simp⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c c' h
      have h1 : Φ (zc c) = Φ (zc c') := congrArg Subtype.val h
      rw [eq_iff_sub_mem Λ Φ hadd hker, mem_iff_repr Λ b] at h1
      funext i
      obtain ⟨m, hm⟩ := h1 i
      rw [map_sub, Finsupp.sub_apply, hrepr, hrepr] at hm
      simp only [algebraMap_int_eq, eq_intCast] at hm
      have hlt := ZMod.val_lt (c i)
      have hlt' := ZMod.val_lt (c' i)
      have hm' : (m : ℝ) * n = (c i).val - (c' i).val := by
        rw [hm]; field_simp
      have hmZ : m * (n : ℤ) = ((c i).val : ℤ) - (c' i).val := by exact_mod_cast hm'
      have hm0 : m = 0 := by
        rcases lt_trichotomy m 0 with h | h | h
        · nlinarith
        · exact h
        · nlinarith
      rw [hm0, zero_mul] at hmZ
      exact ZMod.val_injective n (by omega)
    · rintro ⟨x, hx⟩
      obtain ⟨z, rfl⟩ := hsurj x
      have h1 : Φ (n • z) = 1 := by rw [map_nsmul_of_add Φ hadd, hx]
      rw [hker, mem_iff_repr Λ b] at h1
      choose m hm using h1
      refine ⟨fun i => (m i : ZMod n), Subtype.ext ?_⟩
      change Φ (zc _) = Φ z
      rw [eq_iff_sub_mem Λ Φ hadd hker, mem_iff_repr Λ b]
      intro i
      refine ⟨-(m i / n), ?_⟩
      have hmi := hm i
      rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul] at hmi
      simp only [algebraMap_int_eq, eq_intCast] at hmi ⊢
      rw [map_sub, Finsupp.sub_apply, hrepr]
      have hv : (((m i : ZMod n)).val : ℤ) = m i % n := ZMod.val_intCast (m i)
      have hv' : ((((m i : ZMod n)).val : ℕ) : ℝ) = ((m i % n : ℤ) : ℝ) := by exact_mod_cast hv
      rw [hv']
      have hdiv : ((m i % n : ℤ) : ℝ) = (m i : ℝ) - n * ((m i / n : ℤ) : ℝ) := by
        have := Int.emod_def (m i) n
        rw [this]; push_cast; ring
      rw [hdiv, hmi]
      field_simp
      push_cast
      ring
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_fun, Nat.card_zmod,
    Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis B]

end Torus

theorem finrank_real_fin_complex (g : ℕ) : finrank ℝ (Fin g → ℂ) = 2 * g := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

end T5Torsion

#print axioms T5Torsion.natCard_pow_eq_one
