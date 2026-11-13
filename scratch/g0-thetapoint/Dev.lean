import Mathlib
import ZInQKernel.HDecomp.Analytic.QMLattice

/-! Development file (local copies of the definitions used by `part_theta.lean`). -/

noncomputable section
namespace DevTheta
open Complex

def IsSiegel (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  Ω.transpose = Ω ∧ (Ω.map Complex.im).PosDef

def IsPeriodMatrix (Λ : Submodule ℤ (Fin 2 → ℂ)) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ T : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ), ∀ z, z ∈ Λ ↔
    ∃ m n : Fin 2 → ℤ, T z = Ω.mulVec (fun i => (m i : ℂ)) + fun i => (n i : ℂ)

abbrev Char2 : Type := (Fin 2 → Fin 2) × (Fin 2 → Fin 2)

noncomputable def thetaConst (Ω : Matrix (Fin 2) (Fin 2) ℂ) (m : Char2) : ℂ :=
  ∑' n : Fin 2 → ℤ,
    Complex.exp (Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ
          Ω.mulVec (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2)) +
      2 * Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ (fun i => ((m.2 i : ℕ) : ℂ) / 2)))

noncomputable def absLogHeight {L : Type*} [Field L] [NumberField L] {J : Type*} [Finite J]
    (z : J → L) : ℝ :=
  Height.logHeight z / Module.finrank ℚ L

def evenChars : Finset Char2 :=
  Finset.univ.filter fun m => ((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ)) % 2 = 0

theorem card_evenChars : evenChars.card = 10 := by decide

/-! ### new -/

def jTheta (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  3779136 * (∏ m ∈ evenChars, thetaConst Ω m) ^ 4 / (∑ m ∈ evenChars, thetaConst Ω m ^ 8) ^ 5

def evenEnum : Fin 10 ≃ evenChars :=
  (evenChars.equivFin.trans (finCongr card_evenChars)).symm

theorem prod_evenEnum {R : Type*} [CommMonoid R] (g : Char2 → R) :
    ∏ i : Fin 10, g (evenEnum i) = ∏ m ∈ evenChars, g m := by
  rw [← Finset.prod_coe_sort]
  exact Equiv.prod_comp evenEnum (fun m : evenChars => g m)

theorem sum_evenEnum {R : Type*} [AddCommMonoid R] (g : Char2 → R) :
    ∑ i : Fin 10, g (evenEnum i) = ∑ m ∈ evenChars, g m := by
  rw [← Finset.sum_coe_sort]
  exact Equiv.sum_comp evenEnum (fun m : evenChars => g m)

theorem f1_of_theta {L : Type*} [Field L] [CharZero L] (emb : L →+* ℂ) (Ω : Matrix (Fin 2) (Fin 2) ℂ)
    (z : Char2 → L) (c : ℂ) (hc : c ≠ 0) (hz : ∀ m, emb (z m) = c * thetaConst Ω m) (q : ℚ)
    (hJ : jTheta Ω = (q : ℂ)) :
    3779136 * (∏ i, (fun i => z (evenEnum i)) i) ^ 4 /
      (∑ i, (fun i => z (evenEnum i)) i ^ 8) ^ 5 = algebraMap ℚ L q := by
  apply emb.injective
  rw [eq_ratCast (algebraMap ℚ L), map_ratCast, ← hJ]
  simp only [map_div₀, map_mul, map_pow, map_prod, map_sum, map_ofNat, hz]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [mul_pow]
  rw [← Finset.mul_sum, prod_evenEnum (fun m => thetaConst Ω m),
    sum_evenEnum (fun m => thetaConst Ω m ^ 8)]
  unfold jTheta
  set P := ∏ m ∈ evenChars, thetaConst Ω m
  set S := ∑ m ∈ evenChars, thetaConst Ω m ^ 8
  have h40 : c ^ 40 ≠ 0 := pow_ne_zero 40 hc
  calc 3779136 * ((c ^ 10) ^ 4 * P ^ 4) / (c ^ 8 * S) ^ 5
      = c ^ 40 * (3779136 * P ^ 4) / (c ^ 40 * S ^ 5) := by ring
    _ = 3779136 * P ^ 4 / S ^ 5 := mul_div_mul_left _ _ h40

theorem height_even {L : Type*} [Field L] [NumberField L] (z : Char2 → L) :
    Height.logHeight (fun i => z (evenEnum i)) / Module.finrank ℚ L ≤ absLogHeight z := by
  unfold absLogHeight
  exact div_le_div_of_nonneg_right (Height.logHeight_comp_le (fun i => (evenEnum i : Char2)) z)
    (Nat.cast_nonneg _)

theorem isPeriodMatrix_of_map {Λ Λ' : Submodule ℤ (Fin 2 → ℂ)} {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (h : IsPeriodMatrix Λ Ω) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hF : Λ.map (F.toLinearMap.restrictScalars ℤ) = Λ') : IsPeriodMatrix Λ' Ω := by
  obtain ⟨T, hT⟩ := h
  refine ⟨F.symm.trans T, fun z => ?_⟩
  have hz : z ∈ Λ' ↔ F.symm z ∈ Λ := by
    rw [← hF, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hy
      exact ⟨F.symm z, hy, by simp⟩
  rw [hz, hT]
  rfl

theorem isPeriodMatrix_of_comap {Λ Λ' : Submodule ℤ (Fin 2 → ℂ)} {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (h : IsPeriodMatrix Λ' Ω) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hF : Λ.map (F.toLinearMap.restrictScalars ℤ) = Λ') : IsPeriodMatrix Λ Ω := by
  refine isPeriodMatrix_of_map h F.symm ?_
  rw [← hF, ← Submodule.map_comp]
  convert Submodule.map_id Λ
  ext v
  simp

theorem isPeriodMatrix_qmLattice {τ : ℂ} (hτ : τ.im ≠ 0) :
    IsPeriodMatrix (BPAnalytic.QM.qmLattice hτ) (BPAnalytic.QM.Omega τ) :=
  isPeriodMatrix_of_map
    (⟨LinearEquiv.refl ℂ _, fun z => by
      simpa using BPAnalytic.mem_periodLattice_iff _ (BPAnalytic.QM.det_im_Omega_ne_zero hτ) z⟩)
    (BPAnalytic.QM.FpEquiv hτ).toLinearEquiv (BPAnalytic.QM.map_periodLattice_Omega hτ)

theorem isSiegel_Omega {τ : ℂ} (hτ : 0 < τ.im) : IsSiegel (BPAnalytic.QM.Omega τ) :=
  BPAnalytic.QM.Omega_mem_siegelSpace hτ

end DevTheta
