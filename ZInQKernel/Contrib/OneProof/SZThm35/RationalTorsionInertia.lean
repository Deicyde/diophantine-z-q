import ZInQKernel.Contrib.OneProof.SZThm35.SerreUnipotence
import ZInQKernel.Contrib.CloudR2CM.SerreTate.RigidityProof
import ZInQKernel.Contrib.OneProof.SZThm33.FiniteInertiaFixed
import ZInQKernel.Contrib.OneProof.SZThm33.RationalFixedTate
import Mathlib.Data.Nat.Factorization.Basic

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open ReductSplit HDec.CMSerreTate

namespace SZRaynaud

/-- Every integer at least three has a prime-power divisor at least three. -/
theorem exists_prime_pow_dvd_of_three_le {m : ℕ} (hm : 3 ≤ m) :
    ∃ ℓ k : ℕ, ℓ.Prime ∧ 3 ≤ ℓ ^ k ∧ ℓ ^ k ∣ m := by
  obtain ⟨k, r, hr, hkr⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (by omega : m ≠ 0) 2 (by decide)
  by_cases hr₁ : r = 1
  · rw [hr₁, mul_one] at hkr
    exact ⟨2, k, Nat.prime_two, hkr ▸ hm, hkr ▸ dvd_rfl⟩
  · obtain ⟨ℓ, hℓ, hd⟩ := Nat.exists_prime_and_dvd hr₁
    have hℓ₃ : 3 ≤ ℓ := by
      have hℓ₂ := hℓ.two_le
      by_contra! h
      have h₂ : ℓ = 2 := by omega
      exact hr (h₂ ▸ hd)
    refine ⟨ℓ, 1, hℓ, by simpa only [pow_one] using hℓ₃, ?_⟩
    rw [pow_one, hkr]
    exact hd.trans (dvd_mul_left _ _)

/-- The displacement of a power of a square-zero unipotent is the corresponding
integer multiple of the original displacement. -/
theorem pow_sub_one_eq_nsmul_of_sub_sq_eq_zero {R : Type*} [Ring R]
    {g : R} (hg : (g - 1) ^ 2 = 0) (n : ℕ) :
    g ^ n - 1 = n • (g - 1) := by
  have hfix : (g - 1) * g = g - 1 := by
    have hdiff : (g - 1) * g - (g - 1) = (g - 1) ^ 2 := by rw [pow_two, mul_sub, mul_one]
    exact sub_eq_zero.mp (hdiff.trans hg)
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      g ^ (n + 1) - 1 = (g ^ n - 1) * g + (g - 1) := by rw [pow_succ, sub_mul, one_mul]; abel
      _ = (n + 1) • (g - 1) := by rw [ih, smul_mul_assoc, hfix, succ_nsmul]

/-- Once both displacements square to zero, their mixed product vanishes
if the mixed product for any positive powers does. -/
theorem displacement_mul_eq_zero_of_positive_powers
    {F V : Type*} [Field F] [CharZero F] [AddCommGroup V] [Module F V]
    {g h : Module.End F V}
    (hg : (g - 1) ^ 2 = 0) (hh : (h - 1) ^ 2 = 0)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hp : (h ^ m - 1) * (g ^ n - 1) = 0) :
    (h - 1) * (g - 1) = 0 := by
  rw [pow_sub_one_eq_nsmul_of_sub_sq_eq_zero hg,
    pow_sub_one_eq_nsmul_of_sub_sq_eq_zero hh, smul_mul_assoc, mul_smul_comm] at hp
  have hzero : ((m : F) * (n : F)) • ((h - 1) * (g - 1)) = 0 := by
    rwa [mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hu : ((m : F) * (n : F)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr hm.ne') (Nat.cast_ne_zero.mpr hn.ne')
  exact (smul_eq_zero.mp hzero).resolve_left hu

section Inertia

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (A : PkgI3.AbVar K) (w : ValuationSubring Ω) (E : IntermediateField K Ω)
  [FiniteDimensional K E] (ℓ : ℕ) [Fact ℓ.Prime]

private theorem galVΩ_pow (σ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    galVΩ A ℓ (σ ^ n) = galVΩ A ℓ σ ^ n := by
  change (galTΩ A ℓ (σ ^ n)).baseChange ℚ_[ℓ] = ((galTΩ A ℓ σ).baseChange ℚ_[ℓ]) ^ n
  rw [galTΩ_pow, LinearMap.baseChange_pow]

omit [FiniteDimensional K E] in
private theorem mixed_displacement_restrictScalars
    (hE : ∀ (σ : Ω ≃ₐ[E] Ω), PkgI2.IsInertia w σ → ∀ (τ : Ω ≃ₐ[E] Ω), PkgI2.IsInertia w τ →
      ∀ x : VΩ (A.baseChange E) Ω ℓ,
        galVΩ (A.baseChange E) ℓ τ (galVΩ (A.baseChange E) ℓ σ x - x) =
          galVΩ (A.baseChange E) ℓ σ x - x)
    (σ τ : Ω ≃ₐ[E] Ω) (hσ : PkgI2.IsInertia w σ) (hτ : PkgI2.IsInertia w τ) :
    (galVΩ A ℓ (τ.restrictScalars K) - 1) * (galVΩ A ℓ (σ.restrictScalars K) - 1) = 0 := by
  let e := intermediateRationalTateEquiv A E ℓ
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  have h₁ := intermediateRationalTateEquiv_action A E ℓ σ y
  have h₂ := intermediateRationalTateEquiv_action A E ℓ τ
    (galVΩ (A.baseChange E) ℓ σ y - y)
  change galVΩ A ℓ (τ.restrictScalars K) (galVΩ A ℓ (σ.restrictScalars K) (e y) - e y) -
    (galVΩ A ℓ (σ.restrictScalars K) (e y) - e y) = 0
  rw [← h₁, ← map_sub, ← h₂]
  exact sub_eq_zero.mpr (congrArg e (hE σ hσ τ hτ y))

/-- Rational prime-power torsion and two-factor unipotence over a finite extension
force two-factor unipotence on the original inertia group. -/
theorem levelTwo_of_fixed_primePower_torsion_of_finite_index (k : ℕ) (hk : 3 ≤ ℓ ^ k)
    (hfix : ∀ (σ : Ω ≃ₐ[K] Ω), PkgI2.IsInertia w σ →
      ∀ x : A.Pt Ω, x ^ (ℓ ^ k) = 1 → A.galAct σ x = x)
    (hE : ∀ (σ : Ω ≃ₐ[E] Ω), PkgI2.IsInertia w σ → ∀ (τ : Ω ≃ₐ[E] Ω), PkgI2.IsInertia w τ →
      ∀ x : VΩ (A.baseChange E) Ω ℓ,
        galVΩ (A.baseChange E) ℓ τ (galVΩ (A.baseChange E) ℓ σ x - x) =
          galVΩ (A.baseChange E) ℓ σ x - x) :
    ∀ (σ : Ω ≃ₐ[K] Ω), PkgI2.IsInertia w σ → ∀ (τ : Ω ≃ₐ[K] Ω), PkgI2.IsInertia w τ →
      ∀ x : VΩ A Ω ℓ, galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x := by
  let b := Module.End.baseChangeHom ℤ_[ℓ] ℚ_[ℓ] (TΩ A Ω ℓ)
  have hb (σ : Ω ≃ₐ[K] Ω) : b (galTΩ A ℓ σ) = galVΩ A ℓ σ := rfl
  have hinj : Function.Injective b := by
    intro f g h
    apply LinearMap.ext
    intro x
    apply tate_one_tmul_injective (ℓ := ℓ) (M := Additive (A.Pt Ω))
    change ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] f x) = ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] g x)
    have he := LinearMap.congr_fun h ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x)
    change (f.baseChange ℚ_[ℓ]) ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x) =
      (g.baseChange ℚ_[ℓ]) ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x) at he
    simpa only [LinearMap.baseChange_tmul] using he
  have hsq (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) :
      (galVΩ A ℓ σ - 1) ^ 2 = 0 := by
    obtain ⟨n, hn, σ', hσ', he⟩ := exists_pos_pow_inertia_over_intermediateField E w σ hσ
    have hσeq : σ'.restrictScalars K = σ ^ n := AlgEquiv.ext he
    have hx := mixed_displacement_restrictScalars A w E ℓ hE σ' σ' hσ' hσ'
    rw [hσeq, ← pow_two, ← hb, galTΩ_pow] at hx
    have hy : (galTΩ A ℓ σ ^ n - 1) ^ 2 = 0 := hinj (by
      simpa only [map_pow, map_sub, map_one, map_zero] using hx)
    have hz := sub_sq_eq_zero_of_quasiUnipotent hk (galTΩ_sub_eq_smul A ℓ σ k (hfix σ hσ)) hn hy
    simpa only [map_pow, map_sub, map_one, map_zero, hb] using congrArg b hz
  intro σ hσ τ hτ x
  obtain ⟨n, hn, σ', hσ', heσ⟩ := exists_pos_pow_inertia_over_intermediateField E w σ hσ
  obtain ⟨m, hm, τ', hτ', heτ⟩ := exists_pos_pow_inertia_over_intermediateField E w τ hτ
  have hσeq : σ'.restrictScalars K = σ ^ n := AlgEquiv.ext heσ
  have hτeq : τ'.restrictScalars K = τ ^ m := AlgEquiv.ext heτ
  have hmix := mixed_displacement_restrictScalars A w E ℓ hE σ' τ' hσ' hτ'
  rw [hσeq, hτeq, galVΩ_pow, galVΩ_pow] at hmix
  have hz := displacement_mul_eq_zero_of_positive_powers (hsq σ hσ) (hsq τ hτ) hn hm hmix
  apply sub_eq_zero.mp
  exact LinearMap.congr_fun hz x

end Inertia

end SZRaynaud

#print axioms SZRaynaud.levelTwo_of_fixed_primePower_torsion_of_finite_index
