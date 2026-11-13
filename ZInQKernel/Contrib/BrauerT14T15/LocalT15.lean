import ZInQKernel.Contrib.BrauerT14T15.Kummer2
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant

/-!
# Leaf T15 (`PkgI6.LocalH2CardC`), proved from Tau Ceti's local invariant

For a nonarchimedean local field `K` (Mathlib's `IsNonarchimedeanLocalField`; for instance `ℚ_[p]`),
Tau Ceti proves `invMap K : Br K ≃+ ℚ/ℤ` (`Brauer/Invariant.lean`, vendored), where
`Br K = H²(G_K, (Kˢ)ˣ)` and `unitsRepH2Equiv K` identifies it with Tau Ceti's explicit cochain
`H²(Gal(Kˢ/K), (Kˢ)ˣ)`.  The `2`-torsion of `ℚ/ℤ` is `{0, 1/2}`, so the explicit `H²` has exactly
one nonzero element killed by `2`, and the Kummer bridge (`Kummer2.lean`) gives
`PkgI6.H2TwoClasses (Gal(Kˢ/K))`.  The restriction isomorphism `Field.absoluteGaloisGroup K ≃ₜ*
Gal(Kˢ/K)` (`absoluteGaloisGroupRestrictEquiv`) transports it to Mathlib's absolute Galois group.

The real place is `H²(G_ℝ, ℤ/2)` for `G_ℝ` of order two, proved by elementary cochain algebra
(the proof of task t-brauer-purity, `scratch/t-brauer-purity/LocalH2RealKernel.lean`, reproduced in
`Real.lean`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

namespace ZInQ.Contrib.BrauerT14T15

open TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory PkgI6

/-! ### The `2`-torsion of `ℚ/ℤ` -/

lemma addCircle_two_torsion (x : AddCircle (1 : ℚ)) (hx : 2 • x = 0) :
    x = 0 ∨ x = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  induction x using QuotientAddGroup.induction_on with
  | H q =>
  have hq : ((2 • q : ℚ) : AddCircle (1 : ℚ)) = 0 := by rw [AddCircle.coe_nsmul]; exact hx
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).mp hq
  simp only [zsmul_eq_mul, mul_one, nsmul_eq_mul, Nat.cast_ofNat] at hn
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    apply (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one]
    push_cast at hn
    linarith
  · right
    rw [← sub_eq_zero, ← AddCircle.coe_sub]
    apply (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr
    refine ⟨k, ?_⟩
    simp only [zsmul_eq_mul, mul_one]
    push_cast at hn
    linarith

lemma addCircle_half_ne_zero : ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℚ)).mp h
  simp only [zsmul_eq_mul, mul_one] at hn
  have h2 : (2 * n : ℚ) = 1 := by rw [hn]; norm_num
  have h3 : (2 * n : ℤ) = 1 := by exact_mod_cast h2
  omega

lemma addCircle_two_nsmul_half : 2 • ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) = 0 := by
  rw [← AddCircle.coe_nsmul]
  apply (AddCircle.coe_eq_zero_iff (1 : ℚ)).mpr
  exact ⟨1, by norm_num⟩

/-! ### `H²(G_K, ℤ/2)` for a nonarchimedean local field -/

section Local

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The explicit `H²(Gal(Kˢ/K), (Kˢ)ˣ)` is `ℚ/ℤ`, by Tau Ceti's local invariant. -/
noncomputable def explicitInv : H2 (AbsoluteGaloisGroup K) (UnitsCoeff K) ≃+ AddCircle (1 : ℚ) :=
  (unitsRepH2Equiv K).trans (invMap K)

/-- **`H²(Gal(Kˢ/K), ℤ/2)` has exactly two classes** for a nonarchimedean local field with `2 ≠ 0`. -/
theorem h2TwoClasses_absoluteGaloisGroup (h2 : (2 : K) ≠ 0) :
    H2TwoClasses (AbsoluteGaloisGroup K) := by
  set φ := explicitInv K
  refine h2TwoClasses_of_two_torsion h2 ⟨φ.symm ((1 / 2 : ℚ) : AddCircle (1 : ℚ)), ?_, ?_⟩ ?_
  · intro h
    apply addCircle_half_ne_zero
    simpa using congrArg φ h
  · rw [← map_nsmul, addCircle_two_nsmul_half, map_zero]
  · intro x y hx hx2 hy hy2
    apply φ.injective
    have hx2' : 2 • φ x = 0 := by rw [← map_nsmul, hx2, map_zero]
    have hy2' : 2 • φ y = 0 := by rw [← map_nsmul, hy2, map_zero]
    have hx0 : φ x ≠ 0 := fun h => hx (φ.injective (h.trans (map_zero φ).symm))
    have hy0 : φ y ≠ 0 := fun h => hy (φ.injective (h.trans (map_zero φ).symm))
    rcases addCircle_two_torsion _ hx2' with h | h
    · exact absurd h hx0
    rcases addCircle_two_torsion _ hy2' with h' | h'
    · exact absurd h' hy0
    rw [h, h']

/-- **`H²(G_K, ℤ/2)` has exactly two classes**, on Mathlib's absolute Galois group. -/
theorem h2TwoClasses_local (h2 : (2 : K) ≠ 0) :
    H2TwoClasses (Field.absoluteGaloisGroup K) :=
  h2TwoClasses_of_continuousMulEquiv (absoluteGaloisGroupRestrictEquiv K)
    (h2TwoClasses_absoluteGaloisGroup K h2)

end Local

/-- **The finite-place half of leaf T15 (`PkgI6.LocalH2CardC`), proved.** -/
theorem h2TwoClasses_padic (p : ℕ) [Fact p.Prime] :
    H2TwoClasses (Field.absoluteGaloisGroup ℚ_[p]) :=
  h2TwoClasses_local ℚ_[p] two_ne_zero

end ZInQ.Contrib.BrauerT14T15
