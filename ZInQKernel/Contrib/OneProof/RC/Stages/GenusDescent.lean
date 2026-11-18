import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Points
import ZInQKernel.Contrib.OneProof.RC.Stages.Multiplier

/-! Descent to the degree-at-most-four genus field (tex 8261–8266). -/

noncomputable section

open scoped WeierstrassCurve
open WeierstrassCurve Polynomial NumberField
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.Stages

/-- Adjoining one root of a quadratic over the imaginary quadratic base has
degree at most four, including the case of a root already in the base. -/
theorem finrank_genusField {K H : Type*} [Field K] [Field H] [NumberField K]
    [Algebra K H] [FiniteDimensional K H] [Algebra ℚ H] [IsScalarTower ℚ K H]
    (hK : Module.finrank ℚ K = 2) {s : H} {d : K} (hs : s ^ 2 = algebraMap K H d) :
    Module.finrank ℚ (IntermediateField.adjoin K {s}) ≤ 4 := by
  let F := IntermediateField.adjoin K ({s} : Set H)
  have hdegree : (minpoly K s).natDegree ≤ 2 := by
    have hmonic := monic_X_pow_sub_C (R := K) d (by decide : 2 ≠ 0)
    have hd : minpoly K s ∣ (X ^ 2 - C d : K[X]) := minpoly.dvd K s (by simp [hs])
    have hh := natDegree_le_of_dvd hd hmonic.ne_zero
    simpa [natDegree_X_pow_sub_C] using hh
  rw [← Module.finrank_mul_finrank ℚ K F, hK]
  have hf : Module.finrank K F ≤ 2 := by
    rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite K s)]
    exact hdegree
  omega

/-- A native eigenpoint descends to the field generated over the quadratic base
by its nonzero genus square root. Every automorphism fixing the root reads the
trivial value of the character and therefore fixes both coordinates. -/
theorem eigenPoint_descends {K : Type} [Field K] [NumberField K] {c : ℕ} [NeZero c]
    (E : WeierstrassCurve ℚ)
    [DecidableEq (ringClassField (conductorOrder K c))]
    {χ : Pic (conductorOrder K c) →* ℂˣ}
    {s : ringClassField (conductorOrder K c)} (hs : s ≠ 0)
    (hσ : ∀ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
      σ s = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) * s)
    {P : (E⁄(ringClassField (conductorOrder K c))).toAffine.Point}
    (hP : P ∈ eigenLattice E χ) :
    let F := IntermediateField.adjoin K ({s} : Set (ringClassField (conductorOrder K c)))
    letI := Classical.decEq F
    ∃ R : (E⁄F).toAffine.Point,
      Affine.Point.baseChange (W' := E) F (ringClassField (conductorOrder K c)) R = P := by
  classical
  intro F
  letI := Classical.decEq F
  let H := ringClassField (conductorOrder K c)
  have hfix (g : H ≃ₐ[F] H) : galPt E (g.restrictScalars K) P = P := by
    have hg : g s = s := g.commutes ⟨s, IntermediateField.mem_adjoin_simple_self K s⟩
    have hsgn := hσ (g.restrictScalars K)
    change g s = _ at hsgn
    rw [hg] at hsgn
    have hx : (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm
        (g.restrictScalars K)) : H) = 1 :=
      mul_right_cancel₀ hs (by simpa only [one_mul] using hsgn.symm)
    have hz : chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm
        (g.restrictScalars K)) = 1 := by exact_mod_cast hx
    exact (hP (g.restrictScalars K)).trans (by rw [hz, one_zsmul])
  cases P with
  | zero => exact ⟨0, map_zero _⟩
  | some x y hxy =>
    have hcoord (g : H ≃ₐ[F] H) : g x = x ∧ g y = y := by
      have h := hfix g
      unfold galPt at h
      rw [Affine.Point.map_some] at h
      exact Affine.Point.some.inj h
    obtain ⟨x₀, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F) x).mpr
      fun g => (hcoord g).1
    obtain ⟨y₀, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F) y).mpr
      fun g => (hcoord g).2
    exact ⟨.some x₀ y₀ ((Affine.baseChange_nonsingular E
      (f := Algebra.ofId F H) (algebraMap F H).injective x₀ y₀).mp hxy),
      Affine.Point.map_some _ _⟩

#print axioms finrank_genusField
#print axioms eigenPoint_descends

end ZInQ.Manuscript.RC.Stages
