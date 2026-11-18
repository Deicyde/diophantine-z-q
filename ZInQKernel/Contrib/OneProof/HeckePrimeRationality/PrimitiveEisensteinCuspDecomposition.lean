import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinInterpolant

/-!
# Actual primitive Eisenstein plus cusp decomposition

Vanishing of all actual integral cusp-representative constants is converted
to the genuine cusp bundle, using the actual arithmetic-group cusp theorem
and the all-GL representative zero condition. The interpolating coefficients
are finite complex constants fixed before τ. No basis, dimension, desired
splitting, or Eisenstein/cusp classification premise is taken.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Complex Filter Set UpperHalfPlane Matrix Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinInterpolation

/-- Construct an ACTUAL cusp bundle from proved vanishing of every actual
constant. The actual decomposition below derives this hypothesis itself. -/
def cuspFromConstants (N : ℕ) [NeZero N] (k : ℤ) (f : ModularForm (principalReal N) k)
    (hz : ∀ γ : SL(2, ℤ), constantAt N k f γ = 0) : CuspForm (principalReal N) k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  zero_at_cusps' {c} hc := by
    have hc' := hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc'
    change c.IsZeroAt (f : ℍ → ℂ) k
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc']
    intro γ hγ
    have ht := constantCoefficient_tendsto N k (slashForm N k f γ)
    change Tendsto (⇑f ∣[k] γ) UpperHalfPlane.atImInfty (𝓝 (constantAt N k f γ)) at ht
    rw [hz γ] at ht
    exact ht

lemma cuspFromConstants_coe (N : ℕ) [NeZero N] (k : ℤ) (f : ModularForm (principalReal N) k)
    (hz : ∀ γ : SL(2, ℤ), constantAt N k f γ = 0) :
    ⇑(cuspFromConstants N k f hz) = ⇑f := rfl

/-- The genuine same-level residual cusp, after actual finite interpolation. -/
def residualCusp (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (f : ModularForm (principalReal N) (k : ℤ)) : CuspForm (principalReal N) (k : ℤ) :=
  cuspFromConstants N (k : ℤ) (residualForm N k hk f) (residual_constantAt_zero N hN k hk f)

lemma residualCusp_as_modular (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (f : ModularForm (principalReal N) (k : ℤ)) :
    (residualCusp N hN k hk f : ModularForm (principalReal N) (k : ℤ)) = residualForm N k hk f := by
  apply DFunLike.ext
  intro τ
  rfl

/-- Every actual modular form has the produced primitive interpolant plus an actual cusp. -/
theorem actual_interpolant_plus_cusp (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (f : ModularForm (principalReal N) (k : ℤ)) :
    f = interpolation N k hk f + (residualCusp N hN k hk f : ModularForm (principalReal N) (k : ℤ)) := by
  rw [residualCusp_as_modular,residualForm]
  abel

/-- Explicit coefficients on the COMPLETE finite principal quotient, independent of τ. -/
def interpolationCoefficients (N : ℕ) [NeZero N] (k : ℕ)
    (f : ModularForm (principalReal N) (k : ℤ)) (q : principalQuotient N) : ℂ :=
  (2*(N : ℂ))⁻¹ * quotientConstant N (k : ℤ) f q

lemma interpolation_eq_finite_combination (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (f : ModularForm (principalReal N) (k : ℤ)) :
    interpolation N k hk f = ∑ q : principalQuotient N,
      interpolationCoefficients N k f q • generator N k hk (quotientReduction N q) := by
  rw [interpolation_eq_complete_quotient,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [smul_smul]
  rfl

/-- Genuine Eisenstein+cusp decomposition for every actual principal modular
form in the claimed range. Neither a given basis nor a desired split is input. -/
theorem actual_primitive_eisenstein_cusp_decomposition (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (f : ModularForm (principalReal N) (k : ℤ)) :
    ∃ c : principalQuotient N → ℂ, ∃ g : CuspForm (principalReal N) (k : ℤ),
      f = (∑ q : principalQuotient N, c q •
        ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k)
          (ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinConstants.positiveRow N ᵥ*
            ((quotientReduction N q)⁻¹ : SL(2, ZMod N)))) +
        (g : ModularForm (principalReal N) (k : ℤ)) := by
  refine ⟨interpolationCoefficients N k f,residualCusp N hN k hk f,?_⟩
  have he := actual_interpolant_plus_cusp N hN k hk f
  rw [interpolation_eq_finite_combination] at he
  exact he

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinInterpolation
