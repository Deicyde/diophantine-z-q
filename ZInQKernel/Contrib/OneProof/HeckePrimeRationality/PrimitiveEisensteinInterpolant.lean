import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinInterpolationKernel

/-!
# Actual finite primitive Eisenstein constant-term interpolation

The coefficients come from the actual modular form's complete principal
quotient constants and are fixed before τ. The interpolant is a finite sum
of unchanged primitive Eisenstein modular forms. Its constant at every
integral cusp representative equals the original constant, using the
produced 2N kernel normalization.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable
open Complex Filter Set UpperHalfPlane Matrix Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinInterpolation
open ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinConstants

/-- The genuine constant coefficient as a linear map. -/
def constantLinear (N : ℕ) [NeZero N] (k : ℤ) : ModularForm (principalReal N) k →ₗ[ℂ] ℂ where
  toFun := constantCoefficient N k
  map_add' := constantCoefficient_add N k
  map_smul' c f := by simpa only [smul_eq_mul,RingHom.id_apply] using constantCoefficient_smul N k f c

/-- Actual same-level slash as a complex-linear map. -/
def slashLinear (N : ℕ) (k : ℤ) (γ : SL(2, ℤ)) :
    ModularForm (principalReal N) k →ₗ[ℂ] ModularForm (principalReal N) k where
  toFun f := slashForm N k f γ
  map_add' f g := by
    apply DFunLike.ext
    intro τ
    change ((⇑f+⇑g) ∣[k] γ) τ = (⇑f ∣[k] γ) τ + (⇑g ∣[k] γ) τ
    rw [SlashAction.add_slash]
    rfl
  map_smul' c f := by
    apply DFunLike.ext
    intro τ
    change ((c • ⇑f) ∣[k] γ) τ = c * (⇑f ∣[k] γ) τ
    rw [ModularForm.SL_smul_slash]
    rfl

/-- The actual constant at a cusp representative as a linear functional. -/
def constantAtLinear (N : ℕ) [NeZero N] (k : ℤ) (γ : SL(2, ℤ)) :
    ModularForm (principalReal N) k →ₗ[ℂ] ℂ := (constantLinear N k).comp (slashLinear N k γ)

lemma constantAtLinear_apply (N : ℕ) [NeZero N] (k : ℤ) (γ : SL(2, ℤ))
    (f : ModularForm (principalReal N) k) : constantAtLinear N k γ f = constantAt N k f γ := rfl

/-- An actual primitive Eisenstein form for a complete finite quotient class. -/
def generator (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k) (A : SL(2, ZMod N)) :
    ModularForm (principalReal N) (k : ℤ) :=
  ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k)
    (positiveRow N ᵥ* (A⁻¹ : SL(2, ZMod N)))

/-- The explicit 1/(2N) finite interpolant from actual quotient constants. -/
def interpolation (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (f : ModularForm (principalReal N) (k : ℤ)) : ModularForm (principalReal N) (k : ℤ) :=
  (2*(N : ℂ))⁻¹ • ∑ A : SL(2, ZMod N), finiteConstants N (k : ℤ) f A • generator N k hk A

/-- The literal same sum on the COMPLETE SL₂(ℤ)/Γ(N) quotient. -/
theorem interpolation_eq_complete_quotient (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (f : ModularForm (principalReal N) (k : ℤ)) :
    interpolation N k hk f = (2*(N : ℂ))⁻¹ • ∑ q : principalQuotient N,
      quotientConstant N (k : ℤ) f q • generator N k hk (quotientReduction N q) := by
  unfold interpolation
  congr 1
  rw [← (quotientReduction N).toEquiv.sum_comp
    (fun A : SL(2, ZMod N) => finiteConstants N (k : ℤ) f A • generator N k hk A)]
  apply Finset.sum_congr rfl
  intro q _
  change quotientConstant N (k : ℤ) f ((quotientReduction N).symm (quotientReduction N q)) •
    generator N k hk (quotientReduction N q) = _
  rw [MulEquiv.symm_apply_apply]

lemma generator_slash (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (A : SL(2, ZMod N)) (σ : SL(2, ℤ)) :
    slashForm N (k : ℤ) (generator N k hk A) σ =
      ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k)
        (positiveRow N ᵥ* (A⁻¹*(Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) σ) : SL(2, ZMod N))) := by
  apply DFunLike.ext
  intro τ
  change (eisensteinSeries (positiveRow N ᵥ* (A⁻¹ : SL(2, ZMod N))) (k : ℤ) ∣[(k : ℤ)] σ) τ = _
  rw [EisensteinSeries.eisensteinSeries_slash_apply,Matrix.vecMul_vecMul]
  rfl

lemma generator_constantAt (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (A : SL(2, ZMod N)) (σ : SL(2, ℤ)) :
    constantAt N (k : ℤ) (generator N k hk A) σ =
      constantProfile N k (positiveRow N ᵥ*
        (A⁻¹*(Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) σ) : SL(2, ZMod N))) := by
  rw [constantAt,generator_slash]
  exact actual_primitive_constant_coefficient N k hk _

/-- The interpolant matches every ACTUAL cusp-representative constant. -/
theorem interpolation_constantAt (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (f : ModularForm (principalReal N) (k : ℤ)) (σ : SL(2, ℤ)) :
    constantAt N (k : ℤ) (interpolation N k hk f) σ = constantAt N (k : ℤ) f σ := by
  rw [← finiteConstants_reduce N (k : ℤ) f σ]
  change constantAtLinear N (k : ℤ) σ (interpolation N k hk f) = _
  unfold interpolation
  simp only [LinearMap.map_smul,map_sum,smul_eq_mul,constantAtLinear_apply,generator_constantAt]
  rw [actual_constant_kernel N hN k f]
  have hn : (2*(N : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (NeZero.ne N))
  rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]

/-- An actual modular residual, before conversion to the cusp bundle. -/
def residualForm (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (f : ModularForm (principalReal N) (k : ℤ)) : ModularForm (principalReal N) (k : ℤ) := f-interpolation N k hk f

/-- All actual residual constants vanish, not merely a selected finite list. -/
theorem residual_constantAt_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (f : ModularForm (principalReal N) (k : ℤ)) (σ : SL(2, ℤ)) :
    constantAt N (k : ℤ) (residualForm N k hk f) σ = 0 := by
  change constantAtLinear N (k : ℤ) σ (f-interpolation N k hk f) = 0
  rw [map_sub,constantAtLinear_apply,constantAtLinear_apply,interpolation_constantAt N hN k hk f σ,sub_self]

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinInterpolation
