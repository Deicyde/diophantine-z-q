import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinCuspDecomposition
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinPeterssonOrthogonality
import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule

/-!
# Actual primitive Eisenstein and cusp complements

The genuine Petersson pairing against a cusp is integrable for every actual
modular form and linear in the test form. Orthogonality of the unchanged
primitive generators extends to their actual span. Positive self-pairing on
an actual principal fundamental domain proves disjointness from the cusp
embedding range. The produced finite decomposition proves complementarity
and uniqueness of the residual cusp, not uniqueness of generator coefficients.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set UpperHalfPlane Complex Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm ComplexConjugate Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinComplement
open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinInterpolation

/-- The genuine principal-domain Petersson pairing, conjugate-linear first. -/
def pairing (N : ℕ) (k : ℤ) (f : CuspForm (principalReal N) k)
    (F : ModularForm (principalReal N) k) : ℂ :=
  UpperHalfPlane.peterssonInner k (PrimitivePetersson.principalDomain N) f F

/-- Actual cusp/modular integrability, not an Eis/Eis pairing or a premise. -/
theorem pairing_integrable (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm (principalReal N) k) (F : ModularForm (principalReal N) k) :
    IntegrableOn (UpperHalfPlane.petersson k f F) (PrimitivePetersson.principalDomain N) volume := by
  obtain ⟨C,hC⟩ := CuspFormClass.petersson_bounded_left k (principalReal N) f F
  exact IntegrableOn.of_bound (PrimitivePetersson.principalDomain_volume_lt_top N)
    ((UpperHalfPlane.petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous F)).aestronglyMeasurable.restrict) C (ae_of_all _ hC)

/-- Complex linearity in the second, modular test slot with integrability derived. -/
def pairingRight (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (principalReal N) k) :
    ModularForm (principalReal N) k →ₗ[ℂ] ℂ where
  toFun := pairing N k f
  map_add' F G := by
    exact UpperHalfPlane.peterssonInner_add_right k _ f F G
      (pairing_integrable N k f F) (pairing_integrable N k f G)
  map_smul' c F := by
    change UpperHalfPlane.peterssonInner k (PrimitivePetersson.principalDomain N) f (c • ⇑F) =
      c * UpperHalfPlane.peterssonInner k (PrimitivePetersson.principalDomain N) f F
    exact UpperHalfPlane.peterssonInner_smul_right k (PrimitivePetersson.principalDomain N) c f F

/-- The actual primitive-generator Eisenstein submodule. -/
def eisensteinSpan (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k) :
    Submodule ℂ (ModularForm (principalReal N) (k : ℤ)) :=
  Submodule.span ℂ (Set.range (ModularForm.eisensteinSeriesMF (by exact_mod_cast hk : (3 : ℤ) ≤ k)
    (N := N)))

/-- The actual cusp embedding range, with no chosen complement. -/
def cuspSubmodule (N : ℕ) (k : ℤ) : Submodule ℂ (ModularForm (principalReal N) k) :=
  ModularForm.cuspFormSubmodule (principalReal N) k

/-- Every actual cusp annihilates the full primitive span in its test slot. -/
theorem eisensteinSpan_le_pairing_ker (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (f : CuspForm (principalReal N) (k : ℤ)) :
    eisensteinSpan N k hk ≤ LinearMap.ker (pairingRight N (k : ℤ) f) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,rfl⟩
  exact PrimitivePetersson.actual_primitive_eisenstein_petersson_zero N hN k hk a f

theorem pairing_eisenstein_zero (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (k : ℕ) (hk : 3 ≤ k) (f : CuspForm (principalReal N) (k : ℤ))
    (E : ModularForm (principalReal N) (k : ℤ)) (hE : E ∈ eisensteinSpan N k hk) :
    pairing N (k : ℤ) f E = 0 := eisensteinSpan_le_pairing_ker N hN k hk f hE

/-- Genuine principal-domain positive definiteness of a cusp self-pairing. -/
theorem pairing_self_definite (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℤ)
    (f : CuspForm (principalReal N) k) (hz : pairing N k f (f : ModularForm (principalReal N) k) = 0) :
    f = 0 := by
  let D := PrimitivePetersson.principalDomain N
  let g : ℍ → ℝ := fun τ => (UpperHalfPlane.petersson k f f τ).re
  have hi : IntegrableOn (UpperHalfPlane.petersson k f f) D volume := pairing_integrable N k f f
  have hzero : ∫ τ in D, g τ = 0 :=
    (integral_re hi).trans (congrArg Complex.re hz)
  have hn : ∀ τ, 0 ≤ g τ := by
    intro τ
    simp only [g,UpperHalfPlane.petersson_self_eq_ofReal,Complex.ofReal_re]
    exact mul_nonneg (Complex.normSq_nonneg _) (zpow_nonneg τ.im_pos.le _)
  have hae : g =ᶠ[ae (volume.restrict D)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hn) hi.re).mp hzero
  let T : Set ℍ := {τ | g τ ≠ 0}
  have hcont : Continuous g := Complex.continuous_re.comp
    (UpperHalfPlane.petersson_continuous k (ModularFormClass.continuous f) (ModularFormClass.continuous f))
  have hm : MeasurableSet T := (hcont.isOpen_preimage _ isOpen_ne).measurableSet
  have hnull : volume (T ∩ D) = 0 := by
    have h := hae
    rw [Filter.EventuallyEq,ae_iff] at h
    rw [← Measure.restrict_apply hm]
    exact h
  have hinv (δ : CongruenceSubgroup.Gamma N) (τ : ℍ) : g (δ • τ) = g τ := by
    exact congrArg Complex.re (UpperHalfPlane.petersson_smul_of_mem k f f δ.2 τ)
  have hT : volume T = 0 :=
    (PrimitivePetersson.principalDomain_fundamental N hN).measure_zero_of_invariant T
      (by intro δ; ext τ; rw [Set.mem_smul_set_iff_inv_smul_mem]; simp only [T,Set.mem_setOf_eq,hinv]) hnull
  have hg : g = (0 : ℍ → ℝ) := by
    have ha : g =ᶠ[ae (volume : Measure ℍ)] (0 : ℍ → ℝ) := by
      change ∀ᵐ τ : ℍ ∂volume, g τ = 0
      rw [ae_iff]
      exact hT
    exact Measure.eq_of_ae_eq ha hcont continuous_const
  apply DFunLike.ext
  intro τ
  have ht := congrFun hg τ
  simp only [g,UpperHalfPlane.petersson_self_eq_ofReal,Complex.ofReal_re,Pi.zero_apply] at ht
  exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right
    (ne_of_gt (zpow_pos τ.im_pos k)))

theorem eisenstein_cusp_disjoint (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) :
    Disjoint (eisensteinSpan N k hk) (cuspSubmodule N (k : ℤ)) := by
  rw [Submodule.disjoint_def]
  intro F hE hS
  obtain ⟨f,hf⟩ := hS
  have hz := pairing_eisenstein_zero N hN k hk f F hE
  rw [← hf] at hz
  have he := pairing_self_definite N hN (k : ℤ) f hz
  rw [← hf,he,map_zero]

theorem interpolation_mem_eisensteinSpan (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (F : ModularForm (principalReal N) (k : ℤ)) :
    interpolation N k hk F ∈ eisensteinSpan N k hk := by
  unfold interpolation
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro A _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_,rfl⟩)

/-- The actual finite decomposition supplies the full supremum, not a given split. -/
theorem eisenstein_cusp_sup (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) :
    eisensteinSpan N k hk ⊔ cuspSubmodule N (k : ℤ) = ⊤ := by
  apply eq_top_iff.mpr
  intro F _
  rw [actual_interpolant_plus_cusp N hN k hk F]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (interpolation_mem_eisensteinSpan N k hk F))
    (Submodule.mem_sup_right ⟨residualCusp N hN k hk F,rfl⟩)

/-- Actual primitive Eisenstein and actual cusp submodules are complementary. -/
theorem actual_eisenstein_cusp_isCompl (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) :
    IsCompl (eisensteinSpan N k hk) (cuspSubmodule N (k : ℤ)) :=
  ⟨eisenstein_cusp_disjoint N hN k hk,codisjoint_iff.mpr (eisenstein_cusp_sup N hN k hk)⟩

/-- The residual cusp is unique; primitive-generator coefficients need not be. -/
theorem residual_cusp_unique (N : ℕ) [NeZero N] (hN : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (F E : ModularForm (principalReal N) (k : ℤ)) (hE : E ∈ eisensteinSpan N k hk)
    (g : CuspForm (principalReal N) (k : ℤ)) (hsplit : F = E+(g : ModularForm (principalReal N) (k : ℤ))) :
    g = residualCusp N hN k hk F := by
  have hmemE : E-interpolation N k hk F ∈ eisensteinSpan N k hk :=
    Submodule.sub_mem _ hE (interpolation_mem_eisensteinSpan N k hk F)
  have heq : E-interpolation N k hk F =
      ((residualCusp N hN k hk F-g : CuspForm (principalReal N) (k : ℤ)) :
        ModularForm (principalReal N) (k : ℤ)) := by
    change E-interpolation N k hk F =
      (residualCusp N hN k hk F : ModularForm (principalReal N) (k : ℤ)) -
      (g : ModularForm (principalReal N) (k : ℤ))
    rw [residualCusp_as_modular,residualForm]
    have he : E = F-(g : ModularForm (principalReal N) (k : ℤ)) := by rw [hsplit]; abel
    rw [he]
    abel
  have hmemS : E-interpolation N k hk F ∈ cuspSubmodule N (k : ℤ) :=
    ⟨residualCusp N hN k hk F-g,heq.symm⟩
  have hz := (Submodule.disjoint_def.mp (eisenstein_cusp_disjoint N hN k hk)) _ hmemE hmemS
  have hzero : residualCusp N hN k hk F-g = 0 := by
    apply CuspForm.toModularFormₗ_injective
    change ((residualCusp N hN k hk F-g : CuspForm (principalReal N) (k : ℤ)) :
      ModularForm (principalReal N) (k : ℤ)) = 0
    rw [← heq,hz]
  exact (sub_eq_zero.mp hzero).symm

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinComplement
