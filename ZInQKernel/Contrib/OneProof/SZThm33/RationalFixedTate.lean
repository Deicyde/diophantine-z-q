import ZInQKernel.Contrib.OneProof.SZThm33.FixedTateSpecialization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization

/-!
# The rational Tate invariants of a Néron model
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit
open ZInQ.FaltingsRestate (isCommMonObj_groupModelO)
open scoped TensorProduct

namespace SZRaynaud

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- A Tate module of any abelian group has no scalar torsion over the
adic integers. The transition maps prove injectivity of the uniformizer. -/
theorem tate_smul_injective {M : Type*} [AddCommGroup M] {a : ℤ_[ℓ]} (ha : a ≠ 0) :
    Function.Injective (fun t : PkgI3.Tate.T ℓ M => a • t) := by
  have hℓ : Function.Injective (fun t : PkgI3.Tate.T ℓ M => (ℓ : ℤ_[ℓ]) • t) := by
    intro t u h
    apply Subtype.ext
    funext n
    change (ℓ : ℤ_[ℓ]) • t = (ℓ : ℤ_[ℓ]) • u at h
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul] at h
    have e := congrArg (fun t : PkgI3.Tate.T ℓ M => t.1 (n + 1)) h
    change ℓ • t.1 (n + 1) = ℓ • u.1 (n + 1) at e
    simpa only [t.2.2 n, u.2.2 n] using e
  obtain ⟨n, α, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha PadicInt.irreducible_p
  have hp (m : ℕ) : Function.Injective (fun t : PkgI3.Tate.T ℓ M => (ℓ : ℤ_[ℓ]) ^ m • t) := by
    induction m with
    | zero =>
      intro t u h
      simpa only [pow_zero, one_smul] using h
    | succ m ih =>
      intro t u h
      apply hℓ
      apply ih
      simpa only [pow_succ, mul_smul] using h
  intro t u h
  simp only [mul_smul] at h
  exact hp n ((Units.isUnit α).smul_left_cancel.mp h)

/-- Integral Tate towers inject into their rational scalar extension. -/
theorem tate_one_tmul_injective {M : Type*} [AddCommGroup M] :
    Function.Injective
      (TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ M) 1) := by
  rw [IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors ℤ_[ℓ])]
  intro a
  exact tate_smul_injective (nonZeroDivisors.ne_zero a.2)

namespace Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  {O : ValuationSubring K} {w : ValuationSubring Ω} [IsAlgClosed Ω]
  (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (M : GroupModelO A O)
  (hu : IsUnit (ℓ : O))

local instance : IsCommMonObj M.G := isCommMonObj_groupModelO M

/-- The rational Tate embedding induced by geometric residue specialization. -/
abbrev modelEmbedRationalΩ :
    (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ M.G)))) →ₗ[ℚ_[ℓ]]
      (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TΩ A Ω ℓ)) :=
  (modelEmbedTate hw A M hu).baseChange ℚ_[ℓ]

theorem modelEmbedRationalΩ_injective :
    Function.Injective (modelEmbedRationalΩ hw A M hu) := by
  have : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (modelEmbedTate_injective hw A M hu)

theorem galTΩ_modelEmbedTate_fixed (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) (x : (PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ M.G)))) :
    galTΩ A ℓ σ (modelEmbedTate hw A M hu x) = modelEmbedTate hw A M hu x := by
  let d : w.decompositionSubgroup K := ⟨σ, hσ.1⟩
  have hd : d ∈ w.inertiaSubgroup K := hσ.2
  rw [← modelEmbedTate_tateEnd hw A M hu d x]
  have h₀ : resEnd d = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (resAut d).toRingHom) = 𝟙 _
    rw [show resAut d = 1 from hd]
    exact Spec.map_id _
  congr 1
  apply Subtype.ext
  funext n
  apply Additive.toMul.injective
  apply Over.OverMorphism.ext
  change resEnd d ≫ (Additive.toMul (x.1 n)).left = (Additive.toMul (x.1 n)).left
  rw [h₀, Category.id_comp]

/-- The image of the geometric special-fibre Tate module is fixed by
absolute inertia, also after inverting the residue-unit prime. -/
theorem galVΩ_modelEmbedRationalΩ_fixed (σ : Ω ≃ₐ[K] Ω)
    (hσ : PkgI2.IsInertia w σ) (x : (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ M.G))))) :
    (galTΩ A ℓ σ).baseChange ℚ_[ℓ] (modelEmbedRationalΩ hw A M hu x) =
      modelEmbedRationalΩ hw A M hu x := by
  have h : (galTΩ A ℓ σ).comp (modelEmbedTate hw A M hu) = modelEmbedTate hw A M hu :=
    LinearMap.ext (galTΩ_modelEmbedTate_fixed hw A M hu σ hσ)
  have hQ := congrArg (LinearMap.baseChange ℚ_[ℓ]) h
  rw [LinearMap.baseChange_comp] at hQ
  exact LinearMap.congr_fun hQ x

variable [IsAlgClosure K Ω] [IsDiscreteValuationRing O]

/-- For a Néron model, the image of geometric residue Tate after
inverting ℓ equals the fixed part of the full inertia representation. -/
theorem mem_range_modelEmbedRationalΩ_iff (hN : M.IsNeronModel) (x : (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TΩ A Ω ℓ))) :
    x ∈ (modelEmbedRationalΩ hw A M hu).range ↔
      ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ →
        (galTΩ A ℓ σ).baseChange ℚ_[ℓ] x = x := by
  constructor
  · rintro ⟨y, rfl⟩ σ hσ
    exact galVΩ_modelEmbedRationalΩ_fixed hw A M hu σ hσ y
  · intro hx
    let f := TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (TΩ A Ω ℓ) 1
    obtain ⟨⟨t, s⟩, hclear⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[ℓ]) f x
    have ht (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) : galTΩ A ℓ σ t = t := by
      apply tate_one_tmul_injective
      change (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] (galTΩ A ℓ σ t) = f t
      rw [← LinearMap.baseChange_tmul, show (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] t = f t from rfl, ← hclear,
        LinearMap.map_smul_of_tower, hx σ hσ]
    obtain ⟨t', ht'⟩ := exists_modelEmbedTate_of_inertia_fixed hw A M hu hN t ht
    let c : ℚ_[ℓ] := algebraMap ℤ_[ℓ] ℚ_[ℓ] (s : ℤ_[ℓ])
    have hc : c ≠ 0 := (IsLocalization.map_units ℚ_[ℓ] s).ne_zero
    refine ⟨c⁻¹ • ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] t'), ?_⟩
    rw [map_smul, LinearMap.baseChange_tmul, ht']
    change c⁻¹ • f t = x
    rw [← hclear]
    change c⁻¹ • (s : ℤ_[ℓ]) • x = x
    rw [← algebraMap_smul ℚ_[ℓ] (s : ℤ_[ℓ]), ← mul_smul, inv_mul_cancel₀ hc, one_smul]

#print axioms mem_range_modelEmbedRationalΩ_iff

end Ambient
end SZRaynaud
