import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionRectangularScale

/-!
# Homogeneous rectangular scaling in every nonnegative weight

The rational diagonal slashes of actual admissible torsion products are finite
constant combinations of admissible products at the constructed common level.
The powers come from the actual slash normalization, including weight zero.
-/

noncomputable section
set_option maxHeartbeats 800000

open Complex Function Set
open scoped Real UpperHalfPlane BigOperators MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionRectangularHomogeneous

open ThetaRectangular RectangularThetaLattice RectangularProductExpansion TorsionRectangularScale
open AllLevelProducts AllLevelForms CongruenceSubgroup Matrix.SpecialLinearGroup

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

variable {n : ℕ} [NeZero n]

/-- The actual admissible homogeneous product subspace, at its true weight. -/
def homogeneousSpan (N : ℕ) (hN : 0 < N) (k : ℕ) : Submodule ℂ (_root_.ModularForm (ΓP N) (k : ℤ)) :=
  Submodule.span ℂ {f | ∃ v : Fin k → ℤ × ℤ, ∃ hv : ∀ i,Good N (v i), f=productForm N hN k v hv}

/-- The actual forward translate/restrict map in weight k. -/
def forwardWeightMap (N : ℕ) (k : ℕ) :
    _root_.ModularForm (ΓP N) (k : ℤ) →ₗ[ℂ] _root_.ModularForm (ΓP (n*N)) (k : ℤ) :=
  (_root_.ModularForm.restrictₗ (k : ℤ) ℂ (principal_forward_inclusion (n := n) N)).comp
    (_root_.ModularForm.translateₗ (TauCeti.scaleGL n) (TauCeti.val_det_scaleGL_pos (d := n)))

/-- The actual inverse translate/restrict map in weight k. -/
def inverseWeightMap (N : ℕ) (k : ℕ) :
    _root_.ModularForm (ΓP N) (k : ℤ) →ₗ[ℂ] _root_.ModularForm (ΓP (n*N)) (k : ℤ) :=
  (_root_.ModularForm.restrictₗ (k : ℤ) ℂ (principal_inverse_inclusion (n := n) N)).comp
    (_root_.ModularForm.translateₗ ((TauCeti.scaleGL n)⁻¹) (inverse_scale_det_pos (n := n)))

lemma forwardWeightMap_apply (N k : ℕ) (f : _root_.ModularForm (ΓP N) (k : ℤ)) (τ : ℍ) :
    forwardWeightMap (n := n) N k f τ=(⇑f ∣[(k : ℤ)] TauCeti.scaleGL n) τ := by
  change _root_.ModularForm.restrict (principal_forward_inclusion (n := n) N)
    (_root_.ModularForm.translate f (TauCeti.scaleGL n)) τ = _
  rw [← _root_.ModularForm.coe_translate]
  rfl

lemma inverseWeightMap_apply (N k : ℕ) (f : _root_.ModularForm (ΓP N) (k : ℤ)) (τ : ℍ) :
    inverseWeightMap (n := n) N k f τ=(⇑f ∣[(k : ℤ)] (TauCeti.scaleGL n)⁻¹) τ := by
  change _root_.ModularForm.restrict (principal_inverse_inclusion (n := n) N)
    (_root_.ModularForm.translate f ((TauCeti.scaleGL n)⁻¹)) τ = _
  rw [← _root_.ModularForm.coe_translate]
  rfl

/-- Inverse normalization at every integral weight is proved by the actual group action. -/
lemma inverse_slash_weight (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] (TauCeti.scaleGL n)⁻¹) τ = (n : ℂ)^(1-k)*f ((TauCeti.scaleGL n)⁻¹ • τ) := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast NeZero.ne n
  have hc : ((f ∣[k] (TauCeti.scaleGL n)⁻¹) ∣[k] TauCeti.scaleGL n)=f := by
    rw [← SlashAction.slash_mul,inv_mul_cancel,SlashAction.slash_one]
  have hh := congrFun hc ((TauCeti.scaleGL n)⁻¹ • τ)
  rw [TauCeti.slash_scaleGL_apply,smul_inv_smul] at hh
  have hp : (n : ℂ)^(1-k)*(n : ℂ)^(k-1)=1 := by
    rw [← zpow_add₀ hnC,show (1-k)+(k-1)=0 by ring,zpow_zero]
  calc
    _ = (n : ℂ)^(1-k)*((n : ℂ)^(k-1)*(f ∣[k] (TauCeti.scaleGL n)⁻¹) τ) := by rw [← mul_assoc,hp,one_mul]
    _ = _ := by rw [hh]

/-- Each factor independently chooses a real rectangular translate. -/
def realChoices (N : ℕ) {k : ℕ} (v : Fin k → ℤ × ℤ) (choice : Fin k → Fin n) : Fin k → ℤ × ℤ :=
  fun i => ((n : ℤ)*(v i).1,(v i).2+(N : ℤ)*(choice i : ℕ))

lemma realChoices_good (N : ℕ) {k : ℕ} (v : Fin k → ℤ × ℤ) (hv : ∀ i,Good N (v i))
    (choice : Fin k → Fin n) : ∀ i,Good (n*N) (realChoices N v choice i) :=
  fun i => good_real_lift (NeZero.pos n) (hv i) (choice i)

/-- Each factor independently chooses an imaginary rectangular translate. -/
def imagChoices (N : ℕ) {k : ℕ} (v : Fin k → ℤ × ℤ) (choice : Fin k → Fin n) : Fin k → ℤ × ℤ :=
  fun i => ((v i).1+(N : ℤ)*(choice i : ℕ),(n : ℤ)*(v i).2)

lemma imagChoices_good (N : ℕ) {k : ℕ} (v : Fin k → ℤ × ℤ) (hv : ∀ i,Good N (v i))
    (choice : Fin k → Fin n) : ∀ i,Good (n*N) (imagChoices N v choice i) :=
  fun i => good_imag_lift (NeZero.pos n) (hv i) (choice i)

/-- Forward rational scaling has the exact 1/n coefficient for a homogeneous product of any length. -/
theorem forward_homogeneous_product (N : ℕ) (hN : 0 < N) (k : ℕ) (v : Fin k → ℤ × ℤ)
    (hv : ∀ i,Good N (v i)) :
    forwardWeightMap (n := n) N k (productForm N hN k v hv) =
      (1/(n : ℂ)) • ∑ choice : Fin k → Fin n,
        productForm (n*N) (Nat.mul_pos (NeZero.pos n) hN) k
          (realChoices N v choice) (realChoices_good N v hv choice) := by
  apply _root_.ModularForm.ext
  intro τ
  have he (choice : Fin k → Fin n) : productForm (n*N) (Nat.mul_pos (NeZero.pos n) hN) k
      (realChoices N v choice) (realChoices_good N v hv choice) τ =
        ∏ i : Fin k,Torsion.torsionLogDerivative (n*N) ((n : ℤ)*(v i).1)
          ((v i).2+(N : ℤ)*(choice i : ℕ)) τ := by
    rw [productForm_apply]
    rfl
  rw [forwardWeightMap_apply,TauCeti.slash_scaleGL_apply,scale_upTau,productForm_apply]
  simp only [_root_.smul_apply,smul_eq_mul,_root_.sum_apply]
  simp_rw [he]
  have ht (i : Fin k) := raw_up n N (NeZero.pos n) hN τ (v i).1 (v i).2 (hv i)
  simp_rw [ht]
  rw [RectangularProductExpansion.product_of_sums,← mul_assoc,forward_weight_factor (NeZero.pos n)]

/-- Reciprocal rational scaling retains the exact integral-weight coefficient n^(1-k). -/
theorem inverse_homogeneous_product (N : ℕ) (hN : 0 < N) (k : ℕ) (v : Fin k → ℤ × ℤ)
    (hv : ∀ i,Good N (v i)) :
    inverseWeightMap (n := n) N k (productForm N hN k v hv) =
      (n : ℂ)^(1-(k : ℤ)) • ∑ choice : Fin k → Fin n,
        productForm (n*N) (Nat.mul_pos (NeZero.pos n) hN) k
          (imagChoices N v choice) (imagChoices_good N v hv choice) := by
  apply _root_.ModularForm.ext
  intro τ
  have he (choice : Fin k → Fin n) : productForm (n*N) (Nat.mul_pos (NeZero.pos n) hN) k
      (imagChoices N v choice) (imagChoices_good N v hv choice) τ =
        ∏ i : Fin k,Torsion.torsionLogDerivative (n*N) ((v i).1+(N : ℤ)*(choice i : ℕ))
          ((n : ℤ)*(v i).2) τ := by
    rw [productForm_apply]
    rfl
  rw [inverseWeightMap_apply,inverse_slash_weight,scale_downTau,productForm_apply]
  simp only [_root_.smul_apply,smul_eq_mul,_root_.sum_apply]
  simp_rw [he]
  have ht (i : Fin k) := raw_down n N (NeZero.pos n) hN τ (v i).1 (v i).2 (hv i)
  simp_rw [ht]
  rw [Fintype.prod_sum]

/-- Actual forward translate/restrict preserves the admissible homogeneous product subspace. -/
theorem forward_homogeneous_mem (N : ℕ) (hN : 0 < N) (k : ℕ)
    {f : _root_.ModularForm (ΓP N) (k : ℤ)} (hf : f∈homogeneousSpan N hN k) :
    forwardWeightMap (n := n) N k f∈homogeneousSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k := by
  have hle : homogeneousSpan N hN k ≤
      (homogeneousSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k).comap (forwardWeightMap (n := n) N k) := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,hv,rfl⟩
    change forwardWeightMap (n := n) N k (productForm N hN k v hv)∈
      homogeneousSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k
    rw [forward_homogeneous_product]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro choice _
    exact Submodule.subset_span ⟨realChoices N v choice,realChoices_good N v hv choice,rfl⟩
  exact hle hf

/-- The actual inverse translate/restrict has the same genuine subspace-preservation property. -/
theorem inverse_homogeneous_mem (N : ℕ) (hN : 0 < N) (k : ℕ)
    {f : _root_.ModularForm (ΓP N) (k : ℤ)} (hf : f∈homogeneousSpan N hN k) :
    inverseWeightMap (n := n) N k f∈homogeneousSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k := by
  have hle : homogeneousSpan N hN k ≤
      (homogeneousSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k).comap (inverseWeightMap (n := n) N k) := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,hv,rfl⟩
    change inverseWeightMap (n := n) N k (productForm N hN k v hv)∈
      homogeneousSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k
    rw [inverse_homogeneous_product]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro choice _
    exact Submodule.subset_span ⟨imagChoices N v choice,imagChoices_good N v hv choice,rfl⟩
  exact hle hf

/-- The actual normalized level-raising operator is the precise scalar multiple
of the constructed principal forward translate/restrict map. -/
theorem levelRaise_eq_forward (N k : ℕ) (f : _root_.ModularForm (ΓP N) (k : ℤ)) :
    TauCeti.ModularForm.levelRaise n (principal_forward_inclusion (n := n) N) f =
      (n : ℂ)^(1-(k : ℤ)) • forwardWeightMap (n := n) N k f := by
  apply _root_.ModularForm.ext
  intro τ
  rw [TauCeti.ModularForm.levelRaise_apply,_root_.smul_apply,smul_eq_mul,forwardWeightMap_apply]
  simpa only [Pi.smul_apply,smul_eq_mul] using
    (congrFun (TauCeti.smul_slash_scaleGL_eq (d := n) (k : ℤ) (⇑f : ℍ → ℂ)) τ).symm

/-- The normalized forward operator has coefficient n^(-k), not the 1/n coefficient
of the unnormalized weight-k slash. This also handles the empty product. -/
theorem levelRaise_homogeneous_product (N : ℕ) (hN : 0<N) (k : ℕ) (v : Fin k → ℤ × ℤ)
    (hv : ∀ i,Good N (v i)) :
    TauCeti.ModularForm.levelRaise n (principal_forward_inclusion (n := n) N) (productForm N hN k v hv) =
      (1/(n : ℂ))^k • ∑ choice : Fin k → Fin n,
        productForm (n*N) (Nat.mul_pos (NeZero.pos n) hN) k
          (realChoices N v choice) (realChoices_good N v hv choice) := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast NeZero.ne n
  rw [levelRaise_eq_forward,forward_homogeneous_product,smul_smul]
  congr 1
  calc
    (n : ℂ)^(1-(k : ℤ))*(1/(n : ℂ)) =
      (n : ℂ)^(1-(k : ℤ))*((n : ℂ)^((k : ℤ)-1)*(1/(n : ℂ))^k) := by
        rw [forward_weight_factor (NeZero.pos n)]
    _ = _ := by
      rw [← mul_assoc,← zpow_add₀ hnC,show (1-(k : ℤ))+((k : ℤ)-1)=0 by ring,zpow_zero,one_mul]

/-- Normalized level-raising preserves the actual admissible homogeneous product subspace. -/
theorem levelRaise_homogeneous_mem (N : ℕ) (hN : 0<N) (k : ℕ)
    {f : _root_.ModularForm (ΓP N) (k : ℤ)} (hf : f∈homogeneousSpan N hN k) :
    TauCeti.ModularForm.levelRaise n (principal_forward_inclusion (n := n) N) f ∈
      homogeneousSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k := by
  rw [levelRaise_eq_forward]
  exact Submodule.smul_mem _ _ (forward_homogeneous_mem N hN k hf)

/-- An actual principal-product endpoint with both rational slashes and no isogeny,
translation, modularity or target-span-closure premise. The common level is nN. -/
theorem actual_products_scaled (N : ℕ) (hN : 0<N) (k : ℕ) (v : Fin k → ℤ × ℤ)
    (hv : ∀ i,Good N (v i)) :
    ∃ F G : _root_.ModularForm (ΓP (n*N)) (k : ℤ),
      F∈homogeneousSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k ∧
      G∈homogeneousSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) k ∧
      (∀ τ : ℍ,F τ=(prodFun N v ∣[(k : ℤ)] TauCeti.scaleGL n) τ) ∧
      (∀ τ : ℍ,G τ=(prodFun N v ∣[(k : ℤ)] (TauCeti.scaleGL n)⁻¹) τ) := by
  have hp : productForm N hN k v hv∈homogeneousSpan N hN k := Submodule.subset_span ⟨v,hv,rfl⟩
  refine ⟨forwardWeightMap (n := n) N k (productForm N hN k v hv),
    inverseWeightMap (n := n) N k (productForm N hN k v hv),
    forward_homogeneous_mem N hN k hp,inverse_homogeneous_mem N hN k hp,?_,?_⟩
  · intro τ
    rw [forwardWeightMap_apply,coe_productForm]
  · intro τ
    rw [inverseWeightMap_apply,coe_productForm]

end ZInQ.Contrib.HeckePrimeRationality.TorsionRectangularHomogeneous
