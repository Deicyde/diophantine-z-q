import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RectangularProductExpansion
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaRectangular
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticGeneratorSpan
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# Rational diagonal transport of actual principal torsion products

Both rational scalings are constructed by the actual translate and restriction
operators. Rectangular isogeny identities supply explicit admissible product
combinations at the common level. Weight-two slash normalization is derived
from the actual scaling operator, not from multiplying weight-one slashes.
-/

noncomputable section
set_option maxHeartbeats 800000

open Complex Function Set Matrix
open scoped Real UpperHalfPlane BigOperators MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionRectangularScale

open ThetaRectangular RectangularThetaLattice AllLevelProducts AllLevelForms
open CongruenceSubgroup Matrix.SpecialLinearGroup TauCeti

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (Matrix.SpecialLinearGroup.mapGL ℝ)

variable {n : ℕ} [NeZero n]

lemma scale_upTau (τ : ℍ) : TauCeti.scaleGL n • τ = upTau n (NeZero.pos n) τ := by
  apply UpperHalfPlane.ext
  rw [TauCeti.coe_scaleGL_smul,upTau_coe]

lemma scale_downTau (τ : ℍ) : (TauCeti.scaleGL n)⁻¹ • τ = downTau n (NeZero.pos n) τ := by
  apply UpperHalfPlane.ext
  rw [TauCeti.coe_inv_scaleGL_smul,downTau_coe]

/-- The actual principal-level inclusion for the forward rational scaling. -/
theorem principal_forward_inclusion (N : ℕ) :
    (ΓP (n*N)) ≤ ConjAct.toConjAct (TauCeti.scaleGL n)⁻¹ • (ΓP N) := by
  rintro _ ⟨γ,hγ,rfl⟩
  change γ∈CongruenceSubgroup.Gamma (n*N) at hγ
  rw [TauCeti.mem_conjAct_inv_scaleGL_iff]
  have hsmall := Gamma_le_Gamma_of_dvd (dvd_mul_left N n) hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ hsmall
  obtain ⟨h00,h01,h10,h11⟩ := hsmall
  obtain ⟨q,hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (n*N)).mp hγ.2.2.1
  let c : ℤ := (N : ℤ)*q
  have hc : γ 1 0 = (n : ℤ)*c := by dsimp [c]; push_cast at hq; linear_combination hq
  have hm : TauCeti.conjScale n γ c hc ∈ CongruenceSubgroup.Gamma N := by
    rw [CongruenceSubgroup.Gamma_mem]
    simp [TauCeti.coe_conjScale,c,h00,h01,h11]
  exact ⟨TauCeti.conjScale n γ c hc,hm,(TauCeti.mapGL_conjScale γ c hc).symm⟩

/-- The integral conjugate for inverse scaling when the upper-right entry is divisible by n. -/
def inverseConj (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 0 1 = (n : ℤ)*c) : SL(2,ℤ) :=
  ⟨!![γ 0 0,c;(n : ℤ)*γ 1 0,γ 1 1],by
    rw [Matrix.det_fin_two_of]
    have hd := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
    rw [hc] at hd
    linear_combination hd⟩

omit [NeZero n] in
@[simp] lemma coe_inverseConj (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 0 1=(n : ℤ)*c) :
    ((inverseConj γ c hc : SL(2,ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)=
      !![γ 0 0,c;(n : ℤ)*γ 1 0,γ 1 1] := rfl

lemma mapGL_inverseConj (γ : SL(2,ℤ)) (c : ℤ) (hc : γ 0 1 = (n : ℤ)*c) :
    (TauCeti.scaleGL n)⁻¹ * mapGL ℝ γ * TauCeti.scaleGL n = mapGL ℝ (inverseConj γ c hc) := by
  have hc' : ((γ 0 1 : ℤ) : ℝ)=(n : ℝ)*(c : ℝ) := by exact_mod_cast hc
  rw [mul_assoc,inv_mul_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hc',mul_comm]

/-- The actual principal-level inclusion for inverse rational scaling. -/
theorem principal_inverse_inclusion (N : ℕ) :
    (ΓP (n*N)) ≤ ConjAct.toConjAct ((TauCeti.scaleGL n)⁻¹)⁻¹ • (ΓP N) := by
  rintro _ ⟨γ,hγ,rfl⟩
  change γ∈CongruenceSubgroup.Gamma (n*N) at hγ
  rw [map_inv,(ΓP N).mem_inv_pointwise_smul_iff,ConjAct.toConjAct_smul,inv_inv]
  have hsmall := Gamma_le_Gamma_of_dvd (dvd_mul_left N n) hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ hsmall
  obtain ⟨h00,h01,h10,h11⟩ := hsmall
  obtain ⟨q,hq⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (n*N)).mp hγ.2.1
  let c : ℤ := (N : ℤ)*q
  have hc : γ 0 1 = (n : ℤ)*c := by dsimp [c]; push_cast at hq; linear_combination hq
  have hm : inverseConj γ c hc ∈ CongruenceSubgroup.Gamma N := by
    rw [CongruenceSubgroup.Gamma_mem]
    simp [inverseConj,c,h00,h10,h11]
  exact ⟨inverseConj γ c hc,hm,(mapGL_inverseConj γ c hc).symm⟩

/-- Positive determinant of the actual inverse scaling matrix. -/
lemma inverse_scale_det_pos : 0 < (((TauCeti.scaleGL n)⁻¹).det : ℝ) := by
  rw [map_inv]
  simpa only [Units.val_inv_eq_inv_val] using inv_pos.mpr (TauCeti.val_det_scaleGL_pos (d := n))

/-- Forward actual translation restricted to the constructed common principal level. -/
def forwardMap (N : ℕ) :
    _root_.ModularForm (ΓP N) 2 →ₗ[ℂ] _root_.ModularForm (ΓP (n*N)) 2 :=
  (_root_.ModularForm.restrictₗ 2 ℂ (principal_forward_inclusion (n := n) N)).comp
    (_root_.ModularForm.translateₗ (TauCeti.scaleGL n) (TauCeti.val_det_scaleGL_pos (d := n)))

/-- Inverse actual translation restricted to the same common level. -/
def inverseMap (N : ℕ) :
    _root_.ModularForm (ΓP N) 2 →ₗ[ℂ] _root_.ModularForm (ΓP (n*N)) 2 :=
  (_root_.ModularForm.restrictₗ 2 ℂ (principal_inverse_inclusion (n := n) N)).comp
    (_root_.ModularForm.translateₗ ((TauCeti.scaleGL n)⁻¹) inverse_scale_det_pos)

lemma forwardMap_apply (N : ℕ) (f : _root_.ModularForm (ΓP N) 2) (τ : ℍ) :
    forwardMap (n := n) N f τ = (⇑f ∣[(2 : ℤ)] TauCeti.scaleGL n) τ := by
  change _root_.ModularForm.restrict (principal_forward_inclusion (n := n) N)
    (_root_.ModularForm.translate f (TauCeti.scaleGL n)) τ = _
  rw [← _root_.ModularForm.coe_translate]
  rfl

lemma inverseMap_apply (N : ℕ) (f : _root_.ModularForm (ΓP N) 2) (τ : ℍ) :
    inverseMap (n := n) N f τ = (⇑f ∣[(2 : ℤ)] (TauCeti.scaleGL n)⁻¹) τ := by
  change _root_.ModularForm.restrict (principal_inverse_inclusion (n := n) N)
    (_root_.ModularForm.translate f ((TauCeti.scaleGL n)⁻¹)) τ = _
  rw [← _root_.ModularForm.coe_translate]
  rfl

/-- The weight-two inverse slash factor is proved by cancelling the actual forward slash. -/
lemma inverse_slash_apply (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[(2 : ℤ)] (TauCeti.scaleGL n)⁻¹) τ =
      (1/(n : ℂ)) * f ((TauCeti.scaleGL n)⁻¹ • τ) := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast NeZero.ne n
  have hc : ((f ∣[(2 : ℤ)] (TauCeti.scaleGL n)⁻¹) ∣[(2 : ℤ)] TauCeti.scaleGL n) = f := by
    rw [← SlashAction.slash_mul,inv_mul_cancel,SlashAction.slash_one]
  have hh := congrFun hc ((TauCeti.scaleGL n)⁻¹ • τ)
  rw [TauCeti.slash_scaleGL_apply,smul_inv_smul] at hh
  norm_num at hh
  field_simp [hnC]
  linear_combination hh

/-- The admissible real rectangular target tuple for two source labels. -/
def realTuple (N : ℕ) (v : Fin 2 → ℤ × ℤ) (b c : Fin n) : Fin 2 → ℤ × ℤ :=
  ![((n : ℤ)*(v 0).1,(v 0).2+(N : ℤ)*(b : ℕ)),
    ((n : ℤ)*(v 1).1,(v 1).2+(N : ℤ)*(c : ℕ))]

lemma realTuple_good (N : ℕ) (v : Fin 2 → ℤ × ℤ) (hv : ∀ i,Good N (v i)) (b c : Fin n) :
    ∀ i,Good (n*N) (realTuple N v b c i) := by
  intro i
  fin_cases i
  · exact good_real_lift (NeZero.pos n) (hv 0) b
  · exact good_real_lift (NeZero.pos n) (hv 1) c

/-- The admissible imaginary rectangular target tuple for two source labels. -/
def imagTuple (N : ℕ) (v : Fin 2 → ℤ × ℤ) (a c : Fin n) : Fin 2 → ℤ × ℤ :=
  ![((v 0).1+(N : ℤ)*(a : ℕ),(n : ℤ)*(v 0).2),
    ((v 1).1+(N : ℤ)*(c : ℕ),(n : ℤ)*(v 1).2)]

lemma imagTuple_good (N : ℕ) (v : Fin 2 → ℤ × ℤ) (hv : ∀ i,Good N (v i)) (a c : Fin n) :
    ∀ i,Good (n*N) (imagTuple N v a c i) := by
  intro i
  fin_cases i
  · exact good_imag_lift (NeZero.pos n) (hv 0) a
  · exact good_imag_lift (NeZero.pos n) (hv 1) c

/-- Exact actual forward-translate product identity with its derived 1/n coefficient. -/
theorem forward_product (N : ℕ) (hN : 0 < N) (v : Fin 2 → ℤ × ℤ) (hv : ∀ i,Good N (v i)) :
    forwardMap (n := n) N (productForm N hN 2 v hv) =
      (1/(n : ℂ)) • ∑ b : Fin n, ∑ c : Fin n,
        productForm (n*N) (Nat.mul_pos (NeZero.pos n) hN) 2 (realTuple N v b c) (realTuple_good N v hv b c) := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast NeZero.ne n
  apply _root_.ModularForm.ext
  intro τ
  have ht (b c : Fin n) : productForm (n*N) (Nat.mul_pos (NeZero.pos n) hN) 2
      (realTuple N v b c) (realTuple_good N v hv b c) τ =
        Torsion.torsionLogDerivative (n*N) ((n : ℤ)*(v 0).1) ((v 0).2+(N : ℤ)*(b : ℕ)) τ *
        Torsion.torsionLogDerivative (n*N) ((n : ℤ)*(v 1).1) ((v 1).2+(N : ℤ)*(c : ℕ)) τ := by
    rw [productForm_apply,Fin.prod_univ_two]
    rfl
  rw [forwardMap_apply,TauCeti.slash_scaleGL_apply,scale_upTau,productForm_apply]
  simp only [Fin.prod_univ_two,Int.reduceSub,zpow_one,_root_.smul_apply,smul_eq_mul,_root_.sum_apply]
  simp_rw [ht]
  rw [raw_up n N (NeZero.pos n) hN τ _ _ (hv 0),raw_up n N (NeZero.pos n) hN τ _ _ (hv 1)]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]
  field_simp [hnC]

/-- Exact actual inverse-translate product identity; no weight-one slash multiplication is used. -/
theorem inverse_product (N : ℕ) (hN : 0 < N) (v : Fin 2 → ℤ × ℤ) (hv : ∀ i,Good N (v i)) :
    inverseMap (n := n) N (productForm N hN 2 v hv) =
      (1/(n : ℂ)) • ∑ a : Fin n, ∑ c : Fin n,
        productForm (n*N) (Nat.mul_pos (NeZero.pos n) hN) 2 (imagTuple N v a c) (imagTuple_good N v hv a c) := by
  apply _root_.ModularForm.ext
  intro τ
  have ht (a c : Fin n) : productForm (n*N) (Nat.mul_pos (NeZero.pos n) hN) 2
      (imagTuple N v a c) (imagTuple_good N v hv a c) τ =
        Torsion.torsionLogDerivative (n*N) ((v 0).1+(N : ℤ)*(a : ℕ)) ((n : ℤ)*(v 0).2) τ *
        Torsion.torsionLogDerivative (n*N) ((v 1).1+(N : ℤ)*(c : ℕ)) ((n : ℤ)*(v 1).2) τ := by
    rw [productForm_apply,Fin.prod_univ_two]
    rfl
  rw [inverseMap_apply,inverse_slash_apply,scale_downTau,productForm_apply]
  simp only [Fin.prod_univ_two,_root_.smul_apply,smul_eq_mul,_root_.sum_apply]
  simp_rw [ht]
  rw [raw_down n N (NeZero.pos n) hN τ _ _ (hv 0),raw_down n N (NeZero.pos n) hN τ _ _ (hv 1)]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]

/-- The actual product subspace is preserved by forward rational scaling at a constructed common level. -/
theorem forward_mem_productSpan (N : ℕ) (hN : 0 < N) {f : _root_.ModularForm (ΓP N) 2}
    (hf : f ∈ TorsionQuadraticGenerators.productSpan N hN) :
    forwardMap (n := n) N f ∈ TorsionQuadraticGenerators.productSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) := by
  have hle : TorsionQuadraticGenerators.productSpan N hN ≤
      (TorsionQuadraticGenerators.productSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN)).comap (forwardMap (n := n) N) := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,hv,rfl⟩
    change forwardMap (n := n) N (productForm N hN 2 v hv) ∈
      TorsionQuadraticGenerators.productSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN)
    rw [forward_product]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro b _
    apply Submodule.sum_mem
    intro c _
    exact Submodule.subset_span ⟨realTuple N v b c,realTuple_good N v hv b c,rfl⟩
  exact hle hf

/-- The inverse rational scaling preserves the same actual product subspace. -/
theorem inverse_mem_productSpan (N : ℕ) (hN : 0 < N) {f : _root_.ModularForm (ΓP N) 2}
    (hf : f ∈ TorsionQuadraticGenerators.productSpan N hN) :
    inverseMap (n := n) N f ∈ TorsionQuadraticGenerators.productSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN) := by
  have hle : TorsionQuadraticGenerators.productSpan N hN ≤
      (TorsionQuadraticGenerators.productSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN)).comap (inverseMap (n := n) N) := by
    apply Submodule.span_le.mpr
    rintro f ⟨v,hv,rfl⟩
    change inverseMap (n := n) N (productForm N hN 2 v hv) ∈
      TorsionQuadraticGenerators.productSpan (n*N) (Nat.mul_pos (NeZero.pos n) hN)
    rw [inverse_product]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro a _
    apply Submodule.sum_mem
    intro c _
    exact Submodule.subset_span ⟨imagTuple N v a c,imagTuple_good N v hv a c,rfl⟩
  exact hle hf

end ZInQ.Contrib.HeckePrimeRationality.TorsionRectangularScale
