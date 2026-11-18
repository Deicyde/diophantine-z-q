import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTracePairOrbits
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinTraceInvariance

/-!
# Actual principal-product trace invariance

Right reindexing of the genuine trace quotient and the proved principal-product
slash covariance show that an actual principal-group motion does not change
the normalized trace of a genuine admissible degree-two product.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

open AllLevelProducts AllLevelPrincipal DivisionEisensteinLevelMaps
open ThetaFiveTorsion (act)

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The quotient summands reindex for actual admissible product forms. -/
theorem quotientFunc_product_right_shift (N M : ℕ) (hM : 0 < M)
    (v : Fin 2 → ℤ × ℤ) (hv : ∀ i, AllLevelForms.Good M (v i))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N)
    (q : (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)) :
    let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
    let _ := DivisionEisensteinLowerClosure.mapped_principal_subgroup_normal N M
    SlashInvariantForm.quotientFunc
      (productForm M hM 2 (fun i => act (v i) γ) (good_act_tuple hv γ)) q =
    SlashInvariantForm.quotientFunc (productForm M hM 2 v hv) (MulOpposite.op g⁻¹ • q) := by
  let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
  let _ := DivisionEisensteinLowerClosure.mapped_principal_subgroup_normal N M
  change SlashInvariantForm.quotientFunc
    (productForm M hM 2 (fun i => act (v i) γ) (good_act_tuple hv γ)) q =
    SlashInvariantForm.quotientFunc (productForm M hM 2 v hv) (MulOpposite.op g⁻¹ • q)
  have hseries : ⇑(productForm M hM 2 (fun i => act (v i) γ) (good_act_tuple hv γ)) =
      (⇑(productForm M hM 2 v hv) : ℍ → ℂ) ∣[(2 : ℤ)] (mapGL ℝ γ) :=
    (productForm_slash hM 2 v hv γ).symm
  induction q using QuotientGroup.induction_on' with
  | H r =>
    rw [MulAction.Quotient.smul_coe, SlashInvariantForm.quotientFunc_mk,
      SlashInvariantForm.quotientFunc_mk, hseries]
    norm_num only [Nat.cast_ofNat]
    rw [← SlashAction.slash_mul]
    simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Subgroup.coe_mul,
      Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, g]

/-- Actual normalized product trace is constant on every actual principal-group orbit. -/
theorem normalizedTrace_product_SL (N M : ℕ) (hM : 0 < M)
    (v : Fin 2 → ℤ × ℤ) (hv : ∀ i, AllLevelForms.Good M (v i))
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma N) :
    normalizedTrace N M hM (productForm M hM 2 (fun i => act (v i) γ) (good_act_tuple hv γ)) =
      normalizedTrace N M hM (productForm M hM 2 v hv) := by
  classical
  let : NeZero M := ⟨hM.ne'⟩
  let _ := DivisionEisensteinLowerClosure.mapped_principal_subgroup_normal N M
  let Q := (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)
  let : Fintype Q := Fintype.ofFinite Q
  let g : (ΓP N) := ⟨mapGL ℝ γ, Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩⟩
  rw [normalizedTrace_apply, normalizedTrace_apply]
  apply congrArg (fun f : _root_.ModularForm (ΓP N) 2 => (traceIndex N M : ℂ)⁻¹ • f)
  apply DFunLike.coe_injective
  rw [_root_.ModularForm.coe_trace, _root_.ModularForm.coe_trace]
  have he : ∀ q : Q,
      SlashInvariantForm.quotientFunc
        (productForm M hM 2 (fun i => act (v i) γ) (good_act_tuple hv γ)) q =
        SlashInvariantForm.quotientFunc (productForm M hM 2 v hv) (MulOpposite.op g⁻¹ • q) :=
      fun q => quotientFunc_product_right_shift N M hM v hv γ hγ q
  simp_rw [he]
  exact Equiv.sum_comp (MulAction.toPerm (MulOpposite.op g⁻¹))
    (SlashInvariantForm.quotientFunc (productForm M hM 2 v hv))

/-- Congruence of each admissible label gives equality of the actual products. -/
theorem productForm_eq_of_congr (M : ℕ) (hM : 0 < M)
    (v w : Fin 2 → ℤ × ℤ) (hv : ∀ i, AllLevelForms.Good M (v i))
    (hw : ∀ i, AllLevelForms.Good M (w i)) (hc : ∀ i, CongrN M (v i) (w i)) :
    productForm M hM 2 v hv = productForm M hM 2 w hw := by
  apply _root_.ModularForm.ext
  intro τ
  rw [productForm_apply, productForm_apply]
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg (fun f : ℍ → ℂ => f τ) (F_eq_of_congr hM (hw i) (hc i))

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
