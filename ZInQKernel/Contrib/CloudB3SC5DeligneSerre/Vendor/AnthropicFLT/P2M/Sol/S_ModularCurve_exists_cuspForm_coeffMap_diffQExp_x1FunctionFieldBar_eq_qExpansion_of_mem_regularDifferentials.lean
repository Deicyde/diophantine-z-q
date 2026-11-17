/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials (git blob 9a70f171df6924e33d7de6505630ed2ed2b6c1d5, sha256 5d3a04733a3d39e2e2f87efc9bebc13d8c6a06a52abb843d8204ea0f98543f79).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_HeckeDifferential
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpansionDiff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_isCurveOver_x1FunctionFieldBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_theta_coeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials

open ModularCurve AlgebraicCurve HahnSeries KaehlerDifferential
open scoped MatrixGroups

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace X1ConvGlue

variable (M : ℕ) [NeZero M]




abbrev Fb : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) := x1FunctionFieldBar M

theorem jq_mem_x1FunctionField : jq ∈ x1FunctionField M :=
  intFormRatiosC_subset ℚ (CongruenceSubgroup.Gamma1 M) (ModularCurve.jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 M))

abbrev jB : Fb M :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_x1FunctionField M)⟩

theorem coeffMap_qEuler {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (s : LaurentSeries R) :
    coeffMap f (qEuler R s) = qEuler S (coeffMap f s) := by
  ext n
  simp [qEuler_coeff, coeffMap_coeff]

theorem qEuler_eq_thetaL (s : LaurentSeries ℂ) : qEuler ℂ s = thetaL ℂ s := by
  ext n
  rw [qEuler_coeff, thetaL_apply, ModularCurve.theta_coeff, zsmul_eq_mul]

theorem coeffMap_coeffEmb' (ι₀ : AlgebraicClosure ℚ →+* ℂ) (z : LaurentSeries ℚ) :
    coeffMap ι₀ (coeffEmb (AlgebraicClosure ℚ) z) = coeffEmb ℂ z := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) z

theorem coeffMap_coeffEmb_jq (ι₀ : AlgebraicClosure ℚ →+* ℂ) :
    coeffMap ι₀ (coeffEmb (AlgebraicClosure ℚ) jq) = jqModC ℂ := by
  rw [coeffEmb, coeffMap_coeffMap, ← jqModC_rat]
  exact map_jqModC _

theorem coeffMap_algebraMap' (ι₀ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    coeffMap ι₀ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) =
      algebraMap ℂ (LaurentSeries ℂ) (ι₀ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_mem_laurentBaseChange_complex (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀) :
    coeffMap ι₀ x ∈ laurentBaseChange ℂ F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap']
        exact (laurentBaseChange ℂ F₀).algebraMap_mem _
      · rw [coeffMap_coeffEmb']
        exact coeffEmb_mem_laurentBaseChange ℂ hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

noncomputable def phi (ι₀ : AlgebraicClosure ℚ →+* ℂ) : Fb M →+* LaurentSeries ℂ :=
  (coeffMap ι₀).comp (Fb M).toSubfield.subtype

theorem phi_apply (ι₀ : AlgebraicClosure ℚ →+* ℂ) (x : Fb M) :
    phi M ι₀ x = coeffMap ι₀ (x : LaurentSeries (AlgebraicClosure ℚ)) := rfl

theorem phi_algebraMap (ι₀ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    phi M ι₀ (algebraMap (AlgebraicClosure ℚ) (Fb M) c) = algebraMap ℂ (LaurentSeries ℂ) (ι₀ c) := by
  rw [phi_apply]
  exact coeffMap_algebraMap' ι₀ c

theorem phi_jB (ι₀ : AlgebraicClosure ℚ →+* ℂ) : phi M ι₀ (jB M) = jqModC ℂ := by
  rw [phi_apply]
  exact coeffMap_coeffEmb_jq ι₀

theorem isIntegral_phi (ι₀ : AlgebraicClosure ℚ →+* ℂ) (a : Fb M) {y : Fb M}
    (hy : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb M))) y) :
    IsIntegral (Algebra.adjoin ℂ ({phi M ι₀ a} : Set (LaurentSeries ℂ))) (phi M ι₀ y) := by
  have hmem : ∀ r : Fb M,
      r ∈ Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb M)) →
      phi M ι₀ r ∈ Algebra.adjoin ℂ ({phi M ι₀ a} : Set (LaurentSeries ℂ)) := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
        rw [Set.mem_singleton_iff] at hr
        subst hr
        exact Algebra.subset_adjoin (Set.mem_singleton _)
    | algebraMap c =>
        rw [phi_algebraMap]
        exact Subalgebra.algebraMap_mem _ _
    | add r s _ _ hr hs => rw [map_add]; exact add_mem hr hs
    | mul r s _ _ hr hs => rw [map_mul]; exact mul_mem hr hs
  let ψ : Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb M)) →+*
      Algebra.adjoin ℂ ({phi M ι₀ a} : Set (LaurentSeries ℂ)) :=
    ((phi M ι₀).comp (Algebra.adjoin (AlgebraicClosure ℚ) ({a} : Set (Fb M))).val.toRingHom).codRestrict
      (Algebra.adjoin ℂ ({phi M ι₀ a} : Set (LaurentSeries ℂ))) (fun r => hmem r r.2)
  refine IsIntegral.map_of_comp_eq ψ (phi M ι₀) ?_ hy
  ext r
  rfl

theorem D_jB_ne_zero : D (AlgebraicClosure ℚ) (Fb M) (jB M) ≠ 0 := by
  intro h
  have h1 : diffQExp (Fb M) (D (AlgebraicClosure ℚ) (Fb M) (jB M)) =
      qEuler (AlgebraicClosure ℚ) ((jB M : Fb M) : LaurentSeries (AlgebraicClosure ℚ)) :=
    diffQExp_D _ _
  rw [h, map_zero] at h1
  have h2 := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff (-1)) h1
  simp only at h2
  rw [qEuler_coeff] at h2
  have h3 : ((jB M : Fb M) : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1) = 1 := by
    show (coeffEmb (AlgebraicClosure ℚ) jq).coeff (-1) = 1
    rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]
  rw [h3, HahnSeries.coeff_zero] at h2
  norm_num at h2

theorem alg_transport (F : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)))
    (hF : F = qExpFunctionFieldC (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M))
    (jbar : ↥F) (hjbar : (jbar : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (x : ↥F) (hx : x • D (AlgebraicClosure ℚ) ↥F jbar ∈ regularDifferentials (AlgebraicClosure ℚ) ↥F) :
    IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F))
        (x ^ 6 * jbar ^ 4 * (jbar - algebraMap (AlgebraicClosure ℚ) ↥F 1728) ^ 3) ∧
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar⁻¹} : Set ↥F))
        (x ^ (2 * Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F)) ↥F) *
          jbar ^ (Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F)) ↥F + 1) *
          (jbar - algebraMap (AlgebraicClosure ℚ) ↥F 1728) ^
            Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥F)) ↥F) := by
  subst hF
  exact ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC M (CongruenceSubgroup.Gamma1 M) le_rfl
    (CongruenceSubgroup.Gamma1_in_Gamma0 M) jbar hjbar x hx

theorem Fb_eq : (Fb M : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) =
    qExpFunctionFieldC (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M) :=
  ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M)

theorem coe_jB : ((jB M : Fb M) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
  show coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ)
  rw [coeffEmb, ← jqModC_rat]
  exact map_jqModC _

end X1ConvGlue

end

open scoped MatrixGroups in
open ModularCurve AlgebraicCurve HahnSeries KaehlerDifferential X1ConvGlue in
theorem solution
    (M : ℕ) [NeZero M] (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ])
    (hω : ω ∈ AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma1 M) 2,
      ModularCurve.coeffMap ι₀ (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) := by
  classical
  haveI hCO := ModularCurve.isCurveOver_x1FunctionFieldBar M

  have hrank : Module.finrank (Fb M) Ω[Fb M⁄AlgebraicClosure ℚ] = 1 := IsCurveOver.finrank_kaehler
  obtain ⟨x, hx⟩ := (finrank_eq_one_iff_of_nonzero'
    (D (AlgebraicClosure ℚ) (Fb M) (jB M)) (D_jB_ne_zero M)).mp hrank ω

  have hxreg : x • D (AlgebraicClosure ℚ) (Fb M) (jB M) ∈
      regularDifferentials (AlgebraicClosure ℚ) (Fb M) := by
    rw [hx]; exact hω
  obtain ⟨h₁, h₂⟩ := alg_transport M (Fb M) (Fb_eq M) (jB M) (coe_jB M) x hxreg

  have hXmem : phi M ι₀ x ∈ laurentBaseChange ℂ (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma1 M)) :=
    coeffMap_mem_laurentBaseChange_complex ι₀ _ x.2
  have hJ : phi M ι₀ (jB M) = jqModC ℂ := phi_jB M ι₀
  have h1728 : phi M ι₀ (algebraMap (AlgebraicClosure ℚ) (Fb M) 1728) = algebraMap ℂ (LaurentSeries ℂ) 1728 := by
    rw [phi_algebraMap, map_ofNat]
  have h₁' := isIntegral_phi M ι₀ (jB M) h₁
  have h₂' := isIntegral_phi M ι₀ ((jB M)⁻¹) h₂
  rw [map_inv₀, hJ] at h₂'
  rw [hJ] at h₁'
  simp only [map_mul, map_pow, map_sub, hJ, h1728] at h₁' h₂'
  set n : ℕ := Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jB M} : Set (Fb M))) (Fb M) with hn

  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  have h₁'' : IsIntegral (Algebra.adjoin ℂ ({jqModC ℂ} : Set (LaurentSeries ℂ)))
      ((phi M ι₀ x) ^ 6 * jqModC ℂ ^ (4 * 1) * (jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (3 * 1)) := by
    simpa only [mul_one] using h₁'
  have h₂'' : IsIntegral (Algebra.adjoin ℂ ({(jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ)))
      ((phi M ι₀ x) ^ (2 * n) * jqModC ℂ ^ (1 * n + 1) * (jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (1 * n)) := by
    simpa only [one_mul] using h₂'
  obtain ⟨f, hf⟩ :=
    ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC
      (CongruenceSubgroup.Gamma1 M) hT 1 le_rfl (phi M ι₀ x) hXmem n h₁'' h₂''
  refine ⟨f, ?_⟩

  have hΘ : diffQExp (Fb M) ω =
      ((x : Fb M) : LaurentSeries (AlgebraicClosure ℚ)) *
        qEuler (AlgebraicClosure ℚ) ((jB M : Fb M) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [← hx]
    exact diffQExp_smul_D _ _ _
  show coeffMap ι₀ (diffQExp (Fb M) ω) = _
  rw [hΘ, map_mul, coeffMap_qEuler, qEuler_eq_thetaL, ← phi_apply, ← phi_apply, hJ]
  rw [pow_one] at hf
  exact hf.symm

#print axioms solution
