/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single (git blob e38cb05c1d43529953ad11764ef147b4fb711e3d, sha256 7dd9ffa332055d1359861de279cfe2b0f0eebe9035b3095e6eaf8d5b3519e6ec).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_constantFieldDescent_finset
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_constantFieldExtension
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single_complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_exists_natCast_dvd_ord_sub_of_constantFieldExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single

open AlgebraicCurve

namespace W7XPic0Div

section Basic

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem ord_eq_zero_of_mem_of_inv_mem {f : F} (h1 : f ∈ v.toValuationSubring)
    (h2 : f⁻¹ ∈ v.toValuationSubring) : v.ord f = 0 := by
  have a := ord_nonneg_of_mem v h1
  have b := ord_nonneg_of_mem v h2
  rw [v.ord_inv] at b
  omega

theorem exists_ord_eq_one : ∃ π : F, v.ord π = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  exact ⟨π, v.ord_coe_irreducible hπ⟩

theorem inv_not_mem_of_ord_eq_one {π : F} (h : v.ord π = 1) : π⁻¹ ∉ v.toValuationSubring := by
  intro hmem
  have := ord_nonneg_of_mem v hmem
  rw [v.ord_inv] at this
  omega

end Basic

section CFE

variable {K₀ F₀ K₁ F₁ : Type*} [Field K₀] [Field F₀] [Field K₁] [Field F₁]
  [Algebra K₀ F₀] [Algebra K₁ F₁] [Algebra K₀ K₁] [Algebra F₀ F₁] [Algebra K₀ F₁]
  [IsScalarTower K₀ K₁ F₁] [IsScalarTower K₀ F₀ F₁]
  [IsAlgClosed K₀] [CharZero K₀]
  (hfg₀ : ∃ x : F₀, Transcendental K₀ x ∧
    FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀)
  (hfg₁ : ∃ x : F₁, Transcendental K₁ x ∧
    FiniteDimensional (IntermediateField.adjoin K₁ ({x} : Set F₁)) F₁)
  [IsCurveOver K₀ F₀]
  (hgen : IntermediateField.adjoin K₁ (Set.range (algebraMap F₀ F₁)) = ⊤)

omit [IsAlgClosed K₀] [IsCurveOver K₀ F₀] in
include hfg₀ in

theorem over_or_trivial (v₁ : Place K₁ F₁) :
    (∃ v₀ : Place K₀ F₀,
        v₁.toValuationSubring.comap (algebraMap F₀ F₁) = v₀.toValuationSubring) ∨
      (∀ y : F₀, algebraMap F₀ F₁ y ∈ v₁.toValuationSubring) := by
  by_cases h : ∀ y : F₀, algebraMap F₀ F₁ y ∈ v₁.toValuationSubring
  · exact Or.inr h
  · left
    push Not at h
    obtain ⟨x, -, hfin⟩ := hfg₀
    haveI : FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀ := hfin
    have hwK : ∀ a : K₀, algebraMap F₀ F₁ (algebraMap K₀ F₀ a) ∈ v₁.toValuationSubring := by
      intro a
      rw [← IsScalarTower.algebraMap_apply K₀ F₀ F₁ a, IsScalarTower.algebraMap_apply K₀ K₁ F₁ a]
      exact v₁.algebraMap_mem' _
    obtain ⟨v₀, hv₀⟩ :=
      AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom (K := K₀) x
        (algebraMap F₀ F₁) v₁.toValuationSubring hwK h
    exact ⟨v₀, hv₀.symm⟩

omit [Algebra K₀ K₁] [Algebra K₀ F₁] [IsScalarTower K₀ K₁ F₁] [IsScalarTower K₀ F₀ F₁]
  [IsAlgClosed K₀] [CharZero K₀] [IsCurveOver K₀ F₀] in

theorem not_over_of_trivial {v₁ : Place K₁ F₁}
    (htriv : ∀ y : F₀, algebraMap F₀ F₁ y ∈ v₁.toValuationSubring) (v₀ : Place K₀ F₀) :
    v₁.toValuationSubring.comap (algebraMap F₀ F₁) ≠ v₀.toValuationSubring := by
  intro hv
  apply v₀.ne_top'
  rw [← hv]
  ext y
  simp only [ValuationSubring.mem_comap, ValuationSubring.mem_top, iff_true]
  exact htriv y

include hfg₀ hfg₁ hgen in

theorem eq_of_over_of_over {v₁ w₁ : Place K₁ F₁} {v₀ : Place K₀ F₀}
    (hv : v₁.toValuationSubring.comap (algebraMap F₀ F₁) = v₀.toValuationSubring)
    (hw : w₁.toValuationSubring.comap (algebraMap F₀ F₁) = v₀.toValuationSubring) :
    v₁ = w₁ := by
  obtain ⟨P', -, -, huniq⟩ :=
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K₀ F₀ K₁ F₁
      hfg₀ hfg₁ hgen v₀
  exact (huniq v₁ hv).trans (huniq w₁ hw).symm

include hfg₀ hfg₁ hgen in

theorem ord_eq_of_over {v₁ : Place K₁ F₁} {v₀ : Place K₀ F₀}
    (hv : v₁.toValuationSubring.comap (algebraMap F₀ F₁) = v₀.toValuationSubring) (f : F₀) :
    v₁.ord (algebraMap F₀ F₁ f) = v₀.ord f := by
  obtain ⟨P', -, hord, huniq⟩ :=
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K₀ F₀ K₁ F₁
      hfg₀ hfg₁ hgen v₀
  rw [huniq v₁ hv]
  exact hord f

include hfg₀ hfg₁ hgen in

theorem eq_iff_eq_of_over {v₁ P₁ : Place K₁ F₁} {v₀ P₀ : Place K₀ F₀}
    (hv : v₁.toValuationSubring.comap (algebraMap F₀ F₁) = v₀.toValuationSubring)
    (hP : P₁.toValuationSubring.comap (algebraMap F₀ F₁) = P₀.toValuationSubring) :
    v₁ = P₁ ↔ v₀ = P₀ := by
  constructor
  · rintro rfl
    exact Place.ext (hv.symm.trans hP)
  · rintro rfl
    exact eq_of_over_of_over hfg₀ hfg₁ hgen hv hP

include hfg₀ hfg₁ hgen in

theorem single_sub_single_eq_of_over {v₁ P₁ Q₁ : Place K₁ F₁} {v₀ P₀ Q₀ : Place K₀ F₀}
    (hv : v₁.toValuationSubring.comap (algebraMap F₀ F₁) = v₀.toValuationSubring)
    (hP : P₁.toValuationSubring.comap (algebraMap F₀ F₁) = P₀.toValuationSubring)
    (hQ : Q₁.toValuationSubring.comap (algebraMap F₀ F₁) = Q₀.toValuationSubring) :
    (Finsupp.single P₁ 1 - Finsupp.single Q₁ 1 : Divisor K₁ F₁) v₁ =
      (Finsupp.single P₀ 1 - Finsupp.single Q₀ 1 : Divisor K₀ F₀) v₀ := by
  classical
  have hPiff : (P₁ = v₁) ↔ (P₀ = v₀) := by
    rw [eq_comm, eq_iff_eq_of_over hfg₀ hfg₁ hgen hv hP, eq_comm]
  have hQiff : (Q₁ = v₁) ↔ (Q₀ = v₀) := by
    rw [eq_comm, eq_iff_eq_of_over hfg₀ hfg₁ hgen hv hQ, eq_comm]
  simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
  by_cases hp : P₀ = v₀ <;> by_cases hq : Q₀ = v₀ <;>
    simp [hp, hq, hPiff.mpr, hQiff.mpr, mt hPiff.mp, mt hQiff.mp]

omit [Algebra K₀ K₁] [Algebra K₀ F₁] [IsScalarTower K₀ K₁ F₁] [IsScalarTower K₀ F₀ F₁]
  [IsAlgClosed K₀] [CharZero K₀] [IsCurveOver K₀ F₀] in

theorem single_sub_single_eq_zero_of_not_over {v₁ P₁ Q₁ : Place K₁ F₁} {P₀ Q₀ : Place K₀ F₀}
    (hv : ∀ v₀ : Place K₀ F₀,
      v₁.toValuationSubring.comap (algebraMap F₀ F₁) ≠ v₀.toValuationSubring)
    (hP : P₁.toValuationSubring.comap (algebraMap F₀ F₁) = P₀.toValuationSubring)
    (hQ : Q₁.toValuationSubring.comap (algebraMap F₀ F₁) = Q₀.toValuationSubring) :
    (Finsupp.single P₁ 1 - Finsupp.single Q₁ 1 : Divisor K₁ F₁) v₁ = 0 := by
  classical
  have h1 : P₁ ≠ v₁ := fun h => hv P₀ (h ▸ hP)
  have h2 : Q₁ ≠ v₁ := fun h => hv Q₀ (h ▸ hQ)
  simp [h1, h2]

include hfg₀ hfg₁ hgen in

theorem dvd_ascend {n : ℕ} {P₀ Q₀ : Place K₀ F₀} {P₁ Q₁ : Place K₁ F₁}
    (hP : P₁.toValuationSubring.comap (algebraMap F₀ F₁) = P₀.toValuationSubring)
    (hQ : Q₁.toValuationSubring.comap (algebraMap F₀ F₁) = Q₀.toValuationSubring)
    {f : F₀}
    (hdiv : ∀ v₀ : Place K₀ F₀,
      (n : ℤ) ∣ v₀.ord f - (Finsupp.single P₀ 1 - Finsupp.single Q₀ 1 : Divisor K₀ F₀) v₀)
    (v₁ : Place K₁ F₁) :
    (n : ℤ) ∣ v₁.ord (algebraMap F₀ F₁ f) -
      (Finsupp.single P₁ 1 - Finsupp.single Q₁ 1 : Divisor K₁ F₁) v₁ := by
  rcases over_or_trivial (K₁ := K₁) (F₁ := F₁) hfg₀ v₁ with ⟨v₀, hv⟩ | htriv
  · rw [ord_eq_of_over hfg₀ hfg₁ hgen hv, single_sub_single_eq_of_over hfg₀ hfg₁ hgen hv hP hQ]
    exact hdiv v₀
  · rw [single_sub_single_eq_zero_of_not_over (not_over_of_trivial htriv) hP hQ,
      ord_eq_zero_of_mem_of_inv_mem v₁ (htriv f) (by rw [← map_inv₀]; exact htriv f⁻¹)]
    simp

end CFE

theorem essFiniteType_of_fg {K F : Type*} [Field K] [Field F] [Algebra K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K F := by
  obtain ⟨x, -, hfin⟩ := hfg
  have h1 : Algebra.EssFiniteType K (IntermediateField.adjoin K ({x} : Set F)) :=
    IntermediateField.essFiniteType_iff.2
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  have h2 : Algebra.EssFiniteType (IntermediateField.adjoin K ({x} : Set F)) F := inferInstance
  exact Algebra.EssFiniteType.comp K (IntermediateField.adjoin K ({x} : Set F)) F

end W7XPic0Div

open W7XPic0Div in
theorem solution (K F : Type*) [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F]
    (n : ℕ) (hn : n ≠ 0) (P Q : Place K F) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F,
      (n : ℤ) ∣ v.ord f - (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) v := by
  classical

  obtain ⟨πP, hπP⟩ := exists_ord_eq_one P
  obtain ⟨πQ, hπQ⟩ := exists_ord_eq_one Q

  obtain ⟨K₀, F₀, _, _, _, _, _, _, _, _, algC, _, _, _, hfg₀, htop, ht⟩ :=
    AlgebraicCurve.exists_constantFieldDescent_finset K F hfg ({πP, πQ} : Finset F)
  haveI : CharZero K₀ := (algebraMap K₀ K).charZero

  have restrict_of_unif : ∀ (R : Place K F) (π : F), R.ord π = 1 →
      π ∈ Set.range (algebraMap F₀ F) →
      ∃ R₀ : Place K₀ F₀, R.toValuationSubring.comap (algebraMap F₀ F) = R₀.toValuationSubring := by
    intro R π hπ hmem
    rcases over_or_trivial (K₁ := K) (F₁ := F) hfg₀ R with h | htriv
    · exact h
    · exfalso
      obtain ⟨p, hp⟩ := hmem
      apply inv_not_mem_of_ord_eq_one R hπ
      rw [← hp, ← map_inv₀]
      exact htriv p⁻¹
  have hπPmem : πP ∈ Set.range (algebraMap F₀ F) := ht (by simp)
  have hπQmem : πQ ∈ Set.range (algebraMap F₀ F) := ht (by simp)
  obtain ⟨P₀, hP₀⟩ := restrict_of_unif P πP hπP hπPmem
  obtain ⟨Q₀, hQ₀⟩ := restrict_of_unif Q πQ hπQ hπQmem

  letI : Algebra K₀ ℂ := algC
  haveI : Algebra.EssFiniteType K₀ F₀ := essFiniteType_of_fg hfg₀
  haveI : PerfectField K₀ := PerfectField.ofCharZero
  haveI : HasCanonicalDivisor (K := K₀) (F := F₀) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  obtain ⟨Fc, _, _, _, _, _, _, _, _, hfgc, hgenc⟩ :=
    AlgebraicCurve.exists_constantFieldExtension K₀ F₀ ℂ hfg₀
  obtain ⟨Pc, hPc, -, -⟩ :=
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K₀ F₀ ℂ Fc
      hfg₀ hfgc hgenc P₀
  obtain ⟨Qc, hQc, -, -⟩ :=
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K₀ F₀ ℂ Fc
      hfg₀ hfgc hgenc Q₀

  obtain ⟨fc, hfc0, hfc⟩ :=
    AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex Fc hfgc n hn Pc Qc

  obtain ⟨f₀, hf₀0, hf₀⟩ :=
    AlgebraicCurve.Divisor.exists_natCast_dvd_ord_sub_of_constantFieldExtension K₀ F₀ ℂ Fc
      hfg₀ hfgc hgenc n hn
      (Finsupp.single P₀ 1 - Finsupp.single Q₀ 1) (Finsupp.single Pc 1 - Finsupp.single Qc 1)
      (fun v' v hv => single_sub_single_eq_of_over hfg₀ hfgc hgenc hv hPc hQc)
      (fun v' hv' => single_sub_single_eq_zero_of_not_over hv' hPc hQc)
      ⟨fc, hfc0, hfc⟩

  exact ⟨algebraMap F₀ F f₀, by simpa using hf₀0, dvd_ascend hfg₀ hfg htop hP₀ hQ₀ hf₀⟩
