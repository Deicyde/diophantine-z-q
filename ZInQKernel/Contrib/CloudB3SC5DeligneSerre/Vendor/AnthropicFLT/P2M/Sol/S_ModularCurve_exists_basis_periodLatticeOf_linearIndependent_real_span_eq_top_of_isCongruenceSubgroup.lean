/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup (git blob a3e372614135ce681211bd5c699d570e66874ce4, sha256 7548a9774289e9ae9ca4e220ef029877661c4ae266265323de6580c5c038be83).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_Period_exists_basis_parabolicHoms_of_isAddTorsionFree
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodMapOf_mem_parabolicHoms
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_periodMapOf_apply_eq_periodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open CongruenceSubgroup Module

noncomputable section

namespace ModularCurve
export _root_.ModularCurve (periodOf periodLatticeOf periodOf_mem_periodLatticeOf period Period.IsParabolicHom Period.parabolicHoms eq_zero_of_forall_re_periodOf_eq_zero finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup Period.exists_basis_parabolicHoms_of_isAddTorsionFree periodMapOf_mem_parabolicHoms periodMapOf_apply_eq_periodOf)
namespace PeriodRealStructureOf
open _root_.ModularCurve

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]




omit [Γ.FiniteIndex] in

theorem fg_SL2Z : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
    SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

theorem fg_Gamma : Group.FG Γ := by
  haveI := fg_SL2Z
  infer_instance

omit [Γ.FiniteIndex] in

theorem addMonoidHom_eq_of_eqOn_gen {A : Type*} [AddCommGroup A] {S : Set Γ}
    (hS : Subgroup.closure S = ⊤) (φ ψ : Additive Γ →+ A)
    (h : ∀ s ∈ S, φ (Additive.ofMul s) = ψ (Additive.ofMul s)) : φ = ψ := by
  suffices H : ∀ γ ∈ Subgroup.closure S, φ (Additive.ofMul γ) = ψ (Additive.ofMul γ) by
    ext x
    exact H (Additive.toMul x) (by rw [hS]; exact Subgroup.mem_top _)
  intro γ hγ
  induction hγ using Subgroup.closure_induction with
  | mem y hy => exact h y hy
  | one => change φ 0 = ψ 0; rw [map_zero, map_zero]
  | mul y z _ _ hy hz =>
    have : Additive.ofMul (y * z) = Additive.ofMul y + Additive.ofMul z := rfl
    change φ (Additive.ofMul (y * z)) = ψ (Additive.ofMul (y * z))
    rw [this, map_add, map_add]
    exact congrArg₂ (· + ·) hy hz
  | inv y _ hy =>
    have : Additive.ofMul y⁻¹ = -Additive.ofMul y := rfl
    change φ (Additive.ofMul y⁻¹) = ψ (Additive.ofMul y⁻¹)
    rw [this, map_neg, map_neg]
    exact congrArg Neg.neg hy

theorem finite_addMonoidHom_real : Module.Finite ℝ (Additive Γ →+ ℝ) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (fg_Gamma Γ)
  haveI : Fintype S := hSfin.fintype
  let res : (Additive Γ →+ ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun φ s => φ (Additive.ofMul (s : Γ))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective res ?_
  intro φ ψ hφψ
  refine addMonoidHom_eq_of_eqOn_gen Γ hS φ ψ fun s hs => ?_
  exact congrFun hφψ ⟨s, hs⟩

theorem exists_isParabolicHom_apply_eq_periodOf :
    ∃ Φ : Additive Γ →+ (Module.Dual ℂ (CuspForm Γ 2)), ModularCurve.Period.IsParabolicHom Γ Φ ∧
      ∀ γ : Γ, Φ (Additive.ofMul γ) = ModularCurve.periodOf Γ γ := by
  refine ⟨AddMonoidHom.mk' (fun x => ModularCurve.periodOf Γ (Additive.toMul x)) ?_, ?_, fun γ => rfl⟩
  · intro x y
    apply LinearMap.ext
    intro f
    show ModularCurve.periodOf Γ (Additive.toMul x * Additive.toMul y) f =
      ModularCurve.periodOf Γ (Additive.toMul x) f + ModularCurve.periodOf Γ (Additive.toMul y) f
    rw [← ModularCurve.periodMapOf_apply_eq_periodOf, ← ModularCurve.periodMapOf_apply_eq_periodOf,
      ← ModularCurve.periodMapOf_apply_eq_periodOf, ofMul_mul, map_add]
  · intro γ hγ
    apply LinearMap.ext
    intro f
    show ModularCurve.periodOf Γ γ f = 0
    rw [← ModularCurve.periodMapOf_apply_eq_periodOf]
    exact ModularCurve.periodMapOf_mem_parabolicHoms Γ f γ hγ

theorem finrank_parabolicHoms_real_le (hΓ : IsCongruenceSubgroup Γ) :
    Module.Finite ℝ (ModularCurve.Period.parabolicHoms ℝ Γ ℝ) ∧
      Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Γ ℝ) ≤ 2 * Module.finrank ℂ (CuspForm Γ 2) := by
  obtain ⟨n, b, hb⟩ := ModularCurve.Period.exists_basis_parabolicHoms_of_isAddTorsionFree Γ
  obtain ⟨bR, -⟩ := hb ℝ
  refine ⟨Module.Finite.of_basis bR, ?_⟩
  rw [Module.finrank_eq_card_basis bR, ← Module.finrank_eq_card_basis b]
  exact ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup Γ hΓ

theorem main (hΓ : IsCongruenceSubgroup Γ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.periodLatticeOf Γ)),
      LinearIndependent ℝ (fun i => ((b i : ModularCurve.periodLatticeOf Γ) : (Module.Dual ℂ (CuspForm Γ 2)))) ∧
        Submodule.span ℝ (Set.range fun i => ((b i : ModularCurve.periodLatticeOf Γ) : (Module.Dual ℂ (CuspForm Γ 2)))) = ⊤ := by
  classical
  haveI : FiniteDimensional ℂ (CuspForm Γ 2) :=
    CuspForm.finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) 2

  obtain ⟨Φ, hΦpar, hΦ⟩ := exists_isParabolicHom_apply_eq_periodOf Γ
  set Λ : Submodule ℤ (Module.Dual ℂ (CuspForm Γ 2)) := ModularCurve.periodLatticeOf Γ with hΛdef
  have hΦmem : ∀ x : Additive Γ, Φ x ∈ Λ := fun x => by
    rw [show x = Additive.ofMul (Additive.toMul x) from rfl, hΦ]
    exact ModularCurve.periodOf_mem_periodLatticeOf Γ _

  let Φ' : Additive Γ →+ Λ := Φ.codRestrict Λ hΦmem
  have hΦ'coe : ∀ x, ((Φ' x : Λ) : (Module.Dual ℂ (CuspForm Γ 2))) = Φ x := fun x => rfl
  have hΦ'surj : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    have : ∀ y ∈ Λ, ∃ x, Φ x = y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨γ, rfl⟩ := hy
        exact ⟨Additive.ofMul γ, hΦ γ⟩
      | zero => exact ⟨0, map_zero Φ⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, rfl⟩ := hy
        obtain ⟨c, rfl⟩ := hz
        exact ⟨a + c, map_add Φ a c⟩
      | smul m y _ hy =>
        obtain ⟨a, rfl⟩ := hy
        exact ⟨m • a, map_zsmul Φ m a⟩
    obtain ⟨x, hx⟩ := this y hy
    exact ⟨x, Subtype.ext hx⟩

  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (fg_Gamma Γ)

  have hΛfg : Λ.FG := by
    refine Submodule.fg_def.mpr ⟨(fun s : Γ => ModularCurve.periodOf Γ s) '' S, hSfin.image _, ?_⟩
    rw [hΛdef]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_subset_range _ _)
    · unfold ModularCurve.periodLatticeOf
      rw [Submodule.span_le]
      rintro _ ⟨γ, rfl⟩
      have hγ : γ ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top _
      induction hγ using Subgroup.closure_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | one =>
        rw [← hΦ]
        change Φ 0 ∈ _
        rw [map_zero]; exact Submodule.zero_mem _
      | mul y z _ _ hy hz =>
        rw [← hΦ] at hy hz ⊢
        have : Additive.ofMul (y * z) = Additive.ofMul y + Additive.ofMul z := rfl
        rw [this, map_add]
        exact Submodule.add_mem _ hy hz
      | inv y _ hy =>
        rw [← hΦ] at hy ⊢
        have : Additive.ofMul y⁻¹ = -Additive.ofMul y := rfl
        rw [this, map_neg]
        exact Submodule.neg_mem _ hy
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛfg
  haveI : IsAddTorsionFree (Module.Dual ℂ (CuspForm Γ 2)) := (have := IsAddTorsionFree.of_isTorsionFree ℂ (Module.Dual ℂ (CuspForm Γ 2)); inferInstance)
  haveI : Module.Free ℤ Λ := Module.free_of_finite_type_torsion_free'

  set n := Module.finrank ℤ Λ
  let b : Module.Basis (Fin n) ℤ Λ := Module.finBasis ℤ Λ

  have hU : Submodule.span ℝ (Set.range fun γ : Γ => ModularCurve.periodOf Γ γ) =
      (⊤ : Submodule ℝ (Module.Dual ℂ (CuspForm Γ 2))) := by
    by_contra hne
    obtain ⟨g, hg0, hUg⟩ :=
      Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)

    let G : Module.Dual ℂ (Module.Dual ℂ (CuspForm Γ 2)) := Module.Dual.extendRCLike (𝕜 := ℂ) g
    obtain ⟨v, hv⟩ := (Module.evalEquiv ℂ (CuspForm Γ 2)).surjective G
    have hGv : ∀ φ : (Module.Dual ℂ (CuspForm Γ 2)), G φ = φ v := fun φ => by
      rw [← hv, Module.evalEquiv_apply, Module.Dual.eval_apply]
    have hgre : ∀ φ : (Module.Dual ℂ (CuspForm Γ 2)), g φ = (φ v).re := fun φ => by
      rw [← hGv]
      exact (Module.Dual.re_extendRCLike_apply (𝕜 := ℂ) g φ).symm
    have hv0 : v = 0 := by
      refine ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero Γ v fun γ => ?_
      rw [← hgre]
      have := hUg (Submodule.subset_span ⟨γ, rfl⟩)
      simpa using this
    apply hg0
    ext φ
    rw [hgre, hv0, map_zero]
    simp

  haveI : Module.Finite ℝ (Additive Γ →+ ℝ) := finite_addMonoidHom_real Γ

  let ψ₀ : Fin n → (Additive Γ →+ ℝ) := fun i =>
    (Int.castAddHom ℝ).comp ((b.coord i).toAddMonoidHom.comp Φ')
  have hψ₀ : ∀ i x, ψ₀ i x = ((b.coord i (Φ' x) : ℤ) : ℝ) := fun i x => rfl
  have hψpar : ∀ i, ModularCurve.Period.IsParabolicHom Γ (ψ₀ i) := by
    intro i γ hγ
    have h0 : Φ' (Additive.ofMul γ) = 0 := Subtype.ext (by rw [hΦ'coe, hΦpar γ hγ]; rfl)
    rw [hψ₀, h0, map_zero, Int.cast_zero]
  let ψ : Fin n → ModularCurve.Period.parabolicHoms ℝ Γ ℝ := fun i => ⟨ψ₀ i, hψpar i⟩
  have hψli : LinearIndependent ℝ ψ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hc' : ∀ x : Additive Γ, ∑ i, c i * ((b.coord i (Φ' x) : ℤ) : ℝ) = 0 := by
      intro x
      have := congrArg (fun χ : ModularCurve.Period.parabolicHoms ℝ Γ ℝ =>
        ((χ : Additive Γ →+ ℝ) x)) hc
      simpa [ψ, hψ₀, Submodule.coe_sum, AddMonoidHom.finsetSum_apply] using this
    obtain ⟨x, hx⟩ := hΦ'surj (b j)
    have := hc' x
    rw [hx] at this
    simpa [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] using this
  obtain ⟨hparfin, hparle⟩ := finrank_parabolicHoms_real_le Γ hΓ
  haveI := hparfin
  have hn_le_par : n ≤ Module.finrank ℝ (ModularCurve.Period.parabolicHoms ℝ Γ ℝ) := by
    simpa using hψli.fintype_card_le_finrank
  have hDfin : Module.finrank ℝ (Module.Dual ℂ (CuspForm Γ 2)) = 2 * Module.finrank ℂ (CuspForm Γ 2) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (Module.Dual ℂ (CuspForm Γ 2)), Complex.finrank_real_complex, Subspace.dual_finrank_eq]
  have hn_le : n ≤ Module.finrank ℝ (Module.Dual ℂ (CuspForm Γ 2)) := by
    rw [hDfin]
    exact hn_le_par.trans hparle

  let w : Fin n → (Module.Dual ℂ (CuspForm Γ 2)) := fun i => ((b i : Λ) : (Module.Dual ℂ (CuspForm Γ 2)))
  have hΛw : Submodule.span ℤ (Set.range w) = Λ := by
    have h := congrArg (Submodule.map Λ.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h
  have hΛ_le : ∀ y ∈ Λ, y ∈ Submodule.span ℝ (Set.range w) := by
    intro y hy
    rw [← hΛw] at hy
    exact Submodule.span_le_restrictScalars ℤ ℝ _ hy
  have hspan : Submodule.span ℝ (Set.range w) = ⊤ := by
    rw [eq_top_iff, ← hU, Submodule.span_le]
    rintro _ ⟨γ, rfl⟩
    exact hΛ_le _ (ModularCurve.periodOf_mem_periodLatticeOf Γ γ)
  haveI : Module.Finite ℝ (Module.Dual ℂ (CuspForm Γ 2)) := by
    rw [Module.finite_def, ← hspan]
    exact Submodule.fg_span (Set.finite_range w)
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (Module.Dual ℂ (CuspForm Γ 2)) := by
    refine le_antisymm (by simpa using hn_le) ?_
    have h1 := finrank_range_le_card (R := ℝ) w
    rw [Set.finrank, hspan, finrank_top] at h1
    exact h1
  exact ⟨n, b, linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hcard, hspan⟩

end ModularCurve.PeriodRealStructureOf

end

theorem solution (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (ModularCurve.periodLatticeOf Γ)),
      LinearIndependent ℝ (fun i => ((b i : ModularCurve.periodLatticeOf Γ) :
          Module.Dual ℂ (CuspForm Γ 2))) ∧
        Submodule.span ℝ (Set.range fun i => ((b i : ModularCurve.periodLatticeOf Γ) :
          Module.Dual ℂ (CuspForm Γ 2))) = ⊤ := by
  haveI : Γ.FiniteIndex := hΓ.finiteIndex
  exact ModularCurve.PeriodRealStructureOf.main Γ hΓ
