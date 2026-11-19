/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int (git blob 63fa6e0e982cc9aa1ee17c7f2732c9bda03f7718, sha256 e46017955cc62ad510416d832c9cca908dfe2879028cba7f2e4534d66ef621e7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_periodOf_mul_edgeIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_sum_periodOf_mul_edgeIntegral_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_periodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_cuspForm_petersson_eq_of_finiteIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_eq_zero_of_forall_re_periodOf_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_isParabolicHom_apply_eq_periodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_finiteDimensional_of_isArithmetic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_petersson_mem_periodLatticeOf_iff_re_periodOf_int

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open UpperHalfPlane MeasureTheory

namespace ModularCurve
export _root_.ModularCurve (periodOf periodLatticeOf period periodLattice integral_petersson_gammaFundamentalSet_eq_sum_conj_periodOf_mul_edgeIntegral sum_periodOf_mul_edgeIntegral_eq_zero exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_periodOf exists_cuspForm_petersson_eq_of_finiteIndex eq_zero_of_forall_re_periodOf_eq_zero finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup exists_isParabolicHom_apply_eq_periodOf)
namespace Ws49
namespace RiemannFormIntegralityOf
open _root_.ModularCurve

open ModularCurve.Period

section FG

variable (Γ : Subgroup SL(2, ℤ))

theorem fg_SL2Z : Group.FG SL(2, ℤ) :=
  Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
    SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩

theorem fg_Gamma0 [Γ.FiniteIndex] : Group.FG Γ := by
  haveI := fg_SL2Z
  infer_instance

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

theorem finite_addMonoidHom_real [Γ.FiniteIndex] : Module.Finite ℝ (Additive Γ →+ ℝ) := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (fg_Gamma0 Γ)
  haveI : Fintype S := hSfin.fintype
  let res : (Additive Γ →+ ℝ) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun φ s => φ (Additive.ofMul (s : Γ))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine Module.Finite.of_injective res ?_
  intro φ ψ hφψ
  refine addMonoidHom_eq_of_eqOn_gen Γ hS φ ψ fun s hs => ?_
  exact congrFun hφψ ⟨s, hs⟩

end FG

section RealES

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)



include hΓ in

theorem exists_cuspForm_re_period_eq (φ : Additive Γ →+ ℝ) (hφ : IsParabolicHom Γ φ) :
    ∃ f : (CuspForm Γ 2), ∀ γ : Γ, (ModularCurve.periodOf Γ γ f).re = φ (Additive.ofMul γ) := by
  classical
  haveI : FiniteDimensional ℂ (CuspForm Γ 2) :=
    CuspForm.finiteDimensional_of_isArithmetic ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2
  haveI : Module.Finite ℝ (Additive Γ →+ ℝ) := finite_addMonoidHom_real Γ
  obtain ⟨Φ, hΦpar, hΦ⟩ := ModularCurve.exists_isParabolicHom_apply_eq_periodOf Γ

  let reΦ : (CuspForm Γ 2) → (Additive Γ →+ ℝ) := fun f =>
    { toFun := fun x => (Φ x f).re
      map_zero' := by simp only [map_zero, LinearMap.zero_apply, Complex.zero_re]
      map_add' := fun x y => by simp only [map_add, LinearMap.add_apply, Complex.add_re] }
  have hreΦ : ∀ f x, reΦ f x = (Φ x f).re := fun f x => rfl
  have hreΦpar : ∀ f, IsParabolicHom Γ (reΦ f) := by
    intro f γ hγ
    rw [hreΦ, hΦpar γ hγ, LinearMap.zero_apply, Complex.zero_re]

  let Ψ : (CuspForm Γ 2) →ₗ[ℝ] parabolicHoms ℝ Γ ℝ :=
    { toFun := fun f => ⟨reΦ f, hreΦpar f⟩
      map_add' := fun f g => by
        refine Subtype.ext (AddMonoidHom.ext fun x => ?_)
        simp only [Submodule.coe_add, AddMonoidHom.add_apply, hreΦ, map_add, Complex.add_re]
      map_smul' := fun r f => by
        refine Subtype.ext (AddMonoidHom.ext fun x => ?_)
        simp only [Submodule.coe_smul, AddMonoidHom.smul_apply, RingHom.id_apply, hreΦ,
          smul_eq_mul]
        rw [← Complex.coe_smul, map_smul, smul_eq_mul, Complex.re_ofReal_mul] }
  have hΨ : ∀ (f : (CuspForm Γ 2)) (γ : Γ),
      ((Ψ f : parabolicHoms ℝ Γ ℝ) : Additive Γ →+ ℝ) (Additive.ofMul γ) =
        (ModularCurve.periodOf Γ γ f).re := by
    intro f γ
    change reΦ f (Additive.ofMul γ) = _
    rw [hreΦ, hΦ]

  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    refine ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero Γ f fun γ => ?_
    rw [← hΨ, hf]
    rfl

  have hrange : LinearMap.range Ψ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    rw [LinearMap.finrank_range_of_inj hinj, finrank_real_of_complex]
    exact ModularCurve.finrank_real_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup Γ hΓ
  have hmem : (⟨φ, hφ⟩ : parabolicHoms ℝ Γ ℝ) ∈ LinearMap.range Ψ := by
    rw [hrange]; exact Submodule.mem_top
  obtain ⟨f, hf⟩ := hmem
  refine ⟨f, fun γ => ?_⟩
  rw [← hΨ, hf]

theorem period_mul_and_parabolic :
    (∀ γ δ : Γ, ModularCurve.periodOf Γ (γ * δ) = ModularCurve.periodOf Γ γ + ModularCurve.periodOf Γ δ) ∧
      ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 →
        ModularCurve.periodOf Γ γ = 0 := by
  obtain ⟨Φ, hΦpar, hΦ⟩ := ModularCurve.exists_isParabolicHom_apply_eq_periodOf Γ
  refine ⟨fun γ δ => ?_, fun γ hγ => ?_⟩
  · rw [← hΦ, ← hΦ, ← hΦ, ofMul_mul, map_add]
  · rw [← hΦ]; exact hΦpar γ hγ

end RealES

section Tiling

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)




@[reducible] noncomputable def fintypeQ : Fintype (SL(2, ℤ) ⧸ Γ) := Subgroup.fintypeQuotientOfFiniteIndex

attribute [local instance] fintypeQ

theorem pair_mem (a : SL(2, ℤ)) (q : (SL(2, ℤ) ⧸ Γ)) : (Quotient.out (a • q))⁻¹ * a * Quotient.out q ∈ Γ := by
  have h : (QuotientGroup.mk (Quotient.out (a • q)) : (SL(2, ℤ) ⧸ Γ)) = QuotientGroup.mk (a * Quotient.out q) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [mul_assoc]
  exact QuotientGroup.eq.mp h

noncomputable def gT (q : (SL(2, ℤ) ⧸ Γ)) : Γ :=
  ⟨(Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q, pair_mem Γ _ q⟩

noncomputable def gS (q : (SL(2, ℤ) ⧸ Γ)) : Γ :=
  ⟨(Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q, pair_mem Γ _ q⟩

theorem gT_coe (q : (SL(2, ℤ) ⧸ Γ)) : ((gT Γ q : Γ) : SL(2, ℤ)) =
    (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q := rfl

theorem gS_coe (q : (SL(2, ℤ) ⧸ Γ)) : ((gS Γ q : Γ) : SL(2, ℤ)) =
    (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q := rfl

noncomputable def Gp (g : (CuspForm Γ 2)) (q : (SL(2, ℤ) ⧸ Γ)) (z : ℂ) : ℂ :=
  g ((Quotient.out q)⁻¹ • ofComplex z) /
    denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2

theorem Gp_spec (g : (CuspForm Γ 2)) : ∀ (q : (SL(2, ℤ) ⧸ Γ)) (z : ℂ), Gp Γ g q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
    denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2 := fun _ _ => rfl

noncomputable def ray (g : (CuspForm Γ 2)) (q : (SL(2, ℤ) ⧸ Γ)) : ℂ :=
  ∫ y in Set.Ioi (Real.sqrt 3 / 2), Gp Γ g q (-(1 / 2) + y * Complex.I)

noncomputable def arc (g : (CuspForm Γ 2)) (q : (SL(2, ℤ) ⧸ Γ)) : ℂ :=
  ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
    Gp Γ g q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))

noncomputable def pet (k g : (CuspForm Γ 2)) : ℂ :=
  ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
    UpperHalfPlane.petersson 2 k g τ

noncomputable def PD (c d : (SL(2, ℤ) ⧸ Γ) → ℂ) (g : (CuspForm Γ 2)) : ℂ :=
  Complex.I * ∑ q : (SL(2, ℤ) ⧸ Γ), c q * ray Γ g q + 1 / 2 * ∑ q : (SL(2, ℤ) ⧸ Γ), d q * arc Γ g q

theorem PD_add (c d c' d' : (SL(2, ℤ) ⧸ Γ) → ℂ) (g : (CuspForm Γ 2)) :
    PD Γ (c + c') (d + d') g = PD Γ c d g + PD Γ c' d' g := by
  simp only [PD, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem PD_zero (g : (CuspForm Γ 2)) : PD Γ 0 0 g = 0 := by
  simp [PD]

theorem PD_neg (c d : (SL(2, ℤ) ⧸ Γ) → ℂ) (g : (CuspForm Γ 2)) : PD Γ (-c) (-d) g = -PD Γ c d g := by
  simp only [PD, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

theorem PD_congr {c d c' d' : (SL(2, ℤ) ⧸ Γ) → ℂ} (hc : ∀ q, c q = c' q) (hd : ∀ q, d q = d' q) (g : (CuspForm Γ 2)) :
    PD Γ c d g = PD Γ c' d' g := by
  rw [show c = c' from funext hc, show d = d' from funext hd]

noncomputable def PDZ (φ : Additive Γ →+ ℤ) (g : (CuspForm Γ 2)) : ℂ :=
  PD Γ (fun q => ((φ (Additive.ofMul (gT Γ q)) : ℤ) : ℂ))
    (fun q => ((φ (Additive.ofMul (gS Γ q)) : ℤ) : ℂ)) g

theorem PDZ_add (φ ψ : Additive Γ →+ ℤ) (g : (CuspForm Γ 2)) : PDZ Γ (φ + ψ) g = PDZ Γ φ g + PDZ Γ ψ g := by
  rw [PDZ, PDZ, PDZ, ← PD_add]
  refine PD_congr Γ (fun q => ?_) (fun q => ?_) g <;> simp

theorem PDZ_zero (g : (CuspForm Γ 2)) : PDZ Γ 0 g = 0 := by
  rw [PDZ, ← PD_zero Γ g]
  refine PD_congr Γ (fun q => ?_) (fun q => ?_) g <;> simp

theorem PDZ_neg (φ : Additive Γ →+ ℤ) (g : (CuspForm Γ 2)) : PDZ Γ (-φ) g = -PDZ Γ φ g := by
  rw [PDZ, PDZ, ← PD_neg]
  refine PD_congr Γ (fun q => ?_) (fun q => ?_) g <;> simp

theorem sum_half_split (a b r : (SL(2, ℤ) ⧸ Γ) → ℂ) :
    ∑ q : (SL(2, ℤ) ⧸ Γ), (a q + b q) / 2 * r q = 1 / 2 * ∑ q : (SL(2, ℤ) ⧸ Γ), a q * r q + 1 / 2 * ∑ q : (SL(2, ℤ) ⧸ Γ), b q * r q := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

include hneg in

theorem bilRe (k g : (CuspForm Γ 2)) :
    Complex.I * pet Γ k g =
      PD Γ (fun q => ((ModularCurve.periodOf Γ (gT Γ q) k).re : ℂ))
        (fun q => ((ModularCurve.periodOf Γ (gS Γ q) k).re : ℂ)) g := by
  have hB := ModularCurve.integral_petersson_gammaFundamentalSet_eq_sum_conj_periodOf_mul_edgeIntegral
    Γ hneg k g (gT Γ) (gS Γ) (gT_coe Γ) (gS_coe Γ) (Gp Γ g) (Gp_spec Γ g)
  have hH := ModularCurve.sum_periodOf_mul_edgeIntegral_eq_zero
    Γ hneg k g (gT Γ) (gS Γ) (gT_coe Γ) (gS_coe Γ) (Gp Γ g) (Gp_spec Γ g)
  simp only [PD, pet, ray, arc, Complex.re_eq_add_conj]
  rw [sum_half_split, sum_half_split]
  change Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
      UpperHalfPlane.petersson 2 k g τ) = _
  linear_combination hB - (1 / 2 : ℂ) * hH

include hneg in

theorem bilRe_int (k g : (CuspForm Γ 2)) (φ : Additive Γ →+ ℤ)
    (hk : ∀ γ : Γ, (ModularCurve.periodOf Γ γ k).re = ((φ (Additive.ofMul γ) : ℤ) : ℝ)) :
    Complex.I * pet Γ k g = PDZ Γ φ g := by
  rw [bilRe Γ hneg, PDZ]
  refine PD_congr Γ (fun q => ?_) (fun q => ?_) g
  · rw [hk]; norm_cast
  · rw [hk]; norm_cast

theorem measurableSet_gammaFundamentalSet :
    MeasurableSet (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) :=
  MeasurableSet.iUnion fun q => (ModularGroup.isClosed_fd.smul (Quotient.out q)⁻¹).measurableSet

theorem pet_conj (k g : (CuspForm Γ 2)) : pet Γ g k = conj (pet Γ k g) := by
  rw [pet, pet, ← integral_conj]
  refine setIntegral_congr_fun (measurableSet_gammaFundamentalSet Γ) fun τ _ => ?_
  simp only [UpperHalfPlane.petersson, map_mul, Complex.conj_conj, zpow_ofNat]
  rw [show conj (((τ : ℍ).im : ℂ) ^ 2) = ((τ : ℍ).im : ℂ) ^ 2 by
    rw [map_pow, Complex.conj_ofReal]]
  ring

theorem eq_of_pet_eq (k f : (CuspForm Γ 2)) (h : ∀ g : (CuspForm Γ 2), pet Γ k g = pet Γ f g) : k = f := by
  haveI : FiniteDimensional ℂ (CuspForm Γ 2) :=
    CuspForm.finiteDimensional_of_isArithmetic ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 2
  have h' : ∀ g : (CuspForm Γ 2), pet Γ g k = pet Γ g f := fun g => by
    rw [pet_conj, pet_conj Γ f, h g]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  obtain ⟨hℓ, hhℓ⟩ := ModularCurve.exists_cuspForm_petersson_eq_of_finiteIndex Γ ℓ
  rw [map_sub, ← hhℓ k, ← hhℓ f, sub_eq_zero]
  change Complex.I * pet Γ hℓ k = Complex.I * pet Γ hℓ f
  rw [h']

end Tiling

end ModularCurve.Ws49.RiemannFormIntegralityOf

open ModularCurve.Ws49.RiemannFormIntegralityOf ModularCurve.Period in
theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (f : CuspForm Γ 2) :
    (∃ Λ ∈ ModularCurve.periodLatticeOf Γ, ∀ g : CuspForm Γ 2,
        Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
          UpperHalfPlane.petersson 2 f g τ) = Λ g) ↔
      ∀ γ : Γ, ∃ m : ℤ, (ModularCurve.periodOf Γ γ f).re = m := by
  letI : Fintype (SL(2, ℤ) ⧸ Γ) := fintypeQ Γ
  obtain ⟨hmul, hpar⟩ := period_mul_and_parabolic Γ
  constructor
  ·
    rintro ⟨Λ, hΛ, hfΛ⟩

    have key : ∀ Λ ∈ ModularCurve.periodLatticeOf Γ,
        ∃ φ : Additive Γ →+ ℤ,
          IsParabolicHom Γ φ ∧
            ∀ g, PDZ Γ φ g = Λ g := by
      intro Λ hΛ
      induction hΛ using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨δ, rfl⟩ := hx
        obtain ⟨φ, hφ, hφδ⟩ :=
          ModularCurve.exists_isParabolicHom_sum_intCast_mul_edgeIntegral_eq_periodOf
            Γ hneg (gT Γ) (gS Γ) (gT_coe Γ) (gS_coe Γ) δ
        exact ⟨φ, hφ, fun g => hφδ g (Gp Γ g) (Gp_spec Γ g)⟩
      | zero => exact ⟨0, fun _ _ => rfl, fun g => by rw [PDZ_zero]; rfl⟩
      | add x y _ _ hx hy =>
        obtain ⟨φ, hφ, hφx⟩ := hx
        obtain ⟨ψ, hψ, hψy⟩ := hy
        refine ⟨φ + ψ, fun γ hγ => ?_, fun g => ?_⟩
        · rw [AddMonoidHom.add_apply, hφ γ hγ, hψ γ hγ, add_zero]
        · rw [PDZ_add, hφx, hψy]; rfl
      | smul n x _ hx =>
        obtain ⟨φ, hφ, hφx⟩ := hx
        refine ⟨n • φ, fun γ hγ => ?_, fun g => ?_⟩
        · rw [AddMonoidHom.smul_apply, hφ γ hγ, smul_zero]
        · rw [LinearMap.smul_apply]
          induction n using Int.induction_on with
          | zero => rw [zero_smul, zero_smul, PDZ_zero]
          | succ m ih => rw [add_smul, one_smul, PDZ_add, ih, add_smul, one_smul, hφx]
          | pred m ih =>
            rw [sub_smul, one_smul, sub_eq_add_neg, PDZ_add, PDZ_neg, ih, sub_smul, one_smul,
              hφx, sub_eq_add_neg]
    obtain ⟨φ, hφ, hφΛ⟩ := key Λ hΛ

    let φR : Additive Γ →+ ℝ := (Int.castAddHom ℝ).comp φ
    have hφR : IsParabolicHom Γ φR := fun γ hγ => by
      simp [φR, hφ γ hγ]
    obtain ⟨k, hk⟩ := exists_cuspForm_re_period_eq Γ hΓ φR hφR
    have hk' : ∀ γ, (ModularCurve.periodOf Γ γ k).re = ((φ (Additive.ofMul γ) : ℤ) : ℝ) := fun γ => by
      rw [hk]; rfl

    have hkf : k = f := by
      refine eq_of_pet_eq Γ k f fun g => ?_
      have e1 := bilRe_int Γ hneg k g φ hk'
      have e2 := hfΛ g
      rw [hφΛ] at e1
      change Complex.I * pet Γ f g = Λ g at e2
      exact mul_left_cancel₀ Complex.I_ne_zero (e1.trans e2.symm)
    intro γ
    exact ⟨φ (Additive.ofMul γ), by rw [← hkf, hk']⟩
  ·
    intro h
    choose m hm using h
    let φ : Additive Γ →+ ℤ :=
      { toFun := fun x => m (Additive.toMul x)
        map_zero' := by
          have h1 : (ModularCurve.periodOf Γ (1 : Γ) f).re = 0 := by
            rw [hpar 1 (by simp), LinearMap.zero_apply, Complex.zero_re]
          have := hm 1
          rw [h1] at this
          change m 1 = 0
          exact_mod_cast this.symm
        map_add' := fun x y => by
          change m (Additive.toMul x * Additive.toMul y) = m (Additive.toMul x) + m (Additive.toMul y)
          have := hm (Additive.toMul x * Additive.toMul y)
          rw [hmul, LinearMap.add_apply, Complex.add_re, hm, hm] at this
          exact_mod_cast this.symm }
    have hφm : ∀ γ, φ (Additive.ofMul γ) = m γ := fun γ => rfl
    have hφ : IsParabolicHom Γ φ := fun γ hγ => by
      have := hm γ
      rw [hpar γ hγ, LinearMap.zero_apply, Complex.zero_re] at this
      rw [hφm]
      exact_mod_cast this.symm
    obtain ⟨Λ, hΛ, hΛφ⟩ :=
      ModularCurve.exists_mem_periodLatticeOf_eq_sum_intCast_mul_edgeIntegral_of_isParabolicHom
        Γ hneg (gT Γ) (gS Γ) (gT_coe Γ) (gS_coe Γ) φ hφ
    refine ⟨Λ, hΛ, fun g => ?_⟩
    have e1 := bilRe_int Γ hneg f g φ (fun γ => by rw [hφm, hm])
    have e2 := hΛφ g (Gp Γ g) (Gp_spec Γ g)
    change Complex.I * pet Γ f g = Λ g
    rw [e1, ← e2]
    rfl
