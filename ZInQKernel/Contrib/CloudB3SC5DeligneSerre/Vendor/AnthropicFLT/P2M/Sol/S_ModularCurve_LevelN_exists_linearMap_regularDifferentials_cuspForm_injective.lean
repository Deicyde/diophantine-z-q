/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective (git blob 3900c12998697540cbc2341b5826fa4de592d9f4, sha256 2feed951bb0264e5f1dad1fb3505676cd0ab2f63c71a3996b0fc385845d1a9fe).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_LevelN_exists_linearMap_regularDifferentials_mdifferentiable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_LevelN_isZeroAtImInfty_slash_of_mem_regularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_LevelN_slash_eq_self_of_mem_Gamma_of_mul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve.LevelN
end ModularCurve.LevelN
namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve
end P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve
namespace P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve.LevelN
end P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve.LevelN
namespace P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve.LevelN.CuspFormAssembly
end P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve.LevelN.CuspFormAssembly

namespace P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

namespace ModularCurve
export _root_.ModularCurve (LevelN.ring LevelN.exists_linearMap_regularDifferentials_mdifferentiable LevelN.isZeroAtImInfty_slash_of_mem_regularDifferentials LevelN.slash_eq_self_of_mem_Gamma_of_mul_eq)
namespace LevelN
export _root_.ModularCurve.LevelN (ring exists_linearMap_regularDifferentials_mdifferentiable isZeroAtImInfty_slash_of_mem_regularDifferentials slash_eq_self_of_mem_Gamma_of_mul_eq)
namespace CuspFormAssembly
open _root_.ModularCurve.LevelN
open _root_.ModularCurve

variable (N : ℕ) [NeZero N]
variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring N) K] [IsScalarTower ℂ (ring N) K]
  [IsFractionRing (ring N) K]

def Ψ : AlgebraicCurve.regularDifferentials ℂ K →ₗ[ℂ] (ℍ → ℂ) :=
  (exists_linearMap_regularDifferentials_mdifferentiable N K).2.choose

theorem Ψ_spec :
    Function.Injective (Ψ N K) ∧
      (∀ ω, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Ψ N K ω)) ∧
      ∀ (ω : AlgebraicCurve.regularDifferentials ℂ K) (a b c e : ℍ → ℂ)
        (ha : a ∈ ring N) (hb : b ∈ ring N) (hc : c ∈ ring N) (he : e ∈ ring N),
        b ≠ 0 → e ≠ 0 →
        (ω : KaehlerDifferential ℂ K) =
          (algebraMap (ring N) K ⟨a, ha⟩ / algebraMap (ring N) K ⟨b, hb⟩) •
            KaehlerDifferential.D ℂ K (algebraMap (ring N) K ⟨c, hc⟩ / algebraMap (ring N) K ⟨e, he⟩) →
        ∀ τ : ℍ, Ψ N K ω τ * b τ * e τ ^ 2 =
          a τ * (e τ * deriv (c ∘ ofComplex) τ - c τ * deriv (e ∘ ofComplex) τ) :=
  (exists_linearMap_regularDifferentials_mdifferentiable N K).2.choose_spec

theorem exists_rep (ω : KaehlerDifferential ℂ K) (hω : ω ∈ AlgebraicCurve.regularDifferentials ℂ K) :
    ∃ (a b c e : ℍ → ℂ) (ha : a ∈ ring N) (hb : b ∈ ring N) (hc : c ∈ ring N) (he : e ∈ ring N),
      b ≠ 0 ∧ e ≠ 0 ∧
      ω = (algebraMap (ring N) K ⟨a, ha⟩ / algebraMap (ring N) K ⟨b, hb⟩) •
        KaehlerDifferential.D ℂ K (algebraMap (ring N) K ⟨c, hc⟩ / algebraMap (ring N) K ⟨e, he⟩) :=
  (exists_linearMap_regularDifferentials_mdifferentiable N K).1 ω hω

def toCuspForm (ω : AlgebraicCurve.regularDifferentials ℂ K) :
    CuspForm (CongruenceSubgroup.Gamma N) 2 where
  toFun := Ψ N K ω
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := hA
    obtain ⟨a, b, c, e, ha, hb, hc, he, hb0, he0, hω⟩ := exists_rep N K (ω : KaehlerDifferential ℂ K) ω.2
    exact slash_eq_self_of_mem_Gamma_of_mul_eq N (Ψ N K ω) ((Ψ_spec N K).2.1 ω) a b c e ha hb hc he
      hb0 he0 ((Ψ_spec N K).2.2 ω a b c e ha hb hc he hb0 he0 hω) γ hγ
  holo' := (Ψ_spec N K).2.1 ω
  zero_at_cusps' := by
    intro cusp hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro δ _
    exact isZeroAtImInfty_slash_of_mem_regularDifferentials N K (ω : KaehlerDifferential ℂ K) ω.2
      (Ψ N K ω) (fun a b c e ha hb hc he hb0 he0 hω => (Ψ_spec N K).2.2 ω a b c e ha hb hc he hb0 he0 hω) δ

@[scoped simp]
theorem coe_toCuspForm (ω : AlgebraicCurve.regularDifferentials ℂ K) :
    ((toCuspForm N K ω : CuspForm (CongruenceSubgroup.Gamma N) 2) : ℍ → ℂ) = Ψ N K ω := rfl

def Φ : AlgebraicCurve.regularDifferentials ℂ K →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma N) 2 where
  toFun := toCuspForm N K
  map_add' ω₁ ω₂ := by
    apply DFunLike.ext'
    simp [map_add]
  map_smul' c ω := by
    apply DFunLike.ext'
    simp [map_smul]

theorem Φ_apply (ω : AlgebraicCurve.regularDifferentials ℂ K) : Φ N K ω = toCuspForm N K ω := rfl

theorem Φ_injective : Function.Injective (Φ N K) := by
  intro ω₁ ω₂ h
  apply (Ψ_spec N K).1
  have := congrArg (fun f : CuspForm (CongruenceSubgroup.Gamma N) 2 => (f : ℍ → ℂ)) h
  simpa only [Φ_apply, coe_toCuspForm] using this

end ModularCurve.LevelN.CuspFormAssembly
open scoped _root_.P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve _root_.P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve.LevelN _root_.P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve.LevelN.CuspFormAssembly
open scoped _root_.P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve _root_.P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve.LevelN
open scoped _root_.P2MW.S_ModularCurve_LevelN_exists_linearMap_regularDifferentials_cuspForm_injective.ModularCurve

theorem solution (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] :
    ∃ Φ : AlgebraicCurve.regularDifferentials ℂ K →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma N) 2,
      Function.Injective Φ :=
  ⟨ModularCurve.LevelN.CuspFormAssembly.Φ N K, ModularCurve.LevelN.CuspFormAssembly.Φ_injective N K⟩
