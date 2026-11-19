/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_of_transcendental_j (git blob 3d328542ebca75997e852b07572afbc2f3ef949a, sha256 78363cdfa309386f1866b0bd9970364174fe21164bbd9bdcafc7c060d1a7f0a8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0ModL
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_of_transcendental_j

open AlgebraicCurve ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u v in

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    ∃ Φ : {H : AddSubgroup (E.baseChange Ω).toAffine.Point // IsAddCyclic H ∧ Nat.card H = N} ≃
        {ψ : modularFunctionFieldFullC K N →ₐ[K] Ω //
          ψ ⟨jqModC K, jqModC_mem_full K N⟩ = algebraMap k Ω E.j},
      ∀ (σ : Ω ≃ₐ[k] Ω) (H H' : {H : AddSubgroup (E.baseChange Ω).toAffine.Point //
          IsAddCyclic H ∧ Nat.card H = N}),
        H'.1 = H.1.map (WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω)) →
          ((Φ H').1 : modularFunctionFieldFullC K N →ₐ[K] Ω) =
            ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp (Φ H).1 := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N

  have hNk : (N : k) ≠ 0 := fun h => hN <| (algebraMap K k).injective (by
    rw [map_natCast, map_zero]; exact h)

  have hj₀ : Transcendental K (algebraMap k Ω E.j) :=
    (transcendental_algebraMap_iff (algebraMap k Ω).injective).2 hE

  obtain ⟨Θ, hΘ⟩ :=
    WeierstrassCurve.exists_equiv_addSubgroup_isAddCyclic_isRoot_modularPolynomial_of_transcendental_j
      K N data k Ω hNk E hE hfull

  obtain ⟨e, he⟩ :=
    ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental
      K N hN data Ω (algebraMap k Ω E.j) hj₀
  refine ⟨Θ.trans e.symm, fun σ H H' hH => ?_⟩

  set ψ := e.symm (Θ H) with hψ
  have hψσ : ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ.1 ⟨jqModC K, jqModC_mem_full K N⟩ =
      algebraMap k Ω E.j := by
    rw [AlgHom.comp_apply, ψ.2, AlgHom.restrictScalars_apply, AlgHom.commutes]

  have key : e ⟨((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ.1, hψσ⟩ = Θ H' := by
    apply Subtype.ext
    rw [he, hΘ σ H H' hH]
    show σ (ψ.1 ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩) = σ (Θ H).1
    rw [← he ψ, hψ, Equiv.apply_symm_apply]
  show (e.symm (Θ H')).1 = ((σ : Ω →ₐ[k] Ω).restrictScalars K).comp ψ.1
  rw [← key, Equiv.symm_apply_apply]
