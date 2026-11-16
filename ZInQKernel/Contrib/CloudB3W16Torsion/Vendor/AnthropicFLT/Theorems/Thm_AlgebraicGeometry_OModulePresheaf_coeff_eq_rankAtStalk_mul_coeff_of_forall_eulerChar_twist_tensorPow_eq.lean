/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π] [IsIntegral V]
    (K : V.OrderedAffineCover) (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (d : ℕ) (hd : topologicalKrullDim V ≤ d)
    (q : Polynomial ℚ)
    (hq : ∀ m : ℕ, ((OModulePresheaf.ofModules π (L.tensorPow m)).eulerChar K : ℚ) = q.eval (m : ℚ))
    (F : OModulePresheaf π) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (p : Polynomial ℚ)
    (hp : ∀ m : ℕ, ((F.twist (L.tensorPow m)).eulerChar K : ℚ) = p.eval (m : ℚ))
    (U₀ : V.affineOpens) (𝔭 : PrimeSpectrum Γ(V, U₀.1)) (h𝔭 : 𝔭.asIdeal = ⊥) :
    p.coeff d = (Module.rankAtStalk (R := Γ(V, U₀.1)) (F.obj U₀.1) 𝔭 : ℚ) * q.coeff d := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq.solution
