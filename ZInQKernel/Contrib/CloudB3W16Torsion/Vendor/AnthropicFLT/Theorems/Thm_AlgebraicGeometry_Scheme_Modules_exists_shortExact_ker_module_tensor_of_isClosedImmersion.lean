/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_shortExact_ker_module_tensor_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] {n : ℕ} (F : X.Modules)
    (hF : Scheme.Modules.IsLocallyFreeOfRank n F) :
    ∃ S : ShortComplex X.Modules, S.ShortExact ∧
      Nonempty (S.X₁ ≅ i.ker.module ⊗ F) ∧ Nonempty (S.X₂ ≅ F) ∧
      Nonempty (S.X₃ ≅ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_shortExact_ker_module_tensor_of_isClosedImmersion.solution
