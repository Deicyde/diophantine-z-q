/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq (git blob 3d8c034e9066434062e66a921a3fddb9882814a4, sha256 e0b4a3d77d73e800b6bd856ca0ca385410806934a0599e0bd5fe7a7a900895d0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Gamma0CoeffCohomology
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem HeckeEis.existsUnique_coeffCocycles_sl2z_apply_S_ST_eq
    (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V]
    (ρ : Representation K (Matrix.SpecialLinearGroup (Fin 2) ℤ) V) (x y : V)
    (hx : x + ρ ModularGroup.S x = 0)
    (hy : y + ρ (ModularGroup.S * ModularGroup.T) y
        + ρ (ModularGroup.S * ModularGroup.T) (ρ (ModularGroup.S * ModularGroup.T) y) = 0) :
    ∃! z : ↥(HeckeEis.coeffCocycles ρ),
      (z : Matrix.SpecialLinearGroup (Fin 2) ℤ → V) ModularGroup.S = x
        ∧ (z : Matrix.SpecialLinearGroup (Fin 2) ℤ → V) (ModularGroup.S * ModularGroup.T) = y := by
  revert K V ρ x y hx hy
  exact @_root_.P2MW.S_HeckeEis_existsUnique_coeffCocycles_sl2z_apply_S_ST_eq.solution
