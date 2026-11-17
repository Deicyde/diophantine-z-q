/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC (git blob b335dde0b140d7026acdbced79714540923739e3, sha256 ebd37d24894ac87a5cc4aac67bf80cbbe6d5515c5e2baf5ccf777f15a87820af).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ComplexConjugate AutomorphicForm.ComplexIwasawa

theorem AutomorphicForm.ComplexIwasawa.weyl_mul_unipotent_mul_eq_borel_mul_kC
    {g : Matrix (Fin 2) (Fin 2) ℂ} (hg : g.det ≠ 0) (z : ℂ) :
    !![(0 : ℂ), 1; 1, 0] * !![1, z; 0, 1] * g
      = !![-g.det / (radC g z : ℂ),
            (g 1 0 * conj (botP g z) + g 1 1 * conj (botQ g z)) / (radC g z : ℂ);
           0, (radC g z : ℂ)] * kC g z := by
  revert g hg z
  exact @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_weyl_mul_unipotent_mul_eq_borel_mul_kC.solution
