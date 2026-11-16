/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent
    {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsAffineHom ι]
    {q : P ⟶ Spec (CommRingCat.of A)} (G : OModulePresheaf q) (hq : G.IsQuasicoherent)
    {i : ℕ} (c : Fin (i + 1) → Fin (r + 1)) (d : ℕ) (t : G.obj (⨅ v, ProjSpace.pullbackChart ι (c v))) :
    ∃ (N : ℕ) (t' : ∀ j : Fin (r + 1), G.obj (ProjSpace.pullbackChart ι j)),
      OModulePresheaf.FramesCompat ι G (d + N * (i + 1)) t' ∧
      ∀ j : Fin (r + 1),
        G.res (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
            (t' j) =
          ((∏ v : Fin (i + 1), ProjSpace.restrictFun
                (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
                (ProjSpace.frameUnit ι j (c v))) ^ N *
              ProjSpace.restrictFun
                (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
                (ProjSpace.frameUnit ι j (c 0)) ^ d) •
            G.res (inf_le_right : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ⨅ v, ProjSpace.pullbackChart ι (c v)) t := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.solution
