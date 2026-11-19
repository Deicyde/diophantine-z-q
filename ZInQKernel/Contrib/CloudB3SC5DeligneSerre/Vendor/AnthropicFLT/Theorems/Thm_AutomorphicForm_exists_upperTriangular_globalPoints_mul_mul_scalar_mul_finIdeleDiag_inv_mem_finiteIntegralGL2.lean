/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2 (git blob d80b8f70b630e790b247b5f97162583d90189efb, sha256 0d7fcd9cd751936e3edff3805fb80e6a91170f0a6a1c327610ac34243b2ff31f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem AutomorphicForm.exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2
    (F : Type) [Field F] [NumberField F]
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F))
    (a d : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ)
    (hd : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      Valued.v ((d : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v) =
        max
          (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 0 *
              ((a⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
                IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))
          (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 1) v)))
    (hcls : AutomorphicForm.contentHomFin F a * AutomorphicForm.contentHomFin F d ^ 2 =
      AutomorphicForm.contentHomFin F (Matrix.GeneralLinearGroup.det g)) :
    ∃ b : Matrix.GeneralLinearGroup (Fin 2) F, (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∃ s : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ,
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers F) F
              (AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F b) * g *
            Matrix.GeneralLinearGroup.scalar (Fin 2) s *
          (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers F) F
            (AutomorphicForm.finIdeleDiag F a))⁻¹
        ∈ NumberField.AdelicLevel.finiteIntegralGL2 (NumberField.RingOfIntegers F) F := by
  revert F g a d hd hcls
  exact @_root_.P2MW.S_AutomorphicForm_exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2.solution
