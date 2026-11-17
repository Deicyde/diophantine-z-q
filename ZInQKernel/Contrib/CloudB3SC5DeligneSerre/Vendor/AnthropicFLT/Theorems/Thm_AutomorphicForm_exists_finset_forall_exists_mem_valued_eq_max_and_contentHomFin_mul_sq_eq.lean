/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq (git blob 612d92077bbd0bcb95cb4dba9bcf65bb7bddec6a, sha256 e51d6764e55c20d268f668d4f2f32616e366a45fc231f0662ef9c6b4a59335fa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem AutomorphicForm.exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq
    (F : Type) [Field F] [NumberField F] :
    ∃ R : Finset ((IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ),
      ∀ g : Matrix.GeneralLinearGroup (Fin 2)
        (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F),
        ∃ a ∈ R, ∃ d : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ,
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
            Valued.v ((d : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F) v) =
              max
                (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 0 *
                    ((a⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)ˣ) :
                      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) v))
                (Valued.v (((g : Matrix (Fin 2) (Fin 2)
                      (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) 1 1) v))) ∧
          AutomorphicForm.contentHomFin F a * AutomorphicForm.contentHomFin F d ^ 2 =
            AutomorphicForm.contentHomFin F (Matrix.GeneralLinearGroup.det g) := by
  revert F
  exact @_root_.P2MW.S_AutomorphicForm_exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq.solution
