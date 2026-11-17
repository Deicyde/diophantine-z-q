/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule (git blob 9c2de260dac8ecde380bd05a48e590b7f24029c9, sha256 bd1827cc15d9cf8a69559b7817cfd2f91e67f50c33bf510ef6902d06a367d5b4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchSpherical
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule
    (F : Type) [Field F] [NumberField F]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hxc : Continuous x) (hxt : x ∈ archCutSubmodule F tys) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ)))) ∧
    (∀ v ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))), Continuous v) ∧
    Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))) ≤ archCutSubmodule F tys ∧
    ∀ v ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))), ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
      (fun g : AdelicGL2 (𝓞 F) F => v (g * adelicArchGLIncl F (ι κ))) ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))) := by
  revert F ι hι tys x hxc hxt
  exact @_root_.P2MW.S_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule.solution
