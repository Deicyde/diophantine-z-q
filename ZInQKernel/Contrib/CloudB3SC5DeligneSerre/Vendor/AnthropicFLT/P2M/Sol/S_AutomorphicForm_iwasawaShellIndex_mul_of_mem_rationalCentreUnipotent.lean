/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent (git blob 06d816b2dbadaf9b655284cfe8cf2bd168d408e3, sha256 5c787e125dda06f3d17c8d57e777f3e8fa93975d4c4362035c5e663a70431cf3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RationalCentreUnipotentQuotient
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IwasawaShellIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent

set_option autoImplicit false

open _root_.MeasureTheory
open _root_.NumberField
open _root_.NumberField.AdelicHaar
open _root_.NumberField.AdelicLevel
open _root_.AutomorphicForm
namespace AutomorphicForm
end AutomorphicForm
open _root_.P2MW.S_AutomorphicForm_iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent.AutomorphicForm
open _root_.IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace AutomorphicForm export _root_.AutomorphicForm (rationalCentreUnipotent AdelicGL2 globalPoints centralScalar iwasawaShellIndex iwasawaShellIndex_centralScalar_mul iwasawaShellIndex_unipotentGL2_mul) end AutomorphicForm
open scoped _root_.AutomorphicForm in

theorem AutomorphicForm.globalPoints_scalar_eq_centralScalar (K : Type) [Field K] [NumberField K] (a : Kˣ) :
    globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a) =
      centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K)) i j) =
    (Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : AdelicGL2 (𝓞 K) K) (hx : x ∈ rationalCentreUnipotent K) (g : AdelicGL2 (𝓞 K) K) :
    iwasawaShellIndex K v (x * g) = iwasawaShellIndex K v g := by
  revert g
  rw [rationalCentreUnipotent, Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun x _ => ∀ g, iwasawaShellIndex K v (x * g) = iwasawaShellIndex K v g)
    ?_ ?_ ?_ ?_ hx
  · intro x hx g
    rcases hx with hx | hx
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [MonoidHom.comp_apply, globalPoints_scalar_eq_centralScalar, iwasawaShellIndex_centralScalar_mul]
    · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hx
      exact iwasawaShellIndex_unipotentGL2_mul v g (Multiplicative.toAdd y)
  · intro g; rw [one_mul]
  · intro x y _ _ hx hy g
    rw [mul_assoc, hx, hy]
  · intro x _ hx g
    have := hx (x⁻¹ * g)
    rw [mul_inv_cancel_left] at this
    exact this.symm
