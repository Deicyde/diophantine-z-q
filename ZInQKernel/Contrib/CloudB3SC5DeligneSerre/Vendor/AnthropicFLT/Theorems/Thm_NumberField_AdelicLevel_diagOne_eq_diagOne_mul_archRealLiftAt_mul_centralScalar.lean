/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicLevel_diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar (git blob 64104f3f1bfd6dd4214d20711ddadd14532cf706, sha256 2a07d953aae76928b755920e68919941a1ff879f0fa046cd36f637bd5a94a19d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicLevel_diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain

theorem NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (u : ℝ) (hu : 0 < u)
    (a b' z : (AdeleRing (𝓞 K) K)ˣ)
    (ha : ((a : (AdeleRing (𝓞 K) K))).2 = 1) (hb' : ((b' : (AdeleRing (𝓞 K) K))).2 = 1) (hz : ((z : (AdeleRing (𝓞 K) K))).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : (AdeleRing (𝓞 K) K))).1 w' = ((b' : (AdeleRing (𝓞 K) K))).1 w')
    (hbw : ((b' : (AdeleRing (𝓞 K) K))).1 w = 1)
    (haw : InfinitePlace.Completion.ringEquivRealOfIsReal hw (((a : (AdeleRing (𝓞 K) K))).1 w) = ε * u)
    (hzw' : ∀ w' : InfinitePlace K, w' ≠ w → ((z : (AdeleRing (𝓞 K) K))).1 w' = 1)
    (hzw : InfinitePlace.Completion.ringEquivRealOfIsReal hw (((z : (AdeleRing (𝓞 K) K))).1 w) = Real.sqrt u) :
    diagOne a = diagOne b' * archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt u, 0; 0, (Real.sqrt u)⁻¹]) *
        centralScalar (𝓞 K) K z ∧
      archComponent K w (glArch (𝓞 K) K (diagOne b')) = 1 := by
  revert K w hw ε hε u hu a b' z ha hb' hz hab hbw haw hzw' hzw
  exact @_root_.P2MW.S_NumberField_AdelicLevel_diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar.solution
