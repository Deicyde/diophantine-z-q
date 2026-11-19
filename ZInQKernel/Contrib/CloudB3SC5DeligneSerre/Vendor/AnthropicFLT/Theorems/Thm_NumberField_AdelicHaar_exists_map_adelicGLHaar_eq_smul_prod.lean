/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicHaar_exists_map_adelicGLHaar_eq_smul_prod (git blob bbae35416989372cb205ca8ac8bd5c8b8a6be4a6, sha256 4e04f37095611c8520ce011aff2952c923d5867db2721fc80cf464e36e5da838).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicHaar_exists_map_adelicGLHaar_eq_smul_prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory NumberField.AdelicLevel NumberField.AdelicHaar
open scoped NNReal

theorem NumberField.AdelicHaar.exists_map_adelicGLHaar_eq_smul_prod
    (n : Type) [Fintype n] [DecidableEq n]
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (GL n (InfiniteAdeleRing K))] [BorelSpace (GL n (InfiniteAdeleRing K))]
    [MeasurableSpace (GL n (FiniteAdeleRing (𝓞 K) K))] [BorelSpace (GL n (FiniteAdeleRing (𝓞 K) K))]
    (μa : Measure (GL n (InfiniteAdeleRing K))) [μa.IsHaarMeasure] [μa.Regular]
    (μf : Measure (GL n (FiniteAdeleRing (𝓞 K) K))) [μf.IsHaarMeasure] [μf.Regular] :
    ∃ c : ℝ≥0, 0 < c ∧
      (letI := glBorel n (𝓞 K) K
       Measure.map
           (fun x : GL n (AdeleRing (𝓞 K) K) =>
             (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) x,
               Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) x))
           (adelicGLHaar n (𝓞 K) K) = c • μa.prod μf) := by
  revert n K μa μf
  exact @_root_.P2MW.S_NumberField_AdelicHaar_exists_map_adelicGLHaar_eq_smul_prod.solution
