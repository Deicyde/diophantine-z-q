/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite (git blob 85c9927fe9e88695d4fecaa77b659a2863b7e301, sha256 0c595246213190275abc236e5002acfcd582e095ad1d247e04f2afcf0ec36b0b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite
    (K : Type) [Field K] [NumberField K] (D : Set (AdelicGL2 (𝓞 K) K))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (hΘ : Θ.AgreesAwayFromFinite Θ')
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral R') :
    R.centralChar = R'.centralChar := by
  revert K D Θ Θ' hΘ R hR R' hR'
  exact @_root_.P2MW.S_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite.solution
