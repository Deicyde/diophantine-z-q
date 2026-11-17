/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_H1_moduleFinite (git blob 5b03437d3a4e604438da9df7f990873e53860dd9, sha256 c44452a0cf8e4571d69d2bad04ac75ba8659f94f2deaa2af3f90fe88a996f494).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import Mathlib.Algebra.Module.Hom
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_H1_moduleFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open CohCarrier

theorem CohCarrier.H1_moduleFinite (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (R : Type*) [CommRing R]
    (A : Type*) [AddCommGroup A] [Module R A] [IsNoetherianRing R] [Module.Finite R A] :
    Module.Finite R (H1 M H A) := by
  revert M H R A
  exact @_root_.P2MW.S_CohCarrier_H1_moduleFinite.solution
