/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton (git blob ad64c366fb9bad2d709ac6cef302bee75d0908d2, sha256 ed5eab67990f9a381ae45d355bd711e6b71915d7fdbca1ce584eba5621d27ee6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_M4aHerbrand_IdeleClassVocab
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField

theorem NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton
    (F : Type) [Field F] [NumberField F] :
    ∃ V : Set (AdeleRing (𝓞 F) F)ˣ, IsOpen V ∧
      V ∩ (M4aHerbrand.principalIdeles (𝓞 F) F : Set (AdeleRing (𝓞 F) F)ˣ) = {1} := by
  revert F
  exact @_root_.P2MW.S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton.solution
