/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_LevelN_isDomain_ring (git blob 88e3dcab4a6c547f24e68e0b36fe5d2c98b20c30, sha256 12530fde2ab85da74f75f47268cacc1a8562be1afbc29a1e47439ad91e30f58a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LevelNFunctionField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_WLight_levelN_structure_package

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_LevelN_isDomain_ring

set_option autoImplicit false

open scoped MatrixGroups

theorem solution (M : ℕ) [NeZero M] : IsDomain (ModularCurve.LevelN.ring M) := by

  have hpkg := WLight.levelN_structure_package M PeriodPair.ofTau
    (fun τ => ⟨PeriodPair.ofTau_ω₁ τ, PeriodPair.ofTau_ω₂ τ⟩)
    (ModularCurve.LevelN.wp M) (fun v τ => rfl)
    (ModularCurve.LevelN.fricke M) (fun v τ => rfl)
    ModularCurve.LevelN.jAnalytic (fun τ => rfl)
  obtain ⟨-, -, -, -, -, hdom⟩ := hpkg

  haveI : NoZeroDivisors (ModularCurve.LevelN.ring M) := ⟨fun {a b} h => by
    have h' := hdom (a : UpperHalfPlane → ℂ) (b : UpperHalfPlane → ℂ) a.2 b.2
      (by simpa using congrArg Subtype.val h)
    rcases h' with ha | hb
    · left; exact Subtype.ext ha
    · right; exact Subtype.ext hb⟩
  haveI : Nontrivial (ModularCurve.LevelN.ring M) := inferInstance
  exact NoZeroDivisors.to_isDomain _
