/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed (git blob 1cecd4c222dc38a88d94816f1308070df751ef37, sha256 7c2d42ccaa02a91e880b1218d0e1928b92edb9ec71dc6bf81a582cf6f22b251d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (v : Place K F) (hv : v.deg ≠ 0) : v.deg = 1 := by
  haveI : Module.Finite K v.ResidueField := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hv)
  have e : K ≃ₗ[K] v.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap K v.ResidueField) (IsAlgClosed.algebraMap_bijective_of_isIntegral)
  unfold Place.deg
  rw [← e.finrank_eq, Module.finrank_self]
