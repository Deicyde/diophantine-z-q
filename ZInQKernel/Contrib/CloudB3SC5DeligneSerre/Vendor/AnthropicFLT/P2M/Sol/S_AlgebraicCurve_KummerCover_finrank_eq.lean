/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_KummerCover_finrank_eq (git blob 3dbd070201e94a908ff61727cc18928c6ce13f60, sha256 fa5d529406c14d6389272ab2b8f898e7b309a3cac99657e430c4c1c776f875a5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.KummerExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_KummerCover_finrank_eq
set_option Elab.async false

open Polynomial IntermediateField
namespace AlgebraicCurve
namespace KummerCover
section Pure
variable {F L : Type*} [Field F] [Field L] [Algebra F L]
variable {p : ℕ} [hp : Fact p.Prime] {f : F} {α : L}
private theorem irreducible_X_pow_sub_C (hf : ∀ g : F, g ^ p ≠ f) : Irreducible (X ^ p - C f) :=
  X_pow_sub_C_irreducible_of_prime hp.out hf
end Pure
end AlgebraicCurve.KummerCover

open Polynomial AlgebraicCurve.KummerCover in
theorem solution {F L : Type*} [Field F] [Field L] [Algebra F L] {p : ℕ} [hp : Fact p.Prime] {f : F}
    [IsSplittingField F L (X ^ p - C f)] (hζ : (primitiveRoots p F).Nonempty) (hf : ∀ g : F, g ^ p ≠ f) :
    Module.finrank F L = p :=
  finrank_of_isSplittingField_X_pow_sub_C hζ (irreducible_X_pow_sub_C hf) L

#print axioms solution
