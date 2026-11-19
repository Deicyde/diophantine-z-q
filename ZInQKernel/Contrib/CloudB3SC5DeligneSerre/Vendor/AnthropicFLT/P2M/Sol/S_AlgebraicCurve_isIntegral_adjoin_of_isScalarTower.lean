/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_isIntegral_adjoin_of_isScalarTower (git blob fd50871d2b61d49edf7ac2a4b0777dc3f97051fe, sha256 bb05b035e9da2512896e30d7096330c09c3ddfbafb97973548b3b7349d5ff2f7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_isIntegral_adjoin_of_isScalarTower

set_option autoImplicit false

theorem solution {K L F : Type*} [CommRing K] [CommRing L] [CommRing F] [Algebra K L] [Algebra K F] [Algebra L F] [IsScalarTower K L F] {j x : F} (hx : IsIntegral (Algebra.adjoin K {j}) x) : IsIntegral (Algebra.adjoin L {j}) x := by
  have hsub : Algebra.adjoin K {j} ≤ Subalgebra.restrictScalars K (Algebra.adjoin L {j}) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      ((Subalgebra.mem_restrictScalars K).mpr (Algebra.subset_adjoin rfl)))
  let φ' : ↥(Algebra.adjoin K {j}) →+* ↥(Algebra.adjoin L {j}) :=
    { toFun := fun a => ⟨(a : F), (Subalgebra.mem_restrictScalars K).mp (hsub a.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact IsIntegral.map_of_comp_eq φ' (RingHom.id F) (by ext a; rfl) hx
