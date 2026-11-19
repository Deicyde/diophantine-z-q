/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin (git blob 3c43665d726d770850aadba7e4e804f2f6bef968, sha256 e0180c2f6bc8ea2992d421cb8856768aa7c6d3a37ec46b98a2e8d6e1dd872924).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Valuation.Integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_mem_toValuationSubring_of_isIntegral_adjoin

set_option autoImplicit false

open AlgebraicCurve

namespace ModularCurve

namespace QexpN

private def placeSubalgebra {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    Subalgebra K F :=
  { v.toValuationSubring.toSubring.toSubsemiring with algebraMap_mem' := v.algebraMap_mem' }

private theorem mem_placeSubalgebra {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {y : F} :
    y ∈ placeSubalgebra v ↔ y ∈ v.toValuationSubring := Iff.rfl

private theorem valuationSubring_integers {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) :
    (v.toValuationSubring.valuation).Integers v.toValuationSubring :=
  { hom_inj := Subtype.coe_injective
    map_le_one := fun a => v.toValuationSubring.valuation_le_one a
    exists_of_le_one := fun {r} hr =>
      ⟨⟨r, v.toValuationSubring.mem_of_valuation_le_one r hr⟩, rfl⟩ }

private theorem mem_of_isIntegral_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring)
    (hx : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring := by
  have hle : Algebra.adjoin K {j} ≤ placeSubalgebra v :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ((mem_placeSubalgebra v).mpr hj))
  let φ' : ↥(Algebra.adjoin K {j}) →+* ↥(v.toValuationSubring) :=
    { toFun := fun a => ⟨(a : F), (mem_placeSubalgebra v).mp (hle a.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hOx : IsIntegral (↥v.toValuationSubring) x :=
    IsIntegral.map_of_comp_eq φ' (RingHom.id F) (by ext a; rfl) hx
  exact v.toValuationSubring.mem_of_valuation_le_one x
    ((valuationSubring_integers v).isIntegral_iff_v_le_one.mp hOx)

end QexpN

end ModularCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {j x : F} (hj : j ∈ v.toValuationSubring) (hx : IsIntegral (Algebra.adjoin K {j}) x) : x ∈ v.toValuationSubring :=
  ModularCurve.QexpN.mem_of_isIntegral_adjoin v hj hx
