/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_HopfKer
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v w

theorem HopfAlgebra.exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective
    {R : Type u} [inst_t1 : CommRing R]
    {A : Type v} [inst_t2 : CommRing A] [inst_t3 : HopfAlgebra R A] [inst_t4 : Module.Finite R A] [inst_t5 : Module.Free R A]
    {B : Type w} [inst_t6 : CommRing B] [inst_t7 : HopfAlgebra R B] [inst_t8 : Module.Finite R B] [inst_t9 : Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    (∃ r : A →ₗ[↥(HopfAlgebra.hopfKer π)] ↥(HopfAlgebra.hopfKer π),
        ∀ c : ↥(HopfAlgebra.hopfKer π), r (c : A) = c) ∧
      Module.Finite R ↥(HopfAlgebra.hopfKer π) ∧ Module.Projective R ↥(HopfAlgebra.hopfKer π) ∧
      ∀ 𝔭 : PrimeSpectrum R,
        Module.rankAtStalk (R := R) ↥(HopfAlgebra.hopfKer π) 𝔭 * Module.finrank R B =
          Module.finrank R A :=
  @_root_.P2MW.S_HopfAlgebra_exists_retraction_hopfKer_and_rankAtStalk_mul_finrank_of_surjective.solution R inst_t1 A inst_t2 inst_t3 inst_t4 inst_t5 B inst_t6 inst_t7 inst_t8 inst_t9 π hπ
