/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero

set_option maxHeartbeats 6400000
noncomputable section

theorem solution
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A] :
    IsReduced A := by

  refine isReduced_ofLocalizationMaximal A ?_
  intro J hJ

  obtain ⟨χ, hχ⟩ : ∃ χ : A →ₐ[K] K, J = RingHom.ker χ.toRingHom := by
    haveI := hJ
    letI : Field (A ⧸ J) := Ideal.Quotient.field J
    haveI : Algebra.FiniteType K (A ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J) Ideal.Quotient.mk_surjective

    haveI : Module.Finite K (A ⧸ J) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ J)

    have hbij : Function.Bijective (algebraMap K (A ⧸ J)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e : K ≃ₐ[K] (A ⧸ J) := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ J)) hbij

    refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K J), ?_⟩
    ext a
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply]
    rw [show ∀ x, e.symm.toAlgHom x = e.symm x from fun _ => rfl,
      map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
  subst hχ

  haveI : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime χ.toRingHom
  haveI : IsDomain (Localization.AtPrime (RingHom.ker χ.toRingHom)) :=
    HopfAlgebra.isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero K A χ
  infer_instance

end
