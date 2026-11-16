/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Theorems.Thm_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero

open Bialgebra

theorem solution
    (K : Type*) [Field K] [CharZero K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] [Algebra.FiniteType K A]
    (χ : A →ₐ[K] K) :
    haveI : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime χ.toRingHom
    IsDomain (Localization.AtPrime (RingHom.ker χ.toRingHom)) := by
  haveI hMp : (RingHom.ker χ.toRingHom).IsPrime := RingHom.ker_isPrime χ.toRingHom
  haveI hIp : (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).IsPrime :=
    RingHom.ker_isPrime (Bialgebra.counitAlgHom K A).toRingHom
  set I := RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom with hI
  set M := RingHom.ker χ.toRingHom with hM

  obtain ⟨e, hcomap⟩ :=
    HopfAlgebra.exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom K A χ
  rw [← hI, ← hM] at hcomap

  have hmap : M.primeCompl.map e.toRingEquiv.toMonoidHom = I.primeCompl := by
    have happ : ∀ b : A, e.toRingEquiv.toMonoidHom b = e.toRingEquiv.toRingHom b :=
      fun _ => rfl
    ext a
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_compl_iff, SetLike.mem_coe, ← hcomap, Ideal.mem_comap]
    constructor
    · rintro ⟨b, hb, rfl⟩
      rwa [happ]
    · intro ha
      refine ⟨e.symm a, ?_, e.toRingEquiv.apply_symm_apply a⟩
      rw [show e.toRingEquiv.toRingHom (e.symm a) = a from e.toRingEquiv.apply_symm_apply a]
      exact ha

  let E : Localization.AtPrime M ≃+* Localization.AtPrime I :=
    IsLocalization.ringEquivOfRingEquiv (M := M.primeCompl) (T := I.primeCompl)
      (Localization.AtPrime M) (Localization.AtPrime I) e.toRingEquiv hmap

  haveI : IsDomain (Localization.AtPrime I) :=
    HopfAlgebra.isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero K A
  exact E.injective.isDomain _
