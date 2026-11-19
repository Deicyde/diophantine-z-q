/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero.lean
  Source sha256  : f03220db2c4492966a1f3b69552e910bfb26e28540751ef79135eed1d0bfb46b
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero
r2nos_namespace_dual

open Bialgebra
r2nos_open_dual "Bialgebra"

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
end S_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
