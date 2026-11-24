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
  Source file    : P2M/Sol/S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral.lean
  Source sha256  : 11174e4a91c82de9f1e6785c67b8547fd141c5ea4b728247e5aff19979c88ce6
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral
r2nos_namespace_dual

set_option autoImplicit false

universe u

namespace HeightAux
r2nos_namespace_dual

theorem eq_of_le_of_under_eq {P B : Type*} [CommRing P] [CommRing B] [Algebra P B]
    [Algebra.IsIntegral P B] {Q q : Ideal B} [Q.IsPrime] [q.IsPrime] (hle : Q ≤ q)
    (hu : q.under P ≤ Q.under P) : Q = q := by
  by_contra hne
  have hlt : Q < q := lt_of_le_of_ne hle hne
  obtain ⟨x, hxq, hxQ⟩ := Set.exists_of_ssubset hlt
  have := Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxq, hxQ⟩
    (Algebra.IsIntegral.isIntegral (R := P) x)
  exact absurd (lt_of_lt_of_le this hu) (lt_irrefl _)

theorem height_eq_height_under (P B : Type*) [CommRing P] [IsDomain P] [IsNoetherianRing P]
    [IsIntegrallyClosed P] [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B]
    [FaithfulSMul P B] [Algebra.IsIntegral P B] (q : Ideal B) [q.IsPrime] :
    q.height = (q.under P).height := by
  set p := q.under P with hp
  set I := Ideal.map (algebraMap P B) p with hI
  have hIq : I ≤ q := Ideal.map_comap_le
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ q := by rw [Ideal.mk_ker]; exact hIq
  haveI hQbar : (Ideal.map (Ideal.Quotient.mk I) q).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q
  suffices h0 : (Ideal.map (Ideal.Quotient.mk I) q).height = 0 by
    rw [key, ← hI, h0, add_zero]
  refine nonpos_iff_eq_zero.mp ?_
  rw [← ENat.coe_zero, Ideal.height_le_iff]
  intro Q' hQ' hQ'lt
  exfalso

  set Q := Ideal.comap (Ideal.Quotient.mk I) Q' with hQ
  have hIQ : I ≤ Q := (Ideal.mk_ker (I := I)).symm.trans_le (Ideal.ker_le_comap _)
  have hQq : Q ≤ q := by
    refine (Ideal.comap_mono hQ'lt.le).trans ?_
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    refine sup_le le_rfl ?_
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]; exact hIq
  have hunder : q.under P ≤ Q.under P := by
    change p ≤ Ideal.comap (algebraMap P B) Q
    exact Ideal.le_comap_of_map_le hIQ
  have hQeq : Q = q := eq_of_le_of_under_eq hQq hunder
  have hQ'eq : Ideal.map (Ideal.Quotient.mk I) Q = Q' :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  rw [hQeq] at hQ'eq
  exact absurd (hQ'eq ▸ hQ'lt) (lt_irrefl _)

end HeightAux
theorem solution
    (P B : Type u) [CommRing P] [IsDomain P] [IsNoetherianRing P] [IsIntegrallyClosed P]
    [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B] [FaithfulSMul P B]
    [Algebra.IsIntegral P B] (q : Ideal B) [q.IsPrime] :
    q.height = (q.under P).height :=
  HeightAux.height_eq_height_under P B q
end S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
