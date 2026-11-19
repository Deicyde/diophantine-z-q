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
  Source file    : Definitions/Def_ModularCurve_FibrePoly.lean
  Source sha256  : 64086a5caad18a071c82d69cd0fea10313079a6a82a4af62b7fa91a49726af3b
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 1 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_ModularCurve_KroneckerTransport
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

noncomputable section

open Polynomial
r2nos_open_dual "Polynomial"

namespace ModularCurve
r2nos_namespace_dual

section FibrePoly

variable {k : Type*} [Field k]

def fibrePoly (Φ : Polynomial (Polynomial ℤ)) (a : k) : Polynomial k :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom k) a)

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]

theorem eval₂RingHom_intCast_eq_comp (a : k) :
    Polynomial.eval₂RingHom (Int.castRingHom k) a =
      (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl ℓ) k) a).comp
        (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply,
    Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

theorem fibrePoly_eq_map_reduceModBivar (Φ : Polynomial (Polynomial ℤ)) (a : k) :
    fibrePoly Φ a =
      (reduceModBivar ℓ Φ).map
        (Polynomial.eval₂RingHom (ZMod.castHom (dvd_refl ℓ) k) a) := by
  rw [fibrePoly, eval₂RingHom_intCast_eq_comp (ℓ := ℓ),
    show reduceModBivar ℓ Φ
      = Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) from rfl,
    Polynomial.map_map]

end FibrePoly

section Factorization

variable {k : Type*} [Field k] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ]

theorem C_sub_X_pow_eq_neg_pow (a : k) :
    Polynomial.C a - Polynomial.X ^ ℓ =
      -((Polynomial.X - Polynomial.C ((frobeniusEquiv k ℓ).symm a)) ^ ℓ) := by
  have hpoly : (Polynomial.X - Polynomial.C ((frobeniusEquiv k ℓ).symm a)) ^ ℓ =
      Polynomial.X ^ ℓ - Polynomial.C ((frobeniusEquiv k ℓ).symm a) ^ ℓ :=
    sub_pow_expChar _ _
  rw [hpoly, ← Polynomial.C_pow, frobeniusEquiv_symm_pow_p, neg_sub]

end Factorization

end ModularCurve
end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
