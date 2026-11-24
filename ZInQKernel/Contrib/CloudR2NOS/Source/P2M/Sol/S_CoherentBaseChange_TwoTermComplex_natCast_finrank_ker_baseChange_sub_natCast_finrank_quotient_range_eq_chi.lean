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
  Source file    : P2M/Sol/S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi.lean
  Source sha256  : 5d6c65bcd6594a17522527c393dd5d0a54afec447200436a784bd48528dfa1db
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi
r2nos_namespace_dual

set_option autoImplicit false

universe u v w

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"
w03_open "CoherentBaseChange P2MW.S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi.CoherentBaseChange"

namespace CoherentBaseChange
r2nos_namespace_dual
w03_export "CoherentBaseChange" "TwoTermComplex"
namespace TwoTermComplex
r2nos_namespace_dual
w03_export "CoherentBaseChange.TwoTermComplex" "chi C0 d C1"
namespace ChiFieldAux
r2nos_namespace_dual
w03_open "CoherentBaseChange.TwoTermComplex CoherentBaseChange"

variable {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
  (K : Type w) [Field K] [Algebra R K]

noncomputable def rk : ℕ := Module.finrank K (LinearMap.range (G.d.baseChange K))

theorem h0_add_rk :
    Module.finrank K (LinearMap.ker (G.d.baseChange K)) + rk G K =
      Module.finrank K (K ⊗[R] G.C0) := by
  have h := LinearMap.finrank_range_add_finrank_ker (G.d.baseChange K)
  unfold rk; omega

theorem rk_add_h1 :
    rk G K + Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) =
      Module.finrank K (K ⊗[R] G.C1) := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (G.d.baseChange K))
  unfold rk; omega

theorem main :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  have h0 := h0_add_rk G K
  have h1 := rk_add_h1 G K
  rw [Module.finrank_baseChange] at h0 h1
  show _ = (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ)
  have h0' : (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) + (rk G K : ℤ) =
      (Module.finrank R G.C0 : ℤ) := by exact_mod_cast h0
  have h1' : (rk G K : ℤ) + (Module.finrank K ((K ⊗[R] G.C1) ⧸
      LinearMap.range (G.d.baseChange K)) : ℤ) = (Module.finrank R G.C1 : ℤ) := by exact_mod_cast h1
  omega

end CoherentBaseChange.TwoTermComplex.ChiFieldAux

theorem solution
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
    (K : Type w) [Field K] [Algebra R K] :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by
  exact CoherentBaseChange.TwoTermComplex.ChiFieldAux.main G K
end S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
