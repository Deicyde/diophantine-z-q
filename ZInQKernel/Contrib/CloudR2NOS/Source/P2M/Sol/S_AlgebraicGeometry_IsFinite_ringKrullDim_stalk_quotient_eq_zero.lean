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
  Source file    : P2M/Sol/S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero.lean
  Source sha256  : ef9c73d4e2105fbdb7691e2f62252cea12d4fdbde6eb54afb063c6538b6fd6c1
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: R2×1; rule citations in the batch ledger.
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

namespace P2MW.S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
r2nos_open_dual "CategoryTheory AlgebraicGeometry IsLocalRing"

namespace FD0625672e
r2nos_namespace_dual

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"

theorem ringKrullDim_quotient_map_maximalIdeal_eq_zero
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Algebra.QuasiFinite R S] :
    ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) = 0 := by

  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars R)

  haveI : IsArtinianRing ((maximalIdeal R).Fiber S) := inferInstance
  haveI hA : IsArtinianRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) := e.surjective.isArtinianRing
  haveI : Ring.KrullDimLE 0 (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp hA).2

  haveI : Nontrivial (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
    rw [Ideal.Quotient.nontrivial_iff]
    exact ((((local_hom_TFAE (algebraMap R S)).out 1 3 rfl rfl).mp inferInstance).trans_lt
      (inferInstance : (maximalIdeal S).IsMaximal).ne_top.lt_top).ne
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

end FD0625672e

theorem solution
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g] [IsLocallyNoetherian Y] (x : X) :
    ringKrullDim ((X.presheaf.stalk x) ⧸
      (maximalIdeal (Y.presheaf.stalk (g.base x))).map (g.stalkMap x).hom) = 0 := by
  letI : Algebra (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) := (g.stalkMap x).hom.toAlgebra
  haveI : Algebra.QuasiFinite (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x) := g.quasiFiniteAt x
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap x).hom)
  exact FD0625672e.ringKrullDim_quotient_map_maximalIdeal_eq_zero (Y.presheaf.stalk (g.base x)) (X.presheaf.stalk x)

#print axioms solution
end S_AlgebraicGeometry_IsFinite_ringKrullDim_stalk_quotient_eq_zero
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
