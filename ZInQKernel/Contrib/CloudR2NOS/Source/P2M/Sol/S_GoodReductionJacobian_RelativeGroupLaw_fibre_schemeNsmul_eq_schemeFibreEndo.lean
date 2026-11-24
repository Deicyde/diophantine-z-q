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
  Source file    : P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo.lean
  Source sha256  : b9a344059531e307ab0bb5398a3c57a4e8e83c1fb862507f4febbb6c544624c1
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
r2nos_namespace_dual

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo.GoodReductionJacobian"

universe u

namespace GoodReductionJacobian
r2nos_namespace_dual
w03_export "GoodReductionJacobian" "schemeHomOverComp RelativeGroupLaw RelativeGroupLaw.fibreStr RelativeGroupLaw.fibrePointToBase_coe RelativeGroupLaw.fibrePointOfBase_coe RelativeGroupLaw.idPoint"
namespace RelativeGroupLaw
r2nos_namespace_dual
w03_export "GoodReductionJacobian.RelativeGroupLaw" "baseResidueField fibreStr fibrePointToBase fibrePointOfBase fibrePointToBase_coe fibrePointOfBase_coe fibrePointToBase_ofBase fibre fibre_mul nsmul nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over"
w03_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem fibre_nsmul (G : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{u}))
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of (baseResidueField s))) (n : ℕ)
    (x : SchemeHomOver t' (fibreStr f s)) :
    (G.fibre s).nsmul t' n x = fibrePointOfBase s (G.nsmul _ n (fibrePointToBase s x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [nsmul_succ, ih, fibre_mul, fibrePointToBase_ofBase, nsmul_succ]

theorem nsmul_coe_eq_comp_schemeNsmul' (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hid : schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x := Subtype.ext (Category.comp_id x.1)
  have h : schemeHomOverComp x.1 x.2 (G.nsmul f n idPoint)
      = G.nsmul t n (schemeHomOverComp x.1 x.2 idPoint) :=
    G.nsmul_natural f t x.1 x.2 n idPoint
  rw [hid] at h
  exact (congrArg Subtype.val h).symm

end GoodReductionJacobian.RelativeGroupLaw

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (s : (Spec (CommRingCat.of R) : Scheme.{u})) (n : ℕ) :
    (G.fibre s).schemeNsmul n = schemeFibreEndo f (G.schemeNsmul n) (G.schemeNsmul_over n) s := by
  apply pullback.hom_ext
  · rw [schemeFibreEndo_fst]
    show ((G.fibre s).nsmul (RelativeGroupLaw.fibreStr f s) n RelativeGroupLaw.idPoint).1 ≫ _ = _
    rw [RelativeGroupLaw.fibre_nsmul, RelativeGroupLaw.fibrePointOfBase_coe, pullback.lift_fst,
      RelativeGroupLaw.nsmul_coe_eq_comp_schemeNsmul', RelativeGroupLaw.fibrePointToBase_coe]
    simp only [Category.id_comp]
  · rw [schemeFibreEndo_snd]
    exact (G.fibre s).schemeNsmul_over n
end S_GoodReductionJacobian_RelativeGroupLaw_fibre_schemeNsmul_eq_schemeFibreEndo
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
