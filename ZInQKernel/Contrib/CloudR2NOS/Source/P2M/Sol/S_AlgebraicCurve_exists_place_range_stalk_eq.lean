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
  Source file    : P2M/Sol/S_AlgebraicCurve_exists_place_range_stalk_eq.lean
  Source sha256  : d815d272a7bb9d7b9974f15e0c4bb6bf37373ba67492cb992b6f46b8e1d9effd
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 1600000`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_exists_place_range_stalk_eq
r2nos_namespace_dual

set_option autoImplicit false

w03_open "CategoryTheory AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_exists_place_range_stalk_eq.AlgebraicCurve"

universe u

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "Place baseToFunctionField"
end AlgebraicCurve
r2nos_open_scoped "AlgebraicCurve" in

theorem AlgebraicCurve.baseToFunctionField_apply_eq_algebraMap_stalk
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C]
    (x : C) (a : K) :
    baseToFunctionField c a =
      algebraMap (C.presheaf.stalk x) C.functionField
        ((C.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))) := by
  have key : ∀ s : Γ(C, ⊤), (C.presheaf.germ ⊤ (genericPoint C) trivial).hom s =
      algebraMap (C.presheaf.stalk x) C.functionField ((C.presheaf.germ ⊤ x trivial).hom s) := by
    intro s
    simp_rw [RingHom.algebraMap_toAlgebra]
    change _ = (C.presheaf.germ ⊤ x trivial ≫ C.presheaf.stalkSpecializes _).hom s
    rw [C.presheaf.germ_stalkSpecializes]
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  exact key _

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c]
    (x : C) (hx : IsClosed ({x} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∃ v : AlgebraicCurve.Place K C.functionField,
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring := by
  letI := (baseToFunctionField c).toAlgebra
  haveI hdvr : IsDiscreteValuationRing (C.presheaf.stalk x) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed c x hx
  set O := C.presheaf.stalk x with hO
  set F := C.functionField with hF

  let A : ValuationSubring F := (ValuationRing.valuation O F).valuationSubring
  have hA : (algebraMap O F).range = A.toSubring := by
    ext f
    change f ∈ (algebraMap O F).range ↔ f ∈ (ValuationRing.valuation O F).integer
    rw [ValuationRing.range_algebraMap_eq]
  have hmemA : ∀ f : F, f ∈ A ↔ ∃ a : O, algebraMap O F a = f := fun f =>
    ValuationRing.mem_integer_iff O F f

  have hinj : Function.Injective (algebraMap O F) := IsFractionRing.injective O F
  let e : O ≃+* A :=
    RingEquiv.ofBijective
      ((algebraMap O F).codRestrict A.toSubring fun a => by
        rw [← hA]; exact ⟨a, rfl⟩)
      ⟨fun a b hab => hinj (congrArg Subtype.val hab),
        fun ⟨f, hf⟩ => by
          obtain ⟨a, rfl⟩ := (hmemA f).mp hf
          exact ⟨a, rfl⟩⟩
  refine ⟨⟨A, ?_, ?_, ?_⟩, hA⟩
  ·
    intro a
    rw [hmemA]
    exact ⟨_, (baseToFunctionField_apply_eq_algebraMap_stalk c x a).symm⟩
  ·
    intro htop
    apply IsDiscreteValuationRing.not_isField O
    have hsurj : Function.Surjective (algebraMap O F) := by
      intro f
      have hf : f ∈ A := by rw [htop]; trivial
      exact (hmemA f).mp hf
    exact (RingEquiv.ofBijective (algebraMap O F) ⟨hinj, hsurj⟩).toMulEquiv.isField
      (Field.toIsField F)
  ·
    exact IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
end S_AlgebraicCurve_exists_place_range_stalk_eq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
