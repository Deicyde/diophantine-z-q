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
  Source file    : P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat.lean
  Source sha256  : 1abd82cb35e4a54dd8df2310c9cd8f8b1fcffff29dfe0a112eab6459b905aa98
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
r2nos_namespace_dual

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

universe u

namespace P2mKerRank
r2nos_namespace_dual

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem endDegree_eq_finrank_unit (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] :
    L.endDegree β =
      β.1.finrank ((L.one (𝟙 (Spec (CommRingCat.of K)))).1 (IsLocalRing.closedPoint K)) := by
  haveI : IsFinite (L.endKerStr β) := inferInstance
  rw [RelativeGroupLaw.endDegree_of_isFinite]
  exact Scheme.Hom.finrank_pullback_snd β.1 _ _

theorem finrank_eq_finrank [LocallyOfFiniteType f] (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1]
    [PreconnectedSpace A] (x y : A) : β.1.finrank x = β.1.finrank y := by
  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : LocallyOfFinitePresentation β.1 := inferInstance
  have h := Scheme.Hom.isLocallyConstant_finrank β.1
  exact h.apply_eq_of_preconnectedSpace x y

theorem endDegree_eq_finrank [LocallyOfFiniteType f] (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] [PreconnectedSpace A] (x : A) : L.endDegree β = β.1.finrank x := by
  rw [endDegree_eq_finrank_unit L β]
  exact finrank_eq_finrank β _ x

theorem one_le_finrank [LocallyOfFiniteType f] (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1]
    [PreconnectedSpace A] (x : A) : 1 ≤ β.1.finrank x := by
  rw [finrank_eq_finrank β x (β.1 x)]
  exact Scheme.Hom.one_le_finrank_map β.1 x

theorem surjective [LocallyOfFiniteType f] (β : SchemeHomOver f f) [IsFinite β.1] [Flat β.1]
    [PreconnectedSpace A] : Function.Surjective β.1 := by
  have h : Surjective β.1 := (Scheme.Hom.one_le_finrank_iff_surjective β.1).mp fun x =>
    one_le_finrank β x
  exact h.surj

theorem main [LocallyOfFiniteType f] (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] [PreconnectedSpace A] :
    Function.Surjective β.1 ∧ 0 < L.endDegree β ∧ ∀ x : A, L.endDegree β = β.1.finrank x := by
  refine ⟨surjective β, ?_, endDegree_eq_finrank L β⟩
  rw [endDegree_eq_finrank_unit L β]
  exact one_le_finrank β _

end P2mKerRank

theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [PreconnectedSpace A] (L : RelativeGroupLaw K f) (β : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] :
    Function.Surjective β.1 ∧ 0 < L.endDegree β ∧
      ∀ x : A, L.endDegree β = Scheme.Hom.finrank β.1 x :=
  P2mKerRank.main L β

end
end S_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
