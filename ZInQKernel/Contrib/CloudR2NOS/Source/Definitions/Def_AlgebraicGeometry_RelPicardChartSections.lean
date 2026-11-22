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
  Source file    : Definitions/Def_AlgebraicGeometry_RelPicardChartSections.lean
  Source sha256  : 500f689a8662eedea7144c960a88417291431537c7ac21b7841ed5340174e488
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
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

namespace AlgebraicGeometry.RelPicard
r2nos_namespace_dual

open CategoryTheory CategoryTheory.Limits NeronModelInfra AlgebraicCurve
r2nos_open_dual "CategoryTheory CategoryTheory.Limits NeronModelInfra AlgebraicCurve"

universe u

noncomputable def sectionFibrePoint {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {k : Type u} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    {p : Spec (CommRingCat.of k) ⟶ pullback c s // p ≫ pullback.snd c s = 𝟙 _} :=
  ⟨pullback.lift (s ≫ γ.1) (𝟙 _) (by rw [Category.assoc, γ.2, Category.comp_id, Category.id_comp]),
    pullback.lift_snd _ _ _⟩

def ChartSectionsAt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {n g r : ℕ} (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    {L : Type u} [Field L] [Algebra k L] (M : CurveModel k L)
    (e : M.C ≅ pullback c s) (he : e.hom ≫ pullback.snd c s = M.toBase) : Prop :=
  (∃ Kc : Divisor k L, ∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) ∧
  ∀ D : Divisor k L, (∀ v, 0 ≤ D v) → Divisor.degree D = r →
    ∃ i : Fin n, ell (D - ∑ j : Fin (r - g),
      Finsupp.single (M.pointEquivPlace
        ⟨(sectionFibrePoint (γ i j) s).1 ≫ e.inv, by
          rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (sectionFibrePoint (γ i j) s).2⟩) 1) = 1

def HasChartSections {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {n g r : ℕ} (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (M : CurveModel k L)
      (e : M.C ≅ pullback c s) (he : e.hom ≫ pullback.snd c s = M.toBase), ChartSectionsAt γ s M e he

def HasChartSectionsOverClosedPoints {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {n g r : ℕ} (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
    IsClosed ({s.base (IsLocalRing.closedPoint k)} : Set (Spec (CommRingCat.of R))) →
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (M : CurveModel k L)
      (e : M.C ≅ pullback c s) (he : e.hom ≫ pullback.snd c s = M.toBase), ChartSectionsAt γ s M e he

end AlgebraicGeometry.RelPicard

end ZInQ.Contrib.CloudW03NeronSurj.FLT
