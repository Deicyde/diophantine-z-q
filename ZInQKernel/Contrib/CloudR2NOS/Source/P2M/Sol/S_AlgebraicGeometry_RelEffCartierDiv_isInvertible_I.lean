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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I.lean
  Source sha256  : 9741ab23eef2628f2aec1608f7dae6d5baac576875295fd3e7ef53ca66aa74d1
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_ker_graphOver_mul
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Surjective Scheme.Hom.le_ker_comp SmoothOfRelativeDimension Scheme.Hom IsFinite Scheme Smooth Scheme.ker_eq_top_of_isEmpty Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Scheme.IdealSheafData.ker_subschemeι Scheme.Hom.one_le_finrank_map Flat IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Hom.ker Scheme.Hom.one_le_finrank_iff_surjective Scheme.IdealSheafData graphOver graphOver_fst graphOver_snd graphOver_snd_assoc RelEffCartierDiv mapOnProdOver mapOnProdOver_fst mapOnProdOver_snd isPullback_mapOnProdOver Scheme.IdealSheafData.isInvertible_top Scheme.Hom.isInvertible_ker_of_comp_eq_id RelEffCartierDiv.exists_I_eq_ker_graphOver_mul Scheme.IdealSheafData.isInvertible_of_isInvertible_comap"
namespace RelEffCartierDiv
r2nos_namespace_dual
w03_export "AlgebraicGeometry.RelEffCartierDiv" "pullbackAlong I flat isFinite finrank_eq locallyOfFinitePresentation exists_I_eq_ker_graphOver_mul"
namespace CartierInduction
r2nos_namespace_dual
w03_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]

theorem I_eq_top_of_degree_zero {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f 0 g) :
    D.I = ⊤ := by
  have := D.isFinite
  have := D.flat
  have hempty : IsEmpty ↥D.I.subscheme := by
    by_contra h
    rw [not_isEmpty_iff] at h
    obtain ⟨x⟩ := h
    have h1 := Scheme.Hom.one_le_finrank_map (D.I.subschemeι ≫ pullback.snd f g) x
    rw [D.finrank_eq] at h1
    exact Nat.not_succ_le_zero 0 h1
  rw [← D.I.ker_subschemeι]
  exact Scheme.ker_eq_top_of_isEmpty _

theorem step (r : ℕ)
    (ih : ∀ {T : Scheme.{u}} {g : T ⟶ S} (E : RelEffCartierDiv f r g), E.I.IsInvertible)
    {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f (r + 1) g) : D.I.IsInvertible := by
  have := D.isFinite
  have := D.flat
  have := D.locallyOfFinitePresentation

  let π : D.I.subscheme ⟶ T := D.I.subschemeι ≫ pullback.snd f g
  haveI : Surjective π := by
    refine (Scheme.Hom.one_le_finrank_iff_surjective π).mp fun t => ?_
    show 1 ≤ (D.I.subschemeι ≫ pullback.snd f g).finrank t
    rw [D.finrank_eq t]
    exact Nat.succ_le_succ (Nat.zero_le r)
  let g' : D.I.subscheme ⟶ S := π ≫ g
  have hπ : π ≫ g = g' := rfl
  let D' : RelEffCartierDiv f (r + 1) g' := D.pullbackAlong π hπ

  let a : D.I.subscheme ⟶ 𝒞 := D.I.subschemeι ≫ pullback.fst f g
  have ha : a ≫ f = g' := by
    simp only [a, g', π, Category.assoc, pullback.condition]
  have hgraph : graphOver f a ha ≫ mapOnProdOver f π hπ = D.I.subschemeι := by
    apply pullback.hom_ext
    · rw [Category.assoc, mapOnProdOver_fst, graphOver_fst]
    · rw [Category.assoc, mapOnProdOver_snd, graphOver_snd_assoc]
  have hle : D'.I ≤ (graphOver f a ha).ker := by
    change D.I.comap (mapOnProdOver f π hπ) ≤ _
    have hcomap : D.I.comap (mapOnProdOver f π hπ) =
        (pullback.fst (mapOnProdOver f π hπ) D.I.subschemeι).ker := by
      rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.IdealSheafData.ker_subschemeι]
    rw [hcomap]
    have hfac : pullback.lift (graphOver f a ha) (𝟙 _) (by rw [hgraph, Category.id_comp]) ≫
        pullback.fst (mapOnProdOver f π hπ) D.I.subschemeι = graphOver f a ha :=
      pullback.lift_fst _ _ _
    exact le_of_le_of_eq (Scheme.Hom.le_ker_comp _ _) (congrArg Scheme.Hom.ker hfac)

  obtain ⟨E, hE⟩ := RelEffCartierDiv.exists_I_eq_ker_graphOver_mul D' a ha hle

  have hgr : (graphOver f a ha).ker.IsInvertible := by
    haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
    haveI : SmoothOfRelativeDimension 1 (pullback.snd f g') :=
      MorphismProperty.pullback_snd _ _ inferInstance
    exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (graphOver f a ha) (graphOver_snd f a ha)
  have hD' : (D.I.comap (mapOnProdOver f π hπ)).IsInvertible := by
    change D'.I.IsInvertible
    rw [hE]
    exact hgr.mul (ih E)

  have hbc := (isPullback_mapOnProdOver f π hπ).flip
  haveI : IsFinite (mapOnProdOver f π hπ) := MorphismProperty.of_isPullback hbc inferInstance
  haveI : Flat (mapOnProdOver f π hπ) := MorphismProperty.of_isPullback hbc inferInstance
  haveI : Surjective (mapOnProdOver f π hπ) := MorphismProperty.of_isPullback hbc inferInstance
  exact Scheme.IdealSheafData.isInvertible_of_isInvertible_comap (mapOnProdOver f π hπ) D.I hD'

theorem isInvertible : ∀ (r : ℕ) {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g),
    D.I.IsInvertible
  | 0, _, _, D => by
    rw [I_eq_top_of_degree_zero D]
    exact Scheme.IdealSheafData.isInvertible_top
  | r + 1, _, _, D => step r (fun E => isInvertible r E) D

end AlgebraicGeometry.RelEffCartierDiv.CartierInduction

theorem solution {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (D : RelEffCartierDiv f r g) : D.I.IsInvertible :=
  AlgebraicGeometry.RelEffCartierDiv.CartierInduction.isInvertible r D
end S_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
