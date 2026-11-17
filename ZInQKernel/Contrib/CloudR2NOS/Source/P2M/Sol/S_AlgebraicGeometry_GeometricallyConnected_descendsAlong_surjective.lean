/-
NEW EDITION (H5 lane C4, 2026-11-17, Parent route (E)). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.lean
  Source sha256  : 1b69f535fffa6d45214648e7e9147537c267224ec61f796bf8204728ddc352ba
  Retrieved      : pinned read-only clone the upstream FLT repository (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
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

namespace P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.AlgebraicGeometry"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Surjective Spec Scheme GeometricallyConnected geometrically"
namespace GeometricallyConnectedDescentAux
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

theorem geometricallyConnected_of_pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (σ : S' ⟶ S) [Surjective σ]
    [hgc : GeometricallyConnected (pullback.snd f σ)] : GeometricallyConnected f := by
  refine ⟨fun K _ k Z a b hZ => ?_⟩

  obtain ⟨z, -⟩ := (pullback.fst k σ).surjective default
  let ι := (pullback k σ).fromSpecResidueField z
  let kL : Spec ((pullback k σ).residueField z) ⟶ Spec (.of K) := ι ≫ pullback.fst k σ
  let l' : Spec ((pullback k σ).residueField z) ⟶ S' := ι ≫ pullback.snd k σ
  have hkl : kL ≫ k = l' ≫ σ := by simp only [kL, l', Category.assoc, pullback.condition]
  haveI : Surjective kL := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩

  have s : IsPullback (pullback.fst b kL ≫ a) (pullback.snd b kL) f (l' ≫ σ) := by
    rw [← hkl]
    exact (IsPullback.of_hasPullback b kL).paste_horiz hZ
  let m : pullback b kL ⟶ pullback f σ :=
    pullback.lift (pullback.fst b kL ≫ a) (pullback.snd b kL ≫ l') (by simpa only [Category.assoc] using s.w)
  have hm₁ : m ≫ pullback.fst f σ = pullback.fst b kL ≫ a := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f σ = pullback.snd b kL ≫ l' := pullback.lift_snd _ _ _
  have s' : IsPullback (m ≫ pullback.fst f σ) (pullback.snd b kL) f (l' ≫ σ) := by rw [hm₁]; exact s
  have sq : IsPullback m (pullback.snd b kL) (pullback.snd f σ) l' :=
    IsPullback.of_right s' hm₂ (IsPullback.of_hasPullback f σ)
  have hc : ConnectedSpace ↥(pullback b kL) := hgc.geometrically_connectedSpace l' m (pullback.snd b kL) sq

  exact (pullback.fst b kL).surjective.connectedSpace (pullback.fst b kL).continuous

end AlgebraicGeometry.GeometricallyConnectedDescentAux

theorem solution :
    DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective := by
  refine DescendsAlong.mk' fun {X Y Z} {f} {g} _ hf hfst => ?_
  haveI : Surjective f := hf
  haveI : GeometricallyConnected (pullback.fst f g) := hfst
  haveI : GeometricallyConnected (pullback.snd g f) := by
    rw [← pullbackSymmetry_hom_comp_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _).mpr hfst
  exact AlgebraicGeometry.GeometricallyConnectedDescentAux.geometricallyConnected_of_pullback_snd g f
end S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
