/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 closed-section GM11 sub-gap (G5) `PresentationOfFramesNear`, PROVED (shared with C2 Step 2).
NEW EDITION (lane4 a940f2af, 2026-11-17; G5 fix, lead 2026-11-17T06:11Z). SOURCE ONLY, UNCOMPILED.

The FLT construction (charts from frame coefficients, glued along the frame loci) now comes from the
route-(E) NEW edition `ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top`
and its Sol module (documented lane4 port transform with the published W03 / lane4 dual shims;
upstream FLT@6e837e75, Apache-2.0, attribution in those files). This file keeps the two public names
(`ProjOfFrames.AlgebraicGeometry.exists_projPresentation_of_iSup_eq_top` as an `alias`, and
`ProjOfFrames.presentationOfFramesNear`) for every consumer (Step3AssemblyProved, NativePowFBS, C2).
SUPERSEDES the adapted-body editions ee644b60… / 83a207f8… (latent `p2m_open → open` name-resolution
defect under the nested `AlgebraicGeometry` namespace); those stay frozen as history.
Options: autoImplicit false only.
-/
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step3Gaps
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.ProjOfFrames

/-- The FLT presentation-from-frames theorem (lane4 port constant), under the batch-4 name. -/
alias AlgebraicGeometry.exists_projPresentation_of_iSup_eq_top :=
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top

open ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.AlgebraicGeometry.Scheme.Modules in
/-- **(G5) proved.** The frame loci `LinSys.IsFrameOn.maxOpen` (port Sol internals) of the given
sections cover `X` by hypothesis, and on each of them the section frames. -/
theorem presentationOfFramesNear : PresentationOfFramesNear.{u} := by
  intro R _ X f M N σ hgen
  let U : Fin (N + 1) → X.Opens := fun j => LinSys.IsFrameOn.maxOpen M (σ j)
  have hU : iSup U = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨j, W, hxW, hW⟩ := hgen x
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨j, LinSys.IsFrameOn.le_maxOpen (M := M) (s := σ j) (V := W) hW hxW⟩
  obtain ⟨𝔓, h𝔓, -⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top
      f M N σ U hU (fun i V hV => LinSys.IsFrameOn.maxOpen_isFrameOn (M := M) (σ i) V hV)
  exact ⟨𝔓, h𝔓⟩

end ZInQ.Contrib.CloudR2NOS.ClosedSection.ProjOfFrames
