/-
Copyright (c) 2026 H70 source-port contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

GENERAL GEOMETRIC SOURCE / MODIFICATION NOTICE
The projective-immersion proof is supplied by frenzymath/Jacobian-Challenge,
commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module
Jacobian.AlgebraicGeometry.Group.QuasiProjective, theorem
GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral.
Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; Apache-2.0.

This file is a new thin actual-object application, not a second supplier copy.
It imports the already-published CloudW07JacobiansCurves namespace unchanged.
The ONLY mathematical extension is upgrading the supplied immersion to a closed
immersion using the ORIGINAL PkgI3 object's properness.  The supplier's LICENSE,
NOTICE, authorship, namespace changes, and Mathlib compatibility notices remain
in ZInQKernel/Contrib/CloudW07JacobiansCurves/; see this directory's NOTICE.md.
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudR2Hom.C4SourcePort.ClosedImmersion
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.QuasiProjective

/-!
# A closed projective embedding of the actual PkgI3 abelian variety

The result applies over every field, in arbitrary characteristic and dimension.
Its source is literally `A.X.left`, and its structural equation is literally
`A.X.hom`.  It does not replace the Hom carrier, identify point groups by an
assumption, or assume any of H70/H71/Poincare's desired conclusions.

Projectivity is a genuine geometric input to the bounded-morphism/intersection-
height approach to Hom finite generation.  It is NOT by itself a proof of Hom
finite generation, the rank bound, or integral tensor-Tate faithfulness.
-/

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Hom.C4SourcePort

universe u

/-- Every actual `PkgI3.AbVar` has a closed embedding into finite-coordinate
projective space, over its original field and on its original scheme. -/
theorem exists_closedImmersion_projectiveSpace
    {k : Type u} [Field k] (A : _root_.PkgI3.AbVar k) :
    ∃ (coordinates : Type u) (_ : Finite coordinates)
      (embedding : A.X.left ⟶ ℙ(coordinates; Spec (.of k))),
      IsClosedImmersion embedding ∧
        embedding ≫ ℙ(coordinates; Spec (.of k)) ↘ Spec (.of k) = A.X.hom := by
  obtain ⟨coordinates, finite, embedding, immersion, over⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral A.X
  letI := finite
  letI := immersion
  haveI : IsProper
      (embedding ≫ ℙ(coordinates; Spec (.of k)) ↘ Spec (.of k)) := by
    rw [over]
    infer_instance
  haveI : IsProper embedding :=
    IsProper.of_comp embedding (ℙ(coordinates; Spec (.of k)) ↘ Spec (.of k))
  exact ⟨coordinates, finite, embedding, isClosedImmersion_of_isProper embedding, over⟩

end ZInQ.Contrib.CloudR2Hom.C4SourcePort

#print axioms ZInQ.Contrib.CloudR2Hom.C4SourcePort.exists_closedImmersion_projectiveSpace
