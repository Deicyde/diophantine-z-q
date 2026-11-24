/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

NOTICE OF MODIFICATION / PURPOSE (2026-11-14): new ACTUAL special-fibre generic
point bridge to the accepted H76 smooth-DVR vertical-stalk constructor. Source
proof/notices remain unchanged. The point is the image of the generic point
of the SAME scheme-theoretic closed fibre, not an assumed vertical valuation.

Special-fibre integrality is an explicit intermediate geometry input to be
proved from the actual good model; no original-O henselianity, CharZero,
perfectness, projectivity or NOS/model existence is assumed. This does not yet
identify the original base uniformizer as the vertical uniformizer or construct
a generic line extension. It supplies the real vertical DVR existence input.
-/
import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.P2M.Sol.S_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension

/-- The ACTUAL generic point of a scheme-theoretic fibre, viewed in its model. -/
def verticalGenericPoint {X S : Scheme.{u}} (f : X ⟶ S) (c : S)
    [IrreducibleSpace (f.fiber c)] : X :=
  f.fiberι c (genericPoint (f.fiber c))

theorem verticalGenericPoint_base {X S : Scheme.{u}} (f : X ⟶ S) (c : S)
    [IrreducibleSpace (f.fiber c)] : f (verticalGenericPoint f c) = c := by
  have h : verticalGenericPoint f c ∈ Set.range (f.fiberι c) := ⟨_, rfl⟩
  rw [f.range_fiberι c] at h
  exact h

/-- There is no strict GENERIZATION of that point still in the SAME special
fibre. This follows from the actual fibre embedding/generic point, not an
assumed codimension-one or discrete-valuation Fact. -/
theorem verticalGenericPoint_no_special_generization {X S : Scheme.{u}}
    (f : X ⟶ S) (c : S) [IrreducibleSpace (f.fiber c)]
    (y : X) (hsp : y ⤳ verticalGenericPoint f c) (hy : f y = c) :
    y = verticalGenericPoint f c := by
  let z : f.fiber c := (f.fiberHomeo c).symm ⟨y, hy⟩
  have hz : f.fiberι c z = y := f.fiberι_fiberHomeo_symm c ⟨y, hy⟩
  have hzsp : z ⤳ genericPoint (f.fiber c) := by
    apply (f.fiberι c).isEmbedding.isInducing.specializes_iff.mp
    simpa only [hz, verticalGenericPoint] using hsp
  have he : z = genericPoint (f.fiber c) :=
    (hzsp.antisymm ((genericPoint_spec (f.fiber c)).specializes (Set.mem_univ z))).eq
  rw [← hz, he]
  rfl

/-- Construct the actual vertical DVR at the image of the original closed
fibre's generic point, using the genuine H76 proof and the proved fibre data. -/
theorem verticalGenericPoint_stalk_isDVR
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    [IsIntegral (f.fiber (IsLocalRing.closedPoint R))] :
    ∃ _ : IsDomain (X.presheaf.stalk (verticalGenericPoint f (IsLocalRing.closedPoint R))),
      IsDiscreteValuationRing (X.presheaf.stalk (verticalGenericPoint f (IsLocalRing.closedPoint R))) := by
  exact ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes.solution
    R f (verticalGenericPoint f (IsLocalRing.closedPoint R))
    (verticalGenericPoint_base f _)
    (fun y hsp hy => verticalGenericPoint_no_special_generization f _ y hsp hy)

#print axioms verticalGenericPoint_no_special_generization
#print axioms verticalGenericPoint_stalk_isDVR

end ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension
