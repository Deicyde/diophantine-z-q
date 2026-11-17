/-
Lane5 producer for C3's exact UniversallyOpenOverField.{u} interface.
SOURCE ONLY / UNCOMPILED. Truth pre-check: TRUE, Stacks0383.

The current pinned Mathlib source ALREADY contains the required low-priority
instance in Morphisms/UniversallyOpen.lean146–170, for an integral singleton
target. Its actual proof reduces affine base changes to the field tensor
product prime-spectrum open-map theorem. This interface adapts that genuine
all-scheme result; no LFT/flat-finite-presentation/AlgClosed/smoothness or
characteristic restriction is added. It does not author another openness
core or assume the output as a Fact.
-/
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import ZInQKernel.Contrib.CloudR2NOS.Step1.IdentityComponent

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory

namespace H5OriginalDVR.Lane5.GM3Geometry

/-- EXACT C3 consumer. Spec of ANY field is integral and a singleton; the
held Mathlib instance supplies universal openness for every scheme over it. -/
theorem universallyOpenOverField :
    ZInQ.Contrib.CloudR2NOS.Step1.UniversallyOpenOverField.{u} := by
  intro k _ X f
  letI : IsIntegral (Spec (CommRingCat.of k)) := inferInstance
  letI : Subsingleton (Spec (CommRingCat.of k)) := inferInstance
  exact inferInstance

end H5OriginalDVR.Lane5.GM3Geometry
