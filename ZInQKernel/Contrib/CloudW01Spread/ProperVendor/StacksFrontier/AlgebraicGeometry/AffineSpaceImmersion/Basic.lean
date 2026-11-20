/-
H65 continuation port from AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b.
Source: StacksFrontier/AlgebraicGeometry/AffineSpaceImmersion/Basic.lean
Upstream license: Apache-2.0; see CloudW01Spread/LICENSE.
Modification notice (2026-11-14): import paths remapped into ProperVendor;
frozen supplier imports reused, and gluing imports routed through H65ModelBundle.
Mathematical declarations and proof bodies are unchanged.
-/
module

public import ZInQKernel.Contrib.CloudW01Spread.ProperVendor.StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion

/-!
# A quasi-affine scheme of finite type over a base immerses into a relative affine space

That a quasi-affine scheme locally of finite type over `S` admits an immersion over `S` into a
finite-dimensional relative affine space is
`AlgebraicGeometry.exists_immersion_affineSpace` of
`StacksFrontier/AlgebraicGeometry/Morphisms/ImmersionsAndAffine/AffineSpaceImmersion.lean`, which
this module re-exports.

## References

* [Stacks Project, Tag 04II](https://stacks.math.columbia.edu/tag/04II)
-/
