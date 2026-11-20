/-
Ported from AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b.
Source: StacksFrontier/AlgebraicGeometry/SchemeTheoreticImage/Reduced.lean
Upstream license: Apache-2.0; see EGAProperLimit/LICENSE.
Modified for the Z-in-Q kernel (ega-limit, 2026-11-16): import paths remapped into EGAProperLimit (modules already
vendored in CloudW01Spread are imported from there); the upstream lakefile option
`maxSynthPendingDepth = 3` is set in the file; four declaration names that clash with
CloudW07JacobiansCurves are renamed (ProjectiveSpace -> StacksProjectiveSpace, and three
lemmas get the suffix _stacks; see NOTICE.md). The mathematical content and proofs are unchanged.
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ZInQKernel.Contrib.CloudW01Spread.StacksCore.Tactic.StacksAttribute
public import ZInQKernel.Contrib.CloudB3W16Dimension.StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

-- Port: the upstream lakefile sets `maxSynthPendingDepth = 3` for every file.
set_option maxSynthPendingDepth 3

/-!
# The scheme-theoretic image of a reduced scheme

For a morphism of schemes `f : X ⟶ Y` with `X` reduced, the scheme-theoretic image of `f` is the
reduced induced closed subscheme structure on the closure of the set-theoretic image of `f`:
the kernel ideal sheaf `AlgebraicGeometry.Scheme.Hom.ker` cutting out the image coincides with
the vanishing ideal sheaf of `closure (Set.range f)`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.ker_eq_vanishingIdeal_closure_range`: the scheme-theoretic image
  of a morphism from a reduced scheme is the reduced induced structure on the closure of the
  set-theoretic image.
* `AlgebraicGeometry.Scheme.Hom.support_ker_eq_closure_range`: consequently the image is
  supported on the closure of the set-theoretic image, with no quasi-compactness hypothesis.
* `AlgebraicGeometry.Scheme.Hom.isReduced_image`: and the image is itself reduced.

## Implementation notes

Closed subschemes are represented by their ideal sheaves, so the statement is an equality of
ideal sheaves rather than an identification of closed immersions.

## References

* [Stacks Project, Tag 056B](https://stacks.math.columbia.edu/tag/056B)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The scheme-theoretic image of a morphism `f : X ⟶ Y` with `X` reduced is the reduced induced
closed subscheme structure on the closure of `Set.range f`, that is, the closed subscheme cut out
by the vanishing ideal sheaf of that closure. -/
@[stacks 056B, ega "I 9.5.4" "partial"]
theorem ker_eq_vanishingIdeal_closure_range [IsReduced X] (f : X ⟶ Y) :
    f.ker = IdealSheafData.vanishingIdeal (.closure (Set.range f)) := by
  rw [← IdealSheafData.map_bot f, ← Scheme.nilradical_eq_bot (X := X),
    ← IdealSheafData.vanishingIdeal_top, IdealSheafData.map_vanishingIdeal]
  congr 2
  rw [Closeds.coe_top, Set.image_univ]

/-- The scheme-theoretic image of a morphism from a reduced scheme is supported on the closure of
the set-theoretic image. -/
@[ega "I 9.5.4" "partial"]
theorem support_ker_eq_closure_range [IsReduced X] (f : X ⟶ Y) :
    f.ker.support = .closure (Set.range f) := by
  rw [ker_eq_vanishingIdeal_closure_range]
  exact SetLike.coe_injective (IdealSheafData.coe_support_vanishingIdeal _)

/-- The scheme-theoretic image of a morphism from a reduced scheme is reduced. -/
@[ega "I 9.5.9"]
instance isReduced_image [IsReduced X] (f : X ⟶ Y) : IsReduced f.image := by
  change IsReduced f.ker.subscheme
  rw [ker_eq_vanishingIdeal_closure_range]
  infer_instance

end AlgebraicGeometry.Scheme.Hom

end
