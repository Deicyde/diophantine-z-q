/-
H65 continuation port from AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b.
Source: StacksFrontier/AlgebraicGeometry/Morphisms/ImmersionsAndAffine/ProjectiveSpaceImmersion.lean
Upstream license: Apache-2.0; see CloudW01Spread/LICENSE.
Modification notice (2026-11-14): import paths remapped into ProperVendor;
frozen supplier imports reused, and gluing imports routed through H65ModelBundle.
Original source hashes and all separately documented compatibility changes are retained.

Round-2 modification notice (2026-11-14): the NEW-side Nat-indexed
ProjectiveSpace declaration and member namespace are renamed H65ProjectiveSpace
for actual coexistence with published W7. Module paths, original source refs,
fixed targets, frozen suppliers and pinned packages are unchanged.
-/
module

public import ZInQKernel.Contrib.CloudW01Spread.ProperVendor.StacksFrontier.AlgebraicGeometry.Limits.AffineIntoProjective
public import ZInQKernel.Contrib.CloudW01Spread.ProperVendor.StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
import ZInQKernel.Contrib.CloudW01Spread.StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-affine schemes immerse into projective space over the base

A quasi-affine scheme locally of finite type over `S` immerses over `S` into a relative affine
space `𝔸ⁿ_S` (Stacks 04II, `AlgebraicGeometry.exists_immersion_affineSpace`). Composing with
`AlgebraicGeometry.H65ProjectiveSpace.affineChart`, the standard affine chart of `ℙⁿ_S` at the
zeroth homogeneous coordinate, gives an immersion over `S` into `ℙⁿ_S`.

This is the special case of Stacks 01VS in which the ample invertible sheaf is the structure
sheaf and the identification of the pullback of `𝒪(1)` is dropped, which is the only case the
proof of Chow's lemma over a Noetherian base (Stacks 0200) uses: there 01VS is applied to the
*affine* members of a finite affine open covering of the source, and only the immersion is
consumed. The tag 01VS itself is reserved for the general statement, see
`StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Basic`.

## Main results

* `AlgebraicGeometry.exists_immersion_projectiveSpace`: a quasi-affine scheme locally of finite
  type over `S` admits an immersion into `ℙⁿ_S` over `S`, for some `n`.

## References

* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 04II](https://stacks.math.columbia.edu/tag/04II)
* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry

universe u

/-- **A quasi-affine scheme locally of finite type over `S` immerses into projective space over
`S`.** This is the case of Stacks 01VS in which the ample invertible sheaf is the structure
sheaf, and it is the only case used in the proof of Chow's lemma over a Noetherian base.

The immersion into a relative affine space of Stacks 04II is composed with the standard affine
chart `𝔸ⁿ_S ⟶ ℙⁿ_S` at the zeroth homogeneous coordinate,
`AlgebraicGeometry.H65ProjectiveSpace.affineChart`.

No Tag 01VS attribute is attached: the full tag asserts, for an arbitrary ample invertible sheaf
`L` and every large enough `d`, an immersion pulling `𝒪(1)` back to `L ^⊗ d`, and
`StacksFrontier.AlgebraicGeometry.AmpleImmersionReduction.Basic` reserves the tag for the
declaration that will prove that. Neither the ampleness nor the twist is used below. -/
@[ega "II 5.3.3" "special case"]
theorem exists_immersion_projectiveSpace {X S : Scheme.{u}} (f : X ⟶ S) [X.IsQuasiAffine]
    [LocallyOfFiniteType f] :
    ∃ (n : ℕ) (i : X ⟶ H65ProjectiveSpace n S),
      IsImmersion i ∧ i ≫ (H65ProjectiveSpace n S ↘ S) = f := by
  obtain ⟨n, j, hj, hjf⟩ := exists_immersion_affineSpace f
  refine ⟨n, j ≫ H65ProjectiveSpace.affineChart n S, ?_, ?_⟩
  · have : IsImmersion j := hj
    exact inferInstanceAs (IsImmersion (_ ≫ _))
  · rw [Category.assoc, H65ProjectiveSpace.affineChart_over, hjf]

end AlgebraicGeometry

end

end
