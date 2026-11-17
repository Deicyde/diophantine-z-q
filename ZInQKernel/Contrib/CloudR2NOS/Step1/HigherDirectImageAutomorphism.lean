/-
H5 lane3 Step 1, sub-gap R2 PROVED. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

R2 `HigherDirectImageAutomorphism` (ShearVanishing.lean): `R^q f_*(ψ^*E) ≅ R^q f_* E` for a
scheme automorphism `ψ` with `ψ ≫ f = f`.

Proof (no new cohomology): the published W07 base change of higher direct images to an OPEN
subscheme of the base, `Scheme.Modules.higherDirectImagePullbackIsoRestrict`
(Cohomology/DirectImage/Restrict.lean), applied to the cartesian square
  `ψ` (top), `f` (sides), `𝟙 B` (bottom).
That square is a pullback because both of its horizontal arrows are isomorphisms. It gives
`R^q f_*(ψ^*E) ≅ (R^q f_* E)|_{𝟙 B}`. Mathlib's `restrictFunctorIsoPullback` and `pullbackId`
then identify the restriction along `𝟙 B` with the identity.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.ShearVanishing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Restrict

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem higherDirectImageAutomorphism : HigherDirectImageAutomorphism.{u} := by
  intro Z B _ f ψ _ hψ E q
  have sq : IsPullback ψ f f (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨by rw [hψ, Category.comp_id]⟩
  exact ⟨Scheme.Modules.higherDirectImagePullbackIsoRestrict sq E q ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback (𝟙 B)).app _ ≪≫
    (Scheme.Modules.pullbackId B).app _⟩

end ZInQ.Contrib.CloudR2NOS.Step1
