/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.D7.Defs
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField
import ZInQKernel.Contrib.CloudB3W13.Source.Theorems.Thm_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension

/-!
# W13 dictionary D7, step 5: fake elliptic curves over any ring are smooth of relative dimension 2

FLT proves `SmoothOfRelativeDimension 2 E.f` for `E` over a field
(`FakeEllipticCurve.smoothOfRelativeDimension_two`). Over an arbitrary ring `R`:
* `E.f` is smooth, so near any `x` it has a standard-smooth chart of some relative dimension `m`;
* that chart restricts to the fibre over `f x` (FLT
  `exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField`);
* the fibre is the base change of `E` to the residue field, so by the field theorem and FLT
  `eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension` we get `m = 2`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary.D7

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj ZInQ.Contrib.CloudW03NeronSurj.FLT
open ZInQ.Contrib.CloudW03NeronSurj.FLT.CerednikDrinfeld.QM

/-- The fibre of a fake elliptic curve over a point of the base is smooth of relative dimension 2. -/
lemma smoothOfRelativeDimension_fiber {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {R : Type} [CommRing R] (E : FakeEllipticCurve Λ N R) (y : Spec (CommRingCat.of R)) :
    SmoothOfRelativeDimension 2 (E.f.fiberToSpecResidueField y) := by
  set κ := (Spec (CommRingCat.of R)).residueField y
  let φ : CommRingCat.of R ⟶ κ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField y)
  obtain ⟨E', g, hg, -, -, -, -⟩ := FakeEllipticCurve.exists_isPullback_levelIff φ.hom E
  have hE' : SmoothOfRelativeDimension 2 E'.f := FakeEllipticCurve.smoothOfRelativeDimension_two _ E'
  have hφ : Spec.map (CommRingCat.ofHom φ.hom) = (Spec (CommRingCat.of R)).fromSpecResidueField y := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  rw [hφ] at hg
  have hpb : IsPullback (pullback.fst E.f ((Spec (CommRingCat.of R)).fromSpecResidueField y))
      (E.f.fiberToSpecResidueField y) E.f ((Spec (CommRingCat.of R)).fromSpecResidueField y) :=
    IsPullback.of_hasPullback _ _
  have hfac := hg.flip.isoIsPullback_hom_fst _ _ hpb.flip
  have heq : E.f.fiberToSpecResidueField y = (hg.flip.isoIsPullback _ _ hpb.flip).inv ≫ E'.f :=
    (Iso.eq_inv_comp _).mpr hfac
  rw [heq]
  exact smoothOfRelativeDimension_comp 0 2 (hg.flip.isoIsPullback _ _ hpb.flip).inv E'.f

/-- **A fake elliptic curve over any ring is smooth of relative dimension 2.** -/
theorem smoothOfRelativeDimension_two_ring {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {R : Type} [CommRing R] (E : FakeEllipticCurve Λ N R) : SmoothOfRelativeDimension 2 E.f := by
  haveI : Smooth E.f := E.bundle.smooth
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth E.f x
  obtain ⟨m, hm⟩ : ∃ m, (E.f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m := by
    algebraize [(E.f.appLE U V e).hom]
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hstd.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  obtain ⟨U', V', hV', hx', e', hm'⟩ :=
    FLT.AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField E.f x _ U hU V hV hxV
      e hm
  have h2 := FLT.AlgebraicGeometry.eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
    (E.f.fiberToSpecResidueField (E.f.base x)) 2 (smoothOfRelativeDimension_fiber E (E.f.base x))
    _ U' V' hV' _ hx' e' hm'
  rw [h2] at hm
  exact ⟨U, hU, V, hV, hxV, e, hm⟩

/-- `DimInput`, proved. -/
theorem dimInput : DimInput := fun _ _ E => smoothOfRelativeDimension_two_ring E

end ZInQ.Contrib.CloudB2Shimura.Dictionary.D7
