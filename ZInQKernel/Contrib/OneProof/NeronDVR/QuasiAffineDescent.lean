import ZInQKernel.Contrib.OneProof.NeronDVR.AffinizationDescent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.Affine
import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Effective descent of quasi-affine schemes

The coaction on global sections descends the affinization of a quasi-affine
scheme. The original scheme is an open subscheme of its affinization. The
coaction makes that open saturated for the faithfully flat quotient, so its
image gives the descended open subscheme.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

universe u

variable {S S' : Scheme.{u}} {p : S' ⟶ S}
  {X : Over S'} (d : DescentDatum p X)

set_option backward.isDefEq.respectTransparency false in
private theorem opensRange_saturated {Y' Y : Scheme.{u}} (e : X.left ⟶ Y') [IsOpenImmersion e]
    (g : Y' ⟶ S') (q : Y' ⟶ Y) (f : Y ⟶ S)
    (he : e ≫ g = X.hom) (hq : IsPullback q g f p)
    (hd : d.toHom ≫ e ≫ q = pullback.fst (X.hom ≫ p) p ≫ e ≫ q) :
    q ⁻¹' (q '' (e.opensRange : Set Y')) = e.opensRange := by
  refine Set.Subset.antisymm (fun y hy => ?_) (Set.subset_preimage_image _ _)
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨s, hs₁, hs₂⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := q) (g := q) z y hzy
  let V := (pullback.fst q q) ⁻¹ᵁ e.opensRange
  have hsV : s ∈ V := by
    change pullback.fst q q s ∈ e.opensRange
    rwa [hs₁]
  let a := V.ι ≫ pullback.fst q q
  let b := V.ι ≫ pullback.snd q q
  have hab : a ≫ q = b ≫ q := by
    simp only [a, b, Category.assoc, pullback.condition]
  have hr : Set.range a ⊆ Set.range e := by
    rintro _ ⟨x, rfl⟩
    exact x.property
  let x := IsOpenImmersion.lift e a hr
  have hx : x ≫ e = a := IsOpenImmersion.lift_fac _ _ _
  have hxb : x ≫ (X.hom ≫ p) = (b ≫ g) ≫ p := by
    calc
      x ≫ X.hom ≫ p = (x ≫ e) ≫ g ≫ p := by simp only [← he, Category.assoc]
      _ = a ≫ g ≫ p := by rw [hx]
      _ = a ≫ q ≫ f := by rw [hq.w]
      _ = b ≫ q ≫ f := by simp only [← Category.assoc, hab]
      _ = (b ≫ g) ≫ p := by
        rw [hq.w]
        exact (Category.assoc b g p).symm
  let t := pullback.lift x (b ≫ g) hxb
  have ht : (t ≫ d.toHom) ≫ e = b := by
    apply hq.hom_ext
    · calc
        ((t ≫ d.toHom) ≫ e) ≫ q = t ≫ d.toHom ≫ e ≫ q := by simp only [Category.assoc]
        _ = (t ≫ pullback.fst (X.hom ≫ p) p) ≫ e ≫ q := by rw [hd, Category.assoc]
        _ = b ≫ q := by rw [show t ≫ pullback.fst (X.hom ≫ p) p = x from
          pullback.lift_fst _ _ _, ← Category.assoc, hx, hab]
    · simp only [Category.assoc, he, toHom_comp_hom, t, pullback.lift_snd]
  change y ∈ Set.range e
  let v : (V : Scheme.{u}) := ⟨s, hsV⟩
  refine ⟨(t ≫ d.toHom) v, ?_⟩
  rw [← Scheme.Hom.comp_apply, ht]
  exact hs₂

variable [Flat p] [Surjective p] [QuasiCompact p]

set_option backward.isDefEq.respectTransparency false in
private theorem quasiAffine_descent_of_openImmersion {Y' Y : Scheme.{u}} [IsAffine Y]
    [CompactSpace X.left] (e : X.left ⟶ Y') [IsOpenImmersion e]
    (g : Y' ⟶ S') (q : Y' ⟶ Y) (f : Y ⟶ S)
    (he : e ≫ g = X.hom) (hq : IsPullback q g f p)
    (hd : d.toHom ≫ e ≫ q = pullback.fst (X.hom ≫ p) p ≫ e ≫ q) :
    ∃ (W : Over S) (r : X.left ⟶ W.left), W.left.IsQuasiAffine ∧
      IsPullback r X.hom W.hom p ∧
        d.toHom ≫ r = pullback.fst (X.hom ≫ p) p ≫ r := by
  have hsat := opensRange_saturated d e g q f he hq hd
  have : Flat q := MorphismProperty.of_isPullback hq.flip inferInstance
  have : Surjective q := MorphismProperty.of_isPullback hq.flip inferInstance
  have : QuasiCompact q := MorphismProperty.of_isPullback hq.flip inferInstance
  let U : Y.Opens := ⟨q '' (e.opensRange : Set Y'),
    (Flat.isQuotientMap_of_surjective q).isOpen_preimage.mp (by rw [hsat]; exact e.opensRange.isOpen)⟩
  have hU : q ⁻¹ᵁ U = e.opensRange := TopologicalSpace.Opens.ext hsat
  have hr : Set.range (e ≫ q) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact ⟨e x, ⟨x, rfl⟩, rfl⟩
  let r := IsOpenImmersion.lift U.ι (e ≫ q) hr
  have hri : r ≫ U.ι = e ≫ q := IsOpenImmersion.lift_fac _ _ _
  have hrq : IsPullback r e U.ι q := IsOpenImmersion.isPullback _ _ _ _ hri.symm
    (by rw [Scheme.Opens.opensRange_ι, hU])
  have hrp : IsPullback r X.hom (U.ι ≫ f) p := by
    simpa only [he] using hrq.paste_vert hq
  have : Surjective r := MorphismProperty.of_isPullback hrp.flip inferInstance
  have : CompactSpace ↥U.toScheme := by
    constructor
    simpa only [Set.image_univ, Set.range_eq_univ.mpr r.surjective] using
      (isCompact_univ.image r.continuous)
  have hqa : U.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion U.ι
  refine ⟨Over.mk (U.ι ≫ f), r, hqa, hrp, ?_⟩
  · apply (cancel_mono U.ι).mp
    simp only [Category.assoc, hri, hd]

set_option backward.isDefEq.respectTransparency false in
/-- The descended scheme of a quasi-affine scheme can be taken quasi-affine. -/
theorem exists_quasiAffine_descent [IsAffine S] [IsAffine S'] [X.left.IsQuasiAffine] :
    ∃ (W : Over S) (r : X.left ⟶ W.left), W.left.IsQuasiAffine ∧
      IsPullback r X.hom W.hom p ∧
      ∀ {T : Scheme.{u}} (a b : T ⟶ S') (hab : a ≫ p = b ≫ p)
        (x : Over.mk a ⟶ X), (d.transport a b hab x).left ≫ r = x.left ≫ r := by
  obtain ⟨Y, hY, f, q, hq, hd⟩ :=
    NeronDVR.exists_affinization_descent_of_coaction p X.hom d.toHom d.toHom_comp_hom d.lift_toHom d.coactionMap_toHom
  have : IsAffine Y := hY
  have he : X.left.toSpecΓ ≫ (Spec.map X.hom.appTop ≫ S'.isoSpec.inv) = X.hom := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom,
      Iso.hom_inv_id, Category.comp_id]
  obtain ⟨W, r, hW, hr, hi⟩ := d.quasiAffine_descent_of_openImmersion X.left.toSpecΓ _ q f he hq hd
  refine ⟨W, r, hW, hr, fun a b hab x => ?_⟩
  rw [d.transport_left_eq_lift_toHom, Category.assoc, hi, pullback.lift_fst_assoc]

/-- Quasi-affine schemes satisfy effective fpqc descent over an affine base
with affine cover. -/
theorem isEffective_of_isQuasiAffine [IsAffine S] [IsAffine S'] [X.left.IsQuasiAffine] :
    d.IsEffective := by
  obtain ⟨W, r, _, hq, hr⟩ := d.exists_quasiAffine_descent
  exact ⟨W, r, hq, hr⟩

end CategoryTheory.Over.DescentDatum
