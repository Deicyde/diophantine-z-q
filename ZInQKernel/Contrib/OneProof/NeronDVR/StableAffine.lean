import ZInQKernel.Contrib.OneProof.NeronDVR.QuasiAffineDescent
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.AffineScheme.FiniteSet

/-!
# Invariant affine neighborhoods

A finite set of points in an invariant quasi-affine open is contained in an
invariant affine open inside it. Descend the quasi-affine open, choose a
common affine neighborhood in the quotient, and pull it back.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
theorem exists_affineOpen_of_finite {X : Scheme.{u}} [X.IsQuasiAffine] {s : Set X}
    (hs : s.Finite) : ∃ U : X.Opens, IsAffineOpen U ∧ s ⊆ U := by
  let i := X.toSpecΓ
  obtain ⟨a, ha, ha'⟩ := (isAffineOpen_top _).exists_basicOpen_le_of_finite
    (O := i.opensRange) le_top (hs.image i) (Set.image_subset_range _ _)
  let V := (Spec Γ(X, ⊤)).basicOpen a
  have hV : IsAffineOpen V := (isAffineOpen_top _).basicOpen a
  refine ⟨i ⁻¹ᵁ V, ?_, fun x hx => ha ⟨x, hx, rfl⟩⟩
  have hem : i ''ᵁ (i ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr ha']
  refine (i.isAffineOpen_iff_of_isOpenImmersion (U := i ⁻¹ᵁ V)).mp ?_
  rw [hem]
  exact hV

end AlgebraicGeometry.Scheme

namespace CategoryTheory.Over.DescentDatum

set_option backward.isDefEq.respectTransparency false in
/-- Any finite subset of an invariant quasi-affine open is contained in a
smaller invariant open which is affine. -/
theorem exists_invariant_affineOpen_between
    {S S' : Scheme.{u}} [IsAffine S] [IsAffine S'] {p : S' ⟶ S}
    [Flat p] [Surjective p] [QuasiCompact p]
    {X : Over S'} (d : DescentDatum p X) {U : X.left.Opens} [U.toScheme.IsQuasiAffine]
    (hU : d.IsInvariant U) {s : Set X.left} (hs : s.Finite) (hsU : s ⊆ U) :
    ∃ V : X.left.Opens, d.IsInvariant V ∧ IsAffineOpen V ∧ s ⊆ V ∧ V ≤ U := by
  have : (Over.mk (U.ι ≫ X.hom)).left.IsQuasiAffine := ‹U.toScheme.IsQuasiAffine›
  obtain ⟨W, r, hW, hq, hcompat⟩ := (d.restrict U hU).exists_quasiAffine_descent
  have : W.left.IsQuasiAffine := hW
  let t := U.ι ⁻¹' s
  have ht : t.Finite := hs.preimage U.ι.isEmbedding.injective.injOn
  obtain ⟨A, hA, htA⟩ := Scheme.exists_affineOpen_of_finite (ht.image r)
  have : IsAffineHom r := MorphismProperty.of_isPullback hq.flip inferInstance
  let B := r ⁻¹ᵁ A
  let V := U.ι ''ᵁ B
  have hB : IsAffineOpen B := hA.preimage r
  have hV : IsAffineOpen V := hB.image_of_isOpenImmersion U.ι
  have hVU : V ≤ U := U.ι_image_le B
  refine ⟨V, ?_, hV, ?_, hVU⟩
  · intro T a b hab x hx
    have hxU : Set.range x.left ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      exact hx.trans hVU
    let l := IsOpenImmersion.lift U.ι x.left hxU
    have hl : l ≫ U.ι = x.left := IsOpenImmersion.lift_fac _ _ _
    let point : Over.mk a ⟶ Over.mk (U.ι ≫ X.hom) :=
      Over.homMk l (by
        change l ≫ U.ι ≫ X.hom = a
        rw [← Category.assoc, hl]
        exact Over.w x)
    have hl' : point.left ≫ U.ι = x.left := hl
    have hx' : (Over.homMk (point.left ≫ U.ι) (by rw [hl']; exact Over.w x) :
        Over.mk a ⟶ X) = x := Over.OverMorphism.ext hl
    have heq := d.restrict_transport_left_ι U hU a b hab point
    rw [hx'] at heq
    rintro _ ⟨z, rfl⟩
    have hstep := hcompat a b hab point
    rw [← heq, Scheme.Hom.comp_apply]
    refine ⟨((d.restrict U hU).transport a b hab point).left z, ?_, rfl⟩
    change r (((d.restrict U hU).transport a b hab point).left z) ∈ A
    rw [← Scheme.Hom.comp_apply, hstep, Scheme.Hom.comp_apply]
    have hz := hx (Set.mem_range_self z)
    obtain ⟨z', hz', hz'eq⟩ := hz
    have hlz : U.ι (l z) = x.left z := by rw [← Scheme.Hom.comp_apply, hl]
    have hpt : point.left z = z' := U.ι.isEmbedding.injective (hlz.trans hz'eq.symm)
    change point.left z ∈ B
    rwa [hpt]
  · intro y hy
    let yU : U.toScheme := ⟨y, hsU hy⟩
    exact ⟨yU, htA ⟨yU, hy, rfl⟩, rfl⟩

end CategoryTheory.Over.DescentDatum
