import ZInQKernel.Contrib.OneProof.NeronDVR.SectionSpanCover
import ZInQKernel.Contrib.CloudR2NOS.Descent.Coaction

/-!
# Nonvanishing covers after faithfully flat extension

Flat base change of global sections yields a pointwise nonvanishing cover
downstairs. Quasi-affineness of each nonvanishing locus follows from descent
of its open immersion into the affinization.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped MonoidalCategory TensorProduct

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- Quasi-affineness of a quasi-compact, quasi-separated scheme over an
affine base is reflected by a faithfully flat affine base change. -/
theorem isQuasiAffine_of_isPullback_of_faithfullyFlat
    {S S' X X' : Scheme.{u}} [IsAffine S] [IsAffine S']
    {p : S' ⟶ S} [Flat p] [Surjective p] [QuasiCompact p]
    {f : X ⟶ S} {g : X' ⟶ S'} {a : X' ⟶ X} (h : IsPullback a g f p)
    [QuasiSeparatedSpace X] [X'.IsQuasiAffine] :
    X.IsQuasiAffine := by
  have : Surjective a := MorphismProperty.of_isPullback h.flip inferInstance
  have : CompactSpace X := a.surjective.compactSpace a.continuous
  let q := Spec.map a.appTop
  let ff := Spec.map f.appTop ≫ S.isoSpec.inv
  let gg := Spec.map g.appTop ≫ S'.isoSpec.inv
  let e := h.isoPullback
  have hp := isPushout_appTop_of_flat p f
  have hs := isPullback_SpecMap_of_isPushout _ _ _ _ hp
  have hleft : Spec.map (pullback.fst f p).appTop =
      Spec.map e.inv.appTop ≫ q := by
    rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop]
    congr 2
    exact h.isoPullback_inv_fst.symm
  have hright : Spec.map (pullback.snd f p).appTop =
      Spec.map e.inv.appTop ≫ Spec.map g.appTop := by
    rw [← Spec.map_comp, ← Scheme.Hom.comp_appTop]
    congr 2
    exact h.isoPullback_inv_snd.symm
  have hpSpec : Spec.map p.appTop ≫ S.isoSpec.inv = S'.isoSpec.inv ≫ p := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.isoSpec_hom, ← Scheme.toSpecΓ_naturality,
      Category.assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]
  have hAff : IsPullback q gg ff p := by
    have : IsIso (Spec.map e.inv.appTop) := by
      change IsIso (Scheme.Spec.map (Scheme.Γ.map e.inv.op).op)
      infer_instance
    let e' := asIso (Spec.map e.inv.appTop)
    refine hs.of_iso e' (Iso.refl _) S'.isoSpec.symm S.isoSpec.symm
      (by simpa [e'] using hleft) ?_ (by simp [ff]) hpSpec
    change Spec.map (pullback.snd f p).appTop ≫ S'.isoSpec.inv =
      Spec.map e.inv.appTop ≫ (Spec.map g.appTop ≫ S'.isoSpec.inv)
    rw [hright, Category.assoc]
  have hff : X.toSpecΓ ≫ ff = f := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom,
      Iso.hom_inv_id, Category.comp_id]
  have hgg : X'.toSpecΓ ≫ gg = g := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom,
      Iso.hom_inv_id, Category.comp_id]
  have hpb : IsPullback X'.toSpecΓ a q X.toSpecΓ := by
    apply (show IsPullback (X'.toSpecΓ ≫ gg) a p (X.toSpecΓ ≫ ff) from
      by rw [hff, hgg]; exact h.flip).of_right (Scheme.toSpecΓ_naturality a).symm hAff.flip
  have hqSurj : Surjective q := MorphismProperty.of_isPullback hAff.flip inferInstance
  have hqFlat : Flat q := MorphismProperty.of_isPullback hAff.flip inferInstance
  have hqQc : QuasiCompact q := MorphismProperty.of_isPullback hAff.flip inferInstance
  have : IsOpenImmersion X.toSpecΓ :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsOpenImmersion)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb ⟨⟨hqSurj, hqFlat⟩, hqQc⟩
      inferInstance
  exact {}

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

open ZInQ.Contrib.CloudR2NOS.Descent
open AlgebraicGeometry.SectionPencil (pullbackSectionHom pullbackSectionHom_zeroLocus)

set_option backward.isDefEq.respectTransparency false in
theorem preimage_nonvanishing {X X' : Scheme.{u}} (a : X' ⟶ X)
    {L : X.Modules} [L.IsInvertible] (s : 𝟙_ X.Modules ⟶ L) :
    (pullbackSectionHom a s).zeroLocus.support.compl = a ⁻¹ᵁ s.zeroLocus.support.compl := by
  ext x
  change x ∉ ((pullbackSectionHom a s).zeroLocus.support : Set X') ↔
    x ∉ a ⁻¹' (s.zeroLocus.support : Set X)
  rw [pullbackSectionHom_zeroLocus, Scheme.IdealSheafData.coe_support_comap]

abbrev globalPullbackSection
    {X X' : Scheme.{u}} (a : X' ⟶ X) {L : X.Modules} (s : Γ(L, ⊤)) :
    Γ((Scheme.Modules.pullback a).obj L, ⊤) :=
  Scheme.Modules.pullbackSection a (U := ⊤) s

set_option backward.isDefEq.respectTransparency false in
theorem homOfGlobalSection_pullbackSection
    {X X' : Scheme.{u}} (a : X' ⟶ X) {L : X.Modules} (s : Γ(L, ⊤)) :
    homOfGlobalSection ((Scheme.Modules.pullback a).obj L)
      (globalPullbackSection a s) =
      pullbackSectionHom a (homOfGlobalSection L s) := by
  let M := (Scheme.Modules.pullback a).obj L
  apply (unitHomAddEquiv M).injective
  change (unitHomAddEquiv M).toFun ((unitHomAddEquiv M).invFun
    (globalPullbackSection a s)) = _
  rw [(unitHomAddEquiv M).right_inv]
  change _ = (((pullbackObjUnitIso a).inv ≫ (Scheme.Modules.pullback a).map
    (homOfGlobalSection L s)).app (a ⁻¹ᵁ ⊤)) (1 : Γ(X', ⊤))
  rw [← pullbackSection_app_one]
  exact congrArg (Scheme.Modules.pullbackSection a (U := ⊤)) ((unitHomAddEquiv L).right_inv s).symm

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
  {X X' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {g : X' ⟶ Spec (CommRingCat.of R')} {a : X' ⟶ X}
  (h : IsPullback a g f (Spec.map (CommRingCat.ofHom (algebraMap R R'))))

include h

set_option backward.isDefEq.respectTransparency false in
/-- For a flat base change of a quasi-compact, quasi-separated scheme,
pulled-back global sections generate the global sections upstairs. -/
theorem span_pullbackSection [Module.Flat R R'] [QuasiCompact f] [QuasiSeparated f]
    (L : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) L] :
    letI := moduleTop g ((Scheme.Modules.pullback a).obj L)
    ∀ s : Γ((Scheme.Modules.pullback a).obj L, ⊤), s ∈ Submodule.span R'
      (Set.range (globalPullbackSection a (L := L))) := by
  let := moduleTop g ((Scheme.Modules.pullback a).obj L)
  intro s
  obtain ⟨t, rfl⟩ := (bijective_sectionsBC h L).surjective s
  induction t using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => rw [map_add]; exact Submodule.add_mem _ h₁ h₂
  | tmul r s =>
    rw [sectionsBC_tmul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨s, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/-- A faithfully flat affine base change with an affine nonvanishing cover
supplies nonvanishing sections downstairs and makes the nonvanishing loci
of all global sections downstairs quasi-affine. -/
theorem nonvanishing_cover_of_pullback [Module.FaithfullyFlat R R'] [QuasiCompact f]
    [QuasiSeparated f] {L : X.Modules} [L.IsInvertible]
    (hCover : ∀ x' : X', ∃ s : 𝟙_ X'.Modules ⟶ (Scheme.Modules.pullback a).obj L,
      x' ∈ s.zeroLocus.support.compl ∧ IsAffineOpen s.zeroLocus.support.compl) :
    (∀ x : X, ∃ s : 𝟙_ X.Modules ⟶ L, x ∈ s.zeroLocus.support.compl) ∧
    ∀ s : 𝟙_ X.Modules ⟶ L, (Scheme.Opens.toScheme (X := X) s.zeroLocus.support.compl).IsQuasiAffine := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R R'))
  let M := (Scheme.Modules.pullback a).obj L
  have hff := RingHom.faithfullyFlat_algebraMap_iff.mpr (inferInstance : Module.FaithfullyFlat R R')
  have hp : Flat p ∧ Surjective p :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R R'))).mpr hff
  have : Flat p := hp.1
  have : Surjective p := hp.2
  have : QuasiCompact p := show QuasiCompact (Spec.map _) from inferInstance
  have : Surjective a := MorphismProperty.of_isPullback h.flip inferInstance
  have : QuasiCompact g := MorphismProperty.of_isPullback h inferInstance
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace g
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : M.IsInvertible := inferInstance
  have := SheafOfModules.IsInvertible.isQuasicoherent.{u, u, u}
    (inferInstance : L.IsInvertible)
  constructor
  · intro x
    obtain ⟨x', rfl⟩ := a.surjective x
    obtain ⟨t, ht, _⟩ := hCover x'
    obtain ⟨s, ⟨s₀, rfl⟩, hs⟩ := exists_nonvanishing_of_span
      ((g.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso _).inv.hom)
      _ (span_pullbackSection h L) ⟨t, ht⟩
    rw [homOfGlobalSection_pullbackSection, preimage_nonvanishing] at hs
    exact ⟨homOfGlobalSection L s₀, hs⟩
  · intro s
    let V : X.Opens := s.zeroLocus.support.compl
    have hV' : (a ⁻¹ᵁ V).toScheme.IsQuasiAffine := by
      rw [← preimage_nonvanishing a s]
      exact isQuasiAffine_nonvanishing_of_exists_affine hCover (pullbackSectionHom a s)
    have : QuasiSeparatedSpace V.toScheme := quasiSeparatedSpace_of_quasiSeparated V.ι
    have hres : IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ g) (V.ι ≫ f) p :=
      (isPullback_morphismRestrict a V).paste_vert h
    exact Scheme.isQuasiAffine_of_isPullback_of_faithfullyFlat hres

end AlgebraicGeometry.Scheme.Modules

namespace CategoryTheory.Over.DescentDatum

open Scheme.Modules

/-- A cover by nonvanishing loci and quasi-affineness of those loci
suffice to descend a datum with spanning compatible sections. -/
theorem isEffective_of_span_compatible_sections_of_quasiAffine
    {S S' : Scheme.{u}} [IsAffine S] [IsAffine S'] {p : S' ⟶ S}
    [Flat p] [Surjective p] [QuasiCompact p] {X : Over S'}
    (d : DescentDatum p X) {L : X.left.Modules} [L.IsInvertible]
    (ψ : (Scheme.Modules.pullback (pullback.fst (X.hom ≫ p) p)).obj L ≅
      (Scheme.Modules.pullback d.toHom).obj L)
    {R : Type u} [CommRing R] (r : R →+* Γ(X.left, ⊤))
    (hspan : letI := Module.compHom Γ(L, ⊤) r
      ∀ s, s ∈ Submodule.span R {s |
        ψ.hom.app ⊤ (globalPullbackSection (pullback.fst (X.hom ≫ p) p) s) =
          globalPullbackSection d.toHom s})
    (hcover : ∀ x : X.left, ∃ s : 𝟙_ X.left.Modules ⟶ L, x ∈ s.zeroLocus.support.compl)
    (hqa : ∀ s : 𝟙_ X.left.Modules ⟶ L,
      (Scheme.Opens.toScheme (X := X.left) s.zeroLocus.support.compl).IsQuasiAffine) :
    d.IsEffective := by
  apply d.isEffective_of_forall_exists_mem
  intro x
  obtain ⟨s, hs, hx⟩ := exists_nonvanishing_of_span r _ hspan (hcover x)
  let t := homOfGlobalSection L s
  let U : X.left.Opens := t.zeroLocus.support.compl
  have hinv : d.IsInvariant U := d.isInvariant_nonvanishing_of_pullbackSection ψ s hs
  have : (Over.mk (U.ι ≫ X.hom)).left.IsQuasiAffine := hqa t
  exact ⟨U, hinv, hx, (d.restrict U hinv).isEffective_of_isQuasiAffine⟩

end CategoryTheory.Over.DescentDatum
