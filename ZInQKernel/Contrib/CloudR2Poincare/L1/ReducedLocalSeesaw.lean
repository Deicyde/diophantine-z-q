import ZInQKernel.Contrib.CloudR2Poincare.L1.NonzeroFibreSection
import ZInQKernel.Contrib.CloudR2Poincare.L2.RelativeFibreTriviality

/-! Actual local seesaw over every reduced locally noetherian parameter.
Affine coefficient base change supplies genuine local trivializations;
actual open-immersion range comparison transports them to parameter opens.
The final theorem has exactly the LocalSeesawProbe telescope. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Strong all-base local seesaw: every residue-trivial invertible sheaf on a
proper flat geometrically integral family over a reduced locally noetherian
base is genuinely trivial over a neighborhood of each parameter. -/
theorem exists_open_iso_unit_of_trivial_residue_fibres
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y] [AlgebraicGeometry.IsReduced Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible]
    (hFibres : ∀ y : Y, Scheme.Pic.map (f.fiberι y) (Scheme.Pic.mk M) = 1)
    (y : Y) :
    ∃ W : Y.Opens, y ∈ W ∧
      Nonempty ((Scheme.Modules.pullback ((f ⁻¹ᵁ W).ι)).obj M ≅
        Scheme.Modules.unit (f ⁻¹ᵁ W).toScheme) := by
  classical
  obtain ⟨i, u, hu⟩ := Y.affineCover.exists_eq y
  let Yi := Y.affineCover.X i
  let R := Γ(Yi, ⊤)
  let g : Spec R ⟶ Y := Yi.isoSpec.inv ≫ Y.affineCover.f i
  let u' : Spec R := Yi.isoSpec.hom u
  have hu' : g u' = y := by
    dsimp only [g, u']
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    exact hu
  letI : IsLocallyNoetherian Yi := LocallyOfFiniteType.isLocallyNoetherian (Y.affineCover.f i)
  letI : AlgebraicGeometry.IsReduced Yi :=
    isReduced_of_isOpenImmersion (Y.affineCover.f i)
  letI : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian (⟨⊤, isAffineOpen_top Yi⟩ : Yi.affineOpens)
  letI : _root_.IsReduced R := inferInstanceAs (_root_.IsReduced Γ(Yi, ⊤))
  let px := pullback.fst f g
  let pf := pullback.snd f g
  let M' := (Scheme.Modules.pullback px).obj M
  have hM' : ∀ z : Spec R, Scheme.Pic.map (pf.fiberι z) (Scheme.Pic.mk M') = 1 := by
    intro z
    have hz := ZInQ.Contrib.CloudR2Poincare.L2.fibrePicardClass_baseChange_of_eq_one
      (IsPullback.of_hasPullback f g) (Scheme.Pic.mk M) z (hFibres (g z))
    simpa only [M', Scheme.Pic.map_mk] using hz
  obtain ⟨V, huV, hV⟩ := exists_open_iso_unit_of_trivial_residue_fibres_affine R pf M' hM' u'
  let W := g ''ᵁ V
  let U := pf ⁻¹ᵁ V
  let j : U.toScheme ⟶ X := U.ι ≫ px
  have hunit : Scheme.Pic.map j (Scheme.Pic.mk M) = 1 := by
    change Scheme.Pic.map (U.ι ≫ px) (Scheme.Pic.mk M) = 1
    rw [Scheme.Pic.map_comp, Scheme.Pic.map_mk, Scheme.Pic.map_mk]
    exact ((Scheme.Pic.mk_eq_mk_iff _ _).mpr hV).trans (Scheme.Pic.one_eq_mk_unit).symm
  have himage : px ''ᵁ U = f ⁻¹ᵁ W :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (IsPullback.of_hasPullback f g).flip V
  have hrange : Set.range j = Set.range (f ⁻¹ᵁ W).ι := by
    change Set.range (px.base ∘ U.ι.base) = Set.range (f ⁻¹ᵁ W).ι
    rw [Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact congrArg (fun O : X.Opens ↦ (O : Set X)) himage
  let e := IsOpenImmersion.isoOfRangeEq j (f ⁻¹ᵁ W).ι hrange
  have he : e.hom ≫ (f ⁻¹ᵁ W).ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have ht : Scheme.Pic.map (f ⁻¹ᵁ W).ι (Scheme.Pic.mk M) = 1 := by
    apply pic_map_injective_of_isIso e.hom
    rw [← Scheme.Pic.map_comp, he, hunit, Scheme.Pic.map_one]
  refine ⟨W, ⟨u', huV, hu'⟩, ?_⟩
  apply (Scheme.Pic.mk_eq_mk_iff _ _).mp
  rw [← Scheme.Pic.map_mk, ht]
  exact Scheme.Pic.one_eq_mk_unit

/-- The exact local/Grauert obligation of LocalSeesawProbe, with the original
family and the actual relative parameter base-change morphism. Normalization
is retained in the telescope but local triviality is proved without needing it. -/
theorem localNormalizedSeesaw
    {k : Type u} [Field k] {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [IsProper π] [GeometricallyIntegral π]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ π = 𝟙 _)
    (T : Over (Spec (.of k))) [IsLocallyNoetherian T.left] [AlgebraicGeometry.IsReduced T.left]
    (M : (pullback π T.hom).Modules) [M.IsInvertible]
    (hNorm : Scheme.Pic.map (sectionBaseChange π σ hσ T) (Scheme.Pic.mk M) = 1)
    (hFibres : ∀ t : T.left,
      Scheme.Pic.map (pullback.fst (pullback.snd π T.hom) (T.left.fromSpecResidueField t))
        (Scheme.Pic.mk M) = 1)
    (t : T.left) :
    ∃ U : T.left.Opens, t ∈ U ∧
      let Uover : Over (Spec (.of k)) := Over.mk (U.ι ≫ T.hom)
      let g : Uover ⟶ T := Over.homMk U.ι (by rfl)
      Nonempty ((Scheme.Modules.pullback (JacobianChallenge.baseChangeMap π g)).obj M ≅
        Scheme.Modules.unit (pullback π Uover.hom)) := by
  let f := pullback.snd π T.hom
  obtain ⟨U, ht, hU⟩ := exists_open_iso_unit_of_trivial_residue_fibres f M hFibres t
  let Uover : Over (Spec (.of k)) := Over.mk (U.ι ≫ T.hom)
  let g : Uover ⟶ T := Over.homMk U.ι (by rfl)
  let b := JacobianChallenge.baseChangeMap π g
  let V := f ⁻¹ᵁ U
  have hb : b ≫ f = pullback.snd π Uover.hom ≫ U.ι := by
    simp [b, f, JacobianChallenge.baseChangeMap, g]
  have hrange : Set.range b ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change f (b x) ∈ U
    rw [← Scheme.Hom.comp_apply, hb, Scheme.Hom.comp_apply]
    exact (pullback.snd π Uover.hom x).property
  let a := IsOpenImmersion.lift V.ι b hrange
  have ha : a ≫ V.ι = b := IsOpenImmersion.lift_fac _ _ _
  have hV : Scheme.Pic.map V.ι (Scheme.Pic.mk M) = 1 := by
    rw [Scheme.Pic.map_mk]
    exact ((Scheme.Pic.mk_eq_mk_iff _ _).mpr hU).trans (Scheme.Pic.one_eq_mk_unit).symm
  have hB : Scheme.Pic.map b (Scheme.Pic.mk M) = 1 := by
    rw [← ha, Scheme.Pic.map_comp, hV, Scheme.Pic.map_one]
  refine ⟨U, ht, ?_⟩
  apply (Scheme.Pic.mk_eq_mk_iff _ _).mp
  rw [← Scheme.Pic.map_mk, hB]
  exact Scheme.Pic.one_eq_mk_unit

end ZInQ.Contrib.CloudR2Poincare.L1
