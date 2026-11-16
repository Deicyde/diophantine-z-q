/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Group.Abelian

import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Rigidity: a pointed morphism of proper geometrically integral group schemes over a field is a
homomorphism

Adapted from Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral`
(`Mathlib/AlgebraicGeometry/Group/Abelian.lean`, Andrew Yang and Christian Merten, Apache 2.0): the
same Zariski-main-theorem argument, applied to `δ(x, y) = f(x y) · (f(x) f(y))⁻¹` instead of the
commutator. W13 (Cloud Batch2 Worker 13), dictionary lane D9 groundwork.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

-- Mathlib's own build option (its `lakefile.lean`, `mathlibLeanOptions`), needed by the adapted proof.
set_option maxSynthPendingDepth 3

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary

universe u

variable {K : Type u} [Field K]

open MonoidalCategory CartesianMonoidalCategory MonObj

/-- The defect `δ(x, y) = f(xy) · (f(x) f(y))⁻¹` of a morphism into a group object. -/
noncomputable def homDefect {G H : Over (Spec (.of K))} [GrpObj G] [GrpObj H] (f : G ⟶ H) :
    G ⊗ G ⟶ H :=
  (μ[G] ≫ f) * ((fst G G ≫ f) * (snd G G ≫ f))⁻¹

theorem homDefect_eq_one_iff {G H : Over (Spec (.of K))} [GrpObj G] [GrpObj H] (f : G ⟶ H) :
    homDefect f = 1 ↔ μ[G] ≫ f = (fst G G ≫ f) * (snd G G ≫ f) := by
  rw [homDefect, mul_inv_eq_one]

theorem homDefect_eq_one_of_isAlgClosed [IsAlgClosed K]
    {G H : Over (Spec (.of K))} [IsProper G.hom] [IsIntegral (G ⊗ G).left] [GrpObj G]
    [IsProper H.hom] [GrpObj H] (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) :
    homDefect f = 1 := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : Nonempty G.left := ⟨η[G].left point⟩
  have : IsProper (G ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (G ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (G ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst G G).left := by dsimp; infer_instance
  have : Surjective (fst G G).left := by dsimp; infer_instance
  let δ : G ⊗ G ⟶ H := homDefect f
  have : IsProper (δ.left ≫ H.hom) := by rw [Over.w]; infer_instance
  have : IsProper (fst G H).left := by dsimp; infer_instance
  have : IsClosedImmersion ((lift η[G] η[H]).left ≫ (fst G H).left) := by
    simpa using inferInstanceAs (IsClosedImmersion η[G].left)
  have : IsClosedImmersion (lift η[G] η[H]).left := .of_comp _ (g := (fst G H).left)
  let γ : G ⊗ G ⟶ G ⊗ H := lift (fst _ _) δ
  have : IsProper (γ.left ≫ (fst G H).left) := by simpa [γ]
  have : IsProper γ.left := .of_comp _ (fst G H).left
  -- `δ(1, y) = 1`
  have hδ1 : η[G] ▷ G ≫ δ = toUnit _ ≫ η[H] := by
    simp only [δ, homDefect, comp_mul, GrpObj.comp_inv, ← Category.assoc, MonObj.one_mul]
    rw [whiskerRight_fst, whiskerRight_snd, Category.assoc, hf, ← leftUnitor_hom,
      toUnit_unique (fst _ _) (toUnit _), ← Hom.one_def, _root_.one_mul, _root_.mul_inv_cancel]
  -- `δ(x, 1) = 1`
  have hδ2 : G ◁ η[G] ≫ δ = toUnit _ ≫ η[H] := by
    simp only [δ, homDefect, comp_mul, GrpObj.comp_inv, ← Category.assoc, MonObj.mul_one]
    rw [whiskerLeft_fst, whiskerLeft_snd, Category.assoc, hf, ← rightUnitor_hom,
      toUnit_unique (snd _ _) (toUnit _), ← Hom.one_def, _root_.mul_one, _root_.mul_inv_cancel]
  have hδ1' : ∀ k : 𝟙_ (Over (Spec (.of K))) ⟶ G, lift η[G] k ≫ δ = η[H] := by
    intro k
    have e1 : lift η[G] k = lift (𝟙 _) k ≫ η[G] ▷ G := by ext <;> simp
    rw [e1, Category.assoc, hδ1, ← Category.assoc, toUnit_unique (lift (𝟙 _) k ≫ toUnit _) (𝟙 _),
      Category.id_comp]
  have hδ2l : (G ◁ η[G]).left ≫ δ.left = (toUnit _ ≫ η[H]).left := by
    rw [← Over.comp_left, hδ2]
  change δ = 1
  rw [Hom.one_def]
  ext1
  have Himg : γ.left '' ((fst G G).left ⁻¹' {η[G].left point}) ⊆ {(lift η[G] η[H]).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints hne <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton];
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift η[G] η[H]).left.isClosedMap _ hpoint).preimage γ.left.continuous).isOpen_compl
      · exact (η[G].left.isClosedMap _ hpoint).preimage (fst G G).left.continuous
    obtain ⟨⟨c, hc⟩, e⟩ := (pointEquivClosedPoint (G ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c point = c₀ := congr(($e).1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (Over.homMk c hc ≫ snd G G)
    have : c ≫ pullback.fst G.hom G.hom = η[G].left :=
      ext_of_apply_closedPoint_eq G.hom (by simpa) (by simp) (by simpa)
    have H₁ : c = fc.left ≫ (η[G] ▷ G).left := by dsimp; ext <;> simp [fc, S, this]
    have H₂ : fc ≫ η[G] ▷ G ≫ γ = lift η[G] η[H] := by
      ext1 <;> simp [fc, γ, S, hδ1']
    exact hc₂ <| by simp [H₁, H₂, ← Scheme.Hom.comp_apply, Category.assoc, ← Over.comp_left]
  obtain ⟨U, hηU, HU⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    γ.left (fst G H).left (η[G].left point) (by
      rw [← Over.comp_left, show γ ≫ fst G H = fst G G from lift_fst _ _]
      exact (Set.finite_singleton _).subset Himg)
  simp only [Over.fst_left] at HU
  have Hfin (w : ↥(U : Scheme)) :
      ((pullback.fst G.hom H.hom) ⁻¹' {U.ι w} ∩ Set.range ⇑γ.left).Finite := by
    refine ((((γ.left.imageι ≫ pullback.fst G.hom H.hom) ∣_ U).finite_preimage_singleton w).image
      (Scheme.Opens.ι _ ≫ γ.left.imageι)).subset ?_
    have : U.ι ⁻¹' {U.ι w} = {w} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact U.ι.isOpenEmbedding.injective.eq_iff
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (pullback.fst G.hom H.hom),
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base]
    rintro z ⟨hz1, hz2⟩
    refine ⟨hz1, ?_⟩
    have hzr : z ∈ Set.range γ.left.imageι := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
        IsClosed.closure_eq (by exact γ.left.isClosedMap.isClosed_range)]
      exact hz2
    obtain ⟨t, rfl⟩ := hzr
    have hz1' : pullback.fst G.hom H.hom (γ.left.imageι t) = U.ι w := hz1
    obtain ⟨v, hv⟩ : t ∈ Set.range
        ((γ.left.imageι ≫ pullback.fst G.hom H.hom) ⁻¹ᵁ U).ι := by
      rw [Scheme.Opens.range_ι]
      show pullback.fst G.hom H.hom (γ.left.imageι t) ∈ U
      rw [hz1']
      exact (Scheme.Opens.range_ι U).subset ⟨w, rfl⟩
    exact ⟨v, by rw [← hv]; rfl⟩
  refine ext_of_apply_eq H.hom _
    ((fst G G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst G G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hηU⟩ (fst G G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst G G).left y} := by simpa using (fst G G).left.isClosedMap _ hy
    obtain ⟨w, hw⟩ : (fst G G).left y ∈ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hyU
    let x : 𝟙_ _ ⟶ G := Over.homMk (pointOfClosedPoint G.hom _ hx) (by simp)
    let ze : (G ⊗ G).left := (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[G]).left y
    let xe : (G ⊗ H).left := (fst G G ≫ (ρ_ _).inv ≫ G ◁ η[H]).left y
    have : γ.left y = xe := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst G G).left.continuous).isLocallyClosed ?_ γ.left.continuous
        γ.left.isClosedMap ((Hfin w).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp [hw, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, γ])) ?_ ?_
      · let α : G ⊗ G ⟶ G ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        simp [Set.range_comp, Scheme.Pullback.range_map, x]
      · exact ⟨y, subset_closure (by simp), rfl⟩
      · refine ⟨ze, subset_closure ?_, ?_⟩
        · simp [ze, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
        · have key : fst G G ≫ (ρ_ G).inv ≫ G ◁ η[G] ≫ γ = fst G G ≫ (ρ_ G).inv ≫ G ◁ η[H] := by
            ext1
            · simp [γ]
            · simp only [γ, Category.assoc, lift_snd, whiskerLeft_snd]
              rw [hδ2, toUnit_unique (toUnit _) (snd G (𝟙_ _))]
          simp only [ze, xe, ← Scheme.Hom.comp_apply, ← Over.comp_left, Category.assoc, key]
    convert congr((snd G H).left $this) using 1
    · simp [γ, ← Scheme.Hom.comp_apply]
    · simp [xe, ← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base]
  · simp

set_option backward.defeqAttrib.useBackward true in
/-- **Rigidity.** A morphism `f : G ⟶ H` of group schemes over a field with `G` proper and
geometrically integral and `H` proper, sending the identity to the identity, is multiplicative. -/
theorem homDefect_eq_one {G H : Over (Spec (.of K))} [IsProper G.hom] [GeometricallyIntegral G.hom]
    [GrpObj G] [IsProper H.hom] [GrpObj H] (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) :
    homDefect f = 1 := by
  let p := Spec.map (CommRingCat.ofHom <| algebraMap K (AlgebraicClosure K))
  let G' := (Over.pullback p).obj G
  let H' := (Over.pullback p).obj H
  have : IsProper G'.hom := by dsimp [G']; infer_instance
  have : IsIntegral (G' ⊗ G').left := by dsimp [G']; infer_instance
  have : IsProper H'.hom := by dsimp [H']; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  let : GrpObj H' := Functor.grpObjObj
  have hf' : η[G'] ≫ (Over.pullback p).map f = η[H'] := by
    simp only [G', H', Functor.obj.η_def, Category.assoc, ← Functor.map_comp, hf]
  have := homDefect_eq_one_of_isAlgClosed ((Over.pullback p).map f) hf'
  apply (Over.pullback p).map_injective
  rw [← cancel_epi (Functor.Monoidal.μIso (Over.pullback p) G G).hom]
  dsimp [homDefect] at this ⊢
  simpa only [Functor.map_mul, Functor.map_one, Functor.map_inv', comp_mul, GrpObj.comp_inv,
    comp_one, Functor.map_comp, Category.assoc, Functor.Monoidal.μ_fst_assoc,
    Functor.Monoidal.μ_snd_assoc] using this

/-- **Rigidity, `IsMonHom` form.** -/
theorem isMonHom_of_comp_eq {G H : Over (Spec (.of K))} [IsProper G.hom] [GeometricallyIntegral G.hom]
    [GrpObj G] [IsProper H.hom] [GrpObj H] (f : G ⟶ H) (hf : η[G] ≫ f = η[H]) : IsMonHom f where
  one_hom := hf
  mul_hom := by
    have := (homDefect_eq_one_iff f).1 (homDefect_eq_one f hf)
    rw [this, Hom.mul_def]
    congr 1

end ZInQ.Contrib.CloudB2Shimura.Dictionary
