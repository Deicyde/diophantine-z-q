-- Adapted from AxiomMath/Mordell (https://github.com/AxiomMath/Mordell, commit 82a30cb7857f,
-- file Mordell/AbelianVariety/Rigidity.lean, theorem `Faltings.rigidity`), Apache-2.0; modified,
-- see the change notice below. That file carries no copyright line; its proof follows Mathlib's
-- `isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`
-- (Mathlib/AlgebraicGeometry/Group/Abelian.lean, Copyright (c) 2026 Andrew Yang, Authors: Andrew
-- Yang, Christian Merten, Apache-2.0).
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# The rigidity lemma for a family over a base of finite type

Let `K` be an algebraically closed field, `Y` a `K`-scheme locally of finite type with a `K`-point
`y₀`, `G` a proper `K`-scheme with a `K`-point `e` such that `Y ×_K G` is integral, and `H` a
separated `K`-scheme locally of finite type with a `K`-point `z`. A `K`-morphism
`F : Y ×_K G ⟶ H` with `F(y₀, g) = z` for all `g` and `F(y, e) = z` for all `y` is constant with
value `z` (Mumford, *Abelian varieties*, §4, Rigidity Lemma; Milne, *Abelian varieties*, Ch. I,
Thm. 1.1).

## Main result

* `ZInQ.Contrib.CloudW06PoincareRigidity.rigidity_family`.

## Provenance and change notice (Apache-2.0, §4(b))

The proof is adapted from `Faltings.rigidity` in `Mordell/AbelianVariety/Rigidity.lean` of
AxiomMath/Mordell (https://github.com/AxiomMath/Mordell, commit
`82a30cb7857f6e3cfdb1be91f5533c0ccb57d493`, Apache License 2.0), which in turn follows Mathlib's
`AlgebraicGeometry.isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`.
**Changes** (task cloud-w06, 2026-11-14): the statement is generalised from `F : G ⊗ G ⟶ G` for
one proper group scheme `G` to `F : Y ⊗ G ⟶ H` with three different schemes (`Y` only locally of
finite type, `H` only separated and locally of finite type, unit sections replaced by arbitrary
`K`-points); the proof is rewritten accordingly (the map `φ = (pr₁, F)` now goes to `Y ⊗ H`, the
closedness of the points uses `isClosedImmersion_of_comp_eq_id`, and the final value is `z`);
the declaration is renamed and moved to the namespace `ZInQ.Contrib.CloudW06PoincareRigidity`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory

universe u

namespace ZInQ.Contrib.CloudW06PoincareRigidity

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **The rigidity lemma for a family** (Mumford §4; Milne, *Abelian varieties*, Ch. I, Thm. 1.1,
with the parameter space `Y` only locally of finite type). Over an algebraically closed field `K`,
let `F : Y ⊗ G ⟶ H` be trivial (with value `z`) on `y₀ × G` and on `Y × e`, where `G` is proper,
`Y ⊗ G` is integral and `H` is separated and locally of finite type. Then `F` is constant with
value `z`. -/
theorem rigidity_family {K : Type u} [Field K] [IsAlgClosed K]
    (Y G H : Over (Spec (.of K))) [LocallyOfFiniteType Y.hom] [IsProper G.hom]
    [IsSeparated H.hom] [LocallyOfFiniteType H.hom] [IsIntegral (Y ⊗ G).left]
    (y₀ : 𝟙_ _ ⟶ Y) (e : 𝟙_ _ ⟶ G) (z : 𝟙_ _ ⟶ H) (F : Y ⊗ G ⟶ H)
    (h₁ : y₀ ▷ G ≫ F = toUnit _ ≫ z) (h₂ : Y ◁ e ≫ F = toUnit _ ≫ z) :
    F = toUnit _ ≫ z := by
  let S := Spec (.of K)
  let point : S := IsLocalRing.closedPoint K
  have hpoint : IsClosed {point} := isClosed_discrete _
  have : Nonempty G.left := ⟨e.left point⟩
  have : Nonempty (Spec (.of K)) := ⟨point⟩
  have : Nonempty (𝟙_ (Over (Spec (.of K)))).left := ⟨point⟩
  have : LocallyOfFiniteType G.hom := inferInstance
  have : LocallyOfFiniteType (Y ⊗ G).hom := by dsimp; infer_instance
  have : JacobsonSpace (Y ⊗ G).left := LocallyOfFiniteType.jacobsonSpace (Y := Spec _) (Y ⊗ G).hom
  have : Surjective G.hom := ⟨Function.surjective_to_subsingleton (α := G.left) (β := Spec _) _⟩
  have : IsProper (fst Y G).left := by dsimp; infer_instance
  have : Surjective (fst Y G).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (F.left ≫ H.hom) := by rw [Over.w]; infer_instance
  have : IsReduced (Y ⊗ G).left := inferInstance
  have : IsSeparated (fst Y H).left := by dsimp; infer_instance
  have : LocallyOfFiniteType (fst Y H).left := by dsimp; infer_instance
  have hy₀ : IsClosedImmersion y₀.left :=
    isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) Y.hom y₀.left (by simp)
  have hyz : IsClosedImmersion (lift y₀ z).left :=
    isClosedImmersion_of_comp_eq_id (Y := Spec (.of K)) (Y ⊗ H).hom (lift y₀ z).left (by simp)
  let φ : Y ⊗ G ⟶ Y ⊗ H := lift (fst _ _) F
  have : IsProper (φ.left ≫ (fst Y H).left) := by
    simpa only [Over.tensorObj_left, Over.lift_left, Over.fst_left, limit.lift_π,
      PullbackCone.mk_pt, PullbackCone.mk_π_app, Over.tensorUnit_left, φ]
  have : IsProper φ.left := .of_comp _ (fst Y H).left
  ext1
  -- The fibre `y₀ × G` is contracted by `φ = (pr₁, F)` to the point `(y₀, z)`.
  have hcontr : φ.left '' ((fst Y G).left ⁻¹' {y₀.left point}) ⊆ {(lift y₀ z).left point} := by
    rw [Set.image_subset_iff, ← Set.sdiff_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hne
    obtain ⟨c₀, ⟨hc₁, hc₂⟩, hc₃⟩ := nonempty_inter_closedPoints hne <| by
      rw [Set.sdiff_eq_compl_inter, ← Set.image_singleton, ← Set.image_singleton]
      refine (IsOpen.isLocallyClosed ?_).inter (IsClosed.isLocallyClosed ?_)
      · exact (((lift y₀ z).left.isClosedMap _ hpoint).preimage φ.left.continuous).isOpen_compl
      · exact (y₀.left.isClosedMap _ hpoint).preimage (fst Y G).left.continuous
    obtain ⟨⟨c, hc⟩, e'⟩ := (pointEquivClosedPoint (Y ⊗ G).hom).surjective ⟨c₀, hc₃⟩
    obtain rfl : c point = c₀ := congr(($e').1)
    let fc : 𝟙_ (Over S) ⟶ 𝟙_ (Over S) ⊗ G := lift (𝟙 _) (Over.homMk c hc ≫ snd Y G)
    have hcY : c ≫ pullback.fst Y.hom G.hom = y₀.left :=
      ext_of_apply_closedPoint_eq Y.hom
        (by simpa only [Over.tensorObj_left, Over.tensorObj_hom, Category.assoc] using hc)
        (by simp only [Over.w, Over.tensorUnit_hom])
        (by rw [Scheme.Hom.comp_apply]; exact hc₁)
    have H₁ : c = fc.left ≫ (y₀ ▷ G).left := by
      dsimp
      ext
      · simp only [hcY, Over.lift_left, Over.tensorUnit_left, Over.tensorUnit_hom, Over.id_left,
          Over.comp_left, Over.tensorObj_left, Over.homMk_left, Over.snd_left, Category.assoc,
          Over.whiskerRight_left_fst, limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left,
          PullbackCone.mk_π_app, Category.id_comp, S, fc]
      · simp only [Over.lift_left, Over.tensorUnit_left, Over.tensorUnit_hom, Over.id_left,
          Over.comp_left, Over.tensorObj_left, Over.homMk_left, Over.snd_left, Category.assoc,
          Over.whiskerRight_left_snd, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
          S, fc]
    have H₂ : fc ≫ y₀ ▷ G ≫ φ = lift y₀ z := by
      ext1
      · simp only [comp_lift, whiskerRight_fst, lift_fst_assoc, Category.id_comp,
          lift_whiskerRight_assoc, lift_fst, S, fc, φ]
      · simp only [φ, Category.assoc, lift_snd]
        rw [h₁, ← Category.assoc, toUnit_unique (fc ≫ toUnit _) (𝟙 _), Category.id_comp]
    exact hc₂ <| by simp only [Over.tensorObj_left, Over.tensorUnit_left, Over.lift_left, H₁,
      Over.tensorUnit_hom, ← Over.comp_left, Set.mem_preimage, ← Scheme.Hom.comp_apply,
      Category.assoc, H₂, Set.mem_singleton_iff]
  -- Zariski's main theorem: over a neighbourhood `U` of `y₀`, `φ` has finite fibres.
  obtain ⟨U, hy₀U, hU⟩ := exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    φ.left (fst Y H).left (y₀.left point) (by
      dsimp [-Scheme.Hom.comp_base, φ]
      simp only [pullback.lift_fst]
      exact (Set.finite_singleton _).subset hcontr)
  have hfib (x : U) : ((pullback.fst Y.hom H.hom) ⁻¹' {x.1} ∩ Set.range ⇑φ.left).Finite := by
    refine ((((φ.left.imageι ≫ (fst Y H).left) ∣_ U).finite_preimage_singleton x).image
      (Scheme.Opens.ι _ ≫ φ.left.imageι)).subset ?_
    have : U.ι ⁻¹' {x.1} = {x} := by
      ext
      simp only [Set.mem_preimage, Scheme.Opens.ι_apply, Set.mem_singleton_iff, SetLike.coe_eq_coe]
    rw [← this, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base,
      morphismRestrict_ι, ← Category.assoc, Scheme.Hom.comp_base (_ ≫ _) (fst Y H).left,
      TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    dsimp
    rw [Set.image_preimage_eq_inter_range, Scheme.IdealSheafData.range_subschemeι,
      Scheme.Hom.support_ker, ← Set.inter_assoc, ← Set.preimage_inter,
      Set.singleton_inter_of_mem x.2, IsClosed.closure_eq
      (by exact φ.left.isClosedMap.isClosed_range)]
  -- It suffices to compare `F` with the constant map at the closed points over `U`.
  refine ext_of_apply_eq H.hom _
    ((fst Y G).left ⁻¹ᵁ U).isOpen.isLocallyClosed
    (((fst Y G).left ⁻¹ᵁ U).isOpen.dense ?_) ?_ ?_
  · exact .preimage ⟨_, hy₀U⟩ (fst Y G).left.surjective
  · intro y hyU hy
    have hx : IsClosed {(fst Y G).left y} := by
      simpa only [Over.tensorObj_left, Over.fst_left, Set.image_singleton] using
        (fst Y G).left.isClosedMap _ hy
    let x : 𝟙_ _ ⟶ Y := Over.homMk (pointOfClosedPoint Y.hom _ hx) (by
      simp only [Over.tensorUnit_left, Over.tensorObj_left, Over.fst_left, pointOfClosedPoint_comp,
        Over.tensorUnit_hom])
    let xe : (Y ⊗ G).left := (fst Y G ≫ (ρ_ _).inv ≫ Y ◁ e).left y
    let xz : (Y ⊗ H).left := (fst Y G ≫ (ρ_ _).inv ≫ Y ◁ z).left y
    have hφe : (fst Y G ≫ (ρ_ Y).inv ≫ Y ◁ e) ≫ φ = fst Y G ≫ (ρ_ Y).inv ≫ Y ◁ z := by
      ext1
      · simp only [φ, Category.assoc, lift_fst, whiskerLeft_fst]
      · simp only [φ, Category.assoc, lift_snd, whiskerLeft_snd]
        rw [h₂, toUnit_unique (toUnit (Y ⊗ 𝟙_ _)) (snd Y (𝟙_ _))]
    have : φ.left y = xz := by
      refine subsingleton_image_closure_of_finite_of_isPreirreducible
        (hx.preimage (fst Y G).left.continuous).isLocallyClosed ?_ φ.left.continuous
        φ.left.isClosedMap ((hfib ⟨_, hyU⟩).subset (Set.image_subset_iff.mpr fun _ ↦ by
          simp only [Over.tensorObj_left, Over.fst_left, Set.mem_preimage, Set.mem_singleton_iff,
            Over.lift_left, Set.preimage_inter, Set.preimage_range, Set.inter_univ,
            ← Scheme.Hom.comp_apply, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
            imp_self, φ])) ?_ ?_
      · let α : Y ⊗ G ⟶ Y ⊗ G := toUnit _ ≫ x ⊗ₘ 𝟙 _
        convert!
          ((IrreducibleSpace.isIrreducible_univ _).image α.left
              α.left.continuous.continuousOn).isPreirreducible
        rw [Over.tensorHom_left]
        have hr1 : Set.range (toUnit Y ≫ x).left = {(fst Y G).left y} := by
          ext p
          constructor
          · rintro ⟨q, rfl⟩
            rw [Over.comp_left, Over.toUnit_left, Scheme.Hom.comp_apply]
            exact pointOfClosedPoint_apply Y.hom _ hx _
          · intro hp
            refine ⟨(fst Y G).left y, ?_⟩
            rw [hp, Over.comp_left, Over.toUnit_left, Scheme.Hom.comp_apply]
            exact pointOfClosedPoint_apply Y.hom _ hx _
        have hr2 : Set.range (Over.Hom.left (𝟙 G)) = Set.univ :=
          Set.eq_univ_of_forall fun p => ⟨p, by rw [Over.id_left]; rfl⟩
        rw [Set.image_univ]
        refine Eq.trans ?_ (Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _).symm
        rw [hr1, hr2, Set.preimage_univ, Set.inter_univ, Over.fst_left]
        rfl
      · exact ⟨y, subset_closure (by simp only [Over.tensorObj_left, Over.fst_left,
          Set.mem_preimage, Set.mem_singleton_iff]), rfl⟩
      · refine ⟨xe, subset_closure ?_, ?_⟩
        · simp only [Over.tensorObj_left, Over.fst_left, Over.comp_left, Over.tensorUnit_left,
            Over.tensorUnit_hom, Set.mem_preimage, ← Scheme.Hom.comp_apply, Category.assoc,
            Over.whiskerLeft_left_fst, Over.rightUnitor_inv_left_fst, Category.comp_id,
            Set.mem_singleton_iff, xe]
        · change φ.left ((fst Y G ≫ (ρ_ Y).inv ≫ Y ◁ e).left y) =
            (fst Y G ≫ (ρ_ Y).inv ≫ Y ◁ z).left y
          rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφe]
    have h3 := congrArg (snd Y H).left this
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd] at h3
    rw [h3]
    have e3 : (fst Y G ≫ (ρ_ Y).inv ≫ Y ◁ z) ≫ snd Y H = toUnit _ ≫ z := by
      rw [Category.assoc, Category.assoc, whiskerLeft_snd, ← Category.assoc, ← Category.assoc,
        toUnit_unique ((fst Y G ≫ (ρ_ Y).inv) ≫ snd Y (𝟙_ _)) (toUnit _)]
    change (snd Y H).left ((fst Y G ≫ (ρ_ Y).inv ≫ Y ◁ z).left y) = _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, e3]
  · simp only [Over.tensorObj_left, Over.w, Over.tensorObj_hom, Over.comp_left,
      Over.tensorUnit_left, Over.toUnit_left, Category.assoc, Over.tensorUnit_hom,
      Category.comp_id]

end ZInQ.Contrib.CloudW06PoincareRigidity
