import ZInQKernel.Contrib.MulEtale.Direct.AllBase

/-! Prime-to-residue-characteristic multiplication for smooth commutative groups. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace SmoothGroup

open H101DirectFieldRoute.Translation
open ZInQ.Contrib.MulEtale.FibreMaps
open H101DirectFieldRoute.FibreMultiplication
open H101DirectGlobalDetection.CanonicalFibres

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem etale_pow_of_unit_nbhd {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (m : ℕ) (s : Spec (.of k))
    (H : ∃ V : G.left.Opens, IsAffineOpen V ∧ η[G].left s ∈ V ∧
      Etale (V.ι ≫ (𝟙 G ^ m : G ⟶ G).left)) :
    Etale ((𝟙 G ^ m : G ⟶ G).left) := by
  obtain ⟨V, -, hsV, hV⟩ := H
  let Ω : Type u := AlgebraicClosure k
  let g : Spec (.of Ω) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom <| algebraMap k Ω)
  let G' : Over (Spec (.of Ω)) := (Over.pullback g).obj G
  let : GrpObj G' := Functor.grpObjObj
  have : Smooth G'.hom := by dsimp [G']; infer_instance
  have : IsCommMonObj G' := (Over.pullback g).isCommMonObj_obj
  have hpow : (Over.pullback g).map (𝟙 G ^ m) = (𝟙 G' ^ m : G' ⟶ G') := by
    have h : (Over.pullback g).map (𝟙 G ^ m) = ((Over.pullback g).map (𝟙 G)) ^ m :=
      map_pow ((Over.pullback g).homMonoidHom (X := G) (M := G)) (𝟙 G) m
    rw [CategoryTheory.Functor.map_id] at h
    exact h
  have sq := isPullback_overPullback_map_left g (𝟙 G ^ m)
  have hV' : Etale ((pullback.fst G.hom g ⁻¹ᵁ V).ι ≫ (𝟙 G' ^ m : G' ⟶ G').left) := by
    have big := ((isPullback_morphismRestrict (pullback.fst G.hom g) V).flip.paste_horiz
      sq.flip).flip
    rw [← hpow]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) big hV
  let z : (𝟙_ (Over (Spec (.of Ω)))).left := IsLocalRing.closedPoint Ω
  have he' : η[G'].left z ∈ pullback.fst G.hom g ⁻¹ᵁ V := by
    rw [Scheme.Hom.mem_preimage]
    have hl : ((Over.pullback g).map η[G]).left ≫ pullback.fst G.hom g =
        pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g ≫ η[G].left :=
      pullback.lift_fst _ _ _
    have h1 : η[G'].left ≫ pullback.fst G.hom g =
        (Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g ≫ η[G].left := by
      change (Functor.LaxMonoidal.ε (Over.pullback g) ≫ (Over.pullback g).map η[G]).left ≫
        pullback.fst G.hom g = _
      rw [Over.comp_left, Category.assoc, hl]
    have h2 : (η[G'].left ≫ pullback.fst G.hom g) z =
        ((Functor.LaxMonoidal.ε (Over.pullback g)).left ≫
          pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g ≫ η[G].left) z := by
      rw [h1]
    simp only [Scheme.Hom.comp_apply] at h2
    have hz : pullback.fst (𝟙_ (Over (Spec (.of k)))).hom g
        ((Functor.LaxMonoidal.ε (Over.pullback g)).left z) = s :=
      Subsingleton.elim (α := Spec (.of k)) _ _
    have h3 : pullback.fst G.hom g (η[G'].left z) = η[G].left s :=
      h2.trans (congrArg (fun p ↦ η[G].left p) hz)
    exact (congrArg (fun y ↦ y ∈ V) h3).mpr hsV
  have hG' : Etale (𝟙 G' ^ m : G' ⟶ G').left :=
    etale_pow_id_left_of_isAlgClosed G' m z _ he' hV'
  rw [← hpow] at hG'
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hG'

theorem field_etale_pow {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (m : ℕ) (hm : IsUnit (m : k)) :
    Etale ((𝟙 G ^ m : G ⟶ G).left) :=
  etale_pow_of_unit_nbhd G m (IsLocalRing.closedPoint k)
    (H101DirectFieldRoute.LocalPromotion.exists_etale_open_mul_at_unit_of_isUnit
      k G m hm (IsLocalRing.closedPoint k))

/-- Multiplication on a smooth commutative group scheme is étale when the
multiplier is invertible on the affine base. -/
theorem etale_pow {O : Type} [CommRing O]
    (G : Over (Spec (.of O))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (m : ℕ) (hm : IsUnit (m : O)) : Etale ((𝟙 G ^ m : G ⟶ G).left) := by
  let A : Grp (Over (Spec (.of O))) := Grp.mk G
  have hsmooth : Smooth ((𝟙 G ^ m : G ⟶ G).left ≫ G.hom) := by
    rw [Over.w]
    infer_instance
  apply H101DirectGlobalDetection.etale_of_smooth_structural_and_etale_fibers
    (𝟙 G ^ m : G ⟶ G).left G.hom
  intro s
  change Etale (fiberHom (𝟙 A.X ^ m : A.X ⟶ A.X).left A.X.hom s)
  rw [fiberHom_pow_eq]
  let : GrpObj (fibreGrp A s).X := (fibreGrp A s).grp
  have hSmooth : Smooth (fibreGrp A s).X.hom := by
    change Smooth (pullback.snd G.hom ((Spec (.of O)).fromSpecResidueField s))
    infer_instance
  have hComm : IsCommMonObj (fibreGrp A s).X :=
    (Over.pullback ((Spec (.of O)).fromSpecResidueField s)).isCommMonObj_obj
  have hPower : Etale ((𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left) :=
    @field_etale_pow _ _ (fibreGrp A s).X (fibreGrp A s).grp hComm hSmooth m
      (isUnit_residue_natCast s m hm)
  let power := (𝟙 (fibreGrp A s).X ^ m : (fibreGrp A s).X ⟶ (fibreGrp A s).X).left
  have : Etale power := hPower
  exact Etale.etale_comp (fibreMulDomainIso A s m).hom power

end SmoothGroup
