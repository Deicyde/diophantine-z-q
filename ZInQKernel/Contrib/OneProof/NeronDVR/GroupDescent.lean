import ZInQKernel.Contrib.OneProof.NeronDVR.DescentDatum
import ZInQKernel.Contrib.HeightBC.H5GlueMinimal
import ZInQKernel.Contrib.HeightBC.H5GlueReduction
import ZInQKernel.Contrib.NeronC.NeronGroup
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Comma.Over.Pullback

/-!
# Group compatibility of the Néron descent datum

The transport extends the generic identification of the two groups over the overlap.
The Néron uniqueness property on the smooth domains of the group operations
implies that transport preserves the group law.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

namespace NeronDVR

open ZInQ.H5Glue (genBC genBC_isMonHom pbCompHom pbCompInv pbEqIso)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Comparison

variable {S S' T T' B Bη : Scheme.{0}}
  {p : S' ⟶ S} (N : Over S') (a b : B ⟶ S')

private abbrev V (a : B ⟶ S') := (Over.pullback a).obj N

private def firstPoint : Over.mk ((V N a).hom ≫ a) ⟶ N :=
  Over.homMk (pullback.fst N.hom a) pullback.condition

variable (d : Over.DescentDatum p N) (hab : a ≫ p = b ≫ p)

include hab in
private theorem overlap_equal : ((V N a).hom ≫ a) ≫ p = ((V N a).hom ≫ b) ≫ p := by
  simp [Category.assoc, hab]

/-- The map between the two pullbacks corresponding to transport in a descent datum. -/
def transportHom : (Over.pullback a).obj N ⟶ (Over.pullback b).obj N :=
  let y := d.transport ((V N a).hom ≫ a) ((V N a).hom ≫ b)
    (overlap_equal N a b hab) (firstPoint N a)
  Over.homMk (pullback.lift y.left (V N a).hom (Over.w y)) (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
private theorem transportHom_fst :
    (transportHom N a b d hab).left ≫ pullback.fst N.hom b =
      (d.transport ((V N a).hom ≫ a) ((V N a).hom ≫ b)
        (overlap_equal N a b hab) (firstPoint N a)).left :=
  pullback.lift_fst _ _ _

private theorem transportHom_self :
    transportHom N a a d rfl = 𝟙 ((Over.pullback a).obj N) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [transportHom_fst, d.transport_self]
    simp [firstPoint]
  · exact (Over.w _).trans (Over.w _).symm

private theorem transportHom_comp (c : B ⟶ S') (hbc : b ≫ p = c ≫ p) :
    transportHom N a b d hab ≫ transportHom N b c d hbc =
      transportHom N a c d (hab.trans hbc) := by
  let f := transportHom N a b d hab
  let a₀ := (V N a).hom ≫ a
  let b₀ := (V N a).hom ≫ b
  let c₀ := (V N a).hom ≫ c
  let b₁ := (V N b).hom ≫ b
  let c₁ := (V N b).hom ≫ c
  have hab₀ : a₀ ≫ p = b₀ ≫ p := overlap_equal N a b hab
  have hbc₀ : b₀ ≫ p = c₀ ≫ p := by simp [b₀, c₀, Category.assoc, hbc]
  have hbc₁ : b₁ ≫ p = c₁ ≫ p := overlap_equal N b c hbc
  let y := d.transport a₀ b₀ hab₀ (firstPoint N a)
  let z := (Over.homMk f.left : Over.mk (f.left ≫ b₁) ⟶ Over.mk b₁) ≫ firstPoint N b
  have hz : z.left = y.left := transportHom_fst N a b d hab
  have hb : f.left ≫ b₁ = b₀ := by
    change f.left ≫ (V N b).hom ≫ b = _
    rw [← Category.assoc, Over.w f]
  have hc : f.left ≫ c₁ = c₀ := by
    change f.left ≫ (V N b).hom ≫ c = _
    rw [← Category.assoc, Over.w f]
  have hnat := congrArg CommaMorphism.left
    (d.transport_homMk_comp f.left b₁ c₁ hbc₁ (firstPoint N b))
  have hbc' : (f.left ≫ b₁) ≫ p = (f.left ≫ c₁) ≫ p := by rw [hb, hc, hbc₀]
  have hcongr := d.transport_left_congr hbc' hbc₀ z y hb hc hz
  have hcoc := congrArg CommaMorphism.left (d.transport_transport a₀ b₀ c₀ hab₀ hbc₀
    (firstPoint N a))
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [Over.comp_left, Category.assoc, transportHom_fst, transportHom_fst]
    exact hnat.symm.trans (hcongr.trans hcoc)
  · exact (Over.w _).trans (Over.w _).symm

/-- The isomorphism between the two pullbacks represented by a descent datum. -/
def transportIso : (Over.pullback a).obj N ≅ (Over.pullback b).obj N where
  hom := transportHom N a b d hab
  inv := transportHom N b a d hab.symm
  hom_inv_id := (transportHom_comp N a b d hab a hab.symm).trans (transportHom_self N a d)
  inv_hom_id := (transportHom_comp N b a d hab.symm b hab).trans (transportHom_self N b d)

private theorem pbCompInv_fst {P Q R : Scheme.{0}} (f : P ⟶ Q) (g : Q ⟶ R) (X : Over R) :
    (pbCompInv f g X).left ≫ pullback.fst X.hom (f ≫ g) =
      pullback.fst (pullback.snd X.hom g) f ≫ pullback.fst X.hom g := by
  let I := (Over.pullbackComp f g).app X
  change I.inv.left ≫ pullback.fst X.hom (f ≫ g) = _
  rw [← Over.pullbackComp_hom_app_left_fst_fst f g X]
  exact Over.inv_left_hom_left_assoc I _

@[reassoc (attr := simp)]
private theorem pbEqIso_fst {P Q : Scheme.{0}} {f g : P ⟶ Q} (h : f = g) (X : Over Q) :
    (pbEqIso h X).hom.left ≫ pullback.fst X.hom g = pullback.fst X.hom f := by
  subst h
  change 𝟙 _ ≫ _ = _
  simp

variable (j : T ⟶ S) (j' : T' ⟶ S') (t : T' ⟶ T)
  (hpb : IsPullback j' t p j)
  {A : Over T} (e : (Over.pullback j').obj N ≅ (Over.pullback t).obj A)
  (i : Bη ⟶ B) (m₁ m₂ : Bη ⟶ T') (u : Bη ⟶ T)
  (ha : i ≫ a = m₁ ≫ j') (hb : i ≫ b = m₂ ≫ j')
  (hu₁ : m₁ ≫ t = u) (hu₂ : m₂ ≫ t = u)

private abbrev W (a : B ⟶ S') := (Over.pullback i).obj (V N a)

private def pointToGeneric (m : Bη ⟶ T') (hw : i ≫ a = m ≫ j') :
    (W N i a).left ⟶ ((Over.pullback j').obj N).left :=
  pullback.lift (pullback.fst (V N a).hom i ≫ pullback.fst N.hom a)
    ((W N i a).hom ≫ m) (by
      rw [Category.assoc, pullback.condition (f := N.hom) (g := a), ← Category.assoc]
      change (pullback.fst (V N a).hom i ≫ (V N a).hom) ≫ a = _
      rw [pullback.condition, Category.assoc, hw, ← Category.assoc]
      rfl)

private theorem genBC_fst (m : Bη ⟶ T') (hw : i ≫ a = m ≫ j') (hu : m ≫ t = u) :
    (genBC i a m j' t u hw hu N A e).hom.left ≫ pullback.fst A.hom u =
      pointToGeneric N a j' i m hw ≫ e.hom.left ≫ pullback.fst A.hom t := by
  have hfirst :
      (pbCompInv i a N ≫ (pbEqIso hw N).hom ≫ pbCompHom m j' N).left ≫
          pullback.fst (pullback.snd N.hom j') m = pointToGeneric N a j' i m hw := by
    let f := pbCompInv i a N ≫ (pbEqIso hw N).hom ≫ pbCompHom m j' N
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, pbCompHom,
        Over.pullbackComp_hom_app_left_fst_fst, pbEqIso_fst, pbCompInv_fst,
        pointToGeneric, pullback.lift_fst]
      rfl
    · have hf : f.left ≫ pullback.snd (pullback.snd N.hom j') m = (W N i a).hom := Over.w f
      change f.left ≫ pullback.fst (pullback.snd N.hom j') m ≫ pullback.snd N.hom j' = _
      rw [pullback.condition, ← Category.assoc, hf]
      exact (pullback.lift_snd _ _ _).symm
  have hmap : ((Over.pullback m).map e.hom).left ≫ pullback.fst (pullback.snd A.hom t) m =
      pullback.fst (pullback.snd N.hom j') m ≫ e.hom.left := pullback.lift_fst _ _ _
  change (pbCompInv i a N ≫ (pbEqIso hw N).hom ≫ pbCompHom m j' N ≫
    (Over.pullback m).map e.hom ≫ pbCompInv m t A ≫ (pbEqIso hu A).hom).left ≫
    pullback.fst A.hom u = _
  simp only [Over.comp_left, Category.assoc, pbEqIso_fst, pbCompInv_fst, reassoc_of% hmap]
  rw [← hfirst]
  simp only [Over.comp_left, Category.assoc]

variable [Smooth N.hom] [Smooth p]
  (hex : ∀ (Y : Over S') [Smooth Y.hom],
    Function.Bijective (fun f : Y ⟶ N => (Over.pullback j').map f))

/-- Over the generic overlap the transport map is the canonical comparison of
the two pullbacks of the prescribed generic fibre. -/
theorem neronDescentDatum_transportHom_generic :
    (Over.pullback i).map (transportHom N a b (neronDescentDatum j p N j' t hpb e hex) hab) ≫
        (genBC i b m₂ j' t u hb hu₂ N A e).hom =
      (genBC i a m₁ j' t u ha hu₁ N A e).hom := by
  let d := neronDescentDatum j p N j' t hpb e hex
  let f := transportHom N a b d hab
  let fη := (Over.pullback i).map f
  let q := pullback.fst (V N a).hom i
  let qη := (W N i a).hom
  let α := q ≫ ((V N a).hom ≫ a)
  let β := q ≫ ((V N a).hom ≫ b)
  have hαβ : α ≫ p = β ≫ p := by simp [α, β, Category.assoc, hab]
  let x : Over.mk α ⟶ N :=
    (Over.homMk q : Over.mk α ⟶ Over.mk ((V N a).hom ≫ a)) ≫ firstPoint N a
  let y := d.transport α β hαβ x
  have hy : y.left = q ≫
      (d.transport ((V N a).hom ≫ a) ((V N a).hom ≫ b)
        (overlap_equal N a b hab) (firstPoint N a)).left :=
    congrArg CommaMorphism.left (d.transport_homMk_comp q _ _ _ (firstPoint N a))
  have hα : α = (qη ≫ m₁) ≫ j' := by
    change q ≫ (V N a).hom ≫ a = _
    rw [← Category.assoc q, pullback.condition, Category.assoc, ha, Category.assoc]
    rfl
  have hβ : β = (qη ≫ m₂) ≫ j' := by
    change q ≫ (V N a).hom ≫ b = _
    rw [← Category.assoc q, pullback.condition, Category.assoc, hb, Category.assoc]
    rfl
  have hu : (qη ≫ m₁) ≫ t = (qη ≫ m₂) ≫ t := by
    simp [Category.assoc, hu₁, hu₂]
  have heq := neronDescentDatum_transport_generic_point j p N j' t hpb e hex
    α β hαβ x (qη ≫ m₁) (qη ≫ m₂) hα hβ hu
  have h₁ : pointToGeneric N a j' i m₁ ha =
      pullback.lift x.left (qη ≫ m₁) ((Over.w x).trans hα) := rfl
  have h₂ : fη.left ≫ pointToGeneric N b j' i m₂ hb =
      pullback.lift y.left (qη ≫ m₂) ((Over.w y).trans hβ) := by
    apply pullback.hom_ext
    · simp [fη, f, q, pointToGeneric, Over.pullback_map_left, Category.assoc, hy]
    · have hfη : fη.left ≫ (W N i b).hom = qη := Over.w fη
      simp only [pointToGeneric, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hfη]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (fη ≫ (genBC i b m₂ j' t u hb hu₂ N A e).hom).left ≫ pullback.fst A.hom u = _
    rw [Over.comp_left, Category.assoc, genBC_fst, genBC_fst, h₁,
      ← Category.assoc fη.left, h₂]
    exact heq
  · exact (Over.w _).trans (Over.w _).symm

include ha hb hu₁ hu₂ in
/-- The two pullbacks of a smooth separated Néron group over an overlap are compared
by a group homomorphism. Over the generic overlap, this is the comparison through the
prescribed generic group. -/
theorem neronDescentDatum_transportHom_isMonHom [GrpObj N] [GrpObj A] [IsSeparated N.hom]
    [IsSchemeTheoreticallyDominant i] [QuasiCompact i]
    (he : letI : GrpObj ((Over.pullback j').obj N) := Functor.grpObjObj
      letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj
      IsMonHom e.hom) :
    letI : GrpObj ((Over.pullback a).obj N) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback b).obj N) := Functor.grpObjObj
    IsMonHom (transportHom N a b (neronDescentDatum j p N j' t hpb e hex) hab) := by
  let : GrpObj (V N a) := Functor.grpObjObj
  let : GrpObj (V N b) := Functor.grpObjObj
  let : GrpObj (W N i a) := Functor.grpObjObj
  let : GrpObj (W N i b) := Functor.grpObjObj
  let : GrpObj ((Over.pullback u).obj A) := Functor.grpObjObj
  let f := transportHom N a b (neronDescentDatum j p N j' t hpb e hex) hab
  let ga := genBC i a m₁ j' t u ha hu₁ N A e
  let gb := genBC i b m₂ j' t u hb hu₂ N A e
  have : IsMonHom ga.hom := genBC_isMonHom i a m₁ j' t u ha hu₁ N A e he
  have : IsMonHom gb.hom := genBC_isMonHom i b m₂ j' t u hb hu₂ N A e he
  have hF : (Over.pullback i).map f = ga.hom ≫ gb.inv :=
    gb.eq_comp_inv.mpr
      (neronDescentDatum_transportHom_generic N a b hab j j' t hpb e i m₁ m₂ u ha hb hu₁ hu₂ hex)
  have : IsMonHom ((Over.pullback i).map f) := by rw [hF]; infer_instance
  have hXa : Smooth (V N a).hom := show Smooth (pullback.snd N.hom a) from inferInstance
  have : IsSeparated (V N b).hom := show IsSeparated (pullback.snd N.hom b) from inferInstance
  have : Smooth (𝟙_ (Over B)).hom := ZInQ.Contrib.NeronC.smooth_tensorUnit B
  have : Smooth (V N a ⊗ V N a).hom := ZInQ.Contrib.NeronC.smooth_tensor _ _ hXa hXa
  exact ZInQ.H5Glue.isMonHom_of_map (Over.pullback i) f
    (ZInQ.Contrib.NeronC.pullback_map_injective i _ _)
    (ZInQ.Contrib.NeronC.pullback_map_injective i _ _)

end Comparison

/-- The canonical Néron descent datum is compatible with the group law on the
double overlap. -/
theorem neronDescentDatum_groupCompatible {S S' T T' : Scheme.{0}}
    (j : T ⟶ S) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (p : S' ⟶ S) [Smooth p] (j' : T' ⟶ S') (t : T' ⟶ T)
    (hpb : IsPullback j' t p j)
    (N : Over S') [Smooth N.hom] [IsSeparated N.hom] [GrpObj N]
    {A : Over T} [GrpObj A] (e : (Over.pullback j').obj N ≅ (Over.pullback t).obj A)
    (he : letI : GrpObj ((Over.pullback j').obj N) := Functor.grpObjObj
      letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj
      IsMonHom e.hom)
    (hex : ∀ (Y : Over S') [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback j').map f)) :
    letI : GrpObj ((Over.pullback (pullback.fst p p)).obj N) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback (pullback.snd p p)).obj N) := Functor.grpObjObj
    IsMonHom (transportHom N (pullback.fst p p) (pullback.snd p p)
      (neronDescentDatum j p N j' t hpb e hex) pullback.condition) := by
  let a := pullback.fst p p
  let b := pullback.snd p p
  have hab : a ≫ p = b ≫ p := pullback.condition
  let i := pullback.fst (a ≫ p) j
  let u := pullback.snd (a ≫ p) j
  have h₁ : (i ≫ a) ≫ p = u ≫ j := (Category.assoc _ _ _).trans pullback.condition
  have h₂ : (i ≫ b) ≫ p = u ≫ j := by
    rw [Category.assoc, ← hab]
    exact pullback.condition
  let m₁ := hpb.lift (i ≫ a) u h₁
  let m₂ := hpb.lift (i ≫ b) u h₂
  have ha : i ≫ a = m₁ ≫ j' := (hpb.lift_fst _ _ _).symm
  have hb : i ≫ b = m₂ ≫ j' := (hpb.lift_fst _ _ _).symm
  have hu₁ : m₁ ≫ t = u := hpb.lift_snd _ _ _
  have hu₂ : m₂ ≫ t = u := hpb.lift_snd _ _ _
  have : Smooth a := show Smooth (pullback.fst p p) from inferInstance
  have : IsSchemeTheoreticallyDominant i :=
    show IsSchemeTheoreticallyDominant (pullback.fst (a ≫ p) j) from inferInstance
  have : QuasiCompact i := show QuasiCompact (pullback.fst (a ≫ p) j) from inferInstance
  exact neronDescentDatum_transportHom_isMonHom N a b hab j j' t hpb e
    i m₁ m₂ u ha hb hu₁ hu₂ hex he

end

end NeronDVR
