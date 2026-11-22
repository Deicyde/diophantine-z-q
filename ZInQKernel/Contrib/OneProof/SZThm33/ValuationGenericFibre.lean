import ZInQKernel.Contrib.OneProof.SZThm33.GenericBaseChange
import ZInQKernel.Contrib.OneProof.DirectWeil.IdentityModelPolarization
import ZInQKernel.Contrib.OneProof.DirectWeil.FiniteWeilPairing

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue SmoothGroup SGA7PersistsNF PicDict
open Scheme.Modules
open scoped CategoryTheory.MonObj

namespace SZRaynaud.Ambient

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {K : Type} [Field K] {O : ValuationSubring K} {w : ValuationSubring (AlgebraicClosure K)}
  (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
  (A : PkgI3.AbVar K) (M : GroupModelO A O)

/-- The group over the ambient valuation ring obtained by base-changing the model. -/
abbrev valuationModel := (Over.pullback (base hw)).obj M.G

instance valuationModel_grp : GrpObj (valuationModel hw A M) := Functor.grpObjObj

instance valuationModel_comm : IsCommMonObj (valuationModel hw A M) := by
  let := ZInQ.FaltingsRestate.isCommMonObj_groupModelO M
  exact Functor.isCommMonObj_obj (F := Over.pullback (base hw))

private theorem gen_base_composite : (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) ≫ jO O = gen ≫ base hw := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- The actual generic fibre over the ambient ring is the specified
abelian variety over the canonical algebraic closure. -/
def valuationGenericIso : bcX A ≅ (Over.pullback (gen (w := w))).obj (valuationModel hw A M) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).mapIso M.gen.symm ≪≫
    isoX (pbCompIso (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (jO O) (gen ≫ base hw) (gen_base_composite hw) (Grp.mk M.G)) ≪≫
    (isoX (pbCompIso gen (base hw) (gen ≫ base hw) rfl (Grp.mk M.G))).symm

theorem valuationGenericIso_isMonHom :
    letI : GrpObj ((Over.pullback (gen (w := w))).obj (valuationModel hw A M)) := Functor.grpObjObj
    IsMonHom (valuationGenericIso hw A M).hom := by
  let : GrpObj ((Over.pullback (gen (w := w))).obj (valuationModel hw A M)) := Functor.grpObjObj
  let : GrpObj ((Over.pullback (jO O)).obj M.G) := Functor.grpObjObj
  let : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).obj ((Over.pullback (jO O)).obj M.G)) := Functor.grpObjObj
  let : GrpObj ((Over.pullback (gen ≫ base hw)).obj M.G) := Functor.grpObjObj
  have : IsMonHom M.gen.hom := M.gen_hom
  unfold valuationGenericIso
  change IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).map M.gen.inv ≫
    (isoX (pbCompIso (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (jO O) (gen ≫ base hw) (gen_base_composite hw) (Grp.mk M.G))).hom ≫
    (isoX (pbCompIso gen (base hw) (gen ≫ base hw) rfl (Grp.mk M.G))).inv)
  infer_instance

/-- The generic scheme maps into the ambient valuation model along its generic fibre. -/
def valuationGenericMap : (bcX A).left ⟶ (valuationModel hw A M).left :=
  (valuationGenericIso hw A M).hom.left ≫ pullback.fst (valuationModel hw A M).hom gen

theorem valuationGenericMap_base :
    valuationGenericMap hw A M ≫ (valuationModel hw A M).hom = (bcX A).hom ≫ gen := by
  rw [valuationGenericMap, Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ gen) (Over.w (valuationGenericIso hw A M).hom)

theorem valuationGenericMap_comp_model :
    valuationGenericMap hw A M ≫ pullback.fst M.G.hom (base hw) =
      pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) ≫ M.gen.inv.left ≫ pullback.fst M.G.hom (jO O) := by
  let p := (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))).map M.gen.inv
  let e₁ := isoX (pbCompIso (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (jO O) (gen ≫ base hw) (gen_base_composite hw) (Grp.mk M.G))
  let e₂ := isoX (pbCompIso gen (base hw) (gen ≫ base hw) rfl (Grp.mk M.G))
  have h₁ : e₁.hom.left ≫ pullback.fst M.G.hom (gen ≫ base hw) =
      pullback.fst (pullback.snd M.G.hom (jO O)) (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) ≫ pullback.fst M.G.hom (jO O) :=
    pbCompIso_fst (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (jO O) (gen ≫ base hw) (gen_base_composite hw) (Grp.mk M.G)
  have h₂ : e₂.inv.left ≫ pullback.fst (valuationModel hw A M).hom gen ≫
      pullback.fst M.G.hom (base hw) = pullback.fst M.G.hom (gen ≫ base hw) :=
    pbCompIso_inv_fst gen (base hw) (gen ≫ base hw) rfl (Grp.mk M.G)
  have hp : p.left ≫ pullback.fst ((Over.pullback (jO O)).obj M.G).hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) =
      pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) ≫ M.gen.inv.left := by
    simp only [p, Over.pullback_map_left, pullback.lift_fst]
  change (p.left ≫ e₁.hom.left ≫ e₂.inv.left) ≫ _ ≫ _ = _
  simp only [Category.assoc]
  rw [h₂, h₁, ← Category.assoc p.left]
  exact (congrArg (· ≫ pullback.fst M.G.hom (jO O)) hp).trans (Category.assoc _ _ _)

/-- The line restricted along the generic fibre agrees in Picard with the
base change of the line obtained through the model's chosen generic isomorphism. -/
theorem valuationGenericMap_modelLine (L : M.G.left.Modules) [SheafOfModules.IsInvertible L] :
    letI : SheafOfModules.IsInvertible (Relative.genericModelLine M L) := by
      unfold Relative.genericModelLine
      infer_instance
    Scheme.Pic.map (valuationGenericMap hw A M ≫ pullback.fst M.G.hom (base hw)) (Scheme.Pic.mk L) =
      bcPic A (Scheme.Pic.mk (Relative.genericModelLine M L)) := by
  simp only [valuationGenericMap_comp_model, bcPic, Relative.genericModelLine, ← Scheme.Pic.map_mk,
    Scheme.Pic.map_comp]
  rfl

/-- A model point over the valuation ring, considered as a section of the
group after base change to that ring. -/
def valuationSectionEquiv :
    (Over.mk (base hw) ⟶ M.G) ≃*
      (𝟙_ (Over (Spec (CommRingCat.of w))) ⟶ valuationModel hw A M) :=
  pullbackTestPointEquiv (base hw) (𝟙 _) (base hw) (Category.id_comp _) M.G

theorem valuationSectionEquiv_fst (x : Over.mk (base hw) ⟶ M.G) :
    (valuationSectionEquiv hw A M x).left ≫ pullback.fst M.G.hom (base hw) = x.left :=
  pullbackTestPointEquiv_fst (base hw) (𝟙 _) (base hw) (Category.id_comp _) M.G x

theorem genPtHom_inv_fst (x : Over.mk (gen ≫ base hw) ⟶ M.G) :
    (genPtHom hw A M x).left ≫ M.gen.inv.left ≫ pullback.fst M.G.hom (jO O) = x.left := by
  let y : PkgI3.AbVar.ptObj (AlgebraicClosure K) ⟶ (Over.pullback (jO O)).obj M.G :=
    pullbackTestPointEquiv (jO O) (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (gen ≫ base hw) (gen_base_composite hw) M.G x
  have hy : y.left ≫ pullback.fst M.G.hom (jO O) = x.left :=
    pullbackTestPointEquiv_fst (jO O) (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) (gen ≫ base hw) (gen_base_composite hw) M.G x
  have hgen := genPtHom_eq_of_projection hw A M x y hy
  rw [← hgen]
  calc
    _ = (y ≫ M.gen.hom ≫ M.gen.inv).left ≫ pullback.fst M.G.hom (jO O) := by
      simp only [Over.comp_left, Category.assoc]
    _ = _ := by rw [Iso.hom_inv_id, Category.comp_id, hy]

/-- Evaluation at the generic point of a valuation section is the
geometric point used in the Tate embedding. -/
theorem valuationGenericMap_point (x : Over.mk (base hw) ⟶ M.G) :
    (pts (genPtHom hw A M (restrictPoint gen x))).left ≫ valuationGenericMap hw A M =
      gen ≫ (valuationSectionEquiv hw A M x).left := by
  apply pullback.hom_ext
  · have h := pts_left_fst (genPtHom hw A M (restrictPoint gen x))
    simp only [Category.assoc, valuationGenericMap_comp_model, reassoc_of% h,
      genPtHom_inv_fst, valuationSectionEquiv_fst]
    rfl
  · have hl : (pts (genPtHom hw A M (restrictPoint gen x))).left ≫ (bcX A).hom = 𝟙 _ :=
      Over.w (pts (genPtHom hw A M (restrictPoint gen x)))
    have hr : (valuationSectionEquiv hw A M x).left ≫ (valuationModel hw A M).hom = 𝟙 _ :=
      Over.w (valuationSectionEquiv hw A M x)
    change (_ ≫ valuationGenericMap hw A M) ≫ (valuationModel hw A M).hom =
      gen ≫ (valuationSectionEquiv hw A M x).left ≫ (valuationModel hw A M).hom
    simp only [Category.assoc, valuationGenericMap_base, reassoc_of% hl, hr]
    exact (Category.comp_id (gen (w := w))).symm

end SZRaynaud.Ambient
