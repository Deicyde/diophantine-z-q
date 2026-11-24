import ZInQKernel.Contrib.OneProof.SZThm33.PullbackTate
import ZInQKernel.Contrib.OneProof.SZThm33.ModelTateEmbedding
import ZInQKernel.Contrib.OneProof.SGA7PersistsNF

/-!
# Generic points of a base-changed group model over a shared closure
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue SmoothGroup SGA7PersistsNF ZInQ.Contrib.AbVarBC

namespace SZRaynaud.Ambient

variable {K L Ω : Type} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
  {O : ValuationSubring K} {P : ValuationSubring L} {w : ValuationSubring Ω}
  (hw : w.comap (algebraMap K Ω) = O) (hp : w.comap (algebraMap L Ω) = P)
  (hP : P.comap (algebraMap K L) = O)

theorem ambientBase_comp : base hp ≫ gD hP = base hw := by
  rw [← Spec.map_comp]
  congr 1
  ext a : 2
  apply Subtype.ext
  exact (IsScalarTower.algebraMap_apply K L Ω (a : K)).symm

variable (A : PkgI3.AbVar K) (M : GroupModelO A O)

private theorem genPtHom_of_fst
    (x : Over.mk (gen ≫ base hw) ⟶ M.G)
    (y : PkgI3.AbVar.ptObj (K := K) Ω ⟶ (Over.pullback (jO O)).obj M.G)
    (hy : y.left ≫ pullback.fst M.G.hom (jO O) = x.left) :
    y ≫ M.gen.hom = genPtHom hw A M x := by
  change y ≫ M.gen.hom =
    (Over.mapPullbackAdj (jO O)).homEquiv (PkgI3.AbVar.ptObj Ω) M.G (_ ≫ x) ≫ M.gen.hom
  congr 1
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [hy, pullback_homEquiv_fst]
    exact (Category.id_comp x.left).symm
  · exact y.w.trans (Over.w _).symm

/-- A generic lift is identified by its projection to the original model. -/
theorem genPtHom_eq_of_projection
    (x : Over.mk (gen ≫ base hw) ⟶ M.G)
    (y : PkgI3.AbVar.ptObj (K := K) Ω ⟶ (Over.pullback (jO O)).obj M.G)
    (hy : y.left ≫ pullback.fst M.G.hom (jO O) = x.left) :
    y ≫ M.gen.hom = genPtHom hw A M x :=
  genPtHom_of_fst hw A M x y hy

/-- The point equivalence for base change takes the first projection on
underlying schemes. -/
theorem bcPt_left_fst (x : (A.baseChange L).Pt Ω) :
    (bcPt A Ω x).left = x.left ≫ pullback.fst A.X.hom (sK K L) := by
  let e := (Over.mapPullbackAdj (sK K L)).homEquiv (PkgI3.AbVar.ptObj Ω) A.X
  change (((ptMapIso (K := K) (L := L) Ω).inv ≫ e.symm x)).left =
    x.left ≫ pullback.fst A.X.hom (sK K L)
  let q : Spec (.of Ω) ⟶ A.X.left := (e.symm x).left
  have h := pullback_homEquiv_fst (sK K L) (PkgI3.AbVar.ptObj Ω) A.X (e.symm x)
  change (e (e.symm x)).left ≫ pullback.fst A.X.hom (sK K L) = q at h
  have he := congrArg Over.Hom.left (e.apply_symm_apply x)
  change (𝟙 (Spec (.of Ω))) ≫ q = _
  exact (Category.id_comp _).trans (h.symm.trans (congrArg (· ≫ pullback.fst A.X.hom (sK K L)) he))

private theorem ambientGeneric_w :
    (PkgI3.AbVar.ptObj (K := K) Ω).hom ≫ jO O = gen (w := w) ≫ base hw := by
  change Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ jO O = gen ≫ base hw
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

/-- A point of the changed model gives a point of the original model over the
same ambient generic field by projection. -/
def ambientProjectGeneric
    (x : Over.mk (gen ≫ base hp) ⟶ (bcDVR hP M).G) :
    Over.mk (gen ≫ base hw) ⟶ M.G := by
  let a : Spec (.of Ω) ⟶ pullback M.G.hom (gD hP) := x.left
  have ha : a ≫ pullback.snd M.G.hom (gD hP) = gen ≫ base hp := x.w
  refine Over.homMk (a ≫ pullback.fst M.G.hom (gD hP)) ?_
  change (a ≫ pullback.fst M.G.hom (gD hP)) ≫ M.G.hom = gen ≫ base hw
  rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Category.assoc,
    ambientBase_comp hw hp hP]

set_option maxHeartbeats 750000 in
/-- The chosen generic-fibre isomorphism of the changed model commutes with
the first projection to the original model. -/
theorem genPtHom_bcDVR
    (x : Over.mk (gen ≫ base hp) ⟶ (bcDVR hP M).G) :
    bcPt A Ω (genPtHom hp (A.baseChange L) (bcDVR hP M) x) =
      genPtHom hw A M (ambientProjectGeneric hw hp hP A M x) := by
  let B := gD hP
  let K₀ := jO O
  let L₀ := jO P
  let s := sK K L
  let G := M.G
  let Mp := bcDVR hP M
  let e₁ := isoX (pbCompIso L₀ B (s ≫ K₀) (jO_gD hP) (Grp.mk G))
  let e₂ := isoX (pbCompIso s K₀ (s ≫ K₀) rfl (Grp.mk G))
  let F := Over.pullback s
  let x₀ : Spec (.of Ω) ⟶ Mp.G.left := x.left
  have hx : x₀ ≫ Mp.G.hom = (PkgI3.AbVar.ptObj (K := L) Ω).hom ≫ L₀ :=
    x.w.trans (ambientGeneric_w hp).symm
  let y : PkgI3.AbVar.ptObj (K := L) Ω ⟶ (Over.pullback L₀).obj Mp.G :=
    Over.homMk (pullback.lift x₀ (PkgI3.AbVar.ptObj (K := L) Ω).hom hx) (pullback.lift_snd _ _ _)
  have hy : y.left ≫ pullback.fst Mp.G.hom L₀ = x.left := pullback.lift_fst _ _ _
  have hy₁ : y ≫ Mp.gen.hom = genPtHom hp (A.baseChange L) Mp x :=
    genPtHom_of_fst hp (A.baseChange L) Mp x y hy
  let z : PkgI3.AbVar.ptObj (K := L) Ω ⟶ F.obj ((Over.pullback K₀).obj G) :=
    y ≫ e₁.hom ≫ e₂.inv
  have hz : z.left ≫ pullback.fst ((Over.pullback K₀).obj G).hom s ≫
      pullback.fst G.hom K₀ = x.left ≫ pullback.fst G.hom B := by
    change y.left ≫ e₁.hom.left ≫ e₂.inv.left ≫ pullback.fst (pullback.snd G.hom K₀) s ≫
      pullback.fst G.hom K₀ = _
    have h₁ := pbCompIso_fst L₀ B (s ≫ K₀) (jO_gD hP) (Grp.mk G)
    have h₂ := pbCompIso_inv_fst s K₀ (s ≫ K₀) rfl (Grp.mk G)
    rw [show e₂.inv.left ≫ pullback.fst (pullback.snd G.hom K₀) s ≫
      pullback.fst G.hom K₀ = pullback.fst G.hom (s ≫ K₀) from h₂]
    have ha : e₁.hom.left ≫ pullback.fst G.hom (s ≫ K₀) =
        pullback.fst Mp.G.hom L₀ ≫ pullback.fst G.hom B := h₁
    exact (congrArg (fun f : ((Over.pullback L₀).obj Mp.G).left ⟶ G.left => y.left ≫ f) ha).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst G.hom B) hy))
  let Z := (Over.pullback K₀).obj G
  let z₀ : Spec (.of Ω) ⟶ pullback Z.hom s := z.left
  have hz₀ : z₀ ≫ pullback.snd Z.hom s = Spec.map (CommRingCat.ofHom (algebraMap L Ω)) := z.w
  let zK : PkgI3.AbVar.ptObj (K := K) Ω ⟶ Z := Over.homMk
    (z₀ ≫ pullback.fst Z.hom s) (by
      change (z₀ ≫ pullback.fst Z.hom s) ≫ Z.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω))
      rw [Category.assoc, pullback.condition, ← Category.assoc, hz₀]
      exact specMap_comp_sK (K := K) (L := L) Ω)
  have hcomp : z ≫ F.map M.gen.hom = y ≫ Mp.gen.hom := rfl
  have hf : (F.map M.gen.hom).left ≫ pullback.fst A.X.hom s =
      pullback.fst Z.hom s ≫ M.gen.hom.left := by
    simp only [F, Over.pullback_map_left, pullback.lift_fst]
    rfl
  apply Over.OverMorphism.ext
  rw [bcPt_left_fst, ← hy₁, ← hcomp]
  change (z.left ≫ (F.map M.gen.hom).left) ≫ pullback.fst A.X.hom s = _
  rw [Category.assoc, hf]
  have e := congrArg Over.Hom.left
    (genPtHom_of_fst hw A M (ambientProjectGeneric hw hp hP A M x) zK hz)
  exact (Category.assoc _ _ _).symm.trans e

#print axioms ambientBase_comp
#print axioms genPtHom_bcDVR

end SZRaynaud.Ambient
