import ZInQKernel.Contrib.OneProof.SZThm33.AmbientValuationEmbedding
import ZInQKernel.Contrib.OneProof.FaltingsDict

/-!
# The geometric residue Tate module inside the given abelian variety
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit
open ZInQ.Contrib.AbVarBC
open ZInQ.FaltingsRestate (isCommMonObj_groupModelO)

namespace SZRaynaud.Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  {O : ValuationSubring K} {w : ValuationSubring Ω}
  (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
  (M : GroupModelO A O)

private theorem gen_base : (PkgI3.AbVar.ptObj (K := K) Ω).hom ≫ jO O = gen ≫ base hw := by
  change Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ jO O = gen ≫ base hw
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

private def genPtIso : (Over.map (jO O)).obj (PkgI3.AbVar.ptObj (K := K) Ω) ≅ (Over.mk (gen ≫ base hw)) :=
  Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (gen_base hw).symm)

def genPtHom : ((Over.mk (gen ≫ base hw)) ⟶ M.G) →* A.Pt Ω := by
  let F := Over.pullback (jO O)
  letI : GrpObj (F.obj M.G) := Functor.grpObjObj
  have hgen : IsMonHom M.gen.hom := M.gen_hom
  let Φ := (Over.mapPullbackAdj (jO O)).homEquiv (PkgI3.AbVar.ptObj (K := K) Ω) M.G
  refine
    { toFun := fun x => Φ ((genPtIso hw).hom ≫ x) ≫ M.gen.hom
      map_one' := ?_
      map_mul' := ?_ }
  · rw [MonObj.comp_one, show Φ 1 = 1 by
      dsimp [Φ]
      rw [Adjunction.homEquiv_unit, F.map_one, MonObj.comp_one],
      MonObj.one_comp]
  · intro x y
    rw [MonObj.comp_mul, show ∀ v u, Φ (v * u) = Φ v * Φ u from fun v u => by
      dsimp [Φ]
      rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
        F.map_mul, MonObj.comp_mul], MonObj.mul_comp]

theorem genPtHom_injective : Function.Injective (genPtHom hw A M) := by
  intro x y h
  apply (cancel_epi (genPtIso hw).hom).mp
  apply ((Over.mapPullbackAdj (jO O)).homEquiv (PkgI3.AbVar.ptObj (K := K) Ω) M.G).injective
  exact (cancel_mono M.gen.hom).mp h

theorem genPtHom_surjective : Function.Surjective (genPtHom hw A M) := by
  intro x
  let Φ := (Over.mapPullbackAdj (jO O)).homEquiv (PkgI3.AbVar.ptObj (K := K) Ω) M.G
  refine ⟨(genPtIso hw).inv ≫ Φ.symm (x ≫ M.gen.inv), ?_⟩
  change Φ ((genPtIso hw).hom ≫ (genPtIso hw).inv ≫ Φ.symm
    (x ≫ M.gen.inv)) ≫ M.gen.hom = x
  rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

theorem genPtHom_extPt {E : Type} [Field E] [Algebra K E]
    {v : ValuationSubring E} (hv : v.comap (algebraMap K E) = O)
    (κ : E →ₐ[K] Ω) (x : Over.mk (gen (w := v) ≫ base hv) ⟶ M.G)
    (he : Spec.map (CommRingCat.ofHom (κ : E →+* Ω)) ≫ (gen (w := v) ≫ base hv) =
      gen (w := w) ≫ base hw) :
    genPtHom hw A M (Over.homMk _ he ≫ x) = extPt A κ (genPtHom hv A M x) := by
  let e := genPtIso hw
  let e' := genPtIso hv
  let y := extHom κ
  let y' : (Over.mk (gen ≫ base hw)) ⟶ Over.mk (gen (w := v) ≫ base hv) := Over.homMk _ he
  have h : e.hom ≫ y' = (Over.map (jO O)).map y ≫ e'.hom := by
    apply Over.OverMorphism.ext
    change (𝟙 _) ≫ Spec.map (CommRingCat.ofHom (κ : E →+* Ω)) =
      Spec.map (CommRingCat.ofHom (κ : E →+* Ω)) ≫ (𝟙 _)
    rw [Category.id_comp, Category.comp_id]
  change ((Over.mapPullbackAdj (jO O)).homEquiv (PkgI3.AbVar.ptObj (K := K) Ω) M.G (e.hom ≫ y' ≫ x)) ≫ M.gen.hom =
    y ≫ ((Over.mapPullbackAdj (jO O)).homEquiv _ M.G (e'.hom ≫ x)) ≫ M.gen.hom
  rw [← Category.assoc e.hom, h, Category.assoc, Adjunction.homEquiv_naturality_left,
    Category.assoc]

private theorem genPtHom_natural (d : w.decompositionSubgroup K) (x : (Over.mk (gen ≫ base hw)) ⟶ M.G) :
    genPtHom hw A M
        ((Over.homMk (genEnd d) (genEnd_gen_base hw d) : (Over.mk (gen ≫ base hw)) ⟶ (Over.mk (gen ≫ base hw))) ≫ x) =
      A.galAct d.1 (genPtHom hw A M x) := by
  let y : (PkgI3.AbVar.ptObj (K := K) Ω) ⟶ (PkgI3.AbVar.ptObj (K := K) Ω) := PkgI3.AbVar.galHom d.1
  let y' : (Over.mk (gen ≫ base hw)) ⟶ (Over.mk (gen ≫ base hw)) := Over.homMk (genEnd d) (genEnd_gen_base hw d)
  let e := genPtIso hw
  have h : e.hom ≫ y' = (Over.map (jO O)).map y ≫ e.hom := by
    apply Over.OverMorphism.ext
    change (𝟙 _) ≫ genEnd d = genEnd d ≫ (𝟙 _)
    rw [Category.id_comp, Category.comp_id]
  change ((Over.mapPullbackAdj (jO O)).homEquiv (PkgI3.AbVar.ptObj (K := K) Ω) M.G (e.hom ≫ y' ≫ x)) ≫ M.gen.hom =
    y ≫ ((Over.mapPullbackAdj (jO O)).homEquiv (PkgI3.AbVar.ptObj (K := K) Ω) M.G (e.hom ≫ x)) ≫ M.gen.hom
  rw [← Category.assoc e.hom, h, Category.assoc, Adjunction.homEquiv_naturality_left,
    Category.assoc]

variable [IsAlgClosed Ω] {ℓ : ℕ} [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

local instance : IsCommMonObj M.G := isCommMonObj_groupModelO M

/-- The residue Tate towers of the given Néron model inject into the
Tate module of its specified abelian generic fibre. -/
def modelEmbedTate :
    PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ M.G)) →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
  (PkgI3.Tate.map (genPtHom hw A M).toAdditive).comp (embedTate hw hu)

theorem modelEmbedTate_injective : Function.Injective (modelEmbedTate hw A M hu) := by
  intro x y h
  apply embedTate_injective (X := M.G) hw hu
  apply Subtype.ext
  funext n
  apply Additive.toMul.injective
  apply genPtHom_injective hw A M
  exact congrArg (fun t : TΩ A Ω ℓ => Additive.toMul (t.1 n)) h

theorem modelEmbedTate_tateEnd (d : w.decompositionSubgroup K)
    (t : PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ M.G))) :
    modelEmbedTate hw A M hu
        (SmoothGroup.tateEnd _ (resEnd d) (resEnd_res_base hw d) t) =
      galTΩ A ℓ d.1 (modelEmbedTate hw A M hu t) := by
  unfold modelEmbedTate
  rw [LinearMap.comp_apply, LinearMap.comp_apply, embedTate_tateEnd hw d hu t]
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (genPtHom_natural hw A M d _)

#print axioms modelEmbedTate_injective
#print axioms modelEmbedTate_tateEnd

end SZRaynaud.Ambient
