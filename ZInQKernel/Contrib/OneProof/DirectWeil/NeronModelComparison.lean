import ZInQKernel.OneProof.H.TailZ14

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open ReductSplit ReductGlue

namespace SZRaynaud

variable {K : Type} [Field K] {O : ValuationSubring K} {A : PkgI3.AbVar K}

/-- A smooth group model has a unique group homomorphism to the Néron model
compatible with the given identifications of the generic fibres. -/
theorem exists_unique_neronModelComparison (M N : GroupModelO A O) (hN : N.IsNeronModel) :
    ∃! f : M.G ⟶ N.G, IsMonHom f ∧
      (Over.pullback (jO O)).map f ≫ N.gen.hom = M.gen.hom := by
  let F := Over.pullback (jO O)
  let : GrpObj (F.obj M.G) := Functor.grpObjObj
  let : GrpObj (F.obj N.G) := Functor.grpObjObj
  have := M.gen_hom
  have := N.gen_hom
  obtain ⟨f, hf⟩ := (hN M.G).surjective M.gen.hom
  change F.map f ≫ N.gen.hom = M.gen.hom at hf
  have key {T : Over (Spec (.of O))} (a : T ⟶ M.G) :
      F.map (a ≫ f) ≫ N.gen.hom = F.map a ≫ M.gen.hom := by
    rw [Functor.map_comp, Category.assoc, hf]
  have hmul (T : Over (Spec (.of O))) [Smooth T.hom] (a b : T ⟶ M.G) :
      (a * b) ≫ f = a ≫ f * b ≫ f := by
    apply (hN T).injective
    change F.map ((a * b) ≫ f) ≫ N.gen.hom = F.map (a ≫ f * b ≫ f) ≫ N.gen.hom
    rw [key, Functor.map_mul, Functor.map_mul, MonObj.mul_comp, MonObj.mul_comp, key, key]
  have hone (T : Over (Spec (.of O))) [Smooth T.hom] : (1 : T ⟶ M.G) ≫ f = 1 := by
    apply (hN T).injective
    change F.map (1 ≫ f) ≫ N.gen.hom = F.map 1 ≫ N.gen.hom
    rw [key, Functor.map_one, Functor.map_one, MonObj.one_comp, MonObj.one_comp]
  have : Smooth (𝟙_ (Over (Spec (.of O)))).hom := ZInQ.Contrib.NeronC.smooth_tensorUnit _
  have : Smooth (M.G ⊗ M.G).hom := ZInQ.Contrib.NeronC.smooth_tensor _ _ inferInstance inferInstance
  refine ⟨f, ⟨⟨?_, ?_⟩, hf⟩, fun f' hf' => (hN M.G).injective (hf'.2.trans hf.symm)⟩
  · rw [MonObj.one_eq_one, MonObj.one_eq_one, hone]
  · rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, hmul, MonObj.comp_mul]
    simp

def neronModelComparison (M N : GroupModelO A O) (hN : N.IsNeronModel) : M.G ⟶ N.G :=
  Classical.choose (exists_unique_neronModelComparison M N hN)

theorem neronModelComparison_hom (M N : GroupModelO A O) (hN : N.IsNeronModel) :
    IsMonHom (neronModelComparison M N hN) :=
  (Classical.choose_spec (exists_unique_neronModelComparison M N hN)).1.1

theorem neronModelComparison_generic (M N : GroupModelO A O) (hN : N.IsNeronModel) :
    (Over.pullback (jO O)).map (neronModelComparison M N hN) ≫ N.gen.hom = M.gen.hom :=
  (Classical.choose_spec (exists_unique_neronModelComparison M N hN)).1.2

theorem neronModelComparison_generic_isIso (M N : GroupModelO A O) (hN : N.IsNeronModel) :
    IsIso ((Over.pullback (jO O)).map (neronModelComparison M N hN)) := by
  have e : (Over.pullback (jO O)).map (neronModelComparison M N hN) = M.gen.hom ≫ N.gen.inv := by
    rw [← neronModelComparison_generic M N hN, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]
  infer_instance

end SZRaynaud
