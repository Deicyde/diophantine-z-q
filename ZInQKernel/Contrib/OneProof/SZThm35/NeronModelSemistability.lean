import ZInQKernel.Contrib.OneProof.DirectWeil.NeronModelComparison
import ZInQKernel.Contrib.OneProof.SZRaynaud

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open ReductSplit

namespace SZRaynaud

variable {K : Type} [Field K] {O : ValuationSubring K} {A : PkgI3.AbVar K}

/-- The canonical comparison between two Néron models of the same abelian
variety is an isomorphism. -/
theorem isIso_neronModelComparison_of_neron (M N : GroupModelO A O)
    (hM : M.IsNeronModel) (hN : N.IsNeronModel) :
    IsIso (neronModelComparison M N hN) := by
  let f := neronModelComparison M N hN
  let g := neronModelComparison N M hM
  let F := Over.pullback (jO O)
  have hf : F.map f ≫ N.gen.hom = M.gen.hom := neronModelComparison_generic M N hN
  have hg : F.map g ≫ M.gen.hom = N.gen.hom := neronModelComparison_generic N M hM
  change IsIso f
  refine ⟨⟨g, ?_, ?_⟩⟩
  · apply (hM M.G).injective
    change F.map (f ≫ g) ≫ M.gen.hom = F.map (𝟙 M.G) ≫ M.gen.hom
    rw [F.map_comp, Category.assoc, hg, hf, F.map_id, Category.id_comp]
  · apply (hN N.G).injective
    change F.map (g ≫ f) ≫ N.gen.hom = F.map (𝟙 N.G) ≫ N.gen.hom
    rw [F.map_comp, Category.assoc, hf, hg, F.map_id, Category.id_comp]

/-- Semistability over the residue field passes to every Néron model. -/
theorem isSemistableResT_of_hasSemistableReductionSZ (N : GroupModelO A O) (hN : N.IsNeronModel)
    (h : HasSemistableReductionSZ A O) : DictModels.RaynaudOr.IsSemistableResT N := by
  obtain ⟨M, hM, hS⟩ := h
  let f := neronModelComparison M N hN
  let : IsIso f := isIso_neronModelComparison_of_neron M N hM hN
  let : IsMonHom f := neronModelComparison_hom M N hN
  let F := Over.pullback (UnipotentForward.sRes O)
  let i : UnipotentForward.specialFibre M ⟶ UnipotentForward.specialFibre N := F.map f
  have : IsIso (F.map f) := inferInstance
  let : IsIso i := ‹IsIso (F.map f)›
  let : IsMonHom i := Functor.map.instIsMonHom (F := F) M.G N.G f
  have : IsIso ((Over.forget _).map i) := inferInstance
  let : IsIso i.left := this
  change DictModels.RaynaudOr.HasSemiAbelianIdCompTorus (UnipotentForward.specialFibre M) at hS
  change DictModels.RaynaudOr.HasSemiAbelianIdCompTorus (UnipotentForward.specialFibre N)
  obtain ⟨U, hU, inc, hinc, hm, hconn, B, π, hπ, hflat, hsurj, r, e, he, hk, hn⟩ := hS
  let : GrpObj U := hU
  let : IsOpenImmersion inc.left := hinc
  let : IsMonHom inc := hm
  have hOpen : IsOpenImmersion (inc ≫ i).left := by
    rw [Over.comp_left]
    infer_instance
  exact ⟨U, hU, inc ≫ i, hOpen, inferInstance, hconn, B, π, hπ, hflat, hsurj, r, e, he, hk, hn⟩

end SZRaynaud

#print axioms SZRaynaud.isSemistableResT_of_hasSemistableReductionSZ
