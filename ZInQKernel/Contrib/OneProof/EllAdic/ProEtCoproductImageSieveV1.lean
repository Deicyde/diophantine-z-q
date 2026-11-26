import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.LocallySurjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace RC53.EllAdic

universe u w

/-- Glue actual local lifts over a covering family presented as the disjoint
summands of a scheme coproduct. The presentation need not be definitional. -/
theorem proEt_imageSieve_of_coproductCover
    {S : Scheme.{u}} {I : Type w} [Small.{u} I]
    (W : I → S.ProEt) {V U : S.ProEt}
    (a : ∀ i, W i ⟶ V) (p : V ⟶ U)
    (e : V.left ≅ ∐ (fun i => (W i).left))
    (ha : ∀ i, (a i).left ≫ e.hom = Sigma.ι (fun j => (W j).left) i)
    (hc : Presieve.ofArrows W a ∈ Scheme.ProEt.precoverage S V)
    {F G : Sheaf (Scheme.ProEt.topology S) Ab.{u+1}}
    (f : F ⟶ G) (r : ToType (G.obj.obj (op U)))
    (h : ∀ i, Presheaf.imageSieve f.hom r (a i ≫ p)) :
    Presheaf.imageSieve f.hom r p := by
  classical
  let J := Scheme.ProEt.topology S
  let L : S.ProEt ⥤ Scheme.{u} := Scheme.ProEt.forget S ⋙ Over.forget S
  let PF := F.obj ⋙ forget Ab.{u+1}
  let PG := G.obj ⋙ forget Ab.{u+1}
  have hF : Presieve.IsSheaf J PF :=
    (isSheaf_iff_isSheaf_of_type J PF).1
      (Presheaf.isSheaf_comp_of_isSheaf J F.obj (forget Ab.{u+1}) F.2)
  have hG : Presieve.IsSheaf J PG :=
    (isSheaf_iff_isSheaf_of_type J PG).1
      (Presheaf.isSheaf_comp_of_isSheaf J G.obj (forget Ab.{u+1}) G.2)
  have hcov : Sieve.generate (Presieve.ofArrows W a) ∈ J V :=
    Precoverage.generate_mem_toGrothendieck hc
  let t : (i : I) → PF.obj (op (W i)) :=
    fun i => Presheaf.localPreimage f.hom r (a i ≫ p) (h i)
  have ht (i : I) : f.hom.app (op (W i)) (t i) = G.obj.map (a i ≫ p).op r :=
    Presheaf.app_localPreimage f.hom r (a i ≫ p) (h i)
  have hcompat : Presieve.Arrows.Compatible PF a t := by
    intro i j Z b c hbc
    have hh : b.left ≫ (a i).left = c.left ≫ (a j).left := L.congr_map hbc
    have hleft : b.left ≫ Sigma.ι (fun k => (W k).left) i =
        c.left ≫ Sigma.ι (fun k => (W k).left) j := by
      calc
        b.left ≫ Sigma.ι (fun k => (W k).left) i = (b.left ≫ (a i).left) ≫ e.hom :=
          (congrArg (fun m => b.left ≫ m) (ha i).symm).trans (Category.assoc _ _ _).symm
        _ = (c.left ≫ (a j).left) ≫ e.hom := congrArg (fun m => m ≫ e.hom) hh
        _ = c.left ≫ Sigma.ι (fun k => (W k).left) j :=
          (Category.assoc _ _ _).trans (congrArg (fun m => c.left ≫ m) (ha j))
    by_cases hij : i = j
    · subst j
      let : IsOpenImmersion (Sigma.ι (fun k => (W k).left) i) :=
        (AlgebraicGeometry.sigmaOpenCover (fun k => (W k).left)).map_prop i
      have hleft' : b.left = c.left := (cancel_mono _).1 hleft
      have heq : b = c := L.map_injective hleft'
      rw [heq]
    · let : IsEmpty Z.left := AlgebraicGeometry.isEmpty_of_commSq_sigmaι_of_ne
          (g := fun k => (W k).left) ⟨hleft⟩ hij
      apply (hF.isSeparated (⊥ : Sieve Z) (Scheme.ProEt.bot_mem_topology Z)).ext
      intro Y q hq
      exact False.elim hq
  obtain ⟨x, hx, _⟩ :=
    (Presieve.isSheafFor_arrows_iff (P := PF) (π := a)).1
      (hF.isSheafFor (Presieve.ofArrows W a) hcov) t hcompat
  refine ⟨x, ?_⟩
  let s : PG.obj (op V) := G.obj.map p.op r
  have hr (i : I) : PG.map (a i).op (f.hom.app (op V) x) = PG.map (a i).op s := by
    change G.obj.map (a i).op (f.hom.app _ x) = G.obj.map (a i).op (G.obj.map p.op r)
    have hxi : F.obj.map (a i).op x = t i := hx i
    rw [← NatTrans.naturality_apply f.hom, hxi, ht i,
      op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  have hj :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompatible (P := PG) (π := a)).1
      (hG.isSheafFor (Presieve.ofArrows W a) hcov)
  change f.hom.app (op V) x = s
  apply hj.injective
  exact Subtype.ext (funext hr)

end RC53.EllAdic
