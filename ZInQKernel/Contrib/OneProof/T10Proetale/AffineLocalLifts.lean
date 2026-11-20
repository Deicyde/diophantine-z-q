import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.AlgebraicGeometry.Limits

/-!
# Single affine refinements for local lifts

Over an affine object of the small pro-étale site, a section that lifts locally
along an abelian sheaf map lifts along a single affine weakly étale surjection.
A finite affine refinement suffices: take the disjoint union and glue the lifts.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

variable {X : Scheme.{0}}

private abbrev J := Scheme.ProEt.topology X

/-- The scheme underlying a map of the small pro-étale site. -/
abbrev proUnderlying (X : Scheme.{0}) : X.ProEt ⥤ Scheme.{0} :=
  Scheme.ProEt.forget X ⋙ Over.forget X

private lemma over_w {U V : X.ProEt} (a : U ⟶ V) :
    (proUnderlying X).map a ≫ V.hom = U.hom :=
  ((Scheme.ProEt.forget X).map a).w

set_option backward.isDefEq.respectTransparency false in
/-- A weakly étale quasi-compact surjection in the small site gives a covering sieve. -/
theorem proSingletonCover {U V : X.ProEt} (a : V ⟶ U)
    [WeaklyEtale ((proUnderlying X).map a)] [Surjective ((proUnderlying X).map a)]
    [QuasiCompact ((proUnderlying X).map a)] :
    Sieve.generate (Presieve.singleton a) ∈ J (X := X) U := by
  apply Precoverage.generate_mem_toGrothendieck
  rw [Scheme.ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_singleton]
  exact Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem pro_open_family_cover {U : X.ProEt} {I : Type} {V : I → X.ProEt}
    (a : ∀ i, V i ⟶ U) (ha : ∀ i, IsOpenImmersion ((proUnderlying X).map (a i)))
    (hs : ∀ x : U.left, ∃ i, ∃ y : (V i).left, (proUnderlying X).map (a i) y = x) :
    Sieve.ofArrows _ a ∈ J (X := X) U := by
  apply Precoverage.generate_mem_toGrothendieck
  rw [Scheme.ProEt.precoverage, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
  apply Scheme.zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale)
  rw [Scheme.ofArrows_mem_precoverage_iff]
  exact ⟨hs, ha⟩

private abbrev proDisjointUnion {I : Type} (V : I → Scheme.{0}) (U : X.ProEt)
    (a : ∀ i, V i ⟶ U.left) [∀ i, WeaklyEtale (a i)] : X.ProEt :=
  have : WeaklyEtale (Sigma.desc a) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale) (fun _i => inferInstance)
  .mk (Sigma.desc a ≫ U.hom)

private def proDisjointUnionMap {I : Type} (V : I → Scheme.{0}) (U : X.ProEt)
    (a : ∀ i, V i ⟶ U.left) [∀ i, WeaklyEtale (a i)] :
    proDisjointUnion V U a ⟶ U :=
  MorphismProperty.Over.homMk (Sigma.desc a) rfl

set_option backward.isDefEq.respectTransparency false in
private theorem gluing_local_lifts {U : X.ProEt} {I : Type} (V : I → Scheme.{0})
    (a : ∀ i, V i ⟶ U.left) [∀ i, WeaklyEtale (a i)]
    {F G : Sheaf (J (X := X)) Ab.{1}} (f : F ⟶ G) (s : G.obj.obj (op U))
    (b : ∀ i, Scheme.ProEt.mk (a i ≫ U.hom) ⟶ U)
    (hb : ∀ i, (proUnderlying X).map (b i) = a i)
    (hl : ∀ i, (Presheaf.imageSieve f.hom s) (b i)) :
    (Presheaf.imageSieve f.hom s) (proDisjointUnionMap V U a) := by
  classical
  let W := proDisjointUnion V U a
  let Wi (i : I) := Scheme.ProEt.mk (a i ≫ U.hom)
  let e (i : I) : Wi i ⟶ W := MorphismProperty.Over.homMk (Sigma.ι V i) (by
    change Sigma.ι V i ≫ Sigma.desc a ≫ U.hom = a i ≫ U.hom
    simp)
  have he (i : I) : e i ≫ proDisjointUnionMap V U a = b i := by
    apply (proUnderlying X).map_injective
    change Sigma.ι V i ≫ Sigma.desc a = (proUnderlying X).map (b i)
    rw [Sigma.ι_comp_desc, hb]
  let P := F.obj ⋙ forget Ab.{1}
  let Q := G.obj ⋙ forget Ab.{1}
  have hP := (sheafCompose (J (X := X)) (forget Ab.{1})).obj F |>.property
  have hQ := (sheafCompose (J (X := X)) (forget Ab.{1})).obj G |>.property
  have hc : Sieve.ofArrows _ e ∈ J (X := X) W :=
    pro_open_family_cover e (fun i => inferInstanceAs (IsOpenImmersion (Sigma.ι V i))) (fun x => by
      obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk V).surjective x
      exact ⟨i, y, (sigmaMk_mk V i y).symm.trans hy⟩)
  let R := Presieve.ofArrows Wi e
  have hPS : R.IsSheafFor P := (Presieve.isSheafFor_iff_generate _).mpr (hP.isSheafFor _ hc)
  have hQS : R.IsSheafFor Q := (Presieve.isSheafFor_iff_generate _).mpr (hQ.isSheafFor _ hc)
  choose z hz using hl
  have hcompat : Presieve.Arrows.Compatible P e z := by
    intro i j T l r hh
    by_cases hij : i = j
    · subst j
      have hlr : l = r := by
        apply (proUnderlying X).map_injective
        apply (cancel_mono (Sigma.ι V i)).mp
        have hmap := congrArg ((proUnderlying X).map) hh
        rw [Functor.map_comp, Functor.map_comp] at hmap
        exact hmap
      rw [hlr]
    · have : IsEmpty T.left := isEmpty_of_commSq_sigmaι_of_ne (g := V)
        (a := (proUnderlying X).map l) (b := (proUnderlying X).map r)
        ⟨by
          have hmap := congrArg ((proUnderlying X).map) hh
          rw [Functor.map_comp, Functor.map_comp] at hmap
          exact hmap⟩ hij
      apply (hP.isSheafFor _ (Scheme.ProEt.bot_mem_topology T)).isSeparatedFor.ext
      intro T' k hk
      exact False.elim hk
  obtain ⟨y, hy, _⟩ := (Presieve.isSheafFor_arrows_iff P e).mp hPS z hcompat
  refine ⟨y, ?_⟩
  apply hQS.isSeparatedFor.ext
  rintro _ _ ⟨i⟩
  change G.obj.map (e i).op (f.hom.app (op W) y) =
    G.obj.map (e i).op (G.obj.map (proDisjointUnionMap V U a).op s)
  rw [← NatTrans.naturality_apply f.hom (e i).op, show F.obj.map (e i).op y = z i from hy i,
    hz i, ← Functor.map_comp_apply, ← op_comp, he]

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- A locally liftable section on an affine object lifts on a single affine
weakly étale surjection. -/
theorem affineCover_lift {U : X.ProEt} [IsAffine U.left]
    {F G : Sheaf (J (X := X)) Ab.{1}} (f : F ⟶ G) (s : G.obj.obj (op U))
    (h : Presheaf.imageSieve f.hom s ∈ J (X := X) U) :
    ∃ (V : X.ProEt) (p : V ⟶ U), IsAffine V.left ∧ WeaklyEtale ((proUnderlying X).map p) ∧
      Surjective ((proUnderlying X).map p) ∧ (Presheaf.imageSieve f.hom s) p := by
  let K := Scheme.ProEt.precoverage X
  let : K.IsStableUnderComposition := inferInstanceAs
    (Scheme.proetalePrecoverage.comap (proUnderlying X)).IsStableUnderComposition
  let : K.IsStableUnderBaseChange := inferInstanceAs
    (Scheme.proetalePrecoverage.comap (proUnderlying X)).IsStableUnderBaseChange
  let : K.HasIsos := inferInstanceAs (Scheme.proetalePrecoverage.comap (proUnderlying X)).HasIsos
  obtain ⟨R, hR, hle⟩ := K.mem_toGrothendieck_iff_of_isStableUnderComposition.mp h
  obtain ⟨E, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR
  let B := E.toPreZeroHypercover.map (proUnderlying X)
  have hB : B.presieve₀ ∈ Scheme.proetalePrecoverage U.left := by
    rw [PreZeroHypercover.presieve₀_map]
    exact Precoverage.mem_comap_iff.mp E.mem₀
  let : QuasiCompactCover B := Scheme.presieve₀_mem_qcPrecoverage_iff.mp hB.1
  have htop : IsCompact ((⊤ : U.left.Opens) : Set U.left) := by simpa using isCompact_univ
  obtain ⟨n, j, O, hO, hcov⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact B htop
  let W (i : Fin n) : Scheme := O i
  let g (i : Fin n) : W i ⟶ U.left := (O i).ι ≫ B.f (j i)
  have hprop : ∀ j, WeaklyEtale (B.f j) := by
    have h' : Presieve.ofArrows B.X B.f ∈ Scheme.precoverage (@WeaklyEtale) U.left := hB.2
    rw [Scheme.ofArrows_mem_precoverage_iff] at h'
    exact h'.2
  let (i : Fin n) : WeaklyEtale (B.f (j i)) := hprop (j i)
  let (i : Fin n) : WeaklyEtale (g i) := inferInstanceAs (WeaklyEtale ((O i).ι ≫ B.f (j i)))
  let (i : Fin n) : IsAffine (W i) := hO i
  let V := proDisjointUnion W U g
  let p := proDisjointUnionMap W U g
  have hp : Surjective ((proUnderlying X).map p) := by
    constructor
    intro x
    have hx : x ∈ ⋃ i, B.f (j i) '' (O i) := by rw [hcov]; trivial
    obtain ⟨i, y, hy, hxy⟩ := Set.mem_iUnion.mp hx
    refine ⟨Sigma.ι W i ⟨y, hy⟩, ?_⟩
    change Sigma.desc g (Sigma.ι W i ⟨y, hy⟩) = x
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
    exact hxy
  let v (i : Fin n) : Scheme.ProEt.mk (g i ≫ U.hom) ⟶ E.X (j i) :=
    MorphismProperty.Over.homMk (O i).ι (by
      change (O i).ι ≫ (E.X (j i)).hom = ((O i).ι ≫ B.f (j i)) ≫ U.hom
      rw [Category.assoc]
      congr 1
      exact (over_w (E.f (j i))).symm)
  let b (i : Fin n) := v i ≫ E.f (j i)
  refine ⟨V, p, inferInstanceAs (IsAffine (∐ W)),
    IsZariskiLocalAtSource.sigmaDesc (P := @WeaklyEtale) (fun _i => inferInstance), hp, ?_⟩
  exact gluing_local_lifts W g f s b (fun _ => rfl)
    (fun i => (Presheaf.imageSieve f.hom s).downward_closed
      (hle _ _ (Presieve.ofArrows.mk (j i))) (v i))

end
end ZInQ.Manuscript.T10Proetale
