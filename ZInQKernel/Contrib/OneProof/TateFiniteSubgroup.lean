import ZInQKernel.Contrib.OneProof.TateTorsionSupport

/-! # Finite subgroup schemes from Galois-stable geometric subgroups -/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj PkgI3.AbVar
open scoped CategoryTheory.MonObj
open ZInQ.Contrib.CloudR2Poincare

namespace ZInQ.Contrib.TateFiniteApproximation

variable {K : Type} [Field K]

private theorem exists_geomPt_of_closed {T : Over (Spec (.of K))} [LocallyOfFiniteType T.hom]
    (x : T.left) (hx : IsClosed ({x} : Set T.left)) : ∃ P : GeomPt T, supportPoint P = x := by
  let i := T.left.fromSpecResidueField x
  have : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp hx
  let a : CommRingCat.of K ⟶ T.left.residueField x := Spec.preimage (i ≫ T.hom)
  have ha : Spec.map a = i ≫ T.hom := Spec.map_preimage _
  let : Algebra K (T.left.residueField x) := a.hom.toAlgebra
  have : IsFinite (i ≫ T.hom) :=
    (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := i ≫ T.hom)).mpr inferInstance
  have : Module.Finite K (T.left.residueField x) := by
    change a.hom.Finite
    rw [← IsFinite.SpecMap_iff, ha]
    infer_instance
  let b : T.left.residueField x →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let j := Spec.map (CommRingCat.ofHom b.toRingHom)
  have hw : (j ≫ i) ≫ T.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) := by
    rw [Category.assoc, ← ha, ← Spec.map_comp]
    congr 1
    ext k
    exact b.commutes k
  exact ⟨Over.homMk (j ≫ i) hw, T.left.fromSpecResidueField_apply x _⟩

private abbrev supportOver {X : Over (Spec (.of K))} (Z : TopologicalSpace.Closeds X.left) :=
  Over.mk (L1.reducedClosedSupportι X.left Z ≫ X.hom)

private abbrev supportIncl {X : Over (Spec (.of K))} (Z : TopologicalSpace.Closeds X.left) :
    supportOver Z ⟶ X := Over.homMk (L1.reducedClosedSupportι X.left Z) rfl

private theorem factor_support {T X : Over (Spec (.of K))} [IsReduced T.left]
    [LocallyOfFiniteType T.hom] (Z : TopologicalSpace.Closeds X.left) (f : T ⟶ X)
    (h : ∀ P : GeomPt T, supportPoint (P ≫ f) ∈ Z) :
    ∃ g : T ⟶ supportOver Z, g ≫ supportIncl Z = f := by
  have : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace T.hom
  have hd : Dense (closedPoints T.left) := by
    rw [dense_iff_closure_eq, ← Set.univ_inter (closedPoints T.left),
      JacobsonSpace.closure_inter_closedPoints_eq_closure isOpen_univ.isLocallyClosed, closure_univ]
  have hsub : closedPoints T.left ⊆ f.left ⁻¹' (Z : Set X.left) := by
    intro x hx
    obtain ⟨P, rfl⟩ := exists_geomPt_of_closed x hx
    exact h P
  have hall := closure_minimal hsub (Z.isClosed.preimage f.left.continuous)
  rw [hd.closure_eq] at hall
  obtain ⟨g, hg⟩ := L1.exists_factor_reducedClosedSupport Z f.left
    (fun _ hx => by obtain ⟨y,rfl⟩ := hx; exact hall (Set.mem_univ y))
  refine ⟨Over.homMk g ?_, Over.OverMorphism.ext hg⟩
  change g ≫ L1.reducedClosedSupportι X.left Z ≫ X.hom = T.hom
  rw [← Category.assoc, hg, Over.w]

/-- A closed finite subgroup scheme of an abelian variety. -/
structure FiniteSubgroupScheme (A : PkgI3.AbVar K) where
  obj : Over (Spec (.of K))
  [grp : GrpObj obj]
  incl : obj ⟶ A.X
  [hom : IsMonHom incl]
  [closed : IsClosedImmersion incl.left]
  [finite : IsFinite obj.hom]

attribute [instance] FiniteSubgroupScheme.grp FiniteSubgroupScheme.hom
  FiniteSubgroupScheme.closed FiniteSubgroupScheme.finite

/-- The finite subgroup scheme over K representing precisely a finite,
Galois-stable subgroup of the geometric points. -/
theorem exists_finiteSubgroupScheme [CharZero K] (A : PkgI3.AbVar K)
    (S : Subgroup (GeomPt A.X)) (hfin : (S : Set (GeomPt A.X)).Finite)
    (hstable : ∀ σ : Field.absoluteGaloisGroup K, ∀ P ∈ S, galHom σ ≫ P ∈ S) :
    ∃ H : FiniteSubgroupScheme A, ∀ P : GeomPt A.X, P ∈ S ↔ ∃ z : GeomPt H.obj, z ≫ H.incl = P := by
  obtain ⟨Z, hZ, hpts⟩ := exists_closed_support (K := K) (X := A.X) (S : Set _) hfin hstable
  let H := supportOver (X := A.X) Z
  let j : H ⟶ A.X := supportIncl Z
  have : IsClosedImmersion j.left := L1.reducedClosedSupport_closed A.X.left Z
  have : IsReduced H.left := L1.reducedClosedSupport_reduced A.X.left Z
  have : IsProper H.hom := inferInstanceAs (IsProper ((supportIncl Z).left ≫ A.X.hom))
  have ht : Finite H.left := by
    have hr : (Set.range j.left).Finite := (L1.range_reducedClosedSupportι A.X.left Z).symm ▸ hZ
    let _ := hr.to_subtype
    exact Finite.of_injective (fun x : H.left => (⟨j.left x, x, rfl⟩ : Set.range j.left))
      (fun _ _ h => j.left.isClosedEmbedding.injective (congrArg (fun t : Set.range j.left => t.val) h))
  have : LocallyQuasiFinite H.hom := LocallyQuasiFinite.of_finite_preimage_singleton _ (fun _ => Set.toFinite _)
  have : IsFinite H.hom := IsFinite.of_isProper_of_locallyQuasiFinite _
  have : Etale H.hom := L4.finite_reduced_scheme_etale H.hom
  have : IsFinite (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance
  have : Etale (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance
  have : IsReduced (H ⊗ H).left := L4.finite_etale_scheme_reduced (H ⊗ H).hom
  have : LocallyOfFiniteType (𝟙_ (Over (Spec (.of K)))).hom := inferInstanceAs (LocallyOfFiniteType (𝟙 _))
  have : IsReduced (𝟙_ (Over (Spec (.of K)))).left := inferInstanceAs (IsReduced (Spec (.of K)))
  have : Mono j := Over.mono_of_mono_left j
  have hpt (P : GeomPt H) : P ≫ j ∈ S := (hpts _).mp (by
    change supportPoint (P ≫ j) ∈ (Z : Set A.X.left)
    rw [← L1.range_reducedClosedSupportι A.X.left Z]
    exact ⟨supportPoint P, rfl⟩)
  obtain ⟨m, hm⟩ := factor_support Z (fst H H ≫ j * snd H H ≫ j) (fun P => (hpts _).mpr (by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
    exact S.mul_mem (hpt _) (hpt _)))
  obtain ⟨e, he⟩ := factor_support Z η[A.X] (fun P => (hpts _).mpr (by
    have h : P = toUnit _ := toUnit_unique _ _
    rw [h]; exact S.one_mem))
  obtain ⟨v, hv⟩ := factor_support Z j⁻¹ (fun P => (hpts _).mpr (by
    rw [GrpObj.comp_inv]; exact S.inv_mem (hpt P)))
  let : GrpObj H := L4.grpObjOfMono j m hm e he v hv
  let : IsMonHom j := L4.isMonHom_grpObjOfMono j m hm e he v hv
  refine ⟨⟨H,j⟩, fun P => ⟨?_, ?_⟩⟩
  · intro hp
    let : IsReduced (ptObj (K := K) (AlgebraicClosure K)).left := inferInstanceAs (IsReduced (Spec (.of (AlgebraicClosure K))))
    obtain ⟨a, ha⟩ := L1.exists_factor_reducedClosedSupport Z P.left (fun _ h => by
      obtain ⟨x,rfl⟩ := h
      have heq : x = IsLocalRing.closedPoint (AlgebraicClosure K) :=
        @Subsingleton.elim (PrimeSpectrum (AlgebraicClosure K)) _ _ _
      rw [heq]; exact (hpts _).mpr hp)
    refine ⟨Over.homMk a ?_, Over.OverMorphism.ext ha⟩
    change a ≫ L1.reducedClosedSupportι A.X.left Z ≫ A.X.hom = _
    rw [← Category.assoc, ha, Over.w]
  · rintro ⟨z,rfl⟩
    exact hpt z

end ZInQ.Contrib.TateFiniteApproximation
