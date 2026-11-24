import ZInQKernel.Contrib.OneProof.SZThm33.GeomTateNaturality
import ZInQKernel.Contrib.OneProof.SZThm33.TateIdentityComponent

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.HeightSplit SmoothGroup ReductSplit

namespace SZRaynaud

section Connected

variable {k : Type} [Field k] [IsAlgClosed k] {ℓ : ℕ} [Fact ℓ.Prime]

private def unitAlgPtIso : (𝟙_ (Over (Spec (CommRingCat.of k)))) ≅ algPt k k :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
    change (𝟙 (Spec (.of k))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap k k))) = 𝟙 _
    rw [Category.id_comp, Algebra.algebraMap_self]
    exact Spec.map_id _)

private def precompTate {P Q G : (Over (Spec (CommRingCat.of k)))} [GrpObj G] [IsCommMonObj G] (a : P ⟶ Q) :
    PkgI3.Tate.T ℓ (Additive (Q ⟶ G)) →ₗ[ℤ_[ℓ]] PkgI3.Tate.T ℓ (Additive (P ⟶ G)) :=
  let f : (Q ⟶ G) →* (P ⟶ G) :=
    { toFun := fun x => a ≫ x
      map_one' := MonObj.comp_one a
      map_mul' := MonObj.comp_mul a }
  PkgI3.Tate.map f.toAdditive

/-- Geometric residue Tate towers lift to the connected open subgroup for
the specific affine test scheme used in the semistable presentation. -/
theorem surjective_mapTate_connectedOpenSubgroup
    {G U : (Over (Spec (CommRingCat.of k)))} [GrpObj G] [GrpObj U] [IsCommMonObj G] [IsCommMonObj U]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] [ConnectedSpace U.left]
    (i : U ⟶ G) [IsOpenImmersion i.left] [IsMonHom i] :
    Function.Surjective (mapModelTate (ℓ := ℓ) i (Spec.map (CommRingCat.ofHom (algebraMap k k)))) := by
  let e : (𝟙_ (Over (Spec (CommRingCat.of k)))) ≅ algPt k k := unitAlgPtIso
  intro x
  obtain ⟨y, hy⟩ := (bijective_tate_map_connectedOpenSubgroup (ℓ := ℓ) i).surjective
    (precompTate e.hom x)
  refine ⟨precompTate e.inv y, ?_⟩
  apply Subtype.ext
  funext n
  apply Additive.toMul.injective
  have h := congrArg (fun z : PkgI3.Tate.T ℓ (Additive ((𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶ G)) =>
    e.inv ≫ Additive.toMul (z.1 n)) hy
  change e.inv ≫ (Additive.toMul (y.1 n) ≫ i) =
    e.inv ≫ (e.hom ≫ Additive.toMul (x.1 n)) at h
  rw [Iso.inv_hom_id_assoc, ← Category.assoc] at h
  exact h

end Connected

namespace Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [IsAlgClosed Ω]
  {O : ValuationSubring K} {w : ValuationSubring Ω}
  (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (H M : GroupModelO A O)
  {ℓ : ℕ} [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

attribute [local instance] isCommMonObj_geomSpecialFibre

/-- Any geometric residue Tate tower is represented in the identity model
once the model fibres have geometrically connected identity subgroup. -/
theorem exists_connectedModelTate (i : H.G ⟶ M.G) [IsMonHom i] [IsOpenImmersion i.left]
    [GeometricallyIntegral H.G.hom]
    (hi : (Over.pullback (jO O)).map i ≫ M.gen.hom = H.gen.hom)
    (x : PkgI3.Tate.T ℓ (Additive ((algPt (ResBarO O) (ResBarO O)) ⟶ geomSpecialFibre M))) :
    ∃ y : PkgI3.Tate.T ℓ (Additive ((algPt (ResBarO O) (ResBarO O)) ⟶ geomSpecialFibre H)),
      mapModelTate (geomSpecialModelMap H M i) (Spec.map (CommRingCat.ofHom (algebraMap (ResBarO O) (ResBarO O)))) y = x ∧
      geomSpecialEmbedTate hw A H hu y = geomSpecialEmbedTate hw A M hu x := by
  let f := geomSpecialModelMap H M i
  have : IsOpenImmersion f.left := ZInQ.H5Glue.isOpenImmersion_pullback_map (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))) i
  have : IsMonHom f := geomSpecialModelMap_isMonHom A H M i
  have : LocallyOfFiniteType (geomSpecialFibre M).hom :=
    show LocallyOfFiniteType (pullback.snd M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))) by infer_instance
  have : QuasiCompact (geomSpecialFibre M).hom :=
    show QuasiCompact (pullback.snd M.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))) by infer_instance
  have hgeom : GeometricallyIntegral (geomSpecialFibre H).hom :=
    show GeometricallyIntegral (pullback.snd H.G.hom (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))) by infer_instance
  have : IsIntegral (geomSpecialFibre H).left :=
    GeometricallyIntegral.isIntegral_of_subsingleton (geomSpecialFibre H).hom
  have : ConnectedSpace (geomSpecialFibre H).left := inferInstance
  obtain ⟨y, hy⟩ := surjective_mapTate_connectedOpenSubgroup (ℓ := ℓ) f x
  exact ⟨y, hy, (geomSpecialEmbedTate_modelHom hw A H M hu i hi y).symm.trans
    (congrArg (geomSpecialEmbedTate hw A M hu) hy)⟩

end Ambient
end SZRaynaud
