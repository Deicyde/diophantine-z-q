import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientGroup
import ZInQKernel.Contrib.CloudR2Poincare.L4.KernelGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L4.DimensionTopology
import ZInQKernel.Contrib.CloudR2Poincare.L3.Vendor.StacksFrontier.Topology.Dimension.SpecializingSurjection

/-!
# Geometry of the supplied finite-flat stabilizer quotient

Separatedness is descended from the actual closed action relation; reducedness
and geometric integrality are proved under field base change. Dimension equality
uses the already-proved discrete-fibre bound and the single shared specializing
surjection supplier. No abelian-variety geometry is assumed for Q.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
-- Conservative elaboration budgets; these do not change kernel proof checking.
set_option maxHeartbeats 100000
set_option maxRecDepth 300

/-- Reducedness descends through an actual flat surjection, by injectivity of local flat stalk maps. -/
theorem reduced_of_flat_surjective {X Y : Scheme} (f : X ⟶ Y)
    [Flat f] [Surjective f] [AlgebraicGeometry.IsReduced X] : AlgebraicGeometry.IsReduced Y := by
  haveI (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := f.surjective y
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    haveI : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    haveI : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact isReduced_of_injective (f.stalkMap x).hom
      (FaithfulSMul.algebraMap_injective _ _)
  exact isReduced_of_isReduced_stalk Y

/-- Geometric integrality descends through a finite-flat surjection of k-schemes. -/
theorem geometricallyIntegral_of_finite_flat_surjective {k : Type} [Field k]
    {A Q : Over (Spec (.of k))} (q : A ⟶ Q)
    [IsFinite q.left] [Flat q.left] [Surjective q.left] [GeometricallyIntegral A.hom] :
    GeometricallyIntegral Q.hom := by
  constructor
  intro Ω _ y Z a b hp
  let e := hp.isoPullback
  let f : pullback A.hom y ⟶ pullback Q.hom y :=
    pullback.map A.hom y Q.hom y q.left (𝟙 _) (𝟙 _) (by simpa using (Over.w q).symm) (by simp)
  haveI : IsIntegral (pullback A.hom y) :=
    pullback_of_geometrically (GeometricallyIntegral.geometrically_isIntegral (f := A.hom)) Ω y
  haveI : Flat f := MorphismProperty.pullbackMap (P := @Flat)
    inferInstance inferInstance (Over.w q).symm (by simp)
  haveI : Surjective f := MorphismProperty.pullbackMap (P := @Surjective)
    inferInstance inferInstance (Over.w q).symm (by simp)
  haveI : AlgebraicGeometry.IsReduced (pullback Q.hom y) := reduced_of_flat_surjective f
  haveI : IrreducibleSpace ↥(pullback (C := Scheme) Q.hom y) :=
    f.surjective.irreducibleSpace f.continuous
  haveI : IsIntegral (pullback Q.hom y) := isIntegral_of_irreducibleSpace_of_isReduced _
  haveI : Nonempty Z := ⟨e.inv (Nonempty.some (inferInstance : Nonempty ↥(pullback (C := Scheme) Q.hom y)))⟩
  exact isIntegral_of_isOpenImmersion e.hom

/-- A finite surjection preserves the actual schemes' topological Krull dimensions. -/
theorem dimension_eq_of_finite_surjective {X Y : Scheme} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] : topologicalKrullDim X = topologicalKrullDim Y := by
  apply le_antisymm
  · exact topologicalKrullDim_le_of_discrete_fibres f f.continuous f.isDiscrete_preimage_singleton
  · exact L3.StacksPort.Topology.topologicalKrullDim_le_of_surjective_of_specializingMap_or_generalizingMap
      f f.continuous f.surjective (.inl f.isClosedMap.specializingMap)

variable {k : Type} [Field k] (A : PkgI3.AbVar k) (L : A.X.left.Pic)
    (H : L1.FiniteStabilizerScheme A L) (Q : L1.StabilizerQuotient A L H)

/-- The exact action relation embedded into A×A. -/
abbrev quotientRelation : H.K ⊗ A.X ⟶ A.X ⊗ A.X :=
  lift (quotientTarget A L H) (snd H.K A.X)

/-- The exact action relation is monic, because the subgroup inclusion is monic. -/
theorem mono_quotientRelation : Mono (quotientRelation A L H) := by
  haveI : Mono H.j := Over.mono_of_mono_left H.j
  constructor
  intro T u v h
  have ht : u ≫ quotientTarget A L H = v ≫ quotientTarget A L H := by
    simpa using congrArg (· ≫ fst A.X A.X) h
  have hs : u ≫ snd H.K A.X = v ≫ snd H.K A.X := by
    simpa using congrArg (· ≫ snd A.X A.X) h
  have hj : u ≫ fst H.K A.X ≫ H.j = v ≫ fst H.K A.X ≫ H.j := by
    simp only [quotientTarget, MonObj.comp_mul, Category.assoc] at ht
    rw [hs] at ht
    exact mul_right_cancel ht
  have hk : u ≫ fst H.K A.X = v ≫ fst H.K A.X := by
    apply (cancel_mono H.j).1
    simpa only [Category.assoc] using hj
  ext
  · exact congrArg Over.Hom.left hk
  · exact congrArg Over.Hom.left hs

/-- The action relation is an actual closed immersion, not just a relation on geometric points. -/
theorem closed_quotientRelation : IsClosedImmersion (quotientRelation A L H).left := by
  haveI : IsProper (H.K ⊗ A.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : IsSeparated (A.X ⊗ A.X).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : Mono (quotientRelation A L H) := mono_quotientRelation A L H
  haveI : IsProper (quotientRelation A L H).left := isProper_over_hom _
  exact (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩

/-- The relation is exactly the pullback of the quotient's diagonal along q×q. -/
theorem quotientDiagonal_isPullback :
    IsPullback (quotientRelation A L H) (quotientTarget A L H ≫ Q.q)
      (Q.q ⊗ₘ Q.q) (lift (𝟙 Q.Q) (𝟙 Q.Q)) := by
  haveI : Mono (quotientRelation A L H) := mono_quotientRelation A L H
  refine IsPullback.mk' (by ext <;> simp [quotientRelation, Q.kernelPair.w])
    (fun {T} {u v} hu _ => (cancel_mono (quotientRelation A L H)).1 hu) ?_
  intro T c d hc
  have h₁ : c ≫ fst A.X A.X ≫ Q.q = d := by
    simpa using congrArg (· ≫ fst Q.Q Q.Q) hc
  have h₂ : c ≫ snd A.X A.X ≫ Q.q = d := by
    simpa using congrArg (· ≫ snd Q.Q Q.Q) hc
  let r := Q.kernelPair.lift (c ≫ fst A.X A.X) (c ≫ snd A.X A.X) (h₁.trans h₂.symm)
  refine ⟨r, ?_, ?_⟩
  · ext <;> simp [r, quotientRelation]
  · rw [← Category.assoc, Q.kernelPair.lift_fst]
    exact h₁

/-- The quotient is separated: its diagonal descends from the actual closed action relation. -/
theorem quotient_separated : IsSeparated Q.Q.hom := by
  obtain ⟨hfin, hflat, hsurj⟩ := tensor_fpqc Q.q Q.q
  haveI := hfin
  haveI := hflat
  haveI := hsurj
  let δ : Q.Q ⟶ Q.Q ⊗ Q.Q := lift (𝟙 Q.Q) (𝟙 Q.Q)
  haveI : IsClosedImmersion (quotientRelation A L H).left := closed_quotientRelation A L H
  have hp := (quotientDiagonal_isPullback A L H Q).map (Over.forget (Spec (.of k)))
  change IsPullback (quotientRelation A L H).left (quotientTarget A L H ≫ Q.q).left
    (Q.q ⊗ₘ Q.q).left δ.left at hp
  haveI : UniversallyClosed δ.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp
      ⟨⟨hsurj, hflat⟩, inferInstance⟩ inferInstance
  haveI : Mono δ := by dsimp [δ]; infer_instance
  haveI : LocallyOfFiniteType (δ.left ≫ (fst Q.Q Q.Q).left) := by
    have hδ : δ.left ≫ (fst Q.Q Q.Q).left = 𝟙 Q.Q.left := by
      change (δ ≫ fst Q.Q Q.Q).left = _
      simp [δ]
    rw [hδ]
    infer_instance
  haveI : LocallyOfFiniteType δ.left := locallyOfFiniteType_of_comp δ.left (fst Q.Q Q.Q).left
  haveI : IsProper δ.left := {}
  have hc : IsClosedImmersion δ.left :=
    (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩
  constructor
  exact hc

/-- The supplied quotient has geometric integrality, proved by actual field base change. -/
theorem quotient_geometricallyIntegral : GeometricallyIntegral Q.Q.hom :=
  geometricallyIntegral_of_finite_flat_surjective Q.q

/-- The actual quotient and original abelian variety have identical dimensions. -/
theorem quotient_dim_eq : topologicalKrullDim Q.Q.left = A.dim :=
  (dimension_eq_of_finite_surjective Q.q.left).symm

end ZInQ.Contrib.CloudR2Poincare.L4
