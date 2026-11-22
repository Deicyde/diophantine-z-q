import ZInQKernel.Contrib.OneProof.SZThm33.GeomResidueField

/-!
# The fixed part comes from the specified geometric special fibre
-/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit
open ZInQ.FaltingsRestate (isCommMonObj_groupModelO)

namespace SZRaynaud.Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {O : ValuationSubring K} {w : ValuationSubring Ω}
  (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (M : GroupModelO A O)

private abbrev jResBar (O : ValuationSubring K) :=
  Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O)))

private abbrev resTest (O : ValuationSubring K) :=
  ZInQ.HeightSplit.algPt (ResBarO O) (ResBarO O)

private abbrev resTestAmbient := Over.mk (res ≫ base hw)

private def resPointIso :
    (Over.map (jResBar O)).obj (resTest O) ≅ resTestAmbient hw := by
  let e := Scheme.Spec.mapIso (geomResidueEquiv hw).toCommRingCatIso.op
  refine Over.isoMk e ?_
  change Spec.map (CommRingCat.ofHom (geomResidueEquiv hw).toRingHom) ≫ (res ≫ base hw) =
    Spec.map (CommRingCat.ofHom (algebraMap (ResBarO O) (ResBarO O))) ≫ jResBar O
  rw [Algebra.algebraMap_self, show Spec.map (CommRingCat.ofHom (RingHom.id (ResBarO O))) =
    𝟙 (Spec (.of (ResBarO O))) from Spec.map_id _, Category.id_comp,
    ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact geomResidueEquiv_comp hw

/-- The ambient residue points of the model agree with the rational points
of its geometric special fibre over the model's specified algebraic closure. -/
def geomSpecialPointEquiv :
    (resTest O ⟶ geomSpecialFibre M) ≃* (resTestAmbient hw ⟶ M.G) := by
  let F := Over.pullback (jResBar O)
  letI : GrpObj (F.obj M.G) := Functor.grpObjObj
  change (resTest O ⟶ F.obj M.G) ≃* (resTestAmbient hw ⟶ M.G)
  let e := resPointIso hw
  let Φ := (Over.mapPullbackAdj (jResBar O)).homEquiv (resTest O) M.G
  refine {
    toFun := fun p => e.inv ≫ Φ.symm p
    invFun := fun p => Φ (e.hom ≫ p)
    left_inv := fun p => by
      change Φ (e.hom ≫ e.inv ≫ Φ.symm p) = p
      rw [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
    right_inv := fun p => by
      change e.inv ≫ Φ.symm (Φ (e.hom ≫ p)) = p
      rw [Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
    map_mul' := ?_ }
  intro p q
  obtain ⟨p', rfl⟩ := Φ.surjective p
  obtain ⟨q', rfl⟩ := Φ.surjective q
  have h (x y : (Over.map (jResBar O)).obj (resTest O) ⟶ M.G) :
      Φ (x * y) = Φ x * Φ y := by
    dsimp [Φ]
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
      F.map_mul, MonObj.comp_mul]
  rw [← h, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, MonObj.comp_mul]

variable {ℓ : ℕ} [Fact ℓ.Prime]

local instance : IsCommMonObj M.G := isCommMonObj_groupModelO M

theorem isCommMonObj_geomSpecialFibre : IsCommMonObj (geomSpecialFibre M) :=
  Functor.isCommMonObj_obj (F := Over.pullback (jResBar O))

attribute [local instance] isCommMonObj_geomSpecialFibre

/-- The comparison of the two residue point groups induces an isomorphism
on their Tate modules. -/
def geomSpecialTateEquiv : (PkgI3.Tate.T ℓ (Additive (resTest O ⟶ geomSpecialFibre M))) ≃ₗ[ℤ_[ℓ]] (PkgI3.Tate.T ℓ (Additive (resTestAmbient hw ⟶ M.G))) :=
  let e := geomSpecialPointEquiv hw A M
  let f := PkgI3.Tate.map e.toMonoidHom.toAdditive (ℓ := ℓ)
  LinearEquiv.ofBijective f ⟨by
    intro x y h
    apply Subtype.ext
    funext n
    apply Additive.toMul.injective
    apply e.injective
    exact congrArg (fun t : (PkgI3.Tate.T ℓ (Additive (resTestAmbient hw ⟶ M.G))) => Additive.toMul (t.1 n)) h,
    by
      intro y
      refine ⟨PkgI3.Tate.map e.symm.toMonoidHom.toAdditive y, ?_⟩
      apply Subtype.ext
      funext n
      exact congrArg Additive.ofMul (e.apply_symm_apply _)⟩

variable [IsAlgClosed Ω] (hu : IsUnit (ℓ : O))

/-- The geometric special-fibre rational Tate module maps into the original
generic representation. -/
def geomSpecialEmbedRational :
      (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (Additive (resTest O ⟶ geomSpecialFibre M)))) →ₗ[ℚ_[ℓ]]
        (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TΩ A Ω ℓ)) :=
  let e :
      (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (Additive (resTest O ⟶ geomSpecialFibre M)))) ≃ₗ[ℚ_[ℓ]]
        (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (Additive (resTestAmbient hw ⟶ M.G)))) :=
    LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ (geomSpecialTateEquiv hw A M)
  (modelEmbedRationalΩ hw A M hu).comp e.toLinearMap

set_option linter.unusedSectionVars false in
theorem geomSpecialEmbedRational_injective :
    Function.Injective (geomSpecialEmbedRational hw A M hu) :=
  (modelEmbedRationalΩ_injective hw A M hu).comp
    (LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ (geomSpecialTateEquiv hw A M)).injective

/-- The geometric special fibre computes the exact fixed space of a Néron
model at the chosen prolongation. -/
theorem mem_range_geomSpecialEmbedRational_iff [IsDiscreteValuationRing O]
    (hN : M.IsNeronModel) (x : (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (TΩ A Ω ℓ))) :
    x ∈ (geomSpecialEmbedRational hw A M hu).range ↔
      ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ →
        (galTΩ A ℓ σ).baseChange ℚ_[ℓ] x = x := by
  rw [← mem_range_modelEmbedRationalΩ_iff hw A M hu hN]
  let e :
      (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (Additive (resTest O ⟶ geomSpecialFibre M)))) ≃ₗ[ℚ_[ℓ]]
        (TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (Additive (resTestAmbient hw ⟶ M.G)))) :=
    LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ (geomSpecialTateEquiv hw A M)
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.symm y, ?_⟩
    change modelEmbedRationalΩ hw A M hu (e (e.symm y)) = _
    rw [LinearEquiv.apply_symm_apply]

#print axioms geomSpecialEmbedRational_injective
#print axioms mem_range_geomSpecialEmbedRational_iff

end SZRaynaud.Ambient
