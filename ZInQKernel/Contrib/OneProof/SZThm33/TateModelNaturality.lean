import ZInQKernel.Contrib.OneProof.SZThm33.GeomSpecialTate
import ZInQKernel.Contrib.OneProof.DirectWeil.NeronModelComparison

noncomputable section

open CategoryTheory AlgebraicGeometry Limits CartesianMonoidalCategory MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace SmoothGroup

variable {S : Type} [CommRing S] {X Y : Over (Spec (.of S))}
  [GrpObj X] [GrpObj Y] [IsCommMonObj X] [IsCommMonObj Y]
  {ℓ : ℕ} [Fact ℓ.Prime] (f : X ⟶ Y) [IsMonHom f]

/-- Postcompose Tate towers of points with a homomorphism of the group models. -/
def mapModelTate {T : Scheme} (g : T ⟶ Spec (.of S)) :
    PkgI3.Tate.T ℓ (Additive (Over.mk g ⟶ X)) →ₗ[ℤ_[ℓ]]
      PkgI3.Tate.T ℓ (Additive (Over.mk g ⟶ Y)) :=
  PkgI3.Tate.map (IsMonHom.monoidHom f _).toAdditive

theorem mapModelTate_restrict {T T' : Scheme} (g : T ⟶ Spec (.of S)) (a : T' ⟶ T)
    (x : PkgI3.Tate.T ℓ (Additive (Over.mk g ⟶ X))) :
    restrictTate a (mapModelTate f g x) = mapModelTate f (a ≫ g) (restrictTate a x) := by
  apply Subtype.ext
  funext n
  apply Additive.toMul.injective
  let c : Over.mk (a ≫ g) ⟶ Over.mk g := Over.homMk a rfl
  change c ≫ (Additive.toMul (x.1 n) ≫ f) = (c ≫ Additive.toMul (x.1 n)) ≫ f
  exact (Category.assoc c _ f).symm

variable [Smooth X.hom] [Smooth Y.hom] {R : Type} [CommRing R] [HenselianLocalRing R]
  {T : Scheme} (g : Spec (.of R) ⟶ Spec (.of S)) (hu : IsUnit (ℓ : S)) (a : T ⟶ Spec (.of R))

/-- The unique lift of a residue Tate tower commutes with morphisms of smooth group models. -/
theorem liftTateFromResidue_mapModelTate
    (x : PkgI3.Tate.T ℓ (Additive (Over.mk ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) ⟶ X))) :
    liftTateFromResidue g hu a (mapModelTate f ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) x) =
      mapModelTate f (a ≫ g) (liftTateFromResidue g hu a x) := by
  let ex := LinearEquiv.ofBijective _ (restrictTate_bijective_of_residue (X := X) g hu)
  let ey := LinearEquiv.ofBijective _ (restrictTate_bijective_of_residue (X := Y) g hu)
  have hxy : ey.symm (mapModelTate f ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) x) = mapModelTate f g (ex.symm x) := by
    apply ey.injective
    rw [LinearEquiv.apply_symm_apply]
    change mapModelTate f ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) x =
      restrictTate (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) (mapModelTate f g (ex.symm x))
    rw [mapModelTate_restrict]
    change mapModelTate f ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) x =
      mapModelTate f ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) (ex (ex.symm x))
    rw [LinearEquiv.apply_symm_apply]
  change restrictTate a (ey.symm (mapModelTate f ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ g) x)) =
    mapModelTate f (a ≫ g) (restrictTate a (ex.symm x))
  rw [hxy, mapModelTate_restrict]

end SmoothGroup

namespace SZRaynaud.Ambient

open ReductSplit SmoothGroup
open ZInQ.FaltingsRestate (isCommMonObj_groupModelO)

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  {O : ValuationSubring K} {w : ValuationSubring Ω} (hw : w.comap (algebraMap K Ω) = O)
  (A : PkgI3.AbVar K) (M N : GroupModelO A O)

local instance : IsCommMonObj M.G := isCommMonObj_groupModelO M
local instance : IsCommMonObj N.G := isCommMonObj_groupModelO N

theorem genPtHom_modelHom (i : M.G ⟶ N.G)
    (hi : (Over.pullback (jO O)).map i ≫ N.gen.hom = M.gen.hom) (x : Over.mk (gen (w := w) ≫ base hw) ⟶ M.G) :
    genPtHom hw A N (x ≫ i) = genPtHom hw A M x := by
  change ((Over.mapPullbackAdj (jO O)).homEquiv _ _ (_ ≫ (x ≫ i))) ≫
    N.gen.hom = ((Over.mapPullbackAdj (jO O)).homEquiv _ _ (_ ≫ x)) ≫ M.gen.hom
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right, Category.assoc, hi]

variable [IsAlgClosed Ω] {ℓ : ℕ} [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

/-- A model map compatible with the generic identifications preserves the
image in the generic Tate module of each residue Tate tower. -/
theorem modelEmbedTate_modelHom (i : M.G ⟶ N.G) [IsMonHom i]
    (hi : (Over.pullback (jO O)).map i ≫ N.gen.hom = M.gen.hom)
    (x : PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ M.G))) :
    modelEmbedTate hw A N hu (mapModelTate i (res ≫ base hw) x) =
      modelEmbedTate hw A M hu x := by
  have := henselianLocalRing_of_valuationSubring w
  unfold modelEmbedTate embedTate
  simp only [LinearMap.comp_apply]
  rw [liftTateFromResidue_mapModelTate]
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (genPtHom_modelHom hw A M N i hi _)

theorem modelEmbedTate_comparison (hN : N.IsNeronModel)
    (x : PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hw) ⟶ M.G))) :
    letI : IsMonHom (neronModelComparison M N hN) := neronModelComparison_hom M N hN
    modelEmbedTate hw A N hu (mapModelTate (neronModelComparison M N hN) (res ≫ base hw) x) =
      modelEmbedTate hw A M hu x :=
  letI : IsMonHom (neronModelComparison M N hN) := neronModelComparison_hom M N hN
  modelEmbedTate_modelHom hw A M N hu _ (neronModelComparison_generic M N hN) x

end SZRaynaud.Ambient
