import ZInQKernel.Contrib.OneProof.SZThm33.IdentitySpecialFibre
import ZInQKernel.Contrib.OneProof.SZThm33.TateModelNaturality

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit SmoothGroup

namespace SZRaynaud.Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {O : ValuationSubring K} {w : ValuationSubring Ω}
  (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (M N : GroupModelO A O)

/-- The geometric residue point comparison is natural for model maps. -/
theorem geomSpecialPointEquiv_modelHom (i : M.G ⟶ N.G) (x : (ZInQ.HeightSplit.algPt (ResBarO O) (ResBarO O)) ⟶ geomSpecialFibre M) :
    geomSpecialPointEquiv hw A N (x ≫ geomSpecialModelMap M N i) =
      geomSpecialPointEquiv hw A M x ≫ i := by
  let p : (ZInQ.HeightSplit.algPt (ResBarO O) (ResBarO O)) ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))).obj M.G := x
  change _ ≫ ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))).homEquiv (ZInQ.HeightSplit.algPt (ResBarO O) (ResBarO O)) N.G).symm
    (p ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))).map i) =
    (_ ≫ ((Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))).homEquiv (ZInQ.HeightSplit.algPt (ResBarO O) (ResBarO O)) M.G).symm p) ≫ i
  rw [(Over.mapPullbackAdj (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))).homEquiv_naturality_right_symm p i, Category.assoc]

variable {ℓ : ℕ} [Fact ℓ.Prime]

attribute [local instance] isCommMonObj_geomSpecialFibre
attribute [local instance] ZInQ.FaltingsRestate.isCommMonObj_groupModelO

/-- Base change of a group model homomorphism to the geometric residue field
is still a group homomorphism, with the specified group structures. -/
instance geomSpecialModelMap_isMonHom (i : M.G ⟶ N.G) [IsMonHom i] :
    IsMonHom (geomSpecialModelMap M N i) :=
  Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))))) M.G N.G i

theorem geomSpecialTateEquiv_modelHom (i : M.G ⟶ N.G) [IsMonHom i]
    (x : PkgI3.Tate.T ℓ (Additive ((ZInQ.HeightSplit.algPt (ResBarO O) (ResBarO O)) ⟶ geomSpecialFibre M))) :
    geomSpecialTateEquiv hw A N (mapModelTate (geomSpecialModelMap M N i) (Spec.map (CommRingCat.ofHom (algebraMap (ResBarO O) (ResBarO O)))) x) =
      mapModelTate i (res ≫ base hw) (geomSpecialTateEquiv hw A M x) := by
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (geomSpecialPointEquiv_modelHom hw A M N i (Additive.toMul (x.1 n)))

variable [IsAlgClosed Ω] (hu : IsUnit (ℓ : O))

/-- Specialization in the integral Tate module, using geometric residue
points over the model's specified algebraic closure of its residue field. -/
def geomSpecialEmbedTate :
    PkgI3.Tate.T ℓ (Additive ((ZInQ.HeightSplit.algPt (ResBarO O) (ResBarO O)) ⟶ geomSpecialFibre M)) →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
  (modelEmbedTate hw A M hu).comp (geomSpecialTateEquiv hw A M).toLinearMap

theorem geomSpecialEmbedTate_baseChange :
    (geomSpecialEmbedTate hw A M hu).baseChange ℚ_[ℓ] = geomSpecialEmbedRational hw A M hu := by
  change (modelEmbedTate hw A M hu ∘ₗ
    (geomSpecialTateEquiv hw A M).toLinearMap).baseChange ℚ_[ℓ] = _
  exact LinearMap.baseChange_comp (A := ℚ_[ℓ]) (geomSpecialTateEquiv hw A M).toLinearMap
    (modelEmbedTate hw A M hu)

/-- A model map chosen with the prescribed generic identification preserves
the geometric special-fibre embedding in the integral Tate module. -/
theorem geomSpecialEmbedTate_modelHom (i : M.G ⟶ N.G) [IsMonHom i]
    (hi : (Over.pullback (jO O)).map i ≫ N.gen.hom = M.gen.hom)
    (x : PkgI3.Tate.T ℓ (Additive ((ZInQ.HeightSplit.algPt (ResBarO O) (ResBarO O)) ⟶ geomSpecialFibre M))) :
    geomSpecialEmbedTate hw A N hu (mapModelTate (geomSpecialModelMap M N i) (Spec.map (CommRingCat.ofHom (algebraMap (ResBarO O) (ResBarO O)))) x) =
      geomSpecialEmbedTate hw A M hu x := by
  change modelEmbedTate hw A N hu
      (geomSpecialTateEquiv hw A N (mapModelTate (geomSpecialModelMap M N i) (Spec.map (CommRingCat.ofHom (algebraMap (ResBarO O) (ResBarO O)))) x)) =
    modelEmbedTate hw A M hu (geomSpecialTateEquiv hw A M x)
  rw [geomSpecialTateEquiv_modelHom hw A M N, modelEmbedTate_modelHom hw A M N hu i hi]

end SZRaynaud.Ambient
