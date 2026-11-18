import ActualResidueFrobeniusThird
import SpecialPointBindingThird
import HenselDivision.ValuationStrictHenselV003
import RaynaudWild.ResTFrobeniusV003

/-!
# The actual geometric-residue algebra and the native torus point domain

Algebraic closedness of the valuation residue field is derived from the
original algebraic closure, without a discrete-valuation hypothesis on w.
The residue-field algebraic closure embeds over the actual residue base
map. Its induced algebra structure has the original base map as composite.
Thus the torus supplier's geometric point domain is the actual special
point domain, with an explicit identity-underlying isomorphism.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace SemistableGeometry.ActualResidueTorus

open SemistableGeometry.ActualResidueFrobenius
open SemistableGeometry.SpecialPointBinding
open RaynaudWild.FrobDescent

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
variable {w : ValuationSubring Ω}

/-- An actual base-residue-field embedding of its algebraic closure into the valuation residue field. -/
def barEmbedding (hw : w.comap (algebraMap K Ω) = O) :
    letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
    AlgebraicClosure (IsLocalRing.ResidueField O) →ₐ[IsLocalRing.ResidueField O]
      IsLocalRing.ResidueField w := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  letI : IsAlgClosed (IsLocalRing.ResidueField w) := HenselDivision.isAlgClosed_residueField w
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
  exact IsAlgClosed.lift

/-- The algebra structure is induced by that genuine field embedding. -/
def barAlgebra (hw : w.comap (algebraMap K Ω) = O) :
    Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) :=
  by
    letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
    exact (barEmbedding hw).toRingHom.toAlgebra

/-- Its composite with the original residue base is the original residue map, not an assumed comparison. -/
theorem barAlgebra_comp (hw : w.comap (algebraMap K Ω) = O) :
    letI : Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) := barAlgebra hw
    (algebraMap (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w)).comp
      (algebraMap (IsLocalRing.ResidueField O) (AlgebraicClosure (IsLocalRing.ResidueField O))) =
        residueBase hw := by
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
  change (barEmbedding hw).toRingHom.comp
    (algebraMap (IsLocalRing.ResidueField O) (AlgebraicClosure (IsLocalRing.ResidueField O))) =
      residueBase hw
  exact (barEmbedding hw).comp_algebraMap

/-- The torus supplier's geometric point object is the actual residue special-point object. -/
theorem kPt_eq_specialDomain (hw : w.comap (algebraMap K Ω) = O) :
    letI : Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) := barAlgebra hw
    kPt (k := IsLocalRing.ResidueField O) (Ω := AlgebraicClosure (IsLocalRing.ResidueField O))
      (IsLocalRing.ResidueField w) = specialDomain hw := by
  letI : Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) := barAlgebra hw
  change Over.mk (Spec.map (CommRingCat.ofHom
    ((algebraMap (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w)).comp
      (algebraMap (IsLocalRing.ResidueField O) (AlgebraicClosure (IsLocalRing.ResidueField O)))))) =
    Over.mk (Spec.map (CommRingCat.ofHom (residueBase hw)))
  rw [barAlgebra_comp]

/-- The comparison is an actual over-isomorphism with identity underlying Spec map. -/
def torusDomainIso (hw : w.comap (algebraMap K Ω) = O) :
    letI : Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) := barAlgebra hw
    kPt (k := IsLocalRing.ResidueField O) (Ω := AlgebraicClosure (IsLocalRing.ResidueField O))
      (IsLocalRing.ResidueField w) ≅ specialDomain hw := by
  letI : Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w) := barAlgebra hw
  have hbase : (kPt (k := IsLocalRing.ResidueField O)
      (Ω := AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w)).hom =
      (specialDomain hw).hom := by
    change Spec.map (CommRingCat.ofHom
      ((algebraMap (AlgebraicClosure (IsLocalRing.ResidueField O)) (IsLocalRing.ResidueField w)).comp
        (algebraMap (IsLocalRing.ResidueField O) (AlgebraicClosure (IsLocalRing.ResidueField O))))) =
      Spec.map (CommRingCat.ofHom (residueBase hw))
    rw [barAlgebra_comp]
  refine ⟨Over.homMk (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField w))))
      ((Category.id_comp _).trans hbase.symm),
    Over.homMk (𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField w))))
      ((Category.id_comp _).trans hbase), ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact Category.id_comp _
  · apply Over.OverMorphism.ext
    exact Category.id_comp _

end SemistableGeometry.ActualResidueTorus
