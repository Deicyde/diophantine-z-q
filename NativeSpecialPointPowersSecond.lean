import SpecialPointBindingThird

/-!
# Multiplicativity of the actual special-point lift

The actual pullback lift equals the map/pullback adjunction transport after
an identity-underlying comparison of the two original residue domains.
The genuine group structure induced by base change makes this transport
multiplicative, hence it preserves all powers. No proxy point action or
power-preservation hypothesis is introduced.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace SemistableGeometry.NativeSpecialPointPowers

open SemistableGeometry.IntegralGalois
open SemistableGeometry.SpecialPointBinding

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
variable {w : ValuationSubring Ω}

/-- The mapped geometric residue domain is the actual original residue domain. -/
def domainOverIso (hw : w.comap (algebraMap K Ω) = O) :
    (Over.map (specialBase (O := O))).obj (specialDomain hw) ≅ residueDomain w hw :=
  Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (specialDomain_base hw).symm)

/-- The actual Spec/pullback formula is the genuine adjunction point transport. -/
theorem specialPoint_eq_adjunction (hw : w.comap (algebraMap K Ω) = O)
    (N : Over (Spec (CommRingCat.of O))) (a : residueDomain w hw ⟶ N) :
    specialPoint hw N a =
      (Over.mapPullbackAdj (specialBase (O := O))).homEquiv (specialDomain hw) N
        ((domainOverIso hw).hom ≫ a) := by
  let E := (Over.mapPullbackAdj (specialBase (O := O))).homEquiv (specialDomain hw) N
  apply E.symm.injective
  rw [Equiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  change (specialPoint hw N a).left ≫ pullback.fst N.hom (specialBase (O := O)) =
    𝟙 (Spec (CommRingCat.of (IsLocalRing.ResidueField w))) ≫ a.left
  exact (specialPoint_fst hw N a).trans (Category.id_comp _).symm

/-- Actual residue-point multiplication is respected by the actual special-fibre lift. -/
theorem specialPoint_mul (hw : w.comap (algebraMap K Ω) = O)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] (a b : residueDomain w hw ⟶ N) :
    letI : GrpObj (specialFibre N) := Functor.grpObjObj
    specialPoint hw N (a * b) = specialPoint hw N a * specialPoint hw N b := by
  letI : GrpObj (specialFibre N) := Functor.grpObjObj
  rw [specialPoint_eq_adjunction, specialPoint_eq_adjunction, specialPoint_eq_adjunction,
    MonObj.comp_mul, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.homEquiv_unit, Functor.map_mul, MonObj.comp_mul]

/-- The actual special-point lift is a monoid homomorphism. -/
def specialPointHom (hw : w.comap (algebraMap K Ω) = O)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] :
    letI : GrpObj (specialFibre N) := Functor.grpObjObj
    (residueDomain w hw ⟶ N) →* (specialDomain hw ⟶ specialFibre N) := by
  letI : GrpObj (specialFibre N) := Functor.grpObjObj
  refine {toFun := specialPoint hw N, map_one' := ?_, map_mul' := specialPoint_mul hw N}
  rw [specialPoint_eq_adjunction, MonObj.comp_one, Adjunction.homEquiv_unit,
    Functor.map_one, MonObj.comp_one]

/-- Powers, including the torsion equations, are preserved in the actual special fibre. -/
theorem specialPoint_pow (hw : w.comap (algebraMap K Ω) = O)
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] (a : residueDomain w hw ⟶ N) (q : ℕ) :
    letI : GrpObj (specialFibre N) := Functor.grpObjObj
    specialPoint hw N (a ^ q) = specialPoint hw N a ^ q := by
  letI : GrpObj (specialFibre N) := Functor.grpObjObj
  exact map_pow (specialPointHom hw N) a q

end SemistableGeometry.NativeSpecialPointPowers
