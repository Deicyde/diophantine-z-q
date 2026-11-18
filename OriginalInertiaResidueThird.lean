import OriginalTorusPointMultiplierThird
import HenselDivision.ValuationPointLiftV003

/-!
# Original inertia-fixed torsion and actual residue torsion

Prime-to-residue-characteristic integral torsion is inertia-fixed, by
actual reduction invariance and torsion uniqueness. Conversely the genuine
Néron inertia-descent theorem supplies an integral section for every
original inertia-fixed torsion point. The resulting multiplicative
correspondence composes with the actual residue torsion lifting theorem.
No blanket integrality of the original geometric point group is asserted.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace SemistableGeometry.OriginalInertiaResidue

open SemistableGeometry.IntegralGalois
open SemistableGeometry.OriginalPointBinding
open SemistableGeometry.OriginalTorusPointMultiplier

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/-- The subgroup consists of literal ORIGINAL points killed by m and fixed by every inertia element. -/
def inertiaTorsion (A : PkgI3.AbVar K) (w : ValuationSubring Ω) (m : ℕ) : Subgroup (A.Pt Ω) where
  carrier := {x | x ^ m = 1 ∧ ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ → A.galAct τ x = x}
  one_mem' := ⟨one_pow m, fun τ _ => map_one (A.galAct τ)⟩
  mul_mem' {x y} hx hy := by
    refine ⟨?_, fun τ hτ => ?_⟩
    · rw [mul_pow, hx.1, hy.1, _root_.one_mul]
    · rw [map_mul, hx.2 τ hτ, hy.2 τ hτ]
  inv_mem' {x} hx := by
    refine ⟨?_, fun τ hτ => ?_⟩
    · rw [inv_pow, hx.1, inv_one]
    · rw [map_inv, hx.2 τ hτ]

variable {A : PkgI3.AbVar K} (N : Over (Spec (CommRingCat.of O))) [GrpObj N]
  [Smooth N.hom] [IsSeparated N.hom]
variable (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
variable (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
  IsMonHom gen.hom)
variable (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
  Function.Bijective (fun f : Y ⟶ N => (Over.pullback (base (O := O))).map f ≫ gen.hom))
variable (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)

include hgen hN in
/-- Actual integral m-torsion, m invertible in O, has an inertia-fixed ORIGINAL generic point. -/
theorem integral_torsion_inertia_fixed (m : ℕ) (hm : IsUnit (m : O))
    (a : valuationDomain w hw ⟶ N) (ha : a ^ m = 1) :
    ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
      A.galAct τ (originalPoint N gen w hw a) = originalPoint N gen w hw a := by
  letI : IsCommMonObj N := SemistableGeometry.NeronCommutativityCore.model_commutative N gen hgen hN
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  intro τ hτ
  have hat : (valuationActionArrow w hw τ hτ.1 ≫ a) ^ m = 1 := by
    rw [← MonObj.comp_pow, ha, MonObj.comp_one]
  have hred := inertia_section_reduction N w hw τ hτ a
  have heq := HenselDivision.valuation_point_torsion_eq_of_reduction w hw N m m hm hm
    (reductionArrow w hw) rfl (valuationActionArrow w hw τ hτ.1 ≫ a) a hat ha hred
  rw [← originalPoint_covariance N gen w hw τ hτ.1 a, heq]

/-- The original generic map is an actual homomorphism from integral torsion into original inertia-fixed torsion. -/
def integralGenericHom (m : ℕ) (hm : IsUnit (m : O)) :
    letI : IsCommMonObj N := SemistableGeometry.NeronCommutativityCore.model_commutative N gen hgen hN
    HenselDivision.torsionPts N (valuationDomain w hw) m →* inertiaTorsion A w m := by
  letI : IsCommMonObj N := SemistableGeometry.NeronCommutativityCore.model_commutative N gen hgen hN
  refine
    { toFun := fun a => ⟨originalPoint N gen w hw a.1, ?_⟩
      map_one' := ?_
      map_mul' := fun a b => ?_ }
  · refine ⟨?_, integral_torsion_inertia_fixed N gen hgen hN w hw m hm a.1
      ((HenselDivision.mem_torsionPts _).1 a.2)⟩
    rw [← originalPoint_pow N gen hgen w hw a.1 m, (HenselDivision.mem_torsionPts _).1 a.2]
    exact NeronInvariantTorsion.genericFibre_one O w hw gen hgen
  · apply Subtype.ext
    exact NeronInvariantTorsion.genericFibre_one O w hw gen hgen
  · apply Subtype.ext
    exact NeronInvariantTorsion.genericFibre_mul O w hw gen hgen a.1 b.1

/-- Surjectivity uses original inertia descent, while injectivity uses actual separatedness. -/
theorem integralGenericHom_bijective (m : ℕ) (hm : IsUnit (m : O)) :
    letI : IsCommMonObj N := SemistableGeometry.NeronCommutativityCore.model_commutative N gen hgen hN
    Function.Bijective (integralGenericHom N gen hgen hN w hw m hm) := by
  letI : IsCommMonObj N := SemistableGeometry.NeronCommutativityCore.model_commutative N gen hgen hN
  constructor
  · intro a b h
    apply Subtype.ext
    exact originalPoint_injective N gen w hw (congrArg Subtype.val h)
  · intro x
    obtain ⟨a, ha, hax⟩ := ExistsUnique.exists
      (InertiaNeronGlue.inertia_fixed_torsion_section O w hw gen hgen hN x.1 x.2.2 m x.2.1)
    exact ⟨⟨a, (HenselDivision.mem_torsionPts _).2 ha⟩, Subtype.ext hax⟩

/-- This is an actual multiplicative correspondence, not a supplied point-equivalence premise. -/
def inertiaIntegralEquiv (m : ℕ) (hm : IsUnit (m : O)) :
    letI : IsCommMonObj N := SemistableGeometry.NeronCommutativityCore.model_commutative N gen hgen hN
    HenselDivision.torsionPts N (valuationDomain w hw) m ≃* inertiaTorsion A w m := by
  letI : IsCommMonObj N := SemistableGeometry.NeronCommutativityCore.model_commutative N gen hgen hN
  exact MulEquiv.ofBijective (integralGenericHom N gen hgen hN w hw m hm)
    (integralGenericHom_bijective N gen hgen hN w hw m hm)

/-- Original inertia-fixed torsion is the ACTUAL residue torsion over Spec O, using the genuine residue lift. -/
def inertiaResidueEquiv (m : ℕ) (hm : IsUnit (m : O)) :
    letI : IsCommMonObj N := SemistableGeometry.NeronCommutativityCore.model_commutative N gen hgen hN
    inertiaTorsion A w m ≃* HenselDivision.torsionPts N (residueDomain w hw) m := by
  letI : IsCommMonObj N := SemistableGeometry.NeronCommutativityCore.model_commutative N gen hgen hN
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  exact (inertiaIntegralEquiv N gen hgen hN w hw m hm).symm.trans
    (HenselDivision.valuationTorsionPointRestrictEquiv w hw N m hm (reductionArrow w hw) rfl)

end SemistableGeometry.OriginalInertiaResidue
