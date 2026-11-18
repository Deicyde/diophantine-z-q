import OriginalPointBindingFirst
import InertiaNeronGlueV002

/-!
# Actual integral lifts of inertia- and Frobenius-fixed original torsion points

The inertia descent theorem and the genuine Néron mapping property construct
unique integral torsion sections of the original abelian variety model.
The original generic-point covariance and separatedness then prove that
these sections are fixed by the indicated decomposition automorphism.
No integral lift or desired fixedness is supplied as a premise.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace SemistableGeometry.OriginalFixedTorsion

open SemistableGeometry.IntegralGalois
open SemistableGeometry.OriginalPointBinding

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/-- The literal subgroup of original torsion points fixed by inertia and the indicated automorphism. -/
def fixedLevel (m : ℕ) (σ : Ω ≃ₐ[K] Ω) (w : ValuationSubring Ω) (A : PkgI3.AbVar K) :
    Subgroup (A.Pt Ω) where
  carrier := {x | x ^ m = 1 ∧
    (∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ → A.galAct τ x = x) ∧ A.galAct σ x = x}
  one_mem' := ⟨one_pow m, fun τ _ ↦ map_one (A.galAct τ), map_one (A.galAct σ)⟩
  mul_mem' {x y} hx hy := by
    refine ⟨?_, ?_, ?_⟩
    · rw [mul_pow, hx.1, hy.1, _root_.one_mul]
    · intro τ hτ
      rw [map_mul, hx.2.1 τ hτ, hy.2.1 τ hτ]
    · rw [map_mul, hx.2.2, hy.2.2]
  inv_mem' {x} hx := by
    refine ⟨?_, ?_, ?_⟩
    · rw [inv_pow, hx.1, inv_one]
    · intro τ hτ
      rw [map_inv, hx.2.1 τ hτ]
    · rw [map_inv, hx.2.2]

variable (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [IsSeparated N.hom]

/-- The genuine per-point integral torsion lift, chosen from the already proved inertia descent theorem. -/
def integralLift {A : PkgI3.AbVar K}
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
      IsMonHom gen.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback (base (O := O))).map f ≫ gen.hom))
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (m : ℕ) (σ : Ω ≃ₐ[K] Ω) (x : fixedLevel m σ w A) : valuationDomain w hw ⟶ N :=
  Classical.choose (ExistsUnique.exists
    (InertiaNeronGlue.inertia_fixed_torsion_section O w hw gen hgen hN x.1 x.2.2.1 m x.2.1))

/-- The constructed lift has its actual original generic point and original torsion order. -/
theorem integralLift_spec {A : PkgI3.AbVar K}
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
      IsMonHom gen.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback (base (O := O))).map f ≫ gen.hom))
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (m : ℕ) (σ : Ω ≃ₐ[K] Ω) (x : fixedLevel m σ w A) :
    integralLift N gen hgen hN w hw m σ x ^ m = 1 ∧
      originalPoint N gen w hw (integralLift N gen hgen hN w hw m σ x) = x.1 := by
  exact Classical.choose_spec (ExistsUnique.exists
    (InertiaNeronGlue.inertia_fixed_torsion_section O w hw gen hgen hN x.1 x.2.2.1 m x.2.1))

/-- These actual lifts are fixed by the actual decomposition action, not a modeled operator. -/
theorem integralLift_fixed {A : PkgI3.AbVar K}
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
      IsMonHom gen.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback (base (O := O))).map f ≫ gen.hom))
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (m : ℕ) (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K) (x : fixedLevel m σ w A) :
    valuationActionArrow w hw σ hD ≫ integralLift N gen hgen hN w hw m σ x =
      integralLift N gen hgen hN w hw m σ x := by
  apply integral_fixed_of_original_fixed N gen w hw σ hD
  rw [(integralLift_spec N gen hgen hN w hw m σ x).2]
  exact x.2.2.2

end SemistableGeometry.OriginalFixedTorsion
