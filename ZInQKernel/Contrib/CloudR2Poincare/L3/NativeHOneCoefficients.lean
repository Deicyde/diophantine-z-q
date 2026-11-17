import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.GlobalSections.Proper
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Proper
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Free
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Native H⁰ with actual finite constant coefficients

Proper geometric integrality identifies the actual global functions with the
base field. The actual native H-zero map carries this to H⁰(O_X). Finite-free
coefficients are the actual sheaf coproducts on their basis, not a supplied
cohomological rank formula or a replacement coefficient object.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped BigOperators

namespace ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The actual base-field-to-native-H-zero map for the structure sheaf. -/
def unitHZeroFromField : k →ₗ[k] (Scheme.Modules.unit X).H 0 :=
  { toFun := fun c => (Scheme.Modules.H.zeroLinearEquiv (Scheme.Modules.unit X)).symm
      (Scheme.globalSectionsRingHom k (X := X) c)
    map_add' := fun a b => by
      rw [map_add, map_add]
    map_smul' := fun a b => by
      change (Scheme.Modules.H.zeroLinearEquiv (Scheme.Modules.unit X)).symm
        (Scheme.globalSectionsRingHom k (X := X) (a * b)) =
        Scheme.globalSectionsRingHom k (X := X) a •
          (Scheme.Modules.H.zeroLinearEquiv (Scheme.Modules.unit X)).symm
            (Scheme.globalSectionsRingHom k (X := X) b)
      rw [map_mul]
      exact (Scheme.Modules.H.zeroLinearEquiv (Scheme.Modules.unit X)).symm.map_smul _ _ }

/-- The structure map on actual global functions is bijective under the genuine
proper/geometrically-integral hypotheses, hence so is the native H-zero map. -/
theorem unitHZeroFromField_bijective
    [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))] :
    Function.Bijective (unitHZeroFromField (k := k) (X := X)) := by
  have hσ : Function.Bijective (Scheme.globalSectionsRingHom k (X := X)) :=
    (AlgebraicGeometry.bijective_appTop_of_isProper_of_geometricallyIntegral
      (X ↘ Spec (.of k))).comp
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)
  exact (Scheme.Modules.H.zeroLinearEquiv (Scheme.Modules.unit X)).symm.bijective.comp hσ

/-- Actual field-linear H⁰(O_X) comparison, not a dimension-selected equivalence. -/
def unitHZeroLinearEquiv
    [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))] :
    k ≃ₗ[k] (Scheme.Modules.unit X).H 0 :=
  LinearEquiv.ofBijective unitHZeroFromField unitHZeroFromField_bijective

/-- The native structure-sheaf H-zero rank is exactly one over every field. -/
theorem unit_finrankH_zero
    [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))] :
    Module.finrank k ((Scheme.Modules.unit X).H 0) = 1 :=
  (unitHZeroLinearEquiv (k := k) (X := X)).finrank_eq.symm.trans (Module.finrank_self k)

/-- Properness gives actual finite native cohomology of O_X in every degree. -/
theorem finite_unit_H [IsProper (X ↘ Spec (.of k))] (q : ℕ) :
    Module.Finite k ((Scheme.Modules.unit X).H q) :=
  Scheme.Modules.hasFiniteH_of_isProper (X ↘ Spec (.of k)) (Scheme.Modules.unit X) q

/-- Finite constant coefficients have finite actual native cohomology. -/
theorem finite_free_H [IsProper (X ↘ Spec (.of k))] (I : Type u) [Finite I] (q : ℕ) :
    Module.Finite k (Scheme.Modules.H (X := X) (SheafOfModules.free (R := X.ringCatSheaf) I) q) := by
  haveI : Module.Finite k ((Scheme.Modules.unit X).H q) := finite_unit_H q
  exact Scheme.Modules.finite_H_sigma (p := X ↘ Spec (.of k))
    (fun _ : I => Scheme.Modules.unit X) q (fun _ => inferInstance)

/-- Actual finite-free constant coefficients have H⁰ of their literal rank. -/
theorem free_finrankH_zero
    [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))]
    (I : Type u) [Fintype I] :
    Module.finrank k (Scheme.Modules.H (X := X) (SheafOfModules.free (R := X.ringCatSheaf) I) 0) = Fintype.card I := by
  haveI : Module.Finite k ((Scheme.Modules.unit X).H 0) := finite_unit_H 0
  haveI : HasBiproduct (fun _ : I => Scheme.Modules.unit X) :=
    HasBiproduct.of_hasCoproduct _
  let e : SheafOfModules.free (R := X.ringCatSheaf) I ≅
      ⨁ fun _ : I => Scheme.Modules.unit X :=
    (biproduct.isoCoproduct (fun _ : I => Scheme.Modules.unit X)).symm
  calc
    Module.finrank k (Scheme.Modules.H (X := X) (SheafOfModules.free (R := X.ringCatSheaf) I) 0) =
        (⨁ fun _ : I => Scheme.Modules.unit X).finrankH k 0 :=
      Scheme.Modules.finrankH_congr k e 0
    _ = ∑ _ : I, (Scheme.Modules.unit X).finrankH k 0 :=
      Scheme.Modules.finrankH_of_isBilimit k
        (biproduct.isBilimit (fun _ : I => Scheme.Modules.unit X)) 0
    _ = Fintype.card I := by
      simp only [Scheme.Modules.finrankH, unit_finrankH_zero, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, mul_one]

/-- The actual pullback of the tilde of a finite vector space is an actual finite
free sheaf with the vector space's own finite basis. The raised basis index
preserves the full universe-u statement. -/
def fieldCoefficientFreeIso (g : X ⟶ Spec (.of k)) (V : ModuleCat.{u} k)
    [Module.Finite k V] :
    (Scheme.Modules.pullback g).obj ((tilde.functor (.of k)).obj V) ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin (Module.finrank k V))) := by
  let I := ULift.{u} (Fin (Module.finrank k V))
  let b : Module.Basis I k V := (Module.finBasis k V).reindex Equiv.ulift.symm
  let coordinates : V ≅ ModuleCat.of k (I →₀ k) := b.repr.toModuleIso
  exact (Scheme.Modules.pullback g).mapIso
      ((tilde.functor (.of k)).mapIso coordinates ≪≫ tildeFinsupp I) ≪≫
    Scheme.Modules.pullbackFreeIso g I

/-- H⁰ of the actual finite constant coefficient has dimension equal to the
actual vector space's dimension, using O_X's genuine rank-one H⁰. -/
theorem fieldCoefficient_finrankH_zero
    [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))]
    (V : ModuleCat.{u} k) [Module.Finite k V] :
    Module.finrank k
      (((Scheme.Modules.pullback (X ↘ Spec (.of k))).obj
        ((tilde.functor (.of k)).obj V)).H 0) = Module.finrank k V := by
  calc
    _ = Module.finrank k
        (Scheme.Modules.H (X := X) (SheafOfModules.free (R := X.ringCatSheaf)
          (ULift.{u} (Fin (Module.finrank k V)))) 0) :=
      Scheme.Modules.finrankH_congr k (fieldCoefficientFreeIso (X ↘ Spec (.of k)) V) 0
    _ = Module.finrank k V := by rw [free_finrankH_zero]; simp

/-- Finiteness of the same actual constant coefficient in every cohomology degree. -/
theorem finite_fieldCoefficient_H [IsProper (X ↘ Spec (.of k))]
    (V : ModuleCat.{u} k) [Module.Finite k V] (q : ℕ) :
    Module.Finite k
      (((Scheme.Modules.pullback (X ↘ Spec (.of k))).obj
        ((tilde.functor (.of k)).obj V)).H q) := by
  exact Scheme.Modules.finite_H_of_iso (p := X ↘ Spec (.of k))
    (fieldCoefficientFreeIso (X ↘ Spec (.of k)) V).symm q
      (finite_free_H (k := k) (X := X) (ULift.{u} (Fin (Module.finrank k V))) q)

end ZInQ.Contrib.CloudR2Poincare.L3.HOneCoefficients
