import ZInQKernel.Contrib.CloudR2Poincare.L1.NativeCohomologyLocus
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Semicontinuity of the ACTUAL finite-free sheaf mapping cone

H-72 L6. Actual cone components are the native biproducts P^(n+1) plus D^n.
Their free-sheaf isomorphisms are obtained from the actual biproduct/coprod
and free-sum maps, then the native L1/W07 fibre-homology semicontinuity.
No model is selected from ranks; no cone nonnegativity is assumed.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L6

/-- A genuine binary biproduct of finite-free native module sheaves is finite free. -/
theorem finiteFree_biprod {Y : Scheme.{u}} (M N : Y.Modules)
    (freeM : ∃ r : ℕ, Nonempty (M ≅ SheafOfModules.free
      (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))
    (freeN : ∃ r : ℕ, Nonempty (N ≅ SheafOfModules.free
      (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))) :
    ∃ r : ℕ, Nonempty (M ⊞ N ≅ SheafOfModules.free
      (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) := by
  classical
  obtain ⟨rM, ⟨eM⟩⟩ := freeM
  obtain ⟨rN, ⟨eN⟩⟩ := freeN
  let I := ULift.{u} (Fin rM)
  let J := ULift.{u} (Fin rN)
  let r := Fintype.card (I ⊕ J)
  let reindex : I ⊕ J ≃ ULift.{u} (Fin r) :=
    (Fintype.equivFin (I ⊕ J)).trans Equiv.ulift.symm
  refine ⟨r, ⟨?_⟩⟩
  exact biprod.mapIso eM eN ≪≫
    biprod.isoCoprod (SheafOfModules.free (R := Y.ringCatSheaf) I)
      (SheafOfModules.free (R := Y.ringCatSheaf) J) ≪≫
    SheafOfModules.freeSumIso (R := Y.ringCatSheaf) I J ≪≫
    (SheafOfModules.freeFunctor (R := Y.ringCatSheaf)).mapIso reindex.toIso

/-- Every component of the ACTUAL mapping cone is finite free; degree -1 is allowed. -/
theorem finiteFree_mappingCone_terms {Y : Scheme.{u}}
    (P D : CochainComplex Y.Modules ℤ) (Φ : P ⟶ D)
    (freeP : ∀ n, ∃ r : ℕ, Nonempty (P.X n ≅ SheafOfModules.free
      (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))
    (freeD : ∀ n, ∃ r : ℕ, Nonempty (D.X n ≅ SheafOfModules.free
      (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))) :
    ∀ n, ∃ r : ℕ, Nonempty ((CochainComplex.mappingCone Φ).X n ≅
      SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin r))) := by
  intro n
  obtain ⟨r, ⟨e⟩⟩ := finiteFree_biprod (P.X (n + 1)) (D.X n)
    (freeP (n + 1)) (freeD n)
  exact ⟨r, ⟨HomologicalComplex.homotopyCofiber.XIsoBiprod Φ n (n + 1) rfl ≪≫ e⟩⟩

/-- The literal upper-bound locus for actual native cone fibre homology is open. -/
theorem isOpen_derivedFiberDimension_cone_le {Y : Scheme.{u}}
    (P D : CochainComplex Y.Modules ℤ) (Φ : P ⟶ D)
    (freeP : ∀ n, ∃ r : ℕ, Nonempty (P.X n ≅ SheafOfModules.free
      (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))
    (freeD : ∀ n, ∃ r : ℕ, Nonempty (D.X n ≅ SheafOfModules.free
      (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))) (r : ℕ) :
    IsOpen {y : Y | ZInQ.Contrib.CloudR2Poincare.L1.derivedFiberDimension
      (CochainComplex.mappingCone Φ) 0 y ≤ r} := by
  have hc := ZInQ.Contrib.CloudR2Poincare.L1.isClosed_derivedFiberDimension_ge
    (CochainComplex.mappingCone Φ) (finiteFree_mappingCone_terms P D Φ freeP freeD) 0 (r + 1)
  convert hc.isOpen_compl using 1
  ext y
  change (ZInQ.Contrib.CloudR2Poincare.L1.derivedFiberDimension
      (CochainComplex.mappingCone Φ) 0 y ≤ r) ↔
    ¬ r + 1 ≤ ZInQ.Contrib.CloudR2Poincare.L1.derivedFiberDimension
      (CochainComplex.mappingCone Φ) 0 y
  omega

/-- EXACT §5a: semicontinuity near any point of the ACTUAL finite-free cone,
with no reducedness, Noetherian, boundedness or nonnegative-cone premise. -/
theorem exists_open_derivedFiberDimension_cone_le {Y : Scheme.{u}}
    (P D : CochainComplex Y.Modules ℤ) (Φ : P ⟶ D)
    (freeP : ∀ n, ∃ r : ℕ, Nonempty (P.X n ≅ SheafOfModules.free
      (R := Y.ringCatSheaf) (ULift.{u} (Fin r))))
    (freeD : ∀ n, ∃ r : ℕ, Nonempty (D.X n ≅ SheafOfModules.free
      (R := Y.ringCatSheaf) (ULift.{u} (Fin r)))) (y : Y) :
    ∃ V : Y.Opens, y ∈ V ∧ ∀ z : Y, z ∈ V →
      ZInQ.Contrib.CloudR2Poincare.L1.derivedFiberDimension
          (CochainComplex.mappingCone Φ) 0 z ≤
        ZInQ.Contrib.CloudR2Poincare.L1.derivedFiberDimension
          (CochainComplex.mappingCone Φ) 0 y := by
  let r := ZInQ.Contrib.CloudR2Poincare.L1.derivedFiberDimension
    (CochainComplex.mappingCone Φ) 0 y
  let V : Y.Opens :=
    ⟨{z : Y | ZInQ.Contrib.CloudR2Poincare.L1.derivedFiberDimension
      (CochainComplex.mappingCone Φ) 0 z ≤ r},
      isOpen_derivedFiberDimension_cone_le P D Φ freeP freeD r⟩
  refine ⟨V, ?_, ?_⟩
  · change ZInQ.Contrib.CloudR2Poincare.L1.derivedFiberDimension
      (CochainComplex.mappingCone Φ) 0 y ≤ r
    exact le_rfl
  · intro z hz
    exact hz

end ZInQ.Contrib.CloudR2Poincare.L6
