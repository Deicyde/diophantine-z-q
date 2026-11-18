import ZInQKernel.Contrib.CloudR2Poincare.L1.CechNaturalHComparison

/-!
# Actual scalar and coefficient laws for the native Čech/H comparison

Every comparison below is the retained coefficient-natural comparison of
CechNaturalHComparison. No map is selected from a rank or dimension argument.
The original integer complex and the original field action are retained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Actual native coefficient multiplication is scalar multiplication on the
FULL all-tuple Čech complex, before taking homology. -/
theorem cechModuleCoefficientMapNat_smulHom
    {X S : Scheme.{u}} (q : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (a : Γ(S, ⊤)) :
    cechModuleCoefficientMapNat q (M.smulHom (q.appTop a)) U =
      a • 𝟙 (Scheme.Modules.cechModuleComplexNat q M U) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  funext t
  rfl

/-- Actual homology sends coefficient scalar identity to scalar identity. -/
theorem homologyMap_scalar_identity
    {A : Type u} [CommRing A] {J : Type*} (shape : ComplexShape J)
    (C : HomologicalComplex (ModuleCat.{u} A) shape) (a : A) (n : J) :
    HomologicalComplex.homologyMap (a • 𝟙 C) n = a • 𝟙 (C.homology n) := by
  have h : (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) shape n).map
      (a • 𝟙 C) = a • 𝟙 (C.sc n) := by
    ext <;> rfl
  change ShortComplex.homologyMap _ = _
  rw [h, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

/-- The retained comparison is semilinear along the ACTUAL base structure map. -/
theorem nativeCechHComparisonNat_smul
    {X S : Scheme.{u}} (q : X ⟶ S) [IsAffine S] [IsSeparated q]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) (n : ℕ)
    (a : Γ(S, ⊤)) (z : (Scheme.Modules.cechModuleComplexNat q M U).homology n) :
    nativeCechHComparisonNat q M U affineU coverU n (a • z) =
      q.appTop a • nativeCechHComparisonNat q M U affineU coverU n z := by
  have h : HomologicalComplex.homologyMap
      (cechModuleCoefficientMapNat q (M.smulHom (q.appTop a)) U) n z = a • z := by
    rw [cechModuleCoefficientMapNat_smulHom, homologyMap_scalar_identity]
    rfl
  rw [← h]
  exact (nativeCechHComparisonNat_coefficient_naturality q (M.smulHom (q.appTop a))
    U affineU coverU n z).trans (Scheme.Modules.H.smul_eq_map.{u, u} M n (q.appTop a) _).symm

/-- Original integer Čech coefficient naturality through the ACTUAL extension
homology isomorphism, not an assumption of termwise boundedness. -/
theorem nativeCechHComparison_coefficient_naturality
    {X S : Scheme.{u}} (q : X ⟶ S) [IsAffine S] [IsSeparated q]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i))
    (coverU : ⨆ i, U i = ⊤) (n : ℕ)
    (z : (Scheme.Modules.cechModuleComplex q M U).homology n) :
    nativeCechHComparison q N U affineU coverU n
        (HomologicalComplex.homologyMap (cechModuleCoefficientMap q φ U) n z) =
      Scheme.Modules.H.map φ n (nativeCechHComparison q M U affineU coverU n z) := by
  let eM : (Scheme.Modules.cechModuleComplex q M U).homology (n : ℤ) ≅
      (Scheme.Modules.cechModuleComplexNat q M U).homology n :=
    (Scheme.Modules.cechModuleComplexNat q M U).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  let eN : (Scheme.Modules.cechModuleComplex q N U).homology (n : ℤ) ≅
      (Scheme.Modules.cechModuleComplexNat q N U).homology n :=
    (Scheme.Modules.cechModuleComplexNat q N U).extendHomologyIso
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.extendHomologyIso_hom_naturality (cechModuleCoefficientMapNat q φ U)
      ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl) z
  simp only [ConcreteCategory.comp_apply] at h
  change eN.hom (HomologicalComplex.homologyMap (cechModuleCoefficientMap q φ U) (n : ℤ) z) =
    HomologicalComplex.homologyMap (cechModuleCoefficientMapNat q φ U) n (eM.hom z) at h
  exact (congrArg (nativeCechHComparisonNat q N U affineU coverU n) h).trans
    (nativeCechHComparisonNat_coefficient_naturality q φ U affineU coverU n (eM.hom z))

/-- The ORIGINAL complex comparison is semilinear over the ACTUAL base. -/
theorem nativeCechHComparison_smul
    {X S : Scheme.{u}} (q : X ⟶ S) [IsAffine S] [IsSeparated q]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) (n : ℕ)
    (a : Γ(S, ⊤)) (z : (Scheme.Modules.cechModuleComplex q M U).homology n) :
    nativeCechHComparison q M U affineU coverU n (a • z) =
      q.appTop a • nativeCechHComparison q M U affineU coverU n z := by
  let e := ((Scheme.Modules.cechModuleComplexNat q M U).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) rfl).toLinearEquiv
  change nativeCechHComparisonNat q M U affineU coverU n (e (a • z)) = _
  rw [e.map_smul]
  exact nativeCechHComparisonNat_smul q M U affineU coverU n a (e z)

/-- The retained comparison is linear over the ORIGINAL field, after the
canonical Γ(Spec k) scalar restriction. -/
def nativeCechHFieldLinearEquiv
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) (n : ℕ) :
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).obj
        ((Scheme.Modules.cechModuleComplex (X ↘ Spec (.of k)) M U).homology n) ≃ₗ[k]
      M.H n where
  toAddEquiv := nativeCechHComparison (X ↘ Spec (.of k)) M U affineU coverU n
  map_smul' a z := by
    change nativeCechHComparison (X ↘ Spec (.of k)) M U affineU coverU n
        ((Scheme.ΓSpecIso (.of k)).inv a • z) =
      (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv a) •
        nativeCechHComparison (X ↘ Spec (.of k)) M U affineU coverU n z
    exact nativeCechHComparison_smul (X ↘ Spec (.of k)) M U affineU coverU n _ z

end ZInQ.Contrib.CloudR2Poincare.L1
