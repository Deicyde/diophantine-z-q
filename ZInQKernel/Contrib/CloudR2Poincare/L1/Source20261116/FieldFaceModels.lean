import ZInQKernel.Contrib.CloudR2Poincare.L1.CechNativeFaceComparison
import ZInQKernel.Contrib.CloudR2Poincare.L1.AdjunctionHZero
import ZInQKernel.Contrib.CloudR2Poincare.L3.NativeLerayOne
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Proper
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual degree-zero/one native Čech face isomorphisms over the ORIGINAL field

These equivalences are LinearEquiv.ofBijective of the ALREADY FIXED actual
aligned comparison. They are never selected from a rank. In degree one the
literal existing adjunction map is injective by the certified general L3
Leray segment. A native coefficient-natural affine comparison and honest
proper-field finiteness then make that SAME map surjective.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The EXISTING native adjunction inflation, linear over the ORIGINAL field. -/
def nativeHMapOfAdjunctionFieldLinearMap
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of k))] (N : Y.Modules) (n : ℕ) :
    ((Scheme.Modules.pushforward j).obj N).H n →ₗ[k] N.H n where
  toFun := Scheme.Modules.H.mapOfAdjunction j (𝟙 ((Scheme.Modules.pushforward j).obj N)) n
  map_add' := (Scheme.Modules.H.mapOfAdjunction j (𝟙 ((Scheme.Modules.pushforward j).obj N)) n).map_add
  map_smul' a z := by
    change Scheme.Modules.H.mapOfAdjunction j (𝟙 ((Scheme.Modules.pushforward j).obj N)) n
        (Scheme.globalSectionsRingHom k (X := X) a • z) =
      Scheme.globalSectionsRingHom k (X := Y) a •
        Scheme.Modules.H.mapOfAdjunction j (𝟙 ((Scheme.Modules.pushforward j).obj N)) n z
    rw [Scheme.Modules.H.mapOfAdjunction_smul, Scheme.Hom.appTop_globalSectionsRingHom]

/-- Actual native H¹ adjunction along an affine face is bijective whenever the
honest target cohomology is finite. No supplied injection or map premise. -/
theorem bijective_nativeHOneMapOfAdjunction_of_affine
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of k))] [IsAffineHom j]
    (N : Y.Modules) [N.IsQuasicoherent] [Module.Finite k (N.H 1)] :
    Function.Bijective (Scheme.Modules.H.mapOfAdjunction j
      (𝟙 ((Scheme.Modules.pushforward j).obj N)) 1) := by
  let e : N.H 1 ≃ₗ[k] ((Scheme.Modules.pushforward j).obj N).H 1 :=
    ((Scheme.Modules.nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom k j 1).some.app
      ⟨N, inferInstance⟩).toLinearEquiv
  let f := nativeHMapOfAdjunctionFieldLinearMap (k := k) j N 1
  have hf : Function.Injective f := (L3.nativeLerayOneExact j N).1
  have ht : Function.Surjective (f ∘ₗ e.toLinearMap) :=
    LinearMap.surjective_of_injective (hf.comp e.injective)
  refine ⟨hf, ?_⟩
  intro z
  obtain ⟨x, hx⟩ := ht z
  exact ⟨e x, hx⟩

/-- Actual degree-zero aligned target comparison is bijective, with no finite,
rank, properness or extra model premise. -/
theorem bijective_nativeCechFaceHFieldLinearMap_zero
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of k))] [IsAffineHom j]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) :
    Function.Bijective (nativeCechFaceHFieldLinearMap (k := k) j M U affineU coverU 0) := by
  let q := X ↘ Spec (.of k)
  let N := (Scheme.Modules.pullback j).obj M
  let PN := (Scheme.Modules.pushforward j).obj N
  letI : PN.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom j N
  let e := (HomologicalComplex.homologyMapIso (cechModulePushforwardIso q j N U) (0 : ℤ)).toLinearEquiv
  change Function.Bijective (fun z ↦ Scheme.Modules.H.mapOfAdjunction j (𝟙 PN) 0
    (nativeCechHComparison q PN U affineU coverU 0 (e.symm z)))
  exact (bijective_nativeHZeroMapOfAdjunction j N).comp
    ((nativeCechHComparison q PN U affineU coverU 0).bijective.comp e.symm.bijective)

/-- Proper field geometry discharges the degree-one finiteness premise. The
fixed actual target comparison is then a bijection; no rank-selected map. -/
theorem bijective_nativeCechFaceHFieldLinearMap_one
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of k))] [IsAffineHom j]
    (M : X.Modules) [M.IsInvertible] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) :
    Function.Bijective (nativeCechFaceHFieldLinearMap (k := k) j M U affineU coverU 1) := by
  let q := X ↘ Spec (.of k)
  let N := (Scheme.Modules.pullback j).obj M
  let PN := (Scheme.Modules.pushforward j).obj N
  letI : PN.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom j N
  haveI : Module.Finite k (N.H 1) := Scheme.Modules.hasFiniteH_of_isProper (Y ↘ Spec (.of k)) N 1
  let e := (HomologicalComplex.homologyMapIso (cechModulePushforwardIso q j N U) (1 : ℤ)).toLinearEquiv
  change Function.Bijective (fun z ↦ Scheme.Modules.H.mapOfAdjunction j (𝟙 PN) 1
    (nativeCechHComparison q PN U affineU coverU 1 (e.symm z)))
  exact (bijective_nativeHOneMapOfAdjunction_of_affine (k := k) j N).comp
    ((nativeCechHComparison q PN U affineU coverU 1).bijective.comp e.symm.bijective)

/-- ACTUAL degree-zero field isomorphism, of the already fixed native face map. -/
def nativeCechFaceHFieldLinearEquiv_zero
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of k))] [IsAffineHom j]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) :
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).obj
        ((Scheme.Modules.cechModuleComplex (j ≫ (X ↘ Spec (.of k)))
          ((Scheme.Modules.pullback j).obj M) (fun i ↦ j ⁻¹ᵁ U i)).homology 0) ≃ₗ[k]
      ((Scheme.Modules.pullback j).obj M).H 0 :=
  LinearEquiv.ofBijective (nativeCechFaceHFieldLinearMap (k := k) j M U affineU coverU 0)
    (bijective_nativeCechFaceHFieldLinearMap_zero j M U affineU coverU)

/-- ACTUAL degree-one field isomorphism, of the already fixed native face map. -/
def nativeCechFaceHFieldLinearEquiv_one
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of k))] [IsAffineHom j]
    (M : X.Modules) [M.IsInvertible] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) :
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).obj
        ((Scheme.Modules.cechModuleComplex (j ≫ (X ↘ Spec (.of k)))
          ((Scheme.Modules.pullback j).obj M) (fun i ↦ j ⁻¹ᵁ U i)).homology 1) ≃ₗ[k]
      ((Scheme.Modules.pullback j).obj M).H 1 :=
  LinearEquiv.ofBijective (nativeCechFaceHFieldLinearMap (k := k) j M U affineU coverU 1)
    (bijective_nativeCechFaceHFieldLinearMap_one j M U affineU coverU)

/-- The degree-zero isomorphism retains the ACTUAL existing-H pullback square. -/
theorem nativeCechFaceHFieldLinearEquiv_zero_square
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of k))] [IsAffineHom j]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (z : (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).obj
      ((Scheme.Modules.cechModuleComplex (X ↘ Spec (.of k)) M U).homology 0)) :
    nativeCechFaceHFieldLinearEquiv_zero (k := k) j M U affineU coverU
        (HomologicalComplex.homologyMap (cechModuleFaceMap (X ↘ Spec (.of k)) j M U) (0 : ℤ) z) =
      Scheme.Modules.H.pullback j M 0 (nativeCechHFieldLinearEquiv (k := k) M U affineU coverU 0 z) :=
  nativeCechFaceHFieldLinearMap_square j M U affineU coverU 0 z

/-- The degree-one isomorphism retains the ACTUAL existing-H pullback square. -/
theorem nativeCechFaceHFieldLinearEquiv_one_square
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsProper (Y ↘ Spec (.of k))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of k))] [IsAffineHom j]
    (M : X.Modules) [M.IsInvertible] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (z : (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).obj
      ((Scheme.Modules.cechModuleComplex (X ↘ Spec (.of k)) M U).homology 1)) :
    nativeCechFaceHFieldLinearEquiv_one (k := k) j M U affineU coverU
        (HomologicalComplex.homologyMap (cechModuleFaceMap (X ↘ Spec (.of k)) j M U) (1 : ℤ) z) =
      Scheme.Modules.H.pullback j M 1 (nativeCechHFieldLinearEquiv (k := k) M U affineU coverU 1 z) :=
  nativeCechFaceHFieldLinearMap_square j M U affineU coverU 1 z

end ZInQ.Contrib.CloudR2Poincare.L1
