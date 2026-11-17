import ZInQKernel.Contrib.CloudR2Poincare.L1.Source20261116.ScalarNaturality
import ZInQKernel.Contrib.CloudR2Poincare.L1.CechFacePushforward
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Pullback
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.AffinePushforward

/-!
# Actual native Čech/H face squares

ONE coefficient-natural ambient comparison is used for M and j_*j^*M.
The actual face complex is identified with the pushforward complex, then
mapped by the EXISTING Ext-defined H.mapOfAdjunction j (𝟙 _) n. This gives
literal commutation with the EXISTING H.pullback. No rank-selected map or
arbitrary model premise is used. Bijectivity in degrees 0 and 1 is proved
separately from the native zero-degree adjunction and low-degree Leray.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The ACTUAL aligned target comparison, retaining the existing native
adjunction cohomology map rather than an independently selected object iso. -/
def nativeCechFaceHComparison
    {X Y S : Scheme.{u}} (q : X ⟶ S) [IsAffine S] [IsSeparated q]
    (j : Y ⟶ X) [IsAffineHom j] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i))
    (coverU : ⨆ i, U i = ⊤) (n : ℕ) :
    (Scheme.Modules.cechModuleComplex (j ≫ q) ((Scheme.Modules.pullback j).obj M)
      (fun i ↦ j ⁻¹ᵁ U i)).homology n →+ ((Scheme.Modules.pullback j).obj M).H n :=
  let N := (Scheme.Modules.pullback j).obj M
  let PN := (Scheme.Modules.pushforward j).obj N
  letI : PN.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom j N
  let e := (HomologicalComplex.homologyMapIso (cechModulePushforwardIso q j N U) (n : ℤ)).toLinearEquiv
  (Scheme.Modules.H.mapOfAdjunction j (𝟙 PN) n).comp
    ((nativeCechHComparison q PN U affineU coverU n).toAddMonoidHom.comp
      e.symm.toAddEquiv.toAddMonoidHom)

/-- Exact stored-map formula: actual ambient θ, actual pushforward chain
identification and the existing H.mapOfAdjunction. -/
theorem nativeCechFaceHComparison_apply
    {X Y S : Scheme.{u}} (q : X ⟶ S) [IsAffine S] [IsSeparated q]
    (j : Y ⟶ X) [IsAffineHom j] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i))
    (coverU : ⨆ i, U i = ⊤) (n : ℕ)
    (z : (Scheme.Modules.cechModuleComplex (j ≫ q) ((Scheme.Modules.pullback j).obj M)
      (fun i ↦ j ⁻¹ᵁ U i)).homology n) :
    letI : ((Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj M)).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom j ((Scheme.Modules.pullback j).obj M)
    nativeCechFaceHComparison q j M U affineU coverU n z =
      Scheme.Modules.H.mapOfAdjunction j
        (𝟙 ((Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj M))) n
        (nativeCechHComparison q ((Scheme.Modules.pushforward j).obj ((Scheme.Modules.pullback j).obj M))
          U affineU coverU n
          ((HomologicalComplex.homologyMapIso
            (cechModulePushforwardIso q j ((Scheme.Modules.pullback j).obj M) U) (n : ℤ)).inv z)) := rfl

/-- The ORIGINAL non-alternating native Čech face arrow commutes LITERALLY
with the EXISTING native cohomological pullback. This holds in every degree. -/
theorem nativeCechFaceHComparison_square
    {X Y S : Scheme.{u}} (q : X ⟶ S) [IsAffine S] [IsSeparated q]
    (j : Y ⟶ X) [IsAffineHom j] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i))
    (coverU : ⨆ i, U i = ⊤) (n : ℕ)
    (z : (Scheme.Modules.cechModuleComplex q M U).homology n) :
    nativeCechFaceHComparison q j M U affineU coverU n
        (HomologicalComplex.homologyMap (cechModuleFaceMap q j M U) (n : ℤ) z) =
      Scheme.Modules.H.pullback j M n (nativeCechHComparison q M U affineU coverU n z) := by
  let N := (Scheme.Modules.pullback j).obj M
  let PN := (Scheme.Modules.pushforward j).obj N
  letI : PN.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom j N
  let unit : M ⟶ PN := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M
  let e : (Scheme.Modules.cechModuleComplex q PN U).homology (n : ℤ) ≅
      (Scheme.Modules.cechModuleComplex (j ≫ q) N (fun i ↦ j ⁻¹ᵁ U i)).homology (n : ℤ) :=
    HomologicalComplex.homologyMapIso (cechModulePushforwardIso q j N U) (n : ℤ)
  have h : HomologicalComplex.homologyMap (cechModuleFaceMap q j M U) (n : ℤ) z =
      e.hom (HomologicalComplex.homologyMap (cechModuleCoefficientMap q unit U) (n : ℤ) z) := by
    rw [cechModuleFaceMap_factorization, HomologicalComplex.homologyMap_comp]
    rfl
  have hi (x : (Scheme.Modules.cechModuleComplex q PN U).homology (n : ℤ)) :
      e.inv (e.hom x) = x := ConcreteCategory.congr_hom e.hom_inv_id x
  change Scheme.Modules.H.mapOfAdjunction j (𝟙 PN) n
      (nativeCechHComparison q PN U affineU coverU n
        (e.inv (HomologicalComplex.homologyMap (cechModuleFaceMap q j M U) (n : ℤ) z))) = _
  rw [h, hi, nativeCechHComparison_coefficient_naturality]
  have hn := Scheme.Modules.H.mapOfAdjunction_naturality j unit (𝟙 PN) unit (𝟙 N)
    (by simp) n (nativeCechHComparison q M U affineU coverU n z)
  calc
    _ = Scheme.Modules.H.mapOfAdjunction j unit n
        (nativeCechHComparison q M U affineU coverU n z) := by
      simpa only [Scheme.Modules.H.map_id_apply] using hn
    _ = Scheme.Modules.H.pullback j M n
        (nativeCechHComparison q M U affineU coverU n z) := rfl

/-- The aligned ACTUAL target comparison is semilinear for the ORIGINAL
base structure map, with no face or residue-field flatness premise. -/
theorem nativeCechFaceHComparison_smul
    {X Y S : Scheme.{u}} (q : X ⟶ S) [IsAffine S] [IsSeparated q]
    (j : Y ⟶ X) [IsAffineHom j] (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type u} (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i))
    (coverU : ⨆ i, U i = ⊤) (n : ℕ) (a : Γ(S, ⊤))
    (z : (Scheme.Modules.cechModuleComplex (j ≫ q) ((Scheme.Modules.pullback j).obj M)
      (fun i ↦ j ⁻¹ᵁ U i)).homology n) :
    nativeCechFaceHComparison q j M U affineU coverU n (a • z) =
      (j ≫ q).appTop a • nativeCechFaceHComparison q j M U affineU coverU n z := by
  let N := (Scheme.Modules.pullback j).obj M
  let PN := (Scheme.Modules.pushforward j).obj N
  letI : PN.IsQuasicoherent := Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom j N
  let e := (HomologicalComplex.homologyMapIso (cechModulePushforwardIso q j N U) (n : ℤ)).toLinearEquiv
  change Scheme.Modules.H.mapOfAdjunction j (𝟙 PN) n
      (nativeCechHComparison q PN U affineU coverU n (e.symm (a • z))) = _
  rw [e.symm.map_smul, nativeCechHComparison_smul, Scheme.Modules.H.mapOfAdjunction_smul,
    Scheme.Hom.comp_appTop]
  rfl

/-- The same ACTUAL target comparison is linear over the ORIGINAL field. -/
def nativeCechFaceHFieldLinearMap
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of k))] [IsAffineHom j]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) (n : ℕ) :
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).obj
        ((Scheme.Modules.cechModuleComplex (j ≫ (X ↘ Spec (.of k)))
          ((Scheme.Modules.pullback j).obj M) (fun i ↦ j ⁻¹ᵁ U i)).homology n) →ₗ[k]
      ((Scheme.Modules.pullback j).obj M).H n where
  toFun := nativeCechFaceHComparison (X ↘ Spec (.of k)) j M U affineU coverU n
  map_add' := fun a b ↦ (nativeCechFaceHComparison (X ↘ Spec (.of k)) j M U affineU coverU n).map_add a b
  map_smul' a z := by
    have hj : j ≫ (X ↘ Spec (.of k)) = (Y ↘ Spec (.of k)) :=
      (Scheme.Hom.isOver_iff (Spec (.of k))).mp inferInstance
    change nativeCechFaceHComparison (X ↘ Spec (.of k)) j M U affineU coverU n
        ((Scheme.ΓSpecIso (.of k)).inv a • z) =
      (Y ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv a) •
        nativeCechFaceHComparison (X ↘ Spec (.of k)) j M U affineU coverU n z
    rw [nativeCechFaceHComparison_smul]
    have hs := congrArg (fun p : Y ⟶ Spec (.of k) ↦
      p.appTop ((Scheme.ΓSpecIso (.of k)).inv a)) hj
    exact congrArg (fun c : Γ(Y, ⊤) ↦ c •
      nativeCechFaceHComparison (X ↘ Spec (.of k)) j M U affineU coverU n z) hs

/-- Original-field square, whose right arrow is STILL the existing H.pullback. -/
theorem nativeCechFaceHFieldLinearMap_square
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : Y ⟶ X) [j.IsOver (Spec (.of k))] [IsAffineHom j]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) (n : ℕ)
    (z : (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).obj
      ((Scheme.Modules.cechModuleComplex (X ↘ Spec (.of k)) M U).homology n)) :
    nativeCechFaceHFieldLinearMap (k := k) j M U affineU coverU n
        (HomologicalComplex.homologyMap (cechModuleFaceMap (X ↘ Spec (.of k)) j M U) (n : ℤ) z) =
      Scheme.Modules.H.pullback j M n (nativeCechHFieldLinearEquiv (k := k) M U affineU coverU n z) :=
  nativeCechFaceHComparison_square (X ↘ Spec (.of k)) j M U affineU coverU n z

end ZInQ.Contrib.CloudR2Poincare.L1
