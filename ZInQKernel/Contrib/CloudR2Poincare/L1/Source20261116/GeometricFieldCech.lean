import ZInQKernel.Contrib.CloudR2Poincare.L1.Source20261116.RetainedFaceFibre
import ZInQKernel.Contrib.CloudR2Poincare.L1.RetainedModelScalarKernel

/-!
# Actual geometric field Čech comparison for a retained affine chart

The field point is the existing `fieldPointFromGlobalSections` attached to
β.comp α. Its appTop triangle is proved, not supplied by a caller. Native
Čech base change and L3's literal integer face square construct the comparison
into jB^*a^*M. Target coefficient and cover transports are applied in their
actual inverse orientation. No original Čech termwise bound, flat residue
map, supplied chain square, or dimension-selected equivalence is used.
-/

noncomputable section

universe u
open CategoryTheory Limits AlgebraicGeometry
open ZInQ.Contrib.CloudR2Poincare.L1.RetainedFaceFibreConstruction

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Affine intersections used by the original ALL-tuple Čech complex. The
index tuple is finite; no infinite-inf preimage assertion is used. -/
theorem nativeCech_affineIntersections
    {X B : Scheme.{u}} (q : X ⟶ B) [IsAffine B] [IsSeparated q]
    {ι : Type u} (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i))
    (n : ℕ) (t : Fin (n + 1) → ι) : IsAffineOpen (⨅ l, U (t l)) := by
  classical
  haveI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from q]
    infer_instance
  simpa using (IsAffineOpen.biInf (Set.univ : Set (Fin (n + 1))) Set.finite_univ
    Set.univ_nonempty (fun l _ ↦ affineU (t l)))

/-- The original scalar map determines an actual field-valued point of the
original affine base; no auxiliary field identification is selected. -/
def retainedFieldBasePoint
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    (κ : Type u) [Field κ] (β : S →+* κ) : Spec (.of κ) ⟶ Spec (.of R) :=
  fieldPointFromGlobalSections κ (β.comp (algebraMap Γ(Spec (.of R), ⊤) S))

/-- The native Γ-valued map is literally the raw β.comp α followed by the
original ΓSpec inverse. This is the actual scalar spelling used by Čech. -/
theorem retainedFieldBasePoint_appTop
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    (κ : Type u) [Field κ] (β : S →+* κ) :
    (retainedFieldBasePoint R S κ β).appTop.hom =
      (Scheme.ΓSpecIso (.of κ)).inv.hom.comp
        (β.comp (algebraMap Γ(Spec (.of R), ⊤) S)) :=
  fieldPointFromGlobalSections_appTop κ (β.comp (algebraMap Γ(Spec (.of R), ⊤) S))

/-- The native original-Čech scalar comparison on any actual Cartesian field
fibre, with the algebra map installed from the SAME raw composite. -/
def retainedGeometricCechIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    {X XB : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsSeparated q]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i))
    (κ : Type u) [Field κ] (β : S →+* κ)
    (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X)
    (HC : IsPullback a qB q (retainedFieldBasePoint R S κ β)) :
    (scalarComplexFunctor ((Scheme.ΓSpecIso (.of κ)).inv.hom.comp
        (β.comp (algebraMap Γ(Spec (.of R), ⊤) S)))).obj
      (Scheme.Modules.cechModuleComplex q M U) ≅
        Scheme.Modules.cechModuleComplex qB ((Scheme.Modules.pullback a).obj M)
          (fun i ↦ a ⁻¹ᵁ U i) := by
  let A := Γ(Spec (.of R), ⊤)
  let G := Γ(Spec (.of κ), ⊤)
  let γ : A →+* G := (Scheme.ΓSpecIso (.of κ)).inv.hom.comp (β.comp (algebraMap A S))
  letI : Algebra A G := γ.toAlgebra
  have hg : algebraMap A G = (retainedFieldBasePoint R S κ β).appTop.hom :=
    (retainedFieldBasePoint_appTop R S κ β).symm
  exact Scheme.Modules.cechModuleComplexBaseChangeIso HC M hg U
    (nativeCech_affineIntersections q U affineU)

/-- Native scalar comparison of the original face complex, adjusted by the
ACTUAL coefficient-then-cover target isomorphism in its inverse orientation. -/
def retainedGeometricFaceCechIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    {X Y XB YB : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsSeparated q]
    (j : Y ⟶ X) [IsAffineHom j]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i))
    (κ : Type u) [Field κ] (β : S →+* κ)
    (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HD : IsPullback b (jB ≫ qB) (j ≫ q) (retainedFieldBasePoint R S κ β))
    (square : jB ≫ a = b ≫ j) :
    (scalarComplexFunctor ((Scheme.ΓSpecIso (.of κ)).inv.hom.comp
        (β.comp (algebraMap Γ(Spec (.of R), ⊤) S)))).obj
      (Scheme.Modules.cechModuleComplex (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (fun i ↦ j ⁻¹ᵁ U i)) ≅
      Scheme.Modules.cechModuleComplex (jB ≫ qB)
        ((Scheme.Modules.pullback jB).obj ((Scheme.Modules.pullback a).obj M))
        (fun i ↦ jB ⁻¹ᵁ a ⁻¹ᵁ U i) := by
  let A := Γ(Spec (.of R), ⊤)
  let G := Γ(Spec (.of κ), ⊤)
  let γ : A →+* G := (Scheme.ΓSpecIso (.of κ)).inv.hom.comp (β.comp (algebraMap A S))
  letI : Algebra A G := γ.toAlgebra
  have hg : algebraMap A G = (retainedFieldBasePoint R S κ β).appTop.hom :=
    (retainedFieldBasePoint_appTop R S κ β).symm
  have affineD : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, j ⁻¹ᵁ U (t l)) :=
    nativeCech_affineIntersections (j ≫ q) (fun i ↦ j ⁻¹ᵁ U i) (fun i ↦ (affineU i).preimage j)
  exact Scheme.Modules.cechModuleComplexBaseChangeIso HD ((Scheme.Modules.pullback j).obj M)
      hg (fun i ↦ j ⁻¹ᵁ U i) affineD ≪≫
    (L3.CechFacePromotion.nativeFaceBaseChangeCechTargetIso qB j a b jB square M U).symm

/-- The adjusted target comparison commutes with the original integer Čech
face map. This is L3's actual geometric square, not a new supplied premise. -/
theorem retainedGeometricCechIso_face_square
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    {X Y XB YB : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsSeparated q]
    (j : Y ⟶ X) [IsAffineHom j]
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (affineU : ∀ i, IsAffineOpen (U i))
    (κ : Type u) [Field κ] (β : S →+* κ)
    (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R S κ β))
    (HD : IsPullback b (jB ≫ qB) (j ≫ q) (retainedFieldBasePoint R S κ β))
    (square : jB ≫ a = b ≫ j) :
    (retainedGeometricCechIso R S q M U affineU κ β qB a HC).hom ≫
        cechModuleFaceMap qB jB ((Scheme.Modules.pullback a).obj M) (fun i ↦ a ⁻¹ᵁ U i) =
      (scalarComplexFunctor ((Scheme.ΓSpecIso (.of κ)).inv.hom.comp
          (β.comp (algebraMap Γ(Spec (.of R), ⊤) S)))).map (cechModuleFaceMap q j M U) ≫
        (retainedGeometricFaceCechIso R S q j M U affineU κ β qB a b jB HD square).hom := by
  let A := Γ(Spec (.of R), ⊤)
  let G := Γ(Spec (.of κ), ⊤)
  let γ : A →+* G := (Scheme.ΓSpecIso (.of κ)).inv.hom.comp (β.comp (algebraMap A S))
  letI : Algebra A G := γ.toAlgebra
  have hg : algebraMap A G = (retainedFieldBasePoint R S κ β).appTop.hom :=
    (retainedFieldBasePoint_appTop R S κ β).symm
  let EC := Scheme.Modules.cechModuleComplexBaseChangeIso HC M hg U
    (nativeCech_affineIntersections q U affineU)
  let ED := Scheme.Modules.cechModuleComplexBaseChangeIso HD ((Scheme.Modules.pullback j).obj M)
    hg (fun i ↦ j ⁻¹ᵁ U i)
    (nativeCech_affineIntersections (j ≫ q) (fun i ↦ j ⁻¹ᵁ U i) (fun i ↦ (affineU i).preimage j))
  let T := L3.CechFacePromotion.nativeFaceBaseChangeCechTargetIso qB j a b jB square M U
  let ΦB := cechModuleFaceMap qB jB ((Scheme.Modules.pullback a).obj M) (fun i ↦ a ⁻¹ᵁ U i)
  let Φ := cechModuleFaceMap q j M U
  have h : EC.hom ≫ ΦB ≫ T.hom = (scalarComplexFunctor γ).map Φ ≫ ED.hom :=
    L3.CechFacePromotion.cechModuleFaceMap_baseChange_square q qB (retainedFieldBasePoint R S κ β)
      j a b jB HC HD square M hg U (nativeCech_affineIntersections q U affineU)
      (nativeCech_affineIntersections (j ≫ q) (fun i ↦ j ⁻¹ᵁ U i) (fun i ↦ (affineU i).preimage j))
  change EC.hom ≫ ΦB = (scalarComplexFunctor γ).map Φ ≫ (ED.hom ≫ T.inv)
  apply (cancel_mono T.hom).mp
  calc
    (EC.hom ≫ ΦB) ≫ T.hom = EC.hom ≫ ΦB ≫ T.hom := Category.assoc _ _ _
    _ = (scalarComplexFunctor γ).map Φ ≫ ED.hom := h
    _ = ((scalarComplexFunctor γ).map Φ ≫ (ED.hom ≫ T.inv)) ≫ T.hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Cartesian field faces inherit the original properness and affineness;
no affine-face or proper-fibre premise is added to the geometry consumer. -/
theorem retainedFieldFace_geometry
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    {X Y XB YB : Scheme.{u}} (q : X ⟶ Spec (.of R)) [IsProper q]
    (j : Y ⟶ X) [IsAffineHom j] [IsProper (j ≫ q)]
    (κ : Type u) [Field κ] (β : S →+* κ)
    (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X) (b : YB ⟶ Y) (jB : YB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R S κ β))
    (HD : IsPullback b (jB ≫ qB) (j ≫ q) (retainedFieldBasePoint R S κ β))
    (square : jB ≫ a = b ≫ j) :
    IsProper qB ∧ IsProper (jB ≫ qB) ∧ IsAffineHom jB := by
  have hFace : IsPullback b jB j a := HD.of_bot square.symm HC
  exact ⟨MorphismProperty.of_isPullback (P := @IsProper) HC inferInstance,
    MorphismProperty.of_isPullback (P := @IsProper) HD inferInstance,
    MorphismProperty.of_isPullback (P := @IsAffineHom) hFace inferInstance⟩

end ZInQ.Contrib.CloudR2Poincare.L1
