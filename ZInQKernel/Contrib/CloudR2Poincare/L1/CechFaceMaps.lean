import ZInQKernel.Contrib.CloudR2Poincare.L1.FaceSections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Homology.CochainComplex.Truncation

/-!
# Actual non-alternating native Čech face arrows

The cochains include ALL tuples, including repeated indices. The map is actual
section pullback on each intersection, transported only by equality of opens.
It extends to the original integer Čech complex. Good truncation is a separate
functorial operation; no termwise boundedness of the original Čech complex is
asserted. Its face square is proved and remains a square under every scalar
extension.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite AlgebraicGeometry TopologicalSpace TopCat.Presheaf

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Canonical equality-of-opens transport, with the original base module action. -/
def faceOpenEqLinearEquiv
    {Y S : Scheme.{u}} (q : Y ⟶ S) (M : Y.Modules) {U V : Y.Opens} (h : U = V) :
    Scheme.Modules.sectionsModule q M U ≃ₗ[Γ(S, ⊤)] Scheme.Modules.sectionsModule q M V :=
  (eqToIso (congrArg (Scheme.Modules.sectionsModule q M) h)).toLinearEquiv

@[simp]
theorem faceOpenEqLinearEquiv_refl
    {Y S : Scheme.{u}} (q : Y ⟶ S) (M : Y.Modules) (U : Y.Opens)
    (s : Scheme.Modules.sectionsModule q M U) : faceOpenEqLinearEquiv q M rfl s = s := rfl

/-- Actual preimages preserve the intersections used by native Čech cochains. -/
theorem face_preimage_iInf {X Y : Scheme.{u}} (j : Y ⟶ X) {ι : Type*} [Finite ι] (U : ι → X.Opens) :
    j ⁻¹ᵁ (⨅ i, U i) = ⨅ i, j ⁻¹ᵁ U i := by
  ext y
  change (j y ∈ (((⨅ i, U i) : X.Opens) : Set X)) ↔
    (y ∈ (((⨅ i, j ⁻¹ᵁ U i) : Y.Opens) : Set Y))
  simp only [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  rfl

/-- Actual section pullback commutes with restriction after the explicit
intersection transports; both transports are canonical equality isomorphisms. -/
theorem faceSections_transport_restrict
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {U V : X.Opens} {U' V' : Y.Opens} (h : V ≤ U)
    (hU : j ⁻¹ᵁ U = U') (hV : j ⁻¹ᵁ V = V') (h' : V' ≤ U')
    (s : Scheme.Modules.sectionsModule q M U) :
    faceOpenEqLinearEquiv (j ≫ q) ((Scheme.Modules.pullback j).obj M) hV
        (faceSectionsLinearMap q j M V (Scheme.Modules.sectionsModuleRestrict q M h s)) =
      Scheme.Modules.sectionsModuleRestrict (j ≫ q) ((Scheme.Modules.pullback j).obj M) h'
        (faceOpenEqLinearEquiv (j ≫ q) ((Scheme.Modules.pullback j).obj M) hU
          (faceSectionsLinearMap q j M U s)) := by
  subst U'
  subst V'
  simp only [faceOpenEqLinearEquiv_refl]
  have ht := faceSectionsLinearMap_restrict q j M h s
  exact ht

/-- The actual face map on ALL native cochains, not an alternating-subcomplex avatar. -/
def cechFaceCochainLinearMap
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule q M (⨅ l, U (t l))) →ₗ[Γ(S, ⊤)]
      (∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule (j ≫ q)
        ((Scheme.Modules.pullback j).obj M) (⨅ l, j ⁻¹ᵁ U (t l))) :=
  LinearMap.pi fun t ↦
    (faceOpenEqLinearEquiv (j ≫ q) ((Scheme.Modules.pullback j).obj M)
      (face_preimage_iInf j (fun l ↦ U (t l)))).toLinearMap ∘ₗ
      faceSectionsLinearMap q j M (⨅ l, U (t l)) ∘ₗ LinearMap.proj t

@[simp]
theorem cechFaceCochainLinearMap_apply
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (c : ∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule q M (⨅ l, U (t l)))
    (t : Fin (n + 1) → ι) :
    cechFaceCochainLinearMap q j M U n c t =
      faceOpenEqLinearEquiv (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (face_preimage_iInf j (fun l ↦ U (t l)))
        (Scheme.Modules.pullbackSection j (c t)) := rfl

/-- The actual face cochain map commutes with the FULL native Čech differential. -/
theorem cechFaceCochainLinearMap_d
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (c : ∀ t : Fin (n + 1) → ι, Scheme.Modules.sectionsModule q M (⨅ l, U (t l))) :
    cechFaceCochainLinearMap q j M U (n + 1) (Scheme.Modules.cechModuleD q M U n c) =
      Scheme.Modules.cechModuleD (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (fun i ↦ j ⁻¹ᵁ U i) n (cechFaceCochainLinearMap q j M U n c) := by
  funext t
  simp only [cechFaceCochainLinearMap_apply, Scheme.Modules.cechModuleD_apply_apply]
  change (faceOpenEqLinearEquiv (j ≫ q) ((Scheme.Modules.pullback j).obj M)
    (face_preimage_iInf j (fun l ↦ U (t l))))
      ((faceSectionsLinearMap q j M (⨅ l, U (t l)))
        (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          Scheme.Modules.sectionsModuleRestrict q M
            (iInf_le_iInf_comp U t i.succAbove) (c (t ∘ i.succAbove)))) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, map_zsmul]
  congr 1
  exact faceSections_transport_restrict q j M (iInf_le_iInf_comp U t i.succAbove)
    (face_preimage_iInf j (fun l ↦ U ((t ∘ i.succAbove) l)))
    (face_preimage_iInf j (fun l ↦ U (t l)))
    (iInf_le_iInf_comp (fun a ↦ j ⁻¹ᵁ U a) t i.succAbove) (c (t ∘ i.succAbove))

/-- Actual native degreewise face section pullback as a chain map. -/
def cechModuleFaceMapNat
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    Scheme.Modules.cechModuleComplexNat q M U ⟶
      Scheme.Modules.cechModuleComplexNat (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (fun i ↦ j ⁻¹ᵁ U i) where
  f n := ModuleCat.ofHom (cechFaceCochainLinearMap q j M U n)
  comm' := by
    rintro n _ rfl
    rw [Scheme.Modules.cechModuleComplexNat_d, Scheme.Modules.cechModuleComplexNat_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    exact (cechFaceCochainLinearMap_d q j M U n c).symm

/-- The ACTUAL face arrow between the ORIGINAL integer native Čech complexes. -/
def cechModuleFaceMap
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    Scheme.Modules.cechModuleComplex q M U ⟶
      Scheme.Modules.cechModuleComplex (j ≫ q) ((Scheme.Modules.pullback j).obj M)
        (fun i ↦ j ⁻¹ᵁ U i) :=
  HomologicalComplex.extendMap (cechModuleFaceMapNat q j M U) ComplexShape.embeddingUpNat

/-- Good truncation is compatible with the ACTUAL face arrow, without claiming
that the original non-alternating Čech complex is bounded termwise. -/
theorem cechModuleFaceMap_truncation_square
    {X Y S : Scheme.{u}} (q : X ⟶ S) (j : Y ⟶ X) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (b : ℤ) :
    CochainComplex.truncLEMap (cechModuleFaceMap q j M U) b ≫
        (Scheme.Modules.cechModuleComplex (j ≫ q) ((Scheme.Modules.pullback j).obj M)
          (fun i ↦ j ⁻¹ᵁ U i)).ιTruncLE b =
      (Scheme.Modules.cechModuleComplex q M U).ιTruncLE b ≫ cechModuleFaceMap q j M U :=
  CochainComplex.ιTruncLE_naturality _ _

end ZInQ.Contrib.CloudR2Poincare.L1
