import ZInQKernel.Contrib.CloudR2Poincare.L1.CechBaseChangeSectionSquares
import ZInQKernel.Contrib.CloudR2Poincare.L1.CechCoefficientMaps
import ZInQKernel.Contrib.CloudR2Poincare.L1.AdjunctionHZero
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechBaseChange

/-!
# Canonical coefficient, cover and native scalar Čech transports

Every map here is fixed by actual coefficient maps, equality-of-cover
transports, or the existing native scalar base-change map on pure tensors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Actual coefficient isomorphism on the full Nat Čech complex. -/
def cechModuleCoefficientIsoNat
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (e : M ≅ N)
    {ι : Type u} (U : ι → X.Opens) :
    Scheme.Modules.cechModuleComplexNat q M U ≅ Scheme.Modules.cechModuleComplexNat q N U where
  hom := cechModuleCoefficientMapNat q e.hom U
  inv := cechModuleCoefficientMapNat q e.inv U
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext t
    change e.inv.app (⨅ l, U (t l)) (e.hom.app (⨅ l, U (t l)) (c t)) = c t
    exact coefficientIso_inv_hom_sections e.symm _ _
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    funext t
    change e.hom.app (⨅ l, U (t l)) (e.inv.app (⨅ l, U (t l)) (c t)) = c t
    exact coefficientIso_inv_hom_sections e _ _

/-- Coefficient isomorphism on the ORIGINAL integer Čech complex. -/
def cechModuleCoefficientIso
    {X S : Scheme.{u}} (q : X ⟶ S) {M N : X.Modules} (e : M ≅ N)
    {ι : Type u} (U : ι → X.Opens) :
    Scheme.Modules.cechModuleComplex q M U ≅ Scheme.Modules.cechModuleComplex q N U :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} Γ(S, ⊤))).mapIso
    (cechModuleCoefficientIsoNat q e U)

/-- Canonical equality-of-covers isomorphism on the actual Nat complex. -/
def cechModuleCoverEqIsoNat
    {X S : Scheme.{u}} (q : X ⟶ S) (M : X.Modules) {ι : Type u}
    {U V : ι → X.Opens} (h : U = V) :
    Scheme.Modules.cechModuleComplexNat q M U ≅ Scheme.Modules.cechModuleComplexNat q M V :=
  eqToIso (congrArg (Scheme.Modules.cechModuleComplexNat q M) h)

/-- Canonical equality-of-covers isomorphism on the ORIGINAL integer complex. -/
def cechModuleCoverEqIso
    {X S : Scheme.{u}} (q : X ⟶ S) (M : X.Modules) {ι : Type u}
    {U V : ι → X.Opens} (h : U = V) :
    Scheme.Modules.cechModuleComplex q M U ≅ Scheme.Modules.cechModuleComplex q M V :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} Γ(S, ⊤))).mapIso
    (cechModuleCoverEqIsoNat q M h)

/-- Exact cochain formula for the canonical equality-of-cover map. -/
theorem cechModuleCoverEqIsoNat_hom_f_apply
    {X S : Scheme.{u}} (q : X ⟶ S) (M : X.Modules) {ι : Type u}
    {U V : ι → X.Opens} (h : U = V) (n : ℕ)
    (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) (t : Fin (n + 1) → ι) :
    (cechModuleCoverEqIsoNat q M h).hom.f n c t =
      faceOpenEqLinearEquiv q M (congrArg (fun W : ι → X.Opens ↦ ⨅ l, W (t l)) h) (c t) := by
  subst V
  rfl

/-- The native restriction-based open equality map is the SAME canonical
open transport used by the actual face map. -/
theorem nativeSectionsModuleEqLinearEquiv_eq_faceOpenEq
    {X S : Scheme.{u}} (q : X ⟶ S) (M : X.Modules)
    {U V : X.Opens} (h : U = V) (s : Scheme.Modules.sectionsModule q M U) :
    Scheme.Modules.sectionsModuleEqLinearEquiv (p := q) M h.symm s =
      faceOpenEqLinearEquiv q M h s := by
  change Scheme.Modules.sectionsModuleRestrict q M h.ge s = _
  rw [Scheme.Modules.sectionsModuleRestrict_apply]
  exact (faceOpenEqLinearEquiv_eq_restrict q M h s).symm

/-- ACTUAL pure-tensor formula for the native Nat Čech base-change iso. -/
theorem nativeCechBaseChangeIsoNat_hom_f_tensor
    {X XB S T : Scheme.{u}} {q : X ⟶ S} {qB : XB ⟶ T} {g : T ⟶ S} {a : XB ⟶ X}
    (HC : IsPullback a qB q g) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineInter : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (n : ℕ) (b : Γ(T, ⊤)) (c : (Scheme.Modules.cechModuleComplexNat q M U).X n) :
    (Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineInter).hom.f n
        ((ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
          ((Scheme.Modules.cechModuleComplexNat q M U).X n)) (b ⊗ₜ c)) =
      Scheme.Modules.cechModuleBaseChange HC M hg U n (b ⊗ₜ c) := by
  change Scheme.Modules.cechModuleBaseChange HC M hg U n
      ((ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
        ((Scheme.Modules.cechModuleComplexNat q M U).X n)).symm
        ((ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
          ((Scheme.Modules.cechModuleComplexNat q M U).X n)) (b ⊗ₜ c))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The actual native scalar Čech comparison is termwise actual section
pullback, with ONLY the canonical finite-intersection open transport. -/
theorem nativeCechBaseChangeIsoNat_hom_f_tensor_apply
    {X XB S T : Scheme.{u}} {q : X ⟶ S} {qB : XB ⟶ T} {g : T ⟶ S} {a : XB ⟶ X}
    (HC : IsPullback a qB q g) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (affineInter : ∀ n (t : Fin (n + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (n : ℕ) (b : Γ(T, ⊤)) (c : (Scheme.Modules.cechModuleComplexNat q M U).X n)
    (t : Fin (n + 1) → ι) :
    (Scheme.Modules.cechModuleComplexNatBaseChangeIso HC M hg U affineInter).hom.f n
        ((ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
          ((Scheme.Modules.cechModuleComplexNat q M U).X n)) (b ⊗ₜ c)) t =
      faceOpenEqLinearEquiv qB ((Scheme.Modules.pullback a).obj M)
        (face_preimage_iInf a (fun l ↦ U (t l)))
        (b • (show Scheme.Modules.sectionsModule qB ((Scheme.Modules.pullback a).obj M)
          (a ⁻¹ᵁ (⨅ l, U (t l))) from Scheme.Modules.pullbackSection a (c t))) := by
  rw [nativeCechBaseChangeIsoNat_hom_f_tensor, Scheme.Modules.cechModuleBaseChange_tmul]
  exact (nativeSectionsModuleEqLinearEquiv_eq_faceOpenEq qB ((Scheme.Modules.pullback a).obj M)
    (a.preimage_iInf (fun l ↦ U (t l))) _)

end ZInQ.Contrib.CloudR2Poincare.L1
