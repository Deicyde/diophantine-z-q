import ZInQKernel.Contrib.CloudR2Poincare.L1.CechSectionsKernel

/-!
# The actual coefficient tensor map from canonical Čech-kernel base change

The kernel-preservation premise below is an ordinary internal argument. The
conclusion is about the ACTUAL native coefficient-sections map, not a chosen
cohomology-object isomorphism. All commuting squares are the actual native
Čech/tensor maps.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Identify the native scalar-extended Čech isomorphism on actual tensor cochains. -/
theorem cechBaseChangeIso_hom_f_tensor
    {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
    (square : IsPullback g' f' f g) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ (q : ℕ) (t : Fin (q + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (q : ℕ) (x : Γ(T, ⊤) ⊗[Γ(S, ⊤)] ((Scheme.Modules.cechModuleComplexNat f M U).X q)) :
    (Scheme.Modules.cechModuleComplexNatBaseChangeIso square M hg U hU).hom.f q
        (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
          ((Scheme.Modules.cechModuleComplexNat f M U).X q) x) =
      Scheme.Modules.cechModuleBaseChange square M hg U q x := by
  change Scheme.Modules.cechModuleBaseChange square M hg U q
    ((ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
      ((Scheme.Modules.cechModuleComplexNat f M U).X q)).symm
        (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
          ((Scheme.Modules.cechModuleComplexNat f M U).X q) x)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The canonical coefficient tensor map, with only the target top-open equality read explicitly. -/
def coefficientBaseChangeTop
    {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
    (square : IsPullback g' f' f g) (M : X.Modules)
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom) :
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Scheme.Modules.sectionsModule f M ⊤ →ₗ[Γ(T, ⊤)]
      Scheme.Modules.sectionsModule f' ((Scheme.Modules.pullback g').obj M) ⊤ :=
  (Scheme.Modules.sectionsModuleEqLinearEquiv (p := f') ((Scheme.Modules.pullback g').obj M)
    g'.preimage_top.symm).toLinearMap ∘ₗ Scheme.Modules.sectionsModuleBaseChange square M hg ⊤

/-- The actual tensor augmentation square, now with the target read on top. -/
theorem cechDiagonal_coefficientBaseChangeTop
    {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
    (square : IsPullback g' f' f g) (M : X.Modules)
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} (U : ι → X.Opens)
    (x : Γ(T, ⊤) ⊗[Γ(S, ⊤)] Scheme.Modules.sectionsModule f M ⊤) :
    Scheme.Modules.cechModuleBaseChange square M hg U 0
      ((cechSectionsDiagonal f M U ⊤ (fun _ ↦ le_top)).baseChange Γ(T, ⊤) x) =
    cechSectionsDiagonal f' ((Scheme.Modules.pullback g').obj M)
      (fun i ↦ g' ⁻¹ᵁ U i) ⊤ (fun _ ↦ le_top) (coefficientBaseChangeTop square M hg x) := by
  rw [cechDiagonal_baseChange]
  funext t
  simp only [coefficientBaseChangeTop, LinearMap.coe_comp, Function.comp_apply,
    cechSectionsDiagonal_apply, Scheme.Modules.sectionsModuleEqLinearEquiv,
    LinearEquiv.coe_toLinearMap]
  exact (Scheme.Modules.sectionsModuleRestrict_comp f' ((Scheme.Modules.pullback g').obj M)
    le_top g'.preimage_top.symm.le _).symm

/-- If the ACTUAL d0 Čech kernel comparison is invertible, so is the ACTUAL
canonical coefficient-sections tensor map. -/
theorem bijective_coefficientBaseChange_of_cech_kernelComparison
    {X Y S T : Scheme.{u}} {f : X ⟶ S} {f' : Y ⟶ T} {g : T ⟶ S} {g' : Y ⟶ X}
    (square : IsPullback g' f' f g) (M : X.Modules)
    [IsAffine S] [IsAffine T] [M.IsQuasicoherent]
    [Algebra Γ(S, ⊤) Γ(T, ⊤)] (hg : algebraMap Γ(S, ⊤) Γ(T, ⊤) = g.appTop.hom)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (hU : ∀ (q : ℕ) (t : Fin (q + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (hK : IsIso (kernelComparison ((Scheme.Modules.cechModuleComplexNat f M U).d 0 1)
      (ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))))) :
    Function.Bijective (Scheme.Modules.sectionsModuleBaseChange square M hg ⊤) := by
  let F := ModuleCat.extendScalars (algebraMap Γ(S, ⊤) Γ(T, ⊤))
  let A := Scheme.Modules.cechModuleComplexNat f M U
  let M' := (Scheme.Modules.pullback g').obj M
  let U' := fun i ↦ g' ⁻¹ᵁ U i
  let B := Scheme.Modules.cechModuleComplexNat f' M' U'
  have hcover' : ⨆ i, U' i = ⊤ := by
    rw [← g'.preimage_iSup, hcover, g'.preimage_top]
  let eA := cechCoefficientKernelIso f M U hcover
  let eB := cechCoefficientKernelIso f' M' U' hcover'
  let tensor := ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤)
    (Scheme.Modules.sectionsModule f M ⊤)
  let β : F.obj (Scheme.Modules.sectionsModule f M ⊤) ⟶ Scheme.Modules.sectionsModule f' M' ⊤ :=
    ModuleCat.ofHom (X := F.obj (Scheme.Modules.sectionsModule f M ⊤))
      (Y := Scheme.Modules.sectionsModule f' M' ⊤)
      ((coefficientBaseChangeTop square M hg).comp tensor.symm.toLinearMap)
  let ec := Scheme.Modules.cechModuleComplexNatBaseChangeIso square M hg U hU
  have hk : IsIso (kernelComparison (A.d 0 1) F) := hK
  haveI := hk
  let ek := kernel.mapIso (F.map (A.d 0 1)) (B.d 0 1)
    (asIso (ec.hom.f 0)) (asIso (ec.hom.f 1)) (ec.hom.comm 0 1).symm
  let e := F.mapIso eA ≪≫ asIso (kernelComparison (A.d 0 1) F) ≪≫ ek ≪≫ eB.symm
  let augA : Scheme.Modules.sectionsModule f M ⊤ ⟶ A.X 0 :=
    ModuleCat.ofHom (X := Scheme.Modules.sectionsModule f M ⊤) (Y := A.X 0)
      (cechSectionsDiagonal f M U ⊤ (fun _ ↦ le_top))
  let augB : Scheme.Modules.sectionsModule f' M' ⊤ ⟶ B.X 0 :=
    ModuleCat.ofHom (X := Scheme.Modules.sectionsModule f' M' ⊤) (Y := B.X 0)
      (cechSectionsDiagonal f' M' U' ⊤ (fun _ ↦ le_top))
  have hAugA : eA.hom ≫ kernel.ι (A.d 0 1) = augA :=
    cechCoefficientKernelIso_hom_ι f M U hcover
  have hAugB : eB.hom ≫ kernel.ι (B.d 0 1) = augB :=
    cechCoefficientKernelIso_hom_ι f' M' U' hcover'
  have hβ : β ≫ augB = F.map augA ≫ ec.hom.f 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    obtain ⟨x, rfl⟩ := tensor.surjective v
    change cechSectionsDiagonal f' M' U' ⊤ (fun _ ↦ le_top)
      (coefficientBaseChangeTop square M hg (tensor.symm (tensor x))) = _
    rw [LinearEquiv.symm_apply_apply]
    change cechSectionsDiagonal f' M' U' ⊤ (fun _ ↦ le_top)
      (coefficientBaseChangeTop square M hg x) =
      (ec.hom.f 0).hom ((F.map augA).hom (tensor x))
    have hn : (F.map augA).hom (tensor x) =
        ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤) (A.X 0)
          (augA.hom.baseChange Γ(T, ⊤) x) :=
      ModuleCat.tensorEquivExtendScalars_naturality Γ(S, ⊤) Γ(T, ⊤) augA x
    rw [hn]
    have hc := cechBaseChangeIso_hom_f_tensor square M hg U hU 0
      (augA.hom.baseChange Γ(T, ⊤) x)
    change _ = (ec.hom.f 0)
      (ModuleCat.tensorEquivExtendScalars Γ(S, ⊤) Γ(T, ⊤) (A.X 0)
        (augA.hom.baseChange Γ(T, ⊤) x))
    rw [hc]
    exact (cechDiagonal_coefficientBaseChangeTop square M hg U x).symm
  have he : e.hom ≫ augB = F.map augA ≫ ec.hom.f 0 := by
    rw [← hAugB]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc, ek, kernel.mapIso_hom, kernel.map, kernel.lift_ι, kernel.lift_ι_assoc,
      asIso_hom, Functor.mapIso_hom, kernelComparison_comp_ι_assoc]
    rw [← Category.assoc, ← F.map_comp, hAugA]
  haveI : Mono augB := by
    rw [← hAugB]
    infer_instance
  have hβe : β = e.hom := (cancel_mono augB).mp (hβ.trans he.symm)
  haveI : IsIso β := hβe ▸ inferInstance
  have hbij : Function.Bijective β := ConcreteCategory.bijective_of_isIso β
  have htop : Function.Bijective (coefficientBaseChangeTop square M hg) := by
    constructor
    · intro x y hxy
      apply tensor.injective
      apply hbij.1
      change (coefficientBaseChangeTop square M hg) (tensor.symm (tensor x)) =
        (coefficientBaseChangeTop square M hg) (tensor.symm (tensor y))
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact hxy
    · intro z
      obtain ⟨v, hv⟩ := hbij.2 z
      exact ⟨tensor.symm v, hv⟩
  let top := Scheme.Modules.sectionsModuleEqLinearEquiv (p := f') M' g'.preimage_top.symm
  constructor
  · intro x y hxy
    apply htop.1
    exact congrArg top hxy
  · intro z
    obtain ⟨x, hx⟩ := htop.2 (top z)
    exact ⟨x, top.injective hx⟩

end ZInQ.Contrib.CloudR2Poincare.L1
