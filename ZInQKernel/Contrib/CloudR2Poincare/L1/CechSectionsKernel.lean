import ZInQKernel.Contrib.CloudR2Poincare.L1.CechZeroCompatibility
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Actual coefficient sections are the degree-zero Čech cycles

This constructs and checks the actual augmentation from restrictions, using
native sheaf gluing. Its relation to the canonical tensor map is provided by
CechZeroCompatibility, rather than by an arbitrary cohomology isomorphism.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The actual augmentation lands in degree-zero cycles. -/
theorem cechSectionsDiagonal_d_zero {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (s : Scheme.Modules.sectionsModule f M ⊤) :
    Scheme.Modules.cechModuleD f M U 0 (cechSectionsDiagonal f M U ⊤ (fun _ ↦ le_top) s) = 0 := by
  funext z
  rw [Scheme.Modules.cechModuleD_apply_apply, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    cechSectionsDiagonal_apply, Scheme.Modules.sectionsModuleRestrict_comp]
  simp

/-- Read the section at an actual vertex of a zero cochain. -/
def cechVertexSection {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens)
    (c : ∀ t : Fin 1 → ι, Scheme.Modules.sectionsModule f M (⨅ l, U (t l)))
    (i : ι) : Scheme.Modules.sectionsModule f M (U i) :=
  Scheme.Modules.sectionsModuleRestrict f M (by simp only [iInf_const]; exact le_rfl)
    (c (fun _ ↦ i))

/-- The literal zero-cocycle equation makes the vertex sections compatible on overlaps. -/
theorem cechVertexSection_compatible {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens)
    (c : ∀ t : Fin 1 → ι, Scheme.Modules.sectionsModule f M (⨅ l, U (t l)))
    (hc : Scheme.Modules.cechModuleD f M U 0 c = 0) :
    TopCat.Presheaf.IsCompatible M.presheaf U (cechVertexSection f M U c) := by
  intro i j
  let z : Fin 2 → ι := Fin.cons i (fun _ ↦ j)
  have hz0 : z ∘ (0 : Fin 2).succAbove = fun _ : Fin 1 ↦ j := by
    funext l; fin_cases l; rfl
  have hz1 : z ∘ (1 : Fin 2).succAbove = fun _ : Fin 1 ↦ i := by
    funext l; fin_cases l; rfl
  have hd : ((TopCat.Presheaf.cechComplex U).obj M.presheaf).d 0 1 c = 0 := by
    rw [← Scheme.Modules.cechModuleD_apply f M U 0 c]
    exact hc
  have h0 := congrFun hd z
  rw [TopCat.Presheaf.cechComplex_d_apply, Fin.sum_univ_two] at h0
  have hzj : (⨅ l, U (z l)) ≤ (⨅ l, U ((fun _ : Fin 1 ↦ j) l)) :=
    le_iInf fun _ ↦ iInf_le _ 1
  have hzi : (⨅ l, U (z l)) ≤ (⨅ l, U ((fun _ : Fin 1 ↦ i) l)) :=
    le_iInf fun _ ↦ iInf_le _ 0
  rw [TopCat.Presheaf.map_homOfLE_apply_congr U M.presheaf c hz0 _ hzj,
    TopCat.Presheaf.map_homOfLE_apply_congr U M.presheaf c hz1 _ hzi] at h0
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at h0
  have hpair := sub_eq_zero.mp ((sub_eq_add_neg _ _).trans h0)
  have hz : U i ⊓ U j ≤ (⨅ l, U (z l)) := by
    refine le_iInf fun l ↦ ?_
    fin_cases l
    · exact inf_le_left
    · exact inf_le_right
  have hres := congrArg (M.presheaf.map (homOfLE hz).op) hpair
  rw [TopCat.Presheaf.map_homOfLE_map_homOfLE_apply,
    TopCat.Presheaf.map_homOfLE_map_homOfLE_apply] at hres
  change M.presheaf.map (homOfLE inf_le_left).op (cechVertexSection f M U c i) =
    M.presheaf.map (homOfLE inf_le_right).op (cechVertexSection f M U c j)
  simpa only [cechVertexSection, Scheme.Modules.sectionsModuleRestrict_apply,
    TopCat.Presheaf.map_homOfLE_map_homOfLE_apply] using hres.symm

/-- The actual coefficient augmentation is injective for an open cover. -/
theorem injective_cechSectionsDiagonal {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Injective (cechSectionsDiagonal f M U ⊤ (fun _ ↦ le_top)) := by
  intro s t hst
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, Scheme.Modules.isSheaf M⟩
  apply TopCat.Sheaf.eq_of_locally_eq' F U ⊤ (fun _ ↦ homOfLE le_top) (by rw [hU]) s t
  intro i
  change M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op s =
    M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op t
  have hb : U i ≤ (⨅ l : Fin 1, U ((fun _ : Fin 1 ↦ i) l)) :=
    le_iInf fun _ ↦ le_rfl
  have h := congrArg (Scheme.Modules.sectionsModuleRestrict f M hb)
    (congrFun hst (fun _ : Fin 1 ↦ i))
  rw [cechSectionsDiagonal_apply, cechSectionsDiagonal_apply,
    Scheme.Modules.sectionsModuleRestrict_comp, Scheme.Modules.sectionsModuleRestrict_comp] at h
  exact h

/-- Every actual zero cochain glues to an actual coefficient section, without
cohomology finiteness or geometric hypotheses. -/
theorem exists_section_of_cechZeroCycle {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (c : ∀ t : Fin 1 → ι, Scheme.Modules.sectionsModule f M (⨅ l, U (t l)))
    (hc : Scheme.Modules.cechModuleD f M U 0 c = 0) :
    ∃ s : Scheme.Modules.sectionsModule f M ⊤,
      cechSectionsDiagonal f M U ⊤ (fun _ ↦ le_top) s = c := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, Scheme.Modules.isSheaf M⟩
  obtain ⟨s, hs, _⟩ := TopCat.Sheaf.existsUnique_gluing' F U ⊤
    (fun _ ↦ homOfLE le_top) (by rw [hU]) (cechVertexSection f M U c)
    (cechVertexSection_compatible f M U c hc)
  refine ⟨s, funext fun t ↦ ?_⟩
  have ht : (fun _ : Fin 1 ↦ t 0) = t := by
    funext l
    rw [Subsingleton.elim l 0]
  have hloc := hs (t 0)
  have hi : (⨅ l, U (t l)) ≤ U (t 0) := iInf_le _ 0
  have h := congrArg (M.presheaf.map (homOfLE hi).op) hloc
  change Scheme.Modules.sectionsModuleRestrict f M hi
    (Scheme.Modules.sectionsModuleRestrict f M le_top s) =
      Scheme.Modules.sectionsModuleRestrict f M hi (cechVertexSection f M U c (t 0)) at h
  rw [Scheme.Modules.sectionsModuleRestrict_comp] at h
  rw [cechSectionsDiagonal_apply]
  refine h.trans ?_
  change M.presheaf.map (homOfLE hi).op
    (M.presheaf.map (homOfLE (by simp only [iInf_const]; exact le_rfl)).op
      (c (fun _ : Fin 1 ↦ t 0))) = c t
  rw [TopCat.Presheaf.map_homOfLE_map_homOfLE_apply]
  rw [TopCat.Presheaf.map_homOfLE_apply_congr U M.presheaf c ht _ le_rfl]
  exact TopCat.Presheaf.map_homOfLE_self_apply M.presheaf le_rfl (c t)

/-- The actual augmentation, with its values regarded as actual linear d0 cycles. -/
def cechSectionsCycleMap {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    Scheme.Modules.sectionsModule f M ⊤ →ₗ[Γ(S, ⊤)] LinearMap.ker (Scheme.Modules.cechModuleD f M U 0) :=
  (cechSectionsDiagonal f M U ⊤ (fun _ ↦ le_top)).codRestrict _
    (fun s ↦ cechSectionsDiagonal_d_zero f M U s)

/-- The actual augmentation identifies coefficient sections with the actual linear kernel. -/
theorem bijective_cechSectionsCycleMap {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Function.Bijective (cechSectionsCycleMap f M U) := by
  constructor
  · intro s t h
    apply injective_cechSectionsDiagonal f M U hU
    exact congrArg Subtype.val h
  · intro c
    obtain ⟨s, hs⟩ := exists_section_of_cechZeroCycle f M U hU c.val c.property
    exact ⟨s, Subtype.ext hs⟩

/-- The canonical linear isomorphism from actual coefficient sections to zero Čech cycles. -/
def cechSectionsCycleEquiv {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Scheme.Modules.sectionsModule f M ⊤ ≃ₗ[Γ(S, ⊤)] LinearMap.ker (Scheme.Modules.cechModuleD f M U 0) :=
  LinearEquiv.ofBijective _ (bijective_cechSectionsCycleMap f M U hU)

/-- The actual restriction augmentation is a categorical kernel fork. -/
def cechCoefficientAugmentationIsKernel {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    IsLimit (KernelFork.ofι (ModuleCat.ofHom (cechSectionsDiagonal f M U ⊤ (fun _ ↦ le_top)))
      (by
        rw [Scheme.Modules.cechModuleComplexNat_d]
        ext s
        exact cechSectionsDiagonal_d_zero f M U s) :
      KernelFork ((Scheme.Modules.cechModuleComplexNat f M U).d 0 1)) := by
  apply ModuleCat.isLimitKernelFork
  · rw [Scheme.Modules.cechModuleComplexNat_d]
    change Function.Exact (cechSectionsDiagonal f M U ⊤ (fun _ ↦ le_top)) (Scheme.Modules.cechModuleD f M U 0)
    intro c
    constructor
    · exact exists_section_of_cechZeroCycle f M U hU c
    · rintro ⟨s, rfl⟩
      exact cechSectionsDiagonal_d_zero f M U s
  · exact injective_cechSectionsDiagonal f M U hU

/-- The actual coefficient sections are canonically the categorical d0 kernel
of the ORIGINAL module-valued Čech complex. -/
def cechCoefficientKernelIso {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    Scheme.Modules.sectionsModule f M ⊤ ≅
      kernel ((Scheme.Modules.cechModuleComplexNat f M U).d 0 1) :=
  IsLimit.conePointUniqueUpToIso (cechCoefficientAugmentationIsKernel f M U hU)
    (limit.isLimit (parallelPair ((Scheme.Modules.cechModuleComplexNat f M U).d 0 1) 0))

/-- The canonical isomorphism's inclusion is LITERALLY the restriction augmentation. -/
theorem cechCoefficientKernelIso_hom_ι {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) :
    (cechCoefficientKernelIso f M U hU).hom ≫
      kernel.ι ((Scheme.Modules.cechModuleComplexNat f M U).d 0 1) =
    ModuleCat.ofHom (cechSectionsDiagonal f M U ⊤ (fun _ ↦ le_top)) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (cechCoefficientAugmentationIsKernel f M U hU)
    (limit.isLimit (parallelPair ((Scheme.Modules.cechModuleComplexNat f M U).d 0 1) 0)) WalkingParallelPair.zero

end ZInQ.Contrib.CloudR2Poincare.L1
