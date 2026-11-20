import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Local lifts for degree-one cohomology

In an injective presentation of an abelian sheaf, a degree-one class is represented by
a section of the quotient. Lifts of that section are locally nonempty, and any two
lifts differ by a unique section of the original sheaf. These are the torsor
properties needed before comparing finite constant coefficients between sites.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace ZInQ.Manuscript.T10Proetale

universe u v w w'

noncomputable section

section Ext

variable {D : Type u} [Category.{v} D] [Abelian D] [EnoughInjectives D]

/-- The first short exact sequence in an injective presentation. -/
abbrev injectivePresentation (F : D) : ShortComplex D :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
    (cokernel.condition (Injective.ι F))

/-- The embedding into an injective and its cokernel form a short exact sequence. -/
theorem injectivePresentation_shortExact (F : D) : (injectivePresentation F).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι F))

variable [HasExt.{w'} D]

/-- Apply the boundary map in degree zero to a morphism into the quotient. -/
def extensionClass {R F : D} (s : R ⟶ (injectivePresentation F).X₃) : Ext R F 1 :=
  (Ext.mk₀ s).comp (injectivePresentation_shortExact F).extClass (zero_add 1)

/-- Every degree-one class is given by a morphism into the quotient of an injective. -/
theorem extensionClass_surjective {R F : D} :
    Function.Surjective (extensionClass (R := R) (F := F)) := by
  intro e
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ R (injectivePresentation_shortExact F) e
    (Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨s, hs⟩ := (Ext.mk₀_bijective R (injectivePresentation F).X₃).surjective z
  exact ⟨s, by simpa only [extensionClass, hs] using hz⟩

/-- The class vanishes exactly when its defining morphism lifts through the quotient. -/
theorem extensionClass_eq_zero_iff {R F : D} (s : R ⟶ (injectivePresentation F).X₃) :
    extensionClass s = 0 ↔ ∃ t : R ⟶ Injective.under F,
      t ≫ (injectivePresentation F).g = s := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃ R (injectivePresentation_shortExact F)
      (Ext.mk₀ s) (zero_add 1) h
    obtain ⟨t, ht⟩ := (Ext.mk₀_bijective R (Injective.under F)).surjective z
    refine ⟨t, (Ext.mk₀_bijective R _).injective ?_⟩
    rw [← Ext.mk₀_comp_mk₀, ht]
    exact hz
  · rintro ⟨t, rfl⟩
    change (Ext.mk₀ (t ≫ (injectivePresentation F).g)).comp
      (injectivePresentation_shortExact F).extClass (zero_add 1) = 0
    rw [← Ext.mk₀_comp_mk₀_assoc, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

/-- Two representatives define the same class exactly when their difference lifts. -/
theorem extensionClass_eq_iff {R F : D} (s t : R ⟶ (injectivePresentation F).X₃) :
    extensionClass s = extensionClass t ↔ ∃ d : R ⟶ Injective.under F,
      d ≫ (injectivePresentation F).g = s - t := by
  rw [← extensionClass_eq_zero_iff]
  change _ ↔ (Ext.mk₀ (s - t)).comp _ _ = 0
  rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.add_comp, Ext.neg_comp, ← sub_eq_add_neg]
  exact sub_eq_zero.symm

end Ext

section Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})}

/-- The set of lifts of a section through the last map of an extension. -/
abbrev sectionLifts {U : C} (s : S.X₃.obj.obj (op U)) :=
  { t : S.X₂.obj.obj (op U) // S.g.hom.app (op U) t = s }

/-- Lifts restrict along arrows in the site. -/
def restrictLift {U V : C} (f : V ⟶ U) {s : S.X₃.obj.obj (op U)}
    (t : sectionLifts (S := S) s) : sectionLifts (S := S) (S.X₃.obj.map f.op s) :=
  ⟨S.X₂.obj.map f.op t.1, by
    rw [NatTrans.naturality_apply S.g.hom f.op, t.2]⟩

/-- The sieve on which a given section lifts is a cover. -/
theorem local_sectionLifts [HasSheafify J AddCommGrpCat.{w}]
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (hS : S.ShortExact) {U : C} (s : S.X₃.obj.obj (op U)) :
    Presheaf.imageSieve S.g.hom s ∈ J U := by
  let : IsRegularEpiCategory (Sheaf J AddCommGrpCat.{w}) :=
    regularEpiCategoryOfNormalEpiCategory
  let : Epi S.g := hS.epi_g
  let : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat S.g).2 inferInstance
  exact Presheaf.imageSieve_mem J S.g.hom s

/-- The kernel of the quotient can be computed on sections, since evaluation preserves kernels. -/
theorem exact_and_injective_on_sections [HasSheafify J AddCommGrpCat.{w}]
    (hS : S.ShortExact) (U : C) :
    (∀ x : S.X₂.obj.obj (op U), S.g.hom.app (op U) x = 0 →
      ∃ a : S.X₁.obj.obj (op U), S.f.hom.app (op U) a = x) ∧
      Function.Injective (S.f.hom.app (op U)) := by
  let E := (sheafSections J AddCommGrpCat.{w}).obj (op U)
  let : PreservesFiniteLimits E := preservesFiniteLimits_of_natIso
    (sheafSectionsNatIsoEvaluation (J := J) (A := AddCommGrpCat.{w}) (X := U)).symm
  let : IsRegularEpiCategory (Sheaf J AddCommGrpCat.{w}) :=
    regularEpiCategoryOfNormalEpiCategory
  have hE : IsLimit (KernelFork.ofι (S.map E).f (S.map E).zero) :=
    (KernelFork.ofι S.f S.zero).mapIsLimit hS.fIsKernel E
  have hK := (S.map E).exact_and_mono_f_iff_f_is_kernel.mpr ⟨hE⟩
  exact ⟨(S.map E).ab_exact_iff.mp hK.1, (AddCommGrpCat.mono_iff_injective _).mp hK.2⟩

/-- The kernel sheaf acts by translation, freely and transitively on each nonempty fibre. -/
theorem sectionLifts_existsUnique_translate [HasSheafify J AddCommGrpCat.{w}]
    (hS : S.ShortExact) {U : C} {s : S.X₃.obj.obj (op U)} (x y : sectionLifts (S := S) s) :
    ∃! a : S.X₁.obj.obj (op U), S.f.hom.app (op U) a + x.1 = y.1 := by
  obtain ⟨hex, hinj⟩ := exact_and_injective_on_sections hS U
  obtain ⟨a, ha⟩ := hex (y.1 - x.1) (by rw [map_sub, x.2, y.2, sub_self])
  have ht : S.f.hom.app (op U) a + x.1 = y.1 := by rw [ha, sub_add_cancel]
  exact ⟨a, ht, fun b hb => hinj (add_right_cancel (hb.trans ht.symm))⟩

/-- Kernel translation commutes with restriction on the site. -/
theorem translate_restrict {U V : C} (f : V ⟶ U) (a : S.X₁.obj.obj (op U))
    (x : S.X₂.obj.obj (op U)) :
    S.X₂.obj.map f.op (S.f.hom.app (op U) a + x) =
      S.f.hom.app (op V) (S.X₁.obj.map f.op a) + S.X₂.obj.map f.op x := by
  rw [map_add, NatTrans.naturality_apply S.f.hom f.op]

section Terminal

variable [HasSheafify J AddCommGrpCat.{w}] [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{w})

private def sectionHomEquiv (G : Sheaf J AddCommGrpCat.{w}) :
    (((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) ⟶ G) ≃
      G.obj.obj (op T) :=
  (Equiv.ofBijective _ (Ext.mk₀_bijective _ _)).trans (Sheaf.H.equiv₀ G hT).toEquiv

/-- A section of the quotient in the injective presentation determines a degree-one class. -/
def classOfSection (s : (injectivePresentation F).X₃.obj.obj (op T)) : F.H 1 :=
  extensionClass ((sectionHomEquiv hT (injectivePresentation F).X₃).symm s)

/-- Every derived degree-one cohomology class on a site with a terminal object is
represented by such a section, whose local lifts are the fibres studied above. -/
theorem classOfSection_surjective : Function.Surjective (classOfSection hT F) :=
  extensionClass_surjective.comp (sectionHomEquiv hT (injectivePresentation F).X₃).symm.surjective

/-- The class is zero exactly when the section has a global lift. -/
theorem classOfSection_eq_zero_iff (s : (injectivePresentation F).X₃.obj.obj (op T)) :
    classOfSection hT F s = 0 ↔ Nonempty (sectionLifts (S := injectivePresentation F) s) := by
  let P := injectivePresentation F
  let E (G : Sheaf J AddCommGrpCat.{w}) := sectionHomEquiv hT G
  have hE (t : ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift ℤ))) ⟶ P.X₂) :
      E P.X₃ (t ≫ P.g) = P.g.hom.app (op T) (E P.X₂ t) := by
    change Sheaf.H.equiv₀ P.X₃ hT (Ext.mk₀ (t ≫ P.g)) =
      P.g.hom.app (op T) (Sheaf.H.equiv₀ P.X₂ hT (Ext.mk₀ t))
    rw [← Ext.mk₀_comp_mk₀]
    exact (Sheaf.H.equiv₀_naturality hT P.g (Ext.mk₀ t)).symm
  rw [classOfSection, extensionClass_eq_zero_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨⟨E P.X₂ t, ?_⟩⟩
    rw [← hE t, ht]
    exact (E P.X₃).apply_symm_apply s
  · rintro ⟨⟨t, ht⟩⟩
    refine ⟨(E P.X₂).symm t, (E P.X₃).injective ?_⟩
    rw [hE, (E P.X₂).apply_symm_apply, (E P.X₃).apply_symm_apply]
    exact ht

end Terminal

end Sheaf

end

end ZInQ.Manuscript.T10Proetale
