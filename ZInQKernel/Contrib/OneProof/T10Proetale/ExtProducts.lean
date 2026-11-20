import ZInQKernel.Contrib.OneProof.T10Proetale.ExtensionFibres

/-!
# The degree-one product calculation

For the given product of coefficient objects, the only epimorphism needed is
the product of the cokernel maps from their injective presentations.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

universe w

variable {D : Type*} [Category* D] [Abelian D] [EnoughInjectives D] [HasExt.{w} D]
  {I : Type*} [HasProductsOfShape I D] (A : I → D) (R : D)

/-- The coordinate map on degree-one Ext of a product. -/
def extProductMap : Ext R (∏ᶜ A) 1 →+ ∀ i, Ext R (A i) 1 :=
  AddMonoidHom.pi fun i => (Ext.mk₀ (Pi.π A i)).postcomp R (add_zero 1)

private abbrev injectives (i : I) : D := (injectivePresentation (A i)).X₂

private abbrev quotients (i : I) : D := (injectivePresentation (A i)).X₃

private abbrev productPresentation : ShortComplex D :=
  ShortComplex.mk (Limits.Pi.map fun i => (injectivePresentation (A i)).f)
    (Limits.Pi.map fun i => (injectivePresentation (A i)).g) (by
      rw [Limits.Pi.map_comp_map]
      apply Pi.hom_ext
      intro i
      rw [Limits.Pi.map_π, (injectivePresentation (A i)).zero, comp_zero, zero_comp])

omit [HasExt.{w} D] in
private theorem productPresentation_exact_mono :
    (productPresentation A).Exact ∧ Mono (productPresentation A).f := by
  let P := productPresentation A
  have hm : Mono P.f := by
    change Mono (Limits.Pi.map fun i => (injectivePresentation (A i)).f)
    infer_instance
  have hk : IsLimit (KernelFork.ofι P.f P.zero) := by
    refine KernelFork.IsLimit.ofι' P.f P.zero fun {B} g hg => ?_
    have h (i : I) :
        (g ≫ Pi.π (injectives A) i) ≫ (injectivePresentation (A i)).g = 0 := by
      have H := congrArg (fun f : B ⟶ ∏ᶜ quotients A => f ≫ Pi.π (quotients A) i) hg
      change (g ≫ Limits.Pi.map (fun j => (injectivePresentation (A j)).g)) ≫
        Pi.π (quotients A) i = (0 : B ⟶ ∏ᶜ quotients A) ≫ Pi.π (quotients A) i at H
      simpa only [Category.assoc, Limits.Pi.map_π, zero_comp] using H
    refine ⟨Pi.lift (fun i => (injectivePresentation_shortExact (A i)).fIsKernel.lift
      (KernelFork.ofι (g ≫ Pi.π (injectives A) i) (h i))), ?_⟩
    apply Pi.hom_ext
    intro i
    change (Pi.lift _ ≫ Limits.Pi.map (fun i => (injectivePresentation (A i)).f)) ≫
      Pi.π (injectives A) i = g ≫ Pi.π (injectives A) i
    rw [Category.assoc, Limits.Pi.map_π, Pi.lift_comp_π_assoc]
    exact (injectivePresentation_shortExact (A i)).fIsKernel.fac
      (KernelFork.ofι (g ≫ Pi.π (injectives A) i) (h i)) WalkingParallelPair.zero
  exact P.exact_and_mono_f_iff_f_is_kernel.mpr ⟨hk⟩

omit [HasExt.{w} D] in
private theorem productPresentation_shortExact [Epi (productPresentation A).g] :
    (productPresentation A).ShortExact where
  exact := (productPresentation_exact_mono A).1
  mono_f := (productPresentation_exact_mono A).2
  epi_g := inferInstance

private def productPresentationProjection (i : I) :
    productPresentation A ⟶ injectivePresentation (A i) :=
  ShortComplex.homMk (S₁ := productPresentation A) (S₂ := injectivePresentation (A i))
    (Pi.π A i) (Pi.π (injectives A) i) (Pi.π (quotients A) i)
    (Limits.Pi.map_π (fun j => (injectivePresentation (A j)).f) i).symm
    (Limits.Pi.map_π (fun j => (injectivePresentation (A j)).g) i).symm

set_option maxHeartbeats 400000 in
private lemma boundary_projection [Epi (productPresentation A).g]
    (s : R ⟶ (productPresentation A).X₃) (i : I) :
    extProductMap A R ((Ext.mk₀ s).comp (productPresentation_shortExact A).extClass
      (zero_add 1)) i = extensionClass (s ≫ Pi.π _ i) := by
  change ((Ext.mk₀ s).comp _ (zero_add 1)).comp
    (Ext.mk₀ (productPresentationProjection A i).τ₁) (add_zero 1) = _
  rw [Ext.comp_assoc_of_third_deg_zero, (productPresentation_shortExact A).extClass_naturality
    (injectivePresentation_shortExact (A i)) (productPresentationProjection A i)]
  rw [Ext.mk₀_comp_mk₀_assoc]
  rfl

private abbrev quotientPresentation : ShortComplex D :=
  ShortComplex.mk (productPresentation A).f (cokernel.π (productPresentation A).f)
    (cokernel.condition (productPresentation A).f)

omit [HasExt.{w} D] in
private theorem quotientPresentation_shortExact : (quotientPresentation A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := (productPresentation_exact_mono A).2

private abbrev quotientMap : (quotientPresentation A).X₃ ⟶ (productPresentation A).X₃ :=
  cokernel.desc _ (productPresentation A).g (productPresentation A).zero

private def quotientPresentationToProduct : quotientPresentation A ⟶ productPresentation A :=
  ShortComplex.homMk (𝟙 _) (𝟙 _) (quotientMap A)
    (by simp) (by simp)

set_option maxHeartbeats 400000 in
private lemma quotient_boundary_projection (s : R ⟶ (quotientPresentation A).X₃) (i : I) :
    extProductMap A R ((Ext.mk₀ s).comp (quotientPresentation_shortExact A).extClass
      (zero_add 1)) i = extensionClass (s ≫ quotientMap A ≫ Pi.π (quotients A) i) := by
  let f := quotientPresentationToProduct A ≫ productPresentationProjection A i
  have hf : f.τ₁ = Pi.π A i := by
    change (𝟙 _) ≫ Pi.π A i = _
    exact Category.id_comp _
  change ((Ext.mk₀ s).comp _ (zero_add 1)).comp (Ext.mk₀ (Pi.π A i)) (add_zero 1) = _
  rw [← hf, Ext.comp_assoc_of_third_deg_zero, (quotientPresentation_shortExact A).extClass_naturality
    (injectivePresentation_shortExact (A i)) f, Ext.mk₀_comp_mk₀_assoc]
  rfl

/-- In degree one the canonical map from a product is always injective.
A section of the actual cokernel that lifts in every coordinate lifts to the
product of the injectives. The actual cokernel embeds in the product of the
cokernels, whether or not those two objects agree. -/
theorem extProductMap_injective : Function.Injective (extProductMap A R) := by
  let P := productPresentation A
  let Q := quotientPresentation A
  let hQ := quotientPresentation_shortExact A
  have hmono : Mono (quotientMap A) :=
    P.exact_iff_mono_cokernel_desc.mp (productPresentation_exact_mono A).1
  apply (injective_iff_map_eq_zero (extProductMap A R)).mpr
  intro e he
  have : Injective Q.X₂ := by
    change Injective (∏ᶜ fun i => Injective.under (A i))
    infer_instance
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ R hQ e (Ext.eq_zero_of_injective _) (zero_add 1)
  obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective R Q.X₃).surjective z
  have hh (i : I) : extensionClass (s ≫ quotientMap A ≫ Pi.π (quotients A) i) = 0 := by
    rw [← quotient_boundary_projection A R s i, hz, he]
    rfl
  choose t ht using fun i => (extensionClass_eq_zero_iff _).mp (hh i)
  have hst : Pi.lift t ≫ Q.g = s := by
    rw [← cancel_mono (quotientMap A), Category.assoc, cokernel.π_desc]
    apply Pi.hom_ext
    intro i
    change (Pi.lift t ≫ Limits.Pi.map (fun j => (injectivePresentation (A j)).g)) ≫
      Pi.π (quotients A) i = (s ≫ quotientMap A) ≫ Pi.π (quotients A) i
    simpa only [Category.assoc, Limits.Pi.map_π, Pi.lift_comp_π_assoc] using ht i
  rw [← hz, ← hst, ← Ext.mk₀_comp_mk₀_assoc, hQ.comp_extClass, Ext.comp_zero]

/-- If the product of the specified quotient maps is epi, `Ext¹(R, -)` commutes
with this product. This hypothesis only concerns the quotient maps in the
category of coefficients. -/
theorem extProductMap_bijective
    (h : Epi (Limits.Pi.map fun i => (injectivePresentation (A i)).g)) :
    Function.Bijective (extProductMap A R) := by
  let P := productPresentation A
  let : Epi P.g := h
  let hP := productPresentation_shortExact A
  refine ⟨extProductMap_injective A R, ?_⟩
  intro e
  choose s hs using fun i => extensionClass_surjective (R := R) (F := A i) (e i)
  refine ⟨(Ext.mk₀ (Pi.lift s)).comp hP.extClass (zero_add 1), funext fun i => ?_⟩
  rw [boundary_projection]
  have hsi : Pi.lift s ≫ Pi.π (quotients A) i = s i := Limits.Pi.lift_comp_π _ _
  rw [hsi]
  exact hs i

end
end ZInQ.Manuscript.T10Proetale
