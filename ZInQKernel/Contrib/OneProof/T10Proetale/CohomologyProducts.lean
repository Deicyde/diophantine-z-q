import ZInQKernel.Contrib.OneProof.T10Proetale.CoefficientSequence
import ZInQKernel.Contrib.OneProof.T10Proetale.ExtProducts

/-!
# Products and degree one on the pro-étale site
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

universe u

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

section AbstractFan

variable {D : Type*} [Category* D] [Abelian D] [EnoughInjectives D] [HasExt.{u+1} D]
  {I : Type*} [HasProductsOfShape I D] (A : I → D) (R : D) (c : Fan A)

private def extFanMap : Ext R c.pt 1 →+ ∀ i, Ext R (A i) 1 :=
  AddMonoidHom.pi fun i => (Ext.mk₀ (c.proj i)).postcomp R (add_zero 1)

omit [EnoughInjectives D] in
private theorem extFanMap_comp (hc : IsLimit c) (x : Ext R (∏ᶜ A) 1) :
    extFanMap A R c (x.comp (Ext.mk₀
      ((productIsProduct A).conePointUniqueUpToIso hc).hom) (add_zero 1)) =
      extProductMap A R x := by
  let e := (productIsProduct A).conePointUniqueUpToIso hc
  funext i
  change (x.comp (Ext.mk₀ e.hom) (add_zero 1)).comp (Ext.mk₀ (c.proj i)) (add_zero 1) =
    x.comp (Ext.mk₀ (Pi.π A i)) (add_zero 1)
  have h : e.hom ≫ c.proj i = Pi.π A i :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i)
  rw [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, h]

private theorem extFanMap_injective (hc : IsLimit c) :
    Function.Injective (extFanMap A R c) := by
  let e := (productIsProduct A).conePointUniqueUpToIso hc
  let f : Ext R (∏ᶜ A) 1 →+ Ext R c.pt 1 := (Ext.mk₀ e.hom).postcomp R (add_zero 1)
  have hs : Function.Surjective f := (T10Etale.ext_postcomp_iso_bijective (Z := R) e 1).surjective
  intro a b hab
  obtain ⟨x, rfl⟩ := hs a
  obtain ⟨y, rfl⟩ := hs b
  have heq := (extFanMap_comp A R c hc x).symm.trans (hab.trans (extFanMap_comp A R c hc y))
  exact congrArg f (extProductMap_injective A R heq)

private theorem extFanMap_bijective (hc : IsLimit c)
    (h : Epi (Limits.Pi.map fun i => (injectivePresentation (A i)).g)) :
    Function.Bijective (extFanMap A R c) := by
  refine ⟨extFanMap_injective A R c hc, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := (extProductMap_bijective A R h).surjective y
  exact ⟨_, (extFanMap_comp A R c hc x).trans hx⟩

end AbstractFan

section Cohomology

/-- The source object used to compute cohomology on this small site. -/
abbrev cohomologySource (X : Scheme.{u}) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u+1} :=
  (constantSheaf (Scheme.ProEt.topology X) Ab.{u+1}).obj (AddCommGrpCat.of (ULift ℤ))

/-- The canonical map from degree-one cohomology of the product to its coordinates. -/
def productH1Coordinates : Sheaf.H.{u+1} (productSheaf X ℓ) 1 →+ ∀ n, ProFiniteH X ℓ n 1 :=
  extFanMap (residueSheaf X ℓ) (cohomologySource X) (Fan.mk _ (productProjection X ℓ))

omit [Fact ℓ.Prime] in
/-- The actual cohomology of the product injects into the product of the H¹ groups. -/
theorem productH1Coordinates_injective :
    Function.Injective (productH1Coordinates X ℓ) :=
  extFanMap_injective (residueSheaf X ℓ) (cohomologySource X)
    (Fan.mk (productSheaf X ℓ) (productProjection X ℓ)) (productFanIsLimit X ℓ)

omit [Fact ℓ.Prime] in
/-- It suffices for the one product of injective-presentation quotient maps to
be epi. No all-degree comparison or derived limit theorem is needed. -/
theorem productH1Coordinates_bijective
    (h : Epi (Limits.Pi.map fun n => (injectivePresentation (residueSheaf X ℓ n)).g)) :
    Function.Bijective (productH1Coordinates X ℓ) :=
  extFanMap_bijective (residueSheaf X ℓ) (cohomologySource X)
    (Fan.mk (productSheaf X ℓ) (productProjection X ℓ)) (productFanIsLimit X ℓ) h

end Cohomology

end
end ZInQ.Manuscript.T10Proetale
