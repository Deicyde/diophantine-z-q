/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Restrict the ACTUAL cartesian model comparison to the SAME original
base open, retaining its ambient affine base map. This lets the source
fpqc morphism-descent theorem compare the effective generic output with
the original A, rather than assuming a scheme/group generic output iso.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.ComparisonIso
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.GroupInput

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- The native isomorphism induced by equality of opens, with its actual inclusion equation. -/
def opensEqIso {X : Scheme.{u}} {V W : X.Opens} (h : V = W) : V.toScheme ≅ W.toScheme :=
  eqToIso (congrArg Scheme.Opens.toScheme h)

@[reassoc (attr := simp)]
theorem opensEqIso_hom_ι {X : Scheme.{u}} {V W : X.Opens} (h : V = W) :
    (opensEqIso h).hom ≫ W.ι = V.ι := by
  cases h
  simp [opensEqIso]

section Generic
variable {X X' U S : Scheme.{u}} {q : X' ⟶ X} {f' : X' ⟶ U} {f : X ⟶ S} {p : U ⟶ S}
  (hc : IsPullback q f' f p) (V : S.Opens)

include hc

private theorem preimage_eq : q ⁻¹ᵁ (f ⁻¹ᵁ V) = f' ⁻¹ᵁ (p ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, hc.w, Scheme.Hom.comp_preimage]

/-- Actual restricted comparison from the original generic open of X'. -/
def genericCartMap : (f' ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
  (opensEqIso (preimage_eq hc V).symm).hom ≫ (q ∣_ (f ⁻¹ᵁ V))

@[reassoc (attr := simp)]
theorem genericCartMap_ι : genericCartMap hc V ≫ (f ⁻¹ᵁ V).ι =
    (f' ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ q := by
  rw [genericCartMap, Category.assoc, morphismRestrict_ι, ← Category.assoc, opensEqIso_hom_ι]

/-- The restricted comparison is cartesian over the SAME original
    ambient base map p (not a substituted fraction field). -/
theorem genericCart_isPullback :
    IsPullback (genericCartMap hc V) ((f' ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ f')
      ((f ⁻¹ᵁ V).ι ≫ f) p := by
  let H := isPullback_morphismRestrict q (f ⁻¹ᵁ V)
  let E := opensEqIso (preimage_eq hc V).symm ≪≫ H.isoPullback
  have hp : IsPullback (genericCartMap hc V) (f' ⁻¹ᵁ (p ⁻¹ᵁ V)).ι (f ⁻¹ᵁ V).ι q := by
    refine IsPullback.of_iso_pullback ⟨genericCartMap_ι hc V⟩ E ?_ ?_
    · simp only [E, Iso.trans_hom, Category.assoc, H.isoPullback_hom_fst]
      rfl
    · simp only [E, Iso.trans_hom, Category.assoc, H.isoPullback_hom_snd, opensEqIso_hom_ι]
  exact hp.paste_vert hc

end Generic

/-- The ORIGINAL-A generic cartesian comparison is also cartesian over
    the ambient base map p, by the genuine open square and its actual
    generic GROUP iso. -/
theorem originalGenericModel_isPullback_ambient
    {U S : Scheme.{u}} (p : U ⟶ S) (V : S.Opens) (G : Grp (Over U)) (A : Grp (Over V.toScheme))
    (e : (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅ (Over.pullback (p ∣_ V)).mapGrp.obj A) :
    IsPullback (genericModelOfGroupIso p V G A e).q
      ((G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).ι ≫ G.X.hom) (A.X.hom ≫ V.ι) p := by
  have H := (genericModelOfGroupIso p V G A e).cartesian.paste_vert (isPullback_morphismRestrict p V)
  rwa [morphismRestrict_ι] at H

#print axioms genericCart_isPullback
#print axioms originalGenericModel_isPullback_ambient

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
