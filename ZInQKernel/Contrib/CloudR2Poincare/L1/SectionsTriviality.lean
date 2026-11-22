import ZInQKernel.Contrib.CloudR2Poincare.L1.PicardKernel
import ZInQKernel.Contrib.CloudR2Poincare.L2.LineBundleNonzero
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.GlobalSection

/-!
# Native seesaw pointwise criterion in every dimension

H-72 L1 continuation (A). Triviality iff a bundle and its inverse both have
nonzero global sections is proved with the NATIVE W07 Scheme.Modules/Pic types.
No curve-degree argument or representability hypothesis is used.

The narrower geometric nonzero-map criterion is reused from L2.LineBundleNonzero,
whose step-(3) ownership was clarified after the two lanes initially developed
it in parallel. L1 owns only the native dual/global-section comparison and the
seesaw iff. The original parallel source/proof attempt is banked in L1 reports.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L1

open Scheme

/-- Global sections of the native inverse bundle are morphisms L→O_X. -/
def dualGlobalSectionsEquiv {X : Scheme.{u}} (M : X.Modules) :
    Γ(Mᵛ, ⊤) ≃ (M ⟶ Modules.unit X) :=
  (Modules.unitHomAddEquiv Mᵛ).toEquiv.symm.trans
    ((SheafOfModules.unitHomEquiv Mᵛ).trans
      (SheafOfModules.homObjSectionsEquiv M (Modules.unit X)))

/-- The all-dimensional pointwise seesaw criterion, with the actual native inverse. -/
theorem nonempty_iso_unit_iff_nontrivial_globalSections
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsProper f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible] :
    Nonempty (M ≅ Modules.unit X) ↔ Nontrivial Γ(M, ⊤) ∧ Nontrivial Γ(Mᵛ, ⊤) := by
  haveI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  haveI : Nontrivial Γ(Modules.unit X, ⊤) := inferInstanceAs (Nontrivial Γ(X, ⊤))
  constructor
  · rintro ⟨e⟩
    haveI : Nontrivial Γ(M, ⊤) := (Modules.appLinearEquivOfIso e ⊤).toEquiv.nontrivial
    have hM : Pic.mk M = 1 := by
      rw [Pic.one_eq_mk_unit]
      exact (Pic.mk_eq_mk_iff M (Modules.unit X)).mpr ⟨e⟩
    have hdual : Pic.mk Mᵛ = 1 := by rw [Pic.mk_dual, hM, inv_one]
    obtain ⟨edual⟩ := (Pic.mk_eq_mk_iff Mᵛ (Modules.unit X)).mp
      (hdual.trans (Pic.one_eq_mk_unit))
    exact ⟨inferInstance, (Modules.appLinearEquivOfIso edual ⊤).toEquiv.nontrivial⟩
  · rintro ⟨hs, ht⟩
    haveI := hs
    haveI := ht
    haveI : Nontrivial (Modules.unit X ⟶ M) := (Modules.unitHomAddEquiv M).toEquiv.nontrivial
    haveI : Nontrivial (M ⟶ Modules.unit X) := (dualGlobalSectionsEquiv M).symm.nontrivial
    obtain ⟨s, hs⟩ := exists_ne (0 : Modules.unit X ⟶ M)
    obtain ⟨t, ht⟩ := exists_ne (0 : M ⟶ Modules.unit X)
    exact ZInQ.Contrib.CloudR2Poincare.L2.nonempty_iso_unit_of_nonzero_maps f M s t hs ht

end ZInQ.Contrib.CloudR2Poincare.L1
