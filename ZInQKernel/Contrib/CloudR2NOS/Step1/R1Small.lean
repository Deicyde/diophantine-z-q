/-
H5 lane3 Step 1: R1 small obligations PROVED. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED.
Universe u.

* `subsingleton_H_zero_biproduct`: if every summand has trivial `H⁰`, so does a finite
  biproduct. Write `x = H(𝟙) x = Σ_j H(ι_j) (H(π_j) x)` (`biproduct.total`; W07
  `H.map_id_apply`, `H.map_comp_apply`, `H.map_add_apply` packaged as an additive map); each
  `H(π_j) x = 0`.
* `biproductUnitSectionsNontrivial : BiproductUnitSectionsNontrivial` (R1Core.lean, exact Prop).
  `H⁰(O_Y) ≅ Γ(Y, O_Y)` is nontrivial for nonempty `Y` (germ into a local ring). It embeds into
  `H⁰(⨁ O_Y)` via `ι_{i₀}`, which has the left inverse `π_{i₀}`.
* `biproductUnitTensorSections_inv`: the invertible-`G` form of `BiproductUnitTensorSections`,
  which is exactly what R1a uses. Tensoring with an invertible `G` is an equivalence (W07
  `tensorRight_isEquivalence`), so it preserves biproducts (Mathlib
  `preservesBiproduct_of_preservesCoproduct`, `Functor.mapBiproduct`), and `O ⊗ G ≅ G`.
* `relativeVanishingSectionsCore_of` (hFB): R1 core from C4's obligation alone. R1Core.lean's
  general-`G` obligation is not needed.
* `relativeDetectionSections_of` (hFB): R1b from C4's obligation alone.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.R1Core
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorEquivalence

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- PROVED: trivial `H⁰` is preserved by finite biproducts. -/
theorem subsingleton_H_zero_biproduct {Y : Scheme.{u}} {J : Type} [Fintype J] [DecidableEq J]
    (f : J → Y.Modules) (h : ∀ j, Subsingleton ((f j).H 0)) :
    Subsingleton ((⨁ f).H 0) := by
  have hzero : ∀ {A B : Y.Modules} (z : A.H 0), Scheme.Modules.H.map (0 : A ⟶ B) 0 z = 0 := by
    intro A B z
    have h2 := Scheme.Modules.H.map_add_apply (0 : A ⟶ B) 0 0 z
    rw [add_zero] at h2
    exact self_eq_add_right.mp h2
  have key : ∀ z : (⨁ f).H 0, z = 0 := by
    intro z
    let Φ : ((⨁ f) ⟶ (⨁ f)) →+ (⨁ f).H 0 :=
      { toFun := fun φ => Scheme.Modules.H.map φ 0 z
        map_zero' := hzero z
        map_add' := fun φ ψ => Scheme.Modules.H.map_add_apply φ ψ 0 z }
    have hz : z = Φ (∑ j, biproduct.π f j ≫ biproduct.ι f j) := by
      rw [biproduct.total]
      exact (Scheme.Modules.H.map_id_apply _ 0 z).symm
    rw [hz, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    change Scheme.Modules.H.map (biproduct.π f j ≫ biproduct.ι f j) 0 z = 0
    rw [Scheme.Modules.H.map_comp_apply,
      @Subsingleton.elim _ (h j) (Scheme.Modules.H.map (biproduct.π f j) 0 z) 0, map_zero]
  exact ⟨fun a b => (key a).trans (key b).symm⟩

/-- `BiproductUnitSectionsNontrivial`, PROVED. -/
theorem biproductUnitSectionsNontrivial : BiproductUnitSectionsNontrivial.{u} := by
  intro Y _ h hh hsub
  let i₀ : Fin h := ⟨0, hh⟩
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  haveI : Nontrivial Γ(Y, ⊤) := (Y.presheaf.germ ⊤ y trivial).hom.domain_nontrivial
  haveI : Nontrivial Γ(𝟙_ Y.Modules, ⊤) := (inferInstance : Nontrivial Γ(Y, ⊤))
  haveI : Nontrivial ((𝟙_ Y.Modules).H 0) :=
    (Scheme.Modules.H.zeroLinearEquiv (𝟙_ Y.Modules)).toEquiv.nontrivial
  obtain ⟨x, hx⟩ := exists_ne (0 : (𝟙_ Y.Modules).H 0)
  apply hx
  have hret : Scheme.Modules.H.map (biproduct.π (fun _ : Fin h => 𝟙_ Y.Modules) i₀) 0
      (Scheme.Modules.H.map (biproduct.ι (fun _ : Fin h => 𝟙_ Y.Modules) i₀) 0 x) = x := by
    rw [← Scheme.Modules.H.map_comp_apply, biproduct.ι_π_self, Scheme.Modules.H.map_id_apply]
  rw [← hret, @Subsingleton.elim _ hsub
    (Scheme.Modules.H.map (biproduct.ι (fun _ : Fin h => 𝟙_ Y.Modules) i₀) 0 x) 0, map_zero]

/-- The invertible-`G` form of `BiproductUnitTensorSections`, which is what R1a uses. -/
def BiproductUnitTensorSectionsInv : Prop :=
  ∀ {Y : Scheme.{u}} (h : ℕ) (G : Y.Modules) [G.IsInvertible], Subsingleton (G.H 0) →
    Subsingleton (((⨁ (fun _ : Fin h => 𝟙_ Y.Modules)) ⊗ G).H 0)

/-- PROVED. -/
theorem biproductUnitTensorSections_inv : BiproductUnitTensorSectionsInv.{u} := by
  intro Y h G _ hG
  haveI : PreservesBiproduct (fun _ : Fin h => 𝟙_ Y.Modules) (tensorRight G) :=
    preservesBiproduct_of_preservesCoproduct (tensorRight G)
  let e₁ : (⨁ (fun _ : Fin h => 𝟙_ Y.Modules)) ⊗ G ≅
      ⨁ (fun _ : Fin h => 𝟙_ Y.Modules ⊗ G) :=
    (tensorRight G).mapBiproduct (fun _ : Fin h => 𝟙_ Y.Modules)
  let e₂ : (⨁ (fun _ : Fin h => 𝟙_ Y.Modules ⊗ G)) ≅ ⨁ (fun _ : Fin h => G) :=
    biproduct.mapIso (fun _ => λ_ G)
  exact Subsingleton_H_zero_of_iso (e₁ ≪≫ e₂)
    (subsingleton_H_zero_biproduct (fun _ : Fin h => G) (fun _ => hG))

/-- R1 core from C4's obligation alone. -/
theorem relativeVanishingSectionsCore_of (hFB : FieldBaseChangeFreeDirectImage.{u}) :
    RelativeVanishingSectionsCore.{u} := by
  intro K _ X Y fX fY _ _ _ _ _ _ F _ _ G _ q hG
  obtain ⟨e⟩ := hFB fX fY F q
  exact Subsingleton_H_zero_of_iso (tensorIso e (Iso.refl G))
    (biproductUnitTensorSections_inv _ G hG)

/-- R1b from C4's obligation alone. -/
theorem relativeDetectionSections_of (hFB : FieldBaseChangeFreeDirectImage.{u}) :
    RelativeDetectionSections.{u} :=
  relativeDetectionSections hFB biproductUnitSectionsNontrivial

end ZInQ.Contrib.CloudR2NOS.Step1
