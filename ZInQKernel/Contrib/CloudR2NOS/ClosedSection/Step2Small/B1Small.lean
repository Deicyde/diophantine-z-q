/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 Step-2 small obligations for C3's B1 (`Step2B1/Assembly.lean` 4b764b14, `Step2B1/KeyPlan.lean`
0b7d2191; statements used verbatim through the imports), PROVED natively.
SOURCE ONLY, UNCOMPILED. Native HELD. Universe u, default options.

* `supportComponentsFinite` (`SupportComponentsFinite`): `A` is a Noetherian space (proper, hence
  finite type, over a field), and the closed `supp D` has finitely many maximal irreducible
  subsets (`Step2Small.finite_maximal_irreducible`).
* `translationPermutesComponents` (`TranslationPermutesComponents`): `t_x` and `t_{x⁻¹}` are
  mutually inverse on points (C3's `tr_mul`, `tr_one`), so `t_x⁻¹(C) = t_{x⁻¹}(C)` is irreducible,
  lies in `supp D`, and is maximal (any larger irreducible `Z` gives the irreducible `t_x(Z) ⊇ C`).
* `comapInvertible` (`ComapInvertible`): `t_x` is an isomorphism, hence flat; W07
  `IdealSheafData.IsInvertible.comap_of_flat`.
Truth: all TRUE (these are the proofs).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.Assembly
import ZInQKernel.Contrib.CloudR2NOS.Step2B1.KeyPlan
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import ZInQKernel.Contrib.CloudR2NOS.ClosedSection.Step2Small.NoetherianComponents

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small

local notation "tr" => H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation

section Translation

variable {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K))))

/-- `t_{x⁻¹} ∘ t_x = id` on points. -/
theorem tr_inv_tr_apply (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) (a : A.X.left) :
    (tr A x⁻¹).base ((tr A x).base a) = a := by
  have h := ZInQ.Contrib.CloudR2NOS.Step2B1.tr_mul A x x⁻¹
  rw [mul_inv_cancel, ZInQ.Contrib.CloudR2NOS.Step2B1.tr_one] at h
  have h1 := congrArg (fun φ : A.X.left ⟶ A.X.left => φ.base a) h
  simp only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.Hom.id_base, TopCat.id_app] at h1
  exact h1.symm

/-- `t_x ∘ t_{x⁻¹} = id` on points. -/
theorem tr_tr_inv_apply (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) (a : A.X.left) :
    (tr A x).base ((tr A x⁻¹).base a) = a := by
  have h := ZInQ.Contrib.CloudR2NOS.Step2B1.tr_mul A x⁻¹ x
  rw [inv_mul_cancel, ZInQ.Contrib.CloudR2NOS.Step2B1.tr_one] at h
  have h1 := congrArg (fun φ : A.X.left ⟶ A.X.left => φ.base a) h
  simp only [Scheme.Hom.comp_base, TopCat.comp_app, Scheme.Hom.id_base, TopCat.id_app] at h1
  exact h1.symm

/-- Right translations are isomorphisms of schemes. -/
theorem isIso_tr (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) : IsIso (tr A x) := by
  refine ⟨⟨tr A x⁻¹, ?_, ?_⟩⟩
  · rw [← ZInQ.Contrib.CloudR2NOS.Step2B1.tr_mul, mul_inv_cancel,
      ZInQ.Contrib.CloudR2NOS.Step2B1.tr_one]
  · rw [← ZInQ.Contrib.CloudR2NOS.Step2B1.tr_mul, inv_mul_cancel,
      ZInQ.Contrib.CloudR2NOS.Step2B1.tr_one]

end Translation

/-- An abelian variety over a field is a Noetherian space (proper, hence finite type, over a
Noetherian base, and quasi-compact). -/
theorem noetherianSpace_abelianVariety {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A] :
    NoetherianSpace A.X.left := by
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : IsLocallyNoetherian A.X.left := LocallyOfFiniteType.isLocallyNoetherian A.X.hom
  haveI : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  haveI : IsNoetherian A.X.left :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  infer_instance

/-- **`SupportComponentsFinite` proved.** -/
theorem supportComponentsFinite : ZInQ.Contrib.CloudR2NOS.Step2B1.SupportComponentsFinite.{u} := by
  intro K _ _ A _ D
  haveI := noetherianSpace_abelianVariety A
  exact finite_maximal_irreducible D.support.isClosed

/-- **`TranslationPermutesComponents` proved.** -/
theorem translationPermutesComponents :
    ZInQ.Contrib.CloudR2NOS.Step2B1.TranslationPermutesComponents.{u} := by
  intro K _ _ A _ D x hx C hC
  obtain ⟨⟨hCS, hCirr⟩, hCmax⟩ := hC
  have hSf : ∀ a, a ∈ (D.support : Set A.X.left) ↔ (tr A x).base a ∈ (D.support : Set A.X.left) :=
    fun a => by
      constructor
      · intro ha
        have h' : a ∈ (tr A x) ⁻¹' (D.support : Set A.X.left) := by rw [hx]; exact ha
        exact h'
      · intro ha
        have h' : a ∈ (tr A x) ⁻¹' (D.support : Set A.X.left) := ha
        rwa [hx] at h'
  have hpre : (tr A x) ⁻¹' C = (tr A x⁻¹).base '' C := by
    ext a
    constructor
    · intro ha
      exact ⟨(tr A x).base a, ha, tr_inv_tr_apply A x a⟩
    · rintro ⟨c, hc, rfl⟩
      show (tr A x).base ((tr A x⁻¹).base c) ∈ C
      rw [tr_tr_inv_apply]
      exact hc
  refine ⟨⟨fun a ha => (hSf a).2 (hCS ha), ?_⟩, fun Z hZ hCZ => ?_⟩
  · rw [hpre]
    exact hCirr.image _ (tr A x⁻¹).continuous.continuousOn
  · obtain ⟨hZS, hZirr⟩ := hZ
    have h1 : C ⊆ (tr A x).base '' Z := fun c hc =>
      ⟨(tr A x⁻¹).base c, hCZ (show (tr A x).base ((tr A x⁻¹).base c) ∈ C by
        rw [tr_tr_inv_apply]; exact hc), tr_tr_inv_apply A x c⟩
    have h2 : (tr A x).base '' Z ⊆ (D.support : Set A.X.left) := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hSf z).1 (hZS hz)
    have h3 : IsIrreducible ((tr A x).base '' Z) :=
      hZirr.image _ (tr A x).continuous.continuousOn
    have h4 : (tr A x).base '' Z ⊆ C := hCmax ⟨h2, h3⟩ h1
    intro z hz
    exact h4 ⟨z, hz, rfl⟩

/-- **`ComapInvertible` proved.** -/
theorem comapInvertible : ZInQ.Contrib.CloudR2NOS.Step2B1.ComapInvertible.{u} := by
  intro K _ A D hD x
  haveI : IsIso (tr A x) := isIso_tr A x
  exact hD.comap_of_flat (tr A x)

end ZInQ.Contrib.CloudR2NOS.ClosedSection.Step2Small
