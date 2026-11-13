/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.LocalGlobal.AbsoluteGaloisGroup), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.AbsoluteGaloisGroup`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.AbsoluteGaloisGroup
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Separable
public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.Restriction
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension Pointwise
open TauCeti
namespace AlgHom

variable {K F E : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field E]
  [NumberField E] [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]

/-- **The decomposition group acts through the local absolute Galois group.** Let `K ⊆ F ⊆ E` be
number fields with `E/F` Galois, `ι : E →ₐ[K] Kˢ` an embedding into the separable closure of `K`,
and `w` a finite place of `E` above a finite place `u` of `F` above the finite place `v` of `K`. For
some embedding of separable closures `τ : Kˢ →ₐ[K] K_vˢ`, every element `σ` of the decomposition
group of `w` in `Gal(E/F)` satisfies `absoluteGaloisGroupMap τ g (ι x) = ι (σ x)` for some
`g ∈ G_{K_v}` and every `x ∈ E`. -/
theorem exists_absoluteGaloisGroupMap_apply_eq_of_mem_stabilizer [IsGalois F E]
    (ι : E →ₐ[K] SeparableClosure K) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 F)} [hu : u.asIdeal.LiesOver v.asIdeal]
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver u.asIdeal] :
    ∃ τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K),
      ∀ σ ∈ MulAction.stabilizer Gal(E/F) w.asIdeal,
        ∃ g : AbsoluteGaloisGroup (v.adicCompletion K),
          ∀ x, absoluteGaloisGroupMap τ g (ι x) = ι (σ x) := by
  have := HeightOneSpectrum.adicCompletion_isSeparable v u
  have := HeightOneSpectrum.adicCompletion_isSeparable u w
  -- Embed `F_u` in `K_vˢ` over `K_v`, making `K_vˢ` a separable closure of `F_u`, and then embed
  -- `E_w` in it over `F_u`.
  let κ : u.adicCompletion F →ₐ[v.adicCompletion K] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  let _ : Algebra (u.adicCompletion F) (SeparableClosure (v.adicCompletion K)) :=
    κ.toRingHom.toAlgebra
  have : IsScalarTower (v.adicCompletion K) (u.adicCompletion F)
      (SeparableClosure (v.adicCompletion K)) := .of_algebraMap_eq fun x ↦ (κ.commutes x).symm
  have : Algebra.IsSeparable (u.adicCompletion F) (SeparableClosure (v.adicCompletion K)) :=
    Algebra.isSeparable_tower_top_of_isSeparable (v.adicCompletion K) _ _
  have : IsSepClosure (u.adicCompletion F) (SeparableClosure (v.adicCompletion K)) :=
    ⟨inferInstance, inferInstance⟩
  let τ' : w.adicCompletion E →ₐ[u.adicCompletion F] SeparableClosure (v.adicCompletion K) :=
    IsSepClosed.lift
  -- The embedding `j : E → E_w → K_vˢ` is `K`-linear, because both squares of completions commute.
  have hFE (x : F) : algebraMap E (w.adicCompletion E) (algebraMap F E x) =
      algebraMap (u.adicCompletion F) (w.adicCompletion E)
        (algebraMap F (u.adicCompletion F) x) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra]
    exact (HeightOneSpectrum.adicCompletionExtension_coe F E u w x).symm
  have hKF (x : K) : algebraMap F (u.adicCompletion F) (algebraMap K F x) =
      algebraMap (v.adicCompletion K) (u.adicCompletion F)
        (algebraMap K (v.adicCompletion K) x) := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra]
    exact (HeightOneSpectrum.adicCompletionExtension_coe K F v u x).symm
  have hcomm (x : K) : τ' (algebraMap E (w.adicCompletion E) (algebraMap K E x)) =
      algebraMap K (SeparableClosure (v.adicCompletion K)) x := by
    rw [IsScalarTower.algebraMap_apply K F E, hFE, hKF, τ'.commutes,
      IsScalarTower.algebraMap_apply K (v.adicCompletion K) (SeparableClosure _)]
    exact κ.commutes _
  let j : E →ₐ[K] SeparableClosure (v.adicCompletion K) :=
    { τ'.toRingHom.comp (algebraMap E (w.adicCompletion E)) with commutes' := hcomm }
  -- Extend `j`, read on the image of `ι`, to `τ : Kˢ →ₐ[K] K_vˢ`.
  obtain ⟨τ, hτ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K) ι.fieldRange
    (E := SeparableClosure K) (M := SeparableClosure (v.adicCompletion K))
    (j.comp (ι.equivFieldRange.symm : ι.fieldRange →ₐ[K] E))
  -- `τ.domRestrict` evaluates on `ι.equivFieldRange x` as `τ` on `ι x`, by definition.
  have hτι (x : E) : τ (ι x) = τ' (algebraMap E (w.adicCompletion E) x) :=
    (congrArg (fun φ : ι.fieldRange →ₐ[K] _ ↦ φ (ι.equivFieldRange x)) hτ).trans
      (congrArg j (ι.equivFieldRange.symm_apply_apply x))
  refine ⟨τ, fun σ hσ ↦ ?_⟩
  -- The automorphism of `E_w` induced by `σ` is the restriction along `τ'` of an automorphism `g₀`
  -- of `K_vˢ` over `F_u`, in particular over `K_v`.
  obtain ⟨g₀, hg₀⟩ :=
    τ'.restrictNormalHom_surjective (HeightOneSpectrum.decompositionHom u w ⟨σ, hσ⟩)
  refine ⟨g₀.restrictScalars (v.adicCompletion K), fun x ↦ ?_⟩
  have h : τ (absoluteGaloisGroupMap τ (g₀.restrictScalars (v.adicCompletion K)) (ι x)) =
      τ (ι (σ x)) := by
    rw [absoluteGaloisGroupMap_commutes, hτι, hτι, AlgEquiv.restrictScalars_apply,
      ← τ'.restrictNormalHom_commutes, hg₀, HeightOneSpectrum.decompositionHom_algebraMap]
  exact τ.injective h

end AlgHom

end
end
