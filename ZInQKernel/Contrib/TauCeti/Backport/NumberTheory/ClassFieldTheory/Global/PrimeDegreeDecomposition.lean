/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Global.PrimeDegreeDecomposition), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.PrimeDegreeDecomposition`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.PrimeDegreeDecomposition
public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.NumberField.LocalGlobal.AbsoluteGaloisGroup
public import ZInQKernel.Contrib.TauCeti.Backport.Topology.Algebra.ContinuousMonoidHom.Basic

public section
noncomputable section

namespace AlgHom

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension Pointwise
variable {K : Type} [Field K] [NumberField K]
open TauCeti TauCeti.ClassFieldTheory

/-- **A prime-degree Galois extension is realized by a local absolute Galois group.** Let `F` be a
number field over `K`, `E/F` a Galois extension of number fields of prime degree, and
`ι : E →ₐ[K] Kˢ` an embedding into the separable closure of `K`. Then for some finite place `v`
of `K` and some embedding `τ : Kˢ → K_vˢ`, every `σ ∈ Gal(E/F)` acts on `ι(E)` as the image under
`absoluteGaloisGroupMap τ` of some element of `G_{K_v}`. -/
theorem exists_absoluteGaloisGroupMap_apply_eq_of_finrank_prime {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra K F] [Algebra K E] [Algebra F E]
    [IsScalarTower K F E] [IsGalois F E] (ι : E →ₐ[K] SeparableClosure K)
    (hE : (Module.finrank F E).Prime) :
    ∃ (v : HeightOneSpectrum (𝓞 K))
      (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)),
      ∀ σ : Gal(E/F), ∃ g : AbsoluteGaloisGroup (v.adicCompletion K),
        ∀ x, absoluteGaloisGroupMap τ g (ι x) = ι (σ x) := by
  -- A place `w` of `E` above a place `u` of `F` whose decomposition group is all of `Gal(E/F)`.
  obtain ⟨u, ⟨w, _⟩, hw⟩ := exists_stabilizer_eq_top_of_finrank_prime hE
  obtain ⟨τ, hτ⟩ := ι.exists_absoluteGaloisGroupMap_apply_eq_of_mem_stabilizer
    (v := u.under (𝓞 K)) (u := u) w
  exact ⟨_, τ, fun σ ↦ hτ σ (hw ▸ Subgroup.mem_top σ)⟩

end AlgHom

namespace TauCeti.ClassFieldTheory.NormalLayer

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension Pointwise
variable {K : Type} [Field K] [NumberField K]
open TauCeti IntermediateField

/-- **A prime-degree layer has a surjective decomposition map at some finite place.** Let
`V ◁ U` be a finite normal layer of `G_K` of prime degree. There are a finite place `v` of `K` and
an embedding `τ : Kˢ → K_vˢ` for which the decomposition map `φ_τ⁻¹(U) → U ⧸ V`, induced by
`absoluteGaloisGroupMap τ : G_{K_v} → G_K`, is onto. -/
theorem exists_surjective_absoluteGaloisGroupMap_of_degree_prime
    (L : NormalLayer (AbsoluteGaloisGroup K)) (hL : L.degree.Prime) :
    ∃ (v : HeightOneSpectrum (𝓞 K))
      (τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K)),
      Function.Surjective fun g : L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
          AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K) ↦
        ((absoluteGaloisGroupMap τ).subgroupComap L.ground.toSubgroup g : L.Gal) := by
  -- The fixed fields `F` of `U` and `E` of `V`: `E/F` is Galois, of prime degree.
  obtain ⟨F, hF⟩ : ∃ F, fixedField L.ground.toSubgroup = F := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, fixedField L.top.toSubgroup = E := ⟨_, rfl⟩
  have hle : F ≤ E := hF ▸ hE ▸ fixedField_le (OpenSubgroup.toSubgroup_le.2 L.top_le_ground)
  have : FiniteDimensional K F := hF ▸ finiteDimensional_fixedField_toSubgroup L.ground
  have : FiniteDimensional K E := hE ▸ finiteDimensional_fixedField_toSubgroup L.top
  have : NumberField F := .of_module_finite K F
  have : NumberField E := .of_module_finite K E
  let := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower F E (SeparableClosure K) := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower K F E := .of_algebraMap_eq fun _ ↦ rfl
  have := L.isGalois_of_fixedField hF hE
  let e := L.galEquivOfFixedField hF hE
  have hfin : (Module.finrank F E).Prime := by
    rwa [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr e.toEquiv,
      ← NormalLayer.degree_eq_natCard_gal]
  obtain ⟨v, τ, hτ⟩ := E.val.exists_absoluteGaloisGroupMap_apply_eq_of_finrank_prime hfin
  refine ⟨v, τ, fun γ ↦ ?_⟩
  obtain ⟨g, hg⟩ := hτ (e γ)
  -- The image of `g` acts on `F` as `e γ` does, trivially, so it lies in `U`.
  have hgU : g ∈ L.ground.toSubgroup.comap (absoluteGaloisGroupMap τ :
      AbsoluteGaloisGroup (v.adicCompletion K) →* AbsoluteGaloisGroup K) := by
    rw [Subgroup.mem_comap, toSubgroup_eq_fixingSubgroup_of_fixedField_eq hF]
    rintro ⟨x, hx⟩
    exact (hg ⟨x, hle hx⟩).trans (congrArg E.val ((e γ).commutes ⟨x, hx⟩))
  refine ⟨⟨g, hgU⟩, e.injective (AlgEquiv.ext fun x ↦ Subtype.ext ?_)⟩
  rw [coe_galEquivOfFixedField_mk_apply, ContinuousMonoidHom.subgroupComap_apply_coe]
  exact hg x

end TauCeti.ClassFieldTheory.NormalLayer

end
end
