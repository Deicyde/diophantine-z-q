/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleLocalization), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleLocalization`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleLocalization

public section
noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField ContCohomology
open scoped TensorProduct
variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)
variable {w : InfinitePlace K}
variable (τ : SeparableClosure K →ₐ[K] SeparableClosure w.Completion)

open scoped NumberField.LiesOver in
/-- Every infinite completion coordinate of an idele of a finite subextension is a coordinate
of the corresponding idele of `Kˢ`, along suitable embeddings of separable closures: the
archimedean analogue of `exists_ideleCoeffComponent_ideleCoeffOfIntermediateField_eq`. The
subextension need not be normal over `K`, and the embeddings work simultaneously for all its
ideles. -/
theorem exists_ideleCoeffInfiniteComponent_ideleCoeffOfIntermediateField_eq
    {E : IntermediateField K (SeparableClosure K)} [NumberField E] {w : InfinitePlace K}
    (u : InfinitePlace E) [u.LiesOver w] :
    ∃ (τ' : u.Completion →ₐ[w.Completion] SeparableClosure w.Completion)
      (τ : SeparableClosure K →ₐ[K] SeparableClosure w.Completion),
      ∀ a : IdeleGroup (𝓞 E) E,
      (ideleCoeffInfiniteComponent τ (ideleCoeffOfIntermediateField K E (.ofMul a))).toMul =
        Units.map (τ' : u.Completion →* SeparableClosure w.Completion)
          (u.ideleInfiniteCoord a) := by
  have : CharZero w.Completion :=
    charZero_of_injective_algebraMap (algebraMap K w.Completion).injective
  let τ' : u.Completion →ₐ[w.Completion] SeparableClosure w.Completion := IsSepClosed.lift
  let φ : E →ₐ[K] SeparableClosure w.Completion :=
    (τ'.restrictScalars K).comp (IsScalarTower.toAlgHom K E u.Completion)
  obtain ⟨τ, hτ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K)
    E (E := SeparableClosure K) (M := SeparableClosure w.Completion) φ
  refine ⟨τ', τ, fun a ↦
    toMul_ideleCoeffInfiniteComponent_ideleCoeffOfIntermediateField_eq_map_ideleInfiniteCoord u τ'
      τ (fun x ↦ ?_) a⟩
  exact congrArg (fun ψ : E →ₐ[K] _ ↦ ψ x) hτ

end TauCeti.ClassFieldTheory

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField ContCohomology
open scoped TensorProduct
variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)
open scoped AdicCompletionExtension
local notation "E₀" => ((⊥ : Ω) : IntermediateField K (SeparableClosure K))

variable (v) in
/-- **The coordinates at a finite place of the ideles of `K`.** Some embedding
`τ : Kˢ → K_vˢ` of separable closures reads, for every idele `a` of `K`, its component
`a_v ∈ K_vˣ` as the coordinate at `v` of the extension of `a` to `Kˢ`. -/
theorem exists_ideleCoeffComponent_ideleExtension_eq :
    ∃ τ : SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K),
      ∀ a : IdeleGroup (𝓞 K) K,
        ideleCoeffComponent τ (ideleCoeffOfIntermediateField K E₀
          (.ofMul (GlobalNumberFields.ideleExtension K E₀ a))) =
        (baseUnitsEquivInvariants (v.adicCompletion K) (.ofMul (v.ideleFiniteCoord a)) :
          UnitsCoeff (v.adicCompletion K)) := by
  obtain ⟨w, rfl⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 E₀) v
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨HeightOneSpectrum.under_asIdeal _ w⟩
  -- Naming the subextension keeps the unification with the completion types cheap.
  have h₀ := exists_ideleCoeffComponent_ideleCoeffOfIntermediateField_eq
    (E := E₀) (v := w.under (𝓞 K)) w
  obtain ⟨τ', τ, h⟩ := h₀
  refine ⟨τ, fun a ↦ Additive.toMul.injective ?_⟩
  refine (h (GlobalNumberFields.ideleExtension K E₀ a)).trans ?_
  simp only [GlobalNumberFields.ideleFiniteCoord_ideleExtension,
    toMul_coe_baseUnitsEquivInvariants, toMul_ofMul]
  refine Units.ext ?_
  simp only [Units.coe_map, MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe,
    ← HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra]
  exact τ'.commutes _

end TauCeti.ClassFieldTheory

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField ContCohomology
open scoped TensorProduct
variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
local notation "Ω" => FiniteGaloisIntermediateField K (SeparableClosure K)
open scoped AdicCompletionExtension
local notation "E₀" => ((⊥ : Ω) : IntermediateField K (SeparableClosure K))

open scoped NumberField.LiesOver in
/-- **The coordinates at an infinite place of the ideles of `K`.** Some embedding
`τ : Kˢ → K_wˢ` of separable closures reads, for every idele `a` of `K`, its component
`a_w ∈ K_wˣ` as the coordinate at `w` of the extension of `a` to `Kˢ`. -/
theorem exists_ideleCoeffInfiniteComponent_ideleExtension_eq (w : InfinitePlace K) :
    ∃ τ : SeparableClosure K →ₐ[K] SeparableClosure w.Completion,
      ∀ a : IdeleGroup (𝓞 K) K,
        ideleCoeffInfiniteComponent τ (ideleCoeffOfIntermediateField K E₀
          (.ofMul (GlobalNumberFields.ideleExtension K E₀ a))) =
        (baseUnitsEquivInvariants w.Completion (.ofMul (w.ideleInfiniteCoord a)) :
          UnitsCoeff w.Completion) := by
  obtain ⟨u, rfl⟩ := InfinitePlace.comap_surjective (k := K) (K := E₀) w
  -- Naming the subextension keeps the unification with the completion types cheap.
  have h₀ := exists_ideleCoeffInfiniteComponent_ideleCoeffOfIntermediateField_eq
    (E := E₀) (w := u.comap (algebraMap K E₀)) u
  obtain ⟨τ', τ, h⟩ := h₀
  refine ⟨τ, fun a ↦ Additive.toMul.injective ?_⟩
  refine (h (GlobalNumberFields.ideleExtension K E₀ a)).trans ?_
  simp only [GlobalNumberFields.ideleInfiniteCoord_ideleExtension,
    toMul_coe_baseUnitsEquivInvariants, toMul_ofMul]
  -- The algebra structure of `u.Completion` over the completion below is `completionMap`.
  exact Units.ext (τ'.commutes _)

end TauCeti.ClassFieldTheory

end
end
