import TameGeneratorClosedV001

/-!
# The tame generator in ambient Krull-closure form

From the finite-layer reading of the actual tame generator and the Krull neighbourhood basis
(fixing subgroups of finite Galois layers), an element agreeing on every finite Galois layer with
elements of a set `s` lies in the Krull closure of `s` (`mem_closure_of_layers`). Hence:

* `exists_tame_generator_ambient_closure`: for `Ω/K` Galois, `O` a discrete valuation ring and
  `w` over `O`, some actual inertia element `τ` has the whole inertia group inside the Krull
  closure of `{τ ^ k π | k ∈ ℤ, π wild}`;
* `leaf_tame_generator_ambient_closure`: the same in the leaf's objects (`K` a number field, `Ω`
  an algebraic closure, `PkgI2.IsInertia`, literal strict displacement).

No density, generator or restriction-surjectivity premise is used.
-/

noncomputable section
set_option autoImplicit false

namespace ActualTameInertia

open Topology

/-- **Krull closure from finite-layer agreement.** -/
theorem mem_closure_of_layers {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (s : Set (Ω ≃ₐ[K] Ω)) (σ : Ω ≃ₐ[K] Ω)
    (h : ∀ L : FiniteGaloisIntermediateField K Ω, ∃ ρ ∈ s,
      AlgEquiv.restrictNormalHom L.toIntermediateField ρ =
        AlgEquiv.restrictNormalHom L.toIntermediateField σ) :
    σ ∈ closure s := by
  rw [mem_closure_iff_nhds]
  intro t ht
  have h1 : (fun x : Ω ≃ₐ[K] Ω => σ * x) ⁻¹' t ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) := by
    apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    simpa using ht
  obtain ⟨L, hL⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois (k := K) (K := Ω) _).1 h1
  obtain ⟨ρ, hρs, hρ⟩ := h L
  have hfix : σ⁻¹ * ρ ∈ L.toIntermediateField.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker L.toIntermediateField, MonoidHom.mem_ker,
      map_mul, map_inv, hρ, inv_mul_cancel]
  have h2 : σ * (σ⁻¹ * ρ) ∈ t := hL hfix
  rw [mul_inv_cancel_left] at h2
  exact ⟨ρ, h2, hρs⟩

/-- **Ambient closure form of the actual tame generator** (Galois `Ω/K`, discrete `O`). -/
theorem exists_tame_generator_ambient_closure {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    [IsGalois K Ω] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    ∃ τ ∈ inertiaGroup (K := K) w,
      (inertiaGroup (K := K) w : Set (Ω ≃ₐ[K] Ω)) ⊆
        closure {σ : Ω ≃ₐ[K] Ω | ∃ k : ℤ, ∃ π ∈ wildGroup (K := K) w, σ = τ ^ k * π} := by
  obtain ⟨τ, hτ⟩ := exists_tame_generator_layers O w hw
  refine ⟨τ, τ.2, fun σ hσ => mem_closure_of_layers _ σ fun L => ?_⟩
  obtain ⟨k, π, hπ, hres⟩ := hτ ⟨σ, hσ⟩ L
  refine ⟨(τ : Ω ≃ₐ[K] Ω) ^ k * π, ⟨k, π, hπ, rfl⟩, ?_⟩
  rw [map_mul, ← Subgroup.coe_zpow]
  exact hres

/-- **Ambient closure form in the leaf's objects.** -/
theorem leaf_tame_generator_ambient_closure (K : Type) [Field K] [NumberField K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    ∃ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ ∧
      {σ : Ω ≃ₐ[K] Ω | PkgI2.IsInertia w σ} ⊆
        closure {σ : Ω ≃ₐ[K] Ω | ∃ k : ℤ, ∃ π : Ω ≃ₐ[K] Ω,
          (∀ x : Ω, x ≠ 0 → w.valuation (π x - x) < w.valuation x) ∧ σ = τ ^ k * π} := by
  have : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  obtain ⟨τ, hτ, hlayer⟩ := leaf_tame_generator K O Ω w hw
  refine ⟨τ, hτ, fun σ hσ => mem_closure_of_layers _ σ fun L => ?_⟩
  obtain ⟨k, π, hπ, hres⟩ := hlayer σ hσ L
  exact ⟨τ ^ k * π, ⟨k, π, hπ, rfl⟩, hres⟩

end ActualTameInertia

#check @ActualTameInertia.leaf_tame_generator_ambient_closure
#check @ActualTameInertia.exists_tame_generator_ambient_closure
#print axioms ActualTameInertia.mem_closure_of_layers
#print axioms ActualTameInertia.exists_tame_generator_ambient_closure
#print axioms ActualTameInertia.leaf_tame_generator_ambient_closure
