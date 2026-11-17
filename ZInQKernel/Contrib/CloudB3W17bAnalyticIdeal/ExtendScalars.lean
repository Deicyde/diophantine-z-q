import Mathlib

/-!
# Base change along a local homomorphism reflects surjectivity onto the ring

For a local homomorphism of local rings `R → S` and an `R`-linear `g : M → N` with `N ≅ R`,
`S ⊗ g` is surjective iff `g` is. This is the stalk step identifying the vanishing locus of an
inverse-image ideal.
-/

open CategoryTheory TensorProduct

universe u

namespace ZInQ.Contrib.CloudB3W17bAnalyticIdeal

/-- For a local homomorphism of local rings,
the base change of `g : M → R` is surjective iff `g` is. -/
theorem surjective_baseChange_iff {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] {M : Type*} [AddCommGroup M]
    [Module R M] (g : M →ₗ[R] R) :
    Function.Surjective (LinearMap.baseChange S g) ↔ Function.Surjective g := by
  let e := (Algebra.TensorProduct.rid R S S).toLinearMap.restrictScalars S
  have he : Function.Bijective e := (Algebra.TensorProduct.rid R S S).bijective
  have key : Function.Surjective (e ∘ₗ LinearMap.baseChange S g) ↔ Function.Surjective g := by
    rw [← LinearMap.range_eq_top, ← LinearMap.range_eq_top]
    have hr : LinearMap.range (e ∘ₗ LinearMap.baseChange S g) =
        (Ideal.map (algebraMap R S) (LinearMap.range g) : Submodule S S) := by
      apply le_antisymm
      · rintro _ ⟨t, rfl⟩
        induction t using TensorProduct.inductionOn with
        | tmul s m =>
          simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul, e,
            LinearMap.coe_restrictScalars, AlgEquiv.toLinearMap_apply,
            Algebra.TensorProduct.rid_tmul]
          rw [Algebra.smul_def, mul_comm]
          exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ⟨m, rfl⟩)
        | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
      · intro y hy
        refine Submodule.span_induction
          (p := fun y _ => y ∈ LinearMap.range (e ∘ₗ LinearMap.baseChange S g)) ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨r, ⟨m, rfl⟩, rfl⟩
          refine ⟨1 ⊗ₜ m, ?_⟩
          simp [e, Algebra.smul_def]
        · exact Submodule.zero_mem _
        · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
        · intro a b _ hb; exact Submodule.smul_mem _ a hb
    rw [hr]
    constructor
    · intro h
      by_contra hg
      have hJ : LinearMap.range g ≠ ⊤ := hg
      have hle : LinearMap.range g ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal hJ
      have hle' : Ideal.map (algebraMap R S) (LinearMap.range g) ≤ IsLocalRing.maximalIdeal S := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        have hxm := hle hx
        rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun hu => (IsLocalRing.mem_maximalIdeal x).mp hxm (isUnit_of_map_unit _ x hu)
      have htop : (⊤ : Ideal S) ≤ IsLocalRing.maximalIdeal S := h ▸ hle'
      exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_le_iff.mp htop)
    · intro h
      change Ideal.map (algebraMap R S) (LinearMap.range g) = ⊤
      rw [h]; exact Ideal.map_top _
  rw [← key, LinearMap.coe_comp]
  exact ⟨fun h => he.2.comp h, fun h => (Function.Surjective.of_comp_iff' he _).mp h⟩

/-- **Point-locus step 2 (conditional on the unit-stalk identification `e`).** Extension of
scalars along a local homomorphism of local rings preserves and reflects surjectivity of a map
into a module isomorphic to the ring. -/
theorem surjective_extendScalars_map_iff {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (e : N ≃ₗ[R] R) :
    Function.Surjective ((ModuleCat.extendScalars f).map g) ↔ Function.Surjective g := by
  let _ : Algebra R S := ((algebraMap S S).comp f).toAlgebra
  have : IsLocalHom (algebraMap R S) := by
    show IsLocalHom ((algebraMap S S).comp f)
    rw [Algebra.algebraMap_self, RingHom.id_comp]
    infer_instance
  have h1 : (⇑((ModuleCat.extendScalars f).map g) : _ → _) =
      ⇑(LinearMap.baseChange S g.hom) := rfl
  have hb : Function.Bijective (LinearMap.baseChange S (e : N →ₗ[R] R)) := by
    have := (LinearEquiv.baseChange R S N R e).bijective
    exact this
  have key := surjective_baseChange_iff (S := S) ((e : N →ₗ[R] R) ∘ₗ g.hom)
  have he : Function.Bijective (⇑(e : N →ₗ[R] R)) := e.bijective
  rw [LinearMap.baseChange_comp, LinearMap.coe_comp,
    Function.Surjective.of_comp_iff' hb, LinearMap.coe_comp,
    Function.Surjective.of_comp_iff' he] at key
  exact (congrArg Function.Surjective h1).to_iff.trans key

end ZInQ.Contrib.CloudB3W17bAnalyticIdeal
