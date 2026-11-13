/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

The forward completion-action construction is adapted at declaration level from
TauCeti revision a6027b1d24fcb935c53bd5b50d11b40991cda418,
NumberTheory/NumberField/LocalGlobal/DecompositionGroup.lean.
It uses the actual affine base `ℤ ⊆ 𝓞 L` and the canonical completed algebra.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.NumberField
public import ZInQKernel.Contrib.GlobalDifferentTransport.Equiv
public import Mathlib.FieldTheory.Normal.Basic

/-!
# The actual decomposition-group action on completed rings

The maps in this file act on the concrete completed fields and integer rings.
They agree with the original number-field automorphisms on global elements,
and with the global ring-of-integers action on global integers.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped NumberField Pointwise GlobalDifferentTransportCompletion

namespace GlobalDifferentTransport

variable (L : Type*) [Field L] [NumberField L]
  (v : HeightOneSpectrum ℤ) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The genuine decomposition subgroup in the global rational automorphism group. -/
abbrev decompositionGroup := MulAction.stabilizer Gal(L/ℚ) w.asIdeal

/-- A member of the actual decomposition group preserves the global adic valuation. -/
theorem valuation_stabilizer (σ : decompositionGroup L w) (x : L) :
    w.valuation L ((σ : Gal(L/ℚ)) x) = w.valuation L x := by
  let e := MulSemiringAction.toRingEquiv Gal(L/ℚ) (𝓞 L) (σ : Gal(L/ℚ))
  have hσ : (IsFractionRing.ringEquivOfRingEquiv e : L ≃+* L) =
      (σ : Gal(L/ℚ)).toRingEquiv := by
    apply RingEquiv.toRingHom_injective
    apply IsFractionRing.ringHom_ext (A := 𝓞 L)
    intro a
    change (IsFractionRing.ringEquivOfRingEquiv e : L ≃+* L)
      (algebraMap (𝓞 L) L a) = (σ : Gal(L/ℚ)) (algebraMap (𝓞 L) L a)
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    rfl
  have hw : w.asIdeal = w.asIdeal.map e := by
    calc
      w.asIdeal = (σ : Gal(L/ℚ)) • w.asIdeal :=
        (MulAction.mem_stabilizer_iff.mp σ.2).symm
      _ = w.asIdeal.map e := by
        rw [Ideal.pointwise_smul_def]
        rfl
  rw [← AlgEquiv.coe_toRingEquiv, ← hσ]
  exact valuation_ringEquivOfRingEquiv (K := L) (K' := L) e hw x

/-- The continuous completion isomorphism of a genuine global decomposition automorphism. -/
def completionDecompositionRingEquiv (σ : decompositionGroup L w) :
    w.adicCompletion L ≃+* w.adicCompletion L :=
  adicCompletionRingEquiv w w (σ : Gal(L/ℚ)).toRingEquiv (valuation_stabilizer L w σ)

/-- On global field elements this is the original automorphism. -/
theorem completionDecompositionRingEquiv_algebraMap (σ : decompositionGroup L w) (x : L) :
    completionDecompositionRingEquiv L w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : Gal(L/ℚ)) x) :=
  adicCompletionRingEquiv_algebraMap _ _ _ _ x

/-- The induced field isomorphism is continuous. -/
theorem continuous_completionDecompositionRingEquiv (σ : decompositionGroup L w) :
    Continuous (completionDecompositionRingEquiv L w σ) :=
  continuous_adicCompletionRingEquiv _ _ _ _

/-- The induced isomorphism preserves the completed normalized valuation. -/
theorem valued_completionDecompositionRingEquiv (σ : decompositionGroup L w)
    (x : w.adicCompletion L) :
    Valued.v (completionDecompositionRingEquiv L w σ x) = Valued.v x :=
  valued_adicCompletionRingEquiv _ _ _ _ x

/-- The same actual completion isomorphism as an automorphism over the completed base field. -/
def completionDecompositionAlgEquiv (σ : decompositionGroup L w) :
    w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L :=
  AlgEquiv.ofRingEquiv (f := completionDecompositionRingEquiv L w σ) fun a ↦ by
    have h : (completionDecompositionRingEquiv L w σ).toRingHom.comp
        (completionRingHom ℚ L v w) = completionRingHom ℚ L v w := by
      apply eq_completionRingHom_of_continuous ℚ L v w
      · exact (continuous_completionDecompositionRingEquiv L w σ).comp
          (continuous_completionRingHom ℚ L v w)
      · intro x
        rw [RingHom.comp_apply, completionRingHom_coe]
        change completionDecompositionRingEquiv L w σ
          (algebraMap L (w.adicCompletion L) (algebraMap ℚ L x)) =
            algebraMap L (w.adicCompletion L) (algebraMap ℚ L x)
        rw [completionDecompositionRingEquiv_algebraMap, AlgEquiv.commutes]
    rw [algebraMap_completionAlgebra]
    exact congrArg (fun f : v.adicCompletion ℚ →+* w.adicCompletion L ↦ f a) h

/-- The canonical action of the actual decomposition group on the completed extension field. -/
def decompositionFieldHom : decompositionGroup L w →*
    (w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) where
  toFun := completionDecompositionAlgEquiv L v w
  map_one' := by
    apply DFunLike.coe_injective
    apply (w.denseRange_algebraMap L).equalizer
      (continuous_completionDecompositionRingEquiv L w 1) continuous_id
    funext x
    exact completionDecompositionRingEquiv_algebraMap L w 1 x
  map_mul' σ τ := by
    apply DFunLike.coe_injective
    apply (w.denseRange_algebraMap L).equalizer
      (continuous_completionDecompositionRingEquiv L w (σ * τ))
      ((continuous_completionDecompositionRingEquiv L w σ).comp
        (continuous_completionDecompositionRingEquiv L w τ))
    funext x
    simp only [Function.comp_apply]
    rw [completionDecompositionRingEquiv_algebraMap,
      completionDecompositionRingEquiv_algebraMap,
      completionDecompositionRingEquiv_algebraMap]
    rfl

/-- The field action agrees with the original global automorphism on every global element. -/
theorem decompositionFieldHom_algebraMap (σ : decompositionGroup L w) (x : L) :
    decompositionFieldHom L v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : Gal(L/ℚ)) x) :=
  completionDecompositionRingEquiv_algebraMap L w σ x

/-- The field action of the decomposition group is faithful. -/
theorem decompositionFieldHom_injective : Function.Injective (decompositionFieldHom L v w) := by
  intro σ τ h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L (w.adicCompletion L)).injective
  have hx := congrArg (fun f : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L ↦
    f (algebraMap L (w.adicCompletion L) x)) h
  rw [decompositionFieldHom_algebraMap, decompositionFieldHom_algebraMap] at hx
  exact hx

/-- Restriction of this actual field action to the concrete completed integer ring. -/
def decompositionIntegersEquiv (σ : decompositionGroup L w) :
    w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ] w.adicCompletionIntegers L := by
  let E := completionDecompositionRingEquiv L w σ
  have hE (x : w.adicCompletion L) : Valued.v (E x) = Valued.v x :=
    valued_completionDecompositionRingEquiv L w σ x
  have hE' (x : w.adicCompletion L) : Valued.v (E.symm x) = Valued.v x := by
    rw [← hE (E.symm x), E.apply_symm_apply]
  let e : w.adicCompletionIntegers L ≃+* w.adicCompletionIntegers L :=
    { toFun := fun x ↦ ⟨E x, by rw [mem_adicCompletionIntegers, hE]; exact x.2⟩
      invFun := fun x ↦ ⟨E.symm x, by rw [mem_adicCompletionIntegers, hE']; exact x.2⟩
      left_inv := fun x ↦ Subtype.ext (E.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (E.apply_symm_apply x)
      map_add' := fun x y ↦ Subtype.ext (E.map_add x y)
      map_mul' := fun x y ↦ Subtype.ext (E.map_mul x y) }
  refine AlgEquiv.ofRingEquiv (f := e) fun a ↦ ?_
  apply Subtype.ext
  exact (completionDecompositionAlgEquiv L v w σ).commutes (a : v.adicCompletion ℚ)

/-- The actual decomposition-group homomorphism into automorphisms of the completed integer ring. -/
def decompositionIntegersHom : decompositionGroup L w →*
    (w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ] w.adicCompletionIntegers L) where
  toFun := decompositionIntegersEquiv L v w
  map_one' := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L ↦
      f (x : w.adicCompletion L)) (decompositionFieldHom L v w).map_one
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L ↦
      f (x : w.adicCompletion L)) ((decompositionFieldHom L v w).map_mul σ τ)

/-- The completed-integer action agrees with the genuine global integer action. -/
theorem decompositionIntegersHom_algebraMap (σ : decompositionGroup L w) (a : 𝓞 L) :
    decompositionIntegersHom L v w σ (algebraMap (𝓞 L) (w.adicCompletionIntegers L) a) =
      algebraMap (𝓞 L) (w.adicCompletionIntegers L) ((σ : Gal(L/ℚ)) • a) := by
  apply Subtype.ext
  change completionDecompositionRingEquiv L w σ
    (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L a)) = _
  rw [completionDecompositionRingEquiv_algebraMap]
  rfl

/-- The completed-integer action is faithful. -/
theorem decompositionIntegersHom_injective :
    Function.Injective (decompositionIntegersHom L v w) := by
  intro σ τ h
  apply decompositionFieldHom_injective L v w
  apply AlgEquiv.toRingEquiv_injective
  apply RingEquiv.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := w.adicCompletionIntegers L)
  intro x
  exact congrArg (fun y : w.adicCompletionIntegers L ↦ (y : w.adicCompletion L))
    (congrArg (fun f : w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ]
      w.adicCompletionIntegers L ↦ f x) h)

/-- Every local ring automorphism preserves all powers of the completed maximal ideal. -/
theorem completedIntegerAut_preserves_maximalIdeal_pow
    (σ : w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ]
      w.adicCompletionIntegers L) (n : ℕ) (x : w.adicCompletionIntegers L)
    (hx : x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ n) :
    σ x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ n := by
  have hmap : (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ n).map σ =
      IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) ^ n := by
    rw [Ideal.map_pow]
    change (Ideal.map σ.toRingEquiv
      (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L))) ^ n = _
    rw [IsLocalRing.map_ringEquiv_maximalIdeal σ.toRingEquiv]
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ hx

end GlobalDifferentTransport
