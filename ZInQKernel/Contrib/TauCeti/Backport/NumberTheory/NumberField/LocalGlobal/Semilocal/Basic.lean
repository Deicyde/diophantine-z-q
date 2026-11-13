/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
public import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
public import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree
public import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.PrimesAbove
public import ZInQKernel.Contrib.TauCeti.RingTheory.Ideal.PrimesOver

public section
noncomputable section

open IsDedekindDomain NumberField Module
open scoped TensorProduct NumberField AdicCompletionExtension Valued
open IsDedekindDomain.HeightOneSpectrum
namespace TauCeti

local notation "𝒪" => _root_.NumberField.RingOfIntegers
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K))
variable {L v}
variable (L v)
variable {L v}
variable (L v)

attribute [local instance] Fintype.ofFinite in
/-- **An embedding of `L` into a `K_v`-domain extends to a completion of `L` above `v`.** For a
domain `M` that is a `K_v`-algebra, every `K`-algebra map `φ : L → M` is the restriction to `L` of
a `K_v`-algebra map `L_w → M` from the completion of `L` at some place `w` above `v`. Indeed `φ`
induces a `K_v`-algebra map `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w → M`, and a ring homomorphism from a
finite product of rings to a domain factors through one of the factors. -/
theorem exists_algHom_adicCompletion_eq {M : Type*} [CommRing M] [IsDomain M] [Algebra K M]
    [Algebra (v.adicCompletion K) M] [IsScalarTower K (v.adicCompletion K) M] (φ : L →ₐ[K] M) :
    ∃ (w : HeightOneSpectrum (𝒪 L)) (_ : w.asIdeal.LiesOver v.asIdeal)
      (φ' : w.adicCompletion L →ₐ[v.adicCompletion K] M),
      ∀ x : L, φ x = φ' (algebraMap L (w.adicCompletion L) x) := by
  classical
  -- The `K_v`-algebra map `∏_{w ∣ v} L_w ≃ K_v ⊗[K] L → M` induced by `φ`.
  let f := (Algebra.TensorProduct.lift (Algebra.ofId (v.adicCompletion K) M) φ
    fun _ _ ↦ .all _ _).comp (semilocalEquiv L v).symm.toAlgHom
  -- It kills one of the idempotents `e i = 1 - [i]`, whose product vanishes.
  let e (i : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
      (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletion L := Function.update 1 i 0
  have he (i) : e i + Pi.single i 1 = 1 := funext fun j ↦ by
    by_cases h : j = i
    · subst h
      simp [e]
    · simp [e, h]
  obtain ⟨i, hi⟩ : ∃ i, f (e i) = 0 := by
    have H : ∏ i, e i = 0 := funext fun j ↦ by
      rw [Finset.prod_apply, Pi.zero_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [e])
    have := congrArg f H
    rw [map_prod, map_zero] at this
    simpa using Finset.prod_eq_zero_iff.1 this
  have hi1 : f (Pi.single i 1) = 1 := by
    have := congrArg f (he i)
    rwa [map_add, hi, zero_add, map_one] at this
  -- So `f` factors through the factor `L_i`.
  have hf (x) : f x = f (Pi.single i (x i)) := by
    have hx : x * Pi.single i 1 = Pi.single i (x i) := funext fun j ↦ by
      by_cases h : j = i
      · subst h
        simp
      · simp [h]
    rw [← hx, map_mul, hi1, mul_one]
  let φ' : i.1.adicCompletion L →ₐ[v.adicCompletion K] M :=
    AlgHom.ofLinearMap (f.toLinearMap.comp (LinearMap.single (v.adicCompletion K)
      (fun w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} ↦
        w.1.adicCompletion L) i)) hi1
      (fun x y ↦ by simp [Pi.single_mul])
  refine ⟨i.1, i.2, φ', fun x ↦ ?_⟩
  have : φ x = f (fun w ↦ algebraMap L (w.1.adicCompletion L) x) := by
    simp [f, semilocalEquiv_symm_algebraMap L v x]
  rw [this, hf]
  rfl

end TauCeti

end
end
