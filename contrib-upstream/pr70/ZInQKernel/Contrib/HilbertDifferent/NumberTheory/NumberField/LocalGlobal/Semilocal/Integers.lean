/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/NumberField/LocalGlobal/Semilocal/Integers.lean
Original SHA-256: a99bb035c469101f954444f16e84a893474a3f632eeee8e904f86bc63b35ac32
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/NumberTheory/NumberField/LocalGlobal/Semilocal/Integers.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Topology.Algebra.Module.Compact
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.Approximation
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.IntegralClosure
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open IsDedekindDomain NumberField
open scoped TensorProduct NumberField AdicCompletionExtension Valued

namespace TauCeti

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]
  (L : Type*) [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K))

/- The canonical map from the integral scalar extension at `v` to the product of the completed
integer rings at the places above `v`. -/
def integralSemilocalHom :
    v.adicCompletionIntegers K ⊗[𝓞 K] 𝒪 L →ₐ[v.adicCompletionIntegers K]
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletionIntegers L) :=
  letI (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
      Algebra (𝒪 K) (w.1.adicCompletionIntegers L) :=
    ((algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)).comp
      (algebraMap (𝒪 K) (v.adicCompletionIntegers K))).toAlgebra
  letI (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
      IsScalarTower (𝒪 K) (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (AlgHom.pi fun w ↦
      { algebraMap (𝒪 L) (w.1.adicCompletionIntegers L) with
        commutes' := fun r ↦ by
          -- Expose the composite algebra structure installed just above so the two named
          -- compatibility lemmas apply.
          change algebraMap (𝒪 L) (w.1.adicCompletionIntegers L)
              (algebraMap (𝒪 K) (𝒪 L) r) =
            algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
              (algebraMap (𝒪 K) (v.adicCompletionIntegers K) r)
          rw [algebraMap_adicCompletionIntegersExtensionAlgebra,
            adicCompletionIntegersExtension_algebraMap] })
    fun _ _ ↦ .all _ _

variable {L v}

/- The integral semi-local map on a pure tensor. -/
@[simp]
theorem integralSemilocalHom_tmul (a : v.adicCompletionIntegers K) (x : 𝒪 L)
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    integralSemilocalHom L v (a ⊗ₜ x) w =
      algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) a *
        algebraMap (𝒪 L) (w.1.adicCompletionIntegers L) x := by
  simp [integralSemilocalHom]

variable (L v)

omit [NumberField K] in
/- The diagonal image of the global integers is dense in the product of the completed integer
rings at the places above `v`. -/
theorem denseRange_algebraMap_integers_pi_liesOver :
    DenseRange fun (x : 𝒪 L)
      (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) ↦
        algebraMap (𝒪 L) (w.1.adicCompletionIntegers L) x :=
  denseRange_algebraMap_pi_subtype (K := L) (fun w ↦ w.asIdeal.LiesOver v.asIdeal)

/- The integral semi-local map is surjective. -/
theorem integralSemilocalHom_surjective : Function.Surjective (integralSemilocalHom L v) := by
  let _ (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
      ContinuousSMul (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) := by
    apply continuousSMul_of_algebraMap
    apply continuous_induced_rng.mpr
    rw [algebraMap_adicCompletionIntegersExtensionAlgebra]
    exact (v.continuous_adicCompletionExtension K L w.1).comp continuous_subtype_val |>.congr
      fun x ↦ (coe_adicCompletionIntegersExtension K L v w.1 x).symm
  let s := LinearMap.range (integralSemilocalHom L v).toLinearMap
  have hsfg : s.FG := by
    simpa only [s, LinearMap.range_eq_map] using
      Module.Finite.fg_top.map (integralSemilocalHom L v).toLinearMap
  have hs : Set.range (fun (x : 𝒪 L)
      (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) ↦
        algebraMap (𝒪 L) (w.1.adicCompletionIntegers L) x) ⊆ s := by
    rintro _ ⟨x, rfl⟩
    exact ⟨1 ⊗ₜ x, funext fun w ↦ by simp⟩
  intro y
  exact (Submodule.isCompact_of_fg hsfg).isClosed.closure_subset_iff.mpr hs
    (denseRange_algebraMap_integers_pi_liesOver L v y)

private def integralFieldBaseChangeEquiv :
    v.adicCompletion K ⊗[𝒪 K] 𝒪 L ≃ₐ[v.adicCompletion K]
      v.adicCompletion K ⊗[K] L :=
  (Algebra.TensorProduct.cancelBaseChange (𝒪 K) K (v.adicCompletion K)
      (v.adicCompletion K) (𝒪 L)).symm.trans
    (Algebra.TensorProduct.congr (.refl : v.adicCompletion K ≃ₐ[v.adicCompletion K]
      v.adicCompletion K) (Algebra.IsPushout.equiv (𝒪 K) K (𝒪 L) L))

@[simp]
private theorem integralFieldBaseChangeEquiv_tmul (a : v.adicCompletion K) (x : 𝒪 L) :
    integralFieldBaseChangeEquiv L v (a ⊗ₜ x) = a ⊗ₜ (x : L) := by
  simp [integralFieldBaseChangeEquiv, Algebra.IsPushout.equiv_tmul]

private def integralFieldBaseChangeAlgHom :
    v.adicCompletion K ⊗[𝒪 K] 𝒪 L →ₐ[𝒪 K]
      v.adicCompletion K ⊗[K] L :=
  { (integralFieldBaseChangeEquiv L v).toRingEquiv.toRingHom with
    commutes' := fun r ↦ by
      -- The source uses its tensor-product algebra over `𝒪 K`, whereas the equivalence is
      -- linear over the completion. Exposing both algebra maps lets the pure-tensor lemma bridge
      -- these non-definitionally-equal structures.
      change integralFieldBaseChangeEquiv L v
          (algebraMap (𝒪 K) (v.adicCompletion K) r ⊗ₜ[𝒪 K] (1 : 𝒪 L)) =
        algebraMap (𝒪 K) (v.adicCompletion K) r ⊗ₜ[K] (1 : L)
      rw [integralFieldBaseChangeEquiv_tmul]
      rfl }

private def adicCompletionIntegersToCompletion :
    v.adicCompletionIntegers K →ₐ[𝒪 K] v.adicCompletion K :=
  @AlgHom.restrictScalars (𝒪 K) (v.adicCompletionIntegers K)
    (v.adicCompletionIntegers K) (v.adicCompletion K) _ _ _ _ _ _ _ _ _
    (@IsScalarTower.of_algebraMap_eq (𝒪 K) (v.adicCompletionIntegers K)
      (v.adicCompletionIntegers K) _ _ _ _ _ _ fun _ ↦ rfl)
    (@IsScalarTower.of_algebraMap_eq (𝒪 K) (v.adicCompletionIntegers K)
      (v.adicCompletion K) _ _ _ _ _ _ fun _ ↦ rfl)
    (Algebra.ofId (v.adicCompletionIntegers K) (v.adicCompletion K))

private def integralTensorToBaseChange :
    v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L →ₐ[𝒪 K]
      v.adicCompletion K ⊗[𝒪 K] 𝒪 L :=
  { (Algebra.TensorProduct.map (adicCompletionIntegersToCompletion v)
      (AlgHom.id (𝒪 K) (𝒪 L))).toRingHom with
    commutes' := fun _ ↦ rfl }

omit [NumberField L] in
@[simp]
private theorem integralTensorToBaseChange_tmul
    (a : v.adicCompletionIntegers K) (x : 𝒪 L) :
    integralTensorToBaseChange L v (a ⊗ₜ x) = (a : v.adicCompletion K) ⊗ₜ x := rfl

omit [NumberField L] in
private theorem integralTensorToBaseChange_injective :
    Function.Injective (integralTensorToBaseChange L v) := by
  -- Expose the underlying linear tensor map; the bundled algebra structures differ, but the
  -- functions are definitionally the same.
  change Function.Injective (TensorProduct.map
    (adicCompletionIntegersToCompletion v).toLinearMap
    (AlgHom.id (𝒪 K) (𝒪 L)).toLinearMap)
  exact TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Function.injective_id

/- The canonical inclusion of the integral tensor product in the field tensor product. -/
def integralSemilocalToField :
    v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L →ₐ[𝒪 K]
      v.adicCompletion K ⊗[K] L :=
  (integralFieldBaseChangeAlgHom L v).comp (integralTensorToBaseChange L v)

variable {L v}

/- The inclusion in the field tensor product on a pure tensor. -/
@[simp]
theorem integralSemilocalToField_tmul (a : v.adicCompletionIntegers K) (x : 𝒪 L) :
    integralSemilocalToField L v (a ⊗ₜ x) =
      (a : v.adicCompletion K) ⊗ₜ (x : L) := by
  rw [integralSemilocalToField, AlgHom.comp_apply, integralTensorToBaseChange_tmul]
  exact integralFieldBaseChangeEquiv_tmul (L := L) (v := v) (a : v.adicCompletion K) x

private theorem algebraMap_adicCompletionExtension_coe
    (a : v.adicCompletionIntegers K)
    (w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) :
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (a : v.adicCompletion K) =
      (algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) a :
        w.1.adicCompletion L) := by
  rw [algebraMap_adicCompletionIntegersExtensionAlgebra,
    algebraMap_adicCompletionExtensionAlgebra, coe_adicCompletionIntegersExtension]

private theorem algebraMap_ringOfIntegers_adicCompletion_eq_coe
    (x : 𝒪 L) (w : HeightOneSpectrum (𝒪 L)) :
    algebraMap (𝒪 L) (w.adicCompletion L) x =
      (algebraMap (𝒪 L) (w.adicCompletionIntegers L) x : w.adicCompletion L) := by
  rw [algebraMap_adicCompletionIntegers_apply,
    IsScalarTower.algebraMap_apply (𝒪 L) L (w.adicCompletion L),
    algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply]

/- The integral and field semi-local maps agree after inclusion in the completions. -/
theorem integralSemilocalHom_fieldCompatibility
    (z : v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L) :
    semilocalEquiv L v (integralSemilocalToField L v z) =
      fun w ↦ (integralSemilocalHom L v z w : w.1.adicCompletion L) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy =>
      funext w
      simp only [map_add, Pi.add_apply]
      exact congrArg₂ (fun a b ↦ a + b) (congrFun hx w) (congrFun hy w)
  | tmul a x =>
      funext w
      simp only [integralSemilocalToField_tmul, semilocalEquiv_tmul,
        integralSemilocalHom_tmul]
      rw [← IsScalarTower.algebraMap_apply (𝒪 L) L (w.1.adicCompletion L),
        algebraMap_adicCompletionExtension_coe,
        algebraMap_ringOfIntegers_adicCompletion_eq_coe]
      rfl

variable (L v)

/- The canonical inclusion of the integral tensor product in the field tensor product is
injective. -/
theorem integralSemilocalToField_injective : Function.Injective (integralSemilocalToField L v) := by
  intro x y hxy
  apply integralTensorToBaseChange_injective L v
  apply (integralFieldBaseChangeEquiv L v).injective
  exact hxy

/- The integral semi-local map is injective. -/
theorem integralSemilocalHom_injective : Function.Injective (integralSemilocalHom L v) := by
  intro x y hxy
  apply integralSemilocalToField_injective L v
  apply (semilocalEquiv L v).injective
  rw [integralSemilocalHom_fieldCompatibility,
    integralSemilocalHom_fieldCompatibility, hxy]

/- **The integral semi-local decomposition**: scalar extension of the global integers to the
completed integer ring at `v` is the product of the completed integer rings above `v`. -/
def integralSemilocalEquiv :
    v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L ≃ₐ[v.adicCompletionIntegers K]
      ((w : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}) →
        w.1.adicCompletionIntegers L) :=
  -- Keep the `Bijective` ascription explicit: without it Lean exports the generated proof as a
  -- bare conjunction, which is not transparent enough when downstream lemmas unfold this def.
  AlgEquiv.ofBijective (integralSemilocalHom L v)
    (show Function.Bijective (integralSemilocalHom L v) from
      ⟨integralSemilocalHom_injective L v, integralSemilocalHom_surjective L v⟩)

variable {L v}

/- The integral semi-local decomposition on a pure tensor. -/
theorem integralSemilocalEquiv_fieldCompatibility
    (z : v.adicCompletionIntegers K ⊗[𝒪 K] 𝒪 L) :
    semilocalEquiv L v (integralSemilocalToField L v z) =
      fun w ↦ (integralSemilocalEquiv L v z w : w.1.adicCompletion L) := by
  rw [integralSemilocalEquiv, AlgEquiv.ofBijective_apply]
  exact integralSemilocalHom_fieldCompatibility z

/- Projection of the integral semi-local decomposition to the completed integer ring at `w`. -/
end TauCeti

end

end
