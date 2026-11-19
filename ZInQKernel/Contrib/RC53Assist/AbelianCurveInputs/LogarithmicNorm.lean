import ZInQKernel.Contrib.RC53Assist.InvariantDifferential.DivisorZero
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Field.TransferInstance

/-!
# Logarithmic differentiation of a field norm

For a separating parameter, the logarithmic derivative of the norm equals the
trace of the logarithmic derivative. The proof differentiates the product over
field embeddings. No assertion about the normalization of a Weil differential
is used.

Locators: Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
Chapter III, norm and trace; Mathlib `Algebra.norm_eq_prod_embeddings` and
`trace_eq_sum_embeddings`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurveInputs.LogarithmicNorm

open Module TauCeti Polynomial KaehlerDifferential
open scoped IntermediateField

/-- STRUCTURE. A copy of an algebraic closure, with scalar actions supplied by
chosen field embeddings. Locator: Mathlib `AlgebraicClosure`. -/
private structure NormClosure (F : Type) [Field F] where
  val : AlgebraicClosure F

/-- DEFINITION. The underlying equivalence with the algebraic closure.
Locator: the `NormClosure` structure above. -/
private def normClosureEquiv (F : Type) [Field F] : NormClosure F ≃ AlgebraicClosure F :=
  ⟨fun a => a.val, fun a => ⟨a⟩, fun _ => rfl, fun _ => rfl⟩

/-- INSTANCE. Transport of the field operations to the copied carrier.
Locator: Mathlib `Equiv.field`. -/
private instance normClosureField (F : Type) [Field F] : Field (NormClosure F) :=
  (normClosureEquiv F).field

/-- DEFINITION. The copy equivalence respects addition and multiplication.
Locator: Mathlib `Equiv.field`, and `normClosureEquiv` above. -/
private def normClosureRingEquiv (F : Type) [Field F] : NormClosure F ≃+* AlgebraicClosure F :=
  { normClosureEquiv F with map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }

/-- INSTANCE. The copied field is algebraically closed.
Locator: Mathlib `IsAlgClosed.of_ringEquiv`. -/
private instance normClosureIsAlgClosed (F : Type) [Field F] : IsAlgClosed (NormClosure F) :=
  IsAlgClosed.of_ringEquiv (AlgebraicClosure F) (NormClosure F) (normClosureRingEquiv F).symm

/-- THEOREM. The logarithmic derivative of a nonzero finite product is the sum
of the logarithmic derivatives. Locator: the Leibniz rule and finite induction. -/
private theorem log_derivative_prod {k L ι : Type*} [Field k] [Field L] [Algebra k L]
    (d : Derivation k L L) (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, f i ≠ 0) :
    d (∏ i ∈ s, f i) / (∏ i ∈ s, f i) = ∑ i ∈ s, d (f i) / f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs =>
    have hfi : f i ≠ 0 := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hprod : (∏ j ∈ s, f j) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfs
    rw [Finset.prod_insert hi, Finset.sum_insert hi, d.leibniz, smul_eq_mul, smul_eq_mul]
    rw [← hs hfs]
    field_simp
    ring

/-- THEOREM. Logarithmic differentiation commutes with a finite separable field
norm, with trace on the logarithmic derivative.
Locator: Mathlib `Algebra.norm_eq_prod_embeddings`, `trace_eq_sum_embeddings`;
Tau Ceti `Derivation.apply_eq_derivativeOfSeparating_smul`. -/
theorem separating_trace_logarithmic_derivative {k F : Type} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) {x z : F} (hx : Transcendental k x) (hz : z ≠ 0) :
    letI := hF.finiteDimensional_adjoin hx
    letI := ratFuncAlgebraOfTranscendental hx
    letI := isScalarTower_ratFuncAlgebraOfTranscendental hx
    letI := isFunctionField_iff_functionField.mp hF
    letI := isSeparable_ratFuncAlgebraOfTranscendental hx
    letI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin (RatFunc.transcendental_X (K := k))
    Algebra.trace (RatFunc k) F (derivativeOfSeparating hx z / z) =
      derivativeOfSeparating (RatFunc.transcendental_X (K := k)) (Algebra.norm (RatFunc k) z) /
        Algebra.norm (RatFunc k) z := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  haveI := hF.finiteDimensional_adjoin hx
  letI := ratFuncAlgebraOfTranscendental hx
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental hx
  haveI := isFunctionField_iff_functionField.mp hF
  haveI := isSeparable_ratFuncAlgebraOfTranscendental hx
  haveI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin (RatFunc.transcendental_X (K := k))
  let L := NormClosure F
  letI : Algebra F L := ((normClosureRingEquiv F).symm.toRingHom.comp
    (algebraMap F (AlgebraicClosure F))).toAlgebra
  haveI : Algebra.IsSeparable F L := Algebra.IsSeparable.of_equiv_equiv
    (RingEquiv.refl F) (normClosureRingEquiv F).symm (by rfl)
  letI : Algebra k L := ((algebraMap F L).comp (algebraMap k F)).toAlgebra
  haveI : IsScalarTower k F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let xL : L := algebraMap F L x
  have hxL : Transcendental k xL := hx.algHom (IsScalarTower.toAlgHom k F L)
    (algebraMap F L).injective
  letI := ratFuncAlgebraOfTranscendental hxL
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental hxL
  haveI : IsScalarTower (RatFunc k) F L := IsScalarTower.of_algebraMap_eq fun p =>
    (map_algebraMap_ratFuncAlgebraOfTranscendental (IsScalarTower.toAlgHom k F L)
      (algebraMap F L).injective hx p).symm
  haveI : Algebra.IsSeparable (RatFunc k) L := Algebra.IsSeparable.trans (RatFunc k) F L
  have hxLmap : algebraMap (RatFunc k) L RatFunc.X = xL := by
    rw [IsScalarTower.algebraMap_apply (RatFunc k) F L,
      algebraMap_ratFuncAlgebraOfTranscendental_X hx]
  haveI : Algebra.IsSeparable k⟮xL⟯ L := by
    have h := (isSeparable_adjoin_algebraMap_X_iff (k := k) (F := L)).mpr
      (inferInstance : Algebra.IsSeparable (RatFunc k) L)
    rwa [hxLmap] at h
  let dL := derivativeOfSeparating hxL
  let dF := derivativeOfSeparating hx
  let dR := derivativeOfSeparating (RatFunc.transcendental_X (K := k))
  have hxmap : algebraMap (RatFunc k) F RatFunc.X = x :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hx
  have hcomm (r : RatFunc k) : dL (algebraMap (RatFunc k) L r) =
      algebraMap (RatFunc k) L (dR r) := by
    have h := (dL.compAlgebraMap (RatFunc k)).apply_eq_derivativeOfSeparating_smul
      (RatFunc.transcendental_X (K := k)) r
    change dL (algebraMap (RatFunc k) L r) =
      dR r • dL (algebraMap (RatFunc k) L RatFunc.X) at h
    rw [hxLmap] at h
    have hself : dL xL = 1 := derivativeOfSeparating_self hxL
    simpa only [hself, Algebra.smul_def, mul_one] using h
  have hσx (σ : F →ₐ[RatFunc k] L) : σ x = xL := by
    rw [← hxmap, σ.commutes, hxLmap]
  have hσd (σ : F →ₐ[RatFunc k] L) (a : F) : dL (σ a) = σ (dF a) := by
    letI : Algebra F L := σ.toRingHom.toAlgebra
    haveI : IsScalarTower k F L := IsScalarTower.of_algebraMap_eq fun c => by
      change algebraMap k L c = σ (algebraMap k F c)
      rw [IsScalarTower.algebraMap_apply k (RatFunc k) F c, σ.commutes,
        ← IsScalarTower.algebraMap_apply k (RatFunc k) L]
    have h := (dL.compAlgebraMap F).apply_eq_derivativeOfSeparating_smul hx a
    change dL (σ a) = dF a • dL (σ x) at h
    rw [hσx] at h
    have hself : dL xL = 1 := derivativeOfSeparating_self hxL
    have hAF : algebraMap F L = σ.toRingHom := rfl
    have hApp : σ.toRingHom (dF a) = σ (dF a) := rfl
    exact (show dL (σ a) = σ.toRingHom (dF a) from
      by simpa only [hself, Algebra.smul_def, mul_one, hAF] using h).trans hApp
  classical
  have hnorm : algebraMap (RatFunc k) L (Algebra.norm (RatFunc k) z) =
      ∏ σ : F →ₐ[RatFunc k] L, σ z := Algebra.norm_eq_prod_embeddings (RatFunc k) L z
  have htrace : algebraMap (RatFunc k) L (Algebra.trace (RatFunc k) F (dF z / z)) =
      ∑ σ : F →ₐ[RatFunc k] L, σ (dF z / z) := trace_eq_sum_embeddings L
  apply (algebraMap (RatFunc k) L).injective
  rw [htrace, map_div₀, ← hcomm, hnorm,
    log_derivative_prod dL Finset.univ (fun σ : F →ₐ[RatFunc k] L => σ z)
      (fun σ _ => by
        have hApp : σ.toRingHom z = σ z := rfl
        simpa only [map_zero, hApp] using σ.injective.ne hz)]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hσd, map_div₀]

end ZInQ.Contrib.RC53Assist.AbelianCurveInputs.LogarithmicNorm
