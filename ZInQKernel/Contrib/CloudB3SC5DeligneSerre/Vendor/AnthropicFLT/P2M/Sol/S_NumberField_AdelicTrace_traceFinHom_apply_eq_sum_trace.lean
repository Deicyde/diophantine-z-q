/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace (git blob 5466989ebc6c1f7edbbb94c4ffc1c67898db9c53, sha256 c7f3f88bb3e474278abe809b76876b5f5413065de86a4a94707ef190a3104590).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_DedekindDomain_Completion_BaseChange
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace

set_option autoImplicit false

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.NumberField
open _root_.IsDedekindDomain
open _root_.NumberField.StandardAddChar
open scoped TensorProduct

noncomputable section

namespace NumberField
export _root_.NumberField (place RingOfIntegers RingOfIntegers.coe_eq_algebraMap AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles)
namespace AdelicTrace
export _root_.NumberField.AdelicTrace (diag diag_apply traceInt traceInt_diag eq_traceInt)
namespace ComponentFormula
open _root_.NumberField.AdelicTrace
open _root_.NumberField

private theorem trace_pi_apply {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    {S : ι → Type*} [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)] (y : Π i, S i) :
    Algebra.trace R (Π i, S i) y = ∑ i, Algebra.trace R (S i) (y i) := by
  classical
  let b : Π i, Module.Basis (Module.Free.ChooseBasisIndex R (S i)) R (S i) :=
    fun i => Module.Free.chooseBasis R (S i)
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b) y, Matrix.trace]
  simp_rw [Algebra.trace_eq_matrix_trace (b _), Matrix.trace, Matrix.diag_apply,
    Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Pi.mul_apply, Pi.single_eq_same]

section fieldLevel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))



private def piEquiv [Module.Finite (𝓞 K) (𝓞 L)] :
    (HeightOneSpectrum.adicCompletion K v) ⊗[K] L ≃ₐ[(HeightOneSpectrum.adicCompletion K v)] Π w : v.Extension (𝓞 L), w.1.adicCompletion L :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm K (HeightOneSpectrum.adicCompletion K v) L).toRingEquiv.trans
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toRingEquiv)
    (fun s => by
      funext w
      change HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v
          (Algebra.TensorProduct.comm K (HeightOneSpectrum.adicCompletion K v) L ((algebraMap (HeightOneSpectrum.adicCompletion K v) (HeightOneSpectrum.adicCompletion K v) s) ⊗ₜ[K] (1 : L))) w = _
      rw [Algebra.TensorProduct.comm_tmul, HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one,
        one_mul, Pi.algebraMap_apply]
      rfl)

private theorem piEquiv_one_tmul [Module.Finite (𝓞 K) (𝓞 L)] (a : L) (w : v.Extension (𝓞 L)) :
    piEquiv K L v ((1 : (HeightOneSpectrum.adicCompletion K v)) ⊗ₜ[K] a) w = algebraMap L (w.1.adicCompletion L) a := by
  change HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v
      (Algebra.TensorProduct.comm K (HeightOneSpectrum.adicCompletion K v) L ((1 : (HeightOneSpectrum.adicCompletion K v)) ⊗ₜ[K] a)) w = _
  rw [Algebra.TensorProduct.comm_tmul, HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, mul_one]

private theorem trace_one_tmul (a : L) :
    Algebra.trace (HeightOneSpectrum.adicCompletion K v) ((HeightOneSpectrum.adicCompletion K v) ⊗[K] L) ((1 : (HeightOneSpectrum.adicCompletion K v)) ⊗ₜ[K] a) = algebraMap K (HeightOneSpectrum.adicCompletion K v) (Algebra.trace K L a) := by
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

private theorem localGlobal (a : L) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
    algebraMap K (HeightOneSpectrum.adicCompletion K v) (Algebra.trace K L a)
      = ∑ w : v.Extension (𝓞 L), Algebra.trace (HeightOneSpectrum.adicCompletion K v) (w.1.adicCompletion L) (algebraMap L (w.1.adicCompletion L) a) := by
  letI := HeightOneSpectrum.Extension.fintype (𝓞 K) K L (𝓞 L) v
  haveI : Module.Finite (𝓞 K) (𝓞 L) :=
    have := IsIntegralClosure.isNoetherian (𝓞 K) K L (𝓞 L)
    Module.IsNoetherian.finite (𝓞 K) (𝓞 L)
  haveI : ∀ w : v.Extension (𝓞 L), Module.Free (HeightOneSpectrum.adicCompletion K v) (w.1.adicCompletion L) :=
    fun w => Module.Free.of_divisionRing _ _
  have h1 := Algebra.trace_eq_of_algEquiv (piEquiv K L v) ((1 : (HeightOneSpectrum.adicCompletion K v)) ⊗ₜ[K] a)
  rw [trace_one_tmul, trace_pi_apply] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [piEquiv_one_tmul]

end fieldLevel

section integerLevel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))






private theorem algebraMap_integers_injective : Function.Injective (algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w))) := by
  intro x y h
  apply Subtype.val_injective
  have h' := congrArg (fun z : (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w)) => (z : (HeightOneSpectrum.adicCompletion L (Subtype.val w)))) h
  change (w.adicCompletionSemialgHom K L) x.val = (w.adicCompletionSemialgHom K L) y.val at h'
  exact (w.adicCompletionSemialgHom K L).toRingHom.injective h'

private scoped instance faithfulSMul_integers : FaithfulSMul (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w)) :=
  (faithfulSMul_iff_algebraMap_injective (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w))).mpr (algebraMap_integers_injective K L v w)

private scoped instance isScalarTower_integers : IsScalarTower (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w)) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) :=
  .of_algebraMap_smul fun _ _ => rfl

private scoped instance free_integers [Module.Finite (𝓞 K) (𝓞 L)] : Module.Free (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w)) :=
  Module.free_of_finite_type_torsion_free'

private scoped instance isIntegralClosure_integers [Module.Finite (𝓞 K) (𝓞 L)] : IsIntegralClosure (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w)) (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) where
  algebraMap_injective := IsFractionRing.injective (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w)) (HeightOneSpectrum.adicCompletion L (Subtype.val w))
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      exact IsIntegrallyClosed.isIntegral_iff.mp hx.tower_top
    · rintro ⟨y, rfl⟩
      exact (Algebra.IsIntegral.isIntegral (R := (HeightOneSpectrum.adicCompletionIntegers K v)) y).algebraMap

private theorem trace_coe_integer [Module.Finite (𝓞 K) (𝓞 L)] (y : (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w))) :
    Algebra.trace (HeightOneSpectrum.adicCompletion K v) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) (y : (HeightOneSpectrum.adicCompletion L (Subtype.val w))) = algebraMap (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) (Algebra.trace (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w)) y) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w)) (nonZeroDivisors (HeightOneSpectrum.adicCompletionIntegers K v))) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) :=
    IsIntegralClosure.isLocalization (HeightOneSpectrum.adicCompletionIntegers K v) (HeightOneSpectrum.adicCompletion K v) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) (HeightOneSpectrum.adicCompletionIntegers L (Subtype.val w))
  exact Algebra.trace_localization (HeightOneSpectrum.adicCompletionIntegers K v) (nonZeroDivisors (HeightOneSpectrum.adicCompletionIntegers K v)) (Rₘ := (HeightOneSpectrum.adicCompletion K v)) (Sₘ := (HeightOneSpectrum.adicCompletion L (Subtype.val w))) y

end integerLevel

section placewise

variable (K : Type) [Field K] [NumberField K]

private def placewiseTrace :
    (Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K)
      →+ (Π p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ) where
  toFun y p :=
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    ∑ w : p.Extension (𝓞 K),
      Algebra.trace (p.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers K) (y w.1)
  map_zero' := by
    funext p
    simp only [Pi.zero_apply, map_zero, Finset.sum_const_zero]
  map_add' y z := by
    funext p
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]

private theorem placewiseTrace_apply_coe (y : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    ((placewiseTrace K y p : p.adicCompletionIntegers ℚ) : p.adicCompletion ℚ)
      = ∑ w : p.Extension (𝓞 K),
          Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) ((y w.1 : w.1.adicCompletion K)) := by
  letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) :=
    have := IsIntegralClosure.isNoetherian (𝓞 ℚ) ℚ K (𝓞 K)
    Module.IsNoetherian.finite (𝓞 ℚ) (𝓞 K)
  change ((algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ))
      (∑ w : p.Extension (𝓞 K),
        Algebra.trace (p.adicCompletionIntegers ℚ) (w.1.adicCompletionIntegers K) (y w.1))) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← trace_coe_integer ℚ K p w (y w.1)]

private theorem continuous_placewiseTrace : Continuous (placewiseTrace K) := by
  haveI : Module.Finite (𝓞 ℚ) (𝓞 K) :=
    have := IsIntegralClosure.isNoetherian (𝓞 ℚ) ℚ K (𝓞 K)
    Module.IsNoetherian.finite (𝓞 ℚ) (𝓞 K)
  apply continuous_pi
  intro p
  letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
  rw [continuous_induced_rng]
  have hfun : (Subtype.val ∘ fun y : (Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K) =>
        placewiseTrace K y p)
      = fun y => ∑ w : p.Extension (𝓞 K),
          Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) ((y w.1 : w.1.adicCompletion K)) :=
    funext fun y => placewiseTrace_apply_coe K y p
  rw [hfun]
  refine continuous_finsetSum _ fun w _ => ?_
  have hc : Continuous fun y : (Π u : HeightOneSpectrum (𝓞 K), u.adicCompletionIntegers K) =>
      ((y w.1 : w.1.adicCompletion K)) :=
    continuous_subtype_val.comp (continuous_apply w.1)
  exact (IsModuleTopology.continuous_of_linearMap
    (Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K))).comp hc

private theorem placewiseTrace_diag (a : 𝓞 K) :
    placewiseTrace K (diag K a) = traceInt K (diag K a) := by
  funext p
  letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
  apply Subtype.val_injective
  rw [placewiseTrace_apply_coe, traceInt_diag]

  have hl : ∀ w : p.Extension (𝓞 K),
      ((diag K a w.1 : w.1.adicCompletionIntegers K) : w.1.adicCompletion K)
        = algebraMap K (w.1.adicCompletion K) (a : K) := fun w => by
    rw [diag_apply]
    rfl
  simp_rw [hl]
  rw [← localGlobal ℚ K p (a : K)]

  have hr : (((algebraMap ℤ (𝓞 ℚ) (Algebra.trace ℤ (𝓞 K) a) : 𝓞 ℚ) : ℚ)) = Algebra.trace ℚ K (a : K) := by
    rw [← Algebra.coe_trace_int, eq_intCast, RingOfIntegers.coe_eq_algebraMap, map_intCast]
  change _ = algebraMap ℚ (p.adicCompletion ℚ) (((algebraMap ℤ (𝓞 ℚ) (Algebra.trace ℤ (𝓞 K) a) : 𝓞 ℚ) : ℚ))
  rw [hr]

private theorem placewiseTrace_eq_traceInt : placewiseTrace K = traceInt K :=
  eq_traceInt K (continuous_placewiseTrace K) (placewiseTrace_diag K)

end placewise

section assembly

variable (K : Type) [Field K] [NumberField K]

private def sm (z : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K) : FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
    (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite z

private theorem sm_apply (z : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K)
    (w : HeightOneSpectrum (𝓞 K)) : sm K z w = (z w : w.adicCompletion K) := rfl

private theorem traceFinHom_sm (z : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K) :
    traceFinHom K (sm K z) = sm ℚ (traceInt K z) :=
  traceFinHom_structureMap K z

private theorem sub_apply' (a b : FiniteAdeleRing (𝓞 K) K) (w : HeightOneSpectrum (𝓞 K)) :
    (a - b) w = a w - b w := rfl

private theorem algebraMap_apply' (q : ℚ) (p : HeightOneSpectrum (𝓞 ℚ)) :
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q) p = algebraMap ℚ (p.adicCompletion ℚ) q := rfl

private theorem algebraMap_apply'' (k : K) (w : HeightOneSpectrum (𝓞 K)) :
    (algebraMap K (FiniteAdeleRing (𝓞 K) K) k) w = algebraMap K (w.adicCompletion K) k := rfl

private theorem main (x : FiniteAdeleRing (𝓞 K) K) (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    (traceFinHom K x) p
      = ∑ w : p.Extension (𝓞 K), Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) (x w.1) := by
  letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
  obtain ⟨k, hk⟩ := NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 K) K x
  let y : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K :=
    fun w => ⟨(algebraMap K (FiniteAdeleRing (𝓞 K) K) k + x) w, hk w⟩
  have hy : sm K y = algebraMap K (FiniteAdeleRing (𝓞 K) K) k + x :=
    RestrictedProduct.ext _ _ fun w => rfl
  have hx : x = sm K y - algebraMap K (FiniteAdeleRing (𝓞 K) K) k := by
    rw [hy, add_sub_cancel_left]
  rw [hx, map_sub, traceFinHom_sm, traceFinHom_algebraMap, sub_apply' ℚ, sm_apply, algebraMap_apply',
    ← placewiseTrace_eq_traceInt, placewiseTrace_apply_coe, localGlobal ℚ K p k, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← map_sub, sub_apply' K, sm_apply, algebraMap_apply'']

end assembly

end NumberField.AdelicTrace.ComponentFormula
open scoped _root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.NumberField _root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.NumberField.AdelicTrace _root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.NumberField.AdelicTrace.ComponentFormula
open scoped _root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.NumberField _root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.NumberField.AdelicTrace
open scoped _root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.NumberField

end
open scoped _root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.NumberField _root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.NumberField.AdelicTrace _root_.P2MW.S_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace.NumberField.AdelicTrace.ComponentFormula

theorem solution
    (K : Type) [Field K] [NumberField K]
    (x : FiniteAdeleRing (𝓞 K) K)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ K (𝓞 K) p
    (traceFinHom K x) p
      = ∑ w : p.Extension (𝓞 K),
          Algebra.trace (p.adicCompletion ℚ) (w.1.adicCompletion K) (x w.1) :=
  NumberField.AdelicTrace.ComponentFormula.main K x p
