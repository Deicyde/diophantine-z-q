/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace (git blob dd0dc93f57aac84ef9fe956dd69a0a382ecc65fd, sha256 ba41113b73b455393a1cdcff37ecea9f8c3f6f7e8807907297c2071d1942ce58).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_DedekindDomain_Completion_BaseChange
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_AdelicTrace_traceFinHom_apply_eq_sum_trace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace

set_option autoImplicit false

open _root_.NumberField
namespace NumberField
end NumberField
open _root_.P2MW.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace.NumberField
open _root_.IsDedekindDomain
open _root_.NumberField.StandardAddChar
namespace NumberField.StandardAddChar
end NumberField.StandardAddChar
open _root_.P2MW.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace.NumberField.StandardAddChar

noncomputable section

namespace NumberField
export _root_.NumberField (InfiniteAdeleRing place AdelicTrace.traceFinHom_apply_eq_sum_trace)
namespace StandardAddChar
export _root_.NumberField.StandardAddChar (finAdeleSingleAt finAdeleSingleAt_apply_self finAdeleSingleAt_apply_of_ne psiLocal psiLocal_apply traceFinHom adelicTraceData traceInfHom AdelicTraceData AdelicTraceData.adelicTrace_apply psiV psiFin psiFin_apply psiArch psiQ psiQ_apply)
namespace LocalTraceCompat
open _root_.NumberField.StandardAddChar
open _root_.NumberField

section oneField

variable (L : Type) [Field L] [NumberField L]

private theorem psiLocal_eq_psiFin (u : HeightOneSpectrum (𝓞 L)) (x : u.adicCompletion L) :
    psiLocal L u x = psiFin (traceFinHom L (finAdeleSingleAt L u x)) := by
  rw [psiLocal_apply]
  change psiQ ((adelicTraceData L).adelicTrace ((0 : InfiniteAdeleRing L), finAdeleSingleAt L u x)) = _
  rw [AdelicTraceData.adelicTrace_apply, psiQ_apply]
  change psiArch (traceInfHom L 0) * psiFin (traceFinHom L (finAdeleSingleAt L u x)) = _
  rw [map_zero, AddChar.map_zero_eq_one, one_mul]

private theorem psiLocal_eq_psiV_trace (p : HeightOneSpectrum (𝓞 ℚ)) (u : p.Extension (𝓞 L))
    (x : u.1.adicCompletion L) :
    psiLocal L u.1 x = psiV p (Algebra.trace (p.adicCompletion ℚ) (u.1.adicCompletion L) x) := by
  rw [psiLocal_eq_psiFin, psiFin_apply]
  rw [finprod_eq_single _ p (fun q hq => ?_)]
  · congr 1
    rw [NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace L (finAdeleSingleAt L u.1 x) p]
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ L (𝓞 L) p
    rw [Finset.sum_eq_single u]
    · rw [finAdeleSingleAt_apply_self]
    · intro w _ hw
      rw [finAdeleSingleAt_apply_of_ne L u.1 _ (fun h => hw (Subtype.ext h)), map_zero]
    · intro h
      exact absurd (Finset.mem_univ u) h
  · rw [NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace L (finAdeleSingleAt L u.1 x) q]
    letI := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ L (𝓞 L) q
    rw [Finset.sum_eq_zero (fun w _ => ?_), AddChar.map_zero_eq_one]
    have hne : w.1 ≠ u.1 := fun h => hq (by rw [← w.2, ← u.2, h])
    rw [finAdeleSingleAt_apply_of_ne L u.1 _ hne, map_zero]

end oneField

section tower

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

private theorem ringHom_ratInt_ext {R : Type*} [Ring R] (f g : 𝓞 ℚ →+* R) : f = g := by
  refine RingHom.ext fun x => ?_
  have hx : x = ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) := by
    have h := (eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom (Rat.ringOfIntegersEquiv x)).symm
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply] at h
    exact h.symm
  rw [hx, map_intCast, map_intCast]

private theorem under_rat_eq : w.1.under (𝓞 ℚ) = v.under (𝓞 ℚ) := by
  apply HeightOneSpectrum.ext
  have hv : v.asIdeal = Ideal.under (𝓞 K) w.1.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (congrArg HeightOneSpectrum.asIdeal w.2).symm
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, hv,
    Ideal.under_def, Ideal.under_def, Ideal.under_def, Ideal.comap_comap,
    ringHom_ratInt_ext ((algebraMap (𝓞 K) (𝓞 L)).comp (algebraMap (𝓞 ℚ) (𝓞 K))) (algebraMap (𝓞 ℚ) (𝓞 L))]

private def pQ : HeightOneSpectrum (𝓞 ℚ) := v.under (𝓞 ℚ)

private def vp : (pQ K v).Extension (𝓞 K) := ⟨v, rfl⟩

private def wp : (pQ K v).Extension (𝓞 L) := ⟨w.1, under_rat_eq K L v w⟩





@[reducible] private def algQK : Algebra (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) (HeightOneSpectrum.adicCompletion K v) := inferInstanceAs (Algebra (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) ((vp K v).1.adicCompletion K))
@[reducible] private def algQL : Algebra (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) := inferInstanceAs (Algebra (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) ((wp K L v w).1.adicCompletion L))

attribute [local instance] algQK algQL

private theorem finiteDimensional_QK : FiniteDimensional (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) (HeightOneSpectrum.adicCompletion K v) :=
  inferInstanceAs (FiniteDimensional (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) ((vp K v).1.adicCompletion K))
private theorem finiteDimensional_QL : FiniteDimensional (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) :=
  inferInstanceAs (FiniteDimensional (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) ((wp K L v w).1.adicCompletion L))

attribute [local instance] finiteDimensional_QK finiteDimensional_QL

private theorem tower_apply (y : (HeightOneSpectrum.adicCompletion ℚ (pQ K v))) :
    algebraMap (HeightOneSpectrum.adicCompletion K v) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) (algebraMap (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) (HeightOneSpectrum.adicCompletion K v) y) = algebraMap (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) y := by
  have hKL : Continuous (algebraMap (HeightOneSpectrum.adicCompletion K v) (HeightOneSpectrum.adicCompletion L (Subtype.val w))) :=
    HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K L w
  have hQK : Continuous (algebraMap (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) (HeightOneSpectrum.adicCompletion K v)) :=
    HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous ℚ K (vp K v)
  have hQL : Continuous (algebraMap (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) (HeightOneSpectrum.adicCompletion L (Subtype.val w))) :=
    HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous ℚ L (wp K L v w)
  refine DenseRange.induction_on (HeightOneSpectrum.denseRange_algebraMap ℚ (pQ K v)) y
    (isClosed_eq (hKL.comp hQK) hQL) (fun q => ?_)
  change (w.adicCompletionSemialgHom K L) (((vp K v).adicCompletionSemialgHom ℚ K) (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) q))
    = ((wp K L v w).adicCompletionSemialgHom ℚ L) (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) q)
  have h1 : ((vp K v).adicCompletionSemialgHom ℚ K) (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) q) = algebraMap K (HeightOneSpectrum.adicCompletion K v) (algebraMap ℚ K q) :=
    SemialgHom.commutes _ _
  have h2 : (w.adicCompletionSemialgHom K L) (algebraMap K (HeightOneSpectrum.adicCompletion K v) (algebraMap ℚ K q))
      = algebraMap L (HeightOneSpectrum.adicCompletion L (Subtype.val w)) (algebraMap K L (algebraMap ℚ K q)) :=
    SemialgHom.commutes _ _
  have h3 : ((wp K L v w).adicCompletionSemialgHom ℚ L) (algebraMap ℚ (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) q) = algebraMap L (HeightOneSpectrum.adicCompletion L (Subtype.val w)) (algebraMap ℚ L q) :=
    SemialgHom.commutes _ _
  rw [h1, h2, h3, eq_ratCast (algebraMap ℚ K) q, eq_ratCast (algebraMap ℚ L) q, map_ratCast]

private theorem isScalarTower_QKL : IsScalarTower (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) (HeightOneSpectrum.adicCompletion K v) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) :=
  IsScalarTower.of_algebraMap_eq fun y => (tower_apply K L v w y).symm

attribute [local instance] isScalarTower_QKL

private theorem trace_tower (x : (HeightOneSpectrum.adicCompletion L (Subtype.val w))) :
    Algebra.trace (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) (HeightOneSpectrum.adicCompletion K v) (Algebra.trace (HeightOneSpectrum.adicCompletion K v) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) x) = Algebra.trace (HeightOneSpectrum.adicCompletion ℚ (pQ K v)) (HeightOneSpectrum.adicCompletion L (Subtype.val w)) x :=
  Algebra.trace_trace x

end tower

private theorem main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) (x : w.1.adicCompletion L) :
    psiLocal L w.1 x
      = psiLocal K v (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x) := by
  have hL := psiLocal_eq_psiV_trace L (pQ K v) (wp K L v w) x
  have hK := psiLocal_eq_psiV_trace K (pQ K v) (vp K v)
    (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x)
  have ht := trace_tower K L v w x
  change psiLocal L w.1 x = _ at hL
  change psiLocal K v _ = _ at hK
  rw [hL, hK]
  exact congrArg (psiV (pQ K v)) ht.symm

end NumberField.StandardAddChar.LocalTraceCompat

end

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L))
    (x : w.1.adicCompletion L) :
    psiLocal L w.1 x
      = psiLocal K v (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x) :=
  NumberField.StandardAddChar.LocalTraceCompat.main K L v w x
