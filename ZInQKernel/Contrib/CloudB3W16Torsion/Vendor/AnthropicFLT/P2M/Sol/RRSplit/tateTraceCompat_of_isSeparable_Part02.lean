/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean; source lines 2341-4418.
Includes FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean material:
Copyright (c) 2025 Salvatore Mercuri. Authors: Salvatore Mercuri, Kevin Buzzard.
Includes FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean material:
Copyright (c) 2025 Ruben Van de Velde.
Authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri.
Modification notice (CloudB3 Worker16 curve support, 2026-11-16):
Factored at balanced source section boundaries. Relocated imports with the canonical main-port reuse map; expanded P2M
namespace/open/export command helpers to ordinary Lean commands, removed metadata
reactivation commands, and resolved metadata aliases directly. Expanded local notation
literally. Promoted source-private helpers into the original P2MW module namespace
so proofs can cross factoring-file boundaries without new root-name collisions.
Kept mathematical proof bodies and all public solution signatures; no new mathematical
assumptions. Lean 4.35 compatibility edits are recorded in the accompanying manifest.
Complete original LICENSE, NOTICE, and attribution are in this vendor root; a local
copy is supplied in RRSplit for independent distribution of this support patch.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.tateTraceCompat_of_isSeparable_Part01
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.LinearConjugation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable

-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_nonneg_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.ord_nonneg_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.mem_of_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.mem_iff_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.comap_algebraMap_ne_top :=
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.comap_algebraMap_ne_top
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_ord_algebraMap_pos :=
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.exists_ord_algebraMap_pos
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizerSubring :=
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.uniformizerSubring
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.uniformizer_mem :=
  @_root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place.uniformizer_mem


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section Composite

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem kwF4gRRTate_poleWindowFinite : KwF4gRRTatePoleWindowFinite K L :=
  kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite
    (kwF4gRRTate_DVRQuotPowKFinite_of_cotangent
      kwF4gRRTate_DVRCotangentKFinite)

end Composite


section Subset

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem lmul_adicIntegers_subset_poleWindow (fh : u.adicCompletion)
    (πh : u.adicCompletionIntegers) (M : ℕ)
    (hfhM : (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers) :
    Submodule.map (lmulK u fh) (adicIntegersKSubmod u) ≤ poleWindowKSubmod u πh M := by
  rintro x ⟨a, ha, rfl⟩

  rw [mem_poleWindowKSubmod_iff]
  show (πh : u.adicCompletion)^M * (lmulK u fh) a ∈ u.adicCompletionIntegers
  have : (lmulK u fh) a = fh * a := rfl
  rw [this, ← mul_assoc]
  exact mul_mem hfhM (show a ∈ u.adicCompletionIntegers from ha)

end Subset


section Discharge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

theorem kwF4gRRTate_poleWindowImageFinite :
    KwF4gRRTatePoleWindowImageFinite u := by
  intro fh
  obtain ⟨πh, hπh⟩ := IsDiscreteValuationRing.exists_irreducible u.adicCompletionIntegers
  obtain ⟨M, hfhM⟩ := kwF4gRRTate_clearPole u πh hπh fh

  set A := adicIntegersKSubmod u
  set P := poleWindowKSubmod u πh M
  have hsub : Submodule.map A.mkQ (Submodule.map (lmulK u fh) A)
      ≤ Submodule.map A.mkQ P :=
    Submodule.map_mono (lmul_adicIntegers_subset_poleWindow u fh πh M hfhM)

  suffices hPim : FiniteDimensional K (Submodule.map A.mkQ P : Submodule K _) by
    exact Submodule.finiteDimensional_of_le hsub

  haveI : FiniteDimensional K (P ⧸ (A.comap P.subtype)) :=
    kwF4gRRTate_poleWindowFinite (K := K) (L := L) u πh hπh M
  let r : P →ₗ[K] (u.adicCompletion ⧸ A) := A.mkQ ∘ₗ P.subtype
  have hrange : LinearMap.range r = Submodule.map A.mkQ P := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker r = A.comap P.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have e : (P ⧸ (A.comap P.subtype)) ≃ₗ[K] LinearMap.range r := hker ▸ r.quotKerEquivRange
  rw [← hrange]
  exact e.finiteDimensional

end Discharge


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section KerInf

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (pA' : u.adicCompletion →ₗ[K] u.adicCompletion)

theorem ker_pA'_inf_integers (h : SameRangeIdemProjectors (tateProj u) pA') :
    LinearMap.ker pA' ⊓ adicIntegersKSubmod u = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hker, hint⟩ := Submodule.mem_inf.mp hx
  have h0 : pA' x = 0 := LinearMap.mem_ker.mp hker

  have hxR : x ∈ LinearMap.range (tateProj u) := by rw [range_tateProj u]; exact hint

  have hpAx : pA' x = x := pA'_fixes_range h x hxR
  rw [Submodule.mem_bot, ← hpAx, h0]

theorem finiteDimensional_ker_pA'_inf_poleWindow
    (h : SameRangeIdemProjectors (tateProj u) pA')
    [u.FiniteResidue] (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K
      ((LinearMap.ker pA' ⊓ poleWindowKSubmod u πh M : Submodule K _)) := by
  haveI := kwF4gRRTate_poleWindowFinite (K := K) (L := L) u πh hπh M
  set A := adicIntegersKSubmod u
  set P := poleWindowKSubmod u πh M
  let A' : Submodule K P := A.comap P.subtype
  let ι : (LinearMap.ker pA' ⊓ P : Submodule K _) →ₗ[K] P ⧸ A' :=
    (A'.mkQ).comp (Submodule.inclusion inf_le_right)
  refine FiniteDimensional.of_injective ι ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro xh hxker
  obtain ⟨x, hxkp⟩ := xh
  obtain ⟨hxk, hxp⟩ := Submodule.mem_inf.mp hxkp
  simp only [ι, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.inclusion_apply] at hxker
  have hxA : x ∈ A := hxker
  have hx0 : x = 0 := by
    have hbot : x ∈ (⊥ : Submodule K u.adicCompletion) := by
      rw [← ker_pA'_inf_integers u pA' h]; exact Submodule.mem_inf.mpr ⟨hxk, hxA⟩
    exact (Submodule.mem_bot K).mp hbot
  exact Subtype.ext hx0

end KerInf


section Discharge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (pA' : u.adicCompletion →ₗ[K] u.adicCompletion)
variable [∀ u : Place K L, u.FiniteResidue]

theorem finiteDimensional_principalPart_pA'_range
    (h : SameRangeIdemProjectors (tateProj u) pA') (fh : u.adicCompletion) :
    FiniteDimensional K
      (LinearMap.range
        ((LinearMap.id - pA') ∘ₗ lmulK u fh ∘ₗ (adicIntegersKSubmod u).subtype)) := by
  obtain ⟨πh, hπh⟩ := IsDiscreteValuationRing.exists_irreducible u.adicCompletionIntegers
  obtain ⟨M, hfhM⟩ := kwF4gRRTate_clearPole u πh hπh fh
  haveI := finiteDimensional_ker_pA'_inf_poleWindow u pA' h πh hπh M
  apply Submodule.finiteDimensional_of_le
    (S₂ := LinearMap.ker pA' ⊓ poleWindowKSubmod u πh M)
  rintro x ⟨a, rfl⟩
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  ·
    rw [LinearMap.mem_ker]
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Submodule.subtype_apply, map_sub]
    exact sub_eq_zero.mpr (h.idem_pA' _).symm
  ·
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Submodule.subtype_apply]
    refine sub_mem ?_ ?_
    · exact lmul_adicIntegers_subset_poleWindow u fh πh M hfhM ⟨a, a.2, rfl⟩
    · refine adicIntegersKSubmod_le_poleWindowKSubmod u πh M ?_
      have heq : LinearMap.range pA' = adicIntegersKSubmod u := by
        rw [← h.range_eq, range_tateProj u]
      exact heq.le (LinearMap.mem_range_self pA' _)

theorem kwF4gRRTate_commFiniteGen :
    KwF4gRRTateCommFiniteGen u pA' := by
  intro h fh gh

  haveI h3f := finiteDimensional_principalPart_pA'_range u pA' h fh
  haveI h3g := finiteDimensional_principalPart_pA'_range u pA' h gh
  set qf := (LinearMap.id - pA') ∘ₗ lmulK u fh ∘ₗ (adicIntegersKSubmod u).subtype
  set qg := (LinearMap.id - pA') ∘ₗ lmulK u gh ∘ₗ (adicIntegersKSubmod u).subtype
  set Wf := LinearMap.range qf
  set Wg := LinearMap.range qg

  set S₂ : Submodule K u.adicCompletion :=
    Submodule.map (pA' ∘ₗ lmulK u gh) Wf ⊔ Submodule.map (pA' ∘ₗ lmulK u fh) Wg with hS₂
  haveI : FiniteDimensional K S₂ := by
    haveI : FiniteDimensional K (Submodule.map (pA' ∘ₗ lmulK u gh) Wf : Submodule K _) :=
      inferInstance
    haveI : FiniteDimensional K (Submodule.map (pA' ∘ₗ lmulK u fh) Wg : Submodule K _) :=
      inferInstance
    exact Submodule.finiteDimensional_sup _ _

  set R := LinearMap.range (tateCommRestrict pA' (lmulK u fh) (lmulK u gh))
  suffices himg : Submodule.map (LinearMap.range pA').subtype R ≤ S₂ by
    haveI : FiniteDimensional K (Submodule.map (LinearMap.range pA').subtype R) :=
      Submodule.finiteDimensional_of_le himg
    exact (Submodule.equivMapOfInjective (LinearMap.range pA').subtype
        (LinearMap.range pA').injective_subtype R).symm.finiteDimensional

  rintro x ⟨y, hyR, rfl⟩
  obtain ⟨a, rfl⟩ := hyR

  have heq : LinearMap.range pA' = adicIntegersKSubmod u := by
    rw [← h.range_eq, range_tateProj u]
  have haO : (a : u.adicCompletion) ∈ adicIntegersKSubmod u := heq.le a.2
  set aO : adicIntegersKSubmod u := ⟨(a : u.adicCompletion), haO⟩
  have hcomm : lmulK u fh ∘ₗ lmulK u gh = lmulK u gh ∘ₗ lmulK u fh := by
    refine LinearMap.ext fun y' => ?_; show fh * (gh * y') = gh * (fh * y'); ring

  show (tateCommRestrict pA' (lmulK u fh) (lmulK u gh) a : u.adicCompletion) ∈ S₂
  rw [show (tateCommRestrict pA' (lmulK u fh) (lmulK u gh) a : u.adicCompletion)
      = tateComm pA' (lmulK u fh) (lmulK u gh) (a : u.adicCompletion) from rfl,
    tateComm_eq_of_commute hcomm]

  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact ⟨qf aO, ⟨aO, rfl⟩, rfl⟩
  · exact ⟨qg aO, ⟨aO, rfl⟩, rfl⟩

end Discharge


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finrankTrace_congr {φ ψ : V →ₗ[K] V}
    [hφ : FiniteDimensional K (LinearMap.range φ)]
    [hψ : FiniteDimensional K (LinearMap.range ψ)]
    (h : φ = ψ) : finrankTrace φ = finrankTrace ψ := by
  subst h; rfl

theorem range_sub_le (φ ψ : V →ₗ[K] V) :
    LinearMap.range (φ - ψ) ≤ LinearMap.range φ ⊔ LinearMap.range ψ := by
  rintro x ⟨y, rfl⟩
  exact sub_mem (Submodule.mem_sup_left (mem_range_self φ y))
    (Submodule.mem_sup_right (mem_range_self ψ y))

scoped instance instFinDimRangeSub (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (φ - ψ)) :=
  haveI : FiniteDimensional K
      ((LinearMap.range φ ⊔ LinearMap.range ψ : Submodule K V) : Type _) :=
    Submodule.finiteDimensional_sup _ _
  Submodule.finiteDimensional_of_le (range_sub_le φ ψ)

theorem finrankTrace_sub (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    finrankTrace φ - finrankTrace ψ = finrankTrace (φ - ψ) := by
  set W' : Submodule K V := LinearMap.range φ ⊔ LinearMap.range ψ
  haveI : FiniteDimensional K W' := Submodule.finiteDimensional_sup _ _
  have hφψW : ∀ x ∈ W', (φ - ψ) x ∈ W' := fun x _ =>
    sub_mem (Submodule.mem_sup_left (mem_range_self φ x))
      (Submodule.mem_sup_right (mem_range_self ψ x))
  rw [finrankTrace_sub_eq φ ψ,
    finrankTrace_eq_trace_on_superspace (φ - ψ) W' (range_sub_le φ ψ) hφψW]

end Additivity


section ConjInvariance

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
variable [AddCommGroup N] [Module K N]

theorem range_conj_eq_map (e : M ≃ₗ[K] N) (φ : M →ₗ[K] M) :
    LinearMap.range (e.conj φ) = (LinearMap.range φ).map (e : M →ₗ[K] N) := by
  rw [LinearEquiv.conj_apply, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearMap.range_comp]

theorem finrankTrace_conj (e : M ≃ₗ[K] N) (φ : M →ₗ[K] M)
    [hφ : FiniteDimensional K (LinearMap.range φ)] :
    haveI : FiniteDimensional K (LinearMap.range (e.conj φ)) := by
      rw [range_conj_eq_map]
      exact (Submodule.equivMapOfInjective _ e.injective _).finiteDimensional
    finrankTrace (e.conj φ) = finrankTrace φ := by

  have hgf : ((e : M →ₗ[K] N) ∘ₗ φ) ∘ₗ (e.symm : N →ₗ[K] M) = e.conj φ := by
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.conj_apply]
  have hfg : (e.symm : N →ₗ[K] M) ∘ₗ ((e : M →ₗ[K] N) ∘ₗ φ) = φ := by
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  haveI : FiniteDimensional K
      (LinearMap.range (((e : M →ₗ[K] N) ∘ₗ φ) ∘ₗ (e.symm : N →ₗ[K] M))) := by
    rw [hgf, range_conj_eq_map]
    exact (Submodule.equivMapOfInjective _ e.injective _).finiteDimensional
  haveI : FiniteDimensional K
      (LinearMap.range ((e.symm : N →ₗ[K] M) ∘ₗ ((e : M →ₗ[K] N) ∘ₗ φ))) := by
    rw [hfg]; exact hφ
  have hcyc := finrankTrace_comp_comm (e.symm : N →ₗ[K] M) ((e : M →ₗ[K] N) ∘ₗ φ)

  haveI hconj : FiniteDimensional K (LinearMap.range (e.conj φ)) := by
    rw [range_conj_eq_map]
    exact (Submodule.equivMapOfInjective _ e.injective _).finiteDimensional
  exact (finrankTrace_congr hgf.symm).trans (hcyc.trans (finrankTrace_congr hfg))

end ConjInvariance


section TermMaps

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

def alphaMap (c : u.adicCompletion) :
    LinearMap.range (tateProj u) →ₗ[K] (u.adicCompletion ⧸ LinearMap.range (tateProj u)) :=
  (LinearMap.range (tateProj u)).mkQ ∘ₗ lmulK u c ∘ₗ (LinearMap.range (tateProj u)).subtype

theorem alphaMap_apply (c : u.adicCompletion) (a : LinearMap.range (tateProj u)) :
    alphaMap u c a = Submodule.Quotient.mk (c * (a : u.adicCompletion)) := rfl

def mulOnRange {gh : u.adicCompletion} (hgh : gh ∈ u.adicCompletionIntegers) :
    LinearMap.range (tateProj u) →ₗ[K] LinearMap.range (tateProj u) :=
  (lmulK u gh).restrict (fun x hx => by
    have hxO : x ∈ u.adicCompletionIntegers :=
      (range_tateProj u ▸ hx : x ∈ adicIntegersKSubmod u)
    have hghx : gh * x ∈ u.adicCompletionIntegers := mul_mem hgh hxO
    rw [range_tateProj u]
    exact (show gh * x ∈ adicIntegersKSubmod u from hghx))

theorem mulOnRange_apply {gh : u.adicCompletion} (hgh : gh ∈ u.adicCompletionIntegers)
    (a : LinearMap.range (tateProj u)) :
    (mulOnRange u hgh a : u.adicCompletion) = gh * (a : u.adicCompletion) := rfl

variable [u.FiniteResidue]

theorem finiteDimensional_range_alphaMap (c : u.adicCompletion) :
    FiniteDimensional K (LinearMap.range (alphaMap u c)) := by

  haveI hF21 := kwF4gRRTate_poleWindowImageFinite u c
  set Q1 := u.adicCompletion ⧸ LinearMap.range (tateProj u)
  set Q2 := u.adicCompletion ⧸ adicIntegersKSubmod u
  let eQ : Q1 ≃ₗ[K] Q2 := Submodule.quotEquivOfEq _ _ (range_tateProj u)

  have hmap : (LinearMap.range (alphaMap u c)).map (eQ : Q1 →ₗ[K] Q2)
      = Submodule.map (adicIntegersKSubmod u).mkQ
          (Submodule.map (lmulK u c) (adicIntegersKSubmod u)) := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := hy
      refine ⟨c * (a : u.adicCompletion), ⟨(a : u.adicCompletion), ?_, rfl⟩, ?_⟩
      · exact (range_tateProj u) ▸ a.2
      · rfl
    · rintro x ⟨y, ⟨av, hav, rfl⟩, rfl⟩
      refine ⟨alphaMap u c ⟨av, (range_tateProj u).symm ▸ hav⟩, ⟨_, rfl⟩, ?_⟩
      rfl
  have : FiniteDimensional K
      ((LinearMap.range (alphaMap u c)).map (eQ : Q1 →ₗ[K] Q2)) := by
    rw [hmap]; exact hF21
  exact (Submodule.equivMapOfInjective (eQ : Q1 →ₗ[K] Q2) eQ.injective
    (LinearMap.range (alphaMap u c))).symm.finiteDimensional

end TermMaps


section Cyclicity

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]
variable {pA' : u.adicCompletion →ₗ[K] u.adicCompletion}

scoped instance instFinDimRangeDeltaAlpha (h : SameRangeIdemProjectors (tateProj u) pA')
    (c : u.adicCompletion) :
    FiniteDimensional K (LinearMap.range (deltaQuotFactor h ∘ₗ alphaMap u c)) := by
  haveI := finiteDimensional_range_alphaMap u c
  rw [LinearMap.range_comp]
  infer_instance

scoped instance instFinDimRangeMulDeltaAlpha (h : SameRangeIdemProjectors (tateProj u) pA')
    (c : u.adicCompletion) {gh : u.adicCompletion} (hgh : gh ∈ u.adicCompletionIntegers) :
    FiniteDimensional K
      (LinearMap.range (mulOnRange u hgh ∘ₗ deltaQuotFactor h ∘ₗ alphaMap u c)) := by
  haveI := finiteDimensional_range_alphaMap u c
  rw [LinearMap.range_comp, LinearMap.range_comp]
  infer_instance

theorem finrankTrace_term_eq (h : SameRangeIdemProjectors (tateProj u) pA')
    (fh : u.adicCompletion) {gh : u.adicCompletion} (hgh : gh ∈ u.adicCompletionIntegers) :
    finrankTrace (deltaQuotFactor h ∘ₗ alphaMap u (gh * fh))
      = finrankTrace (mulOnRange u hgh ∘ₗ deltaQuotFactor h ∘ₗ alphaMap u fh) := by

  set dQ := deltaQuotFactor h
  set α₁ := alphaMap u (gh * fh)
  set α₂ := alphaMap u fh
  set β := mulOnRange u hgh

  haveI hFα₁ : FiniteDimensional K (LinearMap.range α₁) :=
    finiteDimensional_range_alphaMap u (gh * fh)
  haveI hFα₂ : FiniteDimensional K (LinearMap.range α₂) :=
    finiteDimensional_range_alphaMap u fh
  haveI hFS₁ : FiniteDimensional K (LinearMap.range (α₁ ∘ₗ dQ)) := by
    apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range α₁)
    exact LinearMap.range_comp_le_range _ _
  haveI hFS₂ : FiniteDimensional K (LinearMap.range (α₂ ∘ₗ (β ∘ₗ dQ))) := by
    apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range α₂)
    exact LinearMap.range_comp_le_range _ _

  haveI hFT₂' : FiniteDimensional K (LinearMap.range ((β ∘ₗ dQ) ∘ₗ α₂)) :=
    instFinDimRangeMulDeltaAlpha u h fh hgh

  have hcyc₁ : finrankTrace (dQ ∘ₗ α₁) = finrankTrace (α₁ ∘ₗ dQ) :=
    finrankTrace_comp_comm α₁ dQ
  have hcyc₂ : finrankTrace ((β ∘ₗ dQ) ∘ₗ α₂) = finrankTrace (α₂ ∘ₗ (β ∘ₗ dQ)) :=
    finrankTrace_comp_comm α₂ (β ∘ₗ dQ)

  have hSeq : α₁ ∘ₗ dQ = α₂ ∘ₗ (β ∘ₗ dQ) := by
    apply LinearMap.ext; intro y
    simp only [LinearMap.comp_apply]
    rw [alphaMap_apply, alphaMap_apply, mulOnRange_apply]
    congr 1
    ring

  show finrankTrace (dQ ∘ₗ α₁) = finrankTrace ((β ∘ₗ dQ) ∘ₗ α₂)
  rw [hcyc₁, hcyc₂]
  exact finrankTrace_congr hSeq

end Cyclicity


section Headline

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [∀ u : Place K L, u.FiniteResidue]

theorem kwF4gRRTate_projectorIndep : KwF4gRRTateProjectorIndep K L := by
  intro u pA' h fh gh hgh _ _

  set Φ := tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh)
  set Ψ' := tateCommRestrict pA' (lmulK u fh) (lmulK u gh)

  let e : LinearMap.range pA' ≃ₗ[K] LinearMap.range (tateProj u) :=
    LinearEquiv.ofEq _ _ h.range_eq.symm
  set Ψ := e.conj Ψ' with hΨdef

  haveI hFΨ : FiniteDimensional K (LinearMap.range Ψ) := by
    rw [hΨdef, range_conj_eq_map]
    infer_instance

  have hΨeq : finrankTrace Ψ = finrankTrace Ψ' := finrankTrace_conj e Ψ'
  show finrankTrace Φ = finrankTrace Ψ'
  rw [← hΨeq]

  set dQ := deltaQuotFactor h
  set T₁ := dQ ∘ₗ alphaMap u (gh * fh) with hT₁def
  set T₂ := mulOnRange u hgh ∘ₗ dQ ∘ₗ alphaMap u fh with hT₂def

  have hΦΨ : Φ - Ψ = T₁ - T₂ := by
    apply LinearMap.ext; intro a
    apply Subtype.ext

    simp only [LinearMap.sub_apply, AddSubgroupClass.coe_sub]

    have hΦv : (Φ a : u.adicCompletion)
        = (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh) a : u.adicCompletion) :=
      rfl
    have hΨv : (Ψ a : u.adicCompletion) = tateComm pA' (lmulK u fh) (lmulK u gh)
        (a : u.adicCompletion) := by
      show ((e.conj Ψ') a : u.adicCompletion) = _
      simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]

      have he_coe : ∀ (x : LinearMap.range pA'), ((e x : LinearMap.range (tateProj u)) :
          u.adicCompletion) = (x : u.adicCompletion) := fun x => rfl
      have hesymm_coe : ∀ (x : LinearMap.range (tateProj u)),
          ((e.symm x : LinearMap.range pA') : u.adicCompletion)
          = (x : u.adicCompletion) := fun x => rfl
      rw [he_coe, tateCommRestrict_apply, hesymm_coe]
    rw [hΦv, hΨv]

    rw [tateCommRestrict_diff u pA' h hgh fh a]

    have hT₁v : (T₁ a : u.adicCompletion)
        = (tateProj u - pA') (gh * fh * (a : u.adicCompletion)) := by
      simp only [T₁, LinearMap.comp_apply, dQ]
      rw [alphaMap_apply, deltaQuotFactor_apply]
    have hT₂v : (T₂ a : u.adicCompletion)
        = gh * (tateProj u - pA') (fh * (a : u.adicCompletion)) := by
      simp only [T₂, LinearMap.comp_apply, dQ]
      rw [alphaMap_apply, mulOnRange_apply, deltaQuotFactor_apply]
    rw [hT₁v, hT₂v]

  haveI hFT₁ : FiniteDimensional K (LinearMap.range T₁) :=
    instFinDimRangeDeltaAlpha u h (gh * fh)
  haveI hFT₂ : FiniteDimensional K (LinearMap.range T₂) :=
    instFinDimRangeMulDeltaAlpha u h fh hgh

  have hchain : finrankTrace Φ - finrankTrace Ψ = finrankTrace T₁ - finrankTrace T₂ := by
    rw [finrankTrace_sub Φ Ψ, finrankTrace_sub T₁ T₂]
    exact finrankTrace_congr hΦΨ
  rw [← sub_eq_zero, hchain, finrankTrace_term_eq u h fh hgh, sub_self]

end Headline


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

scoped instance instFinDimRangeNeg (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    FiniteDimensional K (LinearMap.range (-φ)) := by
  have h : LinearMap.range (-φ) = LinearMap.range φ := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩; exact ⟨-y, by simp⟩
    · rintro x ⟨y, rfl⟩; exact ⟨-y, by simp⟩
  rw [h]; infer_instance

scoped instance instFinDimRangeZero : FiniteDimensional K (LinearMap.range (0 : V →ₗ[K] V)) := by
  rw [LinearMap.range_zero]; infer_instance

theorem finrankTrace_zero : finrankTrace (0 : V →ₗ[K] V) = 0 := by
  unfold finrankTrace
  have hrest : (0 : V →ₗ[K] V).restrict
      (p := LinearMap.range (0 : V →ₗ[K] V))
      (fun x _ => LinearMap.mem_range_self _ x) = 0 := by
    apply LinearMap.ext; intro; apply Subtype.ext; rfl
  rw [hrest, _root_.map_zero]

theorem finrankTrace_neg (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    finrankTrace (-φ) = -finrankTrace φ := by
  have hsub := finrankTrace_sub (0 : V →ₗ[K] V) φ
  rw [finrankTrace_zero, zero_sub] at hsub
  calc finrankTrace (-φ) = finrankTrace ((0 : V →ₗ[K] V) - φ) :=
        finrankTrace_congr (zero_sub φ).symm
    _ = -finrankTrace φ := hsub.symm

scoped instance instFinDimRangeAdd (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (φ + ψ)) := by
  rw [show φ + ψ = φ - (-ψ) from (sub_neg_eq_add φ ψ).symm]
  exact instFinDimRangeSub φ (-ψ)

theorem finrankTrace_add (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    finrankTrace (φ + ψ) = finrankTrace φ + finrankTrace ψ := by
  have h := finrankTrace_sub φ (-ψ)
  rw [finrankTrace_neg, sub_neg_eq_add] at h
  calc finrankTrace (φ + ψ) = finrankTrace (φ - (-ψ)) :=
        finrankTrace_congr (sub_neg_eq_add φ ψ).symm
    _ = finrankTrace φ + finrankTrace ψ := h.symm

end Additivity


section TateCommAddFst

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem tateComm_add_fst (pA φ₁ φ₂ ψ : V →ₗ[K] V) :
    tateComm pA (φ₁ + φ₂) ψ = tateComm pA φ₁ ψ + tateComm pA φ₂ ψ := by
  unfold tateComm
  ext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_add]
  abel

theorem tateCommRestrict_add_fst (pA φ₁ φ₂ ψ : V →ₗ[K] V) :
    tateCommRestrict pA (φ₁ + φ₂) ψ
      = tateCommRestrict pA φ₁ ψ + tateCommRestrict pA φ₂ ψ := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  show (tateCommRestrict pA (φ₁ + φ₂) ψ a : V)
    = (tateCommRestrict pA φ₁ ψ a : V) + (tateCommRestrict pA φ₂ ψ a : V)
  rw [tateCommRestrict_apply, tateCommRestrict_apply, tateCommRestrict_apply]
  exact congrFun (congrArg DFunLike.coe (tateComm_add_fst pA φ₁ φ₂ ψ)) (a : V)

theorem tateCommTrace_add_fst (pA φ₁ φ₂ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ₁ ψ))]
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ₂ ψ))] :
    haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict pA (φ₁ + φ₂) ψ)) := by
      rw [tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
    tateCommTrace pA (φ₁ + φ₂) ψ = tateCommTrace pA φ₁ ψ + tateCommTrace pA φ₂ ψ := by
  haveI : FiniteDimensional K (LinearMap.range (tateCommRestrict pA (φ₁ + φ₂) ψ)) := by
    rw [tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
  unfold tateCommTrace
  rw [← finrankTrace_add]
  exact finrankTrace_congr (tateCommRestrict_add_fst pA φ₁ φ₂ ψ)

end TateCommAddFst


section TateResAddFst

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem tateRes_add_fst (fh₁ fh₂ gh : u.adicCompletion)
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₁) (lmulK u gh)))]
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₂) (lmulK u gh)))] :
    haveI : FiniteDimensional K (LinearMap.range
        (tateCommRestrict (tateProj u) (lmulK u (fh₁ + fh₂)) (lmulK u gh))) := by
      have heq : lmulK u (fh₁ + fh₂) = lmulK u fh₁ + lmulK u fh₂ := map_add _ _ _
      rw [heq, tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
    tateRes u (fh₁ + fh₂) gh = tateRes u fh₁ gh + tateRes u fh₂ gh := by
  have heq : lmulK u (fh₁ + fh₂) = lmulK u fh₁ + lmulK u fh₂ := map_add _ _ _
  haveI : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u (fh₁ + fh₂)) (lmulK u gh))) := by
    rw [heq, tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
  haveI : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh₁ + lmulK u fh₂) (lmulK u gh))) := by
    rw [tateCommRestrict_add_fst]; exact instFinDimRangeAdd _ _
  unfold tateRes
  have hct := tateCommTrace_add_fst (tateProj u) (lmulK u fh₁) (lmulK u fh₂) (lmulK u gh)
  unfold tateCommTrace at hct ⊢
  rw [← hct]
  exact finrankTrace_congr (by rw [heq])

end TateResAddFst


section CohenMint

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

end CohenMint


section Reprice

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]
variable [∀ u : Place K L, u.FiniteResidue]

end Reprice


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section DualAmbient

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def tateCommDual (pA φ ψ : V →ₗ[K] V) : V →ₗ[K] V :=
  φ ∘ₗ pA ∘ₗ ψ ∘ₗ pA - ψ ∘ₗ pA ∘ₗ φ ∘ₗ pA

theorem tateCommDual_apply (pA φ ψ : V →ₗ[K] V) (x : V) :
    tateCommDual pA φ ψ x = φ (pA (ψ (pA x))) - ψ (pA (φ (pA x))) := rfl

theorem tateCommTrace_eq_finrankTrace_tateCommDual {pA φ ψ : V →ₗ[K] V}
    [hR : FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ ψ))]
    [hD : FiniteDimensional K (LinearMap.range (tateCommDual pA φ ψ))] :
    tateCommTrace pA φ ψ = finrankTrace (tateCommDual pA φ ψ) := by

  set r : V →ₗ[K] LinearMap.range pA :=
    pA.codRestrict (LinearMap.range pA) (fun x => LinearMap.mem_range_self pA x) with hr
  set incl : LinearMap.range pA →ₗ[K] V := (LinearMap.range pA).subtype with hincl

  set X : V →ₗ[K] V := φ ∘ₗ pA ∘ₗ ψ - ψ ∘ₗ pA ∘ₗ φ with hX

  have hinclr : incl ∘ₗ r = pA := by
    apply LinearMap.ext; intro x; rfl
  have htateCommDual : X ∘ₗ pA = tateCommDual pA φ ψ := by
    apply LinearMap.ext; intro x
    simp only [hX, LinearMap.comp_apply, LinearMap.sub_apply, tateCommDual_apply]
  have htateCommRestrict : r ∘ₗ X ∘ₗ incl = tateCommRestrict pA φ ψ := by
    apply LinearMap.ext; intro a; apply Subtype.ext
    show pA (X (a : V)) = (tateCommRestrict pA φ ψ a : V)
    rw [tateCommRestrict_apply, tateComm_apply]
    simp only [hX, LinearMap.sub_apply, LinearMap.comp_apply, map_sub]

  have heqXir : (X ∘ₗ incl) ∘ₗ r = tateCommDual pA φ ψ := by
    rw [LinearMap.comp_assoc, hinclr, htateCommDual]
  haveI hRfg : FiniteDimensional K (LinearMap.range (r ∘ₗ (X ∘ₗ incl))) :=
    htateCommRestrict.symm ▸ hR
  haveI hRgf : FiniteDimensional K (LinearMap.range ((X ∘ₗ incl) ∘ₗ r)) :=
    heqXir.symm ▸ hD
  calc tateCommTrace pA φ ψ
      = finrankTrace (tateCommRestrict pA φ ψ) := rfl
    _ = finrankTrace (r ∘ₗ (X ∘ₗ incl)) := (finrankTrace_congr htateCommRestrict).symm
    _ = finrankTrace ((X ∘ₗ incl) ∘ₗ r) := finrankTrace_comp_comm (X ∘ₗ incl) r
    _ = finrankTrace (tateCommDual pA φ ψ) := finrankTrace_congr heqXir

end DualAmbient


section FinsetAdditivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

scoped instance instFinDimRangeSum {ι : Type*} (s : Finset ι) (f : ι → V →ₗ[K] V)
    [∀ i, FiniteDimensional K (LinearMap.range (f i))] :
    FiniteDimensional K (LinearMap.range (∑ i ∈ s, f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact instFinDimRangeZero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact instFinDimRangeAdd _ _

theorem finrankTrace_sum {ι : Type*} (s : Finset ι) (f : ι → V →ₗ[K] V)
    [∀ i, FiniteDimensional K (LinearMap.range (f i))] :
    finrankTrace (∑ i ∈ s, f i) = ∑ i ∈ s, finrankTrace (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    calc finrankTrace (∑ i ∈ (∅ : Finset ι), f i)
        = finrankTrace (0 : V →ₗ[K] V) := finrankTrace_congr Finset.sum_empty
      _ = 0 := finrankTrace_zero
      _ = ∑ i ∈ (∅ : Finset ι), finrankTrace (f i) := Finset.sum_empty.symm
  | insert a s ha ih =>
    haveI := instFinDimRangeSum s f
    have hRHS : (∑ i ∈ insert a s, finrankTrace (f i) : K)
        = finrankTrace (f a) + ∑ i ∈ s, finrankTrace (f i) := Finset.sum_insert ha
    rw [hRHS, ← ih]
    calc finrankTrace (∑ i ∈ insert a s, f i)
        = finrankTrace (f a + ∑ i ∈ s, f i) := finrankTrace_congr (Finset.sum_insert ha)
      _ = finrankTrace (f a) + finrankTrace (∑ i ∈ s, f i) := finrankTrace_add _ _

end FinsetAdditivity


section LemmaC

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem finiteDimensional_range_comp_middle
    {M₁ M₂ M₃ M₄ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [AddCommGroup M₄] [Module K M₁] [Module K M₂] [Module K M₃] [Module K M₄]
    (A : M₃ →ₗ[K] M₄) (δ : M₂ →ₗ[K] M₃) (B : M₁ →ₗ[K] M₂)
    [FiniteDimensional K (LinearMap.range δ)] :
    FiniteDimensional K (LinearMap.range (A ∘ₗ δ ∘ₗ B)) := by
  apply Submodule.finiteDimensional_of_le (S₂ := Submodule.map A (LinearMap.range δ))
  rintro x ⟨y, rfl⟩
  exact ⟨δ (B y), LinearMap.mem_range_self _ _, rfl⟩

end LemmaC


section AmbientFinite

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable [u.FiniteResidue]

theorem finiteDimensional_range_tateCommDual_tateProj
    (fh : u.adicCompletion) {gh : u.adicCompletion} (hgh : gh ∈ u.adicCompletionIntegers) :
    FiniteDimensional K
      (LinearMap.range (tateCommDual (tateProj u) (lmulK u fh) (lmulK u gh))) := by

  have hker : LinearMap.range (tateProj u)
      ≤ LinearMap.ker (LinearMap.id - tateProj u) := by
    rintro x ⟨y, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      tateProj_of_mem u (tateProj_mem_integers u y), sub_self]

  set pre : u.adicCompletion →ₗ[K] LinearMap.range (tateProj u) :=
    (tateProj u).codRestrict (LinearMap.range (tateProj u))
      (fun x => LinearMap.mem_range_self _ x) with hpre
  set post : (u.adicCompletion ⧸ LinearMap.range (tateProj u)) →ₗ[K] u.adicCompletion :=
    (lmulK u gh) ∘ₗ Submodule.liftQ _ (LinearMap.id - tateProj u) hker with hpost

  have hfactor : tateCommDual (tateProj u) (lmulK u fh) (lmulK u gh)
      = post ∘ₗ alphaMap u fh ∘ₗ pre := by
    apply LinearMap.ext; intro x

    change fh * tateProj u (gh * tateProj u x) - gh * tateProj u (fh * tateProj u x)
      = gh * (fh * tateProj u x - tateProj u (fh * tateProj u x))
    rw [tateProj_of_mem u (mul_mem hgh (tateProj_mem_integers u x))]
    ring
  rw [hfactor]
  haveI := finiteDimensional_range_alphaMap u fh
  exact finiteDimensional_range_comp_middle post (alphaMap u fh) pre

end AmbientFinite


section TateResSum

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem tateRes_sum_fst {ι : Type*} (s : Finset ι) (f : ι → u.adicCompletion)
    (gh : u.adicCompletion) (hfin : KwF4gRRTateCommFinite K L) :
    haveI := fun i => hfin u (f i) gh
    haveI := hfin u (∑ i ∈ s, f i) gh
    ∑ i ∈ s, tateRes u (f i) gh = tateRes u (∑ i ∈ s, f i) gh := by
  haveI := fun i => hfin u (f i) gh
  classical
  induction s using Finset.induction_on with
  | empty =>
    haveI := hfin u (0 : u.adicCompletion) gh
    rw [Finset.sum_empty, Finset.sum_empty]

    unfold tateRes tateCommTrace
    have h0 : tateCommRestrict (tateProj u) (lmulK u 0) (lmulK u gh) = 0 := by
      apply LinearMap.ext; intro a; apply Subtype.ext
      rw [tateCommRestrict_apply, tateComm_apply]
      simp [lmulK]
    rw [finrankTrace_congr h0, finrankTrace_zero]
  | insert a s ha ih =>
    haveI := hfin u (∑ i ∈ s, f i) gh
    haveI := hfin u (∑ i ∈ insert a s, f i) gh
    haveI := hfin u (f a + ∑ i ∈ s, f i) gh
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih,
      tateRes_add_fst u (f a) (∑ i ∈ s, f i) gh]

end TateResSum


section BlockSumMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

def KwF4gRRTateTraceCompatBlockSum (hfinF : KwF4gRRTateCommFinite K F)
    (hfinE : KwF4gRRTateCommFinite K E) : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F) (g : F),
    haveI := hfinF w (algebraMap F w.adicCompletion g)
      (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
    let b := Module.finBasis (w.restrict E).adicCompletion w.adicCompletion
    let M := LinearMap.toMatrix b b
      (Algebra.lmul (w.restrict E).adicCompletion w.adicCompletion
        (algebraMap F w.adicCompletion g))
    haveI := fun i => hfinE (w.restrict E) (M i i)
      (algebraMap E (w.restrict E).adicCompletion (w.restrict E).uniformizer)
    tateRes w (algebraMap F w.adicCompletion g)
        (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
      = ∑ i, tateRes (w.restrict E) (M i i)
          (algebraMap E (w.restrict E).adicCompletion (w.restrict E).uniformizer)

end BlockSumMint


section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

theorem kwF4gRRTate_traceCompat_of_blockSum
    (hfinF : KwF4gRRTateCommFinite K F) (hfinE : KwF4gRRTateCommFinite K E)
    (hBS : KwF4gRRTateTraceCompatBlockSum K F E hfinF hfinE) :
    KwF4gRRTateTraceCompat K F E hfinF hfinE := by
  intro _ _ _ v w hw g

  have hv : w.restrict E = v := Place.mem_fiber.mp hw
  subst hv

  set V₀ := (w.restrict E).adicCompletion
  set W₀ := w.adicCompletion
  set b : Module.Basis (Fin (Module.finrank V₀ W₀)) V₀ W₀ := Module.finBasis V₀ W₀ with hb
  set M := LinearMap.toMatrix b b (Algebra.lmul V₀ W₀ (algebraMap F W₀ g)) with hM
  set πv := algebraMap E V₀ (w.restrict E).uniformizer

  haveI hfiw := hfinF w (algebraMap F W₀ g)
    (algebraMap F W₀ (algebraMap E F (w.restrict E).uniformizer))
  haveI hfiv := fun i => hfinE (w.restrict E) (M i i) πv
  haveI hfisum := hfinE (w.restrict E) (∑ i, M i i) πv

  have hBSw := hBS (w.restrict E) w hw g
  simp only at hBSw
  rw [hBSw]

  rw [tateRes_sum_fst (w.restrict E) Finset.univ (fun i => M i i) πv hfinE]

  have hdiag : ∑ i, M i i = Algebra.trace V₀ W₀ (algebraMap F W₀ g) := by
    have htr := LinearMap.trace_eq_matrix_trace (R := V₀) b
      (Algebra.lmul V₀ W₀ (algebraMap F W₀ g))
    rw [show (Algebra.trace V₀ W₀ (algebraMap F W₀ g) : V₀)
      = LinearMap.trace V₀ W₀ (Algebra.lmul V₀ W₀ (algebraMap F W₀ g)) from rfl, htr,
      hM, Matrix.trace]
    rfl

  have hcast : kwHgfV352_completionTraceAt (w.restrict E) w hw g
      = kw_ffgc_completionTraceF' E w g := rfl
  have hτ : ∑ i, M i i = kwHgfV352_completionTraceAt (w.restrict E) w hw g := by
    rw [hcast, kw_ffgc_completionTraceF'_apply, hdiag]
  rw [show (∑ i ∈ Finset.univ, M i i) = ∑ i, M i i from rfl, hτ]

end Headline


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 25600000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section ConjNaturality

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M]
variable [AddCommGroup N] [Module K N]

theorem tateCommDual_conj (e : M ≃ₗ[K] N) (pA φ ψ : M →ₗ[K] M) :
    e.conj (tateCommDual pA φ ψ) = tateCommDual (e.conj pA) (e.conj φ) (e.conj ψ) := by
  apply LinearMap.ext; intro x
  simp only [LinearEquiv.conj_apply, tateCommDual_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, map_sub, LinearEquiv.symm_apply_apply]

end ConjNaturality


section ProdProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L)

def prodTateProj (ι : Type*) :
    (ι → v.adicCompletion) →ₗ[K] (ι → v.adicCompletion) :=
  LinearMap.pi (fun i => tateProj v ∘ₗ LinearMap.proj i)

theorem prodTateProj_apply {ι : Type*} (x : ι → v.adicCompletion) (i : ι) :
    prodTateProj v ι x i = tateProj v (x i) := rfl

theorem prodTateProj_idem {ι : Type*} (x : ι → v.adicCompletion) :
    prodTateProj v ι (prodTateProj v ι x) = prodTateProj v ι x :=
  funext fun i => congrFun (congrArg DFunLike.coe (tateProj_idem v)) (x i)

end ProdProj


section BlockDecomp

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : Place K L)
variable {n : ℕ}

def matMulLin (M : Matrix (Fin n) (Fin n) v.adicCompletion) :
    (Fin n → v.adicCompletion) →ₗ[K] (Fin n → v.adicCompletion) :=
  LinearMap.pi (fun i => ∑ j, lmulK v (M i j) ∘ₗ LinearMap.proj j)

theorem matMulLin_apply (M : Matrix (Fin n) (Fin n) v.adicCompletion)
    (x : Fin n → v.adicCompletion) (i : Fin n) :
    matMulLin v M x i = ∑ j, M i j * x j := by
  simp only [matMulLin, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  rfl

def scalarLin (πv : v.adicCompletion) :
    (Fin n → v.adicCompletion) →ₗ[K] (Fin n → v.adicCompletion) :=
  LinearMap.pi (fun i => lmulK v πv ∘ₗ LinearMap.proj i)

theorem scalarLin_apply (πv : v.adicCompletion) (x : Fin n → v.adicCompletion) (i : Fin n) :
    scalarLin v πv x i = πv * x i := rfl

theorem tateCommDual_prodTateProj_eq_blockSum
    (M : Matrix (Fin n) (Fin n) v.adicCompletion) (πv : v.adicCompletion) :
    tateCommDual (prodTateProj v (Fin n)) (matMulLin v M) (scalarLin v πv)
      = ∑ i, ∑ j, LinearMap.single K (fun _ => v.adicCompletion) i
          ∘ₗ tateCommDual (tateProj v) (lmulK v (M i j)) (lmulK v πv)
          ∘ₗ LinearMap.proj j := by
  apply LinearMap.ext; intro x; funext i

  have hRHS : ((∑ i', ∑ j, LinearMap.single K (fun _ => v.adicCompletion) i'
          ∘ₗ tateCommDual (tateProj v) (lmulK v (M i' j)) (lmulK v πv)
          ∘ₗ LinearMap.proj j) x) i
      = ∑ j, tateCommDual (tateProj v) (lmulK v (M i j)) (lmulK v πv) (x j) := by
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      Finset.sum_apply, LinearMap.single_apply]
    rw [Finset.sum_eq_single i (fun i' _ hi' => ?_) (fun h => absurd (Finset.mem_univ i) h)]
    · simp only [Pi.single_eq_same]
    · exact Finset.sum_eq_zero fun j _ => Pi.single_eq_of_ne' hi' _
  rw [hRHS, tateCommDual_apply]

  simp only [prodTateProj_apply, matMulLin_apply, scalarLin_apply, Pi.sub_apply]
  rw [show tateProj v (∑ j, M i j * tateProj v (x j))
      = ∑ j, tateProj v (M i j * tateProj v (x j)) from map_sum _ _ _,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tateCommDual_apply]; rfl

end BlockDecomp


section BlockTrace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {n : ℕ}

theorem finrankTrace_blockSum (T : Fin n → Fin n → (V →ₗ[K] V))
    [hT : ∀ i j, FiniteDimensional K (LinearMap.range (T i j))] :
    haveI : ∀ (i j : Fin n), FiniteDimensional K (LinearMap.range
        (LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i j
          ∘ₗ (LinearMap.proj j : (Fin n → V) →ₗ[K] V))) :=
      fun i j => finiteDimensional_range_comp_middle
        (LinearMap.single K (fun _ : Fin n => V) i) (T i j)
        (LinearMap.proj j : (Fin n → V) →ₗ[K] V)
    finrankTrace (∑ i, ∑ j, LinearMap.single K (fun _ : Fin n => V) i
        ∘ₗ T i j ∘ₗ (LinearMap.proj j : (Fin n → V) →ₗ[K] V))
      = ∑ i, finrankTrace (T i i) := by
  haveI : ∀ (i j : Fin n), FiniteDimensional K (LinearMap.range
      (LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i j
        ∘ₗ (LinearMap.proj j : (Fin n → V) →ₗ[K] V))) :=
    fun i j => finiteDimensional_range_comp_middle
      (LinearMap.single K (fun _ : Fin n => V) i) (T i j)
      (LinearMap.proj j : (Fin n → V) →ₗ[K] V)
  haveI : ∀ (i : Fin n), FiniteDimensional K (LinearMap.range
      (∑ j, LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i j
        ∘ₗ (LinearMap.proj j : (Fin n → V) →ₗ[K] V))) :=
    fun i => instFinDimRangeSum _ _
  rw [finrankTrace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finrankTrace_sum]

  have hassoc : ∀ (j : Fin n), LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i j
      ∘ₗ (LinearMap.proj j : (Fin n → V) →ₗ[K] V)
      = (LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i j)
        ∘ₗ (LinearMap.proj j : (Fin n → V) →ₗ[K] V) := fun j => rfl
  have hswap : ∀ (j : Fin n), (LinearMap.proj j : (Fin n → V) →ₗ[K] V)
      ∘ₗ (LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i j)
      = if j = i then T i i else 0 := fun j => by
    apply LinearMap.ext; intro y
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]
    by_cases hji : j = i
    · subst hji; rw [if_pos rfl, Pi.single_eq_same]
    · rw [if_neg hji, Pi.single_eq_of_ne hji, LinearMap.zero_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)]
  ·
    haveI hfi : FiniteDimensional K (LinearMap.range
        ((LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i i)
          ∘ₗ (LinearMap.proj i : (Fin n → V) →ₗ[K] V))) := hassoc i ▸ inferInstance
    haveI hgi : FiniteDimensional K (LinearMap.range
        ((LinearMap.proj i : (Fin n → V) →ₗ[K] V)
          ∘ₗ (LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i i))) := by
      rw [hswap i, if_pos rfl]; exact hT i i
    calc finrankTrace (LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i i
            ∘ₗ (LinearMap.proj i : (Fin n → V) →ₗ[K] V))
        = finrankTrace ((LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i i)
            ∘ₗ (LinearMap.proj i : (Fin n → V) →ₗ[K] V)) := finrankTrace_congr (hassoc i)
      _ = finrankTrace ((LinearMap.proj i : (Fin n → V) →ₗ[K] V)
            ∘ₗ (LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i i)) :=
          finrankTrace_comp_comm _ _
      _ = finrankTrace (T i i) := finrankTrace_congr (by rw [hswap i, if_pos rfl])
  ·
    haveI hfj : FiniteDimensional K (LinearMap.range
        ((LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i j)
          ∘ₗ (LinearMap.proj j : (Fin n → V) →ₗ[K] V))) := hassoc j ▸ inferInstance
    haveI hgj : FiniteDimensional K (LinearMap.range
        ((LinearMap.proj j : (Fin n → V) →ₗ[K] V)
          ∘ₗ (LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i j))) := by
      rw [hswap j, if_neg hj]; exact instFinDimRangeZero
    calc finrankTrace (LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i j
            ∘ₗ (LinearMap.proj j : (Fin n → V) →ₗ[K] V))
        = finrankTrace ((LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i j)
            ∘ₗ (LinearMap.proj j : (Fin n → V) →ₗ[K] V)) := finrankTrace_congr (hassoc j)
      _ = finrankTrace ((LinearMap.proj j : (Fin n → V) →ₗ[K] V)
            ∘ₗ (LinearMap.single K (fun _ : Fin n => V) i ∘ₗ T i j)) :=
          finrankTrace_comp_comm _ _
      _ = finrankTrace (0 : V →ₗ[K] V) := finrankTrace_congr (by rw [hswap j, if_neg hj])
      _ = 0 := finrankTrace_zero

end BlockTrace


section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

scoped instance instIsScalarTowerKVhatWhat (w : Place K F) :
    IsScalarTower K (w.restrict E).adicCompletion w.adicCompletion :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K F w.adicCompletion c,
      IsScalarTower.algebraMap_apply K E F c,
      IsScalarTower.algebraMap_apply K E (w.restrict E).adicCompletion c]
    exact kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w (algebraMap K E c)

end Headline


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 51200000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section Freeness

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwF4gRRTate_free_adicCompletionIntegers (w : Place K F) [FiniteDimensional E F]
    [Algebra.IsSeparable (w.restrict E).adicCompletion w.adicCompletion] :
    Module.Free (w.restrict E).adicCompletionIntegers w.adicCompletionIntegers := by
  haveI : Algebra.IsAlgebraic (w.restrict E).adicCompletion w.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : IsIntegralClosure w.adicCompletionIntegers (w.restrict E).adicCompletionIntegers
      w.adicCompletion := kw_ffgc_isIntegralClosure_adicCompletionIntegers E w
  haveI : IsNoetherian (w.restrict E).adicCompletionIntegers w.adicCompletionIntegers :=
    IsIntegralClosure.isNoetherian (w.restrict E).adicCompletionIntegers
      (w.restrict E).adicCompletion w.adicCompletion w.adicCompletionIntegers
  haveI : Module.Finite (w.restrict E).adicCompletionIntegers w.adicCompletionIntegers :=
    Module.IsNoetherian.finite _ _
  exact Module.free_of_finite_type_torsion_free'

end Freeness


section IntegralBasisMint

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

structure IntegralBasisData (w : Place K F) [FiniteDimensional E F] where

  basis : Module.Basis
    (Fin (Module.finrank (w.restrict E).adicCompletion w.adicCompletion))
    (w.restrict E).adicCompletion w.adicCompletion

  basis_mem : ∀ i, basis i ∈ w.adicCompletionIntegers

  mem_integers_iff : ∀ y, y ∈ w.adicCompletionIntegers
    ↔ ∀ i, basis.repr y i ∈ (w.restrict E).adicCompletionIntegers

variable (K F E) in

def KwF4gRRTateIntegralBasisCompat : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (w : Place K F), Nonempty (IntegralBasisData (E := E) w)

end IntegralBasisMint


section IntegralProdProj

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable (w : Place K F) [FiniteDimensional E F] (D : IntegralBasisData (E := E) w)

def integralBasisEquivFunK : w.adicCompletion ≃ₗ[K]
    (Fin (Module.finrank (w.restrict E).adicCompletion w.adicCompletion)
      → (w.restrict E).adicCompletion) :=
  D.basis.equivFun.restrictScalars K

theorem integralBasisEquivFunK_apply (y : w.adicCompletion) :
    integralBasisEquivFunK w D y = D.basis.equivFun y := rfl

def integralProdProj : w.adicCompletion →ₗ[K] w.adicCompletion :=
  (integralBasisEquivFunK w D).symm.conj (prodTateProj (w.restrict E) _)

theorem integralProdProj_idem (y : w.adicCompletion) :
    integralProdProj w D (integralProdProj w D y) = integralProdProj w D y := by
  unfold integralProdProj
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rw [prodTateProj_idem]

theorem range_integralProdProj :
    LinearMap.range (integralProdProj w D) = adicIntegersKSubmod w := by
  apply le_antisymm
  · rintro y ⟨z, rfl⟩

    rw [mem_adicIntegersKSubmod_iff, D.mem_integers_iff]
    intro i
    have : D.basis.repr (integralProdProj w D z) i
        = tateProj (w.restrict E) ((D.basis.equivFun z) i) := by
      have hipp : integralProdProj w D z
          = D.basis.equivFun.symm (prodTateProj (w.restrict E) _ (D.basis.equivFun z)) := by
        unfold integralProdProj
        simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.symm_symm, integralBasisEquivFunK, LinearEquiv.restrictScalars_apply,
          LinearEquiv.restrictScalars_symm_apply]
      rw [hipp, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply,
        prodTateProj_apply]
    rw [this]
    exact tateProj_mem_integers (w.restrict E) _
  · intro y hy
    refine ⟨y, ?_⟩

    have hrepr := (D.mem_integers_iff y).mp ((mem_adicIntegersKSubmod_iff w y).mp hy)
    unfold integralProdProj
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm]
    rw [show prodTateProj (w.restrict E) _ ((integralBasisEquivFunK w D) y)
      = (integralBasisEquivFunK w D) y from ?_]
    · exact (integralBasisEquivFunK w D).symm_apply_apply y
    · funext i
      rw [prodTateProj_apply, integralBasisEquivFunK_apply, Module.Basis.equivFun_apply]
      exact tateProj_of_mem (w.restrict E) (hrepr i)

theorem sameRangeIdemProjectors_integralProdProj :
    SameRangeIdemProjectors (tateProj w) (integralProdProj w D) where
  idem_pA x := congrFun (congrArg DFunLike.coe (tateProj_idem w)) x
  idem_pA' := integralProdProj_idem w D
  range_eq := (range_tateProj w).trans (range_integralProdProj w D).symm

end IntegralProdProj


section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem integralBasisEquivFunK_conj_lmulK_algebraMap (w : Place K F) [FiniteDimensional E F]
    (D : IntegralBasisData (E := E) w) (g : F) :
    (integralBasisEquivFunK w D).conj (lmulK w (algebraMap F w.adicCompletion g))
      = matMulLin (w.restrict E)
          (LinearMap.toMatrix D.basis D.basis
            (Algebra.lmul (w.restrict E).adicCompletion w.adicCompletion
              (algebraMap F w.adicCompletion g))) := by
  apply LinearMap.ext; intro x; funext i
  rw [matMulLin_apply, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe]
  show D.basis.equivFun (algebraMap F w.adicCompletion g * (D.basis.equivFun.symm x)) i
    = ∑ j, (LinearMap.toMatrix D.basis D.basis
        (Algebra.lmul (w.restrict E).adicCompletion w.adicCompletion
          (algebraMap F w.adicCompletion g))) i j * x j
  have hreprsymm : ⇑(D.basis.repr (D.basis.equivFun.symm x)) = x := by
    funext j; rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [Module.Basis.equivFun_apply,
    show algebraMap F w.adicCompletion g * D.basis.equivFun.symm x
    = Algebra.lmul (w.restrict E).adicCompletion w.adicCompletion
        (algebraMap F w.adicCompletion g) (D.basis.equivFun.symm x) from rfl,
    ← LinearMap.toMatrix_mulVec_repr D.basis D.basis, hreprsymm, Matrix.mulVec]
  rfl

theorem integralBasisEquivFunK_conj_lmulK_scalar (w : Place K F) [FiniteDimensional E F]
    (D : IntegralBasisData (E := E) w) (e : E) :
    (integralBasisEquivFunK w D).conj
        (lmulK w (algebraMap F w.adicCompletion (algebraMap E F e)))
      = scalarLin (w.restrict E) (algebraMap E (w.restrict E).adicCompletion e) := by
  apply LinearMap.ext; intro x; funext i
  rw [scalarLin_apply, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe]
  show D.basis.equivFun (algebraMap F w.adicCompletion (algebraMap E F e)
      * (D.basis.equivFun.symm x)) i
    = algebraMap E (w.restrict E).adicCompletion e * x i
  have halg : algebraMap F w.adicCompletion (algebraMap E F e)
      = algebraMap (w.restrict E).adicCompletion w.adicCompletion
          (algebraMap E (w.restrict E).adicCompletion e) :=
    kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w e
  rw [halg, ← Algebra.smul_def, map_smul, LinearEquiv.apply_symm_apply,
    Pi.smul_apply, smul_eq_mul]

theorem kwF4gRRTate_blockSum_of_integralBasisCompat
    [∀ w : Place K F, w.FiniteResidue] [∀ v : Place K E, v.FiniteResidue]
    (hfinF : KwF4gRRTateCommFinite K F) (hfinE : KwF4gRRTateCommFinite K E)
    (hIBC : KwF4gRRTateIntegralBasisCompat K F E) :
    KwF4gRRTateTraceCompatBlockSum K F E hfinF hfinE := by
  intro _ _ _ v w hw g
  have hv : w.restrict E = v := Place.mem_fiber.mp hw
  subst hv
  obtain ⟨D⟩ := hIBC w
  set V₀ := (w.restrict E).adicCompletion
  set W₀ := w.adicCompletion
  set n := Module.finrank V₀ W₀
  set b : Module.Basis (Fin n) V₀ W₀ := Module.finBasis V₀ W₀ with hb
  set M := LinearMap.toMatrix b b (Algebra.lmul V₀ W₀ (algebraMap F W₀ g)) with hM
  set M' := LinearMap.toMatrix D.basis D.basis
    (Algebra.lmul V₀ W₀ (algebraMap F W₀ g)) with hM'
  set πv := algebraMap E V₀ (w.restrict E).uniformizer with hπv
  set ghF := algebraMap F W₀ (algebraMap E F (w.restrict E).uniformizer) with hghF
  set eD : W₀ ≃ₗ[K] (Fin n → V₀) := integralBasisEquivFunK w D with heD
  set P := prodTateProj (w.restrict E) (Fin n) with hP
  set pI := integralProdProj w D with hpI

  have hghmem : ghF ∈ w.adicCompletionIntegers := by
    rw [hghF]; exact (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff w _).mpr
      ((Place.mem_restrict_iff w).mp (w.restrict E).uniformizer_mem)
  have hπvmem : πv ∈ (w.restrict E).adicCompletionIntegers := by
    rw [hπv]; exact (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff _ _).mpr
      (w.restrict E).uniformizer_mem

  haveI hFw := hfinF w (algebraMap F W₀ g) ghF
  haveI hFv := fun i => hfinE (w.restrict E) (M i i) πv
  haveI hFv' := fun i => hfinE (w.restrict E) (M' i i) πv
  haveI hFpI : FiniteDimensional K (LinearMap.range
      (tateCommRestrict pI (lmulK w (algebraMap F W₀ g)) (lmulK w ghF))) :=
    kwF4gRRTate_commFiniteGen w pI
      (sameRangeIdemProjectors_integralProdProj w D) (algebraMap F W₀ g) ghF
  haveI hD1 : FiniteDimensional K (LinearMap.range
      (tateCommDual (tateProj w) (lmulK w (algebraMap F W₀ g)) (lmulK w ghF))) :=
    finiteDimensional_range_tateCommDual_tateProj w (algebraMap F W₀ g) hghmem
  haveI hTij' : ∀ (i j : Fin n), FiniteDimensional K (LinearMap.range
      (tateCommDual (tateProj (w.restrict E)) (lmulK (w.restrict E) (M' i j))
        (lmulK (w.restrict E) πv))) := fun i j =>
    finiteDimensional_range_tateCommDual_tateProj (w.restrict E) (M' i j) hπvmem
  haveI hTii : ∀ (i : Fin n), FiniteDimensional K (LinearMap.range
      (tateCommDual (tateProj (w.restrict E)) (lmulK (w.restrict E) (M i i))
        (lmulK (w.restrict E) πv))) := fun i =>
    finiteDimensional_range_tateCommDual_tateProj (w.restrict E) (M i i) hπvmem

  have hPconj : eD.conj pI = P := by
    change eD.conj (eD.symm.conj P) = P
    exact P2MW.CloudB3W16RRSplit.conj_symm_conj eD P
  have hTCDconj : eD.conj (tateCommDual pI (lmulK w (algebraMap F W₀ g)) (lmulK w ghF))
      = tateCommDual P (matMulLin (w.restrict E) M') (scalarLin (w.restrict E) πv) := by
    rw [tateCommDual_conj, hPconj, heD, integralBasisEquivFunK_conj_lmulK_algebraMap,
      integralBasisEquivFunK_conj_lmulK_scalar]

  haveI hBlk' : ∀ (i j : Fin n), FiniteDimensional K (LinearMap.range
      (LinearMap.single K (fun _ : Fin n => V₀) i
        ∘ₗ tateCommDual (tateProj (w.restrict E)) (lmulK (w.restrict E) (M' i j))
            (lmulK (w.restrict E) πv)
        ∘ₗ (LinearMap.proj j : (Fin n → V₀) →ₗ[K] V₀))) :=
    fun i j => finiteDimensional_range_comp_middle _ _ _
  haveI hBlkI' : ∀ (i : Fin n), FiniteDimensional K (LinearMap.range
      (∑ j, LinearMap.single K (fun _ : Fin n => V₀) i
        ∘ₗ tateCommDual (tateProj (w.restrict E)) (lmulK (w.restrict E) (M' i j))
            (lmulK (w.restrict E) πv)
        ∘ₗ (LinearMap.proj j : (Fin n → V₀) →ₗ[K] V₀))) :=
    fun i => instFinDimRangeSum _ _
  haveI hBlkSum' : FiniteDimensional K (LinearMap.range
      (∑ i, ∑ j, LinearMap.single K (fun _ : Fin n => V₀) i
        ∘ₗ tateCommDual (tateProj (w.restrict E)) (lmulK (w.restrict E) (M' i j))
            (lmulK (w.restrict E) πv)
        ∘ₗ (LinearMap.proj j : (Fin n → V₀) →ₗ[K] V₀))) := instFinDimRangeSum _ _

  set rTCDpI := LinearMap.range
    (tateCommDual pI (lmulK w (algebraMap F W₀ g)) (lmulK w ghF)) with hrTCDpI
  haveI hmapfin : FiniteDimensional K (rTCDpI.map (eD : W₀ →ₗ[K] (Fin n → V₀))) := by
    rw [hrTCDpI, ← range_conj_eq_map, hTCDconj, tateCommDual_prodTateProj_eq_blockSum]
    exact hBlkSum'
  haveI hDpI : FiniteDimensional K rTCDpI :=
    (Submodule.equivMapOfInjective (eD : W₀ →ₗ[K] (Fin n → V₀))
      eD.injective rTCDpI).symm.finiteDimensional
  haveI hDpI' : FiniteDimensional K (LinearMap.range
      (tateCommDual pI (lmulK w (algebraMap F W₀ g)) (lmulK w ghF))) := hrTCDpI ▸ hDpI
  haveI hDeDconj : FiniteDimensional K (LinearMap.range
      (eD.conj (tateCommDual pI (lmulK w (algebraMap F W₀ g)) (lmulK w ghF)))) := by
    rw [range_conj_eq_map, ← hrTCDpI]; exact hmapfin
  haveI hDP : FiniteDimensional K (LinearMap.range
      (tateCommDual P (matMulLin (w.restrict E) M') (scalarLin (w.restrict E) πv))) :=
    hTCDconj ▸ hDeDconj

  simp only
  have hchain : tateRes w (algebraMap F W₀ g) ghF
      = ∑ i, tateRes (w.restrict E) (M' i i) πv := by
    calc tateRes w (algebraMap F W₀ g) ghF
        = tateCommTrace (tateProj w) (lmulK w (algebraMap F W₀ g)) (lmulK w ghF) := rfl
      _ = tateCommTrace pI (lmulK w (algebraMap F W₀ g)) (lmulK w ghF) :=
          kwF4gRRTate_projectorIndep w pI
            (sameRangeIdemProjectors_integralProdProj w D)
            (algebraMap F W₀ g) ghF hghmem
      _ = finrankTrace (tateCommDual pI (lmulK w (algebraMap F W₀ g)) (lmulK w ghF)) :=
          tateCommTrace_eq_finrankTrace_tateCommDual
      _ = finrankTrace (eD.conj (tateCommDual pI (lmulK w (algebraMap F W₀ g))
            (lmulK w ghF))) := (finrankTrace_conj eD _).symm
      _ = finrankTrace (tateCommDual P (matMulLin (w.restrict E) M')
            (scalarLin (w.restrict E) πv)) := finrankTrace_congr hTCDconj
      _ = finrankTrace (∑ i, ∑ j, LinearMap.single K (fun _ : Fin n => V₀) i
            ∘ₗ tateCommDual (tateProj (w.restrict E)) (lmulK (w.restrict E) (M' i j))
                (lmulK (w.restrict E) πv)
            ∘ₗ (LinearMap.proj j : (Fin n → V₀) →ₗ[K] V₀)) :=
          finrankTrace_congr (tateCommDual_prodTateProj_eq_blockSum (w.restrict E) M' πv)
      _ = ∑ i, finrankTrace (tateCommDual (tateProj (w.restrict E))
            (lmulK (w.restrict E) (M' i i)) (lmulK (w.restrict E) πv)) :=
          finrankTrace_blockSum _
      _ = ∑ i, tateRes (w.restrict E) (M' i i) πv := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact (tateCommTrace_eq_finrankTrace_tateCommDual
            (pA := tateProj (w.restrict E))).symm

  haveI hFsum := hfinE (w.restrict E) (∑ i, M' i i) πv
  haveI hFsumM := hfinE (w.restrict E) (∑ i, M i i) πv
  have htr : (∑ i, M' i i : V₀) = ∑ i, M i i := by
    have h1 : (∑ i, M' i i : V₀) = Algebra.trace V₀ W₀ (algebraMap F W₀ g) := by
      rw [show (Algebra.trace V₀ W₀ (algebraMap F W₀ g) : V₀)
        = LinearMap.trace V₀ W₀ (Algebra.lmul V₀ W₀ (algebraMap F W₀ g)) from rfl,
        LinearMap.trace_eq_matrix_trace (R := V₀) D.basis, hM', Matrix.trace]
      rfl
    have h2 : (∑ i, M i i : V₀) = Algebra.trace V₀ W₀ (algebraMap F W₀ g) := by
      rw [show (Algebra.trace V₀ W₀ (algebraMap F W₀ g) : V₀)
        = LinearMap.trace V₀ W₀ (Algebra.lmul V₀ W₀ (algebraMap F W₀ g)) from rfl,
        LinearMap.trace_eq_matrix_trace (R := V₀) b, hM, Matrix.trace]
      rfl
    rw [h1, h2]
  rw [hchain, tateRes_sum_fst (w.restrict E) Finset.univ (fun i => M' i i) πv hfinE,
    tateRes_sum_fst (w.restrict E) Finset.univ (fun i => M i i) πv hfinE,
    show (∑ i ∈ Finset.univ, M' i i) = ∑ i, M' i i from rfl,
    show (∑ i ∈ Finset.univ, M i i) = ∑ i, M i i from rfl, htr]

theorem kwF4gRRTate_traceCompat_of_integralBasisCompat
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]
    [∀ w : Place K F, w.FiniteResidue] [∀ v : Place K E, v.FiniteResidue]
    (hfinF : KwF4gRRTateCommFinite K F) (hfinE : KwF4gRRTateCommFinite K E)
    (hIBC : KwF4gRRTateIntegralBasisCompat K F E) :
    KwF4gRRTateTraceCompat K F E hfinF hfinE :=
  kwF4gRRTate_traceCompat_of_blockSum hfinF hfinE
    (kwF4gRRTate_blockSum_of_integralBasisCompat hfinF hfinE hIBC)

end Headline


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 25600000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section Construct

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable (w : Place K F) [FiniteDimensional E F]
variable [Algebra.IsSeparable (w.restrict E).adicCompletion w.adicCompletion]
variable [Module.IsTorsionFree (w.restrict E).adicCompletionIntegers w.adicCompletion]

scoped instance instIsLocalizationAlgebraMapSubmonoid :
    haveI : Algebra.IsAlgebraic (w.restrict E).adicCompletion w.adicCompletion :=
      Algebra.IsAlgebraic.of_finite _ _
    haveI := kw_ffgc_isIntegralClosure_adicCompletionIntegers E w
    IsLocalization (Algebra.algebraMapSubmonoid w.adicCompletionIntegers
      (nonZeroDivisors (w.restrict E).adicCompletionIntegers)) w.adicCompletion := by
  haveI : Algebra.IsAlgebraic (w.restrict E).adicCompletion w.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI := kw_ffgc_isIntegralClosure_adicCompletionIntegers E w
  exact IsIntegralClosure.isLocalization (w.restrict E).adicCompletionIntegers
    (w.restrict E).adicCompletion w.adicCompletion w.adicCompletionIntegers

def integralBasisDataOf : IntegralBasisData (E := E) w := by
  haveI : Algebra.IsAlgebraic (w.restrict E).adicCompletion w.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI hIC := kw_ffgc_isIntegralClosure_adicCompletionIntegers E w
  haveI hFree := kwF4gRRTate_free_adicCompletionIntegers (E := E) w
  haveI : IsNoetherian (w.restrict E).adicCompletionIntegers w.adicCompletionIntegers :=
    IsIntegralClosure.isNoetherian (w.restrict E).adicCompletionIntegers
      (w.restrict E).adicCompletion w.adicCompletion w.adicCompletionIntegers

  let c := Module.Free.chooseBasis (w.restrict E).adicCompletionIntegers w.adicCompletionIntegers

  let c' := c.localizationLocalization (w.restrict E).adicCompletion
    (nonZeroDivisors (w.restrict E).adicCompletionIntegers) w.adicCompletion

  have hrank : Module.finrank (w.restrict E).adicCompletionIntegers w.adicCompletionIntegers
      = Module.finrank (w.restrict E).adicCompletion w.adicCompletion :=
    IsIntegralClosure.rank (w.restrict E).adicCompletionIntegers
      (w.restrict E).adicCompletion w.adicCompletion w.adicCompletionIntegers
  let e : Module.Free.ChooseBasisIndex (w.restrict E).adicCompletionIntegers
        w.adicCompletionIntegers
      ≃ Fin (Module.finrank (w.restrict E).adicCompletion w.adicCompletion) :=
    (Fintype.equivFinOfCardEq (by
      rw [← hrank, Module.finrank_eq_card_chooseBasisIndex]))
  let c'' := c'.reindex e
  refine { basis := c'', basis_mem := ?_, mem_integers_iff := ?_ }
  ·
    intro i
    rw [show c'' i = c' (e.symm i) from Module.Basis.reindex_apply c' e i,
      Module.Basis.localizationLocalization_apply]
    exact (c (e.symm i)).2
  ·
    intro y
    constructor
    ·
      intro hy i
      obtain ⟨z, hz⟩ : ∃ z : w.adicCompletionIntegers,
          algebraMap w.adicCompletionIntegers w.adicCompletion z = y := ⟨⟨y, hy⟩, rfl⟩
      rw [← hz, Module.Basis.repr_reindex_apply,
        Module.Basis.localizationLocalization_repr_algebraMap]
      exact (c.repr z (e.symm i)).2
    ·
      intro hrepr
      have hsum : y = ∑ i, c''.repr y i • c'' i := (c''.sum_repr y).symm
      rw [hsum]
      refine sum_mem fun i _ => ?_
      have hci : c'' i ∈ w.adicCompletionIntegers := by
        rw [show c'' i = c' (e.symm i) from Module.Basis.reindex_apply c' e i,
          Module.Basis.localizationLocalization_apply]
        exact (c (e.symm i)).2
      rw [show c''.repr y i • c'' i
        = algebraMap (w.restrict E).adicCompletion w.adicCompletion (c''.repr y i) * c'' i
        from Algebra.smul_def _ _]
      refine mul_mem ?_ hci

      obtain ⟨a, ha⟩ : ∃ a : (w.restrict E).adicCompletionIntegers,
          (a : (w.restrict E).adicCompletion) = c''.repr y i := ⟨⟨_, hrepr i⟩, rfl⟩
      rw [← ha]
      exact (algebraMap (w.restrict E).adicCompletionIntegers w.adicCompletionIntegers a).2

end Construct


section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end Headline


end ModularCurve.KwF4gRRTate



end


end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.TensorProduct
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.TensorProduct
open AlgebraicCurve.KwBwnmchRFTDCDischarge

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4R1V384a
open _root_.ModularCurve

section FiberAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

scoped instance kwF4R1V384a_instAlgebraFiberCompletion (v : Place K E) (w' : v.fiber F) :
    Algebra v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kw_ffgc_algebraAdicCompletionComap E w'

scoped instance kwF4R1V384a_instIsScalarTowerFiberCompletion (v : Place K E) (w' : v.fiber F) :
    IsScalarTower E v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  refine IsScalarTower.of_algebraMap_eq fun e => ?_
  rw [show algebraMap E w'.adicCompletion e = algebraMap F w'.adicCompletion (algebraMap E F e)
    from IsScalarTower.algebraMap_apply E F w'.adicCompletion e]
  exact kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w' e

end FiberAlgebra


section SemilocalDiag

variable {K : Type*} (F : Type*) [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

def kwF4R1V384a_semilocalComponent (v : Place K E) (w' : v.fiber F) :
    v.adicCompletion ⊗[E] F →ₐ[v.adicCompletion] w'.1.adicCompletion :=
  Algebra.TensorProduct.lift (Algebra.ofId v.adicCompletion w'.1.adicCompletion)
    (IsScalarTower.toAlgHom E F w'.1.adicCompletion) (fun _ _ => mul_comm _ _)

@[scoped simp]
theorem kwF4R1V384a_semilocalComponent_tmul (v : Place K E) (w' : v.fiber F)
    (c : v.adicCompletion) (g : F) :
    kwF4R1V384a_semilocalComponent F v w' (c ⊗ₜ[E] g)
      = algebraMap v.adicCompletion w'.1.adicCompletion c
          * algebraMap F w'.1.adicCompletion g := by
  unfold kwF4R1V384a_semilocalComponent
  rw [Algebra.TensorProduct.lift_tmul]
  rfl

variable {F}

end SemilocalDiag


section Mint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end Mint


section PerComponentSurjective

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
variable [FiniteDimensional E F]

theorem kwF4R1V384a_completionLinearCombination_surjective
    (w' : Place K F) {ι : Type*} [Fintype ι] (b : Module.Basis ι E F) :
    Function.Surjective (kw_ffgc_completionLinearCombination E w' b) := by
  letI := kw_ffgc_rankOne_adicCompletion (K := K) (w'.restrict E)
  letI : NontriviallyNormedField (w'.restrict E).adicCompletion :=
    Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion
      (WithZero (Multiplicative ℤ))
  rw [← Set.range_eq_univ, ← LinearMap.coe_range,
    ← (LinearMap.range (kw_ffgc_completionLinearCombination E w' b))
        |>.closed_of_finiteDimensional.closure_eq]
  exact (kw_ffgc_denseRange_completionLinearCombination E w' b).closure_range

theorem kwF4R1V384a_semilocalComponent_surjective (v : Place K E) (w' : v.fiber F) :
    Function.Surjective (kwF4R1V384a_semilocalComponent F v w') := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  intro y
  let b := Module.finBasis E F
  obtain ⟨c, hc⟩ := kwF4R1V384a_completionLinearCombination_surjective w' b y
  refine ⟨∑ i, c i ⊗ₜ[E] b i, ?_⟩
  rw [map_sum, ← hc]
  unfold kw_ffgc_completionLinearCombination
  rw [Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kwF4R1V384a_semilocalComponent_tmul, Algebra.smul_def]

end PerComponentSurjective


section SpecificMints

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end SpecificMints


section BijEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

scoped instance kwF4R1V384a_instModuleFiberCompletion
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (v : Place K E) (w' : v.fiber F) :
    Module v.adicCompletion w'.1.adicCompletion :=
  Algebra.toModule

end BijEngine


section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

open FLT.Gapsw7X3xCrossPlaceTraceDecomposition

end Headline


end ModularCurve.KwF4R1V384a



end

end


end


section
section

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsDedekindDomain
open _root_.TensorProduct
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.TensorProduct
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing
open scoped _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place _root_.Valued _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4R1V386a
open _root_.ModularCurve

open ModularCurve.KwF4R1V384a

section IsSeparableLift

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwF4R1V386a_isSeparable_algebraMap_fiberCompletion
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (v : Place K E) (w' : v.fiber F) (g : F) :
    IsSeparable v.adicCompletion (algebraMap F w'.1.adicCompletion g) := by

  have hroot : Polynomial.aeval (R := v.adicCompletion)
      (algebraMap F w'.1.adicCompletion g)
      ((minpoly E g).map (algebraMap E v.adicCompletion)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap,
      show algebraMap F w'.1.adicCompletion g
          = IsScalarTower.toAlgHom E F w'.1.adicCompletion g from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, _root_.map_zero]

  have hmapsep : ((minpoly E g).map (algebraMap E v.adicCompletion)).Separable :=
    Polynomial.Separable.map (Algebra.IsSeparable.isSeparable E g)
  exact hmapsep.of_dvd (minpoly.dvd v.adicCompletion _ hroot)

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 8000000 in

theorem kwF4R1V386a_isSeparable_fiberCompletion
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (v : Place K E) (w' : v.fiber F) :
    Algebra.IsSeparable v.adicCompletion w'.1.adicCompletion := by

  have hgen : Algebra.adjoin v.adicCompletion
      (Set.range (algebraMap F w'.1.adicCompletion)) = ⊤ := by
    rw [Algebra.eq_top_iff]
    intro y
    obtain ⟨x, rfl⟩ := kwF4R1V384a_semilocalComponent_surjective v w' y
    induction x using TensorProduct.induction_on with
    | zero => simp only [_root_.map_zero]; exact zero_mem _
    | tmul c g =>
      rw [kwF4R1V384a_semilocalComponent_tmul, ← Algebra.smul_def]
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self g)) c
    | add x y hx hy => rw [map_add]; exact add_mem hx hy

  have hsep : ∀ x ∈ Set.range (algebraMap F w'.1.adicCompletion),
      IsSeparable v.adicCompletion x := by
    rintro _ ⟨g, rfl⟩
    exact kwF4R1V386a_isSeparable_algebraMap_fiberCompletion v w' g

  have hgenI : IntermediateField.adjoin v.adicCompletion
      (Set.range (algebraMap F w'.1.adicCompletion)) = ⊤ := by
    rw [eq_top_iff]; intro x _
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (hgen ▸ Algebra.mem_top)

  haveI hsepAdj : Algebra.IsSeparable v.adicCompletion
      (IntermediateField.adjoin v.adicCompletion
        (Set.range (algebraMap F w'.1.adicCompletion))) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable v.adicCompletion
      w'.1.adicCompletion).mpr hsep
  rw [hgenI] at hsepAdj
  exact Algebra.IsSeparable.of_algHom v.adicCompletion
    (⊤ : IntermediateField v.adicCompletion w'.1.adicCompletion)
    (IntermediateField.topEquiv (F := v.adicCompletion)
      (E := w'.1.adicCompletion)).symm.toAlgHom

end IsSeparableLift


section DistinctKernels

open scoped _root_.Valued _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Valued _root_.NNReal _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.NNReal _root_.WithZero _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end DistinctKernels


section FinrankCompletionEF

open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.IsLocalRing
open _root_.Valuation
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Valuation

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end FinrankCompletionEF


section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

end Headline


end ModularCurve.KwF4R1V386a



end

end


end


section
section

set_option maxHeartbeats 25600000
set_option synthInstance.maxHeartbeats 9600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable.ModularCurve.KwF4R1V386a

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateTraceCompat)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateTraceCompat)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section IsSeparableLift

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwTateRR3_isSeparable_completion_of_global
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F]
    (w : Place K F) :
    Algebra.IsSeparable (w.restrict E).adicCompletion w.adicCompletion :=
  kwF4R1V386a_isSeparable_fiberCompletion (K := K) (F := F) (E := E)
    (w.restrict E) ⟨w, Place.restrict_mem_fiber w⟩

end IsSeparableLift


section IsTorsionFree

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwTateRR3_isTorsionFree_integersCompletion (w : Place K F) :
    Module.IsTorsionFree (w.restrict E).adicCompletionIntegers w.adicCompletion :=
  .trans_faithfulSMul (w.restrict E).adicCompletionIntegers (w.restrict E).adicCompletion
    w.adicCompletion

end IsTorsionFree


section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

theorem kwTateRR3_integralBasisCompat_of_isSeparable_global [Algebra.IsSeparable E F] :
    KwF4gRRTateIntegralBasisCompat K F E := by
  intro _ _ _ w
  haveI := kwTateRR3_isSeparable_completion_of_global (K := K) (E := E) w
  haveI := kwTateRR3_isTorsionFree_integersCompletion (K := K) (E := E) w
  exact ⟨integralBasisDataOf w⟩

theorem kwTateRR3_traceCompat_of_isSeparable_global [Algebra.IsSeparable E F]
    [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]
    [∀ w : Place K F, w.FiniteResidue] [∀ v : Place K E, v.FiniteResidue]
    (hfinF : KwF4gRRTateCommFinite K F) (hfinE : KwF4gRRTateCommFinite K E) :
    KwF4gRRTateTraceCompat K F E hfinF hfinE :=
  kwF4gRRTate_traceCompat_of_integralBasisCompat hfinF hfinE
    kwTateRR3_integralBasisCompat_of_isSeparable_global

end Headline


end ModularCurve.KwF4gRRTate



end


end


end


theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F] [Algebra.IsSeparable E F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K E] [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue] [∀ v : AlgebraicCurve.Place K E, v.FiniteResidue] (hfinF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F) (hfinE : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K E) : ModularCurve.KwF4gRRTate.KwF4gRRTateTraceCompat K F E hfinF hfinE :=
  ModularCurve.KwF4gRRTate.kwTateRR3_traceCompat_of_isSeparable_global hfinF hfinE

end P2MW.S_AlgebraicCurve_tateTraceCompat_of_isSeparable
