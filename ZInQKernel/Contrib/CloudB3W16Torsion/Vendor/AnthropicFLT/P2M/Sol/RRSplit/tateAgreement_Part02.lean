/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_tateAgreement.lean; source lines 2458-4816.
Includes FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean material:
Copyright (c) 2025 Salvatore Mercuri. Authors: Salvatore Mercuri, Kevin Buzzard.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.tateAgreement_Part01

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_tateAgreement

-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_nonneg_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place.ord_nonneg_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place.mem_of_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place.mem_iff_ord_nonneg


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section Additivity

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end Additivity


section TateCommAddFst

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end TateCommAddFst


section TateResAddFst

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

end TateResAddFst


section CohenMint

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

def KwF4gRRTateCohenTateAgreement : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue],
    ∃ (pC : u.adicCompletion →ₗ[K] u.adicCompletion)
      (hpC : SameRangeIdemProjectors (tateProj u) pC),
    ∀ (fh : u.adicCompletion)
      [FiniteDimensional K (LinearMap.range
        (tateCommRestrict pC (lmulK u fh)
          (lmulK u (algebraMap L u.adicCompletion u.uniformizer))))],
    tateCommTrace pC (lmulK u fh) (lmulK u (algebraMap L u.adicCompletion u.uniformizer))
      = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh)

end CohenMint


section Reprice

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]
variable [∀ u : Place K L, u.FiniteResidue]

theorem kwF4gRRTate_agreement_of_cohenTateAgreement
    (hfin : KwF4gRRTateCommFinite K L)
    (hCTA : KwF4gRRTateCohenTateAgreement K L) :
    KwF4gRRTateAgreement K L hfin := by
  intro u _ fh
  obtain ⟨pC, hpC, hCTA_u⟩ := hCTA u
  set ghπ := algebraMap L u.adicCompletion u.uniformizer
  have hgh : ghπ ∈ u.adicCompletionIntegers :=
    (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr u.uniformizer_mem
  haveI hF1 := hfin u fh ghπ
  haveI hF2 : FiniteDimensional K (LinearMap.range
      (tateCommRestrict pC (lmulK u fh) (lmulK u ghπ))) :=
    kwF4gRRTate_commFiniteGen u pC hpC fh ghπ

  show tateRes u fh ghπ = Algebra.trace K u.ResidueField
    (kwHgfV352_localResidueCompletion u fh)
  unfold tateRes
  rw [kwF4gRRTate_projectorIndep u pC hpC fh ghπ hgh]
  exact hCTA_u fh

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateCommRestrict tateCommRestrict_apply tateCommTrace tateComm_eq_of_commute adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateAgreement)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section CohenKernelData

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

structure TateCohenKernelData (u : Place K L) [u.FiniteResidue] where

  pC : u.adicCompletion →ₗ[K] u.adicCompletion

  pC_idem : ∀ x, pC (pC x) = pC x

  range_pC : LinearMap.range (tateProj u) = LinearMap.range pC

  liftκ : u.ResidueField →ₗ[K] LinearMap.range pC

  liftκ_inj : Function.Injective liftκ

  tateComm_mem_range_liftκ : ∀ (fh : u.adicCompletion) (a : LinearMap.range pC),
    tateCommRestrict pC (lmulK u fh)
      (lmulK u (algebraMap L u.adicCompletion u.uniformizer)) a ∈ LinearMap.range liftκ

  tateComm_liftκ : ∀ (fh : u.adicCompletion) (c : u.ResidueField),
    tateCommRestrict pC (lmulK u fh)
      (lmulK u (algebraMap L u.adicCompletion u.uniformizer)) (liftκ c)
      = liftκ (kwHgfV352_localResidueCompletion u fh * c)

variable {u : Place K L} [u.FiniteResidue]

theorem sameRangeIdemProjectors_of_kernelData (D : TateCohenKernelData u) :
    SameRangeIdemProjectors (tateProj u) D.pC where
  idem_pA x := congrFun (congrArg DFunLike.coe (tateProj_idem u)) x
  idem_pA' := D.pC_idem
  range_eq := D.range_pC

end CohenKernelData


section TraceComputation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]
variable {u : Place K L} [u.FiniteResidue]

theorem tateCommTrace_of_kernelData (D : TateCohenKernelData u) (fh : u.adicCompletion)
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict D.pC (lmulK u fh)
        (lmulK u (algebraMap L u.adicCompletion u.uniformizer))))] :
    tateCommTrace D.pC (lmulK u fh)
        (lmulK u (algebraMap L u.adicCompletion u.uniformizer))
      = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh) := by
  haveI : FiniteDimensional K u.ResidueField := Place.FiniteResidue.finite
  set T := tateCommRestrict D.pC (lmulK u fh)
    (lmulK u (algebraMap L u.adicCompletion u.uniformizer)) with hT
  set W : Submodule K (LinearMap.range D.pC) := LinearMap.range D.liftκ with hW
  haveI hWfin : FiniteDimensional K W := LinearMap.finiteDimensional_range D.liftκ

  have hrange : LinearMap.range T ≤ W := by
    rintro x ⟨a, rfl⟩; exact D.tateComm_mem_range_liftκ fh a

  have hstab : ∀ x ∈ W, T x ∈ W := by
    rintro x ⟨c, rfl⟩
    exact ⟨kwHgfV352_localResidueCompletion u fh * c, (D.tateComm_liftκ fh c).symm⟩

  let e : u.ResidueField ≃ₗ[K] W := LinearEquiv.ofInjective D.liftκ D.liftκ_inj
  have he_apply : ∀ c, ((e c : W) : LinearMap.range D.pC) = D.liftκ c := fun c => rfl

  have hconj : T.restrict hstab
      = e.conj (Algebra.lmul K u.ResidueField
          (kwHgfV352_localResidueCompletion u fh)) := by
    refine LinearMap.ext fun w => ?_
    obtain ⟨c, rfl⟩ := e.surjective w
    apply Subtype.ext
    calc ((T.restrict hstab) (e c) : LinearMap.range D.pC)
        = T ((e c : W) : LinearMap.range D.pC) := rfl
      _ = T (D.liftκ c) := by rw [he_apply]
      _ = D.liftκ (kwHgfV352_localResidueCompletion u fh * c) := D.tateComm_liftκ fh c
      _ = ((e (kwHgfV352_localResidueCompletion u fh * c) : W) : LinearMap.range D.pC) :=
            (he_apply _).symm
      _ = (((e.conj (Algebra.lmul K u.ResidueField
              (kwHgfV352_localResidueCompletion u fh))) (e c) : W)
              : LinearMap.range D.pC) := by
            congr 1
            rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
              LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
            rfl

  calc tateCommTrace D.pC (lmulK u fh)
        (lmulK u (algebraMap L u.adicCompletion u.uniformizer))
      = finrankTrace T := rfl
    _ = LinearMap.trace K W (T.restrict hstab) :=
          finrankTrace_eq_trace_on_superspace T W hrange hstab
    _ = LinearMap.trace K W (e.conj (Algebra.lmul K u.ResidueField
          (kwHgfV352_localResidueCompletion u fh))) := by rw [hconj]
    _ = LinearMap.trace K u.ResidueField (Algebra.lmul K u.ResidueField
          (kwHgfV352_localResidueCompletion u fh)) :=
          LinearMap.trace_conj' (N := ↥W) (Algebra.lmul K u.ResidueField (kwHgfV352_localResidueCompletion u fh)) e
    _ = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh) := rfl

end TraceComputation


section Mint

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

def KwF4gRRTateCohenKernelDataExists : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue], Nonempty (TateCohenKernelData u)

end Mint


section Headline

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

theorem kwF4gRRTate_cohenTateAgreement_of_kernelData
    (hD : KwF4gRRTateCohenKernelDataExists K L) :
    KwF4gRRTateCohenTateAgreement K L := by
  intro u _
  obtain ⟨D⟩ := hD u
  exact ⟨D.pC, sameRangeIdemProjectors_of_kernelData D,
    fun fh _ => tateCommTrace_of_kernelData D fh⟩

theorem kwF4gRRTate_agreement_of_kernelData
    [∀ u : Place K L, u.FiniteResidue]
    (hfin : KwF4gRRTateCommFinite K L)
    (hD : KwF4gRRTateCohenKernelDataExists K L) :
    KwF4gRRTateAgreement K L hfin :=
  kwF4gRRTate_agreement_of_cohenTateAgreement hfin
    (kwF4gRRTate_cohenTateAgreement_of_kernelData hD)

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
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.FunctionField
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.FunctionField
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.KaehlerDifferential
open ModularCurve.GF24a9RRDx
open _root_.ModularCurve.KwF4R1V391a
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4R1V391a
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4R1V392a

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwF4R1V394a
open _root_.ModularCurve

section LinearWrappers

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
variable [Nontrivial Ω[E⁄K]]

theorem kwF4R1V394a_localResidueCompletion_smul
    (v : Place K E) (c : K) (xh : v.adicCompletion) :
    kwHgfV352_localResidueCompletion v (c • xh)
      = c • kwHgfV352_localResidueCompletion v xh := by
  obtain ⟨x, hx⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh

  have halg : algebraMap E v.adicCompletion (c • x)
      = c • algebraMap E v.adicCompletion x := by
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply K E v.adicCompletion,
      ← Algebra.smul_def]
  have hcx : algebraMap E v.adicCompletion (c • x) - c • xh
      ∈ v.adicCompletionIntegers := by
    rw [halg, ← smul_sub, Algebra.smul_def,
      IsScalarTower.algebraMap_apply K E v.adicCompletion c]
    refine mul_mem ?_ hx

    exact (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff v _).mpr
      (v.algebraMap_mem' c)
  rw [kwHgfV352_localResidueCompletion_spec v _ hcx,
    kwHgfV352_localResidueCompletion_spec v _ hx, map_smul]

end LinearWrappers


section OrdCompat

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

variable {K F E}
variable [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
variable [Nontrivial Ω[E⁄K]]

end OrdCompat


section Recursion

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
variable [Nontrivial Ω[E⁄K]]

variable [Nontrivial Ω[F⁄K]]

end Recursion


section MonomialMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end MonomialMint


section Engine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

end Engine


end ModularCurve.KwF4R1V394a



end

end


end


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.Lg37
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Lg37
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4R1V410a

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwTateRR3
open _root_.ModularCurve

section CohenSectionHat

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def cohenSectionHat (u : Place K L) (S : Lg37CompletionSection u) :
    u.ResidueField →ₐ[K] u.adicCompletion where
  toRingHom :=
    (u.adicCompletionIntegers.subtype).comp
      ((kwF4R1V410a_ringEquiv u).toRingHom.comp S.lift.toRingHom)
  commutes' c := by
    show ((kwF4R1V410a_ringEquiv u (S.lift (algebraMap K u.ResidueField c))
        : u.adicCompletionIntegers) : u.adicCompletion)
      = algebraMap K u.adicCompletion c
    rw [S.lift.commutes c,
      IsScalarTower.algebraMap_apply K u.toValuationSubring (lg37_completion u) c,
      kwF4R1V410a_ringEquiv_of u,
      IsScalarTower.algebraMap_apply K L u.adicCompletion c]
    rfl

theorem cohenSectionHat_apply (u : Place K L) (S : Lg37CompletionSection u)
    (a : u.ResidueField) :
    cohenSectionHat u S a
      = ((kwF4R1V410a_ringEquiv u (S.lift a) : u.adicCompletionIntegers)
          : u.adicCompletion) := rfl

theorem cohenSectionHat_mem_integers (u : Place K L) (S : Lg37CompletionSection u)
    (a : u.ResidueField) :
    cohenSectionHat u S a ∈ u.adicCompletionIntegers :=
  (kwF4R1V410a_ringEquiv u (S.lift a)).2

theorem cohenSectionHat_mem_adicIntegersKSubmod (u : Place K L)
    (S : Lg37CompletionSection u) (a : u.ResidueField) :
    cohenSectionHat u S a ∈ adicIntegersKSubmod u :=
  cohenSectionHat_mem_integers u S a

theorem cohenSectionHat_injective (u : Place K L) (S : Lg37CompletionSection u) :
    Function.Injective (cohenSectionHat u S) :=
  (cohenSectionHat u S).toRingHom.injective

end CohenSectionHat


section CohenProjC

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

def cohenProjC (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) :
    u.adicCompletion →ₗ[K] u.adicCompletion :=
  (adicIntegersKSubmod u).subtype ∘ₗ Submodule.projectionOnto (adicIntegersKSubmod u) B hcompl

theorem cohenProjC_mem_integers (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) (x : u.adicCompletion) :
    cohenProjC u B hcompl x ∈ u.adicCompletionIntegers :=
  (Submodule.projectionOnto (adicIntegersKSubmod u) B hcompl x).2

theorem cohenProjC_of_mem (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) {x : u.adicCompletion}
    (hx : x ∈ u.adicCompletionIntegers) :
    cohenProjC u B hcompl x = x :=
  congrArg Subtype.val (Submodule.projectionOnto_apply_left hcompl ⟨x, hx⟩)

theorem cohenProjC_of_mem_B (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) {x : u.adicCompletion}
    (hx : x ∈ B) :
    cohenProjC u B hcompl x = 0 :=
  congrArg Subtype.val (Submodule.projectionOnto_apply_right hcompl ⟨x, hx⟩)

theorem cohenProjC_idem (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) (x : u.adicCompletion) :
    cohenProjC u B hcompl (cohenProjC u B hcompl x) = cohenProjC u B hcompl x :=
  cohenProjC_of_mem u B hcompl (cohenProjC_mem_integers u B hcompl x)

theorem range_cohenProjC (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) :
    LinearMap.range (cohenProjC u B hcompl) = adicIntegersKSubmod u :=
  le_antisymm (fun x ⟨y, hy⟩ => hy ▸ cohenProjC_mem_integers u B hcompl y)
    (fun x hx => ⟨x, cohenProjC_of_mem u B hcompl hx⟩)

theorem sub_cohenProjC_mem_B (B : Submodule K u.adicCompletion)
    (hcompl : IsCompl (adicIntegersKSubmod u) B) (x : u.adicCompletion) :
    x - cohenProjC u B hcompl x ∈ B := by
  have htop : x ∈ adicIntegersKSubmod u ⊔ B := by
    rw [hcompl.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp htop
  subst hab
  rw [map_add, cohenProjC_of_mem u B hcompl ha,
    cohenProjC_of_mem_B u B hcompl hb, add_zero, add_sub_cancel_left]
  exact hb

end CohenProjC


section SingleTerm

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (B : Submodule K u.adicCompletion) (hcompl : IsCompl (adicIntegersKSubmod u) B)

theorem cohenTateCommRestrict_single_term (fh : u.adicCompletion)
    (a : LinearMap.range (cohenProjC u B hcompl)) :
    (tateCommRestrict (cohenProjC u B hcompl) (lmulK u fh)
        (lmulK u (algebraMap L u.adicCompletion u.uniformizer)) a
      : u.adicCompletion)
    = cohenProjC u B hcompl
        (algebraMap L u.adicCompletion u.uniformizer
          * (fh * (a : u.adicCompletion)
              - cohenProjC u B hcompl (fh * (a : u.adicCompletion)))) := by
  have haInt : (a : u.adicCompletion) ∈ u.adicCompletionIntegers :=
    (range_cohenProjC u B hcompl ▸ a.2 :
      (a : u.adicCompletion) ∈ adicIntegersKSubmod u)
  have hπ : algebraMap L u.adicCompletion u.uniformizer ∈ u.adicCompletionIntegers :=
    (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr u.uniformizer_mem
  have hcomm : lmulK u fh ∘ₗ lmulK u (algebraMap L u.adicCompletion u.uniformizer)
      = lmulK u (algebraMap L u.adicCompletion u.uniformizer) ∘ₗ lmulK u fh := by
    refine LinearMap.ext fun x => ?_
    show fh * (algebraMap L u.adicCompletion u.uniformizer * x) =
      algebraMap L u.adicCompletion u.uniformizer * (fh * x)
    ring
  rw [tateCommRestrict_apply, tateComm_eq_of_commute hcomm]

  show cohenProjC u B hcompl (_ * (fh * ↑a - cohenProjC u B hcompl (fh * ↑a)))
      - cohenProjC u B hcompl (fh * (_ * ↑a - cohenProjC u B hcompl (_ * ↑a)))
    = cohenProjC u B hcompl (_ * (fh * ↑a - cohenProjC u B hcompl (fh * ↑a)))
  rw [cohenProjC_of_mem u B hcompl (mul_mem hπ haInt), sub_self, mul_zero, _root_.map_zero, sub_zero]

end SingleTerm


section CohenLaurentSpec

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

structure KwTateRR3CohenLaurentSpec (u : Place K L) [u.FiniteResidue] where

  S : Lg37CompletionSection u

  B : Submodule K u.adicCompletion

  hcompl : IsCompl (adicIntegersKSubmod u) B

  ε : B →ₗ[K] u.ResidueField

  shift_sub_mem : ∀ z : B,
    algebraMap L u.adicCompletion u.uniformizer * (z : u.adicCompletion)
      - cohenSectionHat u S (ε z) ∈ B

  ε_principalPart_mul_sectionHat : ∀ (fh : u.adicCompletion) (c : u.ResidueField),
    ε ⟨fh * cohenSectionHat u S c
          - cohenProjC u B hcompl (fh * cohenSectionHat u S c),
        sub_cohenProjC_mem_B u B hcompl _⟩
      = kwHgfV352_localResidueCompletion u fh * c

variable {u : Place K L} [u.FiniteResidue] (D : KwTateRR3CohenLaurentSpec u)

theorem cohenProjC_uniformizer_mul_of_mem_B {x : u.adicCompletion} (hx : x ∈ D.B) :
    cohenProjC u D.B D.hcompl
        (algebraMap L u.adicCompletion u.uniformizer * x)
      = cohenSectionHat u D.S (D.ε ⟨x, hx⟩) := by
  have hsplit : algebraMap L u.adicCompletion u.uniformizer * x
      = cohenSectionHat u D.S (D.ε ⟨x, hx⟩)
        + (algebraMap L u.adicCompletion u.uniformizer * x
            - cohenSectionHat u D.S (D.ε ⟨x, hx⟩)) := (add_sub_cancel _ _).symm
  rw [hsplit, map_add, cohenProjC_of_mem u D.B D.hcompl
      (cohenSectionHat_mem_integers u D.S _),
    cohenProjC_of_mem_B u D.B D.hcompl (D.shift_sub_mem ⟨x, hx⟩), add_zero]

end CohenLaurentSpec


section Construct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]
variable {u : Place K L} [u.FiniteResidue]

def cohenLiftκ (D : KwTateRR3CohenLaurentSpec u) :
    u.ResidueField →ₗ[K] LinearMap.range (cohenProjC u D.B D.hcompl) where
  toFun c := ⟨cohenSectionHat u D.S c,
    (range_cohenProjC u D.B D.hcompl).symm ▸
      cohenSectionHat_mem_adicIntegersKSubmod u D.S c⟩
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' r a := Subtype.ext ((cohenSectionHat u D.S).toLinearMap.map_smul r a)

theorem cohenLiftκ_coe (D : KwTateRR3CohenLaurentSpec u) (c : u.ResidueField) :
    ((cohenLiftκ D c : LinearMap.range (cohenProjC u D.B D.hcompl)) : u.adicCompletion)
      = cohenSectionHat u D.S c := rfl

theorem cohenLiftκ_injective (D : KwTateRR3CohenLaurentSpec u) :
    Function.Injective (cohenLiftκ D) := by
  intro a b hab
  have hval : cohenSectionHat u D.S a = cohenSectionHat u D.S b :=
    (cohenLiftκ_coe D a).symm.trans
      ((congrArg Subtype.val hab).trans (cohenLiftκ_coe D b))
  exact cohenSectionHat_injective u D.S hval

def tateCohenKernelData_of_cohenLaurentSpec (D : KwTateRR3CohenLaurentSpec u) :
    TateCohenKernelData u where
  pC := cohenProjC u D.B D.hcompl
  pC_idem := cohenProjC_idem u D.B D.hcompl
  range_pC := (range_tateProj u).trans (range_cohenProjC u D.B D.hcompl).symm
  liftκ := cohenLiftκ D
  liftκ_inj := cohenLiftκ_injective D
  tateComm_mem_range_liftκ fh a := by

    have hmem := sub_cohenProjC_mem_B u D.B D.hcompl (fh * (a : u.adicCompletion))
    refine ⟨D.ε ⟨_, hmem⟩, ?_⟩
    apply Subtype.ext
    rw [cohenLiftκ_coe, cohenTateCommRestrict_single_term u D.B D.hcompl fh a,
      cohenProjC_uniformizer_mul_of_mem_B D hmem]
  tateComm_liftκ fh c := by
    apply Subtype.ext
    have hmem := sub_cohenProjC_mem_B u D.B D.hcompl (fh * cohenSectionHat u D.S c)
    rw [cohenLiftκ_coe, cohenTateCommRestrict_single_term u D.B D.hcompl fh (cohenLiftκ D c),
      cohenLiftκ_coe, cohenProjC_uniformizer_mul_of_mem_B D hmem]
    congr 1
    exact D.ε_principalPart_mul_sectionHat fh c

end Construct


section Mint

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

def KwTateRR3CohenLaurentSpecExists : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue], Nonempty (KwTateRR3CohenLaurentSpec u)

end Mint


section Headline

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

theorem kwTateRR3_cohenKernelDataExists_of_cohenLaurentSpec
    (hD : KwTateRR3CohenLaurentSpecExists K L) :
    KwF4gRRTateCohenKernelDataExists K L := fun u _ =>
  (hD u).map tateCohenKernelData_of_cohenLaurentSpec

end Headline


end ModularCurve.KwTateRR3



end


end


end


section
section

set_option maxHeartbeats 6400000

open _root_.Polynomial
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Polynomial
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.KaehlerDifferential
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.KaehlerDifferential
open _root_.ModularCurve.Lg37
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Lg37
open _root_.ModularCurve.KwNo6Pin
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwNo6Pin
open _root_.ModularCurve.KwNo6Section
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwNo6Section
open _root_.ModularCurve.Mp72a102T3
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Mp72a102T3

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwNo6HrouteR
open _root_.ModularCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem aCoeff_sub (v : Place K F) (S : Lg37CompletionSection v) (m : ℕ)
    (x y : lg37_completion v) :
    aCoeff v S m (x - y) = aCoeff v S m x - aCoeff v S m y := by
  rw [eq_sub_iff_add_eq, ← aCoeff_add, sub_add_cancel]

theorem aCoeff_uniformizerHat_pow_mul_eq_zero_of_lt (v : Place K F)
    (S : Lg37CompletionSection v) {k m : ℕ} (hk : k < m)
    (x : lg37_completion v) :
    aCoeff v S k ((algebraMap v.toValuationSubring (lg37_completion v)
      v.uniformizerSubring) ^ m * x) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
  rw [show k + j + 1 = k + (j + 1) from by omega, pow_add, mul_assoc]
  have hsh := aCoeff_shift_pow v S 0 k
    ((algebraMap v.toValuationSubring (lg37_completion v)
      v.uniformizerSubring) ^ (j + 1) * x)
  rw [Nat.zero_add] at hsh
  rw [hsh, aCoeff_zero]

  show lg37_residueHat v _ = 0
  rw [pow_succ', mul_assoc, map_mul, lg37_residueHat_algebraMap,
    (IsLocalRing.residue_eq_zero_iff _).mpr v.uniformizerSubring_mem_maximalIdeal, zero_mul]

theorem taylor_choose_eq_aCoeff (v : Place K F) (S : Lg37CompletionSection v)
    (n : ℕ) (x : lg37_completion v) {k : ℕ} (hk : k < n) :
    Classical.choose (mp72a102_t3_sigma_taylor_expansion v S n x) k = aCoeff v S k x := by
  set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S n x)
  have hcc := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S n x)
  set cc' := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (k + 1) x) with hcc'_def
  have hcc' := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (k + 1) x)

  have hfac := mp72a102_t3_evalₐ_factor (maximalIdeal v.toValuationSubring) hk
    (x - ∑ i ∈ Finset.range n, S.lift (cc i)
      * algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring ^ i)
  rw [hcc, _root_.map_zero] at hfac
  have htail : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (k + 1)
      (∑ i ∈ Finset.Ico (k + 1) n, S.lift (cc i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Finset.mem_Ico.mp hi).1
    have heq : S.lift (cc (k + 1 + j))
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ (k + 1 + j)
        = algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ (k + 1)
          * (algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ j * S.lift (cc (k + 1 + j))) := by
      rw [pow_add]; ring
    rw [heq]
    exact Mp72a103T2.mp72a103_t2_evalDepth_pow_uniformizer_mul_eq_zero v (k + 1) _
  have hhead : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (k + 1)
      (x - ∑ i ∈ Finset.range (k + 1), S.lift (cc i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have hsplit : x - ∑ i ∈ Finset.range (k + 1), S.lift (cc i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i
        = (x - ∑ i ∈ Finset.range n, S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          + ∑ i ∈ Finset.Ico (k + 1) n, S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i := by
      rw [show Finset.range n = Finset.range (k + 1) ∪ Finset.Ico (k + 1) n from by
          simp only [Finset.range_eq_Ico]
          exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) hk).symm,
        Finset.sum_union (by
          rw [Finset.range_eq_Ico]; exact Finset.Ico_disjoint_Ico_consecutive 0 (k + 1) n)]
      ring
    rw [hsplit, map_add, ← hfac, htail, add_zero]

  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (k + 1)
      (∑ i ∈ Finset.range (k + 1), S.lift ((fun i => cc' i - cc i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (k + 1), S.lift (cc' i - cc i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = (x - ∑ i ∈ Finset.range (k + 1), S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          - (x - ∑ i ∈ Finset.range (k + 1), S.lift (cc' i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hhead, hcc', sub_zero]
  have hzero := Mp72a103T2.mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (k + 1)
    (fun i => cc' i - cc i) key k (Nat.lt_succ_self k)
  have h := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hcc'_def]
  exact h

theorem exists_approximant (v : Place K F) (S : Lg37CompletionSection v)
    (a : v.ResidueField) (M : ℕ) :
    ∃ ℓ : v.toValuationSubring, IsLocalRing.residue _ ℓ = a
      ∧ ∀ k, 1 ≤ k → k ≤ M →
        aCoeff v S k (algebraMap v.toValuationSubring (lg37_completion v) ℓ) = 0 := by
  induction M with
  | zero =>
    obtain ⟨ℓ, hℓ⟩ := IsLocalRing.residue_surjective a
    exact ⟨ℓ, hℓ, fun k hk1 hk0 => absurd (hk1.trans hk0) (by omega)⟩
  | succ M ih =>
    obtain ⟨ℓ, hres, hvan⟩ := ih

    set b := aCoeff v S (M + 1)
      (algebraMap v.toValuationSubring (lg37_completion v) ℓ) with hb
    obtain ⟨n, hn⟩ := IsLocalRing.residue_surjective b
    refine ⟨ℓ - n * v.uniformizerSubring ^ (M + 1), ?_, ?_⟩
    · rw [map_sub, map_mul, map_pow, hres, sub_eq_self, mul_eq_zero]
      right
      exact pow_eq_zero_iff (by omega) |>.mpr
        ((IsLocalRing.residue_eq_zero_iff _).mpr v.uniformizerSubring_mem_maximalIdeal)
    · intro k hk1 hkM
      rw [map_sub, map_mul, map_pow, aCoeff_sub,
        mul_comm (algebraMap _ _ n) _]
      rcases Nat.lt_or_ge k (M + 1) with hk | hk
      ·
        rw [hvan k hk1 (Nat.lt_succ_iff.mp hk),
          aCoeff_uniformizerHat_pow_mul_eq_zero_of_lt v S hk, sub_zero]
      ·
        have hkeq : k = M + 1 := le_antisymm hkM hk
        subst hkeq
        rw [← hb]
        have hsh := aCoeff_shift_pow v S 0 (M + 1)
          (algebraMap v.toValuationSubring (lg37_completion v) n)
        rw [Nat.zero_add] at hsh
        rw [hsh, aCoeff_zero, lg37_residueHat_algebraMap, hn, sub_self]

section Separability

variable [HasCanonicalLocalResidueKStar K F]
variable (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

end Separability


attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

end ModularCurve.KwNo6HrouteR



end


end


end


section
section

open scoped _root_.PadicInt _root_.P2MW.S_AlgebraicCurve_tateAgreement.PadicInt _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicGeometry
open _root_.BigOperators
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.BigOperators
open _root_.CategoryTheory
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.CategoryTheory
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.CategoryTheory
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicGeometry
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.NeronModelInfra
open _root_.ModularCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwOdaDHDR
open _root_.Order
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Order
open _root_.Topology
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Topology
open FLT.HopfSpec GoodReductionJacobian
open Deformation.PDivisible Deformation.ModpDieudonne
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Module
open _root_.CongruenceSubgroup
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.CongruenceSubgroup
open NeronOggShafarevich
open AlgebraicGeometry.KwSmoothIrredRelDimConstantEngine
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.RationalFunctionField
open scoped _root_.TensorProduct _root_.P2MW.S_AlgebraicCurve_tateAgreement.TensorProduct
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IntermediateField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.RationalFunctionField
open ModularCurve.KwNo6HrouteV
open ModularCurve.KwNo6HrouteY
open ModularCurve.KwNo6HrouteZ
open ModularCurve.GF24a9RRDx
open ModularCurve.GF24a12CohenSupply
open Ldgr30BankGate
open Modularity.Ldgr27TraceSemilinearSlice
open Ldgr24DefectKernelSlice
open Ldgr23CohenDefectCorrectionSlice
open ModularCurve.Ldgr25PlaceExtensionSlice
open Ldgr25CorrectedChoiceSlice
open Modularity.Ldgr26CorrectedRowsBandSlice
open ModularCurve.GF24a11bRowACurrencyBridge
open ModularCurve.GF24a12CohenSupply
open ModularCurve.Ldgr32RegularLegSlice
open ModularCurve.Ldgr31PerPlaceRowJoinSlice
open ModularCurve.Ldgr29SimplePoleResidueSlice
open ModularCurve.Ldgr25CotraceCompatSlice
open AlgebraicCurve.FiberKaehlerLocalDatum
open ModularCurve.KwNo6HrouteS
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.ModularCurve.KwNo6Pin
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwNo6Pin
open ModularCurve.KwNo6HrouteR
open _root_.ModularCurve.Lg37
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Lg37
open _root_.ModularCurve.Mp72a102T3
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Mp72a102T3
open _root_.Mp72a103T2
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Mp72a103T2
open _root_.Mp72a102T1
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Mp72a102T1
open _root_.ModularCurve.KwNo6Section
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwNo6Section
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing
open _root_.Module.IsLocalRing
open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_tateAgreement.Polynomial _root_.AlgebraicGeometry.Polynomial

noncomputable section

section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwOdaDHDR
open _root_.ModularCurve

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem kwHgf_v277_aCoeff_section_lift_mul (v : Place K F)
    (S : Lg37CompletionSection v) (m : ℕ) (a : v.ResidueField)
    (x : lg37_completion v) :
    aCoeff v S m (S.lift a * x) = a * aCoeff v S m x := by
  have hx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
  have hax' := Classical.choose_spec
    (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (S.lift a * x))
  set ax := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
    with hax_def
  set aax := Classical.choose
    (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (S.lift a * x)) with haax_def

  have hsmul : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      ((S.lift a * x)
        - ∑ i ∈ Finset.range (m + 1),
            S.lift ((fun i => a * ax i) i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
    have e : (S.lift a * x)
          - ∑ i ∈ Finset.range (m + 1), S.lift (a * ax i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
        = S.lift a
          * (x - ∑ i ∈ Finset.range (m + 1), S.lift (ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_mul, mul_assoc]
    rw [e, mp72a102_t3_evalDepth_mul, hx, mul_zero]

  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      (∑ i ∈ Finset.range (m + 1),
          S.lift ((fun i => a * ax i - aax i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (m + 1),
            S.lift (a * ax i - aax i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((S.lift a * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (aax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          - ((S.lift a * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (a * ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hax', hsmul, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (m + 1)
    (fun i => a * ax i - aax i) key m (Nat.lt_succ_self m)
  have han : aax m = a * ax m := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hax_def, ← haax_def]
  exact han

end Generic


end ModularCurve.KwOdaDHDR



end


end


end


end


section
section

open scoped _root_.PadicInt _root_.P2MW.S_AlgebraicCurve_tateAgreement.PadicInt _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicGeometry
open _root_.BigOperators
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.BigOperators
open _root_.CategoryTheory
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.CategoryTheory
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.CategoryTheory
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicGeometry
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.NeronModelInfra
open _root_.ModularCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwOdaDHDR
open _root_.Order
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Order
open _root_.Topology
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Topology
open FLT.HopfSpec GoodReductionJacobian
open Deformation.PDivisible Deformation.ModpDieudonne
open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.Module
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Module
open _root_.CongruenceSubgroup
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.CongruenceSubgroup
open NeronOggShafarevich
open AlgebraicGeometry.KwSmoothIrredRelDimConstantEngine
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.RationalFunctionField
open scoped _root_.TensorProduct _root_.P2MW.S_AlgebraicCurve_tateAgreement.TensorProduct
open _root_.IntermediateField
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IntermediateField
open _root_.AlgebraicCurve.RationalFunctionField
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.RationalFunctionField
open ModularCurve.KwNo6HrouteV
open ModularCurve.KwNo6HrouteY
open ModularCurve.KwNo6HrouteZ
open ModularCurve.GF24a9RRDx
open ModularCurve.GF24a12CohenSupply
open Ldgr30BankGate
open Modularity.Ldgr27TraceSemilinearSlice
open Ldgr24DefectKernelSlice
open Ldgr23CohenDefectCorrectionSlice
open ModularCurve.Ldgr25PlaceExtensionSlice
open Ldgr25CorrectedChoiceSlice
open Modularity.Ldgr26CorrectedRowsBandSlice
open ModularCurve.GF24a11bRowACurrencyBridge
open ModularCurve.GF24a12CohenSupply
open ModularCurve.Ldgr32RegularLegSlice
open ModularCurve.Ldgr31PerPlaceRowJoinSlice
open ModularCurve.Ldgr29SimplePoleResidueSlice
open ModularCurve.Ldgr25CotraceCompatSlice
open AlgebraicCurve.FiberKaehlerLocalDatum
open ModularCurve.KwNo6HrouteS
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.ModularCurve.KwNo6Pin
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwNo6Pin
open ModularCurve.KwNo6HrouteR
open _root_.ModularCurve.Lg37
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Lg37
open _root_.ModularCurve.Mp72a102T3
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Mp72a102T3
open _root_.Mp72a103T2
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Mp72a103T2
open _root_.Mp72a102T1
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Mp72a102T1
open _root_.ModularCurve.KwNo6Section
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwNo6Section
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing
open _root_.Module.IsLocalRing
open scoped _root_.Polynomial _root_.P2MW.S_AlgebraicCurve_tateAgreement.Polynomial _root_.AlgebraicGeometry.Polynomial

noncomputable section

section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwOdaDHDR
open _root_.ModularCurve

attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem kwHgf_v278_aCoeff_eq_zero_of_evalDepth_zero (v : Place K F)
    (S : Lg37CompletionSection v) {n : ℕ} (w : lg37_completion v)
    (hw : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n w = 0)
    {k : ℕ} (hk : k < n) :
    aCoeff v S k w = 0 := by
  have hspec := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S n w)
  set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S n w) with hcc_def
  have hsum : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
      (∑ i ∈ Finset.range n, S.lift ((fun i => cc i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e : (∑ i ∈ Finset.range n, S.lift (cc i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = w - (w - ∑ i ∈ Finset.range n, S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by ring
    simp only at e ⊢
    rw [e, map_sub, hw, hspec, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S n
    (fun i => cc i) hsum k hk
  rw [← taylor_choose_eq_aCoeff v S n w hk, ← hcc_def]
  exact hzero

theorem kwHgf_v278_resStar_approximant_mul (v : Place K F)
    (S : Lg37CompletionSection v) (ℓ : v.toValuationSubring) (M : ℕ)
    (hvan : ∀ k, 1 ≤ k → k ≤ M →
      aCoeff v S k (algebraMap v.toValuationSubring (lg37_completion v) ℓ) = 0)
    (g : F) (hg : g ∈ v.poleSubmodule (M + 1)) :
    resStar v S ((ℓ : F) * g) = IsLocalRing.residue _ ℓ * resStar v S g := by
  set a := IsLocalRing.residue _ ℓ with ha

  have hgN : (-v.ord g).toNat ≤ M + 1 := by
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [v.ord_zero]; simp
    · have := (v.mem_poleSubmodule_iff_ord hg0).mp hg
      omega
  have hlgN : (-v.ord ((ℓ : F) * g)).toNat ≤ M + 1 := by
    rcases eq_or_ne ((ℓ : F) * g) 0 with h0 | hlg0
    · rw [h0, v.ord_zero]; simp
    · have hg0 : g ≠ 0 := right_ne_zero_of_mul hlg0
      have hl0 : (ℓ : F) ≠ 0 := left_ne_zero_of_mul hlg0
      have hge := (v.mem_poleSubmodule_iff_ord hg0).mp hg
      have hlge : (0 : ℤ) ≤ v.ord (ℓ : F) := (v.mem_iff_ord_nonneg hl0).mp ℓ.2
      rw [v.ord_mul hl0 hg0]
      omega

  rw [← aCoeff_clearedHat_of_le v S ((ℓ : F) * g) hlgN,
    ← aCoeff_clearedHat_of_le v S g hgN]
  set x := clearedHat v g hgN with hx_def
  have hιℓx : clearedHat v ((ℓ : F) * g) hlgN
      = algebraMap v.toValuationSubring (lg37_completion v) ℓ * x := by
    rw [hx_def]
    unfold clearedHat
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    push_cast
    ring
  rw [hιℓx]

  have hsplit : algebraMap v.toValuationSubring (lg37_completion v) ℓ * x
      = S.lift a * x
        + (algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a) * x := by
    ring
  rw [hsplit, aCoeff_add]

  rw [kwHgf_v277_aCoeff_section_lift_mul v S (M + 1) a x]

  suffices hsnd : aCoeff v S (M + 1)
      ((algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a) * x)
      = 0 by rw [hsnd, add_zero]

  set x' := algebraMap v.toValuationSubring (lg37_completion v)
    ⟨v.uniformizer ^ (M + 1) * g, (v.mem_poleSubmodule).mp hg⟩ with hx'_def
  have hxfac : x = algebraMap v.toValuationSubring (lg37_completion v)
      v.uniformizerSubring * x' := by
    rw [hx_def, hx'_def]
    unfold clearedHat
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    ring
  rw [hxfac, show
    (algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a)
        * (algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring * x')
      = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
        * ((algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a)
          * x') from by ring,
    aCoeff_shift]

  have hev : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (M + 1)
      (algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a) = 0 := by
    have hspec := Classical.choose_spec
      (mp72a102_t3_sigma_taylor_expansion v S (M + 1)
        (algebraMap v.toValuationSubring (lg37_completion v) ℓ))
    set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (M + 1)
        (algebraMap v.toValuationSubring (lg37_completion v) ℓ)) with hcc_def
    have hcc : ∀ k, k < M + 1 → cc k
        = aCoeff v S k (algebraMap v.toValuationSubring (lg37_completion v) ℓ) :=
      fun k hk => hcc_def ▸ taylor_choose_eq_aCoeff v S (M + 1) _ hk
    suffices hsum : (∑ i ∈ Finset.range (M + 1), S.lift (cc i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = S.lift a by
      rw [← hsum]; exact hspec
    rw [Finset.sum_eq_single 0
      (fun i hi hi0 => by
        rw [hcc i (Finset.mem_range.mp hi),
          hvan i (Nat.one_le_iff_ne_zero.mpr hi0)
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
          _root_.map_zero, zero_mul])
      (fun h => absurd (Finset.mem_range.mpr (by omega)) h),
      pow_zero, mul_one, hcc 0 (by omega), aCoeff_zero,
      lg37_residueHat_algebraMap, ← ha]

  exact kwHgf_v278_aCoeff_eq_zero_of_evalDepth_zero v S
    ((algebraMap v.toValuationSubring (lg37_completion v) ℓ - S.lift a) * x')
    (by rw [map_mul, hev, zero_mul]) (Nat.lt_succ_self M)

end Generic


end ModularCurve.KwOdaDHDR



end


end


end


end


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.Lg37
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Lg37
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4R1V410a
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwTateRR3
open _root_.ModularCurve.KwNo6Pin
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwNo6Pin
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwNo6HrouteR
open _root_.ModularCurve.Mp72a102T3
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Mp72a102T3
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwOdaDHDR
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4R1V394a
open _root_.Mp72a103T2
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Mp72a103T2
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain.HeightOneSpectrum
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.WithZero

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwTateRR3
open _root_.ModularCurve

section ApproximantHev

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem approximant_evalₐ_sub_lift_eq_zero (u : Place K L) (S : Lg37CompletionSection u)
    {ℓ : u.toValuationSubring} {M : ℕ}
    (hvan : ∀ k, 1 ≤ k → k ≤ M →
      aCoeff u S k (algebraMap u.toValuationSubring (lg37_completion u) ℓ) = 0) :
    AdicCompletion.evalₐ (maximalIdeal u.toValuationSubring) (M + 1)
      (algebraMap u.toValuationSubring (lg37_completion u) ℓ
        - S.lift (IsLocalRing.residue _ ℓ)) = 0 := by
  set a := IsLocalRing.residue _ ℓ with ha
  have hspec := Classical.choose_spec
    (mp72a102_t3_sigma_taylor_expansion u S (M + 1)
      (algebraMap u.toValuationSubring (lg37_completion u) ℓ))
  set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion u S (M + 1)
      (algebraMap u.toValuationSubring (lg37_completion u) ℓ)) with hcc_def
  have hcc : ∀ k, k < M + 1 → cc k
      = aCoeff u S k (algebraMap u.toValuationSubring (lg37_completion u) ℓ) :=
    fun k hk => hcc_def ▸ taylor_choose_eq_aCoeff u S (M + 1) _ hk
  suffices hsum : (∑ i ∈ Finset.range (M + 1), S.lift (cc i)
      * algebraMap u.toValuationSubring (lg37_completion u)
          u.uniformizerSubring ^ i) = S.lift a by
    rw [← hsum]; exact hspec
  rw [Finset.sum_eq_single 0
    (fun i hi hi0 => by
      rw [hcc i (Finset.mem_range.mp hi),
        hvan i (Nat.one_le_iff_ne_zero.mpr hi0)
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)),
        _root_.map_zero, zero_mul])
    (fun h => absurd (Finset.mem_range.mpr (by omega)) h),
    pow_zero, mul_one, hcc 0 (by omega), aCoeff_zero,
    lg37_residueHat_algebraMap, ← ha]

end ApproximantHev


section V410aBridge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem v410a_mem_completionIdeal_pow_of_evalₐ_eq_zero (n : ℕ)
    (z : lg37_completion u)
    (hz : AdicCompletion.evalₐ (maximalIdeal u.toValuationSubring) n z = 0) :
    kwF4R1V410a_ringEquiv u z ∈ (u.heightOneSpectrum.completionIdeal L) ^ n := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, kwF4R1V410a_ringEquiv_apply,
    kwF4R1V410a_mk_forward u n z, hz, _root_.map_zero]

theorem valued_algebraMap_uniformizer :
    Valued.v (algebraMap L u.adicCompletion u.uniformizer) = WithZero.exp (-1 : ℤ) := by
  rw [show algebraMap L u.adicCompletion u.uniformizer
      = ((u.uniformizer : L) : u.adicCompletion) from rfl,
    valuedAdicCompletion_eq_valuation' (K := L) u.heightOneSpectrum,
    show u.heightOneSpectrum.valuation L u.uniformizer = u.adicValuation u.uniformizer
      from rfl,
    show u.adicValuation u.uniformizer = WithZero.exp (-(u.ord u.uniformizer)) from by
      rw [Place.ord, neg_neg,
        WithZero.exp_log (u.adicValuation_ne_zero u.uniformizer_ne_zero)],
    u.ord_uniformizer]

theorem v410a_evalDepth_mul_mem_integers (n : ℕ) (z : lg37_completion u)
    (hz : AdicCompletion.evalₐ (maximalIdeal u.toValuationSubring) n z = 0)
    (fh : u.adicCompletion)
    (hfh : (algebraMap L u.adicCompletion u.uniformizer)^n * fh ∈ u.adicCompletionIntegers) :
    ((kwF4R1V410a_ringEquiv u z : u.adicCompletionIntegers) : u.adicCompletion) * fh
      ∈ u.adicCompletionIntegers := by
  rw [mem_adicCompletionIntegers, map_mul]

  have hzmem := v410a_mem_completionIdeal_pow_of_evalₐ_eq_zero u n z hz
  have hzval : Valued.v
      ((kwF4R1V410a_ringEquiv u z : u.adicCompletionIntegers) : u.adicCompletion)
      ≤ WithZero.exp (-(n : ℤ)) := by
    rw [WithZero.exp_eq_coe_ofAdd]
    exact (adicCompletion.mem_completionIdeal_pow L u.heightOneSpectrum
      (kwF4R1V410a_ringEquiv u z)).mp hzmem

  have hπval : Valued.v ((algebraMap L u.adicCompletion u.uniformizer)^n)
      = WithZero.exp (-(n : ℤ)) := by
    rw [map_pow, valued_algebraMap_uniformizer u, ← WithZero.exp_nsmul]
    congr 1; ring
  have hfhval : Valued.v fh ≤ WithZero.exp (n : ℤ) := by
    have h1 : Valued.v ((algebraMap L u.adicCompletion u.uniformizer)^n * fh) ≤ 1 := hfh
    rw [map_mul, hπval] at h1
    calc Valued.v fh
        = WithZero.exp (n : ℤ) * (WithZero.exp (-(n : ℤ)) * Valued.v fh) := by
          rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
      _ ≤ WithZero.exp (n : ℤ) * 1 := mul_le_mul_of_nonneg_left h1 (WithZero.zero_le _)
      _ = WithZero.exp (n : ℤ) := mul_one _

  calc Valued.v ((kwF4R1V410a_ringEquiv u z : u.adicCompletionIntegers)
          : u.adicCompletion) * Valued.v fh
      ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (n : ℤ) := mul_le_mul' hzval hfhval
    _ = WithZero.exp ((-(n : ℤ)) + (n : ℤ)) := (WithZero.exp_add _ _).symm
    _ = 1 := by rw [_root_.neg_add_cancel, WithZero.exp_zero]

end V410aBridge


section EpsSpec

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K]

theorem kwTateRR3_localResidueCompletion_sub (u : Place K L) (xh yh : u.adicCompletion) :
    kwHgfV352_localResidueCompletion u (xh - yh)
      = kwHgfV352_localResidueCompletion u xh
        - kwHgfV352_localResidueCompletion u yh := by
  rw [eq_sub_iff_add_eq, ← kwHgfV352_localResidueCompletion_add, sub_add_cancel]

theorem algebraMap_sub_cohenSectionHat_eq_v410a (u : Place K L)
    (S : Lg37CompletionSection u) (ℓ : u.toValuationSubring) :
    algebraMap L u.adicCompletion (ℓ : L)
        - cohenSectionHat u S (IsLocalRing.residue _ ℓ)
      = ((kwF4R1V410a_ringEquiv u
            (algebraMap u.toValuationSubring (lg37_completion u) ℓ
              - S.lift (IsLocalRing.residue _ ℓ))
          : u.adicCompletionIntegers) : u.adicCompletion) := by
  have hℓ : algebraMap L u.adicCompletion (ℓ : L)
      = ((kwF4R1V410a_ringEquiv u
            (algebraMap u.toValuationSubring (lg37_completion u) ℓ)
          : u.adicCompletionIntegers) : u.adicCompletion) := by
    rw [kwF4R1V410a_ringEquiv_of u ℓ]; rfl
  rw [hℓ, cohenSectionHat_apply, map_sub]
  exact (AddSubgroupClass.coe_sub _ _).symm

theorem localResidueCompletion_mul_cohenSectionHat
    (u : Place K L) (S : Lg37CompletionSection u)
    (fh : u.adicCompletion) (c : u.ResidueField) :
    kwHgfV352_localResidueCompletion u (fh * cohenSectionHat u S c)
      = kwHgfV352_localResidueCompletion u fh * c := by

  obtain ⟨f, hf⟩ := kwHgfV352_exists_sub_mem_adicCompletionIntegers u fh

  rcases (em (f ∈ u.toValuationSubring)) with hfmem | hfnmem
  · have hfh_mem : fh ∈ u.adicCompletionIntegers := by
      have hfhat : algebraMap L u.adicCompletion f ∈ u.adicCompletionIntegers :=
        (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u f).mpr hfmem
      have hsub : algebraMap L u.adicCompletion f
          - (algebraMap L u.adicCompletion f - fh) = fh := by ring
      exact hsub ▸ sub_mem hfhat hf
    rw [kwHgfV352_localResidueCompletion_eq_zero_of_mem_integers u hfh_mem, zero_mul,
      kwHgfV352_localResidueCompletion_eq_zero_of_mem_integers u
        (mul_mem hfh_mem (cohenSectionHat_mem_integers u S c))]

  have hf0 : f ≠ 0 := fun h => hfnmem (h ▸ zero_mem _)
  have hord_neg : u.ord f < 0 :=
    not_le.mp (fun h => hfnmem ((u.mem_iff_ord_nonneg hf0).mpr h))
  set M := (-u.ord f).toNat with hM_def
  have hM_eq : (M : ℤ) = -u.ord f := Int.toNat_of_nonneg (by omega)

  have hfpole : f ∈ u.poleSubmodule (M + 1) := by
    rw [u.mem_poleSubmodule_iff_ord hf0]; omega

  obtain ⟨ℓ, hℓres, hℓvan⟩ := exists_approximant u S c M

  have hV278 : resStar u S ((ℓ : L) * f) = c * resStar u S f := by
    rw [← hℓres]
    exact kwHgf_v278_resStar_approximant_mul u S ℓ M hℓvan f hfpole

  have hfhLR : kwHgfV352_localResidueCompletion u fh = resStar u S f := by
    rw [kwHgfV352_localResidueCompletion_spec u fh hf, localResidue_eq_resStar u S f]

  have hgap : algebraMap L u.adicCompletion ((ℓ : L) * f) - fh * cohenSectionHat u S c
      ∈ u.adicCompletionIntegers := by
    have hℓhat_mem : algebraMap L u.adicCompletion (ℓ : L) ∈ u.adicCompletionIntegers :=
      (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr ℓ.2

    have hfirst : algebraMap L u.adicCompletion (ℓ : L)
        * (algebraMap L u.adicCompletion f - fh) ∈ u.adicCompletionIntegers :=
      mul_mem hℓhat_mem hf

    have hsecond : (algebraMap L u.adicCompletion (ℓ : L)
        - cohenSectionHat u S c) * fh ∈ u.adicCompletionIntegers := by
      rw [← hℓres, algebraMap_sub_cohenSectionHat_eq_v410a u S ℓ]
      refine v410a_evalDepth_mul_mem_integers u (M + 1) _
        (approximant_evalₐ_sub_lift_eq_zero u S hℓvan) fh ?_

      have hπmem : algebraMap L u.adicCompletion u.uniformizer ^ (M + 1)
          ∈ u.adicCompletionIntegers := pow_mem
        ((kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr
          u.uniformizer_mem) _
      have hπf : algebraMap L u.adicCompletion u.uniformizer ^ (M + 1)
          * algebraMap L u.adicCompletion f ∈ u.adicCompletionIntegers := by
        rw [← map_pow, ← map_mul]
        exact (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr
          ((u.mem_poleSubmodule).mp hfpole)
      have hdecomp : algebraMap L u.adicCompletion u.uniformizer ^ (M + 1) * fh
          = algebraMap L u.adicCompletion u.uniformizer ^ (M + 1)
              * algebraMap L u.adicCompletion f
            - algebraMap L u.adicCompletion u.uniformizer ^ (M + 1)
              * (algebraMap L u.adicCompletion f - fh) := by ring
      rw [hdecomp]; exact sub_mem hπf (mul_mem hπmem hf)

    have hdecomp : algebraMap L u.adicCompletion ((ℓ : L) * f)
          - fh * cohenSectionHat u S c
        = algebraMap L u.adicCompletion (ℓ : L)
            * (algebraMap L u.adicCompletion f - fh)
          + (algebraMap L u.adicCompletion (ℓ : L)
              - cohenSectionHat u S c) * fh := by
      rw [map_mul]; ring
    rw [hdecomp]; exact add_mem hfirst hsecond

  rw [kwHgfV352_localResidueCompletion_spec u _ hgap,
    localResidue_eq_resStar u S ((ℓ : L) * f), hV278, hfhLR, mul_comm]

end EpsSpec


section ComplMint

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [HasCanonicalLocalResidueKStar K L]

structure KwTateRR3CohenLaurentCompl (u : Place K L) [u.FiniteResidue] where

  S : Lg37CompletionSection u

  B : Submodule K u.adicCompletion

  hcompl : IsCompl (adicIntegersKSubmod u) B

  shift_sub_mem : ∀ z : B,
    algebraMap L u.adicCompletion u.uniformizer * (z : u.adicCompletion)
      - cohenSectionHat u S (kwHgfV352_localResidueCompletion u (z : u.adicCompletion)) ∈ B

variable (K L) in

def KwTateRR3CohenLaurentComplExists : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue], Nonempty (KwTateRR3CohenLaurentCompl u)

end ComplMint


section Construct

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K]
variable {u : Place K L} [u.FiniteResidue]

def localResidueCompletionₗ (u : Place K L) : u.adicCompletion →ₗ[K] u.ResidueField where
  toFun := kwHgfV352_localResidueCompletion u
  map_add' := kwHgfV352_localResidueCompletion_add u
  map_smul' c x := by
    rw [RingHom.id_apply]; exact kwF4R1V394a_localResidueCompletion_smul u c x

def cohenLaurentSpec_of_compl (C : KwTateRR3CohenLaurentCompl u) :
    KwTateRR3CohenLaurentSpec u where
  S := C.S
  B := C.B
  hcompl := C.hcompl
  ε := (localResidueCompletionₗ u).comp C.B.subtype
  shift_sub_mem z := C.shift_sub_mem z
  ε_principalPart_mul_sectionHat fh c := by

    show kwHgfV352_localResidueCompletion u
        (fh * cohenSectionHat u C.S c
          - cohenProjC u C.B C.hcompl (fh * cohenSectionHat u C.S c))
      = kwHgfV352_localResidueCompletion u fh * c
    rw [kwTateRR3_localResidueCompletion_sub u,
      kwHgfV352_localResidueCompletion_eq_zero_of_mem_integers u
        (cohenProjC_mem_integers u C.B C.hcompl _),
      sub_zero, localResidueCompletion_mul_cohenSectionHat u C.S fh c]

end Construct


section Headline

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K]

theorem kwTateRR3_cohenLaurentSpecExists_of_complExists
    (hC : KwTateRR3CohenLaurentComplExists K L) :
    KwTateRR3CohenLaurentSpecExists K L := fun u _ =>
  (hC u).map cohenLaurentSpec_of_compl

theorem kwTateRR3_cohenKernelDataExists_of_complExists
    (hC : KwTateRR3CohenLaurentComplExists K L) :
    KwF4gRRTateCohenKernelDataExists K L :=
  kwTateRR3_cohenKernelDataExists_of_cohenLaurentSpec
    (kwTateRR3_cohenLaurentSpecExists_of_complExists hC)

end Headline


end ModularCurve.KwTateRR3



end

end


end


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.Submodule
open _root_.IsLocalRing
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsLocalRing
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4gRRTate
open _root_.ModularCurve.Lg37
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.Lg37
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwF4R1V410a
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwTateRR3
open _root_.ModularCurve.KwNo6Pin
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwNo6Pin
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.ModularCurve.KwNo6HrouteR
open _root_.IsDedekindDomain
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain
open _root_.IsDedekindDomain.HeightOneSpectrum
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.IsDedekindDomain.HeightOneSpectrum
open _root_.WithZero
open _root_.P2MW.S_AlgebraicCurve_tateAgreement.WithZero

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateAgreement)

namespace KwTateRR3
open _root_.ModularCurve

section UniformizerHat

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

abbrev uniformizerHat : u.adicCompletion := algebraMap L u.adicCompletion u.uniformizer

theorem uniformizerHat_ne_zero : uniformizerHat u ≠ 0 :=
  fun h => u.uniformizer_ne_zero
    ((map_eq_zero_iff _ (algebraMap L u.adicCompletion).injective).mp h)

theorem uniformizerHat_mem_integers : uniformizerHat u ∈ u.adicCompletionIntegers :=
  (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr u.uniformizer_mem

theorem irreducible_uniformizerHat :
    Irreducible (⟨uniformizerHat u, uniformizerHat_mem_integers u⟩
      : u.adicCompletionIntegers) := by
  refine (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (adicCompletion.maximalIdeal_eq_span_uniformizer L u.heightOneSpectrum ?_)
  rw [valued_algebraMap_uniformizer u, WithZero.exp_eq_coe_ofAdd]

end UniformizerHat


section CohenPhi

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (S : Lg37CompletionSection u)

def cohenΦ : (ℕ →₀ u.ResidueField) →ₗ[K] u.adicCompletion :=
  Finsupp.lsum K fun j =>
    lmulK u ((uniformizerHat u)⁻¹ ^ (j + 1)) ∘ₗ (cohenSectionHat u S).toLinearMap

theorem cohenΦ_apply (δ : ℕ →₀ u.ResidueField) :
    cohenΦ u S δ = δ.sum fun j c => (uniformizerHat u)⁻¹ ^ (j + 1) * cohenSectionHat u S c := by
  rw [cohenΦ, Finsupp.coe_lsum]; rfl

theorem cohenΦ_single (j : ℕ) (c : u.ResidueField) :
    cohenΦ u S (Finsupp.single j c)
      = (uniformizerHat u)⁻¹ ^ (j + 1) * cohenSectionHat u S c := by
  rw [cohenΦ_apply, Finsupp.sum_single_index]
  rw [_root_.map_zero, mul_zero]

def cohenB : Submodule K u.adicCompletion := LinearMap.range (cohenΦ u S)

theorem monomial_mem_cohenB (j : ℕ) (c : u.ResidueField) :
    (uniformizerHat u)⁻¹ ^ (j + 1) * cohenSectionHat u S c ∈ cohenB u S :=
  ⟨Finsupp.single j c, cohenΦ_single u S j c⟩

end CohenPhi


section LocResComplMonomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K] (u : Place K L)

theorem locResCompl_uniformizerHat_inv (S : Lg37CompletionSection u) :
    kwHgfV352_localResidueCompletion u ((uniformizerHat u)⁻¹) = 1 := by
  rw [show (uniformizerHat u)⁻¹ = algebraMap L u.adicCompletion (u.uniformizer)⁻¹ from
      (map_inv₀ (algebraMap L u.adicCompletion) _).symm,
    kwHgfV352_localResidueCompletion_algebraMap u, localResidue_eq_resStar u S,
    resStar_simplePole u S _
      (by rw [mul_inv_cancel₀ u.uniformizer_ne_zero]; exact one_mem _)]
  exact congrArg (IsLocalRing.residue _)
    (Subtype.ext (mul_inv_cancel₀ u.uniformizer_ne_zero)) |>.trans (map_one _)

theorem locResCompl_uniformizerHat_inv_pow_succ (S : Lg37CompletionSection u)
    {j : ℕ} (hj : 1 ≤ j) :
    kwHgfV352_localResidueCompletion u ((uniformizerHat u)⁻¹ ^ (j + 1)) = 0 := by
  rw [show (uniformizerHat u)⁻¹ ^ (j + 1)
        = algebraMap L u.adicCompletion (u.uniformizer ^ (j + 1))⁻¹ by
      rw [map_inv₀ (algebraMap L u.adicCompletion), map_pow, inv_pow],
    kwHgfV352_localResidueCompletion_algebraMap u, localResidue_eq_resStar u S,
    resStar_higherPoleMonomial u S hj]

end LocResComplMonomial


section LocResComplPhi

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K] (u : Place K L)
variable (S : Lg37CompletionSection u)

theorem locResCompl_cohenΦ (δ : ℕ →₀ u.ResidueField) :
    kwHgfV352_localResidueCompletion u (cohenΦ u S δ) = δ 0 := by
  rw [show kwHgfV352_localResidueCompletion u (cohenΦ u S δ)
      = localResidueCompletionₗ u (cohenΦ u S δ) from rfl,
    cohenΦ_apply, map_finsuppSum]
  refine (Finsupp.sum_eq_single 0 (fun j _ hj0 => ?_) (fun _ => ?_)).trans ?_
  · show kwHgfV352_localResidueCompletion u _ = 0
    rw [localResidueCompletion_mul_cohenSectionHat u S,
      locResCompl_uniformizerHat_inv_pow_succ u S (Nat.one_le_iff_ne_zero.mpr hj0), zero_mul]
  · show kwHgfV352_localResidueCompletion u _ = 0
    rw [_root_.map_zero, mul_zero]
    exact _root_.map_zero (localResidueCompletionₗ u)
  · show kwHgfV352_localResidueCompletion u _ = _
    rw [zero_add, pow_one, localResidueCompletion_mul_cohenSectionHat u S,
      locResCompl_uniformizerHat_inv u S, one_mul]

end LocResComplPhi


section ShiftCore

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (S : Lg37CompletionSection u)

theorem uniformizerHat_mul_cohenΦ (δ : ℕ →₀ u.ResidueField) :
    uniformizerHat u * cohenΦ u S δ
      = δ.sum fun j c => (uniformizerHat u)⁻¹ ^ j * cohenSectionHat u S c := by
  rw [cohenΦ_apply, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [pow_succ', ← mul_assoc, ← mul_assoc,
    mul_inv_cancel₀ (uniformizerHat_ne_zero u), one_mul]

theorem uniformizerHat_mul_cohenΦ_sub_mem (δ : ℕ →₀ u.ResidueField) :
    uniformizerHat u * cohenΦ u S δ - cohenSectionHat u S (δ 0) ∈ cohenB u S := by
  rw [uniformizerHat_mul_cohenΦ u S δ, Finsupp.sum,
    show cohenSectionHat u S (δ 0)
        = (uniformizerHat u)⁻¹ ^ 0 * cohenSectionHat u S (δ 0) by rw [pow_zero, one_mul]]

  have hterm : ∀ j ∈ δ.support, j ≠ 0 →
      (uniformizerHat u)⁻¹ ^ j * cohenSectionHat u S (δ j) ∈ cohenB u S := fun j _ hj0 => by
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
    exact monomial_mem_cohenB u S j' (δ (j' + 1))
  rcases em ((0 : ℕ) ∈ δ.support) with h0 | h0
  · rw [← Finset.sum_erase_add _ _ h0, add_sub_cancel_right]
    exact sum_mem fun j hj => hterm j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  · rw [Finsupp.notMem_support_iff.mp h0, _root_.map_zero, mul_zero, sub_zero]
    exact sum_mem fun j hj => hterm j hj fun hj0 => h0 (hj0 ▸ hj)

end ShiftCore


section Disjoint

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)
variable (S : Lg37CompletionSection u)

theorem valued_cohenSectionHat_of_ne_zero {c : u.ResidueField} (hc : c ≠ 0) :
    Valued.v (cohenSectionHat u S c) = 1 := by
  refine le_antisymm (cohenSectionHat_mem_integers u S c) ?_
  have hprod : Valued.v (cohenSectionHat u S c) * Valued.v (cohenSectionHat u S c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  calc (1 : ℤᵐ⁰)
      = Valued.v (cohenSectionHat u S c) * Valued.v (cohenSectionHat u S c⁻¹) := hprod.symm
    _ ≤ Valued.v (cohenSectionHat u S c) * 1 :=
        mul_le_mul_right (cohenSectionHat_mem_integers u S c⁻¹) _
    _ = Valued.v (cohenSectionHat u S c) := mul_one _

theorem uniformizerHat_pow_mul_cohenΦ_sub_top (δ : ℕ →₀ u.ResidueField)
    (hδ : δ.support.Nonempty) :
    let J := δ.support.max' hδ
    (uniformizerHat u) ^ (J + 1) * cohenΦ u S δ - cohenSectionHat u S (δ J)
      = ∑ j ∈ δ.support.erase J,
          (uniformizerHat u) ^ (J - j) * cohenSectionHat u S (δ j) := by
  intro J
  have hJmem : J ∈ δ.support := δ.support.max'_mem hδ
  rw [cohenΦ_apply, Finsupp.mul_sum, Finsupp.sum,
    ← Finset.sum_erase_add _ _ hJmem,
    show (uniformizerHat u) ^ (J + 1) * ((uniformizerHat u)⁻¹ ^ (J + 1)
            * cohenSectionHat u S (δ J))
        = cohenSectionHat u S (δ J) by
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (uniformizerHat_ne_zero u), one_pow, one_mul],
    add_sub_cancel_right]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjJ : j < J := lt_of_le_of_ne
    (δ.support.le_max' j (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj)
  rw [← mul_assoc]
  congr 1

  rw [show J + 1 = (J - j) + (j + 1) by omega, pow_add, mul_assoc,
    ← mul_pow, mul_inv_cancel₀ (uniformizerHat_ne_zero u), one_pow, mul_one]

theorem cohenΦ_mem_integers_iff_zero (δ : ℕ →₀ u.ResidueField) :
    cohenΦ u S δ ∈ u.adicCompletionIntegers → δ = 0 := by
  intro hmem
  by_contra hδ0
  have hδne : δ.support.Nonempty := Finsupp.support_nonempty_iff.mpr hδ0
  set J := δ.support.max' hδne with hJ
  have hδJ : δ J ≠ 0 := Finsupp.mem_support_iff.mp (δ.support.max'_mem hδne)

  have hi : Valued.v ((uniformizerHat u) ^ (J + 1) * cohenΦ u S δ)
      ≤ WithZero.exp (-1 : ℤ) := by
    rw [map_mul, map_pow, valued_algebraMap_uniformizer u, ← WithZero.exp_nsmul]
    calc WithZero.exp ((J + 1) • (-1 : ℤ)) * Valued.v (cohenΦ u S δ)
        ≤ WithZero.exp ((J + 1) • (-1 : ℤ)) * 1 := mul_le_mul_right hmem _
      _ = WithZero.exp (-((J : ℤ) + 1)) := by rw [mul_one]; congr 1; ring
      _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)

  have hii : Valued.v
      ((uniformizerHat u) ^ (J + 1) * cohenΦ u S δ - cohenSectionHat u S (δ J))
      ≤ WithZero.exp (-1 : ℤ) := by
    rw [uniformizerHat_pow_mul_cohenΦ_sub_top u S δ hδne]
    refine Finset.sum_induction _ (fun x => Valued.v x ≤ WithZero.exp (-1 : ℤ))
      (fun a b ha hb => (Valued.v.map_add a b).trans (max_le ha hb))
      ?_ fun j hj => ?_
    · show Valued.v (0 : u.adicCompletion) ≤ _
      rw [_root_.map_zero]; exact WithZero.zero_le _
    · have hjJ : j < J := lt_of_le_of_ne
        (δ.support.le_max' j (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj)
      show Valued.v (_ * _) ≤ _
      rw [map_mul, map_pow, valued_algebraMap_uniformizer u, ← WithZero.exp_nsmul]
      calc WithZero.exp ((J - j) • (-1 : ℤ)) * Valued.v (cohenSectionHat u S (δ j))
          ≤ WithZero.exp ((J - j) • (-1 : ℤ)) * 1 :=
            mul_le_mul_right (cohenSectionHat_mem_integers u S _) _
        _ = WithZero.exp (-((J - j : ℕ) : ℤ)) := by rw [mul_one]; congr 1; ring
        _ ≤ WithZero.exp (-1 : ℤ) := WithZero.exp_le_exp.mpr (by omega)

  have hiii : Valued.v (cohenSectionHat u S (δ J)) ≤ WithZero.exp (-1 : ℤ) := by
    have hdecomp : cohenSectionHat u S (δ J)
        = (uniformizerHat u) ^ (J + 1) * cohenΦ u S δ
          - ((uniformizerHat u) ^ (J + 1) * cohenΦ u S δ - cohenSectionHat u S (δ J)) := by ring
    rw [hdecomp, sub_eq_add_neg]
    exact (Valued.v.map_add _ _).trans (max_le hi (by rwa [Valuation.map_neg]))

  rw [valued_cohenSectionHat_of_ne_zero u S hδJ] at hiii
  exact absurd hiii (not_le.mpr (by
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr (by norm_num)))

theorem disjoint_adicIntegersKSubmod_cohenB :
    _root_.Disjoint (adicIntegersKSubmod u) (cohenB u S) := by
  rw [Submodule.disjoint_def]
  rintro x hxO ⟨δ, rfl⟩
  rw [cohenΦ_mem_integers_iff_zero u S δ hxO, _root_.map_zero]

end Disjoint


section Codisjoint

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K] (u : Place K L)
variable (S : Lg37CompletionSection u)

theorem uniformizerHat_inv_mul_mem_integers_of_valued_le
    {y : u.adicCompletion} (hy : Valued.v y ≤ WithZero.exp (-1 : ℤ)) :
    (uniformizerHat u)⁻¹ * y ∈ u.adicCompletionIntegers := by
  show Valued.v ((uniformizerHat u)⁻¹ * y) ≤ 1
  rw [map_mul, map_inv₀, valued_algebraMap_uniformizer u, ← WithZero.exp_neg, neg_neg]
  calc WithZero.exp (1 : ℤ) * Valued.v y
      ≤ WithZero.exp (1 : ℤ) * WithZero.exp (-1 : ℤ) := mul_le_mul_right hy _
    _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]

theorem valued_le_of_mem_completionIdeal {y : u.adicCompletionIntegers}
    (hy : y ∈ u.heightOneSpectrum.completionIdeal L) :
    Valued.v (y : u.adicCompletion) ≤ WithZero.exp (-1 : ℤ) := by
  have := (adicCompletion.mem_completionIdeal_pow L u.heightOneSpectrum y).mp
    (by rw [pow_one]; exact hy)
  rwa [← WithZero.exp_eq_coe_ofAdd, show (-((1 : ℕ) : ℤ)) = (-1 : ℤ) by norm_num] at this

theorem exists_residue_peel (ŷ : u.adicCompletionIntegers) :
    ∃ c : u.ResidueField,
      (uniformizerHat u)⁻¹ * ((ŷ : u.adicCompletion) - cohenSectionHat u S c)
        ∈ u.adicCompletionIntegers := by
  obtain ⟨ℓ, hℓ⟩ := kwF4R1V410a_exists_sub_mem_completionIdeal_pow u 1 ŷ
  refine ⟨IsLocalRing.residue _ ℓ, uniformizerHat_inv_mul_mem_integers_of_valued_le u ?_⟩

  have hcoe : ((algebraMap u.toValuationSubring u.adicCompletionIntegers ℓ
        : u.adicCompletionIntegers) : u.adicCompletion)
      = algebraMap L u.adicCompletion (ℓ : L) := rfl
  have hdecomp : (ŷ : u.adicCompletion) - cohenSectionHat u S (IsLocalRing.residue _ ℓ)
      = ((ŷ - algebraMap u.toValuationSubring u.adicCompletionIntegers ℓ
            : u.adicCompletionIntegers) : u.adicCompletion)
        + (algebraMap L u.adicCompletion (ℓ : L)
            - cohenSectionHat u S (IsLocalRing.residue _ ℓ)) := by
    push_cast [hcoe]; ring
  rw [hdecomp]
  refine (Valued.v.map_add _ _).trans (max_le ?_ ?_)
  ·
    refine valued_le_of_mem_completionIdeal u ?_
    rw [← pow_one (u.heightOneSpectrum.completionIdeal L)]; exact hℓ
  ·
    rw [algebraMap_sub_cohenSectionHat_eq_v410a u S ℓ]
    refine valued_le_of_mem_completionIdeal u ?_
    rw [← pow_one (u.heightOneSpectrum.completionIdeal L)]
    exact v410a_mem_completionIdeal_pow_of_evalₐ_eq_zero u 1 _
      (approximant_evalₐ_sub_lift_eq_zero u S (M := 0) (ℓ := ℓ)
        (fun k hk1 hk0 => absurd hk0 (by omega)))

theorem mem_sup_of_uniformizerHat_pow_mul_mem_integers (M : ℕ) :
    ∀ x : u.adicCompletion, (uniformizerHat u) ^ M * x ∈ u.adicCompletionIntegers →
      x ∈ adicIntegersKSubmod u ⊔ cohenB u S := by
  induction M with
  | zero => intro x hx; rw [pow_zero, one_mul] at hx; exact Submodule.mem_sup_left hx
  | succ M IH =>
    intro x hx
    obtain ⟨c, hc⟩ := exists_residue_peel u S ⟨_, hx⟩

    have hne := uniformizerHat_ne_zero u
    have hstep : (uniformizerHat u) ^ M * (x
        - (uniformizerHat u)⁻¹ ^ (M + 1) * cohenSectionHat u S c)
        ∈ u.adicCompletionIntegers := by
      have heq : (uniformizerHat u) ^ M * (x
            - (uniformizerHat u)⁻¹ ^ (M + 1) * cohenSectionHat u S c)
          = (uniformizerHat u)⁻¹ * ((uniformizerHat u)^(M+1)*x - cohenSectionHat u S c) := by
        rw [mul_sub, mul_sub,
          show (uniformizerHat u)⁻¹ * ((uniformizerHat u)^(M+1) * x)
              = (uniformizerHat u)^M * x by
            rw [← mul_assoc, pow_succ', ← mul_assoc, inv_mul_cancel₀ hne, one_mul],
          show (uniformizerHat u)^M * ((uniformizerHat u)⁻¹^(M+1) * cohenSectionHat u S c)
              = (uniformizerHat u)⁻¹ * cohenSectionHat u S c by
            rw [← mul_assoc, pow_succ, ← mul_assoc, ← mul_pow,
              mul_inv_cancel₀ hne, one_pow, one_mul]]
      rw [heq]; exact hc
    have hx' := IH _ hstep
    have hb : (uniformizerHat u)⁻¹ ^ (M + 1) * cohenSectionHat u S c ∈ cohenB u S :=
      monomial_mem_cohenB u S M c
    have hx_eq : x = (x - (uniformizerHat u)⁻¹ ^ (M + 1) * cohenSectionHat u S c)
        + (uniformizerHat u)⁻¹ ^ (M + 1) * cohenSectionHat u S c := by ring
    rw [hx_eq]
    exact add_mem hx' (Submodule.mem_sup_right hb)

theorem codisjoint_adicIntegersKSubmod_cohenB :
    Codisjoint (adicIntegersKSubmod u) (cohenB u S) := by
  rw [codisjoint_iff, eq_top_iff]
  intro x _
  obtain ⟨M, hM⟩ := kwF4gRRTate_clearPole u
    ⟨uniformizerHat u, uniformizerHat_mem_integers u⟩ (irreducible_uniformizerHat u) x
  exact mem_sup_of_uniformizerHat_pow_mul_mem_integers u S M x hM

end Codisjoint


section Assembly

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K]

def cohenLaurentCompl_of_section (u : Place K L) [u.FiniteResidue]
    (S : Lg37CompletionSection u) : KwTateRR3CohenLaurentCompl u where
  S := S
  B := cohenB u S
  hcompl := ⟨disjoint_adicIntegersKSubmod_cohenB u S,
    codisjoint_adicIntegersKSubmod_cohenB u S⟩
  shift_sub_mem z := by
    obtain ⟨δ, hδ⟩ := z.2
    rw [← hδ, locResCompl_cohenΦ u S δ]
    exact uniformizerHat_mul_cohenΦ_sub_mem u S δ

end Assembly


section Headline

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [IsCurveOver K L] [PerfectField K]

theorem kwTateRR3_cohenLaurentComplExists :
    KwTateRR3CohenLaurentComplExists K L := fun u _ => by
  haveI : FiniteDimensional K u.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsSeparable K u.ResidueField :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact (completionSection_nonempty_generic u).map (cohenLaurentCompl_of_section u)

theorem kwTateRR3_cohenKernelDataExists :
    KwF4gRRTateCohenKernelDataExists K L :=
  kwTateRR3_cohenKernelDataExists_of_complExists kwTateRR3_cohenLaurentComplExists

end Headline


end ModularCurve.KwTateRR3



end

end


end


theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [AlgebraicCurve.IsCurveOver K L] [PerfectField K]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue]
    (hfin : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateAgreement K L hfin :=
  ModularCurve.KwF4gRRTate.kwF4gRRTate_agreement_of_kernelData hfin
    ModularCurve.KwTateRR3.kwTateRR3_cohenKernelDataExists

end P2MW.S_AlgebraicCurve_tateAgreement
