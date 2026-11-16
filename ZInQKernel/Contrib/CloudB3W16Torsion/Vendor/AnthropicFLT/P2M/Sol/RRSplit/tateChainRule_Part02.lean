/-
Copyright 2026 Anthropic, PBC. Released under Apache License 2.0.
Source: https://github.com/anthropics/fermats-last-theorem
Revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicCurve_tateChainRule.lean; source lines 2531-2832.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.RRSplit.tateChainRule_Part01

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 6400000
set_option maxHeartbeats 12800000

namespace P2MW.S_AlgebraicCurve_tateChainRule

-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.ord_nonneg_of_mem :=
  @_root_.P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place.ord_nonneg_of_mem
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_of_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place.mem_of_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.mem_iff_ord_nonneg :=
  @_root_.P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place.mem_iff_ord_nonneg
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.comap_algebraMap_ne_top :=
  @_root_.P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place.comap_algebraMap_ne_top
-- RRSplit source-private field lookup bridge (transparent).
private noncomputable abbrev _root_.AlgebraicCurve.Place.exists_ord_algebraMap_pos :=
  @_root_.P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place.exists_ord_algebraMap_pos


section
section

set_option maxHeartbeats 12800000
set_option synthInstance.maxHeartbeats 6400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve
open _root_.AlgebraicCurve.Place
open _root_.P2MW.S_AlgebraicCurve_tateChainRule.AlgebraicCurve.Place
open _root_.LinearMap
open _root_.P2MW.S_AlgebraicCurve_tateChainRule.LinearMap
open _root_.Submodule
open _root_.P2MW.S_AlgebraicCurve_tateChainRule.Submodule
open _root_.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4gRRTate
open _root_.P2MW.S_AlgebraicCurve_tateChainRule.ModularCurve.KwF4R1V473a

noncomputable section

namespace ModularCurve

export _root_.ModularCurve (KwF4gRRTate.KwF4gRRTateCommFinite KwF4gRRTate.KwF4gRRTateChainRule)

namespace KwF4gRRTate

export _root_.ModularCurve.KwF4gRRTate (finrankTrace tateComm tateComm_apply tateCommRestrict tateCommRestrict_apply tateCommTrace adicIntegersKSubmod tateProj lmulK tateRes KwF4gRRTateCommFinite KwF4gRRTateChainRule)

open _root_.ModularCurve.KwF4gRRTate
open _root_.ModularCurve

section DualDom

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def DualDom (w : Place K F) : Type _ := w.adicCompletion →ₗ[K] K

scoped instance (w : Place K F) : AddCommGroup (DualDom w) :=
  inferInstanceAs (AddCommGroup (w.adicCompletion →ₗ[K] K))

def DualDom.toLM {w : Place K F} (φ : DualDom w) : w.adicCompletion →ₗ[K] K := φ

@[scoped ext] theorem DualDom.ext {w : Place K F} {φ ψ : DualDom w}
    (h : ∀ x, φ.toLM x = ψ.toLM x) : φ = ψ := LinearMap.ext h


@[scoped simp] theorem DualDom.toLM_add {w : Place K F} (φ ψ : DualDom w) :
    (φ + ψ).toLM = φ.toLM + ψ.toLM := rfl


scoped instance (w : Place K F) : Module F (DualDom w) where
  smul h φ := φ.toLM ∘ₗ lmulK w (algebraMap F w.adicCompletion h)
  one_smul φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F w.adicCompletion 1 * x) = φ.toLM x
    rw [_root_.map_one, one_mul]
  mul_smul a b φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ (a * b) * x) = φ.toLM (algebraMap F _ b * (algebraMap F _ a * x))
    rw [(algebraMap F w.adicCompletion).map_mul, mul_comm (algebraMap F _ a), mul_assoc]
  smul_zero a := DualDom.ext fun _ => rfl
  smul_add a φ ψ := DualDom.ext fun _ => rfl
  add_smul a b φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ (a + b) * x)
      = φ.toLM (algebraMap F _ a * x) + φ.toLM (algebraMap F _ b * x)
    rw [(algebraMap F w.adicCompletion).map_add, add_mul, φ.toLM.map_add]
  zero_smul φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ 0 * x) = 0
    rw [(algebraMap F w.adicCompletion).map_zero, zero_mul, φ.toLM.map_zero]

@[scoped simp] theorem DualDom.smul_apply {w : Place K F} (h : F) (φ : DualDom w)
    (x : w.adicCompletion) :
    (h • φ).toLM x = φ.toLM (algebraMap F w.adicCompletion h * x) := rfl


scoped instance (w : Place K F) : Module K (DualDom w) :=
  inferInstanceAs (Module K (w.adicCompletion →ₗ[K] K))

theorem DualDom.k_smul_apply {w : Place K F} (c : K) (φ : DualDom w)
    (x : w.adicCompletion) :
    (c • φ).toLM x = c • φ.toLM x := rfl

scoped instance (w : Place K F) : IsScalarTower K F (DualDom w) where
  smul_assoc c h φ := DualDom.ext fun x => by
    show φ.toLM (algebraMap F _ (c • h) * x) = c • φ.toLM (algebraMap F _ h * x)
    rw [Algebra.smul_def, (algebraMap F w.adicCompletion).map_mul,
      ← IsScalarTower.algebraMap_apply K F w.adicCompletion,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_mul_assoc, φ.toLM.map_smul]

end DualDom


section GenericFactor

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [Nontrivial Ω[F⁄K]]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M]

theorem derivation_apply_eq_diffCoeff_smul (w : Place K F) [w.DCoordGenerates]
    (δ : Derivation K F M) (g : F) :
    δ g = w.differentialCoeff (KaehlerDifferential.D K F g) • δ w.uniformizer := by
  have hL := Derivation.liftKaehlerDifferential_comp_D δ
  have hLπ : δ.liftKaehlerDifferential w.dCoord = δ w.uniformizer := hL w.uniformizer
  calc δ g = δ.liftKaehlerDifferential (KaehlerDifferential.D K F g) := (hL g).symm
    _ = δ.liftKaehlerDifferential
        (w.differentialCoeff (KaehlerDifferential.D K F g) • w.dCoord) := by
          rw [w.differentialCoeff_smul_dCoord]
    _ = w.differentialCoeff (KaehlerDifferential.D K F g) • δ w.uniformizer := by
          rw [map_smul, hLπ]

end GenericFactor


section TateResDerivation

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem range_smul_le {V : Type*} [AddCommGroup V] [Module K V]
    (c : K) (φ : V →ₗ[K] V) : LinearMap.range (c • φ) ≤ LinearMap.range φ := by
  rintro y ⟨x, rfl⟩
  exact (LinearMap.range φ).smul_mem c (LinearMap.mem_range_self φ x)

theorem finDimRangeSMul {V : Type*} [AddCommGroup V] [Module K V]
    (c : K) (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    FiniteDimensional K (LinearMap.range (c • φ)) :=
  Submodule.finiteDimensional_of_le (range_smul_le c φ)

theorem finrankTrace_smul {V : Type*} [AddCommGroup V] [Module K V]
    (c : K) (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] :
    haveI := finDimRangeSMul c φ
    finrankTrace (c • φ) = c • finrankTrace φ := by
  haveI := finDimRangeSMul c φ
  have hW : ∀ x ∈ LinearMap.range φ, (c • φ) x ∈ LinearMap.range φ := fun x _ =>
    range_smul_le c φ (LinearMap.mem_range_self _ x)
  rw [finrankTrace_eq_trace_on_superspace (c • φ) (LinearMap.range φ) (range_smul_le c φ) hW]
  unfold finrankTrace
  rw [← LinearMap.map_smul]
  exact congrArg (LinearMap.trace K _) (LinearMap.ext fun x => Subtype.ext rfl)

theorem tateCommRestrict_smul_snd {V : Type*} [AddCommGroup V] [Module K V]
    (pA φ ψ : V →ₗ[K] V) (c : K) :
    tateCommRestrict pA φ (c • ψ) = c • tateCommRestrict pA φ ψ := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  show (tateCommRestrict pA φ (c • ψ) a : V) = (c • tateCommRestrict pA φ ψ a : V)
  rw [tateCommRestrict_apply, tateCommRestrict_apply]
  unfold tateComm
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_smul,
    smul_sub, Submodule.coe_smul]

theorem tateCommRestrict_smul_fst {V : Type*} [AddCommGroup V] [Module K V]
    (pA φ ψ : V →ₗ[K] V) (c : K) :
    tateCommRestrict pA (c • φ) ψ = c • tateCommRestrict pA φ ψ := by
  apply LinearMap.ext; intro a; apply Subtype.ext
  show (tateCommRestrict pA (c • φ) ψ a : V) = (c • tateCommRestrict pA φ ψ a : V)
  rw [tateCommRestrict_apply, tateCommRestrict_apply]
  unfold tateComm
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_smul,
    smul_sub, Submodule.coe_smul]

theorem tateRes_congr_snd (u : Place K F) {fh gh₁ gh₂ : u.adicCompletion} (heq : gh₁ = gh₂)
    [h₁ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh₁)))]
    [h₂ : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh₂)))] :
    tateRes u fh gh₁ = tateRes u fh gh₂ := by
  subst heq; rfl

theorem tateRes_add_snd (u : Place K F) (hfin : KwF4gRRTateCommFinite K F)
    (f g h : u.adicCompletion) :
    haveI := hfin u f (g + h); haveI := hfin u f g; haveI := hfin u f h
    tateRes u f (g + h) = tateRes u f g + tateRes u f h := by
  haveI := hfin u f (g + h); haveI := hfin u f g; haveI := hfin u f h
  have heq : lmulK u (g + h) = lmulK u g + lmulK u h := map_add _ _ _
  haveI : FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u f) (lmulK u g + lmulK u h))) := by
    rw [← heq]; exact hfin u f (g + h)
  unfold tateRes
  have hct := tateCommTrace_add_snd (tateProj u) (lmulK u f) (lmulK u g) (lmulK u h)
  unfold tateCommTrace at hct ⊢
  rw [← hct]
  exact finrankTrace_congr (by rw [heq])

def tateResFstLM (w : Place K F) (hfin : KwF4gRRTateCommFinite K F)
    (gh : w.adicCompletion) : DualDom w where
  toFun f := haveI := hfin w f gh; tateRes w f gh
  map_add' f₁ f₂ := by
    haveI := hfin w f₁ gh; haveI := hfin w f₂ gh
    exact tateRes_add_fst w f₁ f₂ gh
  map_smul' c f := by
    haveI := hfin w f gh; haveI := hfin w (c • f) gh
    show tateRes w (c • f) gh = c • tateRes w f gh
    have heq : tateCommRestrict (tateProj w) (lmulK w (c • f)) (lmulK w gh)
        = c • tateCommRestrict (tateProj w) (lmulK w f) (lmulK w gh) := by
      rw [show lmulK w (c • f) = c • lmulK w f from map_smul _ _ _,
        tateCommRestrict_smul_fst]
    haveI := finDimRangeSMul c (tateCommRestrict (tateProj w) (lmulK w f) (lmulK w gh))
    unfold tateRes tateCommTrace
    rw [finrankTrace_congr heq, finrankTrace_smul]

@[scoped simp] theorem tateResFstLM_apply (w : Place K F) (hfin : KwF4gRRTateCommFinite K F)
    (gh f : w.adicCompletion) :
    (tateResFstLM w hfin gh).toLM f = haveI := hfin w f gh; tateRes w f gh := rfl

variable [HasPrincipalDivisors K F] [Nontrivial Ω[F⁄K]]

def tateResSndDer (w : Place K F) [w.DCoordGenerates] [w.FiniteResidue]
    (hfin : KwF4gRRTateCommFinite K F) : Derivation K F (DualDom w) :=
  Derivation.mk'
    { toFun := fun g => tateResFstLM w hfin (algebraMap F w.adicCompletion g)
      map_add' := fun g h => DualDom.ext fun f => by
        simp only [tateResFstLM_apply, DualDom.toLM_add, map_add]
        exact tateRes_add_snd w hfin f _ _
      map_smul' := fun c g => DualDom.ext fun f => by
        simp only [tateResFstLM_apply, RingHom.id_apply, DualDom.k_smul_apply]
        haveI := hfin w f (algebraMap F _ (c • g))
        haveI := hfin w f (algebraMap F _ g)
        show tateRes w f (algebraMap F _ (c • g)) = c • tateRes w f (algebraMap F _ g)
        have heq : tateCommRestrict (tateProj w) (lmulK w f)
              (lmulK w (algebraMap F _ (c • g)))
            = c • tateCommRestrict (tateProj w) (lmulK w f)
              (lmulK w (algebraMap F _ g)) := by
          rw [show lmulK w (algebraMap F _ (c • g)) = c • lmulK w (algebraMap F _ g) from by
              rw [Algebra.smul_def, (algebraMap F w.adicCompletion).map_mul,
                ← IsScalarTower.algebraMap_apply K F w.adicCompletion,
                Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
              exact map_smul _ _ _,
            tateCommRestrict_smul_snd]
        haveI := finDimRangeSMul c
          (tateCommRestrict (tateProj w) (lmulK w f) (lmulK w (algebraMap F _ g)))
        unfold tateRes tateCommTrace
        rw [finrankTrace_congr heq, finrankTrace_smul] }
    (fun g h => DualDom.ext fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, tateResFstLM_apply, DualDom.smul_apply,
        DualDom.toLM_add]
      haveI := hfin w f (algebraMap F _ (g * h))
      haveI := hfin w (algebraMap F _ g * f) (algebraMap F _ h)
      haveI := hfin w (algebraMap F _ h * f) (algebraMap F _ g)
      haveI := hfin w f (algebraMap F _ g * algebraMap F _ h)
      haveI := hfin w (f * algebraMap F _ g) (algebraMap F _ h)
      haveI := hfin w (f * algebraMap F _ h) (algebraMap F _ g)
      show tateRes w f (algebraMap F _ (g * h))
        = tateRes w (algebraMap F _ g * f) (algebraMap F _ h)
          + tateRes w (algebraMap F _ h * f) (algebraMap F _ g)
      rw [tateRes_congr_snd w ((algebraMap F w.adicCompletion).map_mul g h),
        tateRes_leibniz_snd w hfin f (algebraMap F _ g) (algebraMap F _ h),
        tateRes_congr_fst w (mul_comm f (algebraMap F _ g)),
        tateRes_congr_fst w (mul_comm f (algebraMap F _ h))])

@[scoped simp] theorem tateResSndDer_apply (w : Place K F) [w.DCoordGenerates] [w.FiniteResidue]
    (hfin : KwF4gRRTateCommFinite K F) (g : F) (f : w.adicCompletion) :
    ((tateResSndDer w hfin) g).toLM f
      = haveI := hfin w f (algebraMap F _ g); tateRes w f (algebraMap F _ g) := rfl

end TateResDerivation


section Headline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [HasPrincipalDivisors K F] [Nontrivial Ω[F⁄K]]

theorem kwTateRR2_derivationFactorSnd [∀ w : Place K F, w.FiniteResidue]
    (hfinF : KwF4gRRTateCommFinite K F) :
    KwF4gRRTateDerivationFactorSnd K F hfinF := by
  intro w _ f g
  haveI := hfinF w f (algebraMap F _ g)
  haveI := hfinF w (f * algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)))
    (algebraMap F _ w.uniformizer)

  have hδ := derivation_apply_eq_diffCoeff_smul (M := DualDom w) w (tateResSndDer w hfinF) g
  haveI := hfinF w (algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)) * f)
    (algebraMap F _ w.uniformizer)
  calc tateRes w f (algebraMap F _ g)
      = ((tateResSndDer w hfinF) g).toLM f := (tateResSndDer_apply w hfinF g f).symm
    _ = (w.differentialCoeff (KaehlerDifferential.D K F g)
          • (tateResSndDer w hfinF) w.uniformizer).toLM f := by rw [hδ]
    _ = ((tateResSndDer w hfinF) w.uniformizer).toLM
          (algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)) * f) :=
        DualDom.smul_apply _ _ _
    _ = tateRes w (algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)) * f)
          (algebraMap F _ w.uniformizer) := tateResSndDer_apply w hfinF w.uniformizer _
    _ = tateRes w (f * algebraMap F _ (w.differentialCoeff (KaehlerDifferential.D K F g)))
          (algebraMap F _ w.uniformizer) :=
        tateRes_congr_fst w (mul_comm _ f)

end Headline


section Composite

variable {K F E : Type*} [Field K] [Field F] [Algebra K F]
variable [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

end Composite


end ModularCurve.KwF4gRRTate



end


end


end


theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K F] [AlgebraicCurve.HasCanonicalLocalResidueKStar K E] [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue] (hfinF : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K F) : ModularCurve.KwF4gRRTate.KwF4gRRTateChainRule K F E hfinF :=
  ModularCurve.KwF4gRRTate.kwF4gRRTate_chainRule_of_derivationFactor hfinF
    (fun {_ _} => ModularCurve.KwF4gRRTate.kwTateRR2_derivationFactorSnd hfinF)

end P2MW.S_AlgebraicCurve_tateChainRule
