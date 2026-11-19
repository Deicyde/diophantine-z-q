/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf (git blob 43944f52c6c8375882ff8c1619e5d8b9e14c0ece, sha256 9f2bf38008c2f147d0e5a12267d8748093a14f311bc11ff629657ec45bf85fe9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_ComplexConjugation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem ModularCurve.exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hinC : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      ModularCurve.HeckeInputsHAlong ℂ M H ℓ)
    (hstT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.heckeULinH 2 q).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstD : ∀ (d : (ZMod M)ˣ), ∀ v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H),
      (CuspForm.diamondLinH 2 d).dualMap v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hstC : ∀ (φ φ' : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
      (∀ f g : CuspForm (CohCarrier.GammaH M H) 2,
        (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
          φ' g = -(starRingEnd ℂ) (φ f)) →
      φ ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) →
        φ' ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    ∃ v : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) →+
        (Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2) ⧸ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)),
      Function.Bijective v ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
          (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        v z = Submodule.Quotient.mk φ →
        v ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; ModularCurve.heckeOperatorHAlong ℂ M H ℓ) z) =
          Submodule.Quotient.mk ((CuspForm.heckeTLinH 2 hℓ hℓM).dualMap φ)) ∧
      (∀ (q : ℕ) (hq : q.Prime), q ∣ M →
          ∀ (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        v z = Submodule.Quotient.mk φ →
        v ((haveI : NeZero q := ⟨hq.ne_zero⟩; ModularCurve.heckeOperatorHAlong ℂ M H q) z) =
          Submodule.Quotient.mk ((CuspForm.heckeULinH 2 q).dualMap φ)) ∧
      (∀ (d : (ZMod M)ˣ)
          (σ : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ≃ₐ[ℂ]
            ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))),
        (∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
            (pf pg : PowerSeries ℤ) (hf : ModularCurve.IsIntegralQExp f pf) (hg : ModularCurve.IsIntegralQExp g pg)
            (hg0 : ModularCurve.intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)),
            γ ∈ CongruenceSubgroup.Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
            ((σ ⟨ModularCurve.coeffEmb ℂ (ModularCurve.intSeriesC ℚ pf / ModularCurve.intSeriesC ℚ pg),
                  ModularCurve.coeffEmb_mem_laurentBaseChange ℂ
                    (ModularCurve.div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
                ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))) : LaurentSeries ℂ) *
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))) →
        ∀ (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
          (φ : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
          v z = Submodule.Quotient.mk φ →
          v (AlgebraicCurve.SemilinearAut.ofAlgAut σ • z) =
            Submodule.Quotient.mk ((CuspForm.diamondLinH 2 d).dualMap φ)) ∧
      ∀ (z : AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
        (φ φ' : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H) 2)),
        (∀ f g : CuspForm (CohCarrier.GammaH M H) 2,
          (∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) →
            φ' g = -(starRingEnd ℂ) (φ f)) →
        v z = Submodule.Quotient.mk φ →
        v (complexConjAlgEquiv • z) = Submodule.Quotient.mk φ' := by
  revert M H hinC hstT hstU hstD hstC
  exact @_root_.P2MW.S_ModularCurve_exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf.solution
