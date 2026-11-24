/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_relfinrank_fullC_mul_prime_pow
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Relrank
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_relfinrank_fullC_mul_prime_pow
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open ModularCurve
theorem ModularCurve.relfinrank_fullC_mul_prime_pow {K : Type*} [Field K] (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ) (hpM : ¬ p ∣ M) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 1))) (hprev : ∀ b : ℕ, a = b + 1 → IntermediateField.relfinrank (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ b ∧ x = jqNModC K d'}) (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ (b + 1) ∧ x = jqNModC K d'}) = if b = 0 then p + 1 else p) (hnm : a = 0 → jqNModC K p ∉ IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'}) : IntermediateField.relfinrank (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ a ∧ x = jqNModC K d'}) (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ (a + 1) ∧ x = jqNModC K d'}) = if a = 0 then p + 1 else p := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_relfinrank_fullC_mul_prime_pow.solution
