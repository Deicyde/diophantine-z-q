/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_finite_torsion_of_isAlgClosed_of_charZero (git blob f90d7cb6b8c959340196886e17b35e6a1fe786d7, sha256 bbc9ea73c9c569b7e94951f30a22833435a3bd64332f08df500d10cc8c80db2e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_constantFieldDescent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_constantFieldExtension
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_natCard_torsion_eq_of_constantFieldExtension
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_genus_complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_Submodule_finite_torsionBy_pow_of_finite_torsionBy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Pic0_finite_torsion_of_isAlgClosed_of_charZero

namespace FinTorsCharZero

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def subtypeEquivTorsion (n : ℕ) : {c : Pic0 K F // n • c = 0} ≃ Pic0.torsion K F n :=
  Equiv.subtypeEquivRight fun c => by
    rw [Pic0.mem_torsion, natCast_zsmul]

def torsionEquivTorsionBy (m : ℤ) (n : ℕ) (h : (n : ℤ) = m) :
    Pic0.torsion K F n ≃ Submodule.torsionBy ℤ (Pic0 K F) m :=
  Equiv.subtypeEquivRight fun c => by
    rw [Pic0.mem_torsion, Submodule.mem_torsionBy_iff, h]

theorem finite_torsion_of_forall_prime
    (hprime : ∀ (ℓ : ℕ) [Fact ℓ.Prime], Finite (Pic0.torsion K F ℓ))
    (n : ℕ) (hn : n ≠ 0) : Finite {c : Pic0 K F // n • c = 0} := by

  have hpow : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), Finite (Pic0.torsion K F (p ^ k)) := by
    intro p hp k
    haveI : Finite (Pic0.torsion K F p) := hprime p
    have h1 : Finite (Submodule.torsionBy ℤ (Pic0 K F) (p : ℤ)) :=
      Finite.of_equiv _ (torsionEquivTorsionBy (K := K) (F := F) (p : ℤ) p rfl)
    have h2 : Finite (Submodule.torsionBy ℤ (Pic0 K F) ((p : ℤ) ^ k)) :=
      Submodule.finite_torsionBy_pow_of_finite_torsionBy (p : ℤ) h1 k
    exact Finite.of_equiv _ (torsionEquivTorsionBy ((p : ℤ) ^ k) (p ^ k) (by push_cast; rfl)).symm

  have hfin : Finite (Pic0.torsion K F n) :=
    AlgebraicCurve.Pic0.finite_torsion_of_forall_primePow hpow n (Nat.pos_of_ne_zero hn)
  exact Finite.of_equiv _ (subtypeEquivTorsion n).symm

theorem finite_torsion_prime
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] (p : ℕ) [Fact p.Prime] :
    Finite (Pic0.torsion K F p) := by

  obtain ⟨x, hx, hfd⟩ := id hfg
  haveI : Algebra.EssFiniteType K F :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
  haveI : HasCanonicalDivisor (K := K) (F := F) :=
    AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

  obtain ⟨K₀, F₀, _, _, _, _, _, _, _, _, _, _, _, _, _, hfg₀, hgen⟩ :=
    AlgebraicCurve.exists_constantFieldDescent K F hfg
  haveI : CharZero K₀ := (algebraMap K₀ K).charZero

  obtain ⟨Fc, _, _, _, _, _, _, _, _, hfgc, hgenc⟩ :=
    AlgebraicCurve.exists_constantFieldExtension K₀ F₀ ℂ hfg₀
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero

  have h1 := AlgebraicCurve.Pic0.natCard_torsion_eq_of_constantFieldExtension
    K₀ F₀ K F hfg₀ hfg hgen p hp
  have h2 := AlgebraicCurve.Pic0.natCard_torsion_eq_of_constantFieldExtension
    K₀ F₀ ℂ Fc hfg₀ hfgc hgenc p hp

  have h3 := AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_genus_complex Fc hfgc p
  have hne : Nat.card (Pic0.torsion K F p) ≠ 0 := by
    rw [h1, ← h2, h3]
    exact pow_ne_zero _ hp
  exact Nat.finite_of_card_ne_zero hne

end FinTorsCharZero

open AlgebraicCurve

theorem solution
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] (n : ℕ) (hn : n ≠ 0) :
    Finite {c : Pic0 K F // n • c = 0} :=
  FinTorsCharZero.finite_torsion_of_forall_prime
    (fun ℓ _ => FinTorsCharZero.finite_torsion_prime K F hfg ℓ) n hn
