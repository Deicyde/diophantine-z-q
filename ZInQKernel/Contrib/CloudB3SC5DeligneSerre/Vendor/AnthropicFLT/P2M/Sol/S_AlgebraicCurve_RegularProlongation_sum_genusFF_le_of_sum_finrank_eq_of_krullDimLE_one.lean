/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one (git blob 224c160388e52006030771384beb44a0c3f792c4, sha256 856254808af739187098947a8b00119612002602cfbfb549241acf15976f25d6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RegularProlongation_span_residue_lSpace_le_residueSpan_inf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_finrank_residueSpan_inf_add_card_le
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RegularProlongation_finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_poleDivisor_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RegularProlongation_finiteDimensional_adjoin_residue_of_sum_finrank_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one.AlgebraicCurve
end P2MW.S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one.AlgebraicCurve
namespace IsLocalRing
end IsLocalRing
namespace AlgebraicCurve.RegularProlongation
end AlgebraicCurve.RegularProlongation

namespace P2MW.S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one

set_option autoImplicit false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one.AlgebraicCurve
open _root_.IsLocalRing

namespace AlgebraicCurve
export _root_.AlgebraicCurve (RegularProlongation Place Divisor Divisor.degree genusFF IsCurveOver LSpace ell RegularProlongation.span_residue_lSpace_le_residueSpan_inf RegularProlongation.exists_forall_finrank_residueSpan_inf_add_card_le RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one RegularProlongation.finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq finiteDimensional_lSpace isCurveOver_of_isAlgClosed_of_transcendental exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental exists_poleDivisor_of_transcendental degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq)
namespace RegularProlongation
export _root_.AlgebraicCurve.RegularProlongation (integers residue span_residue_lSpace_le_residueSpan_inf exists_forall_finrank_residueSpan_inf_add_card_le exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq finiteDimensional_adjoin_residue_of_sum_finrank_eq)
namespace KD1
open _root_.AlgebraicCurve.RegularProlongation
open _root_.AlgebraicCurve

theorem ell_add_card_le
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (D : Divisor L F) (hD : ∀ v : Place L F, D v = max 0 (-v.ord f))
    (Db : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fb i))
    (hDb : ∀ i, ∀ w : Place (IsLocalRing.ResidueField A) (Fb i),
      Db i w = max 0 (-w.ord ((R i).residue ⟨f, hf i⟩))) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ell (M • D) + Fintype.card ι ≤ (∑ i, ell (M • Db i)) + 1 := by
  classical
  haveI := hfd

  haveI : IsCurveOver L F := isCurveOver_of_isAlgClosed_of_transcendental f htrL
  obtain ⟨hℓ0, -⟩ := exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental f htrL D hD
  haveI hL0 : FiniteDimensional L ↥(LSpace (0 : Divisor L F)) :=
    Module.finite_of_finrank_pos (by
      change 0 < ell (0 : Divisor L F)
      omega)

  obtain ⟨M₀, hM₀⟩ :=
    RegularProlongation.exists_forall_finrank_residueSpan_inf_add_card_le
      A Fb R hR f hf htrL hfd htr heq Db hDb
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨hfin, hcount⟩ := hM₀ M hM

  set ST : Submodule (IsLocalRing.ResidueField A) (∀ i, Fb i) :=
    Submodule.span (IsLocalRing.ResidueField A)
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} with hST
  set STM : Submodule (IsLocalRing.ResidueField A) (∀ i, Fb i) :=
    Submodule.span (IsLocalRing.ResidueField A)
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
          u * (f ^ M)⁻¹ ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} with hSTM
  set ST0 : Submodule (IsLocalRing.ResidueField A) (∀ i, Fb i) :=
    Submodule.span (IsLocalRing.ResidueField A)
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i} with hST0

  have hlift := RegularProlongation.span_residue_lSpace_le_residueSpan_inf A Fb R f hf hfd D hD M
  haveI : FiniteDimensional L ↥(LSpace (M • D)) := finiteDimensional_lSpace (M • D)
  have hdim := RegularProlongation.finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
    A Fb R hR f hf htr heq (LSpace (M • D))
  have h1 : ell (M • D) ≤ Module.finrank (IsLocalRing.ResidueField A) ↥(ST ⊓ STM) := by
    have := Submodule.finrank_mono (R := IsLocalRing.ResidueField A) hlift
    change Module.finrank L ↥(LSpace (M • D)) ≤ _
    rw [← hdim]
    exact this

  have hle : ST ⊓ ST0 ≤ Submodule.span (IsLocalRing.ResidueField A) {(1 : ∀ i, Fb i)} := by
    intro x hx
    obtain ⟨c, hc⟩ :=
      RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one
        A Fb R hR f hf htrL hfd htr heq x hx.1 hx.2
    have hx' : x = c • (1 : ∀ i, Fb i) := by
      funext i
      simp [hc i, Algebra.algebraMap_eq_smul_one]
    rw [hx']
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  have h2 : Module.finrank (IsLocalRing.ResidueField A) ↥(ST ⊓ ST0) ≤ 1 := by
    calc Module.finrank (IsLocalRing.ResidueField A) ↥(ST ⊓ ST0)
        ≤ Module.finrank (IsLocalRing.ResidueField A)
            ↥(Submodule.span (IsLocalRing.ResidueField A) {(1 : ∀ i, Fb i)}) :=
          Submodule.finrank_mono hle
      _ ≤ ({(1 : ∀ i, Fb i)} : Set (∀ i, Fb i)).toFinset.card := finrank_span_le_card _
      _ = 1 := by simp
  omega

theorem main
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∑ i, genusFF (IsLocalRing.ResidueField A) (Fb i) ≤ genusFF L F := by
  classical
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F := hfd
  haveI hfdᵢ : ∀ i, FiniteDimensional
      (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) := fun i =>
    RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq
      A Fb R hR f hf htr heq i

  obtain ⟨D, hD⟩ := exists_poleDivisor_of_transcendental f htrL
  have hDbex : ∀ i, ∃ Db : Divisor (ResidueField A) (Fb i),
      ∀ w, Db w = max 0 (-w.ord ((R i).residue ⟨f, hf i⟩)) := fun i =>
    exists_poleDivisor_of_transcendental ((R i).residue ⟨f, hf i⟩) (htr i)
  choose Db hDb using hDbex

  have hdegD : Divisor.degree D =
      (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F : ℤ) :=
    degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental f htrL D hD
  have hdegDb : ∀ i, Divisor.degree (Db i) =
      (Module.finrank (IntermediateField.adjoin (ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) : ℤ) := fun i =>
    degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
      ((R i).residue ⟨f, hf i⟩) (htr i) (Db i) (hDb i)
  have hsumdeg : ∑ i, Divisor.degree (Db i) = Divisor.degree D := by
    simp_rw [hdegDb, hdegD]
    exact_mod_cast congrArg (Nat.cast (R := ℤ)) heq

  obtain ⟨hℓ0F, M₁, -, hRRF⟩ :=
    exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental f htrL D hD
  have hRRᵢ : ∀ i, ∃ Mi : ℕ, 1 ≤ Mi ∧ ∀ N, Mi ≤ N →
        (ell (N • Db i) : ℤ) =
          N * Divisor.degree (Db i) + 1 - genusFF (ResidueField A) (Fb i) := fun i =>
    (exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
      ((R i).residue ⟨f, hf i⟩) (htr i) (Db i) (hDb i)).2
  choose Mᵢ _hMᵢ hRRbᵢ using hRRᵢ

  obtain ⟨M₀, hM₀⟩ := ell_add_card_le
    A Fb R hR f hf htrL hfd htr heq D hD Db hDb

  let M : ℕ := max (max M₀ M₁) (Finset.univ.sup Mᵢ)
  have hM0 : M₀ ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hM1 : M₁ ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hMᵢ : ∀ i, Mᵢ i ≤ M := fun i =>
    (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)
  have hmain := hM₀ M hM0
  have hmainZ : (ell (M • D) : ℤ) + Fintype.card ι ≤ (∑ i, (ell (M • Db i) : ℤ)) + 1 := by
    exact_mod_cast hmain
  have hlhs : (ell (M • D) : ℤ) = (M : ℤ) * Divisor.degree D + 1 - genusFF L F := hRRF M hM1
  have hrhs : ∑ i, (ell (M • Db i) : ℤ)
      = (M : ℤ) * Divisor.degree D + Fintype.card ι
          - ∑ i, (genusFF (ResidueField A) (Fb i) : ℤ) := by
    calc ∑ i, (ell (M • Db i) : ℤ)
        = ∑ i, ((M : ℤ) * Divisor.degree (Db i) + 1 - genusFF (ResidueField A) (Fb i)) :=
          Finset.sum_congr rfl fun i _ => hRRbᵢ i M (hMᵢ i)
      _ = (M : ℤ) * ∑ i, Divisor.degree (Db i) + ∑ i, (1 : ℤ)
            - ∑ i, (genusFF (ResidueField A) (Fb i) : ℤ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (M : ℤ) * Divisor.degree D + Fintype.card ι
            - ∑ i, (genusFF (ResidueField A) (Fb i) : ℤ) := by
          rw [hsumdeg]; simp
  rw [hlhs, hrhs] at hmainZ
  have hZ : (∑ i, (genusFF (ResidueField A) (Fb i) : ℤ)) ≤ (genusFF L F : ℤ) := by linarith
  exact_mod_cast hZ

end AlgebraicCurve.RegularProlongation.KD1

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∑ i, genusFF (IsLocalRing.ResidueField A) (Fb i) ≤ genusFF L F :=
  AlgebraicCurve.RegularProlongation.KD1.main A Fb R hR f hf htrL hfd htr heq
