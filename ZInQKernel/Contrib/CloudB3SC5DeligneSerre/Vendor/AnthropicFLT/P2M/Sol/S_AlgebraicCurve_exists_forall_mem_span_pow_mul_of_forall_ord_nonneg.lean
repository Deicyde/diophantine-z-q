/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg (git blob e73ec522d70842db4d2d8ff3f408f2cf4172f0d1, sha256 b222c5237da1773125ef776e2ae66e233fb49f771829f7d063926aa7703afd6d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg

set_option autoImplicit false
set_option maxHeartbeats 8000000

open AlgebraicCurve

noncomputable section

theorem fd_lSpace_nsmul_poleDivisor
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)) := by
  haveI : IsCurveOver K F :=
    AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hell0 : ell (0 : Divisor K F) = 1 :=
    (AlgebraicCurve.exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental x hx D hD).1
  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) :=
    FiniteDimensional.of_finrank_eq_succ (n := 0) hell0
  exact fun M => AlgebraicCurve.finiteDimensional_lSpace (M • D)

theorem exists_mem_lSpace_nsmul_of_forall_ord_nonneg
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (h : F) (hh : ∀ v : Place K F, 0 ≤ v.ord x → 0 ≤ v.ord h) :
    ∃ M : ℕ, h ∈ LSpace (M • D) := by
  rcases eq_or_ne h 0 with rfl | hh0
  · exact ⟨0, (LSpace _).zero_mem⟩
  refine ⟨D.support.sup (fun v => (-(v.ord h)).toNat), mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)⟩
  set M := D.support.sup (fun v => (-(v.ord h)).toNat) with hM
  simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul, neg_le]

  by_cases hv : v ∈ D.support
  · have hDv1 : (1:ℤ) ≤ D v := by
      have hne := Finsupp.mem_support_iff.mp hv
      have := hD v; omega
    have hMv : ((-(v.ord h)).toNat : ℤ) ≤ (M:ℤ) := by
      have h' := Finset.le_sup (f := fun w => (-(w.ord h)).toNat) hv
      exact_mod_cast h'
    calc -(v.ord h) ≤ ((-(v.ord h)).toNat : ℤ) := Int.self_le_toNat _
      _ ≤ (M:ℤ) := hMv
      _ = (M:ℤ) * 1 := (mul_one _).symm
      _ ≤ (M:ℤ) * D v := mul_le_mul_of_nonneg_left hDv1 (Nat.cast_nonneg M)
  · have hDv0 : D v = 0 := Finsupp.notMem_support_iff.mp hv
    rw [hDv0, mul_zero]
    have hox : 0 ≤ v.ord x := by
      have := hD v; rw [hDv0] at this; omega
    exact neg_nonpos_of_nonneg (hh v hox)

theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ∃ M₁ : ℕ, ∀ h : F, (∀ v : Place K F, 0 ≤ v.ord x → 0 ≤ v.ord h) →
      h ∈ Submodule.span K {g : F | ∃ j : ℕ, ∃ y ∈ LSpace (M₁ • D), g = x ^ j * y} := by
  classical
  obtain ⟨_, M₀, hM₀1, hell⟩ :=
    AlgebraicCurve.exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental x hx D hD
  have hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)) :=
    fd_lSpace_nsmul_poleDivisor x hx D hD
  set M₁ := M₀ + 1
  refine ⟨M₁, fun h hh => ?_⟩
  set SP := Submodule.span K {g : F | ∃ j : ℕ, ∃ y ∈ LSpace (M₁ • D), g = x ^ j * y} with hSP

  have hD0 : (0 : Divisor K F) ≤ D := fun v => by rw [hD]; exact le_max_left _ _

  have hbase : (LSpace (M₁ • D) : Submodule K F) ≤ SP := fun y hy =>
    Submodule.subset_span ⟨0, y, hy, by rw [pow_zero, one_mul]⟩

  have hxSP : (SP.map (LinearMap.mulLeft K x) : Submodule K F) ≤ SP := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, y, hy, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨j+1, y, hy, ?_⟩
    rw [LinearMap.mulLeft_apply]; ring

  have hup : ∀ k, (LSpace ((M₁ + k) • D) : Submodule K F) ≤ SP := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ n ih =>
      have hdegD : (0:ℤ) ≤ Divisor.degree D := by
        simp only [Divisor.degree, Finsupp.liftAddHom_apply, AddMonoidHom.coe_mulRight,
          Finsupp.sum]
        exact Finset.sum_nonneg fun v _ => mul_nonneg (by simpa using hD0 v) (Nat.cast_nonneg _)
      have hstep := AlgebraicCurve.lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
        x D hD hFD M₀ (Divisor.degree D).toNat (genusFF K F)
        (fun N hN => by rw [hell N hN, Int.toNat_of_nonneg hdegD])
        (M₁ + n) (by omega)
      refine hstep.trans (sup_le ih ?_)
      exact (Submodule.map_mono ih).trans hxSP

  have hall : ∀ m, (LSpace (m • D) : Submodule K F) ≤ SP := fun m => by
    refine (lSpace_mono ?_).trans (hup m)

    intro v
    have hDv : (0:ℤ) ≤ D v := by simpa using hD0 v
    simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul]
    have hmle : (m:ℤ) ≤ ((M₁+m:ℕ):ℤ) := by exact_mod_cast Nat.le_add_left m M₁
    exact mul_le_mul_of_nonneg_right hmle hDv

  obtain ⟨M, hMmem⟩ := exists_mem_lSpace_nsmul_of_forall_ord_nonneg x D hD h hh
  exact hall M hMmem
