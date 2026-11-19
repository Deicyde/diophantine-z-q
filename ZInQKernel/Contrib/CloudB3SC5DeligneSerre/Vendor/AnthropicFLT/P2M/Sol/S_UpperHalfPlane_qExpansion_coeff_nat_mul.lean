/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_UpperHalfPlane_qExpansion_coeff_nat_mul (git blob 115409db8f732c16e66fe3f0aa6b153e38f0ae6c, sha256 8ed2d2b1fc9c08829fd58abb18265a8955beb1395f9234dc4f4ddb8f9bc634fd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_UpperHalfPlane_qExpansion_coeff_nat_mul

set_option autoImplicit false

noncomputable section

open Complex Filter Function UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass

open scoped Real MatrixGroups Topology Manifold

def W26FnLike : Type := ℍ → ℂ

scoped instance : FunLike W26FnLike ℍ ℂ where
  coe f := f
  coe_injective _ _ h := h

theorem solution {h : ℝ} (hh : 0 < h) {F : ℍ → ℂ} (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) h) (hhol : MDiff F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) {M : ℕ} (hM : 0 < M) (n : ℕ) : (qExpansion (M * h) F).coeff n = if M ∣ n then (qExpansion h F).coeff (n / M) else 0 := by
  have hMh : 0 < (M : ℝ) * h := by positivity
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hper' : Periodic (F ∘ ofComplex) (((M : ℝ) * h : ℝ) : ℂ) := by
    simpa using hper.nat_mul M
  have han : AnalyticAt ℂ (cuspFunction (M * h) F) 0 :=
    analyticAt_cuspFunction_zero hMh hper' hhol hbdd

  set c : ℕ → ℂ := fun n ↦ if M ∣ n then (qExpansion h F).coeff (n / M) else 0 with hc
  have hsum : ∀ τ : ℍ, HasSum (fun m ↦ c m • Periodic.qParam (M * h) τ ^ m) (F τ) := by
    intro τ
    have hq : Periodic.qParam h τ = Periodic.qParam (M * h) τ ^ M := by
      simp only [Periodic.qParam, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    have hs := hasSum_qExpansion hh hper hhol hbdd τ
    simp_rw [hq, ← pow_mul] at hs
    have hinj : Injective (fun m : ℕ ↦ M * m) := mul_right_injective₀ hM.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ ↦ M * m),
        (fun m ↦ c m • Periodic.qParam (M * h) τ ^ m) x = 0 := by
      intro x hx
      have : ¬ M ∣ x := by
        rintro ⟨d, rfl⟩
        exact hx ⟨d, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).mp ?_
    convert hs using 1
    ext m
    simp [hc, Nat.mul_div_cancel_left _ hM]

  have key := qExpansion_coeff_unique (F := W26FnLike) (show W26FnLike from F) hMh han hsum n
  exact key.symm

end
