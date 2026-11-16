/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_Velu
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VeluOrderTwo
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_isElliptic_veluQuotient2_of_isElliptic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_exists_enum_twoTorsion_veluQuotient2_discriminant_ne_zero

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

theorem EnumTwoAux.twoTorsionPair {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) {x₀ : K}
    (hx : 4 * x₀ ^ 3 + W.b₂ * x₀ ^ 2 + 2 * W.b₄ * x₀ + W.b₆ = 0) :
    W.toAffine.Equation x₀ (-(W.a₁ * x₀ + W.a₃) / 2) ∧
      W.veluGy x₀ (-(W.a₁ * x₀ + W.a₃) / 2) = 0 := by
  constructor
  · rw [Affine.equation_iff]
    simp only [b₂, b₄, b₆] at hx
    field_simp
    linear_combination -hx
  · simp only [veluGy]
    field_simp
    ring

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic] :
    ∃ (ι : Type) (_ : Fintype ι), Fintype.card ι = 3 ∧
      ∃ P : ι → K × K, Function.Injective P ∧
        (∀ i, W.toAffine.Equation (P i).1 (P i).2) ∧ (∀ i, W.veluGy (P i).1 (P i).2 = 0) ∧
        ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0 := by
  classical

  set C3 : Cubic K := W.twoTorsionPolynomial with hC3
  have ha : C3.a ≠ 0 := by
    show (4 : K) ≠ 0
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hsplit : (Polynomial.map (RingHom.id K) C3.toPoly).Splits := IsAlgClosed.splits _
  obtain ⟨x₁, x₂, x₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplit
  have hdisc : C3.discr ≠ 0 :=
    W.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2) W.isUnit_Δ
  have hnodup : (Cubic.map (RingHom.id K) C3).roots.Nodup :=
    (Cubic.discr_ne_zero_iff_roots_nodup ha hsplit).mp hdisc
  rw [h3] at hnodup
  have h12 : x₁ ≠ x₂ := by intro h; subst h; simp at hnodup
  have h13 : x₁ ≠ x₃ := by intro h; subst h; simp at hnodup
  have h23 : x₂ ≠ x₃ := by intro h; subst h; simp at hnodup
  have ha' : (Cubic.map (RingHom.id K) C3).a ≠ 0 := by simpa [Cubic.map] using ha
  have hroot : ∀ x ∈ ({x₁, x₂, x₃} : Multiset K),
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ = 0 := by
    intro x hx
    have hx' : x ∈ (Cubic.map (RingHom.id K) C3).roots := by rw [h3]; exact hx
    have := (Cubic.mem_roots_iff (Cubic.ne_zero_of_a_ne_zero ha') x).mp hx'
    simpa [Cubic.map, hC3, twoTorsionPolynomial] using this

  let yy : K → K := fun x => -(W.a₁ * x + W.a₃) / 2
  let P : Fin 3 → K × K := ![(x₁, yy x₁), (x₂, yy x₂), (x₃, yy x₃)]
  have hPfst : ∀ i, (P i).1 ∈ ({x₁, x₂, x₃} : Multiset K) := by
    intro i; fin_cases i <;> simp [P]
  have hPsnd : ∀ i, (P i).2 = yy (P i).1 := by
    intro i; fin_cases i <;> rfl
  have hPpair : ∀ i, W.toAffine.Equation (P i).1 (P i).2 ∧ W.veluGy (P i).1 (P i).2 = 0 := by
    intro i; rw [hPsnd]; exact EnumTwoAux.twoTorsionPair h2 W (hroot _ (hPfst i))
  have hPinj : Function.Injective P := by
    intro i i' h
    have h1 := congrArg Prod.fst h
    fin_cases i <;> fin_cases i' <;> simp [P] at h1 ⊢ <;> simp_all
  have hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0 := fun i =>
    (@WeierstrassCurve.isUnit_Δ _ _ (W.veluQuotient2 (P i).1 (P i).2)
      (WeierstrassCurve.isElliptic_veluQuotient2_of_isElliptic (hPpair i).1 (hPpair i).2)).ne_zero
  exact ⟨Fin 3, inferInstance, Fintype.card_fin 3, P, hPinj, fun i => (hPpair i).1, fun i => (hPpair i).2, hΔ⟩
