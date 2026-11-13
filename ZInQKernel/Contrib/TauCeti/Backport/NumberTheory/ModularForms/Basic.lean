/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 4d91513e4d30, module
-- TauCeti.NumberTheory.ModularForms.Basic), Apache-2.0: declarations added to that module after
-- commit 5a01f5fe, whose version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Basic

/-! # Restricting a trace along a factorization (backport) -/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane

open scoped Manifold MatrixGroups ModularForm Pointwise

section ChangeGroup

variable {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

section RestrictTrace

variable {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex Γ] [𝒢.IsFiniteRelIndex Γ']

/-- **Restricting a trace along a factorization.** Let `Γ' ≤ Γ` be such that every element of `Γ`
is a product `x * g` with `x ∈ Γ'` and `g ∈ 𝒢`. Then the trace from `𝒢` to `Γ`, restricted to
`Γ'`, is the trace from `𝒢` to `Γ'`.

For congruence subgroups, with `𝒢 = Γ₁(b)`, `Γ = Γ₁(gcd a b)` and `Γ' = Γ₁(a)`
(`CongruenceSubgroup.exists_mul_eq_of_mem_Gamma1_gcd`), it says that the trace from `Γ₁(lcm a b)`
to `Γ₁(a)` of a form of level `Γ₁(b)` is its trace from `Γ₁(b)` to `Γ₁(gcd a b)`, restricted to
`Γ₁(a)`. -/
lemma SlashInvariantForm.restrict_trace (hΓ' : Γ' ≤ Γ)
    (hmul : ∀ h ∈ Γ, ∃ x ∈ Γ', ∃ g ∈ 𝒢, x * g = h) (f : SlashInvariantForm 𝒢 k) :
    restrict hΓ' (SlashInvariantForm.trace Γ f) = SlashInvariantForm.trace Γ' f := by
  let := Fintype.ofFinite (Γ ⧸ 𝒢.subgroupOf Γ)
  let := Fintype.ofFinite (Γ' ⧸ 𝒢.subgroupOf Γ')
  -- the two traces sum over `Γ' ⧸ (𝒢 ⊓ Γ')` and `Γ ⧸ (𝒢 ⊓ Γ)`; the coset map induced by the
  -- inclusion `Γ' → Γ` is injective, and the factorization hypothesis makes it surjective
  let e := Subgroup.quotientSubgroupOfEmbeddingOfLE 𝒢 hΓ'
  have he : Function.Bijective e := by
    refine ⟨e.injective, fun q ↦ ?_⟩
    induction q using QuotientGroup.induction_on with | H h => ?_
    obtain ⟨x, hx, g, hg, hxg⟩ := hmul h h.2
    refine ⟨QuotientGroup.mk ⟨x, hx⟩, Quotient.sound' ?_⟩
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    simpa [← hxg] using hg
  ext τ
  rw [coe_restrict, coe_trace, coe_trace, Finset.sum_apply, Finset.sum_apply]
  refine (Fintype.sum_bijective e he _ _ fun q ↦ ?_).symm
  induction q using QuotientGroup.induction_on with
  | H x => simp [e, Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, quotientFunc_mk]

/-- **Restricting a trace along a factorization**, for modular forms: see
`SlashInvariantForm.restrict_trace`. -/
lemma ModularForm.restrict_trace (hΓ' : Γ' ≤ Γ)
    (hmul : ∀ h ∈ Γ, ∃ x ∈ Γ', ∃ g ∈ 𝒢, x * g = h) (f : ModularForm 𝒢 k) :
    restrict hΓ' (ModularForm.trace Γ f) = ModularForm.trace Γ' f :=
  ModularForm.ext fun τ ↦ congrFun (congrArg DFunLike.coe
    (SlashInvariantForm.restrict_trace hΓ' hmul f.toSlashInvariantForm)) τ

/-- **Restricting a trace along a factorization**, for cusp forms: see
`SlashInvariantForm.restrict_trace`. -/
lemma CuspForm.restrict_trace (hΓ' : Γ' ≤ Γ)
    (hmul : ∀ h ∈ Γ, ∃ x ∈ Γ', ∃ g ∈ 𝒢, x * g = h) (f : CuspForm 𝒢 k) :
    restrict hΓ' (CuspForm.trace Γ f) = CuspForm.trace Γ' f :=
  CuspForm.ext fun τ ↦ congrFun (congrArg DFunLike.coe
    (SlashInvariantForm.restrict_trace hΓ' hmul f.toSlashInvariantForm)) τ

end RestrictTrace

end ChangeGroup
