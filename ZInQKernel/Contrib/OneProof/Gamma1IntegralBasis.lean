import ZInQKernel.Contrib.OneProof.EigenformCoeffFieldFinite

/-! # gamma1-basis: Shimura's integral basis of `S_k(Γ₁(N))` in its printed form

Task gamma1-basis (2026-11-17), report `docs/research/gamma1-basis.md`, scratch `scratch/gamma1-basis/`.

The open field `gamma1IntegralSpan : CoeffFieldFinite.Gamma1IntegralSpan` ("`S_k(Γ₁(N))` is spanned over `ℂ` by
forms with integral `q`-expansion", `k ≥ 2`) was rated LEAF strict but GLUE strictest by the leaf review of
2026-11-17: the step "a basis spans" sat inside the statement. Here the leaf is restated in the printed form,
the existence of a basis of `S_k(Γ₁(N))` whose members have rational integral Fourier coefficients
(`Gamma1IntegralBasis`), and the old statement is derived from it in proved glue:

* `gamma1IntegralSpan_of_basis : Gamma1IntegralBasis → CoeffFieldFinite.Gamma1IntegralSpan` (the field's proof;
  `Basis.span_eq` and `Submodule.span_mono`);
* `gamma1IntegralBasis_of_span : CoeffFieldFinite.Gamma1IntegralSpan → Gamma1IntegralBasis` (the converse,
  `exists_linearIndependent`): the two statements are equivalent, so the new leaf is neither stronger nor weaker
  than the old one, and it follows from the print whether the print says "has a basis" or "is spanned by".
-/

noncomputable section

namespace Gamma1Basis

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup

/-- **LEAF (Shimura's integral basis of `S_k(Γ₁(N))`, printed form).** For every `N ≥ 1` and every weight
`k ≥ 2`, the space `S_k(Γ₁(N))` of cusp forms of weight `k` on
`Γ₁(N) = {γ ∈ SL₂(ℤ) | γ ≡ (1 * ; 0 1) mod N}` (Mathlib's `CongruenceSubgroup.Gamma1 N`, a `≡ d ≡ 1`, `c ≡ 0`)
has a basis over `ℂ` consisting of forms whose Fourier coefficients at `∞` (the `q`-expansion in
`q = e^{2πiz}`, period `1`) are all rational integers.

Source: Shimura, *Introduction to the arithmetic theory of automorphic functions* (Iwanami Shoten and Princeton
University Press, 1971), §3.5, Thm 3.52 (number from memory, UNVERIFIED); also Diamond–Im, *Modular forms and
modular curves* (1995), §12.3 (`S_k(Γ₁(N), ℤ) ⊗ ℂ = S_k(Γ₁(N))`, UNVERIFIED), and Diamond–Shurman GTM 228 §6.5
for `k = 2` (UNVERIFIED). Printed form: "a basis with rational integral Fourier coefficients", for `Γ₁(N)` and
every weight `k ≥ 2`; the index type is arbitrary (the space is finite-dimensional, so any basis is finite). -/
def Gamma1IntegralBasis : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ), 2 ≤ k →
    ∃ (ι : Type) (b : Module.Basis ι ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)),
      ∀ (i : ι) (n : ℕ), ∃ z : ℤ, (qExpansion 1 (b i)).coeff n = z

/-- **The open field `gamma1IntegralSpan` from the printed integral basis** (glue: a basis spans, and the span
of the integral forms contains the span of the basis). -/
theorem gamma1IntegralSpan_of_basis (h : Gamma1IntegralBasis) : CoeffFieldFinite.Gamma1IntegralSpan := by
  intro N _ k hk
  obtain ⟨ι, b, hb⟩ := h N k hk
  rw [eq_top_iff, ← b.span_eq]
  exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hb i)

/-- **The converse**: the span statement gives a basis inside the integral forms (`exists_linearIndependent`),
so `Gamma1IntegralBasis` and `CoeffFieldFinite.Gamma1IntegralSpan` are equivalent. -/
theorem gamma1IntegralBasis_of_span (h : CoeffFieldFinite.Gamma1IntegralSpan) : Gamma1IntegralBasis := by
  intro N _ k hk
  set R := {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
    ∀ n : ℕ, ∃ z : ℤ, (qExpansion 1 g).coeff n = z}
  obtain ⟨s, hsR, hspan, hli⟩ := exists_linearIndependent ℂ R
  have hs : Submodule.span ℂ (Set.range ((↑) : s → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) = ⊤ := by
    rw [Subtype.range_coe, hspan]
    exact h N k hk
  refine ⟨s, Module.Basis.mk hli (top_le_iff.2 hs), fun i n => ?_⟩
  rw [Module.Basis.mk_apply]
  exact hsR i.2 n

/-- The bridge under the task's name: the new leaf gives the old statement. -/
theorem old_of_basis (h : Gamma1IntegralBasis) : CoeffFieldFinite.Gamma1IntegralSpan :=
  gamma1IntegralSpan_of_basis h

theorem gamma1IntegralBasis_iff_span :
    Gamma1IntegralBasis ↔ CoeffFieldFinite.Gamma1IntegralSpan :=
  ⟨gamma1IntegralSpan_of_basis, gamma1IntegralBasis_of_span⟩

end Gamma1Basis
