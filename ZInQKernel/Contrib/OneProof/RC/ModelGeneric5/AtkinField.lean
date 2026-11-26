import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Model

/-! The rational Atkin–Lehner pullback on the modular function field moves `j` to
`j(Qτ)`, a root of the classical modular polynomial `Φ_Q(X, j)`.

* `pullback_jq`: `AtkinRational.pullback hQ j = j_Q` in `modularFunctionField N`, since
  `j(W_Q τ) = j(Qτ)` (`AtkinRational.chart_coordinates`).
* `modularPolynomial_eval_field`: for every `M ∣ N` and every `ModularPolynomialData M`,
  `Φ_M(j_M, j) = 0` inside `modularFunctionField N` (the vendored Laurent-series identity,
  transported along the inclusion into Laurent series).

The matrix `W_Q` is that of Atkin–Lehner, *Hecke operators on Γ₀(m)*, Math. Ann. 185
(1970) (UNVERIFIED); `Φ_M` is monic over `ℤ[j]` (Lang, *Elliptic Functions*, 1987, Ch. 5,
UNVERIFIED), which the vendored `ModularPolynomialData.monic` records. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Function UpperHalfPlane ModularCurve ShimuraPointDict
open scoped Topology MatrixGroups TauCeti.ExactDivisor
open ZInQ.Manuscript.RC.AtkinPin ZInQ.Manuscript.RC.ModFnClassify
open ZInQ.Manuscript.RC.X0Model ZInQ.Manuscript.RC.AtkinRational

namespace ZInQ.Manuscript.RC.ModelGeneric5

open private fieldGerm_first from ZInQKernel.Contrib.OneProof.RC.AtkinRational.FunctionField

variable {N Q : ℕ} [NeZero N]

omit [NeZero N] in
theorem neZero_of_exact (hQ : Q ∥ N) : NeZero Q := ⟨hQ.ne_zero⟩

theorem neZero_div_of_exact (hQ : Q ∥ N) : NeZero (N / Q) :=
  ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hQ.dvd) hQ.pos).ne'⟩

/-- **The Atkin–Lehner pullback of `j` is `j(Qτ)`.** The pullback is composition with the
Möbius map of `atkinGL hQ`, and `j(W_Q τ) = j(Qτ)` for every `τ ∈ ℍ`. -/
theorem pullback_jq (hQ : Q ∥ N) :
    letI := neZero_of_exact hQ
    pullback hQ ⟨jq, jq_mem N⟩ = ⟨jqN Q, jqN_mem_of_dvd hQ.dvd⟩ := by
  letI := neZero_of_exact hQ
  letI := neZero_div_of_exact hQ
  let τ : ℍ := ⟨Complex.I, by simp⟩
  apply (fieldGerm N τ).injective
  apply Subtype.ext
  change meromorphicIncl (τ : ℂ) (fieldGerm N τ (pullback hQ ⟨jq, jq_mem N⟩)) =
    meromorphicIncl (τ : ℂ) (fieldGerm N τ ⟨jqN Q, jqN_mem_of_dvd hQ.dvd⟩)
  rw [fieldGerm_pullback, fieldGerm_jqN hQ.dvd]
  change pullPuncturedGerm hQ τ
    (meromorphicIncl _ (fieldGerm N (atkinGL hQ • τ) ⟨jq, jq_mem N⟩)) = _
  rw [fieldGerm_first]
  change ((((analyticJ ∘ ofComplex : ℂ → ℂ)) ∘ mobius hQ : ℂ → ℂ) : PuncturedGerm (τ : ℂ)) = _
  congr 1
  funext z
  simp only [Function.comp_apply, mobius, ofComplex_apply]
  exact (chart_coordinates hQ (ofComplex z)).1

/-- **`Φ_M(j_M, j) = 0` in the modular function field of level `N`**, for `M ∣ N`. -/
theorem modularPolynomial_eval_field {M : ℕ} [NeZero M] (hM : M ∣ N)
    (data : ModularPolynomialData M) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (modularFunctionField N))
      ⟨jq, jq_mem N⟩) ⟨jqN M, jqN_mem_of_dvd hM⟩ = 0 := by
  let F := modularFunctionField N
  let ι : F →+* LaurentSeries ℚ := F.toSubfield.subtype
  apply ι.injective
  rw [map_zero, Polynomial.hom_eval₂]
  have he : ι.comp (Polynomial.eval₂RingHom (Int.castRingHom F) ⟨jq, jq_mem N⟩) = evalAtJ := by
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (Subsingleton.elim (((ι.comp
        (Polynomial.eval₂RingHom (Int.castRingHom F) ⟨jq, jq_mem N⟩))).comp Polynomial.C)
          (evalAtJ.comp Polynomial.C)) a
    · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJ_X]
      rfl
  rw [he]
  exact data.eval_eq_zero

#print axioms pullback_jq
#print axioms modularPolynomial_eval_field

end ZInQ.Manuscript.RC.ModelGeneric5
