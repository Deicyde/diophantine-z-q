import ZInQKernel.Contrib.OneProof.GrossZagierAlgebraic
import ZInQKernel.Contrib.OneProof.Gamma0QExp.Cosets

/-!
# The `q`-expansion principle for `Γ₀(N)` (task gamma0-qexp)

Proves `ZInQ.GZAlg.Gamma0QExpansion` (`ZInQKernel/Contrib/OneProof/GrossZagierAlgebraic.lean`):
for `N ≥ 1`, a meromorphic modular function `g` for `Γ₀(N)` (`ZInQ.GZHeegner.IsRatModFnMero N g`)
whose `q`-expansion `x` at `∞` is rational lies in `ℚ(jq, jq(q^N)) = X0Field N`.

Proof (classical; Shimura 1971 §6.2–6.9, Diamond–Shurman §7.5–7.7, UNVERIFIED locators):
1. `analytic_core` (`Gamma0QExp/Cosets.lean`): `B(j, j_N)·g = A(j, j_N)` on punctured
   neighbourhoods of every point of `ℍ`, `A, B ∈ ℂ[X, Y]`, `B(j, j_N) ≢ 0` (symmetric functions of
   the `SL₂(ℤ)/Γ₀(N)`-conjugates, meromorphic level-one functions are rational in `j`
   (`Gamma0QExp/LevelOneMero.lean`), separation of the conjugates of `j_N`).
2. Bridge (`Gamma0QExp/QSeries.lean`): the identity holds for the `q`-expansions in `ℂ((q))`
   (shift `τ ↦ τ + it` into the region where the expansion of `g` converges, continuity of
   `q`-series, uniqueness of coefficients).
3. Descent (`Gamma0QExp/Descent.lean`): a `ℚ`-linear functional `ℂ → ℚ` turns it into a relation
   over `ℚ`, so `x ∈ ℚ(jq, jqN)`.

No new hypotheses: the theorem has exactly the type `ZInQ.GZAlg.Gamma0QExpansion`.
No `sorry`, no `axiom`.
-/

noncomputable section

open UpperHalfPlane ModularCurve Filter Topology
open scoped MatrixGroups

namespace ZInQ.Contrib.Gamma0QExp

open ZInQ.Gamma0QExp


theorem qPar_eq_qParam (τ : ℍ) : ZInQ.GZAlg.qPar τ = Function.Periodic.qParam 1 (τ : ℂ) := by
  simp [ZInQ.GZAlg.qPar, Function.Periodic.qParam]

/-- `aeval (jq, jqN)` of a two-variable polynomial as a `ℂ`-combination of elements of
`ℚ(jq, jqN)`. -/
theorem aeval_eq_sum (N : ℕ) [NeZero N] (P : MvPolynomial (Fin 2) ℂ)
    (S : Finset (Fin 2 →₀ ℕ)) (hS : P.support ⊆ S) :
    MvPolynomial.aeval ![coeffEmb ℂ jq, coeffEmb ℂ (jqN N)] P =
      ∑ s ∈ S, HahnSeries.C (P.coeff s) * coeffEmb ℂ (jq ^ s 0 * jqN N ^ s 1) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Finset.sum_subset hS (fun s _ hs => ?_) |>.trans (Finset.sum_congr rfl fun s _ => ?_)
  · rw [MvPolynomial.notMem_support_iff.1 hs, map_zero, zero_mul]
  · rw [Fin.prod_univ_two, algebraMap_laurentSeries_eq_single, map_mul, map_pow, map_pow]
    rfl

/-- **The `q`-expansion principle for `Γ₀(N)` with rational coefficients.** -/
theorem gamma0QExpansion_proof : ZInQ.GZAlg.Gamma0QExpansion := by
  intro N _ g hg x hx
  obtain ⟨hinv, hmer, hgr, -⟩ := hg
  obtain ⟨A, B, ⟨τ₀, hτ₀⟩, hid⟩ := analytic_core N g hinv hmer hgr
  set v : Fin 2 → LaurentSeries ℂ := ![coeffEmb ℂ jq, coeffEmb ℂ (jqN N)]
  set Fv : Fin 2 → ℍ → ℂ := ![jf, jN N]
  have hFv : ∀ τ : ℍ, (fun i => Fv i τ) = ![jf τ, jN N τ] := fun τ => by
    funext i; fin_cases i <;> rfl
  have hrzv : ∀ i, Rz (v i) (Fv i) := by
    intro i; fin_cases i
    · exact rz_jq
    · exact rz_jqN N
  -- `B(jq, jqN) ≠ 0`
  have hBne : MvPolynomial.aeval v B ≠ 0 := by
    intro h0
    have h1 := Rz.aeval v Fv hrzv B τ₀
    rw [h0] at h1
    simp only [HahnSeries.coeff_zero, zero_mul] at h1
    apply hτ₀
    rw [← hFv τ₀]
    exact (h1.unique hasSum_zero)
  -- shift into the region of convergence of the expansion of `g`
  obtain ⟨T, hT⟩ := hx
  set t : ℝ := max T 0 + 1
  have ht : 0 ≤ t := by positivity
  have hxz : Rz (qTwist (rUnit t) (coeffEmb ℂ x)) (g ∘ shiftH t ht) := by
    refine rz_qTwist_of t ht fun τ => ?_
    have h1 := hT (shiftH t ht τ) (by
      rw [im_shiftH]; have := τ.im_pos; have := le_max_left T 0; linarith)
    simpa only [coeffEmb_coeff_eq, qPar_eq_qParam] using h1
  have hvz : ∀ i, Rz (qTwist (rUnit t) (v i)) (Fv i ∘ shiftH t ht) := fun i =>
    rz_qTwist t ht (hrzv i)
  set L := MvPolynomial.aeval v B * coeffEmb ℂ x - MvPolynomial.aeval v A
  have hL : Rz (qTwist (rUnit t) L) ((fun τ => MvPolynomial.eval ![jf τ, jN N τ] B * g τ -
      MvPolynomial.eval ![jf τ, jN N τ] A) ∘ shiftH t ht) := by
    have h1 := ((Rz.aeval _ _ hvz B).mul hxz).sub (Rz.aeval _ _ hvz A)
    rw [show qTwist (rUnit t) L = MvPolynomial.aeval (fun i => qTwist (rUnit t) (v i)) B *
        qTwist (rUnit t) (coeffEmb ℂ x) - MvPolynomial.aeval (fun i => qTwist (rUnit t) (v i)) A by
      rw [map_sub, map_mul, qTwist_aeval, qTwist_aeval]]
    refine h1.congr_fun fun τ => ?_
    simp only [Function.comp_apply]
    rw [← hFv]
  have hL0 : L = 0 := eq_zero_of_rz_shift t ht hL fun w =>
    (hid w).mono fun z hz => sub_eq_zero.2 hz
  have hrel : MvPolynomial.aeval v B * coeffEmb ℂ x = MvPolynomial.aeval v A := sub_eq_zero.1 hL0
  -- descent
  set S := B.support ∪ A.support
  rw [aeval_eq_sum N B S Finset.subset_union_left, aeval_eq_sum N A S Finset.subset_union_right]
    at hrel
  rw [aeval_eq_sum N B S Finset.subset_union_left] at hBne
  have hu : ∀ s ∈ S, jq ^ s 0 * jqN N ^ s 1 ∈ ZInQ.GZAlg.X0Field N := fun s _ =>
    (ZInQ.GZAlg.X0Field N).mul_mem (pow_mem (jq_mem N) _)
      (pow_mem (show jqN N ∈ ZInQ.GZAlg.X0Field N from jqN_mem N) _)
  exact mem_of_complex_relation (ZInQ.GZAlg.X0Field N) S _ _ hu hu _ _ x hrel hBne

end ZInQ.Contrib.Gamma0QExp
