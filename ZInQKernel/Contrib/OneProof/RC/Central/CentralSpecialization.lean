import Mathlib

/-!
# Lane RC15 (central): the algebra of Lemma `ex:arith-central-specialization`

The 11/5 manuscript (`diophantine_zq.tex`, lines 3894–3988): the central specialization of the
actual class is `z₀ = i(LmP)` (from the retained boundary (4.5)), the specialized paired
functional is the Kummer-dual functional of the same transported point,
`(λ_z)₀(i x) = PD_K(x, c_K(LmP))`, and on a rank-one Mordell–Weil free lattice both free-line
coefficients have valuation `j_rc(h,k) + v₂(Lm)`.

**Form.** The identity is stated on cohomology over the residue field (`ℚ₂` in the text): the three
comparison maps `i, s, q` are quasi-isomorphisms (tex 3958–3959), so `s` and `q` are taken as linear
equivalences, and the retained duality homotopies (tex 3960–3963) become the two equalities `hPD`
and `hc`. The cochain-level homotopies themselves are not modelled (DEPARTURE of form).

Every declaration in this file is `PROVED`; the inputs (4.5) and the two homotopy identities are
hypotheses (ELLIOT, tex 3911–3915 and 3960–3963).

* `central_functional_identity` (tex 3964–3971):
  `(λ_z)₀(i x) = PD_R(i x, j₀⁻¹ c(z₀)) = PD_K(x, s(qs)⁻¹ q c_K(LmP)) = PD_K(x, c_K(LmP))`.
* `addAut_int` (tex 3974–3977): an additive automorphism of the rank-one lattice `ℤ` is `±1`
  ("hence acts by `+1` or `−1`; it preserves the point index").
* `freeLine_valuations` (tex 3906–3907, 3978–3980): the class coefficient `Lm·n` and the functional
  coefficient `ε σ(Lm·n)` (`ε = ±1` the orientation sign of a unimodular pairing) both have
  `v₂ = v₂ n + v₂(Lm) = j_rc + v₂(Lm)`, and their product has `v₂ = 2 j_rc + 2 v₂(Lm)`
  (tex 4062–4064).
-/

namespace ZInQ.Manuscript.RC.Central

/-- **The specialized functional is the Kummer-dual functional of the same point**
(tex 3947–3971). Over a commutative ring `A₀` (the residue field `ℚ₂`), let `i : K₀ → R₀` be the
central Kummer comparison, `s : S₀ ≃ K₀^c` and `q : K₀^c ≃ R₀^c` the two quasi-isomorphisms with
`j₀ = q ∘ s`, `c` and `c_K` the conjugate-dual transports, and `PD_R`, `PD_K` the two pairings, with
the retained duality identities `PD_R(i x, y) = PD_K(x, s y)` and `c(i P) = q c_K(P)`. If
`z₀ = i(Lm • P)` (the boundary (4.5)), then the specialized functional
`(λ_z)₀ = PD_R(−, j₀⁻¹ c(z₀))` satisfies `(λ_z)₀(i x) = PD_K(x, c_K(Lm • P))`. PROVED. -/
theorem central_functional_identity {A₀ K₀ Kc R₀ Rc S₀ : Type*} [CommRing A₀]
    [AddCommGroup K₀] [Module A₀ K₀] [AddCommGroup Kc] [Module A₀ Kc]
    [AddCommGroup R₀] [Module A₀ R₀] [AddCommGroup Rc] [Module A₀ Rc]
    [AddCommGroup S₀] [Module A₀ S₀]
    (i : K₀ →ₗ[A₀] R₀) (s : S₀ ≃ₗ[A₀] Kc) (q : Kc ≃ₗ[A₀] Rc) (c : R₀ →ₗ[A₀] Rc)
    (cK : K₀ →ₗ[A₀] Kc) (PDR : R₀ →ₗ[A₀] S₀ →ₗ[A₀] A₀) (PDK : K₀ →ₗ[A₀] Kc →ₗ[A₀] A₀)
    (hPD : ∀ x y, PDR (i x) y = PDK x (s y)) (hc : ∀ P, c (i P) = q (cK P))
    {z₀ : R₀} {P : K₀} {Lm : A₀} (h45 : z₀ = i (Lm • P)) (x : K₀) :
    PDR (i x) ((s.trans q).symm (c z₀)) = PDK x (cK (Lm • P)) := by
  rw [hPD, h45, hc]
  congr 1
  simp [LinearEquiv.trans_symm]

/-- `s ∘ (q ∘ s)⁻¹ ∘ q = id` (tex 3968–3970): the step that needs `s` and `q` to be
quasi-isomorphisms separately, not only their composite. PROVED. -/
theorem comparison_cancel {A₀ Kc Rc S₀ : Type*} [CommRing A₀] [AddCommGroup Kc] [Module A₀ Kc]
    [AddCommGroup Rc] [Module A₀ Rc] [AddCommGroup S₀] [Module A₀ S₀]
    (s : S₀ ≃ₗ[A₀] Kc) (q : Kc ≃ₗ[A₀] Rc) (y : Kc) : s ((s.trans q).symm (q y)) = y := by
  simp [LinearEquiv.trans_symm]

/-- **An additive automorphism of a rank-one lattice is `±1`** (tex 3974–3977). PROVED. -/
theorem addAut_int (σ : ℤ ≃+ ℤ) : (∀ n, σ n = n) ∨ (∀ n, σ n = -n) := by
  have hσ : ∀ n : ℤ, σ n = n * σ 1 := by
    intro n
    have := map_zsmul σ n 1
    simpa [smul_eq_mul] using this
  have hunit : σ 1 * σ.symm 1 = 1 := by
    have h1 := hσ (σ.symm 1)
    rw [AddEquiv.apply_symm_apply] at h1
    linarith [h1, mul_comm (σ.symm 1) (σ 1)]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hunit with h | h
  · left; intro n; rw [hσ, h, mul_one]
  · right; intro n; rw [hσ, h, mul_neg_one]

/-- `v₂(± y) = v₂ y`. PROVED. -/
theorem padicValInt_neg (y : ℤ) : padicValInt 2 (-y) = padicValInt 2 y := by
  have h : padicValRat 2 ((-y : ℤ) : ℚ) = padicValRat 2 (y : ℚ) := by
    push_cast; exact padicValRat.neg _
  rw [padicValRat.of_int, padicValRat.of_int] at h
  exact_mod_cast h

/-- **Both free-line coefficients have valuation `j_rc + v₂(Lm)`** (tex 3906–3907, 3978–3980).
On the rank-one free lattice `ℤ g`, the point is `P = n g` with `j_rc = v₂ n` (the index
`[ℤ g : ℤ P] = |n|`). The class `Lm P` has coefficient `Lm n`; the conjugate transport `σ` is
`±1`; the functional's coefficient is `ε σ(Lm n)` with `ε = ±1` (unimodular pairing). Both
valuations equal `v₂ n + v₂(Lm)`, and the class-functional tensor has valuation
`2 v₂ n + 2 v₂(Lm)` (tex 4062–4064). PROVED. -/
theorem freeLine_valuations {L m n ε : ℤ} (σ : ℤ ≃+ ℤ) (hL : L ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0)
    (hε : ε = 1 ∨ ε = -1) :
    padicValInt 2 (L * m * n) = padicValInt 2 n + padicValInt 2 (L * m) ∧
      padicValInt 2 (ε * σ (L * m * n)) = padicValInt 2 n + padicValInt 2 (L * m) ∧
      padicValInt 2 ((L * m * n) * (ε * σ (L * m * n))) =
        2 * padicValInt 2 n + 2 * padicValInt 2 (L * m) := by
  have hLm : L * m ≠ 0 := mul_ne_zero hL hm
  have hc : L * m * n ≠ 0 := mul_ne_zero hLm hn
  have h1 : padicValInt 2 (L * m * n) = padicValInt 2 n + padicValInt 2 (L * m) := by
    rw [padicValInt.mul hLm hn, add_comm]
  have hσv : padicValInt 2 (ε * σ (L * m * n)) = padicValInt 2 (L * m * n) := by
    rcases addAut_int σ with h | h <;> rcases hε with rfl | rfl <;> simp [h, padicValInt_neg]
  have hσ0 : ε * σ (L * m * n) ≠ 0 := by
    rcases addAut_int σ with h | h <;> rcases hε with rfl | rfl <;> simp [h, hc]
  refine ⟨h1, hσv.trans h1, ?_⟩
  rw [padicValInt.mul hc hσ0, hσv, h1]; ring

end ZInQ.Manuscript.RC.Central
