import ZInQKernel.Contrib.OneProof.ColmezTiltIso.Ring

/-!
# Colmez's `θ`, as printed, is Mathlib's `fontaineTheta`

Colmez, Math. Ann. 292 (1992), §2, p. 632: "Soit θ l'homomorphisme de W(R) dans O_{C_p} qui à
(x_0,x_1,…,x_n,…) = Σ p^n[x_n^{p^{-n}}] associe Σ p^n x_n^{(n)}."

* `witt_expansion`: in `W(A)` for a perfect ring `A` of characteristic `p`, the printed identity
  `(x_0,x_1,…) = Σ p^n [x_n^{p^{-n}}]` holds modulo `p^N`, for every `N`.
* `wittEquiv : W(ColmezR O p) ≃+* W(PreTilt O p)`, the isomorphism `WittVector.map colmezEquiv`.
* `colmezTheta = fontaineTheta ∘ wittEquiv`, and **`isPAdicLim_colmezTheta`**: `colmezTheta w` is
  the `p`-adic limit of the printed partial sums `Σ_{n<N} p^n x_n^{(n)}`, where `x_n` is the `n`-th
  Witt coordinate of `w`. By uniqueness of limits (`eq_colmezTheta_of_printed`), any map given by
  the printed formula is `colmezTheta`.
* `colmezTheta_teichmuller`: `θ([x]) = x^{(0)}`.
-/

namespace ZInQ.Contrib.ColmezTiltIso

set_option linter.unusedSectionVars false

open Ideal WittVector

section Expansion

variable {p : ℕ} [hp : Fact p.Prime] {A : Type*} [CommRing A] [CharP A p] [PerfectRing A p]

/-- `[x_0] + V(shift x)` has coordinates `x`. -/
theorem teichmuller_add_verschiebung (w : WittVector p A) :
    w = teichmuller p (w.coeff 0) + verschiebung (w.shift 1) := by
  have hdis : ∀ n, (teichmuller p (w.coeff 0)).coeff n = 0 ∨
      (verschiebung (w.shift 1)).coeff n = 0 := by
    intro n
    rcases n with _ | n
    · exact Or.inr (verschiebung_coeff_zero _)
    · exact Or.inl (teichmuller_coeff_pos p _ _ (Nat.succ_pos n))
  ext n
  rw [coeff_add_of_disjoint n _ _ hdis]
  rcases n with _ | n
  · rw [teichmuller_coeff_zero, verschiebung_coeff_zero, add_zero]
  · rw [teichmuller_coeff_pos p _ _ (Nat.succ_pos n), verschiebung_coeff_succ, shift_coeff,
      zero_add, add_comm]

/-- In a perfect ring, `V z = p · F⁻¹ z`. -/
theorem verschiebung_eq_p_mul (z : WittVector p A) :
    verschiebung z = (p : WittVector p A) * WittVector.map
      ((frobeniusEquiv A p).symm : A →+* A) z := by
  set y := WittVector.map ((frobeniusEquiv A p).symm : A →+* A) z
  have hy : WittVector.frobenius y = z := by
    rw [frobenius_eq_map_frobenius]
    ext n
    rw [map_coeff, map_coeff]
    exact frobenius_apply_frobeniusEquiv_symm A p _
  rw [← hy, verschiebung_frobenius, mul_comm]

/-- **The printed Witt expansion** `(x_0,x_1,…) = Σ p^n [x_n^{p^{-n}}]`, modulo `p^N`. -/
theorem witt_expansion (N : ℕ) (w : WittVector p A) :
    ∃ u : WittVector p A, w = (∑ n ∈ Finset.range N, (p : WittVector p A) ^ n *
      teichmuller p (((frobeniusEquiv A p).symm^[n]) (w.coeff n))) +
        (p : WittVector p A) ^ N * u := by
  induction N generalizing w with
  | zero => exact ⟨w, by simp⟩
  | succ N ih =>
    set y := WittVector.map ((frobeniusEquiv A p).symm : A →+* A) (w.shift 1)
    obtain ⟨u, hu⟩ := ih y
    have hy : ∀ n, ((frobeniusEquiv A p).symm^[n]) (y.coeff n) =
        ((frobeniusEquiv A p).symm^[n + 1]) (w.coeff (n + 1)) := by
      intro n
      rw [Function.iterate_succ_apply, map_coeff, shift_coeff, add_comm 1 n]
      rfl
    have hw : w = teichmuller p (w.coeff 0) + (p : WittVector p A) * y :=
      (teichmuller_add_verschiebung w).trans (by rw [verschiebung_eq_p_mul])
    rw [hu] at hw
    refine ⟨u, ?_⟩
    conv_lhs => rw [hw]
    rw [Finset.sum_range_succ']
    simp only [hy, pow_zero, one_mul, Function.iterate_zero, id_eq, mul_add, Finset.mul_sum,
      pow_succ', mul_assoc]
    ring

end Expansion

variable {O : Type*} [CommRing O] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

/-- `θ` along the expansion: `θ(w) ≡ Σ_{n<N} p^n untilt(Frob⁻ⁿ w_n)` modulo `p^N`. -/
theorem fontaineTheta_sub_sum_mem (w : WittVector p (PreTilt O p)) (N : ℕ) :
    fontaineTheta O p w - ∑ n ∈ Finset.range N, (p : O) ^ n *
      PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm^[n]) (w.coeff n)) ∈
        span {(p : O)} ^ N := by
  obtain ⟨u, hu⟩ := witt_expansion N w
  nth_rw 1 [hu]
  rw [map_add, map_sum, map_mul, map_pow, map_natCast]
  simp only [map_mul, map_pow, map_natCast, fontaineTheta_teichmuller, add_sub_cancel_left]
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact dvd_mul_right _ _

/-- `W(R) ≅ W(PreTilt)`, the isomorphism `WittVector.map colmezEquiv`. -/
noncomputable def wittEquiv : WittVector p (ColmezR O p) ≃+* WittVector p (PreTilt O p) where
  toFun := WittVector.map (colmezEquiv (O := O) (p := p)).toRingHom
  invFun := WittVector.map (colmezEquiv (O := O) (p := p)).symm.toRingHom
  left_inv w := by
    refine WittVector.ext fun n => ?_
    rw [map_coeff, map_coeff]
    exact (colmezEquiv (O := O) (p := p)).symm_apply_apply _
  right_inv w := by
    refine WittVector.ext fun n => ?_
    rw [map_coeff, map_coeff]
    exact (colmezEquiv (O := O) (p := p)).apply_symm_apply _
  map_add' := map_add _
  map_mul' := map_mul _

theorem coeff_wittEquiv (w : WittVector p (ColmezR O p)) (n : ℕ) :
    (wittEquiv w).coeff n = colmezEquiv (w.coeff n) :=
  map_coeff _ _ _

theorem wittEquiv_teichmuller (x : ColmezR O p) :
    wittEquiv (teichmuller p x) = teichmuller p (colmezEquiv x) :=
  map_teichmuller p _ x

variable (O p) in
/-- Colmez's `θ : W(R) → O_{C_p}`, through the isomorphism with Mathlib's `fontaineTheta`. -/
noncomputable def colmezTheta : WittVector p (ColmezR O p) →+* O :=
  (fontaineTheta O p).comp wittEquiv.toRingHom

theorem colmezTheta_apply (w : WittVector p (ColmezR O p)) :
    colmezTheta O p w = fontaineTheta O p (wittEquiv w) :=
  rfl

/-- The printed partial sums `Σ_{n<N} p^n x_n^{(n)}`, `x_n` the Witt coordinates of `w`. -/
def printedThetaSum (w : WittVector p (ColmezR O p)) (N : ℕ) : O :=
  ∑ n ∈ Finset.range N, (p : O) ^ n * (w.coeff n).seq n

/-- **`θ` is the printed series** (Colmez, p. 632): `colmezTheta w`, i.e. Mathlib's `fontaineTheta`
applied to `W(colmezEquiv) w`, is the `p`-adic limit of `Σ_{n<N} p^n x_n^{(n)}`; indeed
`θ(w) - Σ_{n<N} p^n x_n^{(n)} ∈ p^N O` for every `N`. -/
theorem colmezTheta_sub_printedThetaSum_mem (w : WittVector p (ColmezR O p)) (N : ℕ) :
    colmezTheta O p w - printedThetaSum w N ∈ span {(p : O)} ^ N := by
  have h := fontaineTheta_sub_sum_mem (wittEquiv w) N
  have e : ∀ n, PreTilt.untilt (((frobeniusEquiv (PreTilt O p) p).symm^[n])
      ((wittEquiv w).coeff n)) = (w.coeff n).seq n := fun n => by
    rw [coeff_wittEquiv, ← colmezEquiv_symm_seq, colmezEquiv.symm_apply_apply]
  simp only [e] at h
  exact h

theorem isPAdicLim_colmezTheta (w : WittVector p (ColmezR O p)) :
    IsPAdicLim p (printedThetaSum w) (colmezTheta O p w) := by
  intro k
  refine Filter.eventually_atTop.mpr ⟨k, fun N hN => ?_⟩
  have h := neg_mem (colmezTheta_sub_printedThetaSum_mem w N)
  rw [neg_sub] at h
  exact Ideal.pow_le_pow_right hN h

/-- **Uniqueness**: any map `W(R) → O` given by the printed formula is `colmezTheta`. -/
theorem eq_colmezTheta_of_printed (θ' : WittVector p (ColmezR O p) → O)
    (h : ∀ w, IsPAdicLim p (printedThetaSum w) (θ' w)) : θ' = colmezTheta O p :=
  funext fun w => (h w).unique (isPAdicLim_colmezTheta w)

/-- **`θ([x]) = x^{(0)}`** on Teichmüller lifts. -/
theorem colmezTheta_teichmuller (x : ColmezR O p) :
    colmezTheta O p (teichmuller p x) = x.seq 0 := by
  rw [colmezTheta_apply, wittEquiv_teichmuller, fontaineTheta_teichmuller, untilt_colmezEquiv]

end ZInQ.Contrib.ColmezTiltIso
