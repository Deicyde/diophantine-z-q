import ZInQKernel.Contrib.OneProof.ThetaDirect.Relations

/-! # theta-direct: `ThetaRatiosAtQM` (the use of `thetaRatiosAlgebraic`) proved, with no hypotheses

Task theta-direct (docs/research/theta-direct.md). The added composite field `thetaRatiosAlgebraic`
(`G0Split.ThetaPt.ThetaRatiosAlgebraic`, GLUE) has one reader, TailK's `gluePieces_of_open4`, which needs only
theta-split's use form `ThetaRatiosAtQM` (theta-fold, wip/theta-fold 8e3dbdea; its verbatim copy is in
`ThetaDirect/UseForm.lean`). This file proves, with no hypotheses (only `propext`, `Classical.choice`, `Quot.sound`):

* `thetaRatiosAtQM_proof : ThetaRatiosAtQM`;
* `thetaRatiosAtQM_of_qmHauptmodul : PkgI1.QMHauptmodul → ThetaRatiosAtQM` (theta-fold's consumer binder);
* `thetaPointOfFibre_of_qmPeriod : FibreQMPeriod → ThetaPointOfFibre` (drop-in for
  `thetaPointOfFibre_of_qm_ratios hQM l.thetaRatiosAlgebraic`).

No Lin–Yang input, no `QMHauptmodul`, no leaf (not even Igusa's theta expressions). Used, all proved in the kernel or
in the copied helper modules: the valence formula for `Γ*` (`valenceFormulaCocompactEq_proof`,
`shimizuCovolumeO1_proof`), `ellipticOrderDvd_proof`, `ellipticOrderLe6_proof`, `gammaStarGen_proof`, gt-theta's
squared theta transformation laws at `M4`, `M6` and `thetaModularity_proof`, cm24-value's theta constants at `Ω₂₄`,
period-glue's factorization at `Ω₀`, theta-glue's duplication formula and igusa-alg's Kronecker-checked identities
`IgusaAlg 3..9` (theta-glue's theta expressions `ψ₄ … χ₁₂` are used only as explicit polynomials in the `θ_m`).

Proof. Igusa's theta expressions `ψ₆`, `χ₁₂` transform with weights 6, 12 under `M4`, `M6` (`Modular.lean`: a signed
permutation of their terms). Hence (R1) `ψ₆Σθ⁸ = c₁∏θ²` and (R2) `(Σθ⁸)²χ₁₂ = c₂(Σθ⁸)⁵ + c₃(∏θ²)²` hold along
`Ω(z)` with algebraic `c_i` (`Relations.lean`: weights 20 and 40 for `Γ*`, vanishing at one, resp. two,
inequivalent nodes forced by the valence formula; constants read off at the CM points `√2 + i` and `τ₂₄`, where the
theta ratios are algebraic, `Nodes.lean`). Where `j_θ(Ω(τ)) = q ∈ ℚ ∖ 0`, write `Σθ⁸ = ρ²`, `∏θ² = ρ⁵ξ`
(`ξ² = q/3779136`); then `ψ₄, ψ₆, χ₁₀, χ₁₂ = ρ²·¼, ρ³·c₁ξ, ρ⁵·(−ξ/2¹⁴), ρ⁶(c₂ + c₃ξ²)`, so by weighted homogeneity
`e_k(θ⁸)/(Σθ⁸)^k = P_k(¼, c₁ξ, −ξ/2¹⁴, c₂ + c₃ξ²)` is algebraic (`IgusaAlg k`, `3 ≤ k ≤ 9`; `k = 2` is the global
`Σθ¹⁶ = (Σθ⁸)²/4`), and the `θ_m⁸/Σθ⁸` are roots of a monic polynomial with algebraic coefficients. -/

set_option linter.all false

noncomputable section

namespace HDec.ThetaDirect

open Complex Polynomial
open HDec.HSyn.G0Split.ThetaPt.ThetaGlue (psi4Th psi6Th chi10Th chi12Th psi4T psi6T chi10T chi12T psi6Th_eq
  chi12Th_eq igusaP)
open HDec.HSyn.G0Split.ThetaPt.ThetaSplit (ThetaRatiosAtQM thetaEight card_thetaEight esymm_one esymm_ten
  two_esymm_two zero_mem_evenChars isOddChar_of_not_even thetaPointOfFibre_of_qm_atQM)

/-! ## Node values -/

theorem psi6T_smul (c : ℂ) (s : PkgI1.Char2 → ℂ) : psi6T (fun m => c * s m) = c ^ 6 * psi6T s := by
  simp only [psi6T]; ring

theorem chi12T_smul (c : ℂ) (s : PkgI1.Char2 → ℂ) : chi12T (fun m => c * s m) = c ^ 12 * chi12T s := by
  simp only [chi12T]; ring

/-- At a node, `Σθ⁸`, `∏θ²`, `ψ₆`, `χ₁₂` are algebraic multiples of `t⁸, t²⁰, t¹², t²⁴` for one `t ≠ 0`. -/
theorem node_vals {Ω : Matrix (Fin 2) (Fin 2) ℂ} (h : NodeAlg Ω) :
    ∃ t : ℂ, t ≠ 0 ∧ ∃ s8 p20 p6 p12 : ℂ, s8 ∈ (algebraicClosure ℚ ℂ) ∧ p20 ∈ (algebraicClosure ℚ ℂ) ∧ p6 ∈ (algebraicClosure ℚ ℂ) ∧ p12 ∈ (algebraicClosure ℚ ℂ) ∧
      PkgI1.thetaSum8 Ω = t ^ 8 * s8 ∧ PkgI1.thetaProd2 Ω = t ^ 20 * p20 ∧
      psi6Th Ω = t ^ 12 * p6 ∧ chi12Th Ω = t ^ 24 * p12 := by
  obtain ⟨m0, h0, hr⟩ := h
  set t := PkgI1.thetaConst m0 Ω
  have hθ : ∀ m, PkgI1.thetaConst m Ω = t * (PkgI1.thetaConst m Ω / t) := fun m => by field_simp
  have hsq : (fun m => PkgI1.thetaConst m Ω ^ 2) = fun m => t ^ 2 * (PkgI1.thetaConst m Ω / t) ^ 2 := by
    funext m; conv_lhs => rw [hθ m]
    ring
  refine ⟨t, h0, ∑ m ∈ PkgI1.evenChars, (PkgI1.thetaConst m Ω / t) ^ 8,
    ∏ m ∈ PkgI1.evenChars, (PkgI1.thetaConst m Ω / t) ^ 2,
    psi6T (fun m => (PkgI1.thetaConst m Ω / t) ^ 2), chi12T (fun m => (PkgI1.thetaConst m Ω / t) ^ 2),
    sum_mem fun m _ => pow_mem (hr m) 8, prod_mem fun m _ => pow_mem (hr m) 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [psi6T]; repeat (first | assumption | with_reducible exact hr _ | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)
  · simp only [chi12T]; repeat (first | assumption | with_reducible exact hr _ | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)
  · rw [PkgI1.thetaSum8, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    conv_lhs => rw [hθ m]
    ring
  · rw [PkgI1.thetaProd2, show t ^ 20 = ∏ _m ∈ PkgI1.evenChars, t ^ 2 by
      rw [Finset.prod_const, PkgI1.card_evenChars, ← pow_mul], ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun m _ => ?_
    conv_lhs => rw [hθ m]
    ring
  · rw [psi6Th_eq, hsq, psi6T_smul, ← pow_mul]
  · rw [chi12Th_eq, hsq, chi12T_smul, ← pow_mul]

theorem c1_mem : c1 ∈ (algebraicClosure ℚ ℂ) := by
  obtain ⟨t, ht, s8, p20, p6, p12, hs8, hp20, hp6, hp12, e8, e20, e6, e12⟩ :=
    node_vals nodeAlg_om24
  have hP : p20 ≠ 0 := by
    intro h0; apply prod2_tau24; rw [tau24_omega, e20, h0, mul_zero]
  have hZ := Zf24_ne
  have e : c1 = p6 * s8 / p20 := by
    unfold c1 GS
    rw [G8_eq', G20_eq', tau24_omega, e8, e20, e6]
    generalize ((tau24 : ℂ) - 3) * ((tau24 : ℂ) + 1) = Z at hZ
    field_simp
  rw [e]; repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)

theorem c2_mem : c2 ∈ (algebraicClosure ℚ ℂ) := by
  obtain ⟨t, ht, s8, p20, p6, p12, hs8, hp20, hp6, hp12, e8, e20, e6, e12⟩ := node_vals nodeAlg_cm4
  have hS : s8 ≠ 0 := by
    intro h0; apply sum8_tau4; rw [tau4_omega, e8, h0, mul_zero]
  have hZ := Zf4_ne
  have e : c2 = p12 / s8 ^ 3 := by
    unfold c2 GS
    rw [G8_eq', tau4_omega, e8, e12]
    generalize ((tau4 : ℂ) - 3) * ((tau4 : ℂ) + 1) = Z at hZ
    field_simp
  rw [e]; repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)

theorem c3_mem : c3 ∈ (algebraicClosure ℚ ℂ) := by
  obtain ⟨t, ht, s8, p20, p6, p12, hs8, hp20, hp6, hp12, e8, e20, e6, e12⟩ :=
    node_vals nodeAlg_om24
  have hP : p20 ≠ 0 := by
    intro h0; apply prod2_tau24; rw [tau24_omega, e20, h0, mul_zero]
  have hZ := Zf24_ne
  have h2 := c2_mem
  have e : c3 = (s8 ^ 2 * p12 - c2 * s8 ^ 5) / p20 ^ 2 := by
    rw [c3]
    unfold GS
    rw [G8_eq', G20_eq', tau24_omega, e8, e20, e12]
    generalize ((tau24 : ℂ) - 3) * ((tau24 : ℂ) + 1) = Z at hZ
    field_simp
  rw [e]; repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)


/-! ## Symmetric functions of the `θ⁸` on the rational fibres of `j_θ` -/

/-- **GLUE (proved: `qmThetaSymmetricAlg_of`).** Where `j_θ(Ω(τ)) = q ∈ ℚ ∖ 0`, every elementary symmetric function
of the ten `θ_m(Ω(τ))⁸`, divided by the matching power of `Σθ_m⁸`, is an algebraic number. (theta-split's
`QMThetaSymmetric` with algebraic in place of explicit rational coefficients, and only on the rational fibres.) -/
def QMThetaSymmetricAlg : Prop :=
  ∀ τ : ℂ, 0 < τ.im → ∀ q : ℚ, q ≠ 0 →
    PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = (q : ℂ) →
    ∀ k ≤ 10, (thetaEight (PkgI1.Omega τ)).esymm k / PkgI1.thetaSum8 (PkgI1.Omega τ) ^ k ∈
      algebraicClosure ℚ ℂ

/-- Weighted homogeneity of Igusa's `P_k` (weights `2, 3, 5, 6`). -/
theorem igusaP_hom (k : ℕ) (hk3 : 3 ≤ k) (hk9 : k ≤ 9) (ρ a b c d : ℂ) :
    igusaP k (ρ ^ 2 * a) (ρ ^ 3 * b) (ρ ^ 5 * c) (ρ ^ 6 * d) = ρ ^ (2 * k) * igusaP k a b c d := by
  interval_cases k <;> simp only [igusaP] <;> ring

theorem igusaP_mem (k : ℕ) (hk3 : 3 ≤ k) (hk9 : k ≤ 9) {a b c d : ℂ} (ha : a ∈ (algebraicClosure ℚ ℂ)) (hb : b ∈ (algebraicClosure ℚ ℂ))
    (hc : c ∈ (algebraicClosure ℚ ℂ)) (hd : d ∈ (algebraicClosure ℚ ℂ)) : igusaP k a b c d ∈ (algebraicClosure ℚ ℂ) := by
  interval_cases k <;> simp only [igusaP] <;> repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)

theorem qmThetaSymmetricAlg_proof : QMThetaSymmetricAlg := by
  intro τ hτ q hq hJ k hk
  set Ω := PkgI1.Omega τ with hΩdef
  have hDen : PkgI1.jDen Ω ≠ 0 := by
    intro h0; rw [h0, div_zero] at hJ; exact hq (by exact_mod_cast hJ.symm)
  have hNum : PkgI1.jNum Ω ≠ 0 := by
    intro h0; rw [h0, zero_div] at hJ; exact hq (by exact_mod_cast hJ.symm)
  have hS : PkgI1.thetaSum8 Ω ≠ 0 := by
    intro h0; apply hDen; rw [PkgI1.jDen, h0]; ring
  have hP : PkgI1.thetaProd2 Ω ≠ 0 := by
    intro h0; apply hNum; rw [PkgI1.jNum, h0]; ring
  set S := PkgI1.thetaSum8 Ω with hSdef
  set P := PkgI1.thetaProd2 Ω with hPdef
  have hq' : 3779136 * P ^ 2 = (q : ℂ) * S ^ 5 := by
    rw [div_eq_iff hDen, PkgI1.jNum, PkgI1.jDen] at hJ; exact hJ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℂ, ρ ^ 2 = S := IsAlgClosed.exists_pow_nat_eq S (by norm_num)
  have hρ0 : ρ ≠ 0 := by rintro rfl; apply hS; rw [← hρ]; ring
  set ξ := P / ρ ^ 5 with hξdef
  have hPξ : P = ρ ^ 5 * ξ := by rw [hξdef]; field_simp
  have hξ2 : ξ ^ 2 = (q : ℂ) / 3779136 := by
    rw [hξdef, div_pow, ← pow_mul, eq_div_iff (by norm_num), div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hρ0)]
    rw [show ρ ^ (5 * 2) = (ρ ^ 2) ^ 5 by ring, hρ]
    linear_combination hq'
  have hξ : ξ ∈ (algebraicClosure ℚ ℂ) := mem_of_pow_mem (n := 2) (by norm_num) (by rw [hξ2]; repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem))
  have hΩ : ZInQ.LeafPush2.IsSiegel Ω := HDec.HSyn.G0Split.ThetaPt.isSiegel_Omega hτ
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · interval_cases k
    · simp
    · rw [esymm_one, ← hSdef, pow_one, div_self hS]; exact one_mem _
    · have hsq := HDec.HSyn.G0Split.ThetaPt.ThetaGlue.thetaEightSquare Ω hΩ
      have h := two_esymm_two (thetaEight Ω)
      have hsum : (thetaEight Ω).sum = S := by
        rw [← HDec.HSyn.G0Split.ThetaPt.ThetaSplit.esymm_one', esymm_one]
      have hsq' : ((thetaEight Ω).map (· ^ 2)).sum = ∑ m ∈ PkgI1.evenChars, PkgI1.thetaConst m Ω ^ 16 := by
        rw [thetaEight, Multiset.map_map, Finset.sum_map_val]
        exact Finset.sum_congr rfl (fun m _ => by simp only [Function.comp_apply]; ring)
      rw [hsum, hsq', hsq] at h
      have e : (thetaEight Ω).esymm 2 = 3 / 8 * S ^ 2 := by
        unfold S PkgI1.thetaSum8 at *
        linear_combination h / 2
      rw [e, mul_div_assoc, div_self (pow_ne_zero _ hS), mul_one]; repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)
  · rcases Nat.lt_or_ge k 10 with h10 | h10
    · have hk9 : k ≤ 9 := by omega
      rw [HDec.HSyn.G0Split.ThetaPt.ThetaGlue.igusaThetaSymmetric_of_alg
        HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.igusaAlg_all Ω hΩ k h3 hk9]
      have r1 := rel1 hτ
      have r2 := rel2 hτ
      rw [← hΩdef, ← hSdef, ← hPdef] at r1 r2
      have e4 : psi4Th Ω = ρ ^ 2 * (1 / 4) := by
        unfold psi4Th; rw [← hSdef, ← hρ]; ring
      have e6 : psi6Th Ω = ρ ^ 3 * (c1 * ξ) := by
        have : psi6Th Ω = c1 * P / S := by rw [eq_div_iff hS]; exact r1
        rw [this, hPξ, ← hρ]; field_simp
      have e10 : chi10Th Ω = ρ ^ 5 * (-ξ / 2 ^ 14) := by
        unfold chi10Th; rw [← hPdef, hPξ]; ring
      have e12 : chi12Th Ω = ρ ^ 6 * (c2 + c3 * ξ ^ 2) := by
        have hS2 : S ^ 2 ≠ 0 := pow_ne_zero _ hS
        have : chi12Th Ω = (c2 * S ^ 5 + c3 * P ^ 2) / S ^ 2 := by rw [eq_div_iff hS2]; linear_combination r2
        rw [this, hPξ, ← hρ]; field_simp
      rw [e4, e6, e10, e12, igusaP_hom k h3 hk9, ← hρ, ← pow_mul, mul_comm, mul_div_assoc,
        div_self (pow_ne_zero _ hρ0), mul_one]
      exact igusaP_mem k h3 hk9 (by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)) (mul_mem c1_mem hξ) (by repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem))
        (add_mem c2_mem (mul_mem c3_mem (pow_mem hξ 2)))
    · have hk10 : k = 10 := by omega
      subst hk10
      rw [esymm_ten Ω hS, hJ, mul_div_assoc, div_self (pow_ne_zero _ hS), mul_one]
      repeat (first | assumption | with_reducible exact one_mem _ | with_reducible exact zero_mem _ | with_reducible exact ofNat_mem' _ | with_reducible exact ratCast_mem' _ | with_reducible apply div_mem | with_reducible apply inv_mem | with_reducible apply add_mem | with_reducible apply sub_mem | with_reducible apply mul_mem | with_reducible apply pow_mem | with_reducible apply neg_mem)

/-! ## The use form -/

/-- A root of a monic polynomial whose elementary symmetric functions are algebraic is algebraic (copied verbatim
from origin/wip/theta-split `scratch/theta-split/ThetaUse.lean` l.368-391, theta-split's `mem_of_esymm_mem`). -/
theorem mem_of_esymm_mem (s : Multiset ℂ) (hs : ∀ k ≤ Multiset.card s, s.esymm k ∈ (algebraicClosure ℚ ℂ)) {y : ℂ}
    (hy : y ∈ s) : y ∈ (algebraicClosure ℚ ℂ) := by
  have hmon : (s.map (fun t => X - C t)).prod.Monic :=
    monic_multiset_prod_of_monic _ _ (fun t _ => monic_X_sub_C t)
  have hlift : (s.map (fun t => X - C t)).prod ∈ lifts (algebraMap (algebraicClosure ℚ ℂ) ℂ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ Multiset.card s
    · rw [Multiset.prod_X_sub_C_coeff s hn]
      have : (-1 : ℂ) ^ (Multiset.card s - n) * s.esymm (Multiset.card s - n) ∈ (algebraicClosure ℚ ℂ) :=
        mul_mem (pow_mem (neg_mem (one_mem _)) _) (hs _ (Nat.sub_le _ _))
      exact ⟨⟨_, this⟩, rfl⟩
    · rw [coeff_eq_zero_of_natDegree_lt]
      · exact ⟨0, by simp⟩
      · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_degree_eq_and_monic hlift hmon
  have hA : IsAlgebraic (algebraicClosure ℚ ℂ) y := by
    refine ⟨Q, hQm.ne_zero, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, hQ, eval_multiset_prod]
    apply Multiset.prod_eq_zero
    rw [Multiset.map_map]
    exact Multiset.mem_map.mpr ⟨y, hy, by simp⟩
  exact mem_algebraicClosure_iff.mpr (hA.restrictScalars ℚ)

/-- **`ThetaRatiosAtQM` from `QMThetaSymmetricAlg` (proved)** (theta-split's `thetaRatiosAtQM_of_symmetric`, with
algebraic in place of rational symmetric functions). -/
theorem thetaRatiosAtQM_of_symAlg (h : QMThetaSymmetricAlg) : ThetaRatiosAtQM := by
  intro τ hτ q hq hJ
  have hDen : PkgI1.jDen (PkgI1.Omega τ) ≠ 0 := by
    intro h0; rw [h0, div_zero] at hJ; exact hq (by exact_mod_cast hJ.symm)
  have hNum : PkgI1.jNum (PkgI1.Omega τ) ≠ 0 := by
    intro h0; rw [h0, zero_div] at hJ; exact hq (by exact_mod_cast hJ.symm)
  have hS : PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 := by
    intro h0; apply hDen; rw [PkgI1.jDen, h0]; ring
  have hProd : PkgI1.thetaProd2 (PkgI1.Omega τ) ≠ 0 := by
    intro h0; apply hNum; rw [PkgI1.jNum, h0]; ring
  set S := PkgI1.thetaSum8 (PkgI1.Omega τ) with hSdef
  have hconv : ∀ m, ZInQ.LeafPush2.thetaConst (BPAnalytic.QM.Omega τ) m = PkgI1.thetaConst m (PkgI1.Omega τ) :=
    fun m => by
      rw [HDec.HSyn.G0Split.ThetaPt.thetaConst_eq_pkgI1, HDec.HSyn.G0Split.ThetaPt.omega_eq]
  have h00 : PkgI1.thetaConst (0, 0) (PkgI1.Omega τ) ≠ 0 := thetaConst_ne_of_prod hProd zero_mem_evenChars
  set s' := (thetaEight (PkgI1.Omega τ)).map (fun t => S⁻¹ • t) with hs'
  have hcard : Multiset.card s' = 10 := by rw [hs', Multiset.card_map, card_thetaEight]
  have hesymm : ∀ k ≤ Multiset.card s', s'.esymm k ∈ (algebraicClosure ℚ ℂ) := by
    intro k hk
    rw [hcard] at hk
    rw [hs', ← Multiset.pow_smul_esymm, smul_eq_mul, inv_pow, ← div_eq_inv_mul]
    exact h τ hτ q hq hJ k hk
  have halg8 : ∀ m ∈ PkgI1.evenChars, S⁻¹ * PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8 ∈ (algebraicClosure ℚ ℂ) :=
    fun m hm => mem_of_esymm_mem s' hesymm
      (Multiset.mem_map.mpr ⟨_, Multiset.mem_map.mpr ⟨m, hm, rfl⟩, rfl⟩)
  refine ⟨(0, 0), by rw [hconv]; exact h00, fun m => ?_⟩
  rw [hconv, hconv, ← mem_algebraicClosure_iff]
  by_cases hm : m ∈ PkgI1.evenChars
  · refine mem_of_pow_mem (n := 8) (by norm_num) ?_
    have : (PkgI1.thetaConst m (PkgI1.Omega τ) / PkgI1.thetaConst (0, 0) (PkgI1.Omega τ)) ^ 8 =
        (S⁻¹ * PkgI1.thetaConst m (PkgI1.Omega τ) ^ 8) *
          (S⁻¹ * PkgI1.thetaConst (0, 0) (PkgI1.Omega τ) ^ 8)⁻¹ := by
      field_simp
    rw [this]
    exact mul_mem (halg8 m hm) (inv_mem (halg8 _ zero_mem_evenChars))
  · rw [thetaConst_odd' _ hm, zero_div]
    exact zero_mem _

/-! ## Main theorems -/

/-- **Main theorem (proved, no hypotheses).** The use form `ThetaRatiosAtQM` of the field `thetaRatiosAlgebraic`:
for `τ ∈ ℍ` with `j_θ(Ω(τ)) = jNum(Ω(τ))/jDen(Ω(τ)) = q ∈ ℚ ∖ 0`, some `θ_{m₀}(Ω(τ)) ≠ 0` and every
`θ_m(Ω(τ))/θ_{m₀}(Ω(τ))` is an algebraic number. -/
theorem thetaRatiosAtQM_proof : ThetaRatiosAtQM :=
  thetaRatiosAtQM_of_symAlg qmThetaSymmetricAlg_proof

/-- **The consumer form** (theta-fold's rethread of `gluePieces_of_open4` takes
`hθ : PkgI1.QMHauptmodul → ThetaRatiosAtQM`). -/
theorem thetaRatiosAtQM_of_qmHauptmodul : PkgI1.QMHauptmodul → ThetaRatiosAtQM := fun _ => thetaRatiosAtQM_proof

/-- **Missing piece 9, `ThetaPointOfFibre`, from `FibreQMPeriod` alone (proved)**: a drop-in replacement for
`ThetaPt.thetaPointOfFibre_of_qm_ratios hQM l.thetaRatiosAlgebraic` in TailK's `gluePieces_of_open4`. -/
theorem thetaPointOfFibre_of_qmPeriod (hQM : HDec.HSyn.G0Split.ThetaPt.FibreQMPeriod) :
    HDec.HSyn.G0Split.ThetaPointOfFibre :=
  thetaPointOfFibre_of_qm_atQM hQM thetaRatiosAtQM_proof

end HDec.ThetaDirect
