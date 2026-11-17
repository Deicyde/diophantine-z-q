import ZInQKernel.Contrib.CloudB3RC53.Nodes

/-!
# RC53 blueprint: the assembly of Theorem 5.3 from the printed leaves and the nodes

* `rootNumberNode_proof`: `RootNumberNode` from Dokchitser–Dokchitser Theorem 1.8 (tex
  L1793–1797), using the rational two-torsion of `E_ℓ` proved in `PoleRC`.
* `centralValueZeroNode_proof`: `CentralValueZeroNode` (the functional equation at `s = 1`).
* `finalRankDeductionNode_proof`: `FinalRankDeductionNode` (tex L5736–5741): the order of a
  product is the sum of the orders.
* `restrictedConverseGenuine_of_nodes`: **Theorem 5.3** from `Prints`, `BranchPackageNode` and
  `MissingAddressNode`, following tex L5666–5741: choose `M, b` as in (5.10); if `L'(E/K, 1) = 0`
  the base-zero lemma gives `ũ_0(0) = 0`, and the missing address `x ≠ 0` then has
  `v₂ ũ_x(0) ≥ M - 2c > B`, contradicting the upper bound.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower

/-- **Root number `-1`** from Dokchitser–Dokchitser Theorem 1.8 (tex L1793–1797). -/
theorem rootNumberNode_proof (P : Prints) : RootNumberNode := by
  intro ℓ hadm hSel
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hadm.1.ne'
  have hE := PoleRC.curve_isElliptic hℓ0
  have h2 : 1 < Nat.card (nsmulAddMonoidHom 2 :
      (Ecurve ℓ).toAffine.Point →+ (Ecurve ℓ).toAffine.Point).ker := by
    rw [PoleRC.card_ker_two_nsmul_eq_four_M hℓ0]; norm_num
  simpa using P.dd (Ecurve ℓ) hE h2 1 hSel

/-- **The functional equation with sign `-1` at `s = 1`.** -/
theorem centralValueZeroNode_proof : CentralValueZeroNode := by
  intro E N hN F hFE
  have h := hFE 1 (by norm_num) (by norm_num)
  have h1 : (2 : ℂ) - 1 = 1 := by norm_num
  rw [h1] at h
  have h0 : completedL N F 1 = 0 := by linear_combination h / 2
  unfold completedL at h0
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  rw [Complex.Gamma_one, mul_one] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h (by simp [Complex.cpow_eq_zero_iff, hN'])
    · exact absurd h (by simp [Complex.cpow_eq_zero_iff, hpi])
  · exact h

/-- **The final deduction** (tex L5736–5741). -/
theorem finalRankDeductionNode_proof : FinalRankDeductionNode := by
  rintro E k ⟨N, hN, F, ⟨hFd, hFL⟩, hFE⟩ ⟨G, hGd, hGL, hGord⟩ hnot
  have hF1 : F 1 = 0 := centralValueZeroNode_proof E N hN F (by simpa using hFE)
  have hFa : AnalyticAt ℂ F 1 := hFd.analyticAt 1
  have hGa : AnalyticAt ℂ G 1 := hGd.analyticAt 1
  have hmul : analyticOrderAt (F * G) 1 = analyticOrderAt F 1 + analyticOrderAt G 1 :=
    analyticOrderAt_mul hFa hGa
  have hG0 : analyticOrderAt G 1 = 0 := by exact_mod_cast hGord
  rw [hG0, add_zero] at hmul
  have hlt : ¬ 2 ≤ analyticOrderAt F 1 := by
    intro h2
    apply hnot
    refine ⟨F * G, hFd.mul hGd, fun s hs => ?_, hmul ▸ h2⟩
    simp only [Pi.mul_apply, hFL s hs, hGL s hs]
  have hne : analyticOrderAt F 1 ≠ 0 := by
    rw [ne_eq, hFa.analyticOrderAt_eq_zero]
    exact not_not.mpr hF1
  refine ⟨F, hFd, hFL, ?_⟩
  generalize analyticOrderAt F 1 = n at hlt hne ⊢
  induction n using ENat.recTopCoe with
  | top => exact absurd le_top hlt
  | coe n =>
    have : n ≠ 0 := by exact_mod_cast hne
    have : ¬ 2 ≤ n := by exact_mod_cast hlt
    have : n = 1 := by omega
    simp [this]

/-- **Theorem 5.3 (`hyp:RC`) from the printed leaves and the two open nodes**, following the
manuscript's top-level argument (tex L1793–1797, L2587–2602, L5666–5741). -/
theorem restrictedConverseGenuine_of_nodes (P : Prints) (hBr : BranchPackageNode)
    (hMA : MissingAddressNode) : RestrictedConverseGenuine := by
  intro ℓ hℓ hsf hmod hSel
  have hadm : Adm ℓ := ⟨hℓ, hsf, hmod⟩
  rcases hBr ℓ hadm hSel with h | hpkg
  · exact h
  obtain ⟨pkg⟩ := hpkg
  by_contra hnot
  have hRN := rootNumberNode_proof P ℓ hadm hSel
  have hP : ProductOrderGeTwo (Ecurve ℓ) pkg.k := by
    by_contra hP
    exact hnot (finalRankDeductionNode_proof _ _ hRN pkg.hk hP)
  set M := pkg.B + 2 * pkg.cdet + 1 with hM
  have h1 : pkg.cdet < M := by omega
  have h2 : pkg.B + 2 * pkg.cdet < M := by omega
  have h3 : (pkg.LT M + 2) * (2 ^ M - 1) < (pkg.LT M + 2) * (2 ^ M - 1) + 1 := by omega
  obtain ⟨C, c, hc, hCl, hPole, hBase, hUB, hBZ⟩ := pkg.coord M _ h1 h2 h3
  obtain ⟨x, hx0, hx⟩ := hMA _ M (pkg.LT M) pkg.B pkg.cdet c C h1 h2 h3 hc hCl hPole hBase
  rw [hBZ hP, sub_zero] at hx
  have hlow := hUB x hx0
  have hlt : (2 : ℝ) ^ (-((M : ℤ) - 2 * c)) < (2 : ℝ) ^ (-(pkg.B : ℤ)) :=
    zpow_lt_zpow_right₀ one_lt_two (by omega)
  linarith

end ZInQ.Contrib.CloudB3RC53
