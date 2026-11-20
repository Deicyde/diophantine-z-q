import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Assembly

/-! Positive rational affine substitutions preserve vanishing at every
cusp. Apply this to the actual moving operators, starting with the masked
App E cusp form (tex 9497–9546). -/

noncomputable section
set_option maxHeartbeats 800000

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion EvenMoving Wiring
open CongruenceSubgroup Matrix Matrix.SpecialLinearGroup UpperHalfPlane Filter
open AppE HalfIntegral ModularForm PrintsAnalytic
open ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.Even ZInQ.Manuscript.RC.Odd
open scoped MatrixGroups BigOperators Topology

private def affine (a b : ℚ) (ha : 0 < a) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, 1]
    (by simpa [Matrix.det_fin_two] using ha.ne')

private theorem affine_det (a b : ℚ) (ha : 0 < a) :
    (affine a b ha).det.val = a := by
  change Matrix.det !![a, b; 0, 1] = a
  simp [Matrix.det_fin_two]

/-- The rational affine substitution only changes the normal at a cusp by
a constant and a reparametrization tending to infinity. -/
theorem affinePoint_zeroAtCusps (k : ℝ) {f : ℍ → ℂ}
    (hf : ∀ γ : SL(2, ℤ), IsZeroAtImInfty (cuspNorm k f γ))
    (a b : ℚ) (ha : 0 < a) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (cuspNorm k (fun z => f (affinePoint a b ha z)) γ) := by
  let F := affine a b ha
  let A : GL (Fin 2) ℚ := F * mapGL ℚ γ
  obtain ⟨β, hβ⟩ := (A • (OnePoint.infty : OnePoint ℚ)).exists_mem_SL2 ℤ
  let G := (mapGL ℚ β)⁻¹ * A
  have hG : G 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp (by
    change ((mapGL ℚ β)⁻¹ * A) • (OnePoint.infty : OnePoint ℚ) = _
    rw [mul_smul, ← hβ, inv_smul_smul])
  let g := G.map (algebraMap ℚ ℝ)
  have hg : g 1 0 = 0 := by simp [g, GeneralLinearGroup.map, hG]
  have hGdet : G.det.val = a := by
    simpa [G, A, F] using affine_det a b ha
  have hgpos : 0 < g.det.val := by
    change 0 < (G.map (algebraMap ℚ ℝ)).det.val
    rw [GeneralLinearGroup.map_det, Units.coe_map, hGdet]
    change 0 < (a : ℝ)
    exact_mod_cast ha
  let v := F.map (algebraMap ℚ ℝ)
  have hprod : mapGL ℝ β * g = v * mapGL ℝ γ := by simp [g, G, A, v]
  have hz (z : ℍ) : affinePoint a b ha (γ • z) = β • (g • z) := by
    have hF (w : ℍ) : affinePoint a b ha w = v • w := by
      apply UpperHalfPlane.ext
      rw [affinePoint_coe, coe_smul_of_det_pos]
      · change _ = ((↑(algebraMap ℚ ℝ a) : ℂ) * (w : ℂ) +
          ↑(algebraMap ℚ ℝ b)) / ((↑(algebraMap ℚ ℝ (0 : ℚ)) : ℂ) * (w : ℂ) +
            ↑(algebraMap ℚ ℝ (1 : ℚ)))
        simp
      · rw [GeneralLinearGroup.map_det, Units.coe_map, affine_det]
        change 0 < (a : ℝ)
        exact_mod_cast ha
    rw [hF]
    change v • (mapGL ℝ γ • z) = mapGL ℝ β • (g • z)
    rw [← mul_smul, ← mul_smul, hprod]
  have hv (z : ℍ) : denom v z = 1 := by
    change (↑(algebraMap ℚ ℝ (0 : ℚ)) : ℂ) * (z : ℂ) + ↑(algebraMap ℚ ℝ (1 : ℚ)) = _
    simp
  have hd (z : ℍ) : denom γ z = denom β (g • z : ℍ) * (g 1 1 : ℝ) := by
    have h₁ := denom_cocycle_σ v (mapGL ℝ γ) z
    have h₂ := denom_cocycle_σ (mapGL ℝ β) g z
    rw [← hprod, hv, map_one, one_mul, h₂] at h₁
    have hgpos' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := hgpos
    simpa [UpperHalfPlane.σ, hgpos', denom, hg] using h₁.symm
  have he (z : ℍ) :
      cuspNorm k (fun w => f (affinePoint a b ha w)) γ z =
        cuspNorm k f β (g • z) * ‖(g 1 1 : ℝ)‖ ^ (-k) := by
    simp only [cuspNorm, hz, hd, norm_mul, Complex.norm_real,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _), mul_assoc]
  rw [show cuspNorm k (fun w => f (affinePoint a b ha w)) γ = _ from funext he]
  change Tendsto _ atImInfty (nhds 0)
  simpa only [zero_mul, Function.comp_apply] using
    (show Tendsto (cuspNorm k f β) atImInfty (nhds 0) from hf β).comp
      (tendsto_smul_atImInfty hg) |>.mul_const (‖(g 1 1 : ℝ)‖ ^ (-k))

private theorem up_zeroAtCusps {n : ℕ} [NeZero n] (k : ℝ) {g : ℍ → ℂ}
    (hg : ∀ γ : SL(2, ℤ), IsZeroAtImInfty (cuspNorm k g γ)) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (cuspNorm k (Up n g) γ) := by
  classical
  let F (r : ZMod n) : ℍ → ℝ := cuspNorm k (fun z => g (unscalePoint n r z)) γ
  have hF (r : ZMod n) : F r ∈ zeroAtImInftySubmodule ℝ :=
    affinePoint_zeroAtCusps k hg _ _ _ γ
  have hsum : (∑ r : ZMod n, F r) ∈ zeroAtImInftySubmodule ℝ :=
    (zeroAtImInftySubmodule ℝ).sum_mem (fun r _ => hF r)
  have ht : IsZeroAtImInfty ((‖(n : ℂ)⁻¹‖ : ℝ) • ∑ r : ZMod n, F r) :=
    (zeroAtImInftySubmodule ℝ).smul_mem _ hsum
  apply isZeroAtImInfty_iff.mpr
  intro ε hε
  obtain ⟨A, hA⟩ := isZeroAtImInfty_iff.mp ht ε hε
  refine ⟨A, fun z hz => le_trans ?_ (hA z hz)⟩
  have he : ∀ r, 0 ≤ F r z := fun r => by unfold F cuspNorm; positivity
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun r _ => he r))]
  rw [cuspNorm, Up_eq_affine, norm_mul, abs_of_nonneg (by positivity)]
  simp only [F, cuspNorm, ← Finset.sum_mul]
  rw [mul_assoc]
  gcongr
  exact norm_sum_le _ _

private theorem sub_smul_zeroAtCusps (k : ℝ) {f g : ℍ → ℂ} (s : ℂ) (γ : SL(2, ℤ))
    (hf : IsZeroAtImInfty (cuspNorm k f γ)) (hg : IsZeroAtImInfty (cuspNorm k g γ)) :
    IsZeroAtImInfty (cuspNorm k (f - s • g) γ) := by
  let Z := zeroAtImInftySubmodule ℝ
  have ht : IsZeroAtImInfty (cuspNorm k f γ + ‖s‖ • cuspNorm k g γ) :=
    Z.add_mem hf (Z.smul_mem _ hg)
  apply isZeroAtImInfty_iff.mpr
  intro ε hε
  obtain ⟨A, hA⟩ := isZeroAtImInfty_iff.mp ht ε hε
  refine ⟨A, fun z hz => le_trans ?_ (hA z hz)⟩
  have he : 0 ≤ cuspNorm k f γ z + ‖s‖ * cuspNorm k g γ z := by
    unfold cuspNorm
    positivity
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Real.norm_of_nonneg he, Real.norm_of_nonneg (by unfold cuspNorm; positivity)]
  simp only [cuspNorm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← add_mul]
  have hn := norm_sub_le (f (γ • z)) (s * g (γ • z))
  rw [norm_mul] at hn
  exact mul_le_mul_of_nonneg_right hn (by positivity)

/-- The exact function used by the Fourier calculation of the moving
operator is cuspidal whenever its input is. -/
theorem movingOp_zeroAtCusps {p : ℕ} [NeZero p] (k : ℝ) {g : ℍ → ℂ} (s : ℂ)
    (hg : ∀ γ : SL(2, ℤ), IsZeroAtImInfty (cuspNorm k g γ)) (γ : SL(2, ℤ)) :
    IsZeroAtImInfty (cuspNorm k (movingOp p s g) γ) := by
  let _ : NeZero (p ^ 2) := ⟨pow_ne_zero _ (NeZero.ne p)⟩
  have hv (γ : SL(2, ℤ)) : IsZeroAtImInfty (cuspNorm k (Vp p (NeZero.pos p) g) γ) := by
    rw [Vp_eq_scale]
    exact affinePoint_zeroAtCusps k hg _ _ _ γ
  exact sub_smul_zeroAtCusps k s γ (up_zeroAtCusps k hv γ) (hv γ)

variable {ℓ : ℕ} {W : WData ℓ} {L : CentralNormalization (Ecurve ℓ)}
variable {τ : SqClass (conductor W.S)}

/-- The actual coefficients of the moving block admit a cuspidal
half-integral witness. No transformation at a new level is used here;
that is supplied independently by the proved moving law. -/
theorem exists_cuspidal_moving_series (P : EvenSource W L τ) (hS : SupportSpec W)
    (U : Finset ℕ) (hU : ∀ p ∈ U, (evenTypes W.S hS.1).Good p) :
    ∃ g, Series (TL (fun p => P.phaseData.η p) U.toList P.sievedCoeff) g ∧
      ∀ γ : SL(2, ℤ), IsZeroAtImInfty (cuspNorm (3 / 2) g γ) := by
  have aux (J : List ℕ) (hJ : ∀ p ∈ J, p.Prime) :
      ∃ g, Series (TL (fun p => P.phaseData.η p) J P.sievedCoeff) g ∧
        ∀ γ : SL(2, ℤ), IsZeroAtImInfty (cuspNorm (3 / 2) g γ) := by
    induction J with
    | nil =>
      obtain ⟨_, _, g, hg, hq⟩ := evenMasked P hS
      have hseries := hasSum_qExpansion one_pos (hiwForm_periodic_comp hg) (hiwForm_mdiff hg)
        (hiwForm_isZeroAtImInfty hg).boundedAtFilter
      refine ⟨g, ?_, fun γ => ?_⟩
      · intro z
        simpa only [TL_nil, ← hq, hiwCoeff, smul_eq_mul] using hseries z
      · change Tendsto (cuspNorm (3 / 2) g γ) atImInfty (nhds 0)
        convert hg.2.2 γ using 1
        funext z
        norm_num [cuspNorm, ModularGroup.denom_apply]
    | cons p J ih =>
      let _ : NeZero p := ⟨(hJ p (by simp)).ne_zero⟩
      obtain ⟨g, hq, hg⟩ := ih (fun q hq => hJ q (List.mem_cons_of_mem _ hq))
      rw [TL_cons]
      exact ⟨movingOp p (P.phaseData.η p) g, movingOp_series p _ hq,
        movingOp_zeroAtCusps _ _ hg⟩
  exact aux U.toList (fun p hp => (hU p (Finset.mem_toList.mp hp)).1)

end ZInQ.Manuscript.RC.EvenJoin
