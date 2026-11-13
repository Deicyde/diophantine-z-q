import ZInQKernel.Contrib.GZTheta.ALBasic

/-!
# atkin-li: a good eigenform of trivial nebentypus is a combination of `g'(eτ)`

Task atkin-li. Let `F ∈ S₂(Γ₁(N), 1)` be an eigenvector of every `T_p`, `p ∤ N`, with eigenvalues
`a_p`, and `g'` a newform of level `M' ∣ N`, trivial nebentypus, with the same eigenvalues. Given
strong multiplicity one across levels (`NewformUniqueAcrossLevels`), there are constants `c_e`
with

  `a_n(F) = ∑_{e ∣ N/M'} c_e a_{n/e}(g')`     (`exists_coeff_rep`; `[e ∣ n]` understood)

and `F(τ) = ∑_{e ∣ N/M'} c_e g'(eτ)` (`exists_fun_rep`). From Tau Ceti's spanning theorem
(`Newform.mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul`), the independence of the
nebentypus spaces, and `NewformUniqueAcrossLevels` for the generators of trivial nebentypus.
-/

open Complex Filter ModularForm CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups

noncomputable section

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE ZInQ.GZDecomp

/-- The coefficients of `g'(eτ)`. -/
def Bc {M' : ℕ} [NeZero M'] (g' : Newform M' 2) (e n : ℕ) : ℂ :=
  if e ∣ n then coeff g' (n / e) else 0

/-- The span of the level raises `V_e g'` at level `N`. -/
def raiseSpan (N : ℕ) [NeZero N] {M' : ℕ} [NeZero M'] (g' : Newform M' 2) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) :=
  Submodule.span ℂ {G | ∃ (e : ℕ) (_ : NeZero e) (h : e * M' ∣ N),
    TauCeti.CuspForm.levelRaise e (TauCeti.Gamma1_map_le_conjAct_scaleGL_of_dvd h) g'.toCuspForm = G}

theorem raiseSpan_le_charSpace (N : ℕ) [NeZero N] {M' : ℕ} [NeZero M'] (g' : Newform M' 2)
    (hg' : g'.χ = 1) : raiseSpan N g' ≤ cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨e, _, h, rfl⟩
  have := TauCeti.CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd h g'.χ g'.mem_charSpace
  rwa [hg', MonoidHom.one_comp] at this

theorem coeff_rep_of_mem_raiseSpan (N : ℕ) [NeZero N] {M' : ℕ} [NeZero M'] (g' : Newform M' 2)
    {G : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2} (hG : G ∈ raiseSpan N g') :
    ∃ c : ℕ → ℂ, ∀ n, (qExpansion 1 G).coeff n =
      ∑ e ∈ (N / M').divisors, c e * Bc g' e n := by
  set ℓ := fun n => CuspForm.qExpansionCoeffₗ one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) 2 n
  have hℓ : ∀ n (H : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2), ℓ n H = (qExpansion 1 H).coeff n :=
    fun n H => CuspForm.qExpansionCoeffₗ_apply _ _ _ _
  simp only [← hℓ]
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, _, h, rfl⟩ := hx
    have hM'0 : N / M' ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N))
        (dvd_of_mul_left_dvd h)) (Nat.pos_of_ne_zero (NeZero.ne M'))
      omega
    have he : e ∈ (N / M').divisors := by
      refine Nat.mem_divisors.mpr ⟨?_, hM'0⟩
      obtain ⟨t, ht⟩ := h
      exact ⟨t, by
        rw [ht, mul_assoc, mul_comm M', ← mul_assoc,
          Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne M'))]⟩
    refine ⟨fun x => if x = e then 1 else 0, fun n => ?_⟩
    rw [hℓ, TauCeti.CuspForm.qExpansion_levelRaise_coeff (TauCeti.one_mem_strictPeriods_Gamma1_map _)
      (TauCeti.one_mem_strictPeriods_Gamma1_map _), Finset.sum_eq_single e]
    · simp [Bc, coeff]
    · intro b _ hb; simp [hb]
    · intro h'; exact absurd he h'
  | zero => exact ⟨0, fun n => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨c', hc'⟩ := hy
    refine ⟨c + c', fun n => ?_⟩
    rw [map_add, hc, hc', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Pi.add_apply]; ring
  | smul a x _ hx =>
    obtain ⟨c, hc⟩ := hx
    refine ⟨a • c, fun n => ?_⟩
    rw [map_smul, hc, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- **The representation on coefficients.** -/
theorem exists_coeff_rep (hU : NewformUniqueAcrossLevels) {N : ℕ} [NeZero N]
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2}
    (hF1 : F ∈ cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ))
    {a : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ℂ}
    (hF : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      heckeTCuspNat 2 p (_hn := ⟨hp.ne_zero⟩) F = a p hp hpN • F)
    {M' : ℕ} [NeZero M'] (hM' : M' ∣ N) (g' : Newform M' 2) (hg'χ : g'.χ = 1)
    (hg'ev : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      g'.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hM') = a p hp hpN) :
    ∃ c : ℕ → ℂ, ∀ n, (qExpansion 1 F).coeff n = ∑ e ∈ (N / M').divisors, c e * Bc g' e n := by
  refine coeff_rep_of_mem_raiseSpan N g' ?_
  set X := ⨆ (ψ : (ZMod N)ˣ →* ℂˣ) (_ : ψ ≠ 1), cuspFormCharSpace 2 ψ with hX
  have hmem : F ∈ raiseSpan N g' ⊔ X := by
    refine Submodule.span_le.mpr ?_ (Newform.mem_span_levelRaise_of_forall_heckeTCuspNat_eq_smul hF)
    rintro _ ⟨Mi, d, _, _, hdM, gi, hgi, rfl⟩
    have hMN : Mi ∣ N := dvd_of_mul_left_dvd hdM
    by_cases hgχ : gi.χ.comp (ZMod.unitsMap hMN) = 1
    · refine Submodule.mem_sup_left ?_
      have hg'1 : g'.χ.comp (ZMod.unitsMap hM') = 1 := by rw [hg'χ, MonoidHom.one_comp]
      obtain ⟨hMeq, hfun⟩ := hU N 2 Mi M' 1 gi g' hMN hM' hgχ hg'1 (fun p hp hpN => by
        rw [hgi p hp hpN, hg'ev p hp hpN])
      subst hMeq
      have hgg : gi.toCuspForm = g'.toCuspForm := DFunLike.coe_injective hfun
      rw [hgg]
      exact Submodule.subset_span ⟨d, inferInstance, hdM, rfl⟩
    · refine Submodule.mem_sup_right ?_
      exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hgχ
        (TauCeti.CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hdM gi.χ gi.mem_charSpace))
  obtain ⟨w, hw, x, hx, hwx⟩ := Submodule.mem_sup.mp hmem
  have hw1 : w ∈ cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ) := raiseSpan_le_charSpace N g' hg'χ hw
  have hx1 : x ∈ cuspFormCharSpace 2 (1 : (ZMod N)ˣ →* ℂˣ) := by
    have : x = F - w := by rw [← hwx]; abel
    rw [this]; exact Submodule.sub_mem _ hF1 hw1
  have hx0 : x = 0 :=
    (Submodule.disjoint_def.mp (iSupIndep_def.mp (iSupIndep_cuspFormCharSpace 2) 1)) x hx1 hx
  rw [← hwx, hx0, add_zero]
  exact hw

/-- **The representation as functions**: `F(τ) = ∑_{e ∣ P} c_e g'(eτ)` from the coefficients. -/
theorem fun_rep_of_coeff_rep {N : ℕ} [NeZero N] (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)
    {M' : ℕ} [NeZero M'] (g' : Newform M' 2) (P : ℕ) (c : ℕ → ℂ)
    (hc : ∀ n, (qExpansion 1 F).coeff n = ∑ e ∈ P.divisors, c e * Bc g' e n) (τ : ℍ) :
    F τ = ∑ e ∈ P.divisors, c e * gAt g'.toCuspForm e τ := by
  have hF := ModularForm.hasSum_qExpansion F one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map _) τ
  simp only [hc] at hF
  have hR : HasSum (fun m : ℕ => ∑ e ∈ P.divisors,
      c e * ((if e ∣ m then coeff g' (m / e) else 0) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m))
      (∑ e ∈ P.divisors, c e * gAt g'.toCuspForm e τ) :=
    hasSum_sum fun e he => by
      rw [gAt, dif_pos (Nat.pos_of_mem_divisors he)]
      exact (hasSum_scaled g'.toCuspForm (Nat.pos_of_mem_divisors he) τ).mul_left _
  refine hF.unique (hR.congr_fun fun m => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Bc]
  ring

end ZInQ.GZTheta
