import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalPoly
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Hecke
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Degeneracy

/-!
# GenusOdd: `GoodReductionOffLevel` from lane RC8's `ModularNewform` (PROVED reduction)

`newformLevel E` is the least `M > 0` such that some `g ∈ S₂(Γ₀(M))` has the Dirichlet
coefficients of `L(E, s)` as `q`-expansion. Let `f` be the newform of `E`, of level `N`
(`ModularNewform`, BCDT). Then `g = f` as functions (same `q`-expansion), so `f` is invariant under
`Γ₀(M)` and `Γ₁(N)`, hence under `Γ(M) ⊔ Γ(N) = Γ(gcd(M, N))` (Tau Ceti's `Gamma_gcd_eq_sup`) and
`T`, hence under `Γ₁(d)`, `d = gcd(M, N)`. If `d ≠ N`, `f = V₁(f)` would be old at level `N`
(`levelRaise_mem_cuspFormsOld`), while it is new and normalised (`disjoint_cuspFormsOld_cuspFormsNew`):
so `N ∣ M` (`dvd_of_hasCuspFormAtLevel`). A prime `p ∤ newformLevel E` therefore does not divide
`N`, and `E` has good reduction at `p` (lane RC18's `hasGoodReduction_of_isNewformOf`).
-/

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup ModularGroup
open scoped MatrixGroups ModularForm

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PrintsAnalytic HeckeRing.GL2

/-- The stabilizer in `SL(2, ℤ)` of a function under the weight-`k` slash action. -/
def slashStab (F : ℍ → ℂ) (k : ℤ) : Subgroup SL(2, ℤ) where
  carrier := {γ | F ∣[k] (mapGL ℝ γ) = F}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, SlashAction.slash_mul] at *
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    calc F ∣[k] (mapGL ℝ a⁻¹) = (F ∣[k] (mapGL ℝ a)) ∣[k] (mapGL ℝ a⁻¹) := by rw [ha]
      _ = F := by rw [← SlashAction.slash_mul, ← map_mul, mul_inv_cancel, map_one,
          SlashAction.slash_one]

/-- A subgroup on whose image a slash-invariant form is invariant lies in the stabilizer
(PROVED). -/
theorem le_slashStab {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F) : Γ ≤ slashStab f k :=
  fun γ hγ => SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩

theorem Gamma_le_Gamma1' (N : ℕ) : Gamma N ≤ Gamma1 N := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  rw [Gamma1_mem]
  exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩

theorem T_zpow_mem_Gamma1 (N : ℕ) (n : ℤ) : T ^ n ∈ Gamma1 N := by
  rw [Gamma1_mem]
  simp [coe_T_zpow]

/-- `Γ₁(d) ⊆ Γ(d) · ⟨T⟩` (PROVED): `γ T^{-b} ∈ Γ(d)` for `γ ∈ Γ₁(d)`, `b` its upper-right entry. -/
theorem mul_T_zpow_mem_Gamma {d : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 d) :
    γ * T ^ (-(γ 0 1)) ∈ Gamma d := by
  rw [Gamma1_mem] at hγ
  obtain ⟨h00, h11, h10⟩ := hγ
  rw [Gamma_mem]
  simp only [coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h00]; ring
  · rw [h00]; ring
  · rw [h10]; ring
  · rw [h10, h11]; ring

/-- **Invariance under `Γ₁(gcd(M, N))`** (PROVED): a function invariant under `Γ₀(M)` (in fact
`Γ(M)` suffices) and `Γ₁(N)` is invariant under `Γ₁(gcd(M, N))`. -/
theorem Gamma1_gcd_le_slashStab {F : ℍ → ℂ} {k : ℤ} {M N : ℕ} (hM : Gamma M ≤ slashStab F k)
    (hN : Gamma1 N ≤ slashStab F k) : Gamma1 (Nat.gcd M N) ≤ slashStab F k := by
  intro γ hγ
  have h1 : γ * T ^ (-(γ 0 1)) ∈ slashStab F k := by
    have := mul_T_zpow_mem_Gamma hγ
    rw [Gamma_gcd_eq_sup] at this
    exact (sup_le hM ((Gamma_le_Gamma1' N).trans hN)) this
  have h2 : T ^ (γ 0 1) ∈ slashStab F k := hN (T_zpow_mem_Gamma1 N _)
  have := (slashStab F k).mul_mem h1 h2
  rwa [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one] at this

/-- **The newform as a cusp form of level `Γ₁(d)`** for `d ∣ N`, given invariance under `Γ₁(d)`. -/
def cuspFormOfStab {N : ℕ} [NeZero N] (f : Newform N 2) (d : ℕ) [NeZero d]
    (h : Gamma1 d ≤ slashStab (⇑f.toCuspForm) 2) :
    CuspForm ((Gamma1 d).map (mapGL ℝ)) 2 where
  toFun := ⇑f.toCuspForm
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact h hγ
  holo' := CuspFormClass.holo f.toCuspForm
  zero_at_cusps' := by
    intro c hc
    have hc' : IsCusp c ((Gamma1 N).map (mapGL ℝ)) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact hc
    exact CuspFormClass.zero_at_cusps f.toCuspForm hc'

/-- **A newform is not invariant under `Γ₁(d)` for a proper divisor `d` of its level** (PROVED):
otherwise it would be old (`V₁` of a form of level `d`) as well as new, hence `0`, while
`a₁ = 1`. -/
theorem eq_of_le_slashStab {N : ℕ} [NeZero N] (f : Newform N 2) {d : ℕ} [NeZero d] (hdN : d ∣ N)
    (h : Gamma1 d ≤ slashStab (⇑f.toCuspForm) 2) : d = N := by
  by_contra hne
  have h1 : 1 * d ∣ N := by rwa [one_mul]
  have hold := TauCeti.levelRaise_mem_cuspFormsOld h1 hne 2 (cuspFormOfStab f d h)
  have heq : TauCeti.CuspForm.levelRaise 1 (TauCeti.Gamma1_map_le_conjAct_scaleGL_of_dvd h1)
      (cuspFormOfStab f d h) = f.toCuspForm := by
    ext τ
    rw [TauCeti.CuspForm.levelRaise_apply, TauCeti.scaleGL_one, one_smul]
    rfl
  rw [heq] at hold
  have h0 : f.toCuspForm = 0 :=
    (Submodule.disjoint_def.mp (TauCeti.disjoint_cuspFormsOld_cuspFormsNew N 2)) _ hold f.isNew
  have h1' := f.isNorm
  rw [h0] at h1'
  have hz : ((0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) : ℍ → ℂ) = 0 := rfl
  rw [hz, UpperHalfPlane.qExpansion_zero, map_zero] at h1'
  exact zero_ne_one h1'

/-- **`g = f`** (PROVED): a cusp form on `Γ₀(M)` with the coefficients of `L(E, s)` is the newform of
`E` as a function on `ℍ`. -/
theorem coe_eq_of_coeff {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] {f : Newform N 2}
    (hf : IsNewformOf E f) {M : ℕ} [NeZero M]
    (g : CuspForm (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2)
    (hg : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 g).coeff n = (E.LFunction n : ℂ)) :
    (⇑g : ℍ → ℂ) = ⇑f.toCuspForm := by
  have hcoeff : ∀ n, (UpperHalfPlane.qExpansion 1 g).coeff n =
      (UpperHalfPlane.qExpansion 1 f.toCuspForm).coeff n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [CuspFormClass.qExpansion_coeff_zero (h := 1) g one_pos (by simp),
        CuspFormClass.qExpansion_coeff_zero (h := 1) f.toCuspForm one_pos
          (TauCeti.one_mem_strictPeriods_Gamma1_map N)]
    · rw [hg n hn, ← nfCoeff, hf.2 n hn]
      rfl
  funext τ
  have hgs := ModularForm.hasSum_qExpansion (h := 1) (f := g) one_pos (by simp) τ
  have hfs := ModularForm.hasSum_qExpansion (h := 1) (f := f.toCuspForm) one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map N) τ
  simp_rw [hcoeff] at hgs
  exact hgs.unique hfs

/-- **The level of the newform divides every level of a cusp form with the coefficients of
`L(E, s)`** (PROVED). -/
theorem dvd_of_hasCuspFormAtLevel {E : WeierstrassCurve ℚ} {N : ℕ} [NeZero N] {f : Newform N 2}
    (hf : IsNewformOf E f) {M : ℕ} (hM : 0 < M) (hE : HasCuspFormAtLevel E M) : N ∣ M := by
  have : NeZero M := ⟨hM.ne'⟩
  obtain ⟨g, hg⟩ := hE
  have hfg := coe_eq_of_coeff hf g hg
  have hstabM : Gamma M ≤ slashStab (⇑f.toCuspForm) 2 := by
    rw [← hfg]
    exact (Gamma_le_Gamma1' M |>.trans (Gamma1_in_Gamma0 M)).trans (le_slashStab g)
  have hstabN : Gamma1 N ≤ slashStab (⇑f.toCuspForm) 2 := le_slashStab f.toCuspForm
  have hd := Gamma1_gcd_le_slashStab hstabM hstabN
  have : NeZero (Nat.gcd M N) := ⟨(Nat.gcd_pos_of_pos_left N hM).ne'⟩
  have heq := eq_of_le_slashStab f (Nat.gcd_dvd_right M N) hd
  rw [← heq]
  exact Nat.gcd_dvd_left M N

/-- **`GoodReductionOffLevel` from `ModularNewform`** (PROVED): lane RC8's printed leaf
`ModularNewform` (BCDT Theorem A, newform form) implies that `E` has good reduction at every prime
not dividing `newformLevel E`. -/
theorem goodReductionOffLevel_of_modularNewform (hMN : ModularNewform) : GoodReductionOffLevel := by
  intro E hE v hv
  obtain ⟨N, _, f, hf⟩ := hMN E hE
  by_cases hne : {M : ℕ | 0 < M ∧ HasCuspFormAtLevel E M}.Nonempty
  · have hmem := Nat.sInf_mem hne
    have hdvd : N ∣ newformLevel E := dvd_of_hasCuspFormAtLevel hf hmem.1 hmem.2
    exact ZInQ.Manuscript.RC.TwistDictionary.hasGoodReduction_of_isNewformOf hf v
      (fun h => hv (h.trans hdvd))
  · exfalso
    apply hv
    have : newformLevel E = 0 := by
      rw [newformLevel, Set.not_nonempty_iff_eq_empty.mp hne, Nat.sInf_empty]
    rw [this]
    exact dvd_zero _

end ZInQ.Contrib.CloudB3RC53.GenusOdd
