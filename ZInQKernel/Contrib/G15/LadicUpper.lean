import ZInQKernel.Contrib.G15.LadicD1

/-!
# G15: D1 kills the upper ramification of `G_{ℚ_p}` above `4a²` on `j L`

For a Galois number field `L`, `j : L →+* ℚ̄_p`, `F = Lj j = ℚ_p(j L)` and `P = primeOf j`:
if `1 ≤ a` and `g_0(F) = e(P|p) ≤ a!`, then every `σ` in the upper ramification group
`G^v(F/ℚ_p)` (`LadicCond.upperSet F v`) with `v > 4a²` fixes `j L` pointwise
(`tauOf_eq_one_of_mem_upperSet`), hence so does every `σ ∈ LadicCond.upperAbs p v`
(`apply_j_eq_of_mem_upperAbs`). This is clause (i) of G15 at the level of one number field.

The argument: `ψ(v)` is the real `u ≥ -1` with `φ_F(u) = v` (`TDifferent.exists_phiF_eq`,
`TDifferent.sInf_phiF`, using the lower-index function of the kernel's filtration of `D_P`,
`lowerIdx`); if `G_b(P) ≠ 1` for `b = ⌈ψ(v)⌉` then `v = φ(ψ v) ≤ φ(b) ≤ 4a²` by `D1_Lj`.

No `sorry`, no `axiom`.
-/

open NumberField
open scoped Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.G15.Ladic

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  (j : L →+* PadicAlgCl p)

/-- `Gal(L/ℚ)` acts faithfully on `𝓞 L`. -/
theorem exists_smul_ne {s : Gal(L/ℚ)} (hs : s ≠ 1) : ∃ x : 𝓞 L, s • x ≠ x := by
  by_contra! h
  apply hs
  ext z
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) z
  have ha : s (algebraMap (𝓞 L) L a) = algebraMap (𝓞 L) L a := congrArg Subtype.val (h a)
  have hb : s (algebraMap (𝓞 L) L b) = algebraMap (𝓞 L) L b := congrArg Subtype.val (h b)
  rw [map_div₀, ha, hb]
  rfl

theorem decompFilt_antitone {i k : ℕ} (hik : i ≤ k) : decompFilt j k ≤ decompFilt j i := by
  intro s hs
  rw [Subgroup.mem_subgroupOf] at hs ⊢
  rw [Ideal.mem_inertia] at hs ⊢
  intro x
  exact Ideal.pow_le_pow_right (by omega) (hs x)

/-- The kernel's filtration of `D_P` is eventually trivial. -/
theorem exists_notMem_decompFilt {s : MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal}
    (hs : s ≠ 1) : ∃ i, s ∉ decompFilt j i := by
  have hs' : (s : Gal(L/ℚ)) ≠ 1 := fun h => hs (Subtype.ext h)
  obtain ⟨x, hx⟩ := exists_smul_ne hs'
  set y := (s : Gal(L/ℚ)) • x - x with hy
  have hy0 : y ≠ 0 := sub_ne_zero.mpr hx
  have hv0 : (primeOf j).intValuation y ≠ 0 :=
    (primeOf j).intValuation_ne_zero y hy0
  set m := WithZero.log ((primeOf j).intValuation y) with hm
  have hm0 : m ≤ 0 := by
    have h1 := (primeOf j).intValuation_le_one y
    rw [← WithZero.exp_log hv0, WithZero.exp_le_one_iff] at h1
    exact h1
  refine ⟨(-m).toNat, fun hmem => ?_⟩
  rw [Subgroup.mem_subgroupOf, Ideal.mem_inertia] at hmem
  have h2 := ((primeOf j).intValuation_le_pow_iff_mem y ((-m).toNat + 1)).mpr (hmem x)
  rw [← WithZero.exp_log hv0, WithZero.exp_le_exp] at h2
  omega

open Classical in
/-- The lower-index function of the kernel's filtration of `D_P`:
`s ∈ G_i(P) ↔ i < lowerIdx s` for `s ≠ 1`. -/
def lowerIdx (s : MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal) : ℕ :=
  if h : ∃ i, s ∉ decompFilt j i then Nat.find h else 0

theorem mem_decompFilt_iff (i : ℕ) (s : MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal)
    (hs : s ≠ 1) : s ∈ decompFilt j i ↔ i < lowerIdx j s := by
  classical
  have h := exists_notMem_decompFilt j hs
  have hl : lowerIdx j s = Nat.find h := by rw [lowerIdx, dif_pos h]
  rw [hl]
  constructor
  · intro hi
    by_contra hle
    push Not at hle
    exact Nat.find_spec h (decompFilt_antitone j hle hi)
  · intro hi
    by_contra hn
    exact Nat.find_min h hi hn

open Classical in
/-- **Upper ramification above `4a²` is trivial on `j L`.** If `1 ≤ a`, `g_0(Lj j) ≤ a!`,
`4a² < v` and `σ ∈ G^v(Lj j/ℚ_p)`, then `σ|_{j L} = 1`. -/
theorem tauOf_eq_one_of_mem_upperSet (a : ℕ) (ha : 1 ≤ a)
    (hea : LadicCond.ramCard (Lj j) 0 ≤ a.factorial) {v : ℝ} (hv : 4 * (a : ℝ) ^ 2 < v)
    {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : σ ∈ LadicCond.upperSet (Lj j) v) :
    tauOf j σ = 1 := by
  have hΓ := mem_decompFilt_iff j
  have hv1 : -1 ≤ v := by nlinarith
  obtain ⟨u, hu, hφu⟩ := TDifferent.exists_phiF_eq (decompFilt j) (lowerIdx j) hΓ hv1
  have hψ := TDifferent.sInf_phiF (decompFilt j) (lowerIdx j) hΓ hu hφu
  rw [mem_upperSet_iff j (tauOf_spec j σ), hψ] at hσ
  have hu1 : -1 < u := by
    rcases eq_or_lt_of_le hu with h | h
    · rw [← h, TDifferent.phiF_neg_one (decompFilt j) (lowerIdx j) hΓ] at hφu
      nlinarith
    · exact h
  rcases hσ with h | h
  · exact absurd h (not_le.mpr hu1)
  · by_contra hne
    set b := ⌈u⌉.toNat with hb
    have hne' : GlueConductor.ramGroup L (primeOf j).asIdeal b ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at h
      exact hne h
    have hD1 := D1_Lj j a ha hea b ((ramCard_Lj_ne_one_iff j b).mpr hne')
    rw [phiAt_Lj_eq] at hD1
    have hub : u ≤ (b : ℝ) := by
      have hc : (0 : ℤ) ≤ ⌈u⌉ := Int.ceil_nonneg_of_neg_one_lt hu1
      have : ((b : ℤ) : ℝ) = ((⌈u⌉ : ℤ) : ℝ) := by rw [hb, Int.toNat_of_nonneg hc]
      rw [show ((b : ℕ) : ℝ) = ((b : ℤ) : ℝ) from rfl, this]
      exact Int.le_ceil u
    have hmono := TDifferent.phiF_mono (decompFilt j) (lowerIdx j) hΓ hu hub
    linarith

/-- **Clause (i) of G15 for one number field**: if `1 ≤ a`, `g_0(ℚ_p(j L)) ≤ a!` and
`4a² < v`, every `σ ∈ G_{ℚ_p}^v` (`LadicCond.upperAbs p v`) fixes `j L` pointwise. -/
theorem apply_j_eq_of_mem_upperAbs (a : ℕ) (ha : 1 ≤ a)
    (hea : LadicCond.ramCard (Lj j) 0 ≤ a.factorial) {v : ℝ} (hv : 4 * (a : ℝ) ^ 2 < v)
    {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : σ ∈ LadicCond.upperAbs p v) (x : L) :
    σ (j x) = j x := by
  have h := tauOf_eq_one_of_mem_upperSet j a ha hea hv (mem_upperSet_of_mem_upperAbs j hσ)
  rw [← tauOf_spec, h]
  rfl

/-- `ℚ̄`-form: `(decomp p σ)|_K = 1` for `σ ∈ G_{ℚ_p}^v`, `v > 4a²`. -/
theorem restrictNormal_decomp_eq_one_of_mem_upperAbs {jQ : PkgI4.Qbar →+* PadicAlgCl p}
    (hjQ : ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) x, jQ (PkgI4.decomp p σ x) = σ (jQ x))
    (K : IntermediateField ℚ PkgI4.Qbar) [NumberField K] [IsGalois ℚ K]
    (a : ℕ) (ha : 1 ≤ a)
    (hea : LadicCond.ramCard (Lj (jQ.comp (algebraMap K PkgI4.Qbar))) 0 ≤ a.factorial)
    {v : ℝ} (hv : 4 * (a : ℝ) ^ 2 < v)
    {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : σ ∈ LadicCond.upperAbs p v) :
    (PkgI4.decomp p σ).restrictNormal K = 1 := by
  rw [← tauOf_eq_restrictNormal hjQ K σ]
  exact tauOf_eq_one_of_mem_upperSet _ a ha hea hv (mem_upperSet_of_mem_upperAbs _ hσ)

end ZInQ.Contrib.G15.Ladic

end
