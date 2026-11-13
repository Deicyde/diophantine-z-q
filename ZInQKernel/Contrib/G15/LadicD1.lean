import ZInQKernel.Contrib.G15.LadicBridge
import ZInQKernel.Contrib.Different.Global

/-!
# G15: Glazer's D1 bound for the kernel's local field `ℚ_p(j L)`

With the transport of `LadicBridge.lean`, the closed global bound
`ZInQ.Contrib.Different.D1_genuine_closed` is restated purely in `LadicCond`'s local terms: for a
Galois number field `L` and `j : L →+* ℚ̄_p`, the local field `F = Lj j = ℚ_p(j L)` satisfies

  `g_0(F) ≤ a!`, `1 ≤ a`, `g_b(F) ≠ 1`  ⟹  `φ_F(b) ≤ 4a²`

with `g_i = LadicCond.ramCard F i` and `φ_F = LadicCond.phiAt F` (`D1_Lj`). On the way:
`TDifferent.phiF Γ m = ∑_{1 ≤ i ≤ m} |Γ_i|/|Γ_0|` at natural `m` (`phiF_natCast`), so
`LadicCond.phiAt (Lj j) m = GlueConductor.phi (ramCard L P) m` (`phiAt_Lj_natCast`).

No `sorry`, no `axiom`.
-/

open NumberField MeasureTheory

noncomputable section

namespace ZInQ.Contrib.G15.Ladic

section PhiNat

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
theorem filtR_eq_of_mem_Ioc (Γ : ℕ → Subgroup G) (m : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ioc (m : ℝ) (m + 1)) : TDifferent.filtR Γ t = Γ (m + 1) := by
  have h1 : ¬ t ≤ -1 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith [ht.1]
  have h2 : ⌈t⌉ = ((m + 1 : ℕ) : ℤ) := by
    rw [Int.ceil_eq_iff]
    push_cast
    exact ⟨by linarith [ht.1], ht.2⟩
  simp only [TDifferent.filtR, h1, ite_false, h2, Int.toNat_natCast]

/-- The integrand of `TDifferent.phiF`. -/
abbrev phiIntegrand (Γ : ℕ → Subgroup G) (t : ℝ) : ℝ :=
  (Nat.card (TDifferent.filtR Γ t) : ℝ) / (Nat.card (TDifferent.filtR Γ 0) : ℝ)

theorem phiIntegrand_eq (Γ : ℕ → Subgroup G) (m : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ioc (m : ℝ) (m + 1)) :
    phiIntegrand Γ t = (Nat.card (Γ (m + 1)) : ℝ) / (Nat.card (Γ 0) : ℝ) := by
  rw [phiIntegrand, filtR_eq_of_mem_Ioc Γ m ht, TDifferent.filtR_zero]

theorem intervalIntegrable_step (Γ : ℕ → Subgroup G) (m : ℕ) :
    IntervalIntegrable (phiIntegrand Γ) volume (m : ℝ) (m + 1) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
  have hc : IntegrableOn (fun _ : ℝ => (Nat.card (Γ (m + 1)) : ℝ) / (Nat.card (Γ 0) : ℝ))
      (Set.Ioc (m : ℝ) (m + 1)) volume := by
    refine integrableOn_const ?_
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  exact hc.congr_fun (fun t ht => (phiIntegrand_eq Γ m ht).symm) measurableSet_Ioc

theorem integral_step (Γ : ℕ → Subgroup G) (m : ℕ) :
    ∫ t in (m : ℝ)..(m + 1), phiIntegrand Γ t =
      (Nat.card (Γ (m + 1)) : ℝ) / (Nat.card (Γ 0) : ℝ) := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ =>
      (Nat.card (Γ (m + 1)) : ℝ) / (Nat.card (Γ 0) : ℝ)) ?_]
  · rw [intervalIntegral.integral_const]; simp
  · refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le (by linarith)] at ht
    exact phiIntegrand_eq Γ m ht

/-- **Herbrand's function at natural arguments**:
`φ(m) = ∑_{1 ≤ i ≤ m} |Γ_i| / |Γ_0|` (the kernel's `GlueConductor.phi`). -/
theorem phiF_natCast (Γ : ℕ → Subgroup G) (m : ℕ) :
    TDifferent.phiF Γ m = ∑ i ∈ Finset.Icc 1 m, (Nat.card (Γ i) : ℝ) / (Nat.card (Γ 0) : ℝ) := by
  have key : ∀ m : ℕ, IntervalIntegrable (phiIntegrand Γ) volume 0 (m : ℝ) ∧
      TDifferent.phiF Γ m =
        ∑ i ∈ Finset.Icc 1 m, (Nat.card (Γ i) : ℝ) / (Nat.card (Γ 0) : ℝ) := by
    intro m
    induction m with
    | zero => exact ⟨by simp, by simp [TDifferent.phiF_zero]⟩
    | succ n ih =>
      obtain ⟨hint, heq⟩ := ih
      have hstep := intervalIntegrable_step Γ n
      have hint' : IntervalIntegrable (phiIntegrand Γ) volume 0 ((n + 1 : ℕ) : ℝ) := by
        push_cast; exact hint.trans hstep
      refine ⟨hint', ?_⟩
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hint hstep
      have hphi : TDifferent.phiF Γ ((n + 1 : ℕ) : ℝ) =
          ∫ t in (0 : ℝ)..((n : ℝ) + 1), phiIntegrand Γ t := by
        rw [TDifferent.phiF]; push_cast; rfl
      rw [hphi, ← hsplit, integral_step, Finset.sum_Icc_succ_top (by omega)]
      rw [TDifferent.phiF] at heq
      rw [show (∫ t in (0 : ℝ)..(n : ℝ), phiIntegrand Γ t) = _ from heq]
  exact (key m).2

end PhiNat

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  (j : L →+* PadicAlgCl p)

open Classical in
/-- **`φ_{Lj j/ℚ_p}(m) = GlueConductor.phi (ramCard L P) m`** at natural `m`. -/
theorem phiAt_Lj_natCast (m : ℕ) :
    LadicCond.phiAt (Lj j) m =
      ((GlueConductor.phi (GlueConductor.ramCard L (primeOf j).asIdeal) m : ℚ) : ℝ) := by
  rw [phiAt_Lj_eq, phiF_natCast (decompFilt j) m, GlueConductor.phi]
  push_cast
  simp only [card_decompFilt]

/-- `g_i(Lj j) ≠ 1 ↔ G_i(P) ≠ 1`. -/
theorem ramCard_Lj_ne_one_iff (i : ℕ) :
    LadicCond.ramCard (Lj j) i ≠ 1 ↔ GlueConductor.ramGroup L (primeOf j).asIdeal i ≠ ⊥ := by
  rw [ramCard_Lj_eq, Ne, Ne, ← Subgroup.card_eq_one]

/-- `g_0(Lj j) = e(P | p)`. -/
theorem ramCard_Lj_zero :
    LadicCond.ramCard (Lj j) 0 = (primeOf j).asIdeal.ramificationIdx ℤ := by
  have := primeOf_liesOver j
  rw [ramCard_Lj_eq]
  show Nat.card (((primeOf j).asIdeal ^ (0 + 1)).inertia Gal(L/ℚ)) = _
  rw [zero_add, pow_one,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) (primeOf j).asIdeal
      Gal(L/ℚ),
    ← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) (Ideal.span {(p : ℤ)})
      (primeOf j).asIdeal]

/-- **D1 for the kernel's local field `F = ℚ_p(j L)`, in `LadicCond`'s terms (closed).**
If `1 ≤ a`, `g_0(F) ≤ a!` and `g_b(F) ≠ 1`, then `φ_F(b) ≤ 4a²`. -/
theorem D1_Lj (a : ℕ) (ha : 1 ≤ a) (hea : LadicCond.ramCard (Lj j) 0 ≤ a.factorial)
    (b : ℕ) (hb : LadicCond.ramCard (Lj j) b ≠ 1) :
    LadicCond.phiAt (Lj j) b ≤ 4 * (a : ℝ) ^ 2 := by
  have := primeOf_liesOver j
  rw [ramCard_Lj_zero] at hea
  have h := ZInQ.Contrib.Different.D1_genuine_closed L p (primeOf j).asIdeal a ha hea b
    ((ramCard_Lj_ne_one_iff j b).mp hb)
  rw [phiAt_Lj_natCast]
  exact_mod_cast h

end ZInQ.Contrib.G15.Ladic

end
