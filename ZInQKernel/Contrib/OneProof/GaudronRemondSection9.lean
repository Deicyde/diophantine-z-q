import ZInQKernel.Contrib.OneProof.AnalyticStableHeight
import ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect

/-! # bost-gr9: the lower bound for the stable Faltings height, as the manuscript cites it

Task bost-gr9 (2026-11-17), report `docs/research/bost-gr9.md`, scratch `scratch/bost-gr9/`.

**The step.** Manuscript `diophantine_zq.tex` L894-895 (step E4 of h-trust): "The general lower bound
`h_F(Z) ≥ -(3/2) dim Z ≥ -2g` is recorded in [gr2014, Section 9]" (Gaudron–Rémond, *Polarisations et
isogénies*, Duke Math. J. 163 (2014), 2057-2108). The tree's row for this step was
`ZInQ.R3Residual.BostLowerBoundAn` (Bost, Sém. Bourbaki 795, Deligne's normalization, not cited by the
manuscript).

**This file.**
* `GaudronRemondSec9LowerAn` (§1): the bound in the form Gaudron–Rémond print it in §9 (in the proof of their
  Lemme 9.1, p. 2098, Faltings' original normalization, read by the locator audit), over the same
  analytic-height object `ZInQ.R3Residual.IsAnStableHeight` as `GaudronRemondThm14An`, so the two GR leaves
  share their definitions.
* §2: the normalization change (Deligne `h_D = h_F + (g/2) log π`) as a proved lemma
  (`bostAn_iff_faltings`, `deligne_heightFormula_shift`); `BostLowerBoundAn` reads `h_F ≥ -(g/2) log(2π²)`.
* §3: the comparison. `gaudronRemondSec9LowerAn_of_bostLowerBoundAn`: the new leaf is implied by the old row
  (never stronger). The converse fails numerically: `BostLowerBoundAn`'s constant `(1/2) log(2π²) = 1.4913…`
  is strictly below `3/2` (`half_log_two_pi_sq_lt`), so the old row is strictly stronger than what the
  manuscript cites, and `bostLowerBoundAn` cannot be proved from the new leaf.
* §4: the consumer's real need, R21 (`ZInQ.DefFaltings.R21_Bost`: `-(3/2) g ≤ h_F^st(A)`), proved from the new
  leaf through the same transports the old route used: `sec9Printed_of_an` (T35), `grBostBound_of_sec9Printed`
  (descent glue, `ZInQ.HeightSplit.GRBostBound`, the GR §9 form already stated in `TailY`), `r21_of_grBost'`.

No `sorry`, no `axiom`, no code that runs at build time. -/

open ZInQ.DefFaltings ZInQ.HeightFix

namespace ZInQ.BostGR9

/-! ## §1. The leaf -/

/-- **Leaf GR14-§9 (printed form): the general lower bound for the stable Faltings height**, as recorded by
É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057-2108, §9, in the proof
of Lemme 9.1, p. 2098 (Duke 163 p. 2098: citation only; docs/research/locators.md row R21; the
source is GR1 Cor 8.4: Gaudron–Rémond, Comment. Math. Helv. 89 (2014), Cor. 8.4, p. 400,
attribution: Bost; normalization p. 352): for every abelian variety `A` of
dimension `g` over a number field, `h(A) ≥ -(3/2) g`, `h` the stable Faltings height in Faltings' original
normalization (the normalization of GR14 Thm 1.4, `(i/2)^g ∫ η ∧ η̄`). Cited by the manuscript at
`diophantine_zq.tex` L894-895 (step E4) as "`h_F(Z) ≥ -(3/2) dim Z`, recorded in [gr2014, Section 9]".

Stated over `ZInQ.R3Residual.IsAnStableHeight`, the object `GaudronRemondThm14An` uses: the stable height
computed on the Néron model over a field of semistable reduction, with the archimedean metric
`(i/2)^g ∫ η̃ ∧ η̄̃` integrated over the complex manifold `A_τ(ℂ)^an` (densities in every holomorphic chart,
`IsHolChart`). -/
def GaudronRemondSec9LowerAn : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, ZInQ.R3Residual.IsAnStableHeight A x → -(3 / 2) * (g : ℝ) ≤ x

/-- The same bound over height-fix's printed stable height `IsPrintedStableHeight` (densities in translated
algebraic coordinates). Equivalent to `GaudronRemondSec9LowerAn` given T35 (`sec9Printed_of_an`,
`sec9An_of_printed`). -/
def GaudronRemondSec9LowerPrinted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsPrintedStableHeight A x → -(3 / 2) * (g : ℝ) ≤ x

/-! ## §2. Deligne's normalization against Faltings' original one (proved) -/

/-- **The height formula under the change of metric `‖·‖²_D = π^{-g} ‖·‖²_F`.** Deligne's metric
`(2π)^{-g} |∫ η ∧ η̄|` is `π^{-g}` times Faltings' `(i/2)^g ∫ η ∧ η̄`; with positive metrics `r τ`, the height
formula `(log s - ½ Σ_τ log ‖η‖²_τ) / [L:ℚ]` shifts by `(g/2) log π`, the sum running over the `[L:ℚ]`
embeddings `L → ℂ`. -/
theorem deligne_heightFormula_shift {L : Type} [Field L] [NumberField L] (g : ℕ) (s : ℝ)
    (r : (L →+* ℂ) → ℝ) (hr : ∀ τ, 0 < r τ) :
    (Real.log s - (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ / Real.pi ^ g)) / Module.finrank ℚ L =
      (Real.log s - (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ)) / Module.finrank ℚ L +
        (g : ℝ) / 2 * Real.log Real.pi := by
  have hpi : 0 < Real.pi ^ g := pow_pos Real.pi_pos g
  have hsum : ∑ τ : L →+* ℂ, Real.log (r τ / Real.pi ^ g) =
      ∑ τ : L →+* ℂ, Real.log (r τ) - (Module.finrank ℚ L : ℝ) * ((g : ℝ) * Real.log Real.pi) := by
    simp only [Real.log_div (hr _).ne' hpi.ne', Real.log_pow, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NumberField.Embeddings.card]
  have hn : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  rw [hsum]
  field_simp
  ring

/-- **The normalization change, pointwise**: Deligne's bound `h_D ≥ -(g/2) log 2π` with `h_D = x + (g/2) log π`
is `x ≥ -(g/2) log(2π²)` (`= -g log(π√2)`). -/
theorem deligne_bound_iff (g : ℕ) (x : ℝ) :
    -((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤ x + (g : ℝ) / 2 * Real.log Real.pi ↔
      -((g : ℝ) / 2 * Real.log (2 * Real.pi ^ 2)) ≤ x := by
  have h : Real.log (2 * Real.pi ^ 2) = Real.log (2 * Real.pi) + Real.log Real.pi := by
    rw [← Real.log_mul (by positivity) Real.pi_pos.ne', pow_two, mul_assoc]
  rw [h]
  constructor <;> intro h' <;> linarith

/-- `BostLowerBoundAn` in Faltings' original normalization. -/
def BostLowerBoundAnFaltings : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, ZInQ.R3Residual.IsAnStableHeight A x → -((g : ℝ) / 2 * Real.log (2 * Real.pi ^ 2)) ≤ x

/-- **The old row, read in Faltings' normalization** (proved; no leaf). -/
theorem bostAn_iff_faltings : ZInQ.R3Residual.BostLowerBoundAn ↔ BostLowerBoundAnFaltings :=
  ⟨fun h K _ _ A g hg x hx => (deligne_bound_iff g x).mp (h K A g hg x hx),
    fun h K _ _ A g hg x hx => (deligne_bound_iff g x).mpr (h K A g hg x hx)⟩

/-! ## §3. The old row against the cited print -/

/-- `(1/2) log(2π²) < 3/2`: the old row's constant is strictly smaller than GR §9's. -/
theorem half_log_two_pi_sq_lt : (1 / 2 : ℝ) * Real.log (2 * Real.pi ^ 2) < 3 / 2 := by
  have h := ZInQ.HeightSplit.log_two_pi_add_log_pi_lt_three
  have e : Real.log (2 * Real.pi ^ 2) = Real.log (2 * Real.pi) + Real.log Real.pi := by
    rw [← Real.log_mul (by positivity) Real.pi_pos.ne', pow_two, mul_assoc]
  rw [e]; linarith

/-- For `g ≥ 1` the old row's bound is strictly stronger than GR §9's at every height value between the
two constants: `-(3/2) g < -(g/2) log(2π²)`. -/
theorem sec9_bound_lt_bost (g : ℕ) (hg : 1 ≤ g) :
    -(3 / 2) * (g : ℝ) < -((g : ℝ) / 2 * Real.log (2 * Real.pi ^ 2)) := by
  have h := half_log_two_pi_sq_lt
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  nlinarith

/-- **The new leaf is never stronger than the old row** `BostLowerBoundAn`. -/
theorem gaudronRemondSec9LowerAn_of_bostLowerBoundAn (h : ZInQ.R3Residual.BostLowerBoundAn) :
    GaudronRemondSec9LowerAn := by
  intro K _ _ A g hg x hx
  have h1 := (bostAn_iff_faltings.mp h) K A g hg x hx
  have h2 := half_log_two_pi_sq_lt
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  nlinarith

/-! ## §4. The consumer's need (R21) from the new leaf -/

/-- **The printed-height form from the leaf** (T35 through `uniformizationLeafAll`, `mumfordTorsionAlgClosed`;
`isAnStableHeight_iff`). -/
theorem sec9Printed_of_an' (h : GaudronRemondSec9LowerAn)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : GaudronRemondSec9LowerPrinted :=
  fun K _ _ A g hg x hx =>
    h K A g hg x ((ZInQ.R3Residual.isAnStableHeight_iff (AvSplit.Final.h38 hUL hMT) A x).mpr hx)

/-- `sec9Printed_of_an'` with `uniformizationLeafAll` filled by its proof. -/
theorem sec9Printed_of_an (h : GaudronRemondSec9LowerAn)
    (hMT : AvSplit.MumfordTorsionAlgClosed) : GaudronRemondSec9LowerPrinted :=
  sec9Printed_of_an' h uniformizationLeafAll_proof hMT

/-- The analytic form from the printed form (given T35): the two forms are equivalent. -/
theorem sec9An_of_printed (h : GaudronRemondSec9LowerPrinted)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) : GaudronRemondSec9LowerAn :=
  fun K _ _ A g hg x hx => h K A g hg x ((ZInQ.R3Residual.isAnStableHeight_iff hT35 A x).mp hx)

/-- **GR §9 over the kernel's stable height** (`ZInQ.HeightSplit.GRBostBound`) from the printed form, T35 and
the descent glue (`isPrintedStableHeight_of`). -/
theorem grBostBound_of_sec9Printed (h : GaudronRemondSec9LowerPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) (hD : SemiAbelianDescendsPerfect) :
    ZInQ.HeightSplit.GRBostBound :=
  fun K _ _ A g hg x hx => h K A g hg x (isPrintedStableHeight_of (AvSplit.Final.h38 hUL hMT) hD hx)

/-- `grBostBound_of_sec9Printed` with the descent glue from the leaf `ChevalleyPerfect` (the shape of
`ZInQ.SemiAbDescend.bostLowerBound_of_printed_chevalley`, which the bundle chain uses). -/
theorem grBostBound_of_sec9Printed_chevalley (h : GaudronRemondSec9LowerPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) (hC : ZInQ.SemiAbDescend.ChevalleyPerfect) :
    ZInQ.HeightSplit.GRBostBound :=
  grBostBound_of_sec9Printed h hUL hMT (ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley hC)

/-- **R21 from GR §9** (`ZInQ.HeightSplit.r21_of_leaves` with `GRBostBound` in place of `BostLowerBound`): the
leaves N1, SS1, SS2 identify the infimum height with the Néron-model height, and the `≠ ⊥` half of H-19. -/
theorem r21_of_grBost (hB : ZInQ.HeightSplit.GRBostBound) (hN1 : ZInQ.H5Neron.NeronModelExists)
    (hSS1 : ZInQ.HeightSplit.SemistableReductionThm) (hSS2 : ZInQ.HeightSplit.SemistableNeronBaseChange)
    (hU : AnalyticUniformizationUnique) (hD : ZInQ.HeightSplit.MetrizedDimUnique) : R21_Bost := by
  intro K _ _ A g hg
  by_cases ht : stableFaltingsHeight A = ⊤
  · rw [ht]; exact le_top
  obtain ⟨x, hx⟩ := ZInQ.HeightSplit.exists_real_of_ne _ ht
    (ZInQ.HeightSplit.stableFaltingsHeight_ne_bot hN1 hSS1 hSS2 hU hD A)
  rw [hx]
  exact EReal.coe_le_coe_iff.mpr
    (hB K A g hg x ((ZInQ.HeightSplit.isStableFaltingsHeight_iff hN1 hSS1 hSS2 A x).mpr hx))

/-- `r21_of_grBost` with `MetrizedDimUnique` discharged (the shape of `ZInQ.HeightSplit.r21_of_leaves'`). -/
theorem r21_of_grBost' (hB : ZInQ.HeightSplit.GRBostBound) (hN1 : ZInQ.H5Neron.NeronModelExists)
    (hSS1 : ZInQ.HeightSplit.SemistableReductionThm) (hSS2 : ZInQ.HeightSplit.SemistableNeronBaseChange)
    (hU : AnalyticUniformizationUnique) : R21_Bost :=
  r21_of_grBost hB hN1 hSS1 hSS2 hU ZInQ.HeightSplit.metrizedDimUnique

/-- **R21 end to end from the GR §9 leaf** and the inputs the bundle chain already supplies
(`mumfordTorsionAlgClosed`, `chevalleyPerfect`, N1, SS1, SS2, AN3 uniqueness). -/
theorem r21_of_sec9An (h : GaudronRemondSec9LowerAn) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hC : ZInQ.SemiAbDescend.ChevalleyPerfect) (hN1 : ZInQ.H5Neron.NeronModelExists)
    (hSS1 : ZInQ.HeightSplit.SemistableReductionThm) (hSS2 : ZInQ.HeightSplit.SemistableNeronBaseChange)
    (hU : AnalyticUniformizationUnique) : R21_Bost :=
  r21_of_grBost' (grBostBound_of_sec9Printed_chevalley (sec9Printed_of_an h hMT)
    uniformizationLeafAll_proof hMT hC) hN1 hSS1 hSS2 hU

end ZInQ.BostGR9
