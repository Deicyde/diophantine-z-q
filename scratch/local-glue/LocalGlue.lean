import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Conductor.Breaks
import ZInQKernel.HDecomp.Textbook.Different
import ZInQKernel.HDecomp.Objects
import ZInQKernel.HDecomp.Descent.Constants
import ZInQKernel.Hypotheses.Height
import ZInQKernel.Multiplication.Certificate.Constants
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.Descent.ProjRep
import ZInQKernel.HDecomp.Descent.B2Glue
import ZInQKernel.HDecomp.Descent.Chi

/-! # local-data: `LocalData p r` (scratch/g15-ram) on G8's `r`

Assembled by `scratch/local-data/build.sh`. Check with
`lake env lean scratch/local-data/LocalData.lean`. The first part (through `end Reduction`) is a
verbatim copy of `scratch/g15-ram/G15Ram.lean` lines 8-1384; then verbatim definitions from
`scratch/g0-mod-galois/part_galois.lean`; then §4 (new). -/

/-!
# g15-ram: the open Prop `G15RamG` of g0-mod-newform (G15, clauses (i)-(ii))

Check with `lake env lean scratch/g15-ram/G15Ram.lean`.

* §0. Verbatim copies (from `scratch/g0-mod-newform/part_new.lean`, `NewForm.lean` lines
  1684-1690, 2037, 2448-2464) of `ModData`, `U0`, `LocalRamG`, `G15RamG`, and (from
  `scratch/g0-mod-galois/part_galois.lean` line 164) of `G0Galois.G11Out`.
* §1. The named smaller Props (glue), each with its glue step and source.
* §2. Local field: `upperBreakFix_of_hilbertSerre` (proved): Glazer's break bound
  `G_{ℚ_p}^t ⊆ G_F` for `t > 4a²` when `e(F/ℚ_p) ≤ a!`, at the level of `LadicCond`'s
  `upperAbs`, from the transport `HilbertSerreLadic` of T20 + T21 and the kernel's D1 arithmetic
  `GlueConductor.upper_break_le`.
* §3. The reduction `g15RamG_of_pieces` (proved).

Leaves and glue targets are hypotheses (`def … : Prop`); no `sorry`, no `axiom`.
-/

noncomputable section

/-! ## §0. Verbatim copies -/

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- **Output of G11:** `r` is unramified at every prime outside `T ∪ {ℓ}`. -/
def G11Out {ℓ : ℕ} [Fact ℓ.Prime] (T : Finset ℕ) (r : GaloisRep ℓ 2) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → p ≠ ℓ → r.UnramifiedAt p

end G0Galois

namespace G0ModNewform

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The data that G8-G12 produce for the model `A/L'`: an embedding `i : ℚ̄ → L̄'`, embeddings
`ιC : ℚ̄ → ℂ`, `ι₅ : ℚ̄ → ℚ̄₅`, `ι₃ : ℚ̄ → ℚ̄₃`, and the two `G_ℚ`-representations `r₅`, `r₃`
(N5 L719-734: `r_ℓ`, made a `G_ℚ`-representation by the Tate action and the descent of G7). -/
structure ModData (L : Type) [Field L] [NumberField L] (A : AbVar L) where
  i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure L
  ιC : Qbar →ₐ[ℚ] ℂ
  ι5 : Qbar →ₐ[ℚ] PadicAlgCl 5
  ι3 : Qbar →ₐ[ℚ] PadicAlgCl 3
  r5 : GaloisRep 5 2
  r3 : GaloisRep 3 2

section LocalRamSec

open LadicCond
open PkgI4 (GQp)

/-- Glazer's uniform bound for the last upper break, `U₀ = 4(DG₀)²` (N5 L826-830). -/
def U0 : ℝ := 4 * ((ZInQ.heightD * ZInQ.heightG0 : ℕ) : ℝ) ^ 2

end LocalRamSec

/-- `LocalRam` with clause (iii) in G11's global form (`G0Galois.G11Out`: `r.UnramifiedAt p`). -/
def LocalRamG (u : ℚ) (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (r : GaloisRep ℓ 2) :
    Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, U0 < t → ∀ σ ∈ LadicCond.upperAbs p t, r.restrictLocal p σ = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ LadicCond.wildSet, r.restrictLocal p σ = 1) ∧
    (p ∉ ZInQ.Mult.S_mul → ¬ p ∣ ZInQ.contactSupport ZInQ.Mult.S_mul u → r.UnramifiedAt p)

/-- **Open part of G15, final form.** Clauses (i)-(ii) of `LocalRam` (D1-D4 on G8's `r_ℓ`) and
clause (iii) as G11's output (proved by g0-mod-galois as `g11`, `G0Galois.G11Out`). -/
def G15RamG {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ) :
    Prop :=
  ∀ p : ℕ, ∀ hp : p.Prime,
    (p ≠ 5 → @LocalRamG u p ⟨hp⟩ 5 _ D.r5) ∧ (p = 5 → @LocalRamG u p ⟨hp⟩ 3 _ D.r3)

end G0ModNewform

/-! ## §1. The smaller named Props -/

namespace G15Ram

open PkgI4 (GQp GaloisRep)
open LadicCond G0ModNewform

section Local

variable (p : ℕ) [Fact p.Prime]

/-- **Glue: T20 + T21 transported to `ℚ̄_p`** (Hilbert's formula for the different, Serre,
*Corps locaux* IV §1 Prop. 4, and Serre's bound `v_F(𝔇) ≤ e − 1 + v_F(e)`, III §6 remark after
Prop. 13; UNVERIFIED numbering). For a finite Galois `F ⊆ ℚ̄_p` with lower ramification groups
`G_i = ramSet F i` (pulled back to `G_{ℚ_p}`) and `g_i = ramCard F i`, some `G_n` is trivial and
`∑_{i<n}(g_i − 1) ≤ e − 1 + e·v_p(e)` with `e = g_0`. Both parts are proved by t-different over
complete DVRs (`PkgI6.hilbertDifferentFormula`, `PkgI6.differentBound`). This Prop is derived
below from them and the transport `LadicDVRModel` (`hilbertSerre_of_model`). The existence of
`n` alone is already proved (`LadicCond.eventuallyTrivial`). -/
def HilbertSerreLadic : Prop :=
  ∀ F : Fld p, IsFinGal F → ∃ n : ℕ, ramSet F n ⊆ fixSet F ∧
    ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0)

/-- **Glue (D1 at the level of `upperAbs`; N5 L796-812, L824-827).** For a finite Galois
`F ⊆ ℚ̄_p` with ramification index `e(F/ℚ_p) ≤ a!`, every absolute upper ramification group
`G_{ℚ_p}^t` with `t > 4a²` fixes `F`. Proved below from `HilbertSerreLadic`
(`upperBreakFix_of_hilbertSerre`). -/
def UpperBreakFix : Prop :=
  ∀ F : Fld p, IsFinGal F → ∀ a : ℕ, 1 ≤ a → ramCard F 0 ≤ a.factorial →
    ∀ t : ℝ, 4 * (a : ℝ) ^ 2 < t → upperAbs p t ⊆ fixSet F

/-- **Glue (Serre, *Corps locaux* IV §3: `G^t ⊆ G^0`'s wild part for `t > 0`; UNVERIFIED
numbering).** For `t > 0` every element of `G_{ℚ_p}^t` lies in wild inertia: `|σx − x| < |x|`
for all `x ≠ 0`. (Proof: take `F` = the Galois closure of `ℚ_p(x)`; `σ|_F ∈ G^t(F) = G_{ψ(t)}(F)`
with `ψ(t) > 0`, so `σ|_F ∈ G_1(F)`, and `σx/x ≡ 1 mod 𝔪_F` because `|F^×| = |ϖ|^ℤ`.)
Proved below (`upperWild`). -/
def UpperWild : Prop :=
  ∀ t : ℝ, 0 < t → upperAbs p t ⊆ wildSet

/-- **Glue (tame extensions; Serre, *Corps locaux* IV §2, Cor. 1-4 of Prop. 7: `G_1` is the
`p`-Sylow subgroup of `G_0`; UNVERIFIED numbering).** If `F ⊆ ℚ̄_p` is finite Galois and `p` does
not divide `e(F/ℚ_p)`, wild inertia fixes `F`. Proved below (`wildFixTame`). -/
def WildFixTame : Prop :=
  ∀ F : Fld p, IsFinGal F → ¬ p ∣ ramCard F 0 → wildSet ⊆ fixSet F

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Glue on G8's construction (G8 + G3 + R6 + D2; N5 L719-727, L819-823).** On `G_F ∩ P_p`
the representation `r` is the scalar `β(σ)` (`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ ∘ σ` with `a_σ μ_σ = 1`
on `G_L ⊇ G_F`, and the Tate action of `A` trivial on `P_p ∩ G_F`: by Raynaud's criterion (R6)
`A` is semistable over `F ⊇ L_v(A[3])` (`A[5]` if `p = 3`), and then wild inertia acts trivially
(D2, `PkgI2.D2_fixed_of_raynaud`); at `p > D` by good reduction (G3) and
Néron–Ogg–Shafarevich). Here `β` is the local twist (the inverse of Glazer's `β`). -/
def TwistShape (r : GaloisRep ℓ 2) (F : Fld p) (β : GQp p → PadicAlgCl ℓ) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet,
    ((r.restrictLocal p σ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
      Matrix.scalar (Fin 2) (β σ)

/-- **Glue on G7's `β` (D3 + T16; N5 L823-844).** The local twist is trivial on
`G_{ℚ_p}^t ∩ G_F` for `t > U`: at odd `p`, `β|_{G_F}` is trivial on wild inertia (its square is
the tame `χ`, and a pro-`p` group has no quotient of order two;
`GlueConductor.char_trivial_of_odd_pgroup`);
at `p = 2`, local reciprocity with the upper numbering theorem (T16) and `(U_F^{e+1})⁴ = U_F^{3e+1}`
(D3, `GlueConductor.fourth_pow_mem`) bound the relative upper break of `β` by `3e`, and
`ψ_{F/ℚ_2}(u) ≥ u` moves it to the absolute numbering; `max(4D², 3e) ≤ U₀`
(`GlueConductor.max_le_U0`). -/
def TwistUpper (F : Fld p) (β : GQp p → PadicAlgCl ℓ) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, β σ = 1

/-- **Glue on G7's `β` at tame primes (N5 L848-851).** `β` is trivial on `P_p ∩ G_F` (for odd
`p`: `β²` is tame, `GlueConductor.char_trivial_of_odd_pgroup`). -/
def TwistTame (F : Fld p) (β : GQp p → PadicAlgCl ℓ) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β σ = 1

/-- **G8-G7 local data at `p ≤ D`** (N5 L819-844): `F` the Galois closure of `L_v(A[3])`
(`A[5]` if `p = 3`), of degree `≤ (DG₀)!`, so `e(F/ℚ_p) ≤ (DG₀)!`; the local twist `β`. -/
def SmallPrimeData (r : GaloisRep ℓ 2) : Prop :=
  ∃ (F : Fld p) (β : GQp p → PadicAlgCl ℓ), IsFinGal F ∧
    ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
    TwistShape p r F β ∧ TwistUpper p F β U0

/-- **G8-G7 local data at `p > D`** (N5 L848-851): `F` the Galois closure of `L_v`, tame since
`[L_v:ℚ_p] ≤ D < p` (the Galois closure of a tame extension is tame); the local twist `β`. -/
def LargePrimeData (r : GaloisRep ℓ 2) : Prop :=
  ∃ (F : Fld p) (β : GQp p → PadicAlgCl ℓ), IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
    TwistShape p r F β ∧ TwistTame p F β

/-- The local data at `p` for `r`, by the size of `p`. -/
def LocalData (r : GaloisRep ℓ 2) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → SmallPrimeData p r) ∧
    ((ZInQ.heightD : ℝ) < p → LargePrimeData p r)

end Local

/-! ## §2. Local field: the break bound at the level of `upperAbs` (proved) -/

section Break

variable {p : ℕ} [Fact p.Prime] {F : Fld p}

theorem ramSet_anti {i j : ℕ} (h : i ≤ j) : ramSet F j ⊆ ramSet F i := by
  rintro σ ⟨ϖ, hϖ, hσ⟩
  refine ⟨ϖ, hϖ, fun x hx hx1 => (hσ x hx hx1).trans ?_⟩
  exact pow_le_pow_of_le_one (norm_nonneg _) hϖ.2.1.le (by omega)

theorem card_image_mono (hF : IsFinGal F) {S T : Set (GQp p)} (h : S ⊆ T) :
    Nat.card (restr F '' S) ≤ Nat.card (restr F '' T) :=
  Nat.card_mono (finite_restr hF T) (Set.image_mono h)

theorem ramCard_anti (hF : IsFinGal F) : Antitone (ramCard F) := fun _ _ h =>
  card_image_mono hF (ramSet_anti h)

theorem one_le_ramCard (hF : IsFinGal F) (i : ℕ) : 1 ≤ ramCard F i := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  exact Nat.one_le_iff_ne_zero.mpr (ramCard_ne_zero hF hϖ i)

/-- If `g_i ≤ 1`, then `G_i` (pulled back) fixes `F`. -/
theorem fix_of_ramCard_le_one (hF : IsFinGal F) {i : ℕ} (h : ramCard F i ≤ 1) :
    ramSet F i ⊆ fixSet F := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  have hfin : Finite (restr F '' ramSet F i) := (finite_restr hF (ramSet F i)).to_subtype
  have hsub : Subsingleton (restr F '' ramSet F i) := Finite.card_le_one_iff_subsingleton.mp h
  have h1 : (1 : GQp p) ∈ ramSet F i := fixSet_subset_ramSet hϖ i (fun x _ => rfl)
  intro σ hσ x hx
  have he : (⟨restr F σ, σ, hσ, rfl⟩ : restr F '' ramSet F i) = ⟨restr F 1, 1, h1, rfl⟩ :=
    Subsingleton.elim _ _
  have := congrFun (congrArg Subtype.val he) ⟨x, hx⟩
  exact this

theorem ramCardR_of_gt {t : ℝ} (ht : -1 < t) : ramCardR F t = ramCard F ⌈t⌉.toNat := by
  unfold ramCardR ramSetR
  rw [if_neg (not_le.mpr ht)]
  rfl

theorem ramCardR_anti (hF : IsFinGal F) : Antitone (ramCardR F) := by
  intro s t hst
  unfold ramCardR ramSetR
  by_cases ht : t ≤ -1
  · have hs : s ≤ -1 := hst.trans ht
    rw [if_pos ht, if_pos hs]
  · rw [if_neg ht]
    by_cases hs : s ≤ -1
    · rw [if_pos hs]
      exact card_image_mono hF (Set.subset_univ _)
    · rw [if_neg hs]
      exact card_image_mono hF (ramSet_anti (Int.toNat_le_toNat (Int.ceil_mono hst)))

/-- The integrand of Herbrand's `φ` (`phiAt`). -/
def gInt (F : Fld p) (t : ℝ) : ℝ := (ramCardR F t : ℝ) / (ramCard F 0 : ℝ)

theorem phiAt_eq (u : ℝ) : phiAt F u = ∫ t in (0 : ℝ)..u, gInt F t := rfl

theorem gInt_anti (hF : IsFinGal F) : Antitone (gInt F) := fun _ _ h =>
  div_le_div_of_nonneg_right (by exact_mod_cast ramCardR_anti hF h) (Nat.cast_nonneg _)

theorem gInt_int (hF : IsFinGal F) (a b : ℝ) :
    IntervalIntegrable (gInt F) MeasureTheory.volume a b :=
  (gInt_anti hF).intervalIntegrable

theorem g0_pos (hF : IsFinGal F) : (0 : ℝ) < ramCard F 0 := by
  exact_mod_cast one_le_ramCard hF 0

theorem gInt_le_one (hF : IsFinGal F) {t : ℝ} (ht : -1 < t) : gInt F t ≤ 1 := by
  rw [gInt, div_le_one (g0_pos hF), ramCardR_of_gt ht]
  exact_mod_cast ramCard_anti hF (Nat.zero_le _)

theorem gInt_ge (hF : IsFinGal F) (t : ℝ) : 1 / (ramCard F 0 : ℝ) ≤ gInt F t := by
  have h1 : 1 ≤ ramCardR F t := by
    have h0 : -1 < max t 0 := lt_of_lt_of_le (by norm_num) (le_max_right t 0)
    have := ramCardR_anti hF (le_max_left t 0)
    rw [ramCardR_of_gt h0] at this
    exact (one_le_ramCard hF _).trans this
  exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (Nat.cast_nonneg _)

theorem gInt_nonneg (hF : IsFinGal F) (t : ℝ) : 0 ≤ gInt F t :=
  le_trans (by have := g0_pos hF; positivity) (gInt_ge hF t)

theorem phi_mono (hF : IsFinGal F) {u w : ℝ} (h : u ≤ w) : phiAt F u ≤ phiAt F w := by
  have h1 := intervalIntegral.integral_interval_sub_left (gInt_int hF 0 w) (gInt_int hF 0 u)
  have h2 : 0 ≤ ∫ t in u..w, gInt F t :=
    intervalIntegral.integral_nonneg h (fun x _ => gInt_nonneg hF x)
  rw [phiAt_eq, phiAt_eq]
  linarith

theorem phi_sub_le (hF : IsFinGal F) {w u : ℝ} (hw : 0 ≤ w) (hwu : w ≤ u) :
    phiAt F u - phiAt F w ≤ u - w := by
  rw [phiAt_eq, phiAt_eq,
    intervalIntegral.integral_interval_sub_left (gInt_int hF _ _) (gInt_int hF _ _)]
  calc ∫ t in w..u, gInt F t ≤ ∫ _ in w..u, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hwu (gInt_int hF _ _) intervalIntegrable_const
          (fun x hx => gInt_le_one hF (by linarith [hx.1]))
    _ = u - w := by rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]

theorem phi_ge (hF : IsFinGal F) {u : ℝ} (hu : 0 ≤ u) :
    u * (1 / (ramCard F 0 : ℝ)) ≤ phiAt F u := by
  rw [phiAt_eq]
  calc u * (1 / (ramCard F 0 : ℝ)) = ∫ _ in (0 : ℝ)..u, (1 / (ramCard F 0 : ℝ)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    _ ≤ ∫ t in (0 : ℝ)..u, gInt F t :=
        intervalIntegral.integral_mono_on hu intervalIntegrable_const (gInt_int hF _ _)
          (fun x _ => gInt_ge hF x)

theorem phi_nat (hF : IsFinGal F) (m : ℕ) :
    phiAt F m = ∑ k ∈ Finset.range m, (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
  rw [phiAt_eq]
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := gInt F) (a := fun k : ℕ => (k : ℝ)) (n := m) (fun k _ => gInt_int hF _ _)
  simp only [Nat.cast_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have : ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), gInt F x =
      ∫ _ in (k : ℝ)..((k + 1 : ℕ) : ℝ), (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall fun x hx => ?_
    rw [Set.uIoc_of_le hk] at hx
    have hx1 := hx.1
    have hx2 := hx.2
    push_cast at hx2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hxm : -1 < x := by linarith
    have hc : ⌈x⌉ = ((k + 1 : ℕ) : ℤ) := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor <;> linarith
    simp only [gInt]
    rw [ramCardR_of_gt hxm, hc, Int.toNat_natCast]
  rw [this, intervalIntegral.integral_const, smul_eq_mul]
  push_cast
  ring

theorem phi_eq_sum (g : ℕ → ℕ) (m : ℕ) :
    GlueConductor.phi g m = ∑ k ∈ Finset.range m, (g (k + 1) : ℚ) / g 0 := by
  induction m with
  | zero => rw [GlueConductor.phi_zero, Finset.sum_range_zero]
  | succ m ih => rw [GlueConductor.phi_succ, ih, Finset.sum_range_succ]

/-- **D1 at the level of `upperAbs` (GLUE, proved from `HilbertSerreLadic`).** -/
theorem upperBreakFix_of_hilbertSerre (h : HilbertSerreLadic p) : UpperBreakFix p := by
  classical
  intro F hF a ha hea t ht σ hσ
  have hex : ∃ n, ramSet F n ⊆ fixSet F ∧ ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0) := h F hF
  have hex' : ∃ n, ramSet F n ⊆ fixSet F := let ⟨n, hn, _⟩ := hex; ⟨n, hn⟩
  set n := Nat.find hex' with hn_def
  have hnfix : ramSet F n ⊆ fixSet F := Nat.find_spec hex'
  obtain ⟨N, hN, hsum⟩ := hex
  have hnN : n ≤ N := Nat.find_min' hex' hN
  have hsum' : ∑ i ∈ Finset.range n, (ramCard F i - 1) ≤
      ramCard F 0 - 1 + ramCard F 0 * padicValNat p (ramCard F 0) :=
    (Finset.sum_le_sum_of_subset (Finset.range_mono hnN)).trans hsum
  set w : ℕ := n - 1 with hw
  have ha2 : (0 : ℝ) ≤ 4 * (a : ℝ) ^ 2 := by positivity
  have hφw : phiAt F w < t := by
    have h4 : phiAt F w ≤ 4 * (a : ℝ) ^ 2 := by
      by_cases hn1 : n ≤ 1
      · have hw0 : w = 0 := by omega
        rw [hw0, Nat.cast_zero, phiAt_eq, intervalIntegral.integral_same]
        exact ha2
      · have hb : ¬ ramSet F w ⊆ fixSet F := Nat.find_min hex' (by omega)
        have hgb : 2 ≤ ramCard F w := by
          by_contra hlt
          exact hb (fix_of_ramCard_le_one hF (by omega))
        have hub := GlueConductor.upper_break_le p a (Fact.out) ha (ramCard F)
          (ramCard_anti hF) (one_le_ramCard hF) w n hgb (by omega) hea hsum'
        rw [phi_nat hF]
        have hcast : ((GlueConductor.phi (ramCard F) w : ℚ) : ℝ) =
            ∑ k ∈ Finset.range w, (ramCard F (k + 1) : ℝ) / ramCard F 0 := by
          rw [phi_eq_sum]
          push_cast
          rfl
        rw [← hcast]
        exact_mod_cast hub
    linarith
  set S := {u : ℝ | -1 ≤ u ∧ t ≤ phiAt F u} with hS
  have ht0 : 0 < t := by linarith
  have hg0 := g0_pos hF
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg w
  have hne : S.Nonempty := by
    refine ⟨w + t * ramCard F 0, by nlinarith, ?_⟩
    have h1 := phi_ge hF (u := w + t * ramCard F 0) (by positivity)
    have h2 : t ≤ (w + t * ramCard F 0) * (1 / (ramCard F 0 : ℝ)) := by
      rw [add_mul, mul_one_div, mul_one_div, mul_div_assoc, div_self hg0.ne', mul_one]
      have : (0 : ℝ) ≤ w / ramCard F 0 := div_nonneg hw0 hg0.le
      linarith
    exact h2.trans h1
  have hlb : ∀ u ∈ S, (w : ℝ) + (t - phiAt F w) ≤ u := by
    rintro u ⟨-, hu⟩
    by_cases huw : u ≤ w
    · exact absurd (hu.trans (phi_mono hF huw)) (not_le.mpr hφw)
    · have := phi_sub_le hF hw0 (le_of_not_ge huw)
      linarith
  have hψ : (w : ℝ) < sInf S := lt_of_lt_of_le (by linarith) (le_csInf hne hlb)
  have hσF : σ ∈ ramSetR F (sInf S) := hσ F hF
  unfold ramSetR at hσF
  rw [if_neg (by linarith)] at hσF
  apply hnfix
  refine ramSet_anti ?_ hσF
  have hz : ((w : ℕ) : ℤ) < ⌈sInf S⌉ := Int.lt_ceil.mpr (by exact_mod_cast hψ)
  omega

end Break

/-! ## §2b. Positive upper groups are wild (proved) -/

section Wild

variable {p : ℕ} [Fact p.Prime]

/-- `G_{ℚ_p}` acts isometrically on `ℚ̄_p` (copied from g0-mod-newform's `norm_aut`). -/
theorem norm_aut' (σ : GQp p) (y : Kbar p) : ‖σ y‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ y).symm

/-- For `t > 0`, `G^t(F) ⊆ G_1(F)` (pulled back): `ψ_F(t) > 0`. -/
theorem ramSet_one_of_upperSet {F : Fld p} (hF : IsFinGal F) {t : ℝ} (ht : 0 < t) {σ : GQp p}
    (hσ : σ ∈ upperSet F t) : σ ∈ ramSet F 1 := by
  set S := {u : ℝ | -1 ≤ u ∧ t ≤ phiAt F u} with hS
  have hg0 := g0_pos hF
  have hφ0 : phiAt F 0 = 0 := by rw [phiAt_eq, intervalIntegral.integral_same]
  have hne : S.Nonempty := by
    refine ⟨t * ramCard F 0, by nlinarith, ?_⟩
    have h1 := phi_ge hF (u := t * ramCard F 0) (by positivity)
    have h2 : t * ramCard F 0 * (1 / (ramCard F 0 : ℝ)) = t := by field_simp
    linarith
  have hlb : ∀ u ∈ S, t ≤ u := by
    rintro u ⟨-, hu⟩
    by_cases hu0 : u ≤ 0
    · have := phi_mono hF hu0
      linarith
    · have := phi_sub_le hF le_rfl (le_of_not_ge hu0)
      linarith
  have hψ : t ≤ sInf S := le_csInf hne hlb
  have hσF : σ ∈ ramSetR F (sInf S) := hσ
  unfold ramSetR at hσF
  rw [if_neg (by linarith)] at hσF
  refine ramSet_anti ?_ hσF
  have hz : (0 : ℤ) < ⌈sInf S⌉ := Int.lt_ceil.mpr (by push_cast; linarith)
  omega

/-- The predicate "`σ x / x ≡ 1`": `‖σ x − x‖ < ‖x‖`. -/
def WildAt (σ : GQp p) (y : Kbar p) : Prop := ‖σ y - y‖ < ‖y‖

theorem wildAt_mul {σ : GQp p} {y z : Kbar p} (hy : WildAt σ y) (hz : WildAt σ z) :
    WildAt σ (y * z) := by
  unfold WildAt at *
  have hy0 : 0 < ‖y‖ := lt_of_le_of_lt (norm_nonneg _) hy
  have hz0 : 0 < ‖z‖ := lt_of_le_of_lt (norm_nonneg _) hz
  have he : σ (y * z) - y * z = σ y * (σ z - z) + (σ y - y) * z := by rw [map_mul]; ring
  rw [he, norm_mul y z]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_aut']
    exact mul_lt_mul_of_pos_left hz hy0
  · rw [norm_mul]
    exact mul_lt_mul_of_pos_right hy hz0

theorem wildAt_inv {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) : WildAt σ y⁻¹ := by
  unfold WildAt at *
  have hy0 : 0 < ‖y‖ := lt_of_le_of_lt (norm_nonneg _) hy
  have hy0' : y ≠ 0 := norm_pos_iff.mp hy0
  have hσy : σ y ≠ 0 := (map_ne_zero σ).mpr hy0'
  have he : σ y⁻¹ - y⁻¹ = (y - σ y) / (σ y * y) := by
    rw [map_inv₀]; field_simp
  rw [he, norm_div, norm_mul, norm_aut', norm_sub_rev, norm_inv,
    div_lt_iff₀ (by positivity)]
  calc ‖σ y - y‖ < ‖y‖ := hy
    _ = ‖y‖⁻¹ * (‖y‖ * ‖y‖) := by field_simp

theorem wildAt_one (σ : GQp p) : WildAt σ 1 := by
  unfold WildAt; simp

theorem wildAt_pow {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) (n : ℕ) : WildAt σ (y ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact wildAt_one σ
  | succ n ih => rw [pow_succ]; exact wildAt_mul ih hy

theorem wildAt_zpow {σ : GQp p} {y : Kbar p} (hy : WildAt σ y) (k : ℤ) : WildAt σ (y ^ k) := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]; exact wildAt_pow hy n
  · rw [zpow_neg, zpow_natCast]; exact wildAt_inv (wildAt_pow hy n)

theorem natCast_mem (F : Fld p) : (p : Kbar p) ∈ F := by
  rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
  exact IntermediateField.algebraMap_mem _ _

/-- An element of `G_1(F)` (pulled back) satisfies `σx/x ≡ 1` for every `x ∈ F^×`. -/
theorem wild_of_ramSet_one {F : Fld p} {σ : GQp p} (hσ : σ ∈ ramSet F 1) {x : Kbar p}
    (hx : x ∈ F) (hx0 : x ≠ 0) : ‖σ x - x‖ < ‖x‖ := by
  obtain ⟨ϖ, hϖ, h1⟩ := hσ
  have hϖ1 : ‖ϖ‖ < 1 := hϖ.2.1
  have hϖpos : 0 < ‖ϖ‖ := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hpn : ‖(p : Kbar p)‖ < 1 := by rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ hp1
    have hp := hϖ.2.2 _ (natCast_mem F) hpn
    exact lt_of_lt_of_le (by rw [norm_p_kbar]; positivity) hp
  have hϖ0 : ϖ ≠ 0 := norm_pos_iff.mp hϖpos
  -- `ϖ` and the units of `F` satisfy `WildAt`
  have hwϖ : WildAt σ ϖ := by
    unfold WildAt
    have := h1 ϖ hϖ.1 hϖ1.le
    calc ‖σ ϖ - ϖ‖ ≤ ‖ϖ‖ ^ (1 + 1) := this
      _ < ‖ϖ‖ := by rw [pow_two]; exact mul_lt_of_lt_one_right hϖpos hϖ1
  have hwu : ∀ z ∈ F, ‖z‖ = 1 → WildAt σ z := by
    intro z hz hz1
    unfold WildAt
    rw [hz1]
    calc ‖σ z - z‖ ≤ ‖ϖ‖ ^ (1 + 1) := h1 z hz hz1.le
      _ < 1 := pow_lt_one₀ (norm_nonneg _) hϖ1 (by norm_num)
  -- discreteness: `x = ϖ^k z` with `‖z‖ = 1`
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hxpos ((one_lt_inv₀ hϖpos).mpr hϖ1)
  set k : ℤ := -(n + 1) with hk
  set z := x * (ϖ ^ k)⁻¹ with hz
  have hzF : z ∈ F := mul_mem hx (inv_mem (zpow_mem hϖ.1 k))
  have hnk : ‖ϖ ^ k‖ = ‖ϖ‖⁻¹ ^ (n + 1) := by
    rw [norm_zpow, hk, zpow_neg, inv_zpow]
  have hnk' : ‖ϖ‖⁻¹ ^ n = ‖ϖ ^ k‖ * ‖ϖ‖ := by
    rw [hnk, zpow_add₀ (inv_ne_zero hϖpos.ne'), zpow_one, mul_assoc,
      inv_mul_cancel₀ hϖpos.ne', mul_one]
  have hpk : 0 < ‖ϖ ^ k‖ := by rw [hnk]; positivity
  have hz_le : ‖z‖ ≤ 1 := by
    rw [hz, norm_mul, norm_inv, ← div_eq_mul_inv, div_le_one hpk, hnk]
    exact hn2
  have hz_gt : ‖ϖ‖ < ‖z‖ := by
    rw [hz, norm_mul, norm_inv, ← div_eq_mul_inv, lt_div_iff₀ hpk]
    rw [hnk'] at hn1
    linarith [mul_comm ‖ϖ ^ k‖ ‖ϖ‖]
  have hz1 : ‖z‖ = 1 := by
    by_contra hne
    exact absurd (hϖ.2.2 z hzF (lt_of_le_of_ne hz_le hne)) (not_le.mpr hz_gt)
  have hxz : x = ϖ ^ k * z := by
    rw [hz, mul_comm x, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero k hϖ0), one_mul]
  have := wildAt_mul (wildAt_zpow hwϖ k) (hwu z hzF hz1)
  rw [← hxz] at this
  exact this

instance isGalois_Kbar : IsGalois ℚ_[p] (Kbar p) := ⟨⟩

/-- **`UpperWild` (GLUE, proved).** For `t > 0`, `G_{ℚ_p}^t ⊆ P_p`. -/
theorem upperWild : UpperWild p := by
  intro t ht σ hσ x hx0
  let F := FiniteGaloisIntermediateField.adjoin ℚ_[p] ({x} : Set (Kbar p))
  have hF : IsFinGal F.toIntermediateField := ⟨inferInstance, inferInstance⟩
  have hxF : x ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin ℚ_[p] {x} rfl
  exact wild_of_ramSet_one (ramSet_one_of_upperSet hF ht (hσ _ hF)) hxF hx0

end Wild

/-! ## §2d. Wild inertia fixes tame extensions (proved) -/

section Tame

variable {p : ℕ} [Fact p.Prime]

theorem wildSet_mul {σ τ : GQp p} (hσ : σ ∈ wildSet) (hτ : τ ∈ wildSet) : σ * τ ∈ wildSet := by
  intro x hx
  have hτx : τ x ≠ 0 := (map_ne_zero τ).mpr hx
  have he : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
    rw [AlgEquiv.mul_apply]; ring
  rw [he]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx))
  have := hσ (τ x) hτx
  rwa [norm_aut'] at this

theorem wildSet_pow {σ : GQp p} (hσ : σ ∈ wildSet) (k : ℕ) : σ ^ k ∈ wildSet := by
  induction k with
  | zero => rw [pow_zero]; exact one_mem_wildSet
  | succ k ih => rw [pow_succ]; exact wildSet_mul ih hσ

theorem norm_natCast_kbar {m : ℕ} (hm : ¬ p ∣ m) : ‖(m : Kbar p)‖ = 1 := by
  have h := PadicAlgCl.norm_extends p (m : ℚ_[p])
  have e : ((m : ℚ_[p]) : PadicAlgCl p) = (m : Kbar p) := map_natCast (algebraMap ℚ_[p] _) m
  rw [e] at h
  rw [h, Padic.norm_natCast_eq_one_iff]
  exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm)

/-- In an ultrametric normed group, a finite sum of terms of norm `< c` has norm `< c`. -/
theorem norm_sum_range_lt {f : ℕ → Kbar p} {c : ℝ} (hc : 0 < c) (m : ℕ)
    (hf : ∀ k < m, ‖f k‖ < c) : ‖∑ k ∈ Finset.range m, f k‖ < c := by
  induction m with
  | zero => simpa using hc
  | succ m ih =>
    rw [Finset.sum_range_succ]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (ih fun k hk => hf k (by omega)) (hf m (by omega)))

/-- **The averaging argument.** A wild `σ` with `σ^m x = x`, `p ∤ m`, fixes `x`. -/
theorem fix_of_wild_pow {σ : GQp p} (hσ : σ ∈ wildSet) {m : ℕ} (hm0 : 0 < m) (hpm : ¬ p ∣ m)
    {x : Kbar p} (hx : (σ ^ m) x = x) : σ x = x := by
  set S := ∑ k ∈ Finset.range m, (σ ^ k) x with hS
  have hσS : σ S = S := by
    have h1 : σ S = ∑ k ∈ Finset.range m, (σ ^ (k + 1)) x := by
      rw [hS, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    have h2 := Finset.sum_range_succ' (fun k => (σ ^ k) x) m
    have h3 := Finset.sum_range_succ (fun k => (σ ^ k) x) m
    simp only [pow_zero, AlgEquiv.one_apply] at h2
    rw [hx] at h3
    rw [h1]
    rw [← hS] at h3
    linear_combination -(h3.symm.trans h2)
  have hkS : ∀ k : ℕ, (σ ^ k) S = S := by
    intro k
    induction k with
    | zero => rw [pow_zero, AlgEquiv.one_apply]
    | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσS]
  have hm : (m : Kbar p) ≠ 0 := by
    intro h
    have := norm_natCast_kbar (p := p) hpm
    rw [h, norm_zero] at this
    exact zero_ne_one this
  set y := (m : Kbar p)⁻¹ * S with hy
  have hky : ∀ k : ℕ, (σ ^ k) y = y := by
    intro k
    rw [hy, map_mul, map_inv₀, map_natCast, hkS]
  set z := x - y with hz
  have hz0 : z = 0 := by
    by_contra hne
    have hsum : ∑ k ∈ Finset.range m, (z - (σ ^ k) z) = (m : Kbar p) * z := by
      have hterm : ∀ k ∈ Finset.range m, z - (σ ^ k) z = x - (σ ^ k) x := by
        intro k _
        rw [hz, map_sub, hky]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← hS, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, hz, hy, mul_sub, ← mul_assoc, mul_inv_cancel₀ hm,
        one_mul]
    have hlt : ‖∑ k ∈ Finset.range m, (z - (σ ^ k) z)‖ < ‖z‖ := by
      apply norm_sum_range_lt (norm_pos_iff.mpr hne)
      intro k _
      rw [norm_sub_rev]
      exact wildSet_pow hσ k z hne
    rw [hsum, norm_mul, norm_natCast_kbar hpm, one_mul] at hlt
    exact lt_irrefl _ hlt
  have hxy : x = y := sub_eq_zero.mp hz0
  rw [hxy]
  have := hky 1
  rwa [pow_one] at this

/-- The inertia subgroup at level `F`, pulled back: `{σ | ‖σx − x‖ < 1 for x ∈ 𝓞_F}`. -/
def inertiaSub (F : Fld p) (hF : IsFinGal F) : Subgroup (GQp p) where
  carrier := {σ | ∀ x ∈ F, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}
  one_mem' := by
    intro x _ _
    simp
  mul_mem' := by
    intro σ τ hσ hτ x hx hx1
    have hτx : τ x ∈ F := apply_mem hF τ hx
    have he : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [he]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hτ x hx hx1))
    exact hσ (τ x) hτx (by rw [norm_aut']; exact hx1)
  inv_mem' := by
    intro σ hσ x hx hx1
    have hσx : σ⁻¹ x ∈ F := apply_mem hF σ⁻¹ hx
    have h1 : ‖σ⁻¹ x‖ ≤ 1 := by rw [norm_aut']; exact hx1
    have h2 := hσ (σ⁻¹ x) hσx h1
    have he : σ (σ⁻¹ x) = x := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [he, norm_sub_rev] at h2
    exact h2

theorem ramSet_zero_eq (F : Fld p) (hF : IsFinGal F) :
    ramSet F 0 = (inertiaSub F hF : Set (GQp p)) := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif hF.1
  ext σ
  constructor
  · rintro ⟨ϖ', hϖ', h⟩ x hx hx1
    have := h x hx hx1
    rw [zero_add, pow_one] at this
    exact lt_of_le_of_lt this hϖ'.2.1
  · intro h
    refine ⟨ϖ, hϖ, fun x hx hx1 => ?_⟩
    rw [zero_add, pow_one]
    exact hϖ.2.2 _ (F.sub_mem (apply_mem hF σ hx) hx) (h x hx hx1)

/-- `e(F/ℚ_p) = |G_0|` as the order of a subgroup of `Gal(F/ℚ_p)`. -/
theorem ramCard_zero_eq (F : Fld p) (hF : IsFinGal F) :
    haveI : Normal ℚ_[p] F := hF.2.to_normal
    ramCard F 0 =
      Nat.card ((inertiaSub F hF).map (AlgEquiv.restrictNormalHom F)) := by
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  set φ : (F ≃ₐ[ℚ_[p]] F) → (F → Kbar p) := fun s x => ((s x : F) : Kbar p) with hφ
  have hφinj : Function.Injective φ := by
    intro s t h
    ext x
    have := congrFun h x
    exact this
  have himg : restr F '' ramSet F 0 =
      φ '' ((inertiaSub F hF).map (AlgEquiv.restrictNormalHom F) : Set _) := by
    rw [ramSet_zero_eq F hF, Subgroup.coe_map, Set.image_image]
    refine Set.image_congr fun σ _ => ?_
    funext x
    simp only [hφ, restr]
    exact (AlgEquiv.restrictNormalHom_apply F σ x).symm
  unfold ramCard
  rw [himg, Nat.card_image_of_injective hφinj]
  rfl

/-- **`WildFixTame` (GLUE, proved).** If `F/ℚ_p` is finite Galois with `p ∤ e(F/ℚ_p)`, wild
inertia fixes `F`. The restriction `s` of a wild `σ` lies in the inertia subgroup, of order `e`,
so its order `m` is prime to `p`; the averaging `y = m⁻¹ ∑_{k<m} σ^k x` then gives `σx = x`. -/
theorem wildFixTame : WildFixTame p := by
  intro F hF hpe σ hσ x hx
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  set s := AlgEquiv.restrictNormalHom F σ with hs
  have hσI : σ ∈ inertiaSub F hF := by
    intro y _ hy1
    by_cases hy0 : y = 0
    · simp [hy0]
    · exact lt_of_lt_of_le (hσ y hy0) hy1
  have hsK : s ∈ (inertiaSub F hF).map (AlgEquiv.restrictNormalHom F) := ⟨σ, hσI, rfl⟩
  have hdvd : orderOf s ∣ ramCard F 0 := by
    rw [ramCard_zero_eq F hF]
    have := orderOf_dvd_natCard (⟨s, hsK⟩ : (inertiaSub F hF).map (AlgEquiv.restrictNormalHom F))
    rwa [Subgroup.orderOf_mk] at this
  have he0 : ramCard F 0 ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_ramCard hF 0)
  have hm0 : 0 < orderOf s :=
    Nat.pos_of_ne_zero fun h => he0 (by rw [h] at hdvd; exact zero_dvd_iff.mp hdvd)
  have hpm : ¬ p ∣ orderOf s := fun h => hpe (h.trans hdvd)
  have hsm : AlgEquiv.restrictNormalHom F (σ ^ orderOf s) = 1 := by
    rw [map_pow, ← hs, pow_orderOf_eq_one]
  have hfix : (σ ^ orderOf s) x = x := by
    have := (AlgEquiv.restrictNormal_eq_one_iff F (σ ^ orderOf s)).mp hsm x hx
    exact this
  exact fix_of_wild_pow hσ hm0 hpm hfix

end Tame

/-! ## §2c. `HilbertSerreLadic` from T20 + T21 (proved by t-different) and a DVR model -/

section Bridge

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Glue: the DVR model of a finite Galois `F ⊆ ℚ̄_p`** (the transport between `LadicCond`'s
norm-defined filtrations and the ring-theoretic setting of T20-T22, `PkgI6`; Serre, *Corps
locaux*, II §2 and IV §1). There are a complete DVR `A` with perfect residue field and a DVR `B`
finite, torsion-free, separable and Galois over `A` (namely `A = ℤ_p` and `B = 𝓞_F`, the elements
of norm `≤ 1`), whose lower ramification groups `PkgI6.lowerRam A B i` have the orders
`ramCard F i` and are trivial only when `ramSet F i` fixes `F`, whose ramification index is
`e = ramCard F 0`, with `(p) = 𝔪_B^e` and every integer prime to `p` a unit of `B`. -/
def LadicDVRModel (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ F : Fld p, IsFinGal F →
    ∃ (A B : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (_ : IsAdicComplete (maximalIdeal A) A) (_ : PerfectField (ResidueField A))
      (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B) (_ : Algebra A B)
      (_ : Module.Finite A B) (_ : Module.IsTorsionFree A B)
      (_ : Algebra.IsSeparable (FractionRing A) (FractionRing B))
      (_ : IsGalois (FractionRing A) (FractionRing B)),
      (∀ i, Nat.card (PkgI6.lowerRam A B i) = ramCard F i) ∧
      (∀ i, PkgI6.lowerRam A B i = ⊥ → ramSet F i ⊆ fixSet F) ∧
      Ideal.ramificationIdx (maximalIdeal B) A = ramCard F 0 ∧
      Ideal.span {(p : B)} = maximalIdeal B ^ ramCard F 0 ∧
      (∀ n : ℕ, ¬ p ∣ n → IsUnit (n : B))

/-- In `B` with `(p) = 𝔪^e` and integers prime to `p` units: `(e) = 𝔪^{e·v_p(e)}`. -/
theorem span_natCast_eq {B : Type} [CommRing B] [IsLocalRing B] {p : ℕ} (hp : p.Prime)
    {e : ℕ} (he : e ≠ 0) (hpB : Ideal.span {(p : B)} = maximalIdeal B ^ e)
    (hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : B)) :
    Ideal.span {(e : B)} = maximalIdeal B ^ (e * padicValNat p e) := by
  have hdec := Nat.ordProj_mul_ordCompl_eq_self e p
  have hnd := Nat.not_dvd_ordCompl hp he
  rw [Nat.factorization_def e hp] at hdec hnd
  set v := padicValNat p e
  set u := e / p ^ v
  have hcast : (e : B) = (p : B) ^ v * (u : B) := by
    conv_lhs => rw [← hdec]
    push_cast
    rfl
  rw [hcast, ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hpB,
    Ideal.span_singleton_eq_top.mpr (hunit u hnd), Ideal.mul_top, ← pow_mul]

variable {p : ℕ} [Fact p.Prime]

/-- **`HilbertSerreLadic` from T20 + T21 and the DVR model (GLUE, proved).** T20 and T21 are
the kernel's theorems `PkgI6.hilbertDifferentFormula`, `PkgI6.differentBound` (t-different). -/
theorem hilbertSerre_of_model (hM : LadicDVRModel p) : HilbertSerreLadic p := by
  intro F hF
  obtain ⟨A, B, _, _, _, _, _, _, _, _, _, _, _, _, _, hcard, hbot, he, hpB, hunit⟩ := hM F hF
  obtain ⟨N, hN, hD⟩ := PkgI6.hilbertDifferentFormula A B
  have hB := PkgI6.differentBound A B
  refine ⟨N, hbot N hN, ?_⟩
  have hsum : ∑ i ∈ Finset.range N, (Nat.card (PkgI6.lowerRam A B i) - 1) =
      ∑ i ∈ Finset.range N, (ramCard F i - 1) :=
    Finset.sum_congr rfl fun i _ => by rw [hcard i]
  rw [hsum] at hD
  have he0 : ramCard F 0 ≠ 0 := Nat.one_le_iff_ne_zero.mp (one_le_ramCard hF 0)
  rw [he, hD, span_natCast_eq (Fact.out) he0 hpB hunit, ← pow_add] at hB
  have hm0 : maximalIdeal B ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hmu : ¬ IsUnit (maximalIdeal B) := by
    rw [Ideal.isUnit_iff]
    exact (maximalIdeal.isMaximal B).ne_top
  exact (pow_dvd_pow_iff hm0 hmu).mp hB

end Bridge

/-! ## §2e. The DVR model over `ℤ_p`: the arithmetic conjuncts are automatic -/

section BridgeZp

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

instance perfectField_residueField_Zp (p : ℕ) [Fact p.Prime] :
    PerfectField (ResidueField ℤ_[p]) :=
  PerfectField.of_ringEquiv (K := ZMod p) PadicInt.residueField.symm

/-- **Glue: the DVR model of a finite Galois `F ⊆ ℚ̄_p` over `ℤ_p`** (transport; Serre, *Corps
locaux* II §2, IV §1). There is a DVR `B` (namely `𝓞_F`, the elements of norm `≤ 1`), finite,
torsion-free, separable and Galois over `ℤ_p`, whose lower ramification groups
`PkgI6.lowerRam ℤ_p B i` have the orders `ramCard F i` and are trivial only when `ramSet F i`
fixes `F`. This is `LadicDVRModel` with `A = ℤ_p`; its other conjuncts are proved
(`ladicDVRModel_of_Zp`). -/
def LadicDVRModelZp (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ F : Fld p, IsFinGal F →
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (_ : Algebra ℤ_[p] B) (_ : Module.Finite ℤ_[p] B) (_ : Module.IsTorsionFree ℤ_[p] B)
      (_ : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing B))
      (_ : IsGalois (FractionRing ℤ_[p]) (FractionRing B)),
      (∀ i, Nat.card (PkgI6.lowerRam ℤ_[p] B i) = ramCard F i) ∧
      (∀ i, PkgI6.lowerRam ℤ_[p] B i = ⊥ → ramSet F i ⊆ fixSet F)

variable {p : ℕ} [Fact p.Prime]

/-- **`LadicDVRModel` from its `ℤ_p` form (GLUE, proved).** `e(B/ℤ_p) = |G_0|`
(t-different's `TDifferent.card_lowerRam_zero`), `(p) = 𝔪_{ℤ_p}` maps to `𝔪_B^e`
(`TDifferent.map_maximalIdeal_eq_pow`), and integers prime to `p` are units of `ℤ_p`. -/
theorem ladicDVRModel_of_Zp (h : LadicDVRModelZp p) : LadicDVRModel p := by
  intro F hF
  obtain ⟨B, _, _, _, _, _, _, _, _, hcard, hbot⟩ := h F hF
  have : IsGaloisGroup (B ≃ₐ[ℤ_[p]] B) ℤ_[p] B := TDifferent.isGaloisGroup_algEquiv ℤ_[p] B
  have : Finite (B ≃ₐ[ℤ_[p]] B) := TDifferent.finite_algEquiv ℤ_[p] B
  have : PerfectField (maximalIdeal ℤ_[p]).ResidueField :=
    PerfectField.of_ringEquiv (K := ResidueField ℤ_[p])
      (RingEquiv.ofBijective
        (algebraMap (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) (maximalIdeal ℤ_[p]).ResidueField :
          ResidueField ℤ_[p] →+* _)
        (maximalIdeal ℤ_[p]).bijective_algebraMap_quotient_residueField)
  have : Algebra.HasSeparableResidueFieldsAt ℤ_[p] B (maximalIdeal ℤ_[p]) := inferInstance
  have he : Ideal.ramificationIdx (maximalIdeal B) ℤ_[p] = ramCard F 0 := by
    rw [← TDifferent.card_lowerRam_zero ℤ_[p] B, hcard 0]
  refine ⟨ℤ_[p], B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hcard, hbot, he, ?_, ?_⟩
  · have hmap := TDifferent.map_maximalIdeal_eq_pow ℤ_[p] B
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast,
      he] at hmap
    exact hmap
  · intro n hn
    have hu : IsUnit (n : ℤ_[p]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hn
    have := hu.map (algebraMap ℤ_[p] B)
    rwa [map_natCast] at this

end BridgeZp

/-! ## §2f. The `ℤ_p`-model `𝓞_F = integralClosure ℤ_p F` (proved): `LadicDVRModelZp` -/

section DVRModelSec

open IsLocalRing Polynomial

variable {p : ℕ} [Fact p.Prime]

section Model

variable (F : Fld p)

/-- `ℤ_p → ℚ_p → F`. -/
@[reducible] def algZpF : Algebra ℤ_[p] F :=
  ((algebraMap ℚ_[p] F).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra

attribute [local instance] algZpF

instance towerZpF : IsScalarTower ℤ_[p] ℚ_[p] F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The ring of integers `𝓞_F = integralClosure ℤ_p F`. -/
abbrev OF := integralClosure ℤ_[p] F

theorem norm_eq_spectral (x : F) : ‖(x : Kbar p)‖ = spectralNorm ℚ_[p] F x := by
  rw [spectralNorm.eq_of_tower (L := Kbar p) x, PadicAlgCl.spectralNorm_eq]
  rfl

variable [FiniteDimensional ℚ_[p] F]

/-- `y ∈ F` is integral over `ℤ_p` iff `‖y‖ ≤ 1` (copied from glue-sqrt-local's
`isIntegral_iff_spectralNorm_le_one`, with the norm of `ℚ̄_p`). -/
theorem isIntegral_iff_norm_le_one (y : F) :
    IsIntegral ℤ_[p] y ↔ ‖(y : Kbar p)‖ ≤ 1 := by
  rw [norm_eq_spectral]
  have hyQ : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  constructor
  · intro hy n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyQ)
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq, minpoly.aeval]

theorem mem_OF (y : F) : y ∈ OF F ↔ ‖(y : Kbar p)‖ ≤ 1 := isIntegral_iff_norm_le_one F y

theorem norm_le_one (b : OF F) : ‖((b : F) : Kbar p)‖ ≤ 1 := (mem_OF F b).mp b.2

theorem isUnit_iff_norm (b : OF F) : IsUnit b ↔ ‖((b : F) : Kbar p)‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖(((u : OF F) : F) : Kbar p)‖ * ‖((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p)‖ = 1 := by
      rw [← norm_mul]
      have : ((u : OF F) : F) * (((u⁻¹ : (OF F)ˣ) : OF F) : F) = 1 := by
        rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
      have h2 : (((u : OF F) : F) : Kbar p) * ((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p) = 1 := by
        rw [← IntermediateField.coe_mul, this, IntermediateField.coe_one]
      rw [h2, norm_one]
    have a1 := norm_le_one F u
    have a2 := norm_le_one F (u⁻¹ : (OF F)ˣ)
    have b1 := norm_nonneg ((((u : OF F) : F) : Kbar p))
    have b2 := norm_nonneg (((((u⁻¹ : (OF F)ˣ) : OF F) : F) : Kbar p))
    nlinarith
  · intro h
    have hx0 : (b : F) ≠ 0 := by
      intro h0
      rw [h0, IntermediateField.coe_zero, norm_zero] at h
      exact zero_ne_one h
    have hinv : ‖(((b : F)⁻¹ : F) : Kbar p)‖ = 1 := by
      rw [IntermediateField.coe_inv, norm_inv, h, inv_one]
    have hint : ((b : F)⁻¹) ∈ OF F := (mem_OF F _).mpr hinv.le
    refine IsUnit.of_mul_eq_one (⟨_, hint⟩ : OF F) ?_
    apply Subtype.ext
    simp [hx0]

theorem isLocalRing_OF : IsLocalRing (OF F) := by
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_iff_norm] at ha hb ⊢
  have ha' : ‖((a : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F a) ha
  have hb' : ‖((b : F) : Kbar p)‖ < 1 := lt_of_le_of_ne (norm_le_one F b) hb
  have := IsUltrametricDist.norm_add_le_max ((a : F) : Kbar p) ((b : F) : Kbar p)
  intro hab
  rw [Subalgebra.coe_add, IntermediateField.coe_add] at hab
  rw [hab] at this
  exact absurd this (not_le.mpr (max_lt ha' hb'))

end Model

section Model2

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] algZpF

theorem finite_OF : Module.Finite ℤ_[p] (OF F) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] F (OF F)

theorem noeth_OF : IsNoetherianRing (OF F) :=
  IsIntegralClosure.isNoetherianRing ℤ_[p] ℚ_[p] F (OF F)

theorem dedekind_OF : IsDedekindDomain (OF F) :=
  IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] F (OF F)

omit [FiniteDimensional ℚ_[p] F] in
theorem coe_natCast_F (n : ℕ) : ((n : F) : Kbar p) = n := map_natCast (algebraMap F (Kbar p)) n

theorem p_mem : ((p : ℕ) : F) ∈ OF F := by
  rw [mem_OF, coe_natCast_F, norm_p_kbar]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)

theorem not_isField_OF : ¬ IsField (OF F) := by
  intro h
  have hp0 : (⟨((p : ℕ) : F), p_mem F⟩ : OF F) ≠ 0 := by
    intro h0
    have := congrArg (fun x : OF F => ((x : F) : Kbar p)) h0
    simp only [ZeroMemClass.coe_zero] at this
    rw [coe_natCast_F] at this
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) this
  obtain ⟨b, hb⟩ := h.mul_inv_cancel hp0
  have hu : IsUnit (⟨((p : ℕ) : F), p_mem F⟩ : OF F) := IsUnit.of_mul_eq_one _ hb
  rw [isUnit_iff_norm] at hu
  change ‖(((p : ℕ) : F) : Kbar p)‖ = 1 at hu
  rw [coe_natCast_F, norm_p_kbar, inv_eq_one] at hu
  have : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

theorem dvr_OF : IsDiscreteValuationRing (OF F) := by
  haveI := isLocalRing_OF F
  haveI := noeth_OF F
  haveI := dedekind_OF F
  have h := (IsDiscreteValuationRing.TFAE (OF F) (not_isField_OF F)).out 1 3
  exact h.mpr (dedekind_OF F)

theorem torsionFree_OF : Module.IsTorsionFree ℤ_[p] (OF F) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap ℤ_[p] F) :=
    (algebraMap ℚ_[p] F).injective.comp (FaithfulSMul.algebraMap_injective ℤ_[p] ℚ_[p])
  intro a b h
  apply hinj
  have := congrArg (fun x : OF F => (x : F)) h
  exact this

variable {F}

/-- The uniformizer `ϖ` as an element of `𝓞_F`. -/
def unifB {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : OF F :=
  ⟨⟨ϖ, hϖ.1⟩, (mem_OF F _).mpr hϖ.2.1.le⟩

theorem coe_unifB {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : (((unifB hϖ : OF F) : F) : Kbar p) = ϖ := rfl

theorem norm_unif_pos {ϖ : Kbar p} (hϖ : IsUnif F ϖ) : 0 < ‖ϖ‖ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpF : (p : Kbar p) ∈ F := by
    rw [← map_natCast (algebraMap ℚ_[p] (Kbar p)) p]
    exact IntermediateField.algebraMap_mem _ _
  have hpn : ‖(p : Kbar p)‖ < 1 := by rw [norm_p_kbar]; exact inv_lt_one_of_one_lt₀ hp1
  have hp := hϖ.2.2 _ hpF hpn
  exact lt_of_lt_of_le (by rw [norm_p_kbar]; positivity) hp

theorem mem_span_pow_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (k : ℕ) (b : OF F) :
    b ∈ Ideal.span {unifB hϖ ^ k} ↔ ‖((b : F) : Kbar p)‖ ≤ ‖ϖ‖ ^ k := by
  have hϖ0 := norm_unif_pos hϖ
  have hϖne : ϖ ≠ 0 := norm_pos_iff.mp hϖ0
  rw [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    have : (((c * unifB hϖ ^ k : OF F) : F) : Kbar p) = ((c : F) : Kbar p) * ϖ ^ k := by
      rw [Subalgebra.coe_mul, Subalgebra.coe_pow, IntermediateField.coe_mul,
        IntermediateField.coe_pow, coe_unifB]
    rw [this, norm_mul, norm_pow]
    calc ‖((c : F) : Kbar p)‖ * ‖ϖ‖ ^ k ≤ 1 * ‖ϖ‖ ^ k :=
          mul_le_mul_of_nonneg_right (norm_le_one F c) (by positivity)
      _ = ‖ϖ‖ ^ k := one_mul _
  · intro h
    set ϖF : F := ⟨ϖ, hϖ.1⟩
    have hϖF : ϖF ≠ 0 := by
      intro h0
      exact hϖne (congrArg (fun x : F => (x : Kbar p)) h0)
    set c : F := (b : F) * (ϖF ^ k)⁻¹ with hc
    have hcn : ‖(c : Kbar p)‖ ≤ 1 := by
      rw [hc, IntermediateField.coe_mul, IntermediateField.coe_inv, IntermediateField.coe_pow,
        norm_mul, norm_inv, norm_pow]
      have : ‖((ϖF : F) : Kbar p)‖ = ‖ϖ‖ := rfl
      rw [this]
      rw [mul_inv_le_iff₀ (by positivity), one_mul]
      exact h
    refine ⟨⟨c, (mem_OF F c).mpr hcn⟩, ?_⟩
    apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow]
    change c * ϖF ^ k = (b : F)
    rw [hc, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hϖF), mul_one]

theorem maximalIdeal_eq {ϖ : Kbar p} (hϖ : IsUnif F ϖ) :
    haveI := isLocalRing_OF F
    maximalIdeal (OF F) = Ideal.span {unifB hϖ} := by
  haveI := isLocalRing_OF F
  ext b
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm, ← pow_one (unifB hϖ),
    mem_span_pow_iff, pow_one]
  constructor
  · intro h
    exact hϖ.2.2 _ (b : F).2 (lt_of_le_of_ne (norm_le_one F b) h)
  · intro h h1
    rw [h1] at h
    exact absurd hϖ.2.1 (not_lt.mpr h)

theorem mem_maximalIdeal_pow_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (k : ℕ) (b : OF F) :
    haveI := isLocalRing_OF F
    b ∈ maximalIdeal (OF F) ^ k ↔ ‖((b : F) : Kbar p)‖ ≤ ‖ϖ‖ ^ k := by
  haveI := isLocalRing_OF F
  rw [maximalIdeal_eq hϖ, Ideal.span_singleton_pow, mem_span_pow_iff]

end Model2

section Galois

attribute [local instance] algZpF FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (F : Fld p) [FiniteDimensional ℚ_[p] F]

attribute [local instance] torsionFree_OF

instance faithful_OF : FaithfulSMul ℤ_[p] (OF F) := by
  rw [faithfulSMul_iff_algebraMap_injective, ← Module.isTorsionFree_iff_algebraMap_injective]
  exact torsionFree_OF F

instance faithful_frac_OF : FaithfulSMul ℤ_[p] (FractionRing (OF F)) := inferInstance


instance isFractionRing_OF : IsFractionRing (OF F) F :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[p] F

theorem hcomp :
    (algebraMap (FractionRing ℤ_[p]) (FractionRing (OF F))).comp
        ((FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.toRingEquiv : ℚ_[p] →+* FractionRing ℤ_[p]) =
      ((FractionRing.algEquiv (OF F) F).symm.toRingEquiv : F →+* FractionRing (OF F)).comp
        (algebraMap ℚ_[p] F) := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
  ext z
  simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv]
  have h1 : (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm (algebraMap ℤ_[p] ℚ_[p] z) =
      algebraMap ℤ_[p] (FractionRing ℤ_[p]) z :=
    (FractionRing.algEquiv ℤ_[p] ℚ_[p]).symm.commutes z
  have h2 : algebraMap ℚ_[p] F (algebraMap ℤ_[p] ℚ_[p] z) =
      algebraMap (OF F) F (algebraMap ℤ_[p] (OF F) z) := rfl
  have h3 : (FractionRing.algEquiv (OF F) F).symm (algebraMap (OF F) F (algebraMap ℤ_[p] (OF F) z))
      = algebraMap (OF F) (FractionRing (OF F)) (algebraMap ℤ_[p] (OF F) z) :=
    (FractionRing.algEquiv (OF F) F).symm.commutes _
  rw [h1, h2, h3, ← IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p])
    (FractionRing (OF F)), IsScalarTower.algebraMap_apply ℤ_[p] (OF F) (FractionRing (OF F))]

theorem isGalois_frac [IsGalois ℚ_[p] F] :
    IsGalois (FractionRing ℤ_[p]) (FractionRing (OF F)) :=
  IsGalois.of_equiv_equiv (hcomp F)

theorem isSeparable_frac :
    Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing (OF F)) :=
  Algebra.IsSeparable.of_equiv_equiv _ _ (hcomp F)

end Galois

section Filtration

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

theorem coe_galRestrict (s : F ≃ₐ[ℚ_[p]] F) (b : OF F) :
    ((galRestrict ℤ_[p] ℚ_[p] F (OF F) s b : OF F) : F) = s (b : F) :=
  algebraMap_galRestrict_apply ℤ_[p] s b

theorem mem_lowerRam_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (i : ℕ) (s : F ≃ₐ[ℚ_[p]] F) :
    haveI := isLocalRing_OF F
    galRestrict ℤ_[p] ℚ_[p] F (OF F) s ∈ PkgI6.lowerRam ℤ_[p] (OF F) i ↔
      ∀ x : F, ‖(x : Kbar p)‖ ≤ 1 → ‖((s x : F) : Kbar p) - x‖ ≤ ‖ϖ‖ ^ (i + 1) := by
  haveI := isLocalRing_OF F
  rw [PkgI6.mem_lowerRam]
  constructor
  · intro h x hx
    have := (mem_maximalIdeal_pow_iff hϖ (i + 1) _).mp (h ⟨x, (mem_OF F x).mpr hx⟩)
    rw [Subalgebra.coe_sub, coe_galRestrict, AddSubgroupClass.coe_sub] at this
    exact this
  · intro h b
    rw [mem_maximalIdeal_pow_iff hϖ, Subalgebra.coe_sub, coe_galRestrict,
      AddSubgroupClass.coe_sub]
    exact h b (norm_le_one F b)

end Filtration

section Card

attribute [local instance] algZpF

variable {F : Fld p} [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

theorem mem_ramSet_iff {ϖ : Kbar p} (hϖ : IsUnif F ϖ) (i : ℕ) (σ : GQp p) :
    haveI := isLocalRing_OF F
    σ ∈ ramSet F i ↔ galRestrict ℤ_[p] ℚ_[p] F (OF F) (AlgEquiv.restrictNormalHom F σ) ∈
      PkgI6.lowerRam ℤ_[p] (OF F) i := by
  haveI := isLocalRing_OF F
  rw [mem_lowerRam_iff hϖ]
  constructor
  · rintro ⟨ϖ', hϖ', h⟩ x hx
    rw [AlgEquiv.restrictNormalHom_apply, ← IsUnif.norm_eq hϖ hϖ']
    exact h x x.2 hx
  · intro h
    refine ⟨ϖ, hϖ, fun x hx hx1 => ?_⟩
    have := h ⟨x, hx⟩ hx1
    rwa [AlgEquiv.restrictNormalHom_apply] at this

theorem card_lowerRam (i : ℕ) :
    haveI := isLocalRing_OF F
    Nat.card (PkgI6.lowerRam ℤ_[p] (OF F) i) = ramCard F i := by
  haveI := isLocalRing_OF F
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (inferInstance : FiniteDimensional ℚ_[p] F)
  set G := galRestrict ℤ_[p] ℚ_[p] F (OF F) with hG
  set K : Set (F ≃ₐ[ℚ_[p]] F) := {s | G s ∈ PkgI6.lowerRam ℤ_[p] (OF F) i} with hKdef
  have h1 : Nat.card (PkgI6.lowerRam ℤ_[p] (OF F) i) = Nat.card K :=
    (Nat.card_congr (G.toEquiv.subtypeEquiv (fun s => Iff.rfl))).symm
  have hK : K = AlgEquiv.restrictNormalHom F '' ramSet F i := by
    ext s
    constructor
    · intro hs
      obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (Kbar p) s
      exact ⟨σ, (mem_ramSet_iff hϖ i σ).mpr hs, rfl⟩
    · rintro ⟨σ, hσ, rfl⟩
      exact (mem_ramSet_iff hϖ i σ).mp hσ
  set φ : (F ≃ₐ[ℚ_[p]] F) → (F → Kbar p) := fun s x => ((s x : F) : Kbar p) with hφ
  have hφinj : Function.Injective φ := by
    intro s t h
    ext x
    exact congrFun h x
  have himg : restr F '' ramSet F i = φ '' (AlgEquiv.restrictNormalHom F '' ramSet F i) := by
    rw [Set.image_image]
    refine Set.image_congr fun σ _ => ?_
    funext x
    exact (AlgEquiv.restrictNormalHom_apply F σ x).symm
  unfold ramCard
  rw [himg, Nat.card_image_of_injective hφinj, ← hK, h1]

theorem fix_of_lowerRam_bot (i : ℕ) :
    haveI := isLocalRing_OF F
    PkgI6.lowerRam ℤ_[p] (OF F) i = ⊥ → ramSet F i ⊆ fixSet F := by
  haveI := isLocalRing_OF F
  intro hbot σ hσ
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (inferInstance : FiniteDimensional ℚ_[p] F)
  have h := (mem_ramSet_iff hϖ i σ).mp hσ
  rw [hbot, Subgroup.mem_bot, ← map_one (galRestrict ℤ_[p] ℚ_[p] F (OF F))] at h
  have h1 := (galRestrict ℤ_[p] ℚ_[p] F (OF F)).injective h
  intro x hx
  exact (AlgEquiv.restrictNormal_eq_one_iff F σ).mp h1 x hx

end Card

section FinalZp

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {p : ℕ} [Fact p.Prime]

/-- **`LadicDVRModelZp` (GLUE, proved).** `B = 𝓞_F = integralClosure ℤ_p F`: a DVR (local by the
ultrametric norm, Dedekind as an integral closure, `IsDiscreteValuationRing.TFAE`), finite and
torsion-free over `ℤ_p`, with `Frac(B) ≅ F` Galois over `Frac(ℤ_p) ≅ ℚ_p`
(`IsGalois.of_equiv_equiv`); `𝔪_B^k = {‖b‖ ≤ ‖ϖ‖^k}`, and `galRestrict` identifies
`PkgI6.lowerRam ℤ_p B i` with the restrictions of `ramSet F i`. -/
theorem ladicDVRModelZp : LadicDVRModelZp p := by
  intro F hF
  haveI : FiniteDimensional ℚ_[p] F := hF.1
  haveI : IsGalois ℚ_[p] F := hF.2
  letI := algZpF F
  haveI := torsionFree_OF F
  haveI := faithful_OF F
  haveI := dvr_OF F
  exact ⟨OF F, inferInstance, inferInstance, dvr_OF F, inferInstance, finite_OF F,
    torsionFree_OF F, isSeparable_frac F, isGalois_frac F, card_lowerRam, fix_of_lowerRam_bot⟩

end FinalZp

end DVRModelSec

/-! ## §3. The reduction (proved) -/

section Reduction

theorem gl_eq_one_of_scalar {ℓ : ℕ} [Fact ℓ.Prime] {g : GL (Fin 2) (PadicAlgCl ℓ)}
    {c : PadicAlgCl ℓ} (h : (g : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = Matrix.scalar (Fin 2) c)
    (hc : c = 1) : g = 1 := by
  apply Units.ext
  rw [h, hc, map_one, Units.val_one]

/-- **`LocalRamG` from the local pieces (GLUE, proved).** -/
theorem localRamG_of {ℓ : ℕ} [Fact ℓ.Prime] (u : ℚ) (p : ℕ) [Fact p.Prime] (hpℓ : p ≠ ℓ)
    (r : GaloisRep ℓ 2) (hUB : UpperBreakFix p) (hUW : UpperWild p) (hWT : WildFixTame p)
    (hd : LocalData p r) (h11 : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) r) :
    LocalRamG u p r := by
  refine ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_, fun hS hM => ?_⟩
  · obtain ⟨F, β, hF, he, hsh, hup⟩ := hd.1 hpD
    have ha : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
      Nat.mul_pos GlueDescent.heightD_pos (by unfold ZInQ.heightG0; norm_num)
    have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
    have hfix : σ ∈ fixSet F := hUB F hF _ ha he t (by unfold U0 at ht; exact ht) hσ
    have hwild : σ ∈ wildSet := hUW t (by linarith) hσ
    exact gl_eq_one_of_scalar (hsh σ ⟨hfix, hwild⟩) (hup t ht σ ⟨hσ, hfix⟩)
  · obtain ⟨F, β, hF, he, hsh, htame⟩ := hd.2 hpD
    have hfix := hWT F hF he hσ
    exact gl_eq_one_of_scalar (hsh σ ⟨hfix, hσ⟩) (htame σ ⟨hfix, hσ⟩)
  · refine h11 p (Fact.out) ?_ hpℓ
    intro hT
    rcases Finset.mem_union.mp hT with h | h
    · exact hS h
    · exact hM (Nat.mem_primeFactors.mp h).2.1

/-- **`G15RamG` from smaller named Props (GLUE, proved).** Closed local-field Props
(`UpperBreakFix`, `UpperWild`, `WildFixTame`), the local data of G8/G7 on `D` (`LocalData`), and
G11's output on `D` for `T = S_mul ∪ supp M_{S_mul}(u)` (`GlueDescent.ramSet`). -/
theorem g15RamG_of_pieces
    (hUB : ∀ (p : ℕ) [Fact p.Prime], UpperBreakFix p)
    (hUW : ∀ (p : ℕ) [Fact p.Prime], UpperWild p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u := by
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨fun h5' => localRamG_of u p h5' D.r5 (hUB p) (hUW p) (hWT p) (h5 p hp h5') h11₅,
    fun h5' => ?_⟩
  subst h5'
  exact localRamG_of u 5 (by norm_num) D.r3 (hUB 5) (hUW 5) (hWT 5) h3 h11₃

/-- **`G15RamG`, with D1 discharged (GLUE, proved).** As `g15RamG_of_pieces`, with
`UpperBreakFix` replaced by the transport `HilbertSerreLadic` of T20 + T21. -/
theorem g15RamG_of_hilbertSerre
    (hHS : ∀ (p : ℕ) [Fact p.Prime], HilbertSerreLadic p)
    (hUW : ∀ (p : ℕ) [Fact p.Prime], UpperWild p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_pieces (fun p _ => upperBreakFix_of_hilbertSerre (hHS p)) hUW hWT D u h5 h3
    h11₅ h11₃

/-- **`G15RamG` from the DVR model, T20-T21 (proved in the kernel), `WildFixTame` and the data
of G7-G8-G11 on `D` (GLUE, proved).** `UpperWild` is proved (`upperWild`). -/
theorem g15RamG_of_model
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModel p)
    (hWT : ∀ (p : ℕ) [Fact p.Prime], WildFixTame p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_hilbertSerre (fun p _ => hilbertSerre_of_model (hM p)) (fun p _ => upperWild) hWT
    D u h5 h3 h11₅ h11₃

/-- **`G15RamG` with all closed local-field glue proved except the DVR model (GLUE, proved).**
Hypotheses: the transport `LadicDVRModel`, the data of G7-G8 on `D` (`LocalData`), and G11's
output on `D`. -/
theorem g15RamG_of_dvrModel
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModel p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_model hM (fun p _ => wildFixTame) D u h5 h3 h11₅ h11₃

/-- **`G15RamG` from the `ℤ_p`-model of finite Galois `F ⊆ ℚ̄_p` (GLUE, proved).** -/
theorem g15RamG_of_zpModel
    (hM : ∀ (p : ℕ) [Fact p.Prime], LadicDVRModelZp p)
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_dvrModel (fun p _ => ladicDVRModel_of_Zp (hM p)) D u h5 h3 h11₅ h11₃

/-- The trivial two-dimensional representation (for the non-vacuity check below). -/
def trivRep (ℓ : ℕ) [Fact ℓ.Prime] : GaloisRep ℓ 2 := ⟨1, continuous_const⟩

/-- **Non-vacuity check (proved).** `LocalData p r` holds for the trivial representation (with
`F = ℚ_p`, `β = 1`), so the hypotheses on `D` are not contradictory. -/
theorem localData_trivRep (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] :
    LocalData p (trivRep ℓ) := by
  have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
  have hshape : TwistShape p (trivRep ℓ) ⊥ (fun _ => 1) := by
    intro σ _
    simp [trivRep, PkgI4.GaloisRep.restrictLocal]
  have he : ramCard (⊥ : Fld p) 0 = 1 := by
    have h1 := one_le_ramCard hF 0
    have h2 : ramCard (⊥ : Fld p) 0 ≤ 1 := by
      unfold ramCard
      have hfin := (finite_restr hF (ramSet (⊥ : Fld p) 0)).to_subtype
      refine Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => ?_⟩
      apply Subtype.ext
      obtain ⟨σ, -, hσ⟩ := a.2
      obtain ⟨τ, -, hτ⟩ := b.2
      rw [← hσ, ← hτ]
      funext x
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
      simp only [restr, ← hq, AlgEquiv.commutes]
    omega
  refine ⟨fun _ => ⟨⊥, fun _ => 1, hF, ?_, hshape, fun _ _ _ _ => rfl⟩,
    fun _ => ⟨⊥, fun _ => 1, hF, ?_, hshape, fun _ _ => rfl⟩⟩
  · rw [he]; exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  · rw [he]; exact (Nat.Prime.one_lt Fact.out).ne' ∘ Nat.dvd_one.mp

/-- **`G15RamG` from the data of G7-G8 on `D` and G11's output alone (GLUE, proved).** Every
closed local-field input is proved: `UpperBreakFix` (from T20, T21 and `ladicDVRModelZp`),
`UpperWild`, `WildFixTame`. -/
theorem g15RamG_of_localData
    {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalData p ⟨hp⟩ 5 _ D.r5)
    (h3 : LocalData 5 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_zpModel (fun _ _ => ladicDVRModelZp) D u h5 h3 h11₅ h11₃

end Reduction

end G15Ram

/-! ## §3' (local-data). Verbatim copies from scratch/g0-mod-galois/part_galois.lean -/

section G0GaloisSec

noncomputable section

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ### Objects -/

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). Its image is `G_K` inside `G_ℚ` for the
embedding `K ↪ ℚ̄` that the map chooses. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- `e` intertwines the operators `f g` on `V` with `r(g) ⊕ r(g)` on `ℚ̄_ℓ² × ℚ̄_ℓ²`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

/-- **Output of G7 (scalar descent, N5 L632-716) at the coefficient prime `ℓ`**, together with
the outputs of G4-G6 that G8 uses. `A` is the model over `K = L'` (an abelian surface with
`End_K(A)` of rank 4, the maximal order case of `End⁰ = B`: A9's output). The data are:
operators `Tm σ = μ_σ ∘ σ` on `ℚ̄_ℓ ⊗ V_ℓ(A)` (without `a_σ`: `GlueDescent.rho` multiplies by
`β_σ⁻¹ a_σ`, giving N5's `ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ ∘ σ`) with the cocycle `c` (`Tm g Tm h = c(g,h) Tm(gh)`),
the scalars `a` and the cochain `β` with `a_g a_h c(g,h) = ε(g,h) a_{gh}` and
`β_g β_h = ε(g,h) β_{gh}` (`∂β = ε`, B2-B3), all trivial on `G_{L'}` where `Tm` is the Tate
action (`L'` contains the kernel field of `β|G_L`; it is taken finite Galois over `ℚ`, as
g0-mod-field's `G7Data` supplies, which `G10Glue` needs); a system of `2 × 2` matrix units (the image of
`B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`) commuting with every `Tm σ` (`μ_σ` is `B`-linear); and continuity of
`σ ↦ β_σ⁻¹ a_σ Tm σ` (glue-rho-cont proved continuity on `G_K`; finite index gives the rest). -/
def G7Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) : Prop :=
  A.dim = 2 ∧ Module.finrank ℤ (PkgI3.AbVar.End A) = 4 ∧
  (∀ g h, Tm g * Tm h = c g h • Tm (g * h)) ∧
  (∀ g h, a g * a h * c g h = ε g h * a (g * h)) ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧
  (∀ σ, Tm (resQ K σ) = tate A ℓ σ ∧ a (resQ K σ) = 1 ∧ β (resQ K σ) = 1) ∧
  (∀ g i j, Commute (Tm g) (u.e i j)) ∧
  (∀ (f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ)) (v : Vb A ℓ),
    Continuous fun g => f (GlueDescent.rho Tm a β g v))

/-- **Output of G8.** `r : G_ℚ → GL₂(ℚ̄_ℓ)` (continuous) and `e : ℚ̄_ℓ ⊗ V_ℓ(A) ≅ ℚ̄_ℓ² × ℚ̄_ℓ²`
with: (i) `e` intertwines the descended representation `ρ` (an operator family on
`ℚ̄_ℓ ⊗ V_ℓ(A)`, in the theorem `GlueDescent.rho Tm a β`) with `r ⊕ r` on all of `G_ℚ`;
(ii) `ρ` is the Tate action on `G_{L'}`; (iii) `r|G_{L'}` is absolutely irreducible, in
Burnside's form (the matrices `r(σ)`, `σ ∈ G_{L'}`, generate `M₂(ℚ̄_ℓ)`). -/
def G8Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ)) (r : GaloisRep ℓ 2) : Prop :=
  (∀ σ, ρ (resQ K σ) = tate A ℓ σ) ∧
  ∃ e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ),
    Intertwines ρ r.mat e ∧
    Algebra.adjoin (PadicAlgCl ℓ) (Set.range fun σ => r.mat (resQ K σ)) = ⊤

end G0Galois

end

end G0GaloisSec

/-! ## §4 (local-data). `LocalData p r` on G8's `r`, from G7's data

The copied `LocalData p r` (§1) is a predicate on a bare `r : GaloisRep ℓ 2`. Here:

* `largePrimeData_iff`, `localData_large_iff` (proved): for `p > D`, `LocalData p r ↔ r` is
  trivial on wild inertia. So `LocalData` fails for any `r` wildly ramified at some `p > D`
  (e.g. `ψ ⊕ 1`, `ψ` a Dirichlet character of conductor `p²`), and cannot be proved for
  arbitrary `r`: it is a claim about the `r` that G8 builds.
* **Main result** `localData_of_g7` (proved): for `r` as in G8's output (`G0Galois.G8Out`) on
  `ρ = GlueDescent.rho Tm a β`, `LocalData p r` follows, at every prime `p`, from
  `G7Clauses β ε L` (clauses of G4/G7) and `LocalGlue p Tm a β L` (the Tate-module glue
  `TorsionFieldWild` at `p ≤ D`, `TateWildTrivialL` at `p > D`, and `BetaUpper` at `p = 2`).
  `g15RamG_of_g7` composes it with g15-ram's `g15RamG_of_localData`.
* On the way (all proved): `twistShape_of_g8` (`r` is scalar where `ρ` is), `betaTame_of_odd`,
  `betaOpen_of_isLocallyConstant`, `wild_fix_root` (wild inertia fixes `μ_n`, `p² ∤ n`),
  `galChar_decomp_wild`, `betaSqWild_of_chi`, `betaCharOn_of_cocycle`, `wild_fix_small_degree`
  (wild inertia fixes every `E` with `[E:ℚ_p] < p`), `exists_finGal_ramCard_le` (Galois closure
  with `e ≤ [E:ℚ_p]!`), `exists_local_field_le` (`[L_v:ℚ_p] ≤ [L:ℚ]`).
-/

namespace G15Ram

open PkgI4 (GQp GaloisRep GQ decomp)
open LadicCond G0ModNewform

section LocalDataSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### The characterization at `p > D` -/

/-- At `p > D` the local data say exactly that `r` is trivial on wild inertia: `F` is tame, so
`P_p ⊆ G_F` (`wildFixTame`), and `r = β = 1` on `G_F ∩ P_p`. Conversely take `F = ℚ_p`. -/
theorem largePrimeData_iff (r : GaloisRep ℓ 2) :
    LargePrimeData p r ↔ ∀ σ ∈ wildSet, r.restrictLocal p σ = 1 := by
  constructor
  · rintro ⟨F, β, hF, hpe, hsh, htm⟩ σ hσ
    have hfix : σ ∈ fixSet F := wildFixTame F hF hpe hσ
    have h1 := hsh σ ⟨hfix, hσ⟩
    rw [htm σ ⟨hfix, hσ⟩, Matrix.scalar_apply, Matrix.diagonal_one] at h1
    exact Units.ext h1
  · intro h
    have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
    have hcard : ramCard (⊥ : Fld p) 0 = 1 := by
      have h1 := one_le_ramCard hF 0
      have h2 : ramCard (⊥ : Fld p) 0 ≤ 1 := by
        unfold ramCard
        have hfin := (finite_restr hF (ramSet (⊥ : Fld p) 0)).to_subtype
        refine Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => ?_⟩
        apply Subtype.ext
        obtain ⟨σ, -, hσ⟩ := a.2
        obtain ⟨τ, -, hτ⟩ := b.2
        rw [← hσ, ← hτ]
        funext x
        obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp x.2
        simp only [restr, ← hq, AlgEquiv.commutes]
      omega
    refine ⟨⊥, fun _ => 1, hF, ?_, ?_, fun _ _ => rfl⟩
    · rw [hcard]; exact (Fact.out : p.Prime).not_dvd_one
    · intro σ hσ
      rw [h σ hσ.2, Matrix.scalar_apply, Matrix.diagonal_one]
      rfl

/-- **`LocalData` at `p > D`, characterized (proved).** -/
theorem localData_large_iff (r : GaloisRep ℓ 2) (hp : (ZInQ.heightD : ℝ) < p) :
    LocalData p r ↔ ∀ σ ∈ wildSet, r.restrictLocal p σ = 1 := by
  rw [← largePrimeData_iff]
  constructor
  · exact fun h => h.2 hp
  · exact fun h => ⟨fun hle => absurd hp (not_lt.mpr hle), fun _ => h⟩

/-! ### From `ρ` to `r` (linear algebra) -/

/-- If `e` intertwines `ρ` with `m ⊕ m` and `ρ(g)` is the scalar `c`, then `m(g)` is the scalar
`c`. -/
theorem mat_eq_scalar_of_intertwines {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {f : G → Module.End (PadicAlgCl ℓ) V} {m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)}
    {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines f m e) {g : G} {c : PadicAlgCl ℓ} (hg : f g = c • 1) :
    m g = Matrix.scalar (Fin 2) c := by
  have hv : ∀ x : Fin 2 → PadicAlgCl ℓ, (m g).mulVec x = c • x := by
    intro x
    have := h g (e.symm (x, x))
    rw [hg, LinearMap.smul_apply, Module.End.one_apply, map_smul,
      LinearEquiv.apply_symm_apply] at this
    exact (congrArg Prod.fst this).symm
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hv x, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

/-! ### The smaller Props on G7's data at `p` -/

/-- **Glue on G4/G7 + R6 + D2 (N5 L719-727, L819-823; at `p > D` G3 + Néron–Ogg–Shafarevich,
N5 L848-851).** On `G_F ∩ P_p` (pushed to `G_ℚ` by `decomp`) the twisted Tate action
`a_σ μ_σ ∘ σ` (`a σ • Tm σ`) is the identity. Glazer: for `σ ∈ G_L` (`F ⊇ L_v`) the descent
datum has `a_σ μ_σ = 1`, so `a_σ Tm σ` is the Tate action of `A/L`; `A` is semistable over
`F ⊇ L_v(A[3])` (`A[5]` if `p = 3`) by Raynaud's criterion (R6, `PkgI2.RaynaudCriterion`), and
then wild inertia acts trivially on `V_ℓ` (D2, `PkgI2.D2_fixed_of_raynaud`); at `p > D`, `A` has
good reduction (G3) and inertia acts trivially (`PkgI2.inertiaTrivial_of_goodReduction`).
Only claimed for `p ≠ ℓ` (D2 and Néron–Ogg–Shafarevich are about `V_ℓ`, `ℓ ≠ p`; at `p = ℓ` it is
false in general); `g15RamG_of_g8` uses it only at `p ≠ ℓ`. -/
def TateWildTrivial {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, a (decomp p σ) • Tm (decomp p σ) = 1

/-- **Glue on G7's `β` (D3 + T16; N5 L823-844).** `β` is trivial on `G_{ℚ_p}^t ∩ G_F` for
`t > U`. At odd `p` it follows from `BetaTame` (`betaUpper_of_betaTame`); at `p = 2` from local
reciprocity with the upper numbering theorem (T16, `PkgI6.LocalReciprocityUpper`) and
`(U_F^{e+1})⁴ = U_F^{3e+1}` (D3, `GlueConductor.fourth_pow_mem`) applied to the character
`β|_{G_F}`, `ψ ≥ id`, and `max(4D², 3e) ≤ U₀` (`GlueConductor.max_le_U0`). -/
def BetaUpper (β : GQ → PadicAlgCl ℓ) (F : Fld p) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, β (decomp p σ) = 1

/-- **Glue on G7's `β` at odd `p` (N5 L835-838, L848-851).** `β` is trivial on `G_F ∩ P_p`.
Proved for odd `p` from `BetaCharOn`, `BetaSqWild`, `BetaOpen` (`betaTame_of_odd`). -/
def BetaTame (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β (decomp p σ) = 1

/-- **Glue on G7 (`∂β = ε` with `ε` inflated from `Gal(L/ℚ)` and normalized; N5 L664-700).**
On `G_F` (`F ⊇ L_v`, so `decomp(G_F) ⊆ G_L`) the cochain `β` is a character. -/
def BetaCharOn (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, β (decomp p (σ * τ)) = β (decomp p σ) * β (decomp p τ)

/-- **Glue on G7 (`β² = χ`, `χ` a Dirichlet character of level `N = ∏ lev q`, `lev p = p` for
odd `p`, so `χ` is tame at odd `p`; N5 L677-683; g0-mod-field `G7Data`).** `β² = 1` on
`G_F ∩ P_p`. -/
def BetaSqWild (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β (decomp p σ) ^ 2 = 1

/-- **Glue (local constancy of `β`, g0-mod-field `G7Data`: `IsLocallyConstant β`, and the
continuity of `decomp`).** `β ∘ decomp` is trivial on `G_{F'}` for some finite Galois `F'`. -/
def BetaOpen (β : GQ → PadicAlgCl ℓ) : Prop :=
  ∃ F' : Fld p, IsFinGal F' ∧ ∀ σ ∈ fixSet F', β (decomp p σ) = 1

/-! ### The reduction -/

/-- **`TwistShape` from G8's output (proved).** With `ρ = β⁻¹ a Tm` and `a Tm = 1` on
`G_F ∩ P_p`, `ρ = β⁻¹` there, and `r` is the same scalar (`e` intertwines `ρ` with `r ⊕ r`). -/
theorem twistShape_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r) {F : Fld p}
    (hT : TateWildTrivial Tm a F) :
    TwistShape p r F (fun σ => (β (decomp p σ))⁻¹) := by
  obtain ⟨-, e, he, -⟩ := hG8
  intro σ hσ
  have hρ : GlueDescent.rho Tm a β (decomp p σ) = (β (decomp p σ))⁻¹ • 1 := by
    unfold GlueDescent.rho
    rw [mul_smul, hT σ hσ]
  exact mat_eq_scalar_of_intertwines he hρ

theorem twistUpper_of_betaUpper {β : GQ → PadicAlgCl ℓ} {F : Fld p} {U : ℝ}
    (h : BetaUpper β F U) : TwistUpper p F (fun σ => (β (decomp p σ))⁻¹) U := by
  intro t ht σ hσ
  simp only [h t ht σ hσ, inv_one]

theorem twistTame_of_betaTame {β : GQ → PadicAlgCl ℓ} {F : Fld p}
    (h : BetaTame β F) : TwistTame p F (fun σ => (β (decomp p σ))⁻¹) := by
  intro σ hσ
  simp only [h σ hσ, inv_one]

/-- **`BetaUpper` from `BetaTame` (proved):** `G_{ℚ_p}^t ⊆ P_p` for `t > 0` (`upperWild`). -/
theorem betaUpper_of_betaTame {β : GQ → PadicAlgCl ℓ} {F : Fld p} {U : ℝ} (hU : 0 ≤ U)
    (h : BetaTame β F) : BetaUpper β F U := by
  intro t ht σ hσ
  exact h σ ⟨hσ.2, upperWild t (lt_of_le_of_lt hU ht) hσ.1⟩

/-- **Corrected form of `LocalData p r`: the local data of G7 at `p` (GLUE on G4/G7 + R6 + D2 +
D3 + T16; N5 L813-851).** A Prop on G7's data `(Tm, a, β)` instead of on the bare `r`: at
`p ≤ D` a finite Galois `F ⊆ ℚ̄_p` with `e(F/ℚ_p) ≤ (DG₀)!` (Glazer: the Galois closure of
`L_v(A[3])`, `A[5]` if `p = 3`, of degree `≤ (DG₀)!`) on which `TateWildTrivial` and
`BetaUpper` (bound `U₀`) hold; at `p > D` a tame finite Galois `F` (the Galois closure of `L_v`,
`[L_v:ℚ_p] ≤ D < p`) with `TateWildTrivial` and `BetaTame`. -/
def G7LocalData {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ F : Fld p, IsFinGal F ∧
      ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
      TateWildTrivial Tm a F ∧ BetaUpper β F U0) ∧
    ((ZInQ.heightD : ℝ) < p → ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
      TateWildTrivial Tm a F ∧ BetaTame β F)

/-- **`LocalData p r` for G8's `r` (proved).** For `r` as in G8's output on
`ρ = GlueDescent.rho Tm a β`, `G7LocalData p Tm a β` gives `LocalData p r`, with the local
twist `σ ↦ β(σ)⁻¹`. -/
theorem localData_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (h : G7LocalData (p := p) Tm a β) : LocalData p r := by
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨F, hF, he, hT, hB⟩ := h.1 hp
    exact ⟨F, _, hF, he, twistShape_of_g8 hG8 hT, twistUpper_of_betaUpper hB⟩
  · obtain ⟨F, hF, he, hT, hB⟩ := h.2 hp
    exact ⟨F, _, hF, he, twistShape_of_g8 hG8 hT, twistTame_of_betaTame hB⟩

/-- **`G15RamG D u` from G8's outputs for `D.r5`, `D.r3` and G7's local data (proved).**
Composes `localData_of_g8` with g15-ram's `g15RamG_of_localData`. The G7/G8 data for `r₅` and
`r₃` may live on different models (`K₅`, `A₅`) and (`K₃`, `A₃`). -/
theorem g15RamG_of_g8 {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : ModData L A) (u : ℚ)
    {K₅ : Type} [Field K₅] [NumberField K₅] {A₅ : PkgI3.AbVar K₅}
    {Tm₅ : GQ → Module.End (PadicAlgCl 5) (G0Galois.Vb A₅ 5)} {a₅ β₅ : GQ → PadicAlgCl 5}
    (hG8₅ : G0Galois.G8Out A₅ 5 (GlueDescent.rho Tm₅ a₅ β₅) D.r5)
    {K₃ : Type} [Field K₃] [NumberField K₃] {A₃ : PkgI3.AbVar K₃}
    {Tm₃ : GQ → Module.End (PadicAlgCl 3) (G0Galois.Vb A₃ 3)} {a₃ β₃ : GQ → PadicAlgCl 3}
    (hG8₃ : G0Galois.G8Out A₃ 3 (GlueDescent.rho Tm₃ a₃ β₃) D.r3)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G7LocalData p ⟨hp⟩ 5 _ _ _ _ Tm₅ a₅ β₅)
    (h3 : G7LocalData (p := 5) Tm₃ a₃ β₃)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_localData D u (fun p hp hp5 => @localData_of_g8 p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ hG8₅
    (h5 p hp hp5)) (localData_of_g8 hG8₃ h3) h11₅ h11₃

/-! ### `BetaTame` at odd `p` (proved) -/

/-- A wild `σ` has `σ^{p^a}` fixing a given finite Galois `F'` for some `a`: the restriction
`s ∈ Gal(F'/ℚ_p)` has order `p^a m` with `p ∤ m`, and the wild `σ^{p^a}` has restriction of
order `m` prime to `p`, so it fixes `F'` (`fix_of_wild_pow`). -/
theorem exists_pow_fix_of_wild {σ : GQp p} (hσ : σ ∈ wildSet) {F' : Fld p} (hF' : IsFinGal F') :
    ∃ a : ℕ, σ ^ (p ^ a) ∈ fixSet F' := by
  haveI : FiniteDimensional ℚ_[p] F' := hF'.1
  haveI : Normal ℚ_[p] F' := hF'.2.to_normal
  set s := AlgEquiv.restrictNormalHom F' σ with hs
  have hm0 : 0 < orderOf s := orderOf_pos s
  obtain ⟨a, m, hpm, hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0.ne' p
    (Fact.out : p.Prime).ne_one
  refine ⟨a, ?_⟩
  have hm0' : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hdec; omega
  intro x hx
  have hsm : AlgEquiv.restrictNormalHom F' ((σ ^ (p ^ a)) ^ m) = 1 := by
    rw [map_pow, map_pow, ← hs, ← pow_mul, ← hdec, pow_orderOf_eq_one]
  have hfix : ((σ ^ (p ^ a)) ^ m) x = x :=
    (AlgEquiv.restrictNormal_eq_one_iff F' _).mp hsm x hx
  exact fix_of_wild_pow (wildSet_pow hσ _) hm0' hpm hfix

theorem fixSet_pow {F : Fld p} {σ : GQp p} (hσ : σ ∈ fixSet F) (k : ℕ) : σ ^ k ∈ fixSet F := by
  induction k with
  | zero => intro x _; rfl
  | succ k ih =>
    intro x hx
    rw [pow_succ, AlgEquiv.mul_apply, hσ x hx, ih x hx]

/-- **`BetaTame` at odd `p` (proved).** If `β` is a character on `G_F`, `β² = 1` on
`G_F ∩ P_p`, and `β ∘ decomp` dies on an open `G_{F'}`, then `β = 1` on `G_F ∩ P_p` for odd `p`:
`β(σ)^{p^a} = β(σ^{p^a}) = 1` with `σ^{p^a} ∈ G_{F'}`, and `β(σ)² = 1`, `gcd(p^a, 2) = 1`. -/
theorem betaTame_of_odd (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {F : Fld p}
    (hmul : BetaCharOn β F) (hsq : BetaSqWild β F) (hopen : BetaOpen (p := p) β) :
    BetaTame β F := by
  obtain ⟨F', hF', h1⟩ := hopen
  intro σ hσ
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ.2 hF'
  have hpow : ∀ k : ℕ, β (decomp p (σ ^ (k + 1))) = β (decomp p σ) ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ σ (k + 1), hmul _ (fixSet_pow hσ.1 _) _ hσ.1, ih, ← pow_succ]
  have hpa : β (decomp p σ) ^ (p ^ a) = 1 := by
    have hpos : 0 < p ^ a := pow_pos (Fact.out : p.Prime).pos a
    obtain ⟨k, hk⟩ : ∃ k, p ^ a = k + 1 := ⟨p ^ a - 1, by omega⟩
    rw [hk, ← hpow k, ← hk]
    exact h1 _ ha
  have hcop : Nat.Coprime (p ^ a) 2 := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp2
  have := pow_gcd_eq_one.mpr ⟨hpa, hsq σ hσ⟩
  rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this

/-- `β(1) = 1` for a nonzero `β` that is a character on `G_F`. -/
theorem beta_one_of_charOn {β : GQ → PadicAlgCl ℓ} {F : Fld p} (hm : BetaCharOn β F)
    (h0 : β 1 ≠ 0) : β 1 = 1 := by
  have h := hm 1 (fun _ _ => rfl) 1 (fun _ _ => rfl)
  rw [mul_one, map_one] at h
  have h' : β 1 * β 1 = β 1 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel₀ h0 h'

/-- **`BetaOpen` from local constancy (proved).** If `β : G_ℚ → ℚ̄_ℓ` is locally constant
(g0-mod-field's `G7Data` has `IsLocallyConstant β` for the `ℂ^×`-valued `β`; any transport of
the values preserves it) and `β(1) = 1`, then `β ∘ decomp` is trivial on `G_{F'}` for a finite
Galois `F'`: `decomp` is continuous (Mathlib's `Field.absoluteGaloisGroup.map`), the fibre over
`1` is an open neighbourhood of `1`, so it contains the fixer of a finite `E`
(`krullTopology_mem_nhds_one_iff`), and of its normal closure `F'`. -/
theorem betaOpen_of_isLocallyConstant {β : GQ → PadicAlgCl ℓ} (hβ : IsLocallyConstant β)
    (h1 : β 1 = 1) : BetaOpen (p := p) β := by
  set S : Set (GQp p) := {σ | β (decomp p σ) = 1} with hSdef
  have hcont : Continuous (decomp p) :=
    (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous
  have hS : S ∈ nhds (1 : GQp p) := by
    have hopen : IsOpen S := (hβ.comp_continuous hcont).isOpen_fiber 1
    refine hopen.mem_nhds ?_
    show β (decomp p 1) = 1
    rw [map_one, h1]
  obtain ⟨E, hEfin, hE⟩ := (krullTopology_mem_nhds_one_iff ℚ_[p] (Kbar p) S).mp hS
  set F' := IntermediateField.normalClosure ℚ_[p] E (Kbar p) with hF'
  haveI : FiniteDimensional ℚ_[p] F' := normalClosure.is_finiteDimensional ℚ_[p] E (Kbar p)
  haveI : Normal ℚ_[p] F' := normalClosure.normal ℚ_[p] E (Kbar p)
  refine ⟨F', ⟨inferInstance, IsGalois.mk⟩, fun σ hσ => ?_⟩
  have hσE : σ ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hσ x (E.le_normalClosure hx)
  exact hE hσE

/-- **Corrected form at odd `p` (GLUE).** `G7LocalData` with the `β`-side replaced by
`BetaCharOn` and `BetaSqWild` on the same `F` (local constancy and `β(1) ≠ 0` are separate
hypotheses of `g7LocalData_of_odd`). -/
def G7LocalDataOdd {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ F : Fld p, IsFinGal F ∧
      ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
      TateWildTrivial Tm a F ∧ BetaCharOn β F ∧ BetaSqWild β F) ∧
    ((ZInQ.heightD : ℝ) < p → ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧
      TateWildTrivial Tm a F ∧ BetaCharOn β F ∧ BetaSqWild β F)

/-- **`G7LocalData` at odd `p` (proved)** from `G7LocalDataOdd`, local constancy of `β` and
`β(1) ≠ 0` (`G0Galois.G7Out` has `∀ g, β g ≠ 0`). -/
theorem g7LocalData_of_odd (hp2 : p ≠ 2) {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a β : GQ → PadicAlgCl ℓ}
    (hβ : IsLocallyConstant β) (h0 : β 1 ≠ 0) (h : G7LocalDataOdd (p := p) Tm a β) :
    G7LocalData (p := p) Tm a β := by
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨F, hF, he, hT, hm, hs⟩ := h.1 hp
    have hopen := betaOpen_of_isLocallyConstant (p := p) hβ (beta_one_of_charOn hm h0)
    exact ⟨F, hF, he, hT, betaUpper_of_betaTame hU0 (betaTame_of_odd hp2 hm hs hopen)⟩
  · obtain ⟨F, hF, he, hT, hm, hs⟩ := h.2 hp
    have hopen := betaOpen_of_isLocallyConstant (p := p) hβ (beta_one_of_charOn hm h0)
    exact ⟨F, hF, he, hT, betaTame_of_odd hp2 hm hs hopen⟩

/-! ### `BetaSqWild` at odd `p` from `β² = χ` (proved)

Wild inertia fixes every root of unity of order `n` with `p² ∤ n` (`wild_fix_root`, norms only);
so the cyclotomic character mod `N`, and every Dirichlet character mod `N`, is trivial on
`decomp(P_p)` when `p² ∤ N` (`galChar_decomp_wild`); and `p² ∤ chiLevel T₋` for odd `p`
(`not_sq_dvd_chiLevel`). -/

theorem norm_eq_one_of_pow_eq_one {η : Kbar p} {n : ℕ} (hn : 0 < n) (h : η ^ n = 1) :
    ‖η‖ = 1 := by
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp this

theorem norm_sum_range_le_one {f : ℕ → Kbar p} (m : ℕ) (hf : ∀ k < m, ‖f k‖ ≤ 1) :
    ‖∑ k ∈ Finset.range m, f k‖ ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _)
      (max_le (ih fun k hk => hf k (by omega)) (hf m (by omega)))

theorem norm_pow_sub_one_le {η : Kbar p} (h1 : ‖η‖ = 1) (i : ℕ) : ‖η ^ i - 1‖ ≤ ‖η - 1‖ := by
  have he : η ^ i - 1 = (∑ k ∈ Finset.range i, η ^ k) * (η - 1) := (geom_sum_mul η i).symm
  rw [he, norm_mul]
  have hs : ‖∑ k ∈ Finset.range i, η ^ k‖ ≤ 1 :=
    norm_sum_range_le_one i fun k _ => by rw [norm_pow, h1, one_pow]
  calc ‖∑ k ∈ Finset.range i, η ^ k‖ * ‖η - 1‖ ≤ 1 * ‖η - 1‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ = ‖η - 1‖ := one_mul _

/-- A root of unity of order prime to `p` congruent to `1` is `1`. -/
theorem eq_one_of_pow_eq_one_of_norm_lt {η : Kbar p} {m : ℕ} (hm0 : 0 < m) (hpm : ¬ p ∣ m)
    (hη : η ^ m = 1) (hlt : ‖η - 1‖ < 1) : η = 1 := by
  by_contra hne
  have h1 : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one hm0 hη
  have hsub : η - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hgeom : ∑ k ∈ Finset.range m, η ^ k = 0 := by
    have := geom_sum_mul η m
    rw [hη, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right hsub
  have hm : (m : Kbar p) = ∑ k ∈ Finset.range m, (1 - η ^ k) := by
    rw [Finset.sum_sub_distrib, hgeom, sub_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
  have hlt' : ‖∑ k ∈ Finset.range m, (1 - η ^ k)‖ < 1 :=
    norm_sum_range_lt one_pos m fun k _ => by
      rw [norm_sub_rev]; exact lt_of_le_of_lt (norm_pow_sub_one_le h1 k) hlt
  rw [← hm, norm_natCast_kbar hpm] at hlt'
  exact lt_irrefl _ hlt'

/-- Wild inertia fixes roots of unity of order prime to `p`. -/
theorem wild_fix_prime_to_p {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} {m : ℕ} (hm0 : 0 < m)
    (hpm : ¬ p ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0.ne'] at hζ; exact zero_ne_one hζ
  set η := σ ζ * ζ⁻¹ with hη
  have hηm : η ^ m = 1 := by
    rw [hη, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : ‖η - 1‖ < 1 := by
    have he : η - 1 = (σ ζ - ζ) * ζ⁻¹ := by rw [hη, sub_mul, mul_inv_cancel₀ hζ0]
    rw [he, norm_mul, norm_inv]
    have hw := hσ ζ hζ0
    have hpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ0
    rw [mul_inv_lt_iff₀ hpos, one_mul]
    exact hw
  have := eq_one_of_pow_eq_one_of_norm_lt hm0 hpm hηm hlt
  rw [hη, mul_inv_eq_one₀ hζ0] at this
  exact this

/-- Wild inertia fixes the `p`-th roots of unity. -/
theorem wild_fix_p_root {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} (hζ : ζ ^ p = 1) :
    σ ζ = ζ := by
  have hp := (Fact.out : p.Prime)
  by_contra hne
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hp.ne_zero] at hζ; exact zero_ne_one hζ
  have hζ1 : ζ ≠ 1 := by rintro rfl; exact hne (map_one σ)
  have h1ζ : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hp.pos hζ
  set η := σ ζ * ζ⁻¹ with hη
  have hηp : η ^ p = 1 := by
    rw [hη, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hη1 : η ≠ 1 := by
    intro h; rw [hη, mul_inv_eq_one₀ hζ0] at h; exact hne h
  have h1η : ‖η‖ = 1 := norm_eq_one_of_pow_eq_one hp.pos hηp
  have hord : orderOf η = p := orderOf_eq_prime hηp hη1
  have hprim : IsPrimitiveRoot η p := by
    have := IsPrimitiveRoot.orderOf η
    rwa [hord] at this
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hζ
  have hx0 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  have hw := hσ (ζ - 1) hx0
  have he : σ (ζ - 1) - (ζ - 1) = ζ * (η - 1) := by
    rw [map_sub, map_one, hη]; field_simp; ring
  rw [he, norm_mul, h1ζ, one_mul, ← hi] at hw
  exact lt_irrefl _ (lt_of_lt_of_le hw (norm_pow_sub_one_le h1η i))

/-- **Wild inertia fixes `μ_n` for `p² ∤ n` (proved).** -/
theorem wild_fix_root {σ : GQp p} (hσ : σ ∈ wildSet) {ζ : Kbar p} {n : ℕ} (hn0 : 0 < n)
    (hp2 : ¬ p ^ 2 ∣ n) (hζ : ζ ^ n = 1) : σ ζ = ζ := by
  have hp := (Fact.out : p.Prime)
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hpm : ¬ p ∣ m := by
      rintro ⟨k, rfl⟩; exact hp2 ⟨k, by ring⟩
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by simp [h] at hn0
    have hζ0 : ζ ≠ 0 := by
      rintro rfl; rw [zero_pow hn0.ne'] at hζ; exact zero_ne_one hζ
    have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
    have hy : σ (ζ ^ p) = ζ ^ p :=
      wild_fix_prime_to_p hσ hm0 hpm (by rw [← pow_mul, hζ])
    have hz : σ (ζ ^ m) = ζ ^ m :=
      wild_fix_p_root hσ (by rw [← pow_mul, mul_comm, hζ])
    have hb : ((p.gcd m : ℕ) : ℤ) = p * p.gcdA m + m * p.gcdB m := Nat.gcd_eq_gcd_ab p m
    rw [hcop.gcd_eq_one, Nat.cast_one] at hb
    have hdec : ζ = (ζ ^ p) ^ (p.gcdA m) * (ζ ^ m) ^ (p.gcdB m) := by
      rw [← zpow_natCast, ← zpow_natCast (ζ) m, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, ← hb,
        zpow_one]
    rw [hdec, map_mul, map_zpow₀, map_zpow₀, hy, hz]
  · exact wild_fix_prime_to_p hσ hn0 hpn hζ

/-- The embedding `ℚ̄ → ℚ̄_p` that `decomp` uses. -/
def embP : PkgI4.Qbar →+* Kbar p :=
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom

/-- `embP ∘ decomp σ = σ ∘ embP` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
theorem decomp_spec (σ : GQp p) (x : PkgI4.Qbar) : embP (decomp p σ x) = σ (embP x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

theorem decomp_fix_root {σ : GQp p} (hσ : σ ∈ wildSet) {x : PkgI4.Qbar} {n : ℕ} (hn0 : 0 < n)
    (hp2 : ¬ p ^ 2 ∣ n) (hx : x ^ n = 1) : decomp p σ x = x := by
  apply (embP (p := p)).injective
  rw [decomp_spec]
  exact wild_fix_root hσ hn0 hp2 (by rw [← map_pow, hx, map_one])

/-- **The cyclotomic character mod `N` is trivial on `decomp(P_p)` when `p² ∤ N` (proved).** -/
theorem cyc_decomp_wild {N : ℕ} [NeZero N] (hp2 : ¬ p ^ 2 ∣ N) {σ : GQp p}
    (hσ : σ ∈ wildSet) : GlueDescent.B2Q.cyc N (decomp p σ) = 1 := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  by_cases hN1 : N = 1
  · subst hN1; exact Subsingleton.elim _ _
  haveI : Fact (1 < N) := ⟨by omega⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  apply Units.ext
  have hu := modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (GlueDescent.B2Q.toRingAut (decomp p σ)) (c := 1) (fun t ht => by
      rw [ZMod.val_one, pow_one]
      have htN : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ N = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N t).mp ht, Units.val_one]
      exact decomp_fix_root hσ hN0 hp2 htN)
  have hc : GlueDescent.B2Q.cyc N (decomp p σ) = modularCyclotomicCharacter (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
      (GlueDescent.B2Q.toRingAut (decomp p σ)) := rfl
  rw [hc, Units.val_one]
  exact hu.symm

/-- **Every Dirichlet character mod `N`, as a Galois character, is trivial on `decomp(P_p)`
when `p² ∤ N` (proved).** -/
theorem galChar_decomp_wild {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hp2 : ¬ p ^ 2 ∣ N) {σ : GQp p} (hσ : σ ∈ wildSet) :
    GlueDescent.B2Q.galChar χ (decomp p σ) = 1 := by
  change χ.toUnitHom (GlueDescent.B2Q.cyc N (decomp p σ)) = 1
  rw [cyc_decomp_wild hp2 hσ, map_one]

/-- **`p² ∤ chiLevel T₋` for odd `p` (proved)**, `T₋` a finite set of primes (`lev q = q` for odd
`q`, `lev 2 = 4`). -/
theorem not_sq_dvd_chiLevel (hp2 : p ≠ 2) {Tm : Finset ℕ} (hTm : ∀ q ∈ Tm, q.Prime) :
    ¬ p ^ 2 ∣ GlueDescent.chiLevel Tm := by
  have hp := (Fact.out : p.Prime)
  intro h
  have hpp : p ∣ GlueDescent.chiLevel Tm := (dvd_pow_self p two_ne_zero).trans h
  have hmem : p ∈ Tm := by
    obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hpp
    have hqp := hTm q hq
    unfold GlueDescent.lev at hpq
    split_ifs at hpq with h2
    · subst h2
      have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hpq)
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this) hp2
    · rwa [(Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq]
  unfold GlueDescent.chiLevel at h
  rw [← Finset.mul_prod_erase Tm _ hmem] at h
  have hlev : GlueDescent.lev p = p := by unfold GlueDescent.lev; rw [if_neg hp2]
  rw [hlev, pow_two] at h
  have hdvd := Nat.dvd_of_mul_dvd_mul_left hp.pos h
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  have hqp := hTm q (Finset.mem_of_mem_erase hq)
  have hqne := Finset.ne_of_mem_erase hq
  unfold GlueDescent.lev at hpq
  split_ifs at hpq with h2
  · subst h2
    have : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hpq)
    exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this) hp2
  · exact hqne ((Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq).symm

/-- **`BetaSqWild` at odd `p` (proved)** from `β² = ι ∘ χ` on `G_F` (`χ` a Dirichlet character
mod `N = chiLevel T₋` for a set `T₋` of primes, as in g0-mod-field's `G7Data`; `ι` the transport
of values `ℂ^× → ℚ̄_ℓ^×`). -/
theorem betaSqWild_of_chi (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {F : Fld p} {Tm : Finset ℕ}
    (hTm : ∀ q ∈ Tm, q.Prime) [NeZero (GlueDescent.chiLevel Tm)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tm)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ σ ∈ fixSet F, β (decomp p σ) ^ 2 = (ι (GlueDescent.B2Q.galChar χ (decomp p σ)) :
      PadicAlgCl ℓ)) :
    BetaSqWild β F := by
  intro σ hσ
  rw [hsq σ hσ.1, galChar_decomp_wild χ (not_sq_dvd_chiLevel hp2 hTm) hσ.2, map_one,
    Units.val_one]

/-! ### `BetaCharOn` from `∂β = ε` (proved) -/

/-- `decomp(G_F) ⊆ G_L` when `F ⊇ embP(L)` (`L ⊆ ℚ̄`; `F ⊇ L_v` for the place `v` of `embP`). -/
theorem decomp_fix_of_le {L : IntermediateField ℚ PkgI4.Qbar} {F : Fld p}
    (hLF : ∀ x ∈ L, embP x ∈ F) {σ : GQp p} (hσ : σ ∈ fixSet F) :
    ∀ x ∈ L, decomp p σ x = x := by
  intro x hx
  apply (embP (p := p)).injective
  rw [decomp_spec]
  exact hσ _ (hLF x hx)

/-- **`BetaCharOn` from G7's `∂β = ε` (proved).** If `β g β h = ε(g,h) β(gh)` (a clause of
`G0Galois.G7Out`), `ε = 1` on `G_L × G_L` (`ε` is inflated from `Gal(L/ℚ)` and normalized,
g0-mod-field `DescentDatum`), and `F ⊇ embP(L)`, then `β` is a character on `G_F`. -/
theorem betaCharOn_of_cocycle {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) {L : IntermediateField ℚ PkgI4.Qbar}
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    {F : Fld p} (hLF : ∀ x ∈ L, embP x ∈ F) : BetaCharOn β F := by
  intro σ hσ τ hτ
  rw [hβ, hε _ _ (decomp_fix_of_le hLF hσ) (decomp_fix_of_le hLF hτ), one_mul, map_mul]

/-! ### Wild inertia fixes fields of degree `< p` (proved) -/

/-- **Wild inertia fixes every finite `E ⊆ ℚ̄_p` with `[E:ℚ_p] < p` (proved).** For `x ∈ E`
and wild `σ`, `σ^{p^a}` fixes the Galois closure of `ℚ_p(x)` (`exists_pow_fix_of_wild`), so the
`σ`-orbit of `x` has `p`-power size; its elements are distinct roots of the minimal polynomial
of `x`, of degree `≤ [E:ℚ_p] < p`; so the orbit is `{x}`. (This replaces "the Galois closure of
`L_v` is tame" at `p > D`.) -/
theorem wild_fix_small_degree {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E < p) : wildSet ⊆ fixSet E := by
  classical
  intro σ hσ x hx
  let F := FiniteGaloisIntermediateField.adjoin ℚ_[p] ({x} : Set (Kbar p))
  have hF : IsFinGal F.toIntermediateField := ⟨inferInstance, inferInstance⟩
  have hxF : x ∈ F.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin ℚ_[p] {x} rfl
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ hF
  have hper : Function.IsPeriodicPt σ (p ^ a) x := by
    unfold Function.IsPeriodicPt Function.IsFixedPt
    rw [← AlgEquiv.coe_pow]
    exact ha x hxF
  set k := Function.minimalPeriod σ x with hk
  have hkdvd : k ∣ p ^ a := hper.minimalPeriod_dvd
  have hkpos : 0 < k := hper.minimalPeriod_pos (pow_pos (Fact.out : p.Prime).pos a)
  -- the orbit lies in the roots of the minimal polynomial
  have hint : IsIntegral ℚ_[p] x := IsIntegral.of_finite ℚ_[p] (⟨x, hx⟩ : E) |>.map E.val
  set P := minpoly ℚ_[p] x with hP
  have hroot : ∀ i : ℕ, (σ^[i] x) ∈ P.aroots (Kbar p) := by
    intro i
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [← AlgEquiv.coe_pow, Polynomial.aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval,
      map_zero]
  have hcard : k ≤ P.natDegree := by
    have hinj : Set.InjOn (fun i => σ^[i] x) (Finset.range k : Set ℕ) := by
      intro i hi j hj hij
      have := Function.iterate_injOn_Iio_minimalPeriod (f := σ) (x := x)
      exact this (by simpa using hi) (by simpa using hj) hij
    have hsub : (Finset.range k).image (fun i => σ^[i] x) ⊆ (P.aroots (Kbar p)).toFinset := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact Multiset.mem_toFinset.mpr (hroot i)
    calc k = ((Finset.range k).image (fun i => σ^[i] x)).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ (P.aroots (Kbar p)).toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (P.aroots (Kbar p)) := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := by
          rw [Polynomial.aroots_def]
          exact (Polynomial.card_roots' _).trans Polynomial.natDegree_map_le
  have hdeg : P.natDegree ≤ Module.finrank ℚ_[p] E := by
    have h1 : (minpoly ℚ_[p] (⟨x, hx⟩ : E)).natDegree ≤ Module.finrank ℚ_[p] E :=
      minpoly.natDegree_le _
    rwa [IntermediateField.minpoly_eq] at h1
  have hkp : k < p := lt_of_le_of_lt (hcard.trans hdeg) hE
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hkdvd
  have hb0 : b = 0 := by
    by_contra hb0
    have : p ≤ p ^ b := Nat.le_self_pow hb0 p
    omega
  rw [hb0, pow_zero] at hb
  have h1 : Function.IsPeriodicPt σ 1 x := by
    rw [← hb]; exact Function.isPeriodicPt_minimalPeriod σ x
  exact h1

/-- **`LocalData` at `p > D` from a field of degree `< p` (proved).** If `E ⊆ ℚ̄_p` has
`[E:ℚ_p] < p` (Glazer: `E = L_v`, `[L_v:ℚ_p] ≤ D < p`) and `a·Tm` and `β` are trivial on
`G_E ∩ P_p`, then `LocalData p r` holds at `p > D` for G8's `r`. -/
theorem localData_large_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hp : (ZInQ.heightD : ℝ) < p) {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E < p) (hT : TateWildTrivial Tm a E) (hB : BetaTame β E) :
    LocalData p r := by
  rw [localData_large_iff r hp]
  intro σ hσ
  have hfix := wild_fix_small_degree hE hσ
  have h1 : ((r.restrictLocal p σ : GL (Fin 2) (PadicAlgCl ℓ)) :
      Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) = Matrix.scalar (Fin 2) ((β (decomp p σ))⁻¹) :=
    twistShape_of_g8 hG8 hT σ ⟨hfix, hσ⟩
  rw [hB σ ⟨hfix, hσ⟩, inv_one, Matrix.scalar_apply, Matrix.diagonal_one] at h1
  exact Units.ext h1

/-! ### The Galois closure and `e ≤ [E:ℚ_p]!` (proved) -/

/-- `e(F/ℚ_p) ≤ [F:ℚ_p]` for finite Galois `F`. -/
theorem ramCard_zero_le_finrank {F : Fld p} (hF : IsFinGal F) :
    ramCard F 0 ≤ Module.finrank ℚ_[p] F := by
  haveI : FiniteDimensional ℚ_[p] F := hF.1
  haveI : IsGalois ℚ_[p] F := hF.2
  haveI : Normal ℚ_[p] F := hF.2.to_normal
  rw [ramCard_zero_eq F hF, ← IsGalois.card_aut_eq_finrank]
  exact Subgroup.card_le_card_group _

/-- **A finite `E ⊆ ℚ̄_p` lies in a finite Galois `F` with `e(F/ℚ_p) ≤ n!` when
`[E:ℚ_p] ≤ n` (proved).** `F` = the splitting field in `ℚ̄_p` of the minimal polynomial `f` of a
primitive element of `E`; `Gal(F/ℚ_p)` acts faithfully on the `≤ deg f ≤ n` roots
(as in `GlueRepo.Numerics.splitting_degree_le`). -/
theorem exists_finGal_ramCard_le {E : Fld p} [FiniteDimensional ℚ_[p] E] {n : ℕ}
    (hE : Module.finrank ℚ_[p] E ≤ n) :
    ∃ F : Fld p, IsFinGal F ∧ E ≤ F ∧ ramCard F 0 ≤ n.factorial := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ_[p] E
  set a : Kbar p := (α : Kbar p) with ha
  have hint : IsIntegral ℚ_[p] a := (IsIntegral.of_finite ℚ_[p] α).map E.val
  set f := minpoly ℚ_[p] a with hf
  have hf0 : f ≠ 0 := minpoly.ne_zero hint
  have hsplit : (f.map (algebraMap ℚ_[p] (Kbar p))).Splits := IsAlgClosed.splits _
  set F : Fld p := IntermediateField.adjoin ℚ_[p] (f.rootSet (Kbar p)) with hFdef
  haveI : Polynomial.IsSplittingField ℚ_[p] F f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  haveI : FiniteDimensional ℚ_[p] F := Polynomial.IsSplittingField.finiteDimensional F f
  have hsep : f.Separable := minpoly.irreducible hint |>.separable
  haveI : IsGalois ℚ_[p] F := IsGalois.of_separable_splitting_field hsep
  have hdeg : f.natDegree ≤ n := by
    have h1 : (minpoly ℚ_[p] α).natDegree ≤ Module.finrank ℚ_[p] E := minpoly.natDegree_le _
    rw [IntermediateField.minpoly_eq] at h1
    exact h1.trans hE
  have hfin : Module.finrank ℚ_[p] F ≤ n.factorial := by
    rw [(Polynomial.IsSplittingField.algEquiv F f).toLinearEquiv.finrank_eq,
      ← Polynomial.Gal.card_of_separable hsep]
    have : Fact ((f.map (algebraMap ℚ_[p] f.SplittingField)).Splits) :=
      ⟨Polynomial.SplittingField.splits f⟩
    calc Nat.card f.Gal ≤ Nat.card (Equiv.Perm (f.rootSet f.SplittingField)) :=
          Nat.card_le_card_of_injective _ (Polynomial.Gal.galActionHom_injective f _)
      _ = (Nat.card (f.rootSet f.SplittingField)).factorial := Nat.card_perm
      _ ≤ n.factorial := by
          apply Nat.factorial_le
          rw [Nat.card_coe_set_eq]
          exact (Polynomial.ncard_rootSet_le f _).trans hdeg
  have hEF : E ≤ F := by
    intro y hy
    have h1 : (⟨y, hy⟩ : E) ∈ IntermediateField.adjoin ℚ_[p] {α} := by rw [hα]; trivial
    have h2 : y ∈ (IntermediateField.adjoin ℚ_[p] {α}).map E.val :=
      ⟨⟨y, hy⟩, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    have hroot : a ∈ f.rootSet (Kbar p) := by
      rw [Polynomial.mem_rootSet]
      exact ⟨hf0, minpoly.aeval ℚ_[p] a⟩
    have hle : IntermediateField.adjoin ℚ_[p] {E.val α} ≤ F :=
      IntermediateField.adjoin_simple_le_iff.mpr (IntermediateField.subset_adjoin _ _ hroot)
    exact hle h2
  have hFG : IsFinGal F := ⟨inferInstance, inferInstance⟩
  exact ⟨F, hFG, hEF, (ramCard_zero_le_finrank hFG).trans hfin⟩

theorem tateWildTrivial_mono {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ} {E F : Fld p} (hEF : E ≤ F)
    (h : TateWildTrivial Tm a E) : TateWildTrivial Tm a F :=
  fun σ hσ => h σ ⟨fun x hx => hσ.1 x (hEF hx), hσ.2⟩

theorem betaUpper_mono {β : GQ → PadicAlgCl ℓ} {E F : Fld p} {U : ℝ} (hEF : E ≤ F)
    (h : BetaUpper β E U) : BetaUpper β F U :=
  fun t ht σ hσ => h t ht σ ⟨hσ.1, fun x hx => hσ.2 x (hEF hx)⟩

/-- **`LocalData` at `p ≤ D` from a field of degree `≤ DG₀` (proved).** If `E ⊆ ℚ̄_p` has
`[E:ℚ_p] ≤ DG₀` (Glazer: `E = L_v(A[3])`, `A[5]` if `p = 3`) and `TateWildTrivial`, `BetaUpper`
hold on `E`, then `LocalData p r` holds at `p ≤ D` for G8's `r` (`F` = the Galois closure,
`exists_finGal_ramCard_le`). -/
theorem localData_small_of_g8 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0)
    (hT : TateWildTrivial Tm a E) (hB : BetaUpper β E U0) : SmallPrimeData p r := by
  obtain ⟨F, hF, hEF, he⟩ := exists_finGal_ramCard_le hE
  exact ⟨F, _, hF, he, twistShape_of_g8 hG8 (tateWildTrivial_mono hEF hT),
    twistUpper_of_betaUpper (betaUpper_mono hEF hB)⟩

/-! ### Assembly at odd `p` (proved) -/

/-- **`LocalData p r` at odd `p` for G8's `r`, from G7's clauses and one named glue Prop
(proved).** Hypotheses:
* G8's output for `ρ = GlueDescent.rho Tm a β` (`G0Galois.G8Out`, proved by g0-mod-galois `g8`);
* clauses of G7 (`G0Galois.G7Out`: `∂β = ε`, `β ≠ 0`; g0-mod-field `G7Data`/`DescentDatum`,
  with the values moved to `ℚ̄_ℓ` by `ι`: `β` locally constant, `β² = ι ∘ χ` for a Dirichlet
  character `χ` mod `chiLevel T₋`, `T₋` a set of primes, and `ε = 1` on `G_L × G_L`, as `ε` is
  inflated from `Gal(L/ℚ)` with `ε(1,1) = 1`);
* at `p ≤ D`: a finite `E ⊆ ℚ̄_p` containing `embP(L)` with `[E:ℚ_p] ≤ DG₀` (Glazer:
  `E = L_v(A[3])`, `A[5]` if `p = 3`) and `TateWildTrivial` on `E`;
* at `p > D`: a finite `E ⊇ embP(L)` with `[E:ℚ_p] < p` (Glazer: `E = L_v`, degree `≤ D`) and
  `TateWildTrivial` on `E`.
The `β`-side (`BetaUpper`, `BetaTame`) is fully proved from these clauses. -/
theorem localData_of_g7_odd (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hβε : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (hβlc : IsLocallyConstant β)
    {Tmin : Finset ℕ} (hTm : ∀ q ∈ Tmin, q.Prime) [NeZero (GlueDescent.chiLevel Tmin)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ))
    {L : IntermediateField ℚ PkgI4.Qbar}
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    (hsmall : (p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0 ∧
      TateWildTrivial Tm a E)
    (hlarge : (ZInQ.heightD : ℝ) < p → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E < p ∧ TateWildTrivial Tm a E) :
    LocalData p r := by
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  have htame : ∀ E : Fld p, (∀ x ∈ L, embP x ∈ E) → BetaTame β E := by
    intro E hLE
    have hm := betaCharOn_of_cocycle (p := p) hβε hε hLE
    have hs := betaSqWild_of_chi hp2 (F := E) hTm χ ι (fun σ _ => hsq _)
    have ho := betaOpen_of_isLocallyConstant (p := p) hβlc (beta_one_of_charOn hm (hβ0 1))
    exact betaTame_of_odd hp2 hm hs ho
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨E, hEfd, hLE, hdeg, hT⟩ := hsmall hp
    exact localData_small_of_g8 hG8 hdeg hT (betaUpper_of_betaTame hU0 (htame E hLE))
  · obtain ⟨E, hEfd, hLE, hdeg, hT⟩ := hlarge hp
    exact (localData_large_of_g8 hG8 hp hdeg hT (htame E hLE)).2 hp

/-! ### `p > D` from `[L:ℚ] ≤ D` (proved) -/

/-- **`[ℚ_p · embP(L) : ℚ_p] ≤ [L:ℚ]` (proved).** For a number field `L ⊆ ℚ̄`, the field
`E = ℚ_p(embP α)` (`α` a primitive element of `L`) contains `embP(L)` and has degree
`≤ deg minpoly_ℚ α = [L:ℚ]` (the minimal polynomial over `ℚ_p` divides the image of the one
over `ℚ`). This is `[L_v:ℚ_p] ≤ [L:ℚ]`. -/
theorem exists_local_field_le (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ (∀ x ∈ L, embP x ∈ E) ∧
      Module.finrank ℚ_[p] E ≤ Module.finrank ℚ L := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ L
  set αQ : PkgI4.Qbar := (α : PkgI4.Qbar) with hαQ
  have hintQ : IsIntegral ℚ αQ := (IsIntegral.of_finite ℚ α).map L.val
  set g := minpoly ℚ αQ with hg
  set a : Kbar p := embP αQ with ha
  have hroot : Polynomial.aeval a (g.map (algebraMap ℚ ℚ_[p])) = 0 := by
    rw [Polynomial.aeval_map_algebraMap, ha]
    have : Polynomial.aeval (embP (p := p) αQ) g = embP (Polynomial.aeval αQ g) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
      congr 1
      exact RingHom.ext_rat _ _
    rw [this, minpoly.aeval, map_zero]
  have hg0 : g.map (algebraMap ℚ ℚ_[p]) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ ℚ_[p]).injective).mpr (minpoly.ne_zero hintQ)
  have hint : IsIntegral ℚ_[p] a :=
    ⟨_, (minpoly.monic hintQ).map _, by
      rw [← Polynomial.aeval_def]; exact hroot⟩
  set E : Fld p := IntermediateField.adjoin ℚ_[p] {a} with hE
  haveI : FiniteDimensional ℚ_[p] E := IntermediateField.adjoin.finiteDimensional hint
  refine ⟨E, inferInstance, ?_, ?_⟩
  · intro x hx
    have h1 : (⟨x, hx⟩ : L) ∈ IntermediateField.adjoin ℚ {α} := by rw [hα]; trivial
    have h2 : x ∈ (IntermediateField.adjoin ℚ {α}).map L.val := ⟨⟨x, hx⟩, h1, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h2
    have h3 : embP (p := p) x ∈
        (IntermediateField.adjoin ℚ {L.val α}).map (embP (p := p)).toRatAlgHom :=
      ⟨x, h2, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h3
    have hle : IntermediateField.adjoin ℚ {(embP (p := p)).toRatAlgHom (L.val α)} ≤
        E.restrictScalars ℚ := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.mem_adjoin_simple_self ℚ_[p] a
    exact hle h3
  · rw [IntermediateField.adjoin.finrank hint]
    have hdvd : minpoly ℚ_[p] a ∣ g.map (algebraMap ℚ ℚ_[p]) := minpoly.dvd ℚ_[p] a hroot
    have h1 := Polynomial.natDegree_le_of_dvd hdvd hg0
    rw [Polynomial.natDegree_map] at h1
    have h2 : g.natDegree = Module.finrank ℚ L := by
      have h3 : (minpoly ℚ α).natDegree ≤ Module.finrank ℚ L := minpoly.natDegree_le _
      have h4 : Module.finrank ℚ L ≤ (minpoly ℚ α).natDegree := by
        have := IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ α)
        rw [hα, IntermediateField.finrank_top'] at this
        omega
      rw [hg, ← IntermediateField.minpoly_eq]
      omega
    omega

/-- **Glue on G3 + Néron–Ogg–Shafarevich + the descent datum on `G_L` (N5 L848-851).** At
`p > D`: on wild inertia elements whose image in `G_ℚ` lies in `G_L`, `a_σ μ_σ ∘ σ` is the
identity (it is the Tate action of `A/L`, which has good reduction at `v ∤ 3`, so inertia acts
trivially, `PkgI2.inertiaTrivial_of_goodReduction`). Only claimed for `p ≠ ℓ`. -/
def TateWildTrivialL {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∀ σ ∈ wildSet, (∀ x ∈ L, decomp p σ x = x) → a (decomp p σ) • Tm (decomp p σ) = 1

theorem tateWildTrivial_of_L {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a : GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (h : TateWildTrivialL (p := p) Tm a L) {E : Fld p}
    (hLE : ∀ x ∈ L, embP x ∈ E) : TateWildTrivial Tm a E :=
  fun σ hσ => h σ hσ.2 (decomp_fix_of_le hLE hσ.1)

/-- **`LocalData p r` at `p > D` for G8's `r` (proved)** from G7's clauses (as in
`localData_of_g7_odd`), `[L:ℚ] ≤ D` (G4's output `G4Out`), and `TateWildTrivialL`. -/
theorem localData_of_g7_large {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)
    (hβε : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (hβlc : IsLocallyConstant β)
    {Tmin : Finset ℕ} (hTm : ∀ q ∈ Tmin, q.Prime) [NeZero (GlueDescent.chiLevel Tmin)]
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ)
    (hsq : ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ))
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L]
    (hε : ∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (hp : (ZInQ.heightD : ℝ) < p)
    (hT : TateWildTrivialL (p := p) Tm a L) :
    LocalData p r := by
  have hpD : ZInQ.heightD < p := by exact_mod_cast hp
  have hp2 : p ≠ 2 := by
    have := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
    omega
  obtain ⟨E, hEfd, hLE, hdeg⟩ := exists_local_field_le (p := p) L
  refine localData_of_g7_odd hp2 hG8 hβε hβ0 hβlc hTm χ ι hsq hε
    (fun hle => absurd hp (not_lt.mpr hle)) (fun _ => ⟨E, hEfd, hLE, ?_, ?_⟩)
  · omega
  · exact tateWildTrivial_of_L hT hLE

/-! ### Final form: the glue on `L_v = ℚ_p · embP(L)` and the assembly for every `p` -/

/-- `L_v = ℚ_p · embP(L) ⊆ ℚ̄_p`, the completion of `L ⊆ ℚ̄` at the place of `embP`. -/
def Lv (L : IntermediateField ℚ PkgI4.Qbar) : Fld p :=
  IntermediateField.adjoin ℚ_[p] (embP '' (L : Set PkgI4.Qbar))

theorem embP_mem_Lv {L : IntermediateField ℚ PkgI4.Qbar} {x : PkgI4.Qbar} (hx : x ∈ L) :
    embP x ∈ Lv (p := p) L :=
  IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩

theorem Lv_le {L : IntermediateField ℚ PkgI4.Qbar} {E : Fld p} (h : ∀ x ∈ L, embP x ∈ E) :
    Lv (p := p) L ≤ E :=
  IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

/-- `[L_v:ℚ_p] ≤ [L:ℚ]` (proved, from `exists_local_field_le`). -/
theorem Lv_fin (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    FiniteDimensional ℚ_[p] (Lv (p := p) L) ∧
      Module.finrank ℚ_[p] (Lv (p := p) L) ≤ Module.finrank ℚ L := by
  obtain ⟨E, hEfd, hLE, hdeg⟩ := exists_local_field_le (p := p) L
  have hle := Lv_le (p := p) hLE
  have hfd : FiniteDimensional ℚ_[p] (Lv (p := p) L) :=
    Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  exact ⟨hfd, (IntermediateField.finrank_le_of_le_right hle).trans hdeg⟩

/-- **The clauses of G4/G7 used here (GLUE: transport between g0-mod-field's `ℂ^×`-valued data
and g0-mod-galois's `ℚ̄_ℓ`-valued `G7Out`).** `L ⊆ ℚ̄` (G4's Hom field) is finite with
`[L:ℚ] ≤ D` (`G4Out`); `∂β = ε` and `β ≠ 0` (`G0Galois.G7Out`); `β` locally constant and
`β² = ι ∘ χ` for a Dirichlet character `χ` mod `chiLevel T₋`, `T₋` a set of primes (`G7Data`, with
`ι : ℂ^× → ℚ̄_ℓ^×` the transport of values); `ε = 1` on `G_L × G_L` (`DescentDatum`: `ε` inflated
from `Gal(L/ℚ)` with `ε(1,1) = 1`). Note: g0-mod-field's interface `G7Data` (and so `AfterG7`)
does not carry `[L:ℚ] ≤ D`; `G4Out` does. -/
def G7Clauses (β : GQ → PadicAlgCl ℓ) (ε : GQ → GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  FiniteDimensional ℚ L ∧ Module.finrank ℚ L ≤ ZInQ.heightD ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧ IsLocallyConstant β ∧
  (∃ (Tmin : Finset ℕ) (_ : ∀ q ∈ Tmin, q.Prime) (_ : NeZero (GlueDescent.chiLevel Tmin))
    (χ : DirichletCharacter ℂ (GlueDescent.chiLevel Tmin)) (ι : ℂˣ →* (PadicAlgCl ℓ)ˣ),
    ∀ g, β g ^ 2 = (ι (GlueDescent.B2Q.galChar χ g) : PadicAlgCl ℓ)) ∧
  (∀ g h : GQ, (∀ x ∈ L, g x = x) → (∀ x ∈ L, h x = x) → ε g h = 1)

/-- **Glue on G4/G7 + R6 + D2 + the torsion field (N5 L813-818).** There is a finite
`E ⊇ L_v` with `[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` on which `a·Tm` is trivial on wild inertia. Glazer:
`E = L_v(A[3])` (`A[5]` if `p = 3`), `[E:L_v] ≤ |GL₄(𝔽₅)| = G₀ = 116064000000`
(`A[m] ≅ (ℤ/m)⁴`, `PkgI2.TorsionStructure`); `A` is semistable over `E` (R6,
`PkgI2.RaynaudCriterion`), so wild inertia acts trivially on `V_ℓ(A)` (D2,
`PkgI2.D2_fixed_of_raynaud`), and `a_σ μ_σ = 1` on `G_L` (`DescentDatum`). Only for `p ≠ ℓ`. -/
def TorsionFieldWild {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    TateWildTrivial Tm a E

/-- **The local glue at `p`.** `TorsionFieldWild` at `p ≤ D`, `TateWildTrivialL` at `p > D`, and
at `p = 2` the bound for `β` on `L_v` (`BetaUpper`, glue on T16 + D3 + Herbrand's `ψ ≥ id`,
N5 L826-844; `β|_{G_{L_v}}` is a character with `β⁴ = 1` on units since the 2-part of `χ` has
conductor `4`). -/
def LocalGlue {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → TorsionFieldWild (p := p) Tm a L) ∧
  ((ZInQ.heightD : ℝ) < p → TateWildTrivialL (p := p) Tm a L) ∧
  (p = 2 → BetaUpper β (Lv (p := p) L) U0)

/-- **`LocalData p r` for G8's `r`, every prime `p` (proved)** from G8's output, the G4/G7
clauses (`G7Clauses`) and the local glue (`LocalGlue`). -/
theorem localData_of_g7 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2} {L : IntermediateField ℚ PkgI4.Qbar}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r) (hC : G7Clauses β ε L)
    (hG : LocalGlue (p := p) Tm a β L) : LocalData p r := by
  obtain ⟨hLfd, hLD, hβε, hβ0, hβlc, ⟨Tmin, hTm, hNZ, χ, ι, hsq⟩, hε⟩ := hC
  obtain ⟨hLvfd, hLvdeg⟩ := Lv_fin (p := p) L
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  -- the field of `TorsionFieldWild` has degree `≤ D G₀`
  have hsmall : (p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧
      (∀ x ∈ L, embP x ∈ E) ∧ Module.finrank ℚ_[p] E ≤ ZInQ.heightD * ZInQ.heightG0 ∧
      TateWildTrivial Tm a E := by
    intro hp
    obtain ⟨E, hEfd, hLvE, hdeg, hT⟩ := hG.1 hp
    refine ⟨E, hEfd, fun x hx => hLvE (embP_mem_Lv hx), ?_, hT⟩
    calc Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) := hdeg
      _ ≤ ZInQ.heightG0 * ZInQ.heightD := Nat.mul_le_mul_left _ (hLvdeg.trans hLD)
      _ = ZInQ.heightD * ZInQ.heightG0 := Nat.mul_comm _ _
  by_cases hp2 : p = 2
  · subst hp2
    have hle : ((2 : ℕ) : ℝ) ≤ (ZInQ.heightD : ℝ) := by exact_mod_cast (by omega : 2 ≤ ZInQ.heightD)
    refine ⟨fun hp => ?_, fun hp => absurd hp (not_lt.mpr hle)⟩
    obtain ⟨E, hEfd, hLvE, hdeg, hT⟩ := hG.1 hp
    obtain ⟨E', hE'fd, hLE', hdeg', hT'⟩ := hsmall hp
    exact localData_small_of_g8 hG8 hdeg' hT' (betaUpper_mono (Lv_le hLE') (hG.2.2 rfl))
  · refine localData_of_g7_odd hp2 hG8 hβε hβ0 hβlc hTm χ ι hsq hε hsmall (fun hp => ?_)
    have hpD : ZInQ.heightD < p := by exact_mod_cast hp
    exact ⟨Lv (p := p) L, hLvfd, fun x hx => embP_mem_Lv hx, by omega,
      tateWildTrivial_of_L (hG.2.1 hp) (fun x hx => embP_mem_Lv hx)⟩

/-- **`G15RamG D u` from G8's outputs, the G4/G7 clauses and the local glue (proved).**
The G7/G8 data for `r₅` and `r₃` (models `A₅/K₅`, `A₃/K₃`, Hom fields `L₅`, `L₃`). -/
theorem g15RamG_of_g7 {L : Type} [Field L] [NumberField L] {A : PkgI3.AbVar L}
    (D : ModData L A) (u : ℚ)
    {K₅ : Type} [Field K₅] [NumberField K₅] {A₅ : PkgI3.AbVar K₅}
    {Tm₅ : GQ → Module.End (PadicAlgCl 5) (G0Galois.Vb A₅ 5)} {a₅ β₅ : GQ → PadicAlgCl 5}
    {ε₅ : GQ → GQ → PadicAlgCl 5} {L₅ : IntermediateField ℚ PkgI4.Qbar}
    (hG8₅ : G0Galois.G8Out A₅ 5 (GlueDescent.rho Tm₅ a₅ β₅) D.r5) (hC₅ : G7Clauses β₅ ε₅ L₅)
    (hG₅ : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm₅ a₅ β₅ L₅)
    {K₃ : Type} [Field K₃] [NumberField K₃] {A₃ : PkgI3.AbVar K₃}
    {Tm₃ : GQ → Module.End (PadicAlgCl 3) (G0Galois.Vb A₃ 3)} {a₃ β₃ : GQ → PadicAlgCl 3}
    {ε₃ : GQ → GQ → PadicAlgCl 3} {L₃ : IntermediateField ℚ PkgI4.Qbar}
    (hG8₃ : G0Galois.G8Out A₃ 3 (GlueDescent.rho Tm₃ a₃ β₃) D.r3) (hC₃ : G7Clauses β₃ ε₃ L₃)
    (hG₃ : LocalGlue (p := 5) Tm₃ a₃ β₃ L₃)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    G15RamG D u :=
  g15RamG_of_localData D u
    (fun p hp hp5 => @localData_of_g7 p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ _ _ hG8₅ hC₅ (hG₅ p hp hp5))
    (localData_of_g7 hG8₃ hC₃ hG₃) h11₅ h11₃

/-! ### Non-vacuity (proved) -/

/-- **`G7LocalData` is satisfiable (proved):** it holds for trivial data (`Tm = 1`, `a = 1`,
`β = 1`, `F = ℚ_p`), so it is not contradictory. -/
theorem g7LocalData_triv {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V] :
    G7LocalData (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V)) (fun _ => 1)
      (fun _ => 1) := by
  have hF : IsFinGal (⊥ : Fld p) := ⟨inferInstance, inferInstance⟩
  have he : ramCard (⊥ : Fld p) 0 = 1 := by
    have h1 := one_le_ramCard hF 0
    have h2 := ramCard_zero_le_finrank hF
    rw [IntermediateField.finrank_bot] at h2
    omega
  have hT : TateWildTrivial (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V))
      (fun _ => (1 : PadicAlgCl ℓ)) ⊥ := fun _ _ => one_smul _ _
  refine ⟨fun _ => ⟨⊥, hF, ?_, hT, fun _ _ _ _ => rfl⟩,
    fun _ => ⟨⊥, hF, ?_, hT, fun _ _ => rfl⟩⟩
  · rw [he]; exact Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  · rw [he]; exact (Nat.Prime.one_lt Fact.out).ne' ∘ Nat.dvd_one.mp

/-- **`G7Clauses` and `LocalGlue` are satisfiable (proved):** both hold for trivial data
(`β = 1`, `ε = 1`, `L = ℚ`, `Tm = 1`, `a = 1`, `χ = 1`, `ι = 1`). -/
theorem g7Clauses_triv : G7Clauses (ℓ := ℓ) (fun _ => 1) (fun _ _ => 1) ⊥ := by
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  refine ⟨inferInstance, ?_, fun _ _ => by simp, fun _ => one_ne_zero,
    IsLocallyConstant.const _, ⟨∅, fun q hq => absurd hq (Finset.notMem_empty q),
      ⟨by simp [GlueDescent.chiLevel]⟩, 1, 1, fun _ => by simp⟩, fun _ _ _ _ => rfl⟩
  rw [IntermediateField.finrank_bot]
  omega

theorem localGlue_triv {V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] :
    LocalGlue (p := p) (fun _ => (1 : Module.End (PadicAlgCl ℓ) V)) (fun _ => 1) (fun _ => 1) L := by
  obtain ⟨hfd, -⟩ := Lv_fin (p := p) L
  have hG0 : 1 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
  refine ⟨fun _ => ⟨Lv (p := p) L, hfd, le_rfl, ?_, fun _ _ => one_smul _ _⟩,
    fun _ _ _ _ => one_smul _ _, fun _ _ _ _ _ => rfl⟩
  exact Nat.le_mul_of_pos_left _ hG0

end LocalDataSec

end G15Ram

#print axioms G15Ram.largePrimeData_iff
#print axioms G15Ram.localData_large_iff
#print axioms G15Ram.mat_eq_scalar_of_intertwines
#print axioms G15Ram.twistShape_of_g8
#print axioms G15Ram.localData_of_g8
#print axioms G15Ram.betaTame_of_odd
#print axioms G15Ram.g15RamG_of_g8
#print axioms G15Ram.betaOpen_of_isLocallyConstant
#print axioms G15Ram.g7LocalData_of_odd
#print axioms G15Ram.wild_fix_root
#print axioms G15Ram.galChar_decomp_wild
#print axioms G15Ram.not_sq_dvd_chiLevel
#print axioms G15Ram.betaSqWild_of_chi
#print axioms G15Ram.betaCharOn_of_cocycle
#print axioms G15Ram.wild_fix_small_degree
#print axioms G15Ram.localData_large_of_g8
#print axioms G15Ram.exists_finGal_ramCard_le
#print axioms G15Ram.localData_small_of_g8
#print axioms G15Ram.localData_of_g7_odd
#print axioms G15Ram.g7LocalData_triv
#print axioms G15Ram.exists_local_field_le
#print axioms G15Ram.localData_of_g7_large
#print axioms G15Ram.Lv_fin
#print axioms G15Ram.localData_of_g7
#print axioms G15Ram.g15RamG_of_g7
#print axioms G15Ram.g7Clauses_triv
#print axioms G15Ram.localGlue_triv


/-! ## §5' (local-glue). Verbatim copy from scratch/g0-mod-galois/part_galois.lean lines 40-58 -/

noncomputable section

namespace G0Galois


/-- The embedding `ℚ̄ → K̄` that `Field.absoluteGaloisGroup.map` chooses (`IsAlgClosed.lift`). -/
def qEmbRing (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →+* AlgebraicClosure K :=
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom

/-- `qEmbRing` as a `ℚ`-algebra map (the `i` of g0-mod-newform's `ModData`). -/
def qEmb (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K :=
  (qEmbRing K).toRatAlgHom

/-- `qEmb K ∘ resQ K τ = τ ∘ qEmb K` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
lemma resQ_spec (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure ℚ) :
    qEmbRing K (resQ K τ x) = τ (qEmbRing K x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

end G0Galois

end

/-! ## §6 (local-glue). `LocalGlue p Tm a β L` on G7's data

`LocalGlue p Tm a β L` (§4 above, copied verbatim from scratch/local-data) is a predicate on
arbitrary operators `Tm`, scalars `a`, `β` and a field `L`. Here:

* `not_localGlue_zero` (proved): it fails for `Tm = 0` at every `p > D`, so it is not a closed
  theorem; it is a claim about the data that G7 builds.
* **Main result** `localGlue_of_g7` (proved): for G7's data (`G0Galois.G7Out`, with the clauses
  `G7Clauses`), `LocalGlue p Tm a β L` follows from three named Props about the abelian surface
  `A/K` and the kernel field, with no `Tm` or `a` left:
  - `KerWild K β L`: wild inertia elements of `G_L` killed by `β` lie in `G_K` (G7Data's kernel
    field clause `G_{L'} = G_L ∩ ker β`, transported);
  - `TateWildK p A ℓ` (`p ≥ 7`): wild inertia at `p` in `G_K` acts trivially on `V_ℓ(A)`;
  - `TateWildKE p A ℓ β L` (`p ≤ 5`): the same on `G_E` for a field `E ⊇ L_v` of degree
    `≤ G₀[L_v:ℚ_p]`, on which also `β` kills wild inertia;
  and `BetaUpper` at `p = 2` (unchanged).
* `tate_eq_one_of_torsFix` (proved): `σ` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` if it fixes every
  `ℓⁿ`-torsion point; so `TateWildK`, `TateWildKE` reduce to statements on torsion points
  (`TorsFixWild`, `TorsFixWildE`), the form in which Raynaud's criterion (R6) and D2 are stated.
-/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GaloisRep GQ decomp)
open LadicCond G0ModNewform
open CategoryTheory MonObj

section LocalGlueSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-! ### `LocalGlue` is not a closed statement -/

/-- **`LocalGlue` fails for `Tm = 0` at every `p > D` (proved).** `σ = 1` is wild and fixes
`L`, and `1 • 0 ≠ 1` on the nonzero space `ℚ̄_ℓ`. -/
theorem not_localGlue_zero (hp : (ZInQ.heightD : ℝ) < p) (L : IntermediateField ℚ PkgI4.Qbar) :
    ¬ LocalGlue (p := p) (fun _ => (0 : Module.End (PadicAlgCl ℓ) (PadicAlgCl ℓ))) (fun _ => 1)
      (fun _ => 1) L := by
  intro h
  have h1 := h.2.1 hp 1 one_mem_wildSet (fun x _ => by rw [map_one]; rfl)
  have h2 := LinearMap.congr_fun h1 1
  simp at h2

/-! ### Fixing `L` and fixing `L_v` -/

/-- If `decomp σ` fixes `L`, then `σ` fixes `L_v = ℚ_p · embP(L)` (proved). -/
theorem fixSet_Lv_of_fix {L : IntermediateField ℚ PkgI4.Qbar} {σ : GQp p}
    (h : ∀ x ∈ L, decomp p σ x = x) : σ ∈ fixSet (Lv (p := p) L) := by
  have hle : Lv (p := p) L ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    apply Lv_le
    intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hσ : σ ∈ MulAction.stabilizer (GQp p) (embP (p := p) x) := by
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, ← decomp_spec, h x hx]
    have := (Subgroup.zpowers_le.mpr hσ) hf
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
  intro y hy
  exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hy) σ (Subgroup.mem_zpowers σ)

/-- `σ` fixes `L_v` iff `decomp σ` fixes `L` (proved). -/
theorem fixSet_Lv_iff {L : IntermediateField ℚ PkgI4.Qbar} {σ : GQp p} :
    σ ∈ fixSet (Lv (p := p) L) ↔ ∀ x ∈ L, decomp p σ x = x :=
  ⟨fun h => decomp_fix_of_le (fun _ hx => embP_mem_Lv hx) h, fixSet_Lv_of_fix⟩

/-! ### `β` on wild inertia of `G_L` at odd `p` -/

/-- **`β` kills wild inertia of `G_L` at odd `p` (proved)** from G7's clauses: on `G_{L_v}`,
`β` is a character (`∂β = ε`, `ε = 1` on `G_L²`) with `β² = χ` tame (`χ` mod `chiLevel T₋`) and
open kernel (local constancy), so `betaTame_of_odd` applies with `F = L_v`. -/
theorem beta_wild_of_clauses (hp2 : p ≠ 2) {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L) {σ : GQp p} (hσ : σ ∈ wildSet)
    (hfix : ∀ x ∈ L, decomp p σ x = x) : β (decomp p σ) = 1 := by
  obtain ⟨-, -, hβε, hβ0, hβlc, ⟨Tmin, hTm, hNZ, χ, ιc, hsq⟩, hε⟩ := hC
  have hm : BetaCharOn β (Lv (p := p) L) :=
    betaCharOn_of_cocycle hβε hε (fun _ hx => embP_mem_Lv hx)
  have hs : BetaSqWild β (Lv (p := p) L) :=
    betaSqWild_of_chi hp2 hTm χ ιc (fun _ _ => hsq _)
  have hopen := betaOpen_of_isLocallyConstant (p := p) hβlc (beta_one_of_charOn hm (hβ0 1))
  exact betaTame_of_odd hp2 hm hs hopen σ ⟨fixSet_Lv_of_fix hfix, hσ⟩

/-! ### The smaller named Props -/

/-- **Glue: G7Data's kernel field clause, transported (N5 L702-716; g0-mod-field `G7Data`,
clause `σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`).** Every `g ∈ G_L` with `β(g) = 1` lies in `G_K`
(the image of `resQ K`), for the model field `K = L'` of `G0Galois.G7Out`. Notes: (i) `resQ K`
is taken along the embedding `K ↪ ℚ̄` that Mathlib's `Field.absoluteGaloisGroup.map` chooses;
`L'` is Galois over `ℚ`, so `G_{L'}` is normal and does not depend on that embedding; (ii) the
`ℚ̄_ℓ`-valued `β` here is `ι ∘ β_ℂ` (F5 of local-data), so `β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1` needs `ι`
injective on the roots of unity, which a transport `ℂ^× → ℚ̄_ℓ^×` can be chosen to be. -/
def KerWild (K : Type) [Field K] [NumberField K] (β : GQ → PadicAlgCl ℓ)
    (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∀ g : GQ, (∀ x ∈ L, g x = x) → β g = 1 → g ∈ (G0Galois.resQ K).range

/-- **Glue on R6 (`PkgI2.RaynaudCriterion`), D2 (`PkgI2.D2_fixed_of_raynaud`) and I2-Tors
(`PkgI2.TorsionStructure`) at `p ≥ 7`, `p ≠ ℓ` (N5 L813-818).** Wild inertia at `p` (at the place
of `embP`) inside `G_K` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)`. Proof plan: `m = 3` (`m = 4` if
`p = 13`); `|GL₄(ℤ/m)|` is prime to `p`, so a wild `σ' ∈ G_K` (whose action on the finite group
`A[m] ≅ (ℤ/m)⁴` has `p`-power order) fixes `A[m]`; over `K(A[m])` Raynaud gives `(σ'-1)² = 0` on
`A[ℓⁿ]`, and D2 gives `σ'` fixes `A[ℓⁿ]`; `tate_eq_one_of_torsFix`. Only true for `p ≠ ℓ`.
(Equivalently: for `p > 2g + 1` inertia acts tamely on `V_ℓ`, Grothendieck, SGA 7 I, Exp. IX;
locator UNVERIFIED.) -/
def TateWildK {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K,
    G0Galois.resQ K σ' = decomp p σ → G0Galois.tate A ℓ σ' = 1

/-- **Glue at `p ∈ {2, 3, 5}`, `p ≠ ℓ` (N5 L813-818, L826-833), on R6, D2, I2-Tors and the
descent of `A` to `L`.** There is a finite `E ⊇ L_v` with `[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` such that
every wild `σ` fixing `E` has `β(σ) = 1` and acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` through `G_K`.
Glazer: `A = (A_L)_{L'}` with `A_L` over `L`; `E = L_v'(A_L[3])` (`A_L[5]` if `p = 3`), where at
`p = 2` `L_v'/L_v` (degree `≤ 4`) kills `β` on wild inertia (`β|G_{L_v}` has order `≤ 4` on
inertia since the `2`-part of `χ` has conductor `4`; an unramified twist removes the rest; at odd
`p`, `L_v' = L_v` by `beta_wild_of_clauses`); `[E:L_v] ≤ 4·|GL₄(𝔽₃)| ≤ G₀`, resp.
`|GL₄(𝔽₅)| = G₀`. Raynaud and D2 on `A_L/E`. Not provable from `A/K` alone at these primes:
`|GL₄(ℤ/m)|` is divisible by `2`, `3` and `5` for every `m ≥ 3`. -/
def TateWildKE {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, β (decomp p σ) = 1 ∧
      ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
        G0Galois.tate A ℓ σ' = 1

/-! ### The reduction -/

/-- On a wild `σ` with `decomp σ ∈ G_L`, `β(decomp σ) = 1`, `a·Tm` is the Tate action through
`G_K` (proved, from `G7Out` and `KerWild`). -/
theorem aTm_eq_one_of_kerWild {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hK : KerWild K β L) {g : GQ} (hfix : ∀ x ∈ L, g x = x) (hβ : β g = 1)
    (htate : ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = g →
      G0Galois.tate A ℓ σ' = 1) :
    a g • Tm g = 1 := by
  obtain ⟨σ', rfl⟩ := hK g hfix hβ
  obtain ⟨hT, ha, -⟩ := h7.2.2.2.2.2.2.1 σ'
  rw [hT, ha, one_smul, htate σ' rfl]

/-- **`LocalGlue` on G7's data (proved).** For `Tm, a, β` as in `G0Galois.G7Out` with the
clauses `G7Clauses`, `LocalGlue p Tm a β L` follows from `KerWild` (all `p`), `TateWildK` at
`p ≥ 7`, `TateWildKE` at `p ≤ 5`, and `BetaUpper` at `p = 2`. At `p ≥ 7`, `p ≤ D`, the field of
`TorsionFieldWild` is `L_v` itself. -/
theorem localGlue_of_g7 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hW : 7 ≤ p → TateWildK (p := p) A ℓ) (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L)
    (hB : p = 2 → BetaUpper β (Lv (p := p) L) U0) :
    LocalGlue (p := p) Tm a β L := by
  have hD12 := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  have hpp : p.Prime := Fact.out
  have h7le : ¬ p ≤ 5 → 7 ≤ p := by
    intro h
    by_contra h'
    have : p = 6 := by omega
    exact absurd (this ▸ hpp) (by norm_num)
  -- at `p ≥ 7`: wild `σ` with `decomp σ ∈ G_L` has `a·Tm = 1`
  have hbig : 7 ≤ p → ∀ σ ∈ wildSet (p := p), (∀ x ∈ L, decomp p σ x = x) →
      a (decomp p σ) • Tm (decomp p σ) = 1 := by
    intro h7p σ hσ hfix
    have hp2 : p ≠ 2 := by omega
    exact aTm_eq_one_of_kerWild h7 hK hfix (beta_wild_of_clauses hp2 hC hσ hfix)
      (hW h7p σ hσ)
  refine ⟨fun hpD => ?_, fun hpD => ?_, hB⟩
  · by_cases h5 : p ≤ 5
    · obtain ⟨E, hEfd, hLvE, hdeg, hEw⟩ := hE h5
      refine ⟨E, hEfd, hLvE, hdeg, fun σ hσ => ?_⟩
      have hfix := decomp_fix_of_le (fun _ hx => hLvE (embP_mem_Lv hx)) hσ.1
      exact aTm_eq_one_of_kerWild h7 hK hfix (hEw σ hσ).1 (hEw σ hσ).2
    · have : FiniteDimensional ℚ L := hC.1
      obtain ⟨hfd, -⟩ := Lv_fin (p := p) L
      have hG0 : 1 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
      refine ⟨Lv (p := p) L, hfd, le_rfl, Nat.le_mul_of_pos_left _ hG0, fun σ hσ => ?_⟩
      exact hbig (h7le h5) σ hσ.2 (fixSet_Lv_iff.mp hσ.1)
  · have hpD' : ZInQ.heightD < p := by exact_mod_cast hpD
    exact fun σ hσ hfix => hbig (by omega) σ hσ hfix

/-! ### From torsion points to `V_ℓ` -/

/-- **`σ` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` if it fixes every `ℓⁿ`-torsion point (proved).**
`T_ℓ(A)` is the group of compatible sequences `(xₙ)` with `xₙ ∈ A(K̄)[ℓⁿ]`
(`PkgI3.Tate.pow_smul_eq_zero`), and `σ` acts termwise. -/
theorem tate_eq_one_of_torsFix {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Field.absoluteGaloisGroup K)
    (h : ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ P = P) :
    G0Galois.tate A ℓ σ = 1 := by
  have hT : A.galT (ℓ := ℓ) σ = LinearMap.id := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    have hx : (ℓ ^ n) • x.1 n = 0 := PkgI3.Tate.pow_smul_eq_zero x.2 n
    have hP : (Additive.toMul (x.1 n)) ^ (ℓ ^ n) = 1 := by
      rw [← toMul_nsmul, hx]; rfl
    change Additive.ofMul (A.galAct σ (Additive.toMul (x.1 n))) = x.1 n
    rw [h n _ hP]; rfl
  have hR : A.galRep ℓ σ = LinearMap.id := by
    change (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ] = LinearMap.id
    rw [hT, LinearMap.baseChange_id]
  change (A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) = LinearMap.id
  rw [hR, LinearMap.baseChange_id]

/-- **Glue on R6 + D2 + I2-Tors, on torsion points (`p ≥ 7`, `p ≠ ℓ`; N5 L813-818).** Wild
inertia at `p` inside `G_K` fixes every `ℓⁿ`-torsion point of `A(K̄)`. This is the form of
`PkgI2.D2_fixed_of_raynaud`; what remains is the bridge from the number field `K` with the place
of `embP` (`resQ`, `decomp`, `wildSet`) to the valuation-ring setting of PkgI2 (a DVR `O ⊆ K(A[m])`
and a valuation ring `w` of `K̄` over it), the base change of `A` to `K(A[m])`, and the
`p`-power order of a wild `σ'` on the finite set `A[m]` (see `TateWildK`). -/
def TorsFixWild {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K,
    G0Galois.resQ K σ' = decomp p σ →
      ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

theorem tateWildK_of_torsFixWild {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    (h : TorsFixWild (p := p) A ℓ) : TateWildK (p := p) A ℓ :=
  fun σ hσ σ' hσ' => tate_eq_one_of_torsFix A ℓ σ' (h σ hσ σ' hσ')

/-- **Glue at `p ∈ {2, 3, 5}` on torsion points** (as `TateWildKE`, with "acts trivially on
`V_ℓ`" replaced by "fixes every `ℓⁿ`-torsion point"). -/
def TorsFixWildE {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, β (decomp p σ) = 1 ∧
      ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
        ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

theorem tateWildKE_of_torsFixWildE {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {β : GQ → PadicAlgCl ℓ} {L : IntermediateField ℚ PkgI4.Qbar}
    (h : TorsFixWildE (p := p) A ℓ β L) : TateWildKE (p := p) A ℓ β L := by
  obtain ⟨E, hEfd, hLvE, hdeg, hw⟩ := h
  exact ⟨E, hEfd, hLvE, hdeg, fun σ hσ =>
    ⟨(hw σ hσ).1, fun σ' hσ' => tate_eq_one_of_torsFix A ℓ σ' ((hw σ hσ).2 σ' hσ')⟩⟩

/-- **Glue at `p ∈ {3, 5}`, `p ≠ ℓ` (as `TorsFixWildE` without the `β` clause, which is
automatic at odd `p`: `torsFixWildE_of_odd`).** Some finite `E ⊇ L_v` with
`[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` has every wild `σ ∈ G_E` fixing `A(K̄)[ℓⁿ]` through `G_K`. Glazer:
`E = L_v(A_L[5])` (`p = 3`), `L_v(A_L[3])` (`p = 5`), for the model `A_L` over `L`; R6 and D2. -/
def TorsFixWildOdd {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ)
    [Fact ℓ.Prime] (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ Lv (p := p) L ≤ E ∧
    Module.finrank ℚ_[p] E ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet E ∩ wildSet, ∀ σ' : Field.absoluteGaloisGroup K,
      G0Galois.resQ K σ' = decomp p σ →
        ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P

/-- At odd `p`, `TorsFixWildOdd` and G7's clauses give `TorsFixWildE` (proved). -/
theorem torsFixWildE_of_odd (hp2 : p ≠ 2) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L)
    (h : TorsFixWildOdd (p := p) A ℓ L) : TorsFixWildE (p := p) A ℓ β L := by
  obtain ⟨E, hEfd, hLvE, hdeg, hw⟩ := h
  exact ⟨E, hEfd, hLvE, hdeg, fun σ hσ => ⟨beta_wild_of_clauses hp2 hC hσ.2
    (decomp_fix_of_le (fun _ hx => hLvE (embP_mem_Lv hx)) hσ.1), hw σ hσ⟩⟩

/-! ### `BetaUpper` at `p = 2` without T16 (proved from a degree-`4` twist field) -/

/-- **Glue at `p = 2` (N5 L826-844; replaces T16 + D3 + Herbrand).** Some finite `M ⊇ L_v` with
`[M:L_v] ≤ 4` has `β = 1` on wild inertia of `G_M`. Proof plan: on `G_{L_v}`, `β` is a character
(`betaCharOn_of_cocycle`) and `β⁴ = χ²` is unramified at `2` (the `2`-part of `χ` is the
character mod `4`, of order `2`; the odd parts are unramified at `2`); an unramified `η` with
`η⁴ = β⁴` exists (`G_{L_v}/I` is procyclic and `β⁴` has finite order), and `M` is the kernel
field of `β η⁻¹`, of order dividing `4`. On wild inertia `η = 1`. -/
def BetaTwist2 (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∃ M : Fld p, FiniteDimensional ℚ_[p] M ∧ Lv (p := p) L ≤ M ∧
    Module.finrank ℚ_[p] M ≤ 4 * Module.finrank ℚ_[p] (Lv (p := p) L) ∧
    ∀ σ ∈ fixSet M ∩ wildSet, β (decomp p σ) = 1

/-- **`BetaUpper` from `BetaTwist2` and G7's clauses (proved), with no class field theory.**
`[M:ℚ_p] ≤ 4D ≤ DG₀`; its Galois closure `F` has `e(F) ≤ (DG₀)!` (`exists_finGal_ramCard_le`), so
`G_{ℚ_p}^t ⊆ G_F ⊆ G_M` for `t > U₀ = 4(DG₀)²` (`UpperBreakFix`, proved from T20 + T21 and
`ladicDVRModelZp`), and `G_{ℚ_p}^t` is wild (`upperWild`). -/
theorem betaUpper_of_twist {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L)
    (h : BetaTwist2 (p := p) β L) : BetaUpper β (Lv (p := p) L) U0 := by
  haveI : FiniteDimensional ℚ L := hC.1
  obtain ⟨M, hMfd, hLvM, hdeg, hM⟩ := h
  obtain ⟨-, hLv⟩ := Lv_fin (p := p) L
  have hG0 : 4 ≤ ZInQ.heightG0 := by unfold ZInQ.heightG0; norm_num
  have hMn : Module.finrank ℚ_[p] M ≤ ZInQ.heightD * ZInQ.heightG0 := by
    calc Module.finrank ℚ_[p] M ≤ 4 * Module.finrank ℚ_[p] (Lv (p := p) L) := hdeg
      _ ≤ ZInQ.heightG0 * ZInQ.heightD := Nat.mul_le_mul hG0 (hLv.trans hC.2.1)
      _ = ZInQ.heightD * ZInQ.heightG0 := Nat.mul_comm _ _
  obtain ⟨F, hF, hMF, he⟩ := exists_finGal_ramCard_le hMn
  have ha : 1 ≤ ZInQ.heightD * ZInQ.heightG0 :=
    Nat.mul_pos GlueDescent.heightD_pos (by unfold ZInQ.heightG0; norm_num)
  have hUB : UpperBreakFix p :=
    upperBreakFix_of_hilbertSerre (hilbertSerre_of_model (ladicDVRModel_of_Zp ladicDVRModelZp))
  have hU0 : (0 : ℝ) ≤ U0 := by unfold U0; positivity
  intro t ht σ hσ
  have hfix : σ ∈ fixSet F := hUB F hF _ ha he t (by unfold U0 at ht; exact ht) hσ.1
  have hwild : σ ∈ wildSet := upperWild (p := p) t (by linarith) hσ.1
  exact hM σ ⟨fun x hx => hfix x (hMF hx), hwild⟩

/-- **`LocalGlue` on G7's data with `BetaTwist2` at `p = 2` (proved)**: as `localGlue_of_g7`,
with `BetaUpper` replaced by the smaller `BetaTwist2` (`betaUpper_of_twist`). -/
theorem localGlue_of_g7_twist {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hW : 7 ≤ p → TateWildK (p := p) A ℓ) (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L)
    (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_g7 h7 hC hK hW hE (fun h => betaUpper_of_twist hC (hB h))

end LocalGlueSec

end G15Ram


/-! ## §7 (local-glue). `TorsFixWild` at `p ≥ 7` from Raynaud's criterion and I2-Tors

`torsFixWild_of_raynaud` (proved): `TorsFixWild` at `p ≥ 7`, `p ≠ ℓ`, follows from
* `WildIter`: a wild `σ'` has `p`-power period on each point of `A(K̄)` (proved in §7b, `wildIter`);
* `TorsGL A m` for `m = 3, 7`: `A(K̄)[m] ≅ (ℤ/m)⁴` as groups (the instance of the leaf I2-Tors,
  `torsGL_of_leaf`);
* `RaynaudPlace A m` for `m = 3` (`p ≠ 13`), `m = 7` (`p = 13`): a wild `σ'` fixing `A(K̄)[m]`
  satisfies `(σ' - 1)² = 0` on
  `A(K̄)[ℓⁿ]` (the instance of the leaf R6 at the place of `embP`; bridge glue).
The algebra in between is proved: `|GL₄(𝔽₃)| = 2⁹·3⁶·5·13` and `13 ∤ |GL₄(𝔽₇)|`, so the action of
a wild `σ'` on `A[m]` has order prime to `p` and `p`-power, hence is trivial
(`iterate_card_GL_fix`); then `(σ'-1)² = 0` and a `p`-power period force `σ' = 1` on
`A[ℓⁿ]` (`fixed_of_unipSq_of_iterate'`, the core of D2). -/

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj

section TorsSec

/-- **An additive structure of `S ≅ (ℤ/q)ⁿ` bounds the period (proved).** If `φ : G →* G` is
injective, maps the multiplicatively closed `S` into itself, and `S ≅ (ℤ/q)ⁿ` as groups, then
`φ^[N] = id` on `S`, `N = |GLₙ(𝔽_q)|`. -/
theorem iterate_card_GL_fix {G : Type*} [Group G] (φ : G →* G) (hinj : Function.Injective φ)
    (S : Set G) (hS : ∀ x ∈ S, φ x ∈ S) (hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    (q : ℕ) [Fact q.Prime] (n : ℕ) (e : S ≃ (Fin n → ZMod q))
    (he : ∀ (x y : S) (h : x.1 * y.1 ∈ S), e ⟨x.1 * y.1, h⟩ = e x + e y) :
    ∀ x ∈ S, φ^[Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod q))] x = x := by
  set φS : S → S := fun x => ⟨φ x, hS x x.2⟩ with hφS
  set f : (Fin n → ZMod q) → (Fin n → ZMod q) := fun v => e (φS (e.symm v)) with hf
  have hadd : ∀ a b, f (a + b) = f a + f b := by
    intro a b
    set x := e.symm a
    set y := e.symm b
    have hxy : e.symm (a + b) = ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ := by
      apply e.injective
      rw [Equiv.apply_symm_apply, he x y, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have hφxy : φS ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ =
        ⟨(φS x).1 * (φS y).1, hSmul _ (φS x).2 _ (φS y).2⟩ := by
      apply Subtype.ext
      simp [hφS, map_mul]
    simp only [hf]
    rw [hxy, hφxy, he]
  have hfinj : Function.Injective f := by
    intro a b h
    have h1 := e.injective h
    have h2 : φ (e.symm a).1 = φ (e.symm b).1 := congrArg Subtype.val h1
    exact e.symm.injective (Subtype.ext (hinj h2))
  have hfbij : Function.Bijective f := Finite.injective_iff_bijective.mp hfinj
  let fA : (Fin n → ZMod q) →+ (Fin n → ZMod q) := AddMonoidHom.mk' f hadd
  let fL := fA.toZModLinearMap q
  let fLE := LinearEquiv.ofBijective fL hfbij
  let u : LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q) :=
    ⟨fLE.toLinearMap, fLE.symm.toLinearMap, by ext v; simp, by ext v; simp⟩
  set N := Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod q)) with hN
  have hcard : Nat.card (LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q)) = N :=
    (Nat.card_congr (Matrix.GeneralLinearGroup.toLin).toEquiv).symm
  have huN : u ^ N = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have hfN : ∀ v, f^[N] v = v := by
    intro v
    have h1 : ((u ^ N : LinearMap.GeneralLinearGroup (ZMod q) (Fin n → ZMod q)) :
        Module.End (ZMod q) (Fin n → ZMod q)) v = v := by rw [huN]; rfl
    rw [Units.val_pow_eq_pow_val, Module.End.pow_apply] at h1
    exact h1
  have hsemi : Function.Semiconj e φS f := by
    intro x
    simp [hf]
  have hval : Function.Semiconj (Subtype.val : S → G) φS φ := fun x => rfl
  intro x hx
  have h1 : e (φS^[N] ⟨x, hx⟩) = e ⟨x, hx⟩ := by
    rw [(hsemi.iterate_right N) ⟨x, hx⟩]
    exact hfN _
  have h2 := congrArg Subtype.val (e.injective h1)
  rw [(hval.iterate_right N) ⟨x, hx⟩] at h2
  exact h2

/-- `|GL₄(𝔽₃)| = 80·78·72·54 = 24261120 = 2⁹·3⁶·5·13` (proved). -/
theorem card_GL4_three : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 3)) = 24261120 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

/-- `|GL₄(𝔽₇)| = 2400·2394·2352·2058` (proved). -/
theorem card_GL4_seven :
    Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 7)) = 2400 * 2394 * 2352 * 2058 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

theorem coprime_card_GL4_three {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) (h13 : p ≠ 13) :
    Nat.Coprime p 24261120 := by
  rw [hp.coprime_iff_not_dvd]
  intro h
  have hfac : (24261120 : ℕ) = 2 ^ 9 * 3 ^ 6 * 5 * 13 := by norm_num
  rw [hfac] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) h; omega
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h; omega

theorem coprime_card_GL4_seven : Nat.Coprime 13 (2400 * 2394 * 2352 * 2058) := by norm_num

variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]

/-- **D2's algebraic core on PkgI3 points (proved; as `PkgI2.fixed_of_unipSq_of_iterate`).** If
`(σ - 1)² x = 0`, `x ∈ A(K̄)[ℓⁿ]`, and `σ^{qᵃ} x = x` with `qᵃ` prime to `ℓⁿ`, then `σ x = x`. -/
theorem fixed_of_unipSq_of_iterate' (A : PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K)
    (x : A.Pt (AlgebraicClosure K)) (ℓ n q a : ℕ) (hcop : Nat.Coprime (q ^ a) (ℓ ^ n))
    (hx : x ^ (ℓ ^ n) = 1)
    (hu : A.galAct σ (A.galAct σ x) * (A.galAct σ x)⁻¹ * (A.galAct σ x)⁻¹ * x = 1)
    (hit : (A.galAct σ)^[q ^ a] x = x) : A.galAct σ x = x := by
  set N := A.galAct σ x * x⁻¹ with hN
  have hσN : A.galAct σ N = N := by
    rw [hN, map_mul, map_inv]
    have h2 : A.galAct σ (A.galAct σ x) * (A.galAct σ x)⁻¹ =
        ((A.galAct σ x)⁻¹ * x)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hu]; group
    rw [h2, mul_inv_rev, inv_inv, mul_comm]
  have hiter : ∀ k : ℕ, (A.galAct σ)^[k] x = N ^ k * x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, map_mul, map_pow, hσN, pow_succ, hN]
      group
  have h1 : N ^ (q ^ a) = 1 := by
    have := hiter (q ^ a)
    rw [hit] at this
    exact (mul_eq_right.mp this.symm)
  have h2 : N ^ (ℓ ^ n) = 1 := by
    rw [hN, mul_pow, ← map_pow, hx, map_one, inv_pow, hx]; simp
  have hN1 : N = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  rw [hN] at hN1
  exact mul_inv_eq_one.mp hN1

/-- **Glue (bridge): wild elements have `p`-power period on points.** For wild `σ` and
`σ' ∈ G_K` over `decomp σ`, every `P ∈ A(K̄)` has `σ'^{pᵃ} P = P` for some `a`. Proof plan: `P` is
defined over a finite `F ⊆ K̄` (a `K̄`-point of a scheme of finite type over `K`); `qEmb K` is an
isomorphism `ℚ̄ ≅ K̄` (both are algebraic closures of `ℚ`), and `embP` sends `qEmb⁻¹(F)` into a
finite extension of `ℚ_p`, whose Galois closure is fixed by some `σ^{pᵃ}`
(`exists_pow_fix_of_wild`, local-data). -/
def WildIter (A : PkgI3.AbVar K) : Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
    ∀ P : A.Pt (AlgebraicClosure K), ∃ a : ℕ, (A.galAct σ')^[p ^ a] P = P

/-- **The instance of the leaf I2-Tors on `A` (`A(K̄)[m] ≅ (ℤ/m)⁴` as groups).** Proved from
`ObjBridge.TorsionStructure` for `dim A = 2` in `torsGL_of_leaf`. -/
def TorsGL (A : PkgI3.AbVar K) (m : ℕ) : Prop :=
  ∃ e : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} ≃ (Fin 4 → ZMod m),
    ∀ (x y : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1})
      (h : x.1 * y.1 ∈ {P : A.Pt (AlgebraicClosure K) | P ^ m = 1}),
      e ⟨x.1 * y.1, h⟩ = e x + e y

/-- **Glue on the leaf R6 (`PkgI2.RaynaudCriterion`) at the place of `embP` (N5 L813-818).**
A wild `σ' ∈ G_K` (over `decomp σ`, `σ ∈ wildSet`) that fixes `A(K̄)[m]` satisfies
`(σ' - 1)² = 0` on `A(K̄)[ℓⁿ]` for every prime `ℓ ≠ p`. Proof plan: R6 on `K' = K(A[m])`
(over which `A[m]` is rational, `m ≥ 3` prime to `p`) with the valuation ring of `K'` at the
place of `embP` (a DVR) and a valuation ring `w` of `K̄` over it; `σ'` fixes `K'`, and a wild
element is in the inertia group of `w`. What is missing is that bridge (PkgI2's setting is a
field with a DVR and `AlgebraicClosure`; here `G_K`, `resQ`, `decomp`) and the base change of
`A` to `K'`. Claimed only for `m ≥ 3` prime to `p` (used with `m = 3` for `p ≠ 13` and `m = 7`
for `p = 13`; for `m = p` Raynaud's criterion does not apply and the statement can fail). -/
def RaynaudPlace (A : PkgI3.AbVar K) (m : ℕ) : Prop :=
  ∀ σ ∈ wildSet (p := p), ∀ σ' : Field.absoluteGaloisGroup K, G0Galois.resQ K σ' = decomp p σ →
    (∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P) →
    ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ∀ (n : ℕ) (x : A.Pt (AlgebraicClosure K)), x ^ (ℓ ^ n) = 1 →
      A.galAct σ' (A.galAct σ' x) * (A.galAct σ' x)⁻¹ * (A.galAct σ' x)⁻¹ * x = 1

/-- **`TorsGL` from the leaf I2-Tors (proved)**, for `dim A = 2` (a clause of `G7Out`). -/
theorem torsGL_of_leaf (hT : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2)
    (m : ℕ) (hm : 0 < m) : TorsGL A m := by
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  obtain ⟨e, he⟩ := hT K (ObjBridge.toGrp A) 2 m (by exact_mod_cast hdim) hm hmK
  exact ⟨e, he⟩

/-- `σ⁻¹ (σ P) = P` on points (proved). -/
theorem galAct_inv_galAct (A : PkgI3.AbVar K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (P : A.Pt (AlgebraicClosure K)) :
    A.galAct σ⁻¹ (A.galAct σ P) = P := by
  change PkgI3.AbVar.galHom σ⁻¹ ≫ PkgI3.AbVar.galHom σ ≫ P = P
  rw [← Category.assoc, ← PkgI3.AbVar.galHom_mul, inv_mul_cancel, PkgI3.AbVar.galHom_one,
    Category.id_comp]

theorem galAct_injective (A : PkgI3.AbVar K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    Function.Injective (A.galAct (L := AlgebraicClosure K) σ) := by
  intro x y h
  have h1 := congrArg (A.galAct σ⁻¹) h
  rwa [galAct_inv_galAct, galAct_inv_galAct] at h1

/-- A wild `σ'` fixes `A(K̄)[m]` when `p ∤ |GL₄(ℤ/m)|` (proved from `WildIter` and `TorsGL`). -/
theorem fix_torsion_of_coprime {A : PkgI3.AbVar K} (hI : WildIter (p := p) A) (m : ℕ)
    [Fact m.Prime] (hT : TorsGL A m)
    (hcop : Nat.Coprime p (Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod m))))
    {σ : GQp p} (hσ : σ ∈ wildSet) {σ' : Field.absoluteGaloisGroup K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) :
    ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P := by
  obtain ⟨e, he⟩ := hT
  intro P hP
  have hfix := iterate_card_GL_fix (A.galAct σ') (galAct_injective A σ')
    {P : A.Pt (AlgebraicClosure K) | P ^ m = 1}
    (fun x hx => by
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [← map_pow, hx, map_one])
    (fun x hx y hy => by
      simp only [Set.mem_ofPred_eq] at hx hy ⊢
      rw [mul_pow, hx, hy, _root_.one_mul]) m 4 e he P hP
  obtain ⟨a, ha⟩ := hI σ hσ σ' hσ' P
  have h1 : Function.IsPeriodicPt (A.galAct σ') (p ^ a) P := ha
  have h2 : Function.IsPeriodicPt (A.galAct σ')
      (Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod m))) P := hfix
  have h3 := h1.gcd h2
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left a hcop)] at h3
  exact h3

/-! ### `WildIter` from `PtFinite` (proved) -/

/-- `σ (τ P) = (στ) P` on points (proved). -/
theorem galAct_galAct (A : PkgI3.AbVar K) (σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (P : A.Pt (AlgebraicClosure K)) : A.galAct σ (A.galAct τ P) = A.galAct (σ * τ) P := by
  change PkgI3.AbVar.galHom σ ≫ PkgI3.AbVar.galHom τ ≫ P = PkgI3.AbVar.galHom (σ * τ) ≫ P
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

theorem galAct_iterate (A : PkgI3.AbVar K) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (P : A.Pt (AlgebraicClosure K)) (k : ℕ) : (A.galAct σ)^[k] P = A.galAct (σ ^ k) P := by
  induction k with
  | zero =>
    change P = PkgI3.AbVar.galHom 1 ≫ P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  | succ k ih => rw [Function.iterate_succ_apply', ih, galAct_galAct, ← pow_succ']

/-- `qEmb K : ℚ̄ → K̄` is onto (proved): `K̄` is integral over `ℚ` (`K` is a number field), hence
over the algebraically closed `ℚ̄`. -/
theorem qEmbRing_surjective (K : Type) [Field K] [NumberField K] :
    Function.Surjective (G0Galois.qEmbRing K) := by
  have hint : Algebra.IsIntegral ℚ (AlgebraicClosure K) := Algebra.IsIntegral.trans K
  have h : ((G0Galois.qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ))).IsIntegral := by
    rw [Subsingleton.elim ((G0Galois.qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ)))
      (algebraMap ℚ (AlgebraicClosure K))]
    exact hint.isIntegral
  exact (IsAlgClosed.ringHom_bijective_of_isIntegral _ (RingHom.IsIntegral.tower_top _ _ h)).2

theorem pow_fix_mono {G X : Type*} [Group G] [MulAction G X] {g : G} {x : X} {q b a : ℕ}
    (h : g ^ (q ^ b) • x = x) (hba : b ≤ a) : g ^ (q ^ a) • x = x := by
  have hmem : g ^ (q ^ b) ∈ MulAction.stabilizer G x := h
  have : g ^ (q ^ a) = (g ^ (q ^ b)) ^ (q ^ (a - b)) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hba]
  rw [this]
  exact (MulAction.stabilizer G x).pow_mem hmem _

/-- **A wild `σ'` has `p`-power period on each element of `K̄` (proved).** `x = qEmb y`;
`σ^{pᵃ}` fixes the normal closure of `ℚ_p(embP y)` (`exists_pow_fix_of_wild`), so
`decomp(σ^{pᵃ})` fixes `y` (`decomp_spec`), and `σ'^{pᵃ} x = qEmb(decomp(σ^{pᵃ}) y) = x`
(`resQ_spec`). -/
theorem wild_pow_fix_elem {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (x : AlgebraicClosure K) :
    ∃ a : ℕ, (σ' ^ (p ^ a)) x = x := by
  obtain ⟨y, rfl⟩ := qEmbRing_surjective K x
  set E : Fld p := IntermediateField.adjoin ℚ_[p] {embP (p := p) y}
  haveI : FiniteDimensional ℚ_[p] E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
  set F' := IntermediateField.normalClosure ℚ_[p] E (Kbar p)
  haveI : FiniteDimensional ℚ_[p] F' := normalClosure.is_finiteDimensional ℚ_[p] E (Kbar p)
  haveI : Normal ℚ_[p] F' := normalClosure.normal ℚ_[p] E (Kbar p)
  obtain ⟨a, ha⟩ := exists_pow_fix_of_wild hσ (F' := F') ⟨inferInstance, IsGalois.mk⟩
  refine ⟨a, ?_⟩
  have hyE : embP (p := p) y ∈ F' :=
    E.le_normalClosure (IntermediateField.mem_adjoin_simple_self ℚ_[p] _)
  have hdec : decomp p (σ ^ (p ^ a)) y = y := by
    apply (embP (p := p)).injective
    rw [decomp_spec]
    exact ha _ hyE
  have h1 : G0Galois.qEmbRing K (G0Galois.resQ K (σ' ^ (p ^ a)) y) =
      (σ' ^ (p ^ a)) (G0Galois.qEmbRing K y) := G0Galois.resQ_spec K _ y
  have hpow : G0Galois.resQ K (σ' ^ (p ^ a)) = (G0Galois.resQ K σ') ^ (p ^ a) := map_pow _ _ _
  rw [hpow, hσ', ← map_pow, hdec] at h1
  exact h1.symm

/-- **A wild `σ'` has `p`-power period on each finite `F ⊆ K̄` over `K` (proved)**, from
`wild_pow_fix_elem` on a basis. -/
theorem wild_pow_fix_field {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (F : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K F] : ∃ a : ℕ, ∀ x ∈ F, (σ' ^ (p ^ a)) x = x := by
  set b := Module.finBasis K F
  choose c hc using fun i => wild_pow_fix_elem hσ hσ' ((b i : F) : AlgebraicClosure K)
  refine ⟨∑ i, c i, fun x hx => ?_⟩
  have hb : ∀ i, (σ' ^ (p ^ (∑ i, c i))) ((b i : F) : AlgebraicClosure K) = b i := fun i =>
    pow_fix_mono (G := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (hc i)
      (Finset.single_le_sum (fun j _ => Nat.zero_le (c j)) (Finset.mem_univ i))
  have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • ((b i : F) : AlgebraicClosure K) := by
    have h := congrArg (fun z : F => (z : AlgebraicClosure K)) (b.sum_repr ⟨x, hx⟩).symm
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    exact h
  rw [hx', map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, hb i, ← Algebra.smul_def]

/-- **Glue (Mathlib-level): `K̄`-points are defined over finite extensions.** Every
`P ∈ A(K̄)` is fixed by `G_F` for a finite `F ⊆ K̄` over `K` (a `K̄`-point of a scheme of finite
type over `K` factors through `Spec F`, `F` generated by the images of finitely many coordinates;
standard, e.g. EGA I/IV, locator UNVERIFIED). -/
def PtFinite (A : PkgI3.AbVar K) : Prop :=
  ∀ P : A.Pt (AlgebraicClosure K), ∃ F : IntermediateField K (AlgebraicClosure K),
    FiniteDimensional K F ∧ ∀ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (∀ x ∈ F, τ x = x) → A.galAct τ P = P

/-- **`WildIter` from `PtFinite` (proved).** -/
theorem wildIter_of_ptFinite {A : PkgI3.AbVar K} (h : PtFinite A) : WildIter (p := p) A := by
  intro σ hσ σ' hσ' P
  obtain ⟨F, hF, hP⟩ := h P
  obtain ⟨a, ha⟩ := wild_pow_fix_field (σ' := σ') hσ hσ' F
  have hit := galAct_iterate A σ' P (p ^ a)
  exact ⟨a, hit.trans (hP _ ha)⟩

/-- **`TorsFixWild` at `p ≥ 7`, `p ≠ ℓ`, from `WildIter`, I2-Tors and Raynaud at the place
(proved).** `m = 3` (`m = 7` if `p = 13`): the wild `σ'` fixes `A[m]`
(`fix_torsion_of_coprime`), so `(σ'-1)² = 0` on `A[ℓⁿ]` (`RaynaudPlace`), and with a `p`-power
period it fixes `A[ℓⁿ]` (`fixed_of_unipSq_of_iterate'`). -/
theorem torsFixWild_of_raynaud {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hI : WildIter (p := p) A) (hT3 : TorsGL A 3) (hT7 : TorsGL A 7)
    (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3) (hR7 : p = 13 → RaynaudPlace (p := p) A 7) :
    TorsFixWild (p := p) A ℓ := by
  intro σ hσ σ' hσ' n x hx
  have hpp : p.Prime := Fact.out
  have hfixm : ∃ m, (∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct σ' P = P) ∧
      RaynaudPlace (p := p) A m := by
    by_cases h13 : p = 13
    · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      refine ⟨7, fix_torsion_of_coprime hI 7 hT7 ?_ hσ hσ', hR7 h13⟩
      rw [card_GL4_seven, h13]; exact coprime_card_GL4_seven
    · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      refine ⟨3, fix_torsion_of_coprime hI 3 hT3 ?_ hσ hσ', hR3 h13⟩
      rw [card_GL4_three]; exact coprime_card_GL4_three hpp h7 h13
  obtain ⟨m, hm, hR⟩ := hfixm
  obtain ⟨a, ha⟩ := hI σ hσ σ' hσ' x
  have hcop : Nat.Coprime (p ^ a) (ℓ ^ n) :=
    Nat.Coprime.pow a n ((Nat.coprime_primes hpp Fact.out).mpr (Ne.symm hℓp))
  exact fixed_of_unipSq_of_iterate' A σ' x ℓ n p a hcop hx
    (hR σ hσ σ' hσ' hm ℓ Fact.out hℓp n x hx) ha

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaves I2-Tors and (through `RaynaudPlace`) R6,
and the bridge `WildIter` (proved).** `dim A = 2` is a clause of `G7Out`. -/
theorem tateWildK_of_leaves {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2)
    (hI : WildIter (p := p) A) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_torsFixWild (torsFixWild_of_raynaud hℓp h7 hI (torsGL_of_leaf hTors A hdim 3
    (by norm_num)) (torsGL_of_leaf hTors A hdim 7 (by norm_num)) hR3 hR7)

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaf I2-Tors, `PtFinite` and `RaynaudPlace`
(proved).** -/
theorem tateWildK_of_leaves' {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (h7 : 7 ≤ p) (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2)
    (hPt : PtFinite A) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_leaves hℓp h7 hTors hdim (wildIter_of_ptFinite hPt) hR3 hR7

end TorsSec

end G15Ram

end

#print axioms G15Ram.not_localGlue_zero
#print axioms G15Ram.fixSet_Lv_iff
#print axioms G15Ram.beta_wild_of_clauses
#print axioms G15Ram.localGlue_of_g7
#print axioms G15Ram.tate_eq_one_of_torsFix
#print axioms G15Ram.tateWildK_of_torsFixWild
#print axioms G15Ram.tateWildKE_of_torsFixWildE
#print axioms G15Ram.iterate_card_GL_fix
#print axioms G15Ram.card_GL4_three
#print axioms G15Ram.torsGL_of_leaf
#print axioms G15Ram.torsFixWild_of_raynaud
#print axioms G15Ram.tateWildK_of_leaves
#print axioms G15Ram.qEmbRing_surjective
#print axioms G15Ram.wild_pow_fix_field
#print axioms G15Ram.wildIter_of_ptFinite
#print axioms G15Ram.tateWildK_of_leaves'
#print axioms G15Ram.torsFixWildE_of_odd
#print axioms G15Ram.betaUpper_of_twist
#print axioms G15Ram.localGlue_of_g7_twist

/-! ## §7b (local-glue). `PtFinite` proved: `K̄`-points come from finite extensions

`K̄ = colim F` over the finite subextensions `F` of `K̄/K` (as in scratch/morph-descend's
`ringCoconeIsColimit`, there for `ℚ̄`), so `Spec K̄ = lim Spec F`; since `A → Spec K` is smooth,
hence locally of finite presentation, Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
(Stacks 01ZC) factors every `K`-morphism `Spec K̄ → A` through some `Spec F`. -/

noncomputable section

namespace G15Ram

open CategoryTheory Limits AlgebraicGeometry

section PtFiniteSec

variable {K : Type} [Field K]

/-- The finite subextensions of `K̄/K`, ordered by inclusion. -/
abbrev FIdx (K : Type) [Field K] : Type :=
  {F : IntermediateField K (AlgebraicClosure K) // FiniteDimensional K F}

instance : IsDirectedOrder (FIdx K) where
  directed F₁ F₂ := by
    obtain ⟨F₁, h₁⟩ := F₁
    obtain ⟨F₂, h₂⟩ := F₂
    exact ⟨⟨F₁ ⊔ F₂, IntermediateField.finiteDimensional_sup F₁ F₂⟩,
      show F₁ ≤ F₁ ⊔ F₂ from le_sup_left, show F₂ ≤ F₁ ⊔ F₂ from le_sup_right⟩

instance : Nonempty (FIdx K) := ⟨⟨⊥, inferInstance⟩⟩

/-- The diagram `F ↦ F` of rings. -/
def fRingDiag (K : Type) [Field K] : FIdx K ⥤ CommRingCat where
  obj F := CommRingCat.of F.1
  map f := CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `K̄` as a cocone. -/
def fRingCocone (K : Type) [Field K] : Cocone (fRingDiag K) where
  pt := CommRingCat.of (AlgebraicClosure K)
  ι := { app F := CommRingCat.ofHom (algebraMap F.1 (AlgebraicClosure K))
         naturality _ _ _ := rfl }

/-- `K̄ = colim F` over the finite subextensions (as morph-descend's `ringCoconeIsColimit`). -/
def fRingCoconeIsColimit (K : Type) [Field K] : IsColimit (fRingCocone K) := by
  haveI : ReflectsColimit (fRingDiag K) (forget CommRingCat) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine isColimitOfReflects (forget CommRingCat) (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro (x : AlgebraicClosure K)
    have hx : _root_.IsIntegral K x := Algebra.IsIntegral.isIntegral _
    have : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
      IntermediateField.adjoin.finiteDimensional hx
    exact ⟨⟨IntermediateField.adjoin K {x}, this⟩,
      ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩, rfl⟩
  · intro i x y h
    exact ⟨i, 𝟙 i, by rw [Subtype.ext h]⟩

/-- The diagram `F ↦ Spec F` of schemes. -/
def fSpecDiag (K : Type) [Field K] : (FIdx K)ᵒᵖ ⥤ Scheme where
  obj F := Spec (CommRingCat.of F.unop.1)
  map f := Spec.map (CommRingCat.ofHom (IntermediateField.inclusion (leOfHom f.unop)).toRingHom)
  map_id F := by
    rw [show CommRingCat.ofHom (IntermediateField.inclusion (leOfHom (𝟙 F).unop)).toRingHom =
      𝟙 _ from rfl, Spec.map_id]
  map_comp f g := by
    rw [← Spec.map_comp]
    rfl

/-- `Spec K̄` as a cone over `fSpecDiag`. -/
def fSpecCone (K : Type) [Field K] : Cone (fSpecDiag K) where
  pt := Spec (CommRingCat.of (AlgebraicClosure K))
  π := { app F := Spec.map (CommRingCat.ofHom (algebraMap F.unop.1 (AlgebraicClosure K)))
         naturality F F' f := by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
          change _ = _ ≫ Spec.map _
          rw [← Spec.map_comp]
          rfl }

/-- `Spec K̄ = lim Spec F` (proved; `Spec` turns the colimit `fRingCoconeIsColimit` into a limit). -/
def fSpecConeIsLimit (K : Type) [Field K] : IsLimit (fSpecCone K) := by
  have h := isLimitOfPreserves Scheme.Spec (fRingCoconeIsColimit K).op
  refine (IsLimit.equivOfNatIsoOfIso (NatIso.ofComponents (fun _ => Iso.refl _) ?_) _ _
    (Cone.ext (Iso.refl _) ?_)) h
  · intro F F' f
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · intro F
    simp only [Iso.refl_hom, Category.id_comp]

/-- **`PtFinite` holds for every abelian variety (proved).** -/
theorem ptFinite (A : PkgI3.AbVar K) : PtFinite A := by
  intro P
  have h3 : ∀ {i j : (FIdx K)ᵒᵖ} (f : i ⟶ j), IsAffineHom ((fSpecDiag K).map f) := fun f => by
    change IsAffineHom (Spec.map _); infer_instance
  have h1 : ∀ i, CompactSpace ((fSpecDiag K).obj i) := fun i => by
    change CompactSpace (Spec _); infer_instance
  have h2 : ∀ i, QuasiSeparatedSpace ((fSpecDiag K).obj i) := fun i => by
    change QuasiSeparatedSpace (Spec _); infer_instance
  let t : fSpecDiag K ⟶ (Functor.const _).obj (Spec (CommRingCat.of K)) :=
    { app F := Spec.map (CommRingCat.ofHom (algebraMap K F.unop.1))
      naturality F F' f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map]
        change Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp]
        rfl }
  have ha : (fSpecCone K).π ≫ t = (Functor.const _).map (P.left ≫ A.X.hom) := by
    ext F
    simp only [NatTrans.comp_app, Functor.const_map_app]
    change Spec.map _ ≫ Spec.map _ = P.left ≫ A.X.hom
    rw [← Spec.map_comp, Over.w P]
    rfl
  obtain ⟨F, g, hg, -⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (fSpecDiag K) t A.X.hom
      (fSpecCone K) (fSpecConeIsLimit K) P.left ha
  refine ⟨F.unop.1, F.unop.2, fun τ hτ => ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (τ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ P.left =
    P.left
  rw [← hg]
  refine (Category.assoc _ _ _).symm.trans (congrArg (· ≫ g) ?_)
  refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
  ext x
  exact hτ x.1 x.2

/-- **`WildIter` holds for every abelian variety (proved)**: `wildIter_of_ptFinite` and
`ptFinite`. -/
theorem wildIter {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    (A : PkgI3.AbVar K) : WildIter (p := p) A :=
  wildIter_of_ptFinite (ptFinite A)

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaf I2-Tors and the instances `RaynaudPlace`
of the leaf R6 alone (proved).** -/
theorem tateWildK_of_raynaud {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p)
    (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2) (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3)
    (hR7 : p = 13 → RaynaudPlace (p := p) A 7) : TateWildK (p := p) A ℓ :=
  tateWildK_of_leaves hℓp h7 hTors hdim (wildIter A) hR3 hR7

end PtFiniteSec

end G15Ram

end

#print axioms G15Ram.ptFinite
#print axioms G15Ram.tateWildK_of_raynaud

/-! ## §7c' (local-glue). Verbatim slices of scratch/neron-lg/NeronLG.lean (origin/wip/neron-lg)
l.207-215, l.225-236, l.1406-1472 -/

noncomputable section

namespace ZInQ.NeronLG

open NumberField
open CategoryTheory MonObj

/-- The discrete valuation ring `𝓞_{L,v}` of a nonzero prime `v` of `𝓞_L`, as a valuation subring
of `L` (the ring of the `v`-adic valuation). -/
noncomputable def dvrAt {L : Type} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : ValuationSubring L :=
  (v.valuation L).valuationSubring

instance {L : Type} [Field L] [NumberField L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    IsDiscreteValuationRing (dvrAt v) := by
  unfold dvrAt; infer_instance

section Classify

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [NumberField K]

/-- Every valuation subring of a number field contains `𝓞_K` (it is integrally closed). -/
theorem ringOfIntegers_mem (O : ValuationSubring K) (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem O)

theorem toO_coe (O : ValuationSubring K) (x : 𝓞 K) : ((toO O x : O) : K) = algebraMap (𝓞 K) K x :=
  rfl

end Classify

section Restrict

variable {K : Type} [Field K] [NumberField K]

/-- The center of a valuation subring `O ≠ ⊤` of a number field on `𝓞_K`: a nonzero prime. -/
def center' (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := (IsLocalRing.maximalIdeal O).comap (toO O)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy⟩ : ∃ y : K, y ∉ O := by
      by_contra h
      push_neg at h
      exact hO (eq_top_iff.2 fun y _ => h y)
    have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
    have hyi : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hy
    let x : O := ⟨y⁻¹, hyi⟩
    have hx : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu'⟩ := hu
      apply hy
      have : ((u⁻¹ : Oˣ) : O) * x = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Oˣ) : O) : K)) * y⁻¹ = 1 := congrArg Subtype.val this
      have h3 : y = (((u⁻¹ : Oˣ) : O) : K) := by
        field_simp at h2
        exact h2.symm
      rw [h3]; exact (((u⁻¹ : Oˣ) : O)).2
    have hx0 : x ≠ 0 := fun h => inv_ne_zero hy0 (congrArg Subtype.val h)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero hb
    have ha : toO O a = x * toO O b := by
      apply Subtype.ext
      rw [toO_coe, Subring.coe_mul, toO_coe, ← hab, div_mul_cancel₀ _ hb0]
    intro hbot
    have hmem : a ∈ (IsLocalRing.maximalIdeal O).comap (toO O) := by
      rw [Ideal.mem_comap, ha]; exact Ideal.mul_mem_right _ _ hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    apply Subtype.ext
    rw [← hab, hmem, map_zero, zero_div]; rfl

/-- **Every valuation subring `O ≠ ⊤` of a number field is `𝓞_{K,v}` (proved).** -/
theorem dvrAt_center' (O : ValuationSubring K) (hO : O ≠ ⊤) : dvrAt (center' O hO) = O := by
  apply ValuationSubring.eq_of_le_of_ne_top _ _ hO
  intro x hx
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (center' O hO) x hx
  have hd : IsUnit (toO O d) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hvd : O.valuation (algebraMap (𝓞 K) K d) = 1 := (O.valuation_eq_one_iff _).1 hd
  apply O.mem_of_valuation_le_one
  have h2 := congrArg O.valuation hnd
  rw [map_mul, hvd, _root_.mul_one] at h2
  rw [h2]
  exact O.valuation_le_one (toO O n)

/-- Every valuation subring `O ≠ ⊤` of a number field is a DVR. -/
theorem isDiscreteValuationRing_of_ne_top (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by
  rw [← dvrAt_center' O hO]
  infer_instance

end Restrict

end ZInQ.NeronLG

end


/-! ## §7c (local-glue). Raynaud's criterion (R6) at the place of `embP`: the rational case

`raynaudPlace_rational` (proved): if `A[m]` is `K`-rational (`m ≥ 3`, `p ∤ m`), the leaf R6
(`ObjBridge.RaynaudCriterion`) gives `RaynaudPlace A m`. The valuation-theoretic bridge is proved:
* `wK`, `OK`: the valuation subrings of `K̄` and `K` at the place of `embP` (norm `≤ 1` after
  `K̄ ≅ ℚ̄ → ℚ̄_p`); `OK` is a DVR (`OK_ne_top` and neron-lg's `isDiscreteValuationRing_of_ne_top`);
* `m`, `ℓ` prime to `p` are units of `OK`;
* a wild `σ'` (over `decomp σ`) lies in the inertia group of `wK` (`isInertia_of_wild`).
The general case of `RaynaudPlace` needs R6 over `K(A[m])` and the base change of `A`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj
open scoped Pointwise

section RaynaudSec

/-- The valuation subring `{x : ‖f x‖ ≤ 1}` for a ring map `f` to an ultrametric normed field. -/
def normVS {F E : Type*} [Field F] [NormedField E] [IsUltrametricDist E] (f : F →+* E) :
    ValuationSubring F where
  carrier := {x | ‖f x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_mul, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha
  mem_or_inv_mem' x := by
    by_cases h : ‖f x‖ ≤ 1
    · exact Or.inl h
    · right
      show ‖f x⁻¹‖ ≤ 1
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp h))

theorem mem_normVS {F E : Type*} [Field F] [NormedField E] [IsUltrametricDist E] (f : F →+* E)
    (x : F) : x ∈ normVS f ↔ ‖f x‖ ≤ 1 := Iff.rfl

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]

/-- `ℚ̄ ≅ K̄` (`qEmbRing` is bijective). -/
def eK (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective (G0Galois.qEmbRing K)
    ⟨(G0Galois.qEmbRing K).injective, qEmbRing_surjective K⟩

/-- `K̄ ≅ ℚ̄ → ℚ̄_p`, the place of `embP` on `K̄`. -/
def ιbar (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] :
    AlgebraicClosure K →+* Kbar p :=
  (embP (p := p)).comp (eK K).symm.toRingHom

/-- The valuation ring of `K̄` at the place of `embP`. -/
def wK (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] :
    ValuationSubring (AlgebraicClosure K) :=
  normVS (ιbar p K)

/-- The valuation ring of `K` at the place of `embP`. -/
def OK (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [NumberField K] : ValuationSubring K :=
  normVS ((ιbar p K).comp (algebraMap K (AlgebraicClosure K)))

theorem wK_comap : (wK p K).comap (algebraMap K (AlgebraicClosure K)) = OK p K := by
  ext x; exact Iff.rfl

theorem OK_ne_top : OK p K ≠ ⊤ := by
  intro h
  have hmem : ((p : K))⁻¹ ∈ OK p K := by rw [h]; exact ValuationSubring.mem_top _
  rw [OK, mem_normVS] at hmem
  simp only [map_inv₀, map_natCast, norm_inv] at hmem
  rw [norm_p_kbar, inv_inv] at hmem
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

instance OK_dvr : IsDiscreteValuationRing (OK p K) :=
  ZInQ.NeronLG.isDiscreteValuationRing_of_ne_top _ OK_ne_top

/-- A natural number prime to `p` is a unit of `OK`. -/
theorem isUnit_natCast_OK {n : ℕ} (hn : ¬ p ∣ n) : IsUnit ((n : OK p K)) := by
  have hnorm : ‖(n : Kbar p)‖ = 1 := norm_natCast_kbar hn
  have hn0 : (n : K) ≠ 0 := by
    intro h0
    have : (n : Kbar p) = 0 := by
      have := congrArg ((ιbar p K).comp (algebraMap K (AlgebraicClosure K))) h0
      simpa using this
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hinv : ((n : K))⁻¹ ∈ OK p K := by
    rw [OK, mem_normVS]
    simp only [map_inv₀, map_natCast, norm_inv, hnorm, inv_one, le_refl]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change ((n : OK p K) : K) * ((n : K))⁻¹ = 1
  rw [show ((n : OK p K) : K) = (n : K) from by simp]
  exact mul_inv_cancel₀ hn0

/-- `ιbar ∘ σ' = σ ∘ ιbar` for `σ'` over `decomp σ` (proved, from `resQ_spec`, `decomp_spec`). -/
theorem ιbar_apply {σ : GQp p} {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) (y : AlgebraicClosure K) :
    ιbar p K (σ' y) = σ (ιbar p K y) := by
  obtain ⟨z, rfl⟩ := (eK K).surjective y
  have h1 : σ' (eK K z) = eK K (decomp p σ z) := by
    have := G0Galois.resQ_spec K σ' z
    rw [hσ'] at this
    exact this.symm
  simp only [ιbar, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [h1, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply, decomp_spec]

theorem norm_wild_eq {σ : GQp p} (hσ : σ ∈ wildSet) (u : Kbar p) : ‖σ u‖ = ‖u‖ := by
  by_cases hu : u = 0
  · rw [hu, map_zero]
  have h := hσ u hu
  have : σ u = u + (σ u - u) := by ring
  rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt h),
    max_eq_left (le_of_lt h)]

/-- **A wild `σ'` lies in the inertia group of `wK` (proved).** -/
theorem isInertia_of_wild {σ : GQp p} (hσ : σ ∈ wildSet)
    {σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (hσ' : G0Galois.resQ K σ' = decomp p σ) : PkgI2.IsInertia (wK p K) σ' := by
  have hnorm : ∀ y, ‖ιbar p K (σ' y)‖ = ‖ιbar p K y‖ := fun y => by
    rw [ιbar_apply hσ', norm_wild_eq hσ]
  have hnorm' : ∀ y, ‖ιbar p K (σ'⁻¹ y)‖ = ‖ιbar p K y‖ := fun y => by
    have := hnorm (σ'⁻¹ y)
    rw [show σ' (σ'⁻¹ y) = y from by
      change (σ' * σ'⁻¹) y = y; rw [mul_inv_cancel]; rfl] at this
    exact this.symm
  have hdec : σ' ∈ (wK p K).decompositionSubgroup K := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change ‖ιbar p K (σ'⁻¹ x)‖ ≤ 1 ↔ ‖ιbar p K x‖ ≤ 1
    rw [hnorm']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨σ', hdec⟩ : (wK p K).decompositionSubgroup K) • IsLocalRing.residue (wK p K) a =
    IsLocalRing.residue (wK p K) a
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  set b : wK p K := (⟨σ', hdec⟩ : (wK p K).decompositionSubgroup K) • a - a with hb
  have hbval : (b : AlgebraicClosure K) = σ' a - a := rfl
  have hlt : ‖ιbar p K (b : AlgebraicClosure K)‖ < 1 := by
    rw [hbval, map_sub, ιbar_apply hσ']
    by_cases ha0 : ιbar p K (a : AlgebraicClosure K) = 0
    · rw [ha0, map_zero, sub_zero, norm_zero]; exact zero_lt_one
    · exact lt_of_lt_of_le (hσ _ ha0) a.2
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.1 hu
  have hc' : ιbar p K (b : AlgebraicClosure K) * ιbar p K (c : AlgebraicClosure K) = 1 := by
    rw [← map_mul]
    have := congrArg Subtype.val hc
    simp only [Subring.coe_mul, OneMemClass.coe_one] at this
    rw [show ((b * c : wK p K) : AlgebraicClosure K) = (b : AlgebraicClosure K) * c from rfl] at this
    rw [this, map_one]
  have hcn : ‖ιbar p K (c : AlgebraicClosure K)‖ ≤ 1 := c.2
  have := congrArg norm hc'
  rw [norm_mul, norm_one] at this
  have h0 : 0 ≤ ‖ιbar p K (b : AlgebraicClosure K)‖ := norm_nonneg _
  nlinarith

/-- **`RaynaudPlace` when `A[m]` is `K`-rational, from the leaf R6 (proved).** -/
theorem raynaudPlace_rational (hR6 : ObjBridge.RaynaudCriterion) (A : PkgI3.AbVar K) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m)
    (hrat : ∀ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct τ P = P) :
    RaynaudPlace (p := p) A m := by
  intro σ hσ σ' hσ' _ ℓ hℓ hℓp n x hx
  have hℓp' : ¬ p ∣ ℓ := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  exact hR6 K (OK p K) (wK p K) wK_comap (ObjBridge.toGrp A) m hm3 (isUnit_natCast_OK hpm)
    hrat σ' (isInertia_of_wild hσ hσ') ℓ hℓ (isUnit_natCast_OK hℓp') n x hx

end RaynaudSec

end G15Ram

end

#print axioms G15Ram.isInertia_of_wild
#print axioms G15Ram.raynaudPlace_rational

noncomputable section

/-! ## §8 (local-glue). The packs: G8's data with the local glue replaced by Props on `A/K`

`G8LocalPack` is copied verbatim from scratch/local-data/tail_part.lean (the hypothesis of
local-data's tail `modularConstituent_tail_L`). `G7LocalPackK` asks instead for G7's data
(`G7Out`), G8's output, the clauses, `KerWild`, and the torsion-point Props `TorsFixWild`
(`p ≥ 7`), `TorsFixWildE` (`p ≤ 5`) and `BetaUpper` (`p = 2`) at the primes in `P`. -/

namespace G0ModNewform

open PkgI4 (Qbar GQ GaloisRep)
open PkgI3

-- BEGIN verbatim copy (scratch/local-data/tail_part.lean)
/-- **G8's data for a representation `r` at coefficient prime `ℓ`, with the G4/G7 clauses and
the local glue at the primes `p ∈ P`** (`G15Ram.G7Clauses`, `G15Ram.LocalGlue`). -/
def G8LocalPack (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (a β : GQ → PadicAlgCl ℓ)
    (ε : GQ → GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ Qbar),
    G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧ G15Ram.G7Clauses β ε L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p → @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β L

-- END verbatim copy

/-- **G7's data for `r` at coefficient prime `ℓ`, with the local glue at `p ∈ P` as Props on the
abelian surface `A/K` (GLUE).** -/
def G7LocalPackK (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (7 ≤ p → @G15Ram.TorsFixWild p ⟨hp⟩ K _ _ A ℓ _) ∧
      (p ≤ 5 → @G15Ram.TorsFixWildE p ⟨hp⟩ K _ _ A ℓ _ β L) ∧
      (p = 2 → @G15Ram.BetaUpper p ⟨hp⟩ ℓ _ β (@G15Ram.Lv p ⟨hp⟩ L) U0)

/-- **`G8LocalPack` from `G7LocalPackK` (proved)**, by `G15Ram.localGlue_of_g7`. -/
theorem g8LocalPack_of_K {ℓ : ℕ} [Fact ℓ.Prime] {r : GaloisRep ℓ 2} {P : ℕ → Prop}
    (h : G7LocalPackK ℓ r P) : G8LocalPack ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, a, β, ε, L, h8, hC, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hW, hE, hB⟩ := hloc p hp hP
  exact G15Ram.localGlue_of_g7 h7 hC hK (fun h => G15Ram.tateWildK_of_torsFixWild (hW h))
    (fun h => G15Ram.tateWildKE_of_torsFixWildE (hE h)) hB

/-- **G15's open Prop `G15RamG` from the packs (proved)**: g15-ram's `G15RamG D u` follows from
G7's data for `D.r5` (local glue at `p ≠ 5`) and for `D.r3` (at `p = 5`), and G11's outputs. -/
theorem g15RamG_of_packK {L : Type} [Field L] [NumberField L] {A : AbVar L} (D : ModData L A)
    (u : ℚ) (h5 : G7LocalPackK 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackK 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ := g8LocalPack_of_K h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ := g8LocalPack_of_K h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

/-- **G7's data for `r` with the local glue at `p ∈ P` in leaf-and-bridge form (GLUE).**
At `p ≥ 7`: `RaynaudPlace A 3` (`p ≠ 13`), resp. `RaynaudPlace A 7` (`p = 13`) (R6 at the place,
with `m` prime to `p`; `PtFinite` is proved, `G15Ram.ptFinite`); at
`p ∈ {3, 5}`: `TorsFixWildOdd`; at `p = 2`: `TorsFixWildE` and `BetaTwist2` (which replaces
`BetaUpper`, `G15Ram.betaUpper_of_twist`). With the leaf I2-Tors
and `p ≠ ℓ` on `P`, it gives `G7LocalPackK` (`g7LocalPackK_of_R`). -/
def G7LocalPackR (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (7 ≤ p → p ≠ 13 → @G15Ram.RaynaudPlace p ⟨hp⟩ K _ _ A 3) ∧
      (p = 13 → @G15Ram.RaynaudPlace p ⟨hp⟩ K _ _ A 7) ∧
      (3 ≤ p → p ≤ 5 → @G15Ram.TorsFixWildOdd p ⟨hp⟩ K _ _ A ℓ _ L) ∧
      (p = 2 → @G15Ram.TorsFixWildE p ⟨hp⟩ K _ _ A ℓ _ β L ∧ @G15Ram.BetaTwist2 p ⟨hp⟩ ℓ _ β L)

/-- **`G7LocalPackK` from `G7LocalPackR`, the leaf I2-Tors and `p ≠ ℓ` on `P` (proved).** -/
theorem g7LocalPackK_of_R (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackR ℓ r P) :
    G7LocalPackK ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hR3, hR7, hO, h2⟩ := hloc p hp hP
  refine ⟨fun h7p => ?_, fun h5 => ?_, fun h2' => G15Ram.betaUpper_of_twist hC (h2 h2').2⟩
  · exact G15Ram.torsFixWild_of_raynaud (Ne.symm (hPℓ p hP)) h7p
      (G15Ram.wildIter A) (G15Ram.torsGL_of_leaf hTors A h7.1 3 (by norm_num))
      (G15Ram.torsGL_of_leaf hTors A h7.1 7 (by norm_num)) (hR3 h7p) hR7
  · by_cases hp2 : p = 2
    · exact (h2 hp2).1
    · have h3 : 3 ≤ p := by have := hp.two_le; omega
      exact G15Ram.torsFixWildE_of_odd hp2 hC (hO h3 h5)

/-- **`G15RamG` from the leaf-and-bridge packs and I2-Tors (proved).** -/
theorem g15RamG_of_packR (hTors : ObjBridge.TorsionStructure) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackR 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackR 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u :=
  g15RamG_of_packK D u (g7LocalPackK_of_R hTors (fun _ h => h) h5)
    (g7LocalPackK_of_R hTors (fun p h => by rw [h]; norm_num) h3) h11₅ h11₃

end G0ModNewform

end

#print axioms G0ModNewform.g8LocalPack_of_K
#print axioms G0ModNewform.g15RamG_of_packK
#print axioms G0ModNewform.g7LocalPackK_of_R
#print axioms G0ModNewform.g15RamG_of_packR
