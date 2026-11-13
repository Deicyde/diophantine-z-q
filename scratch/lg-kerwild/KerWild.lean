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
import ZInQKernel.HDecomp.C10.Link
import ZInQKernel.HDecomp.Descent.B3Assembly
import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Repo.Numerics
import ZInQKernel.HDecomp.Descent.WP3
import ZInQKernel.HDecomp.ModCurves.Defs
import ZInQKernel.HDecomp.Assembly
import ZInQKernel.HDecomp.B3Unram.T32a
import ZInQKernel.Hypotheses.JHeight
import ZInQKernel.HDecomp.Repo.TorsionFree
import ZInQKernel.Multiplication.Certificate.ConstantsProperties
import ZInQKernel.Progressions.Final.Instance
import ZInQKernel.Size.Constants.T

-- BEGIN verbatim body of scratch/local-glue/LocalGlue.lean

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


/-! ## §7c'' (local-glue). Verbatim copy of scratch/unram-tate/BCPoints.lean
(origin/wip/unram-tate) l.14-142 -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace UnramTate

/-- `Spec L → Spec K`. -/
noncomputable abbrev sK (K L : Type) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

theorem specMap_comp_sK :
    Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ sK K L =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq K L Ω]

/-- `Over.map (Spec L → Spec K) (Spec Ω / L) ≅ Spec Ω / K`. -/
noncomputable def ptMapIso :
    (Over.map (sK K L)).obj (PkgI3.AbVar.ptObj (K := L) Ω) ≅ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, PkgI3.AbVar.ptObj, Over.mk_hom]
    erw [Category.id_comp]
    exact (specMap_comp_sK (K := K) (L := L) Ω).symm)

/-- The adjunction bijection is multiplicative. -/
theorem homEquiv_mul (X : Over (Spec (CommRingCat.of L)))
    (p q : (Over.map (sK K L)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (sK K L)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (sK K L)).homEquiv X A.X p *
        (Over.mapPullbackAdj (sK K L)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- **Points of a base change**: `A_L(Ω) ≃* A(Ω)`. -/
noncomputable def bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω where
  toFun p := (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  invFun x := (Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)
  left_inv p := Equiv.apply_symm_apply ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X) p
  right_inv x := by
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)) = x
    rw [Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  map_mul' p q := by
    obtain ⟨p', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective p
    obtain ⟨q', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective q
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
        ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X p' *
          (Over.mapPullbackAdj (sK K L)).homEquiv _ A.X q') = _
    rw [← homEquiv_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      MonObj.comp_mul]

/-- `bcPt` is natural for `L`-automorphisms of `Ω`. -/
theorem bcPt_galAct (σ : Ω ≃ₐ[L] Ω) (p : (A.baseChange L).Pt Ω) :
    bcPt A Ω ((A.baseChange L).galAct σ p) = A.galAct (σ.restrictScalars K) (bcPt A Ω p) := by
  show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      (PkgI3.AbVar.galHom σ ≫ p) =
    PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv ≫
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  have hnat := Adjunction.homEquiv_naturality_left_symm (Over.mapPullbackAdj (sK K L))
    (PkgI3.AbVar.galHom σ) (p : PkgI3.AbVar.ptObj Ω ⟶ (Over.pullback (sK K L)).obj A.X)
  have hsq : (ptMapIso Ω).inv ≫ (Over.map (sK K L)).map (PkgI3.AbVar.galHom σ) =
      PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv := by
    apply Over.OverMorphism.ext
    simp [ptMapIso, PkgI3.AbVar.galHom]
    rfl
  erw [hnat]
  rw [← Category.assoc, hsq, Category.assoc]

end BC

section Tr

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- `Spec Ω₂ → Spec Ω` over `K`, for a `K`-isomorphism `φ : Ω ≃ Ω₂`. -/
noncomputable def trHom (φ : Ω ≃ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem trHom_left (φ : Ω ≃ₐ[K] Ω₂) :
    (trHom φ).left = Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) := rfl

theorem trHom_symm_comp (φ : Ω ≃ₐ[K] Ω₂) : trHom φ.symm ≫ trHom φ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (φ.symm : Ω₂ →+* Ω)) ≫
    Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) = 𝟙 (Spec (CommRingCat.of Ω))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (φ.symm : Ω₂ →+* Ω).comp (φ : Ω →+* Ω₂) = RingHom.id Ω by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

theorem trHom_comp_symm (φ : Ω ≃ₐ[K] Ω₂) : trHom φ ≫ trHom φ.symm = 𝟙 _ := by
  simpa using trHom_symm_comp φ.symm

/-- **Transport of points** along `φ : Ω ≃ₐ[K] Ω₂`. -/
noncomputable def trPt (φ : Ω ≃ₐ[K] Ω₂) : A.Pt Ω ≃* A.Pt Ω₂ where
  toFun p := trHom φ ≫ p
  invFun x := trHom φ.symm ≫ x
  left_inv p := by simp [← Category.assoc, trHom_symm_comp]
  right_inv x := by simp [← Category.assoc, trHom_comp_symm]
  map_mul' p q := MonObj.comp_mul _ _ _

/-- `trPt φ` carries the action of `σ` to that of `φσφ⁻¹`. -/
theorem trPt_galAct (φ : Ω ≃ₐ[K] Ω₂) (σ : Ω ≃ₐ[K] Ω) (σ₂ : Ω₂ ≃ₐ[K] Ω₂)
    (h : ∀ x, σ₂ (φ x) = φ (σ x)) (p : A.Pt Ω) :
    trPt A φ (A.galAct σ p) = A.galAct σ₂ (trPt A φ p) := by
  show trHom φ ≫ PkgI3.AbVar.galHom σ ≫ p = PkgI3.AbVar.galHom σ₂ ≫ trHom φ ≫ p
  have hsq : trHom φ ≫ PkgI3.AbVar.galHom σ = PkgI3.AbVar.galHom σ₂ ≫ trHom φ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ₂ : Ω₂ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x).symm
  rw [← Category.assoc, ← Category.assoc, hsq]

end Tr

end UnramTate

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


/-! ### The general case: R6 over the field of `A[m]`, via the base change of `A` -/

section RaynaudGen

variable {p : ℕ} [Fact p.Prime]

/-- `normVS f ≠ ⊤` for a map of a field to `ℚ̄_p` (`1/p ∉`). -/
theorem normVS_ne_top {F : Type} [Field F] [CharZero F] (f : F →+* Kbar p) : normVS f ≠ ⊤ := by
  intro h
  have hmem : ((p : F))⁻¹ ∈ normVS f := by rw [h]; exact ValuationSubring.mem_top _
  rw [mem_normVS] at hmem
  simp only [map_inv₀, map_natCast, norm_inv] at hmem
  rw [norm_p_kbar, inv_inv] at hmem
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  linarith

/-- A natural number prime to `p` is a unit of `normVS f`. -/
theorem isUnit_natCast_normVS {F : Type} [Field F] (f : F →+* Kbar p) {n : ℕ} (hn : ¬ p ∣ n) :
    IsUnit ((n : normVS f)) := by
  have hnorm : ‖(n : Kbar p)‖ = 1 := norm_natCast_kbar hn
  have hn0 : (n : F) ≠ 0 := by
    intro h0
    have : (n : Kbar p) = 0 := by simpa using congrArg f h0
    rw [this, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hinv : ((n : F))⁻¹ ∈ normVS f := by
    rw [mem_normVS]
    simp only [map_inv₀, map_natCast, norm_inv, hnorm, inv_one, le_refl]
  refine isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext ?_⟩
  change ((n : normVS f) : F) * ((n : F))⁻¹ = 1
  rw [show ((n : normVS f) : F) = (n : F) from by simp]
  exact mul_inv_cancel₀ hn0

/-- **Wild elements are inertial (general form, proved).** If `f ∘ τ = σ ∘ f` with `σ` wild, then
`τ` lies in the inertia group of `normVS f`. -/
theorem isInertia_of_wild_gen {K₀ Ω : Type} [Field K₀] [Field Ω] [Algebra K₀ Ω]
    (f : Ω →+* Kbar p) {σ : GQp p} (hσ : σ ∈ wildSet) (τ : Ω ≃ₐ[K₀] Ω)
    (hf : ∀ y, f (τ y) = σ (f y)) : PkgI2.IsInertia (normVS f) τ := by
  have hnorm : ∀ y, ‖f (τ y)‖ = ‖f y‖ := fun y => by rw [hf, norm_wild_eq hσ]
  have hnorm' : ∀ y, ‖f (τ⁻¹ y)‖ = ‖f y‖ := fun y => by
    have := hnorm (τ⁻¹ y)
    rw [show τ (τ⁻¹ y) = y from by
      change (τ * τ⁻¹) y = y; rw [mul_inv_cancel]; rfl] at this
    exact this.symm
  have hdec : τ ∈ (normVS f).decompositionSubgroup K₀ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    change ‖f (τ⁻¹ x)‖ ≤ 1 ↔ ‖f x‖ ≤ 1
    rw [hnorm']
  refine ⟨hdec, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨τ, hdec⟩ : (normVS f).decompositionSubgroup K₀) • IsLocalRing.residue (normVS f) a =
    IsLocalRing.residue (normVS f) a
  rw [← IsLocalRing.ResidueField.residue_smul]
  apply Ideal.Quotient.eq.mpr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  set b : normVS f := (⟨τ, hdec⟩ : (normVS f).decompositionSubgroup K₀) • a - a with hb
  have hbval : (b : Ω) = τ a - a := rfl
  have hlt : ‖f (b : Ω)‖ < 1 := by
    rw [hbval, map_sub, hf]
    by_cases ha0 : f (a : Ω) = 0
    · rw [ha0, map_zero, sub_zero, norm_zero]; exact zero_lt_one
    · exact lt_of_lt_of_le (hσ _ ha0) a.2
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.1 hu
  have hc' : f (b : Ω) * f (c : Ω) = 1 := by
    rw [← map_mul]
    have := congrArg Subtype.val hc
    simp only [Subring.coe_mul, OneMemClass.coe_one] at this
    rw [show ((b * c : normVS f) : Ω) = (b : Ω) * c from rfl] at this
    rw [this, map_one]
  have hcn : ‖f (c : Ω)‖ ≤ 1 := c.2
  have := congrArg norm hc'
  rw [norm_mul, norm_one] at this
  have h0 : 0 ≤ ‖f (b : Ω)‖ := norm_nonneg _
  nlinarith

variable {K : Type} [Field K] [NumberField K]

/-- The stabilizer of `A(K̄)[m]` in `G_K`. -/
def torsStab (A : PkgI3.AbVar K) (m : ℕ) :
    Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  carrier := {τ | ∀ P : A.Pt (AlgebraicClosure K), P ^ m = 1 → A.galAct τ P = P}
  mul_mem' {a b} ha hb P hP := by
    rw [← galAct_galAct, hb P hP, ha P hP]
  one_mem' P _ := by
    change PkgI3.AbVar.galHom 1 ≫ P = P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  inv_mem' {a} ha P hP := by
    calc A.galAct a⁻¹ P = A.galAct a⁻¹ (A.galAct a P) := by rw [ha P hP]
      _ = P := galAct_inv_galAct A a P

/-- The stabilizer of `A[m]` contains `G_{F'}` for a finite `F'/K` (from `ptFinite`, `A[m]`
finite by I2-Tors). -/
theorem exists_fin_le_torsStab (A : PkgI3.AbVar K) (m : ℕ) [NeZero m] (hT : TorsGL A m) :
    ∃ F' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K F' ∧
      F'.fixingSubgroup ≤ torsStab A m := by
  obtain ⟨e, -⟩ := hT
  haveI : Finite {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} := Finite.of_equiv _ e.symm
  choose F hF hP using fun P : {P : A.Pt (AlgebraicClosure K) | P ^ m = 1} => ptFinite A P.1
  haveI : ∀ i, FiniteDimensional K (F i) := hF
  refine ⟨⨆ i, F i, inferInstance, fun τ hτ P hPm => ?_⟩
  refine hP ⟨P, hPm⟩ τ (fun x hx => ?_)
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
  exact hτ x ((le_iSup F ⟨P, hPm⟩) hx)

/-- **`RaynaudPlace` from the leaves R6 and I2-Tors (proved), for `dim A = 2`, `3 ≤ m`,
`p ∤ m`.** R6 is applied over `F = K(A[m])` (the fixed field of the stabilizer of `A[m]`, finite
by `ptFinite`) to the base change `A_F`, with the valuation rings at the place of `embP`
transported along `K̄ ≅ F̄`; points of `A_F` are those of `A` (`bcPt`, `trPt`, copied from
scratch/unram-tate). -/
theorem raynaudPlace_of_R6 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (A : PkgI3.AbVar K) (hdim : A.dim = 2) {m : ℕ}
    (hm3 : 3 ≤ m) (hpm : ¬ p ∣ m) : RaynaudPlace (p := p) A m := by
  intro σ hσ σ' hσ' hfix ℓ hℓ hℓp n x hx
  set σg : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ' with hσg
  haveI : NeZero m := ⟨by omega⟩
  set H := torsStab A m with hHdef
  obtain ⟨F', hF'fd, hF'H⟩ := exists_fin_le_torsStab A m (torsGL_of_leaf hTors A hdim m (by omega))
  have hHopen : IsOpen (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isOpen_mono hF'H (IntermediateField.fixingSubgroup_isOpen F')
  have hHclosed : IsClosed (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :=
    Subgroup.isClosed_of_isOpen H hHopen
  set F : IntermediateField K (AlgebraicClosure K) := IntermediateField.fixedField H with hFdef
  have hFH : F.fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hFF' : F ≤ F' := by
    intro y hy
    rw [← InfiniteGalois.fixedField_fixingSubgroup F']
    rw [IntermediateField.mem_fixedField_iff] at hy ⊢
    exact fun τ hτ => hy τ (hF'H hτ)
  haveI : FiniteDimensional K F :=
    Module.Finite.of_injective (IntermediateField.inclusion hFF').toLinearMap
      (IntermediateField.inclusion hFF').injective
  haveI : FiniteDimensional ℚ F := Module.Finite.trans K F
  haveI : NumberField F := ⟨⟩
  -- `σ'` fixes `F`
  have hσ'F : ∀ y ∈ F, σg y = y := fun y hy =>
    ((IntermediateField.mem_fixedField_iff _ _).mp hy) σg hfix
  have hℓp' : ¬ p ∣ ℓ := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq Fact.out hℓ).mp h).symm
  -- `K̄` is an algebraic closure of `F`
  haveI : IsAlgClosure F (AlgebraicClosure K) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) (L := F) (A := AlgebraicClosure K)⟩
  let Ω := AlgebraicClosure F
  let ψ : Ω ≃ₐ[F] AlgebraicClosure K := IsAlgClosure.equiv F Ω (AlgebraicClosure K)
  let σF : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K :=
    { σg.toRingEquiv with commutes' := fun c => hσ'F c c.2 }
  let σ₁ : Ω ≃ₐ[F] Ω := (ψ.trans σF).trans ψ.symm
  have hσ₁ : ∀ y, ψ (σ₁ y) = σg (ψ y) := fun y => by
    simp only [σ₁, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
    rfl
  let f₁ : Ω →+* Kbar p := (ιbar p K).comp (ψ : Ω →+* AlgebraicClosure K)
  have hf₁ : ∀ y, f₁ (σ₁ y) = σ (f₁ y) := fun y => by
    change ιbar p K (ψ (σ₁ y)) = σ (ιbar p K (ψ y))
    rw [hσ₁ y]
    exact ιbar_apply (σ' := σg) hσ' (ψ y)
  let w₁ : ValuationSubring Ω := normVS f₁
  let O₁ : ValuationSubring F := normVS (f₁.comp (algebraMap F Ω))
  have hw₁ : w₁.comap (algebraMap F Ω) = O₁ := by ext; exact Iff.rfl
  haveI : IsDiscreteValuationRing O₁ :=
    ZInQ.NeronLG.isDiscreteValuationRing_of_ne_top _ (normVS_ne_top _)
  -- points of `A_F` over `Ω` are points of `A` over `K̄`
  let A₁ : PkgI3.AbVar F := A.baseChange F
  let ψK : Ω ≃ₐ[K] AlgebraicClosure K := ψ.restrictScalars K
  let Φ : A₁.Pt Ω ≃* A.Pt (AlgebraicClosure K) :=
    (UnramTate.bcPt A Ω).trans (UnramTate.trPt A ψK)
  have hΦ : ∀ (τ₁ : Ω ≃ₐ[F] Ω) (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
      (∀ y, τ (ψ y) = ψ (τ₁ y)) → ∀ z, Φ (A₁.galAct τ₁ z) = A.galAct τ (Φ z) := by
    intro τ₁ τ h z
    change UnramTate.trPt A ψK (UnramTate.bcPt A Ω (A₁.galAct τ₁ z)) =
      A.galAct τ (UnramTate.trPt A ψK (UnramTate.bcPt A Ω z))
    rw [UnramTate.bcPt_galAct, UnramTate.trPt_galAct A ψK (τ₁.restrictScalars K) τ h]
  have hrat : ∀ τ₁ : Ω ≃ₐ[F] Ω, ∀ z ∈ PkgI2.torsion (ObjBridge.toGrp A₁) Ω m,
      PkgI2.galAct (ObjBridge.toGrp A₁) τ₁ z = z := by
    intro τ₁ z₀ hz
    let z : A₁.Pt Ω := z₀
    change A₁.galAct τ₁ z = z
    let τF : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K := (ψ.symm.trans τ₁).trans ψ
    let τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τF.restrictScalars K
    have hτ : ∀ y, τ (ψ y) = ψ (τ₁ y) := fun y => by
      change ψ (τ₁ (ψ.symm (ψ y))) = ψ (τ₁ y)
      rw [AlgEquiv.symm_apply_apply]
    have hτH : τ ∈ H := by
      rw [← hFH, IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      exact τF.commutes ⟨y, hy⟩
    have hz' : z ^ m = 1 := hz
    have hzm : (Φ z) ^ m = 1 := by rw [← map_pow, hz', map_one]
    have h1 := hΦ τ₁ τ hτ z
    rw [hτH (Φ z) hzm] at h1
    exact Φ.injective h1
  have hxm : (Φ.symm x) ^ (ℓ ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have hU := hR6 F O₁ w₁ hw₁ (ObjBridge.toGrp A₁) m hm3 (isUnit_natCast_normVS _ hpm) hrat σ₁
    (isInertia_of_wild_gen f₁ hσ σ₁ hf₁) ℓ hℓ (isUnit_natCast_normVS _ hℓp') n (Φ.symm x) hxm
  have hU' : A₁.galAct σ₁ (A₁.galAct σ₁ (Φ.symm x)) * (A₁.galAct σ₁ (Φ.symm x))⁻¹ *
      (A₁.galAct σ₁ (Φ.symm x))⁻¹ * Φ.symm x = 1 := hU
  have hcomm : ∀ z, Φ (A₁.galAct σ₁ z) = A.galAct σg (Φ z) :=
    hΦ σ₁ σg (fun y => (hσ₁ y).symm)
  have h2 := congrArg Φ hU'
  simp only [map_one, map_mul, map_inv, hcomm, MulEquiv.apply_symm_apply] at h2
  exact h2

/-- **`TateWildK` at `p ≥ 7`, `p ≠ ℓ`, from the leaves R6 and I2-Tors alone (proved).**
`m = 3` for `p ≠ 13`, `m = 7` for `p = 13` (`raynaudPlace_of_R6`, `tateWildK_of_raynaud`). -/
theorem tateWildK_of_R6 (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    {A : PkgI3.AbVar K} (hdim : A.dim = 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (h7 : 7 ≤ p) :
    TateWildK (p := p) A ℓ := by
  have hp : p.Prime := Fact.out
  refine tateWildK_of_raynaud hℓp h7 hTors hdim (fun _ => raynaudPlace_of_R6 hR6 hTors A hdim
    (by norm_num) ?_) (fun h13 => raynaudPlace_of_R6 hR6 hTors A hdim (by norm_num) ?_)
  · intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  · intro h
    rw [h13] at h
    norm_num at h

/-- **`LocalGlue` on G7's data from the leaves R6 and I2-Tors (proved), with the remaining glue
`KerWild`, `TateWildKE` (`p ≤ 5`) and `BetaTwist2` (`p = 2`).** At `p ≥ 7`, `p ≠ ℓ`, no glue is
left. -/
theorem localGlue_of_leaves (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_g7_twist h7 hC hK (fun h => tateWildK_of_R6 hR6 hTors h7.1 (Ne.symm hpℓ) h) hE hB

end RaynaudGen

end G15Ram

end

namespace RQ

theorem numberField_of_fd (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] : NumberField L := ⟨⟩

/-- An element of `G_ℚ` as an automorphism of `ℚ̄`. -/
def actQ (τ : Field.absoluteGaloisGroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := τ
/-- An element of `G_K` as an automorphism of `\bar K`. -/
def actK {K : Type} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- `resQ K σ` is `σ` transported along the embedding `g : ℚ̄ → \bar K` that
`Field.absoluteGaloisGroup.map` chooses. -/
theorem resQ_comm' (K : Type) [Field K] [NumberField K] :
    ∃ g : AlgebraicClosure ℚ →+* AlgebraicClosure K, ∀ σ x,
      g (actQ (G0Galois.resQ K σ) x) = actK σ (g x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  let g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := g.toAlgebra
  haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ) (AlgebraicClosure ℚ) x

/-- **`ResQRange` proved**: for finite Galois `L ⊆ ℚ̄`, the image of `resQ L` is `Fix(L)`
(normality of `L` gives `g(L) = L` inside `\bar L`; `g` is bijective because `\bar L/ℚ` is
algebraic). -/
theorem resQ_range (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] [IsGalois ℚ L] :
    (@G0Galois.resQ L _ (numberField_of_fd L)).range = L.fixingSubgroup := by
  haveI := numberField_of_fd L
  obtain ⟨g0, hcomm⟩ := resQ_comm' L
  let g : PkgI4.Qbar →ₐ[ℚ] AlgebraicClosure L := g0.toRatAlgHom
  have hg : ∀ x, g x = g0 x := fun _ => rfl
  -- `g` is bijective (`AlgebraicClosure L` is algebraic over `ℚ`)
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L) := by
    haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
    haveI : Algebra.IsAlgebraic L (AlgebraicClosure L) := AlgebraicClosure.isAlgebraic L
    exact Algebra.IsAlgebraic.trans ℚ L (AlgebraicClosure L)
  have hgbij : Function.Bijective g := by
    letI : Algebra PkgI4.Qbar (AlgebraicClosure L) := g.toAlgebra
    haveI : IsScalarTower ℚ PkgI4.Qbar (AlgebraicClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L) := inferInstance
    haveI : Algebra.IsIntegral PkgI4.Qbar (AlgebraicClosure L) := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : L →ₐ[ℚ] AlgebraicClosure L := IsScalarTower.toAlgHom ℚ L (AlgebraicClosure L)
  let e : L ≃ₐ[ℚ] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal ℚ ψ.fieldRange := Normal.of_algEquiv e
  let f : ψ.fieldRange →ₐ[ℚ] AlgebraicClosure L := (g.comp L.val).comp e.symm.toAlgHom
  have hf := AlgHom.fieldRange_of_normal f
  have hgL : ∀ x : L, ∃ y : L, g x = ψ y := by
    intro x
    have hx : g x ∈ f.fieldRange := ⟨e x, by simp [f]⟩
    rw [hf] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy.symm⟩
  have hLg : ∀ y : L, ∃ x : L, g x = ψ y := by
    intro y
    have hy : ψ y ∈ f.fieldRange := by rw [hf]; exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hy
    exact ⟨e.symm z, by simpa [f] using hz⟩
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    refine (IntermediateField.mem_fixingSubgroup_iff L (actQ (G0Galois.resQ L σ))).mpr ?_
    intro x hx
    apply g.toRingHom.injective
    show g (actQ (G0Galois.resQ L σ) x) = g x
    rw [hg, hcomm σ x, ← hg]
    obtain ⟨y, hy⟩ := hgL ⟨x, hx⟩
    have hy' : g x = ψ y := hy
    rw [hy']
    exact (actK σ).commutes y
  · intro hτ'
    have hτ := (IntermediateField.mem_fixingSubgroup_iff L (actQ τ)).mp hτ'
    let eg : PkgI4.Qbar ≃+* AlgebraicClosure L := RingEquiv.ofBijective g.toRingHom hgbij
    let τ' : PkgI4.Qbar ≃ₐ[ℚ] PkgI4.Qbar := τ
    let σ₀ : AlgebraicClosure L ≃+* AlgebraicClosure L := (eg.symm.trans τ'.toRingEquiv).trans eg
    have hσ₀ : ∀ x, σ₀ (g x) = g (τ' x) := by
      intro x
      show eg (τ' (eg.symm (eg x))) = g (τ' x)
      rw [RingEquiv.symm_apply_apply]; rfl
    have hfix : ∀ y : L, σ₀ (algebraMap L (AlgebraicClosure L) y) =
        algebraMap L (AlgebraicClosure L) y := by
      intro y
      obtain ⟨x, hx⟩ := hLg y
      have hx' : g x = algebraMap L (AlgebraicClosure L) y := hx
      rw [← hx', hσ₀, show τ' (x : PkgI4.Qbar) = x from hτ x x.2]
    let σ : Field.absoluteGaloisGroup L := AlgEquiv.ofRingEquiv (f := σ₀) hfix
    refine ⟨σ, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply g.toRingHom.injective
    show g (actQ (G0Galois.resQ L σ) x) = g (τ' x)
    rw [hg, hcomm σ x, ← hg]
    exact hσ₀ x

end RQ

/-! ## §7d (local-glue). `p ≤ 5`: the torsion field of a model over `L` (proved from a descent Prop)

At `p ∈ {2, 3, 5}` the trick of §7 (`p ∤ |GL₄(𝔽_m)|`) is not available (finding G3), and Glazer
uses the model `A_L` over the Hom field `L` (N5 L813-818): `E = L_v(A_L[m])`, of degree
`≤ |GL₄(𝔽_m)|` over `L_v`. Here:
* `DescentPts A L` (GLUE, new): `L/ℚ` is Galois and `A` has a model `A₀` over `L` with
  `dim A₀ = 2` and a group isomorphism `A₀(L̄) ≅ A(K̄)` intertwining `σ₀ ∈ G_L` with `σ' ∈ G_K`
  whenever both restrict to the same element of `G_ℚ`;
* `index_torsStab_le` (proved): `[G_L : Stab(A₀[q])] ≤ |GL₄(𝔽_q)|` (I2-Tors);
* `torsFix_of_descent` (proved): from R6, I2-Tors and `DescentPts`, for `q ≠ p` prime, `q ≥ 3`, and
  any finite `M ⊇ L_v`, there is `E ⊇ M` with `[E:ℚ_p] ≤ |GL₄(𝔽_q)|·[M:ℚ_p]` on whose wild inertia
  every `ℓⁿ`-torsion point of `A(K̄)` is fixed (`ℓ ≠ p`). `E` is the fixed field of the open
  subgroup `decomp⁻¹(resQ_L(Stab)) ∩ G_M`; its degree is the index (Mathlib's
  `finrank_eq_fixingSubgroup_index`);
* `torsFixWildOdd_of_descent`, `torsFixWildE_two_of_descent`, `tateWildKE_of_descent`,
  `localGlue_of_descent` (proved). -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond
open CategoryTheory MonObj

section DescentSec

variable {p : ℕ} [Fact p.Prime]

attribute [local instance] RQ.numberField_of_fd

/-- **Glue (the descent of `A` to the Hom field `L`; N5 L813-818; g0-mod-field: `G7Data` carries
`A : AbVar L` and `TateBridge` takes `A_{L'}` to be its base change to `L'`).** `L/ℚ` is Galois, and
`A/K` has a model `A₀/L` (`dim A₀ = 2`) with a group isomorphism `φ : A₀(L̄) ≅ A(K̄)` such that
`φ ∘ σ₀ = σ' ∘ φ` whenever `σ₀ ∈ G_L` and `σ' ∈ G_K` have the same image in `G_ℚ` (`resQ`). For
`K = L'` and `A = (A₀)_{L'}` this is the base change of points (`bcPt`) along an identification
`L̄ ≅ L̄'` compatible with `qEmb L` and `qEmb L'`; if Mathlib's choices of the embeddings
`L ↪ ℚ̄` (inside `resQ L`, `resQ L'`) differ on `L` by `γ ∈ Gal(L/ℚ)`, the model is the conjugate
`A₀ ×_{L,γ} L`, so the existential is still met. -/
def DescentPts {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (L : IntermediateField ℚ PkgI4.Qbar) [FiniteDimensional ℚ L] : Prop :=
  IsGalois ℚ L ∧
  ∃ (A₀ : PkgI3.AbVar L) (φ : A₀.Pt (AlgebraicClosure L) ≃* A.Pt (AlgebraicClosure K)),
    A₀.dim = 2 ∧ ∀ (σ₀ : Field.absoluteGaloisGroup L) (σ' : Field.absoluteGaloisGroup K),
      G0Galois.resQ L σ₀ = G0Galois.resQ K σ' →
        ∀ P : A₀.Pt (AlgebraicClosure L), φ (A₀.galAct σ₀ P) = A.galAct σ' (φ P)

variable {K : Type} [Field K] [NumberField K]

/-- **`[G_K : Stab(A[q])] ≤ |GL₄(𝔽_q)|` (proved)** from `A(K̄)[q] ≅ (ℤ/q)⁴` (`TorsGL`): the
action on `A[q]` is a homomorphism `G_K → GL(𝔽_q⁴)` whose kernel is the stabilizer. -/
theorem index_torsStab_le (A : PkgI3.AbVar K) (q : ℕ) [Fact q.Prime] (hT : TorsGL A q) :
    (torsStab A q).index ≠ 0 ∧
      (torsStab A q).index ≤ Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) := by
  set S := {P : A.Pt (AlgebraicClosure K) | P ^ q = 1} with hSdef
  obtain ⟨e, he⟩ := hT
  have hS : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : S), A.galAct σ x.1 ∈ S :=
    fun σ x => by
      have hx : x.1 ^ q = 1 := x.2
      show (A.galAct σ x.1) ^ q = 1
      rw [← map_pow, hx, map_one]
  have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := fun x hx y hy => by
    simp only [hSdef, Set.mem_setOf_eq] at hx hy ⊢
    rw [mul_pow, hx, hy, _root_.one_mul]
  let f : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) → (Fin 4 → ZMod q) → (Fin 4 → ZMod q) :=
    fun σ v => e ⟨A.galAct σ (e.symm v).1, hS σ _⟩
  have hadd : ∀ σ a b, f σ (a + b) = f σ a + f σ b := by
    intro σ a b
    set x := e.symm a
    set y := e.symm b
    have hxy : e.symm (a + b) = ⟨x.1 * y.1, hSmul _ x.2 _ y.2⟩ := by
      apply e.injective
      rw [Equiv.apply_symm_apply, he x y, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have h1 : (⟨A.galAct σ (e.symm (a + b)).1, hS σ _⟩ : S) =
        ⟨(A.galAct σ x.1) * (A.galAct σ y.1), hSmul _ (hS σ x) _ (hS σ y)⟩ := by
      apply Subtype.ext
      simp only [hxy, map_mul]
    show e ⟨A.galAct σ (e.symm (a + b)).1, hS σ _⟩ = e ⟨A.galAct σ x.1, hS σ x⟩ +
      e ⟨A.galAct σ y.1, hS σ y⟩
    rw [h1, he ⟨A.galAct σ x.1, hS σ x⟩ ⟨A.galAct σ y.1, hS σ y⟩]
  have hmul : ∀ σ τ v, f (σ * τ) v = f σ (f τ v) := by
    intro σ τ v
    show e ⟨A.galAct (σ * τ) (e.symm v).1, _⟩ =
      e ⟨A.galAct σ (e.symm (e ⟨A.galAct τ (e.symm v).1, _⟩)).1, _⟩
    congr 1
    apply Subtype.ext
    simp only [Equiv.symm_apply_apply]
    rw [galAct_galAct]
  have hone : ∀ v, f 1 v = v := by
    intro v
    show e ⟨A.galAct 1 (e.symm v).1, _⟩ = v
    have h1 : (⟨A.galAct 1 (e.symm v).1, hS 1 _⟩ : S) = e.symm v := by
      apply Subtype.ext
      change PkgI3.AbVar.galHom 1 ≫ (e.symm v).1 = (e.symm v).1
      rw [PkgI3.AbVar.galHom_one, Category.id_comp]
    rw [h1, Equiv.apply_symm_apply]
  let fL : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →
      ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) := fun σ =>
    { ((AddMonoidHom.mk' (f σ) (hadd σ)).toZModLinearMap q) with
      invFun := f σ⁻¹
      left_inv := fun v => by
        change f σ⁻¹ (f σ v) = v
        rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun v => by
        change f σ (f σ⁻¹ v) = v
        rw [← hmul, mul_inv_cancel, hone] }
  let ρ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
      ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) :=
    { toFun := fL
      map_one' := LinearEquiv.ext hone
      map_mul' := fun σ τ => LinearEquiv.ext (hmul σ τ) }
  have hker : ρ.ker ≤ torsStab A q := by
    intro σ hσ P hP
    have h1 : f σ (e ⟨P, hP⟩) = e ⟨P, hP⟩ := by
      have := congrArg (fun g : (Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q) => g (e ⟨P, hP⟩))
        (MonoidHom.mem_ker.mp hσ)
      exact this
    have h2 := e.injective h1
    simp only [Equiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2
  set N := Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) with hN
  have hcard : Nat.card ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) = N :=
    (Nat.card_congr (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod q)
      (Fin 4 → ZMod q)).toEquiv).symm.trans
      (Nat.card_congr (Matrix.GeneralLinearGroup.toLin).toEquiv).symm
  haveI : Finite ((Fin 4 → ZMod q) ≃ₗ[ZMod q] (Fin 4 → ZMod q)) :=
    Finite.of_equiv _ ((Matrix.GeneralLinearGroup.toLin).toEquiv.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod q) (Fin 4 → ZMod q)).toEquiv)
  have hkerI : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have hr1 : 0 < Nat.card ρ.range := Nat.card_pos
  have hrN : Nat.card ρ.range ≤ N := hcard ▸ Subgroup.card_le_card_group _
  have hdvd : (torsStab A q).index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hker
  have hpos : 0 < (torsStab A q).index := Nat.pos_of_dvd_of_pos hdvd (hkerI ▸ hr1)
  exact ⟨hpos.ne', (Nat.le_of_dvd (hkerI ▸ hr1) hdvd).trans (hkerI ▸ hrN)⟩

/-- `resQ K` is injective (proved): `qEmb K ∘ resQ K τ = τ ∘ qEmb K` and `qEmb K` is onto. -/
theorem resQ_injective' : Function.Injective (G0Galois.resQ K) := by
  intro τ₁ τ₂ h
  let τ₁' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τ₁
  let τ₂' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τ₂
  show τ₁' = τ₂'
  apply AlgEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := qEmbRing_surjective K y
  have h1 := G0Galois.resQ_spec K τ₁' x
  have h2 := G0Galois.resQ_spec K τ₂' x
  change τ₁' (G0Galois.qEmbRing K x) = τ₂' (G0Galois.qEmbRing K x)
  rw [← h1, ← h2]
  exact congrArg (fun g => G0Galois.qEmbRing K (g x)) h

/-- **The torsion field of the model over `L` (proved)** from the leaves R6 (`raynaudPlace_of_R6`)
and I2-Tors and the glue `DescentPts`. For a prime `q ≥ 3`, `q ≠ p`, and a finite `M ⊇ L_v`,
there is a finite `E ⊇ M` with `[E:ℚ_p] ≤ |GL₄(𝔽_q)|·[M:ℚ_p]` such that every wild `σ ∈ G_E` fixes
every `ℓⁿ`-torsion point of `A(K̄)` through `G_K` (`ℓ ≠ p`). `E` is the fixed field of
`H = decomp⁻¹(resQ_L(Stab(A₀[q]))) ∩ G_M`, which is open (it contains `G_{E₀}`, `E₀` generated over
`M` by a basis of `L(A₀[q])`, finite by `ptFinite`), and `[E:ℚ_p] = [G_{ℚ_p} : H]`. For wild
`σ ∈ G_E`, `decomp σ = resQ_L σ₀` with `σ₀` fixing `A₀[q]`; Raynaud (`RaynaudPlace A₀ q`) and the
`p`-power period (`wildIter`) give that `σ₀` fixes `A₀[ℓⁿ]` (D2), and `φ` carries this to `A`. -/
theorem torsFix_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (q : ℕ) [Fact q.Prime] (hq3 : 3 ≤ q) (hpq : q ≠ p)
    (M : Fld p) [FiniteDimensional ℚ_[p] M] (hLvM : Lv (p := p) L ≤ M) :
    ∃ E : Fld p, FiniteDimensional ℚ_[p] E ∧ M ≤ E ∧
      Module.finrank ℚ_[p] E ≤
        Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) * Module.finrank ℚ_[p] M ∧
      ∀ σ ∈ fixSet E ∩ wildSet, ∀ σ' : Field.absoluteGaloisGroup K,
        G0Galois.resQ K σ' = decomp p σ →
          ∀ (n : ℕ) (P : A.Pt (AlgebraicClosure K)), P ^ (ℓ ^ n) = 1 → A.galAct σ' P = P := by
  obtain ⟨hGal, A₀, φ, hdim₀, hφ⟩ := hD
  have hp : p.Prime := Fact.out
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp Fact.out).mp h).symm
  have hT₀ : TorsGL A₀ q := torsGL_of_leaf hTors A₀ hdim₀ q (by omega)
  obtain ⟨hidx0, hidx⟩ := index_torsStab_le A₀ q hT₀
  obtain ⟨F', hF'fd, hF'⟩ := exists_fin_le_torsStab A₀ q hT₀
  let Stab : Subgroup (Field.absoluteGaloisGroup L) := torsStab A₀ q
  let ρL : Field.absoluteGaloisGroup L →* GQ := G0Galois.resQ L
  have hρinj : Function.Injective ρL := resQ_injective'
  have hrange : ρL.range = L.fixingSubgroup := RQ.resQ_range L
  let Hq : Subgroup GQ := Stab.map ρL
  let GM : Subgroup (GQp p) := M.fixingSubgroup
  let H : Subgroup (GQp p) := Hq.comap (decomp p) ⊓ GM
  -- `decomp` of `G_M` fixes `L`
  have hdecL : ∀ σ : GQp p, σ ∈ fixSet M → decomp p σ ∈ L.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).mpr
      (decomp_fix_of_le (fun x hx => hLvM (embP_mem_Lv hx)) hσ)
  -- the open subgroup `G_{E₀}` inside `H`
  haveI : FiniteDimensional L F' := hF'fd
  haveI : Module.Free L F' := Module.Free.of_divisionRing L F'
  let b := Module.finBasis L F'
  let eL : AlgebraicClosure ℚ ≃+* AlgebraicClosure L :=
    RingEquiv.ofBijective (G0Galois.qEmbRing L)
      ⟨(G0Galois.qEmbRing L).injective, qEmbRing_surjective L⟩
  let S₀ : Set (Kbar p) := Set.range fun i => embP (eL.symm (b i : AlgebraicClosure L))
  haveI : Finite S₀ := Set.finite_range _ |>.to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] S₀) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E₀ : Fld p := M ⊔ IntermediateField.adjoin ℚ_[p] S₀
  have hE₀H : E₀.fixingSubgroup ≤ H := by
    intro σ hσ
    have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ
    have hσM : σ ∈ fixSet M := fun x hx => hσ' x (le_sup_left (a := M) hx)
    have hσS : ∀ i, decomp p σ (eL.symm (b i : AlgebraicClosure L)) =
        eL.symm (b i : AlgebraicClosure L) := by
      intro i
      apply (embP (p := p)).injective
      rw [decomp_spec]
      exact hσ' _ (le_sup_right (a := M)
        (IntermediateField.subset_adjoin ℚ_[p] S₀ ⟨i, rfl⟩))
    obtain ⟨σ₀, hσ₀⟩ : decomp p σ ∈ ρL.range := hrange ▸ hdecL σ hσM
    let σ₀' : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L := σ₀
    have hσ₀b : ∀ i, σ₀' (b i : AlgebraicClosure L) = b i := by
      intro i
      have h1 := G0Galois.resQ_spec L σ₀' (eL.symm (b i : AlgebraicClosure L))
      have h2 : G0Galois.qEmbRing L (eL.symm (b i : AlgebraicClosure L)) = b i :=
        eL.apply_symm_apply _
      change G0Galois.qEmbRing L (ρL σ₀ _) = _ at h1
      rw [hσ₀, hσS i, h2] at h1
      exact h1.symm
    have hσ₀F : σ₀' ∈ F'.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      have hsum := b.sum_repr ⟨z, hz⟩
      set c := b.repr ⟨z, hz⟩ with hc
      have hz' : z = ∑ i, c i • (b i : AlgebraicClosure L) := by
        have := congrArg (fun w : F' => (w : AlgebraicClosure L)) hsum
        simp only at this
        rw [← this, IntermediateField.coe_sum]
        rfl
      rw [hz', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, hσ₀b i]
    refine ⟨?_, (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσM⟩
    show decomp p σ ∈ Hq
    exact ⟨σ₀', hF' hσ₀F, hσ₀⟩
  have hHopen : IsOpen (H : Set (GQp p)) :=
    Subgroup.isOpen_mono hE₀H (IntermediateField.fixingSubgroup_isOpen E₀)
  have hHclosed : IsClosed (H : Set (GQp p)) := Subgroup.isClosed_of_isOpen H hHopen
  let E : Fld p := IntermediateField.fixedField H
  have hEH : E.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  -- the index
  have hmapLe : GM.map (decomp p) ≤ ρL.range := by
    rintro _ ⟨σ, hσ, rfl⟩
    rw [hrange]
    exact hdecL σ ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ)
  have hrel1 : Hq.relIndex ρL.range = Stab.index := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hρinj,
      Subgroup.relIndex_top_right]
  have hrel2 : Hq.relIndex (GM.map (decomp p)) ≤ Stab.index := by
    rw [← hrel1]
    exact Subgroup.relIndex_le_of_le_right hmapLe (by rw [hrel1]; exact hidx0)
  have hrel3 : Hq.relIndex (GM.map (decomp p)) ≠ 0 := fun h0 =>
    hidx0 (hrel1 ▸ Subgroup.relIndex_eq_zero_of_le_right hmapLe h0)
  have hHidx : H.index = (Hq.comap (decomp p)).relIndex GM * GM.index := Subgroup.index_inf
  rw [Subgroup.relIndex_comap] at hHidx
  have hMfr : Module.finrank ℚ_[p] M = GM.index :=
    IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) M
  have hEfr : Module.finrank ℚ_[p] E = H.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) E, hEH]
  have hMpos : 0 < Module.finrank ℚ_[p] M := Module.finrank_pos
  have hEpos : 0 < Module.finrank ℚ_[p] E := by
    rw [hEfr, hHidx]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hrel3) (hMfr ▸ hMpos)
  refine ⟨E, Module.finite_of_finrank_pos hEpos, ?_, ?_, ?_⟩
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp (Subgroup.mem_inf.mp hτ).2 x hx
  · rw [hEfr, hHidx, hMfr]
    exact Nat.mul_le_mul_right _ (hrel2.trans hidx)
  · intro σ hσ σ' hσ' n P hP
    have hσE : σ ∈ E.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσ.1
    rw [hEH] at hσE
    obtain ⟨σ₀, hσ₀S, hσ₀⟩ := (Subgroup.mem_inf.mp hσE).1
    have hσ₀' : G0Galois.resQ L σ₀ = decomp p σ := hσ₀
    have hR := raynaudPlace_of_R6 (p := p) hR6 hTors A₀ hdim₀ hq3 hpq'
    set Q := φ.symm P with hQdef
    have hQ : Q ^ (ℓ ^ n) = 1 := by rw [hQdef, ← map_pow, hP, map_one]
    have hu := hR σ hσ.2 σ₀ hσ₀' (fun R hR' => hσ₀S R hR') ℓ Fact.out hℓp n Q hQ
    obtain ⟨a, ha⟩ := wildIter (p := p) A₀ σ hσ.2 σ₀ hσ₀' Q
    have hcop : Nat.Coprime (p ^ a) (ℓ ^ n) :=
      Nat.Coprime.pow a n ((Nat.coprime_primes hp Fact.out).mpr (Ne.symm hℓp))
    have hfix := fixed_of_unipSq_of_iterate' A₀ σ₀ Q ℓ n p a hcop hQ hu ha
    have h1 := hφ σ₀ σ' (hσ₀'.trans hσ'.symm) Q
    rw [hfix, hQdef, MulEquiv.apply_symm_apply] at h1
    exact h1.symm

/-- `|GL₄(𝔽₅)| = G₀ = 116064000000` (proved). -/
theorem card_GL4_five :
    Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 5)) = ZInQ.heightG0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  unfold ZInQ.heightG0
  norm_num

/-- **`TorsFixWildOdd` at every `p ≠ ℓ` (proved)** from the leaves R6, I2-Tors and the glue
`DescentPts`: `torsFix_of_descent` with `M = L_v` and `q = 3` (`q = 5` if `p = 3`);
`|GL₄(𝔽₃)| = 24261120 ≤ G₀` and `|GL₄(𝔽₅)| = G₀` (Glazer's `E = L_v(A_L[3])`, resp. `A_L[5]`). -/
theorem torsFixWildOdd_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : TorsFixWildOdd (p := p) A ℓ L := by
  obtain ⟨hLvfd, -⟩ := Lv_fin (p := p) L
  haveI := hLvfd
  have key : ∃ q : ℕ, ∃ _ : Fact q.Prime, 3 ≤ q ∧ q ≠ p ∧
      Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod q)) ≤ ZInQ.heightG0 := by
    by_cases h3 : p = 3
    · exact ⟨5, ⟨by norm_num⟩, by norm_num, by omega, card_GL4_five.le⟩
    · refine ⟨3, ⟨by norm_num⟩, le_refl _, Ne.symm h3, ?_⟩
      rw [card_GL4_three]
      unfold ZInQ.heightG0
      norm_num
  obtain ⟨q, hq, hq3, hqp, hqN⟩ := key
  obtain ⟨E, hEfd, hLvE, hdeg, hfix⟩ :=
    torsFix_of_descent hR6 hTors hD hℓp q hq3 hqp (Lv (p := p) L) le_rfl
  exact ⟨E, hEfd, hLvE, hdeg.trans (Nat.mul_le_mul_right _ hqN), hfix⟩

/-- **`TorsFixWildE` from `BetaTwist2` (proved; used at `p = 2`, valid for `p ≠ 3`)**:
`torsFix_of_descent` with `q = 3` over `BetaTwist2`'s `M`; `4·|GL₄(𝔽₃)| ≤ G₀`. -/
theorem torsFixWildE_of_twist (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hD : DescentPts A L)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (hp3 : p ≠ 3) {β : GQ → PadicAlgCl ℓ}
    (hB : BetaTwist2 (p := p) β L) : TorsFixWildE (p := p) A ℓ β L := by
  obtain ⟨M, hMfd, hLvM, hMdeg, hMβ⟩ := hB
  haveI := hMfd
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨E, hEfd, hME, hdeg, hfix⟩ :=
    torsFix_of_descent hR6 hTors hD hℓp 3 le_rfl (Ne.symm hp3) M hLvM
  refine ⟨E, hEfd, hLvM.trans hME, ?_, fun σ hσ =>
    ⟨hMβ σ ⟨fun x hx => hσ.1 x (hME hx), hσ.2⟩, hfix σ hσ⟩⟩
  rw [card_GL4_three] at hdeg
  calc Module.finrank ℚ_[p] E ≤ 24261120 * Module.finrank ℚ_[p] M := hdeg
    _ ≤ 24261120 * (4 * Module.finrank ℚ_[p] (Lv (p := p) L)) := Nat.mul_le_mul_left _ hMdeg
    _ = 97044480 * Module.finrank ℚ_[p] (Lv (p := p) L) := by ring
    _ ≤ ZInQ.heightG0 * Module.finrank ℚ_[p] (Lv (p := p) L) :=
        Nat.mul_le_mul_right _ (by unfold ZInQ.heightG0; norm_num)

/-- **`TateWildKE` at every `p ≠ ℓ` (proved)** from R6, I2-Tors, `DescentPts`, G7's clauses and,
at `p = 2`, `BetaTwist2`. -/
theorem tateWildKE_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime]
    {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L] (hC : G7Clauses β ε L)
    (hD : DescentPts A L) (hℓp : ℓ ≠ p) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    TateWildKE (p := p) A ℓ β L := by
  by_cases h2 : p = 2
  · exact tateWildKE_of_torsFixWildE
      (torsFixWildE_of_twist hR6 hTors hD hℓp (by omega) (hB h2))
  · exact tateWildKE_of_torsFixWildE
      (torsFixWildE_of_odd h2 hC (torsFixWildOdd_of_descent hR6 hTors hD hℓp))

/-- **`LocalGlue p Tm a β L` on G7's data (proved)** from the leaves R6 and I2-Tors and the glue
`KerWild` (all `p`), `DescentPts` (`p ≤ 5`) and `BetaTwist2` (`p = 2`). -/
theorem localGlue_of_descent (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    [FiniteDimensional ℚ L] (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hD : p ≤ 5 → DescentPts A L) (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_leaves hR6 hTors hpℓ h7 hC hK
    (fun h5 => tateWildKE_of_descent hR6 hTors hC (hD h5) (Ne.symm hpℓ) hB) hB

/-- **`KerWild` from G7Data's kernel-field clause (proved).** If `L'` is finite Galois,
`G_{L'} = G_L ∩ ker β_ℂ` (g0-mod-field `G7Data`/`G7Out`: `σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`, with
`GQL L = L.fixingSubgroup`), and the `ℚ̄_ℓ`-valued `β` is `ι ∘ β_ℂ` for an injective
`ι : ℂ^× →* ℚ̄_ℓ^×`, then `KerWild L' β L` for G7Out's model field `K = L'`. This is the clause that
g0-assemble's `TateBridge` must add to its output (finding G8). -/
theorem kerWild_of_g7Data {ℓ : ℕ} [Fact ℓ.Prime] {L L' : IntermediateField ℚ PkgI4.Qbar}
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (βC : GQ → ℂˣ)
    (hker : ∀ σ : GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ) (hι : Function.Injective ιC) {β : GQ → PadicAlgCl ℓ}
    (hβ : ∀ g, β g = (ιC (βC g) : PadicAlgCl ℓ)) : KerWild L' β L := by
  intro g hgL hg1
  have h1 : ιC (βC g) = ιC 1 := by
    rw [map_one]
    exact Units.ext (by rw [Units.val_one, ← hβ g, hg1])
  have h2 : βC g = 1 := hι h1
  have h3 : g ∈ L'.fixingSubgroup :=
    (hker g).mpr ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).mpr hgL, h2⟩
  rw [RQ.resQ_range L']
  exact h3

end DescentSec

end G15Ram

end


/-! ## §7e (local-glue). `BetaTwist2` from an unramified fourth root (proved)

`BetaTwist2 β L` (§7, `p = 2`) is reduced to two smaller Props:
* `Beta4Inertia β L` (GLUE on G7's `β² = ι ∘ χ`): `β⁴ = 1` on the inertia subgroup of `G_{L_v}`;
* `UnramRoots p ℓ` (GLUE, textbook: `G_F/I_F ≅ Ẑ` is topologically generated by a Frobenius and
  `F` has an unramified extension of every degree; Serre, *Local Fields*, Ch. III §5 and IV §2,
  locators UNVERIFIED): a continuous character of `G_F` trivial on inertia has an unramified
  continuous fourth root.
`betaTwist2_of_roots` (proved): `M` is the fixed field of `{σ ∈ G_{L_v} : β(σ) = η(σ)}`, the kernel
of the character `β/η` with values in `μ₄(ℚ̄_ℓ)`, so `[M:L_v] ≤ 4`, and `β = η = 1` on wild inertia
of `G_M`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQp GQ decomp)
open LadicCond

section TwistSec

variable {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **Glue on G7's clauses at `p = 2` (N5 L826-833).** `β⁴ = 1` on the inertia subgroup of
`G_{L_v}` (`inertiaSet` is the inertia subgroup of `G_{ℚ_p}`). Proof plan: on `G_{L_v}`,
`β⁴ = ι ∘ χ²` (G7: `β² = ι ∘ galChar χ`), with `χ` mod `N = chiLevel T₋`, `N = 4^a N'`, `N'` odd
squarefree, `a ≤ 1`; inertia at `2` fixes the roots of unity of odd order (they are unramified:
distinct `N'`-th roots of unity are at distance `1`), so `cyc_N(σ) ∈ (ℤ/4)^× × {1}`, of exponent
`2`, and `χ² (cyc_N σ) = 1`. -/
def Beta4Inertia (β : GQ → PadicAlgCl ℓ) (L : IntermediateField ℚ PkgI4.Qbar) : Prop :=
  ∀ σ ∈ fixSet (Lv (p := p) L) ∩ inertiaSet, β (decomp p σ) ^ 4 = 1

variable (p ℓ) in
/-- **Glue (textbook; Serre, *Local Fields*, Ch. III §5 and Ch. IV §2, locators UNVERIFIED): an
unramified fourth root.** For a finite `F/ℚ_p` and a character `ψ` of `G_F` with values in
`ℚ̄_ℓ^×` that is trivial on some open `G_{F''}` and on the inertia subgroup `G_F ∩ I`, there is a
character `η` of `G_F`, trivial on some open `G_{F₁}` and on `G_F ∩ I`, with `η⁴ = ψ` on `G_F`.
(`ψ` factors through `Gal(F_m/F) ≅ ℤ/m`, `F_m` unramified of degree `m`, generated by Frobenius;
take `ξ` with `ξ⁴ = ψ(Frob)`, of order `d ∣ 4m`, and `η(σ) = ξ^k` for `σ|_{F_d} = Frob^k`.) -/
def UnramRoots : Prop :=
  ∀ (F : Fld p), FiniteDimensional ℚ_[p] F → ∀ ψ : GQp p → PadicAlgCl ℓ,
    (∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, ψ (σ * τ) = ψ σ * ψ τ) →
    (∃ F'' : Fld p, FiniteDimensional ℚ_[p] F'' ∧ ∀ σ ∈ fixSet F'', ψ σ = 1) →
    (∀ σ ∈ fixSet F ∩ inertiaSet, ψ σ = 1) →
    ∃ η : GQp p → PadicAlgCl ℓ,
      (∃ F₁ : Fld p, FiniteDimensional ℚ_[p] F₁ ∧ ∀ σ ∈ fixSet F₁, η σ = 1) ∧
      (∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, η (σ * τ) = η σ * η τ) ∧
      (∀ σ ∈ fixSet F, η σ ^ 4 = ψ σ) ∧
      (∀ σ ∈ fixSet F ∩ inertiaSet, η σ = 1)

/-- **`BetaTwist2` from G7's clauses, `Beta4Inertia` and `UnramRoots` (proved).** -/
theorem betaTwist2_of_roots {β : GQ → PadicAlgCl ℓ} {ε : GQ → GQ → PadicAlgCl ℓ}
    {L : IntermediateField ℚ PkgI4.Qbar} (hC : G7Clauses β ε L) (hU : UnramRoots p ℓ)
    (h4 : Beta4Inertia (p := p) β L) : BetaTwist2 (p := p) β L := by
  haveI : FiniteDimensional ℚ L := hC.1
  obtain ⟨hFfd, -⟩ := Lv_fin (p := p) L
  set F : Fld p := Lv (p := p) L with hFdef
  haveI := hFfd
  have hLF : ∀ x ∈ L, embP x ∈ F := fun x hx => embP_mem_Lv hx
  have hmul : BetaCharOn (p := p) β F := betaCharOn_of_cocycle hC.2.2.1 hC.2.2.2.2.2.2 hLF
  have hβ0 : ∀ g, β g ≠ 0 := hC.2.2.2.1
  have hβ1 : β 1 = 1 := by
    have h := hC.2.2.1 1 1
    rw [hC.2.2.2.2.2.2 1 1 (fun _ _ => rfl) (fun _ _ => rfl), one_mul, mul_one] at h
    exact (mul_right_eq_self₀.mp h).resolve_right (hβ0 1)
  obtain ⟨F', hF'gal, hF'⟩ := betaOpen_of_isLocallyConstant (p := p) hC.2.2.2.2.1 hβ1
  haveI : FiniteDimensional ℚ_[p] F' := hF'gal.1
  -- the fourth root
  obtain ⟨η, ⟨F₁, hF₁fd, hF₁⟩, hηmul, hη4, hηI⟩ := hU F hFfd (fun σ => β (decomp p σ) ^ 4)
    (fun σ hσ τ hτ => by beta_reduce; rw [hmul σ hσ τ hτ, mul_pow])
    ⟨F', hF'gal.1, fun σ hσ => by beta_reduce; rw [hF' σ hσ, one_pow]⟩ h4
  haveI := hF₁fd
  have hη0 : ∀ σ ∈ fixSet F, η σ ≠ 0 := fun σ hσ h0 => by
    have := hη4 σ hσ
    rw [h0, zero_pow (by norm_num)] at this
    exact pow_ne_zero 4 (hβ0 _) this.symm
  have h1F : (1 : GQp p) ∈ fixSet F := fun _ _ => rfl
  have hη1 : η 1 = 1 := by
    have h := hηmul 1 h1F 1 h1F
    rw [mul_one] at h
    exact ((mul_right_eq_self₀.mp h.symm).resolve_right (hη0 1 h1F))
  have hβd1 : β (decomp p 1) = 1 := by rw [map_one]; exact hβ1
  have hinvF : ∀ σ ∈ fixSet F, σ⁻¹ ∈ fixSet F := fun σ hσ x hx => by
    conv_lhs => rw [← hσ x hx]
    exact σ.symm_apply_apply x
  have hmulF : ∀ σ ∈ fixSet F, ∀ τ ∈ fixSet F, σ * τ ∈ fixSet F := fun σ hσ τ hτ x hx => by
    show σ (τ x) = x
    rw [hτ x hx, hσ x hx]
  -- the subgroup `U = {σ ∈ G_F : β σ = η σ}`
  let U : Subgroup (GQp p) :=
    { carrier := {σ | σ ∈ fixSet F ∧ β (decomp p σ) = η σ}
      mul_mem' := fun {σ τ} hσ hτ => ⟨hmulF σ hσ.1 τ hτ.1, by
        rw [hmul σ hσ.1 τ hτ.1, hηmul σ hσ.1 τ hτ.1, hσ.2, hτ.2]⟩
      one_mem' := ⟨h1F, by rw [hβd1, hη1]⟩
      inv_mem' := fun {σ} hσ => ⟨hinvF σ hσ.1, by
        have hb := hmul σ⁻¹ (hinvF σ hσ.1) σ hσ.1
        have he := hηmul σ⁻¹ (hinvF σ hσ.1) σ hσ.1
        rw [inv_mul_cancel, hβd1] at hb
        rw [inv_mul_cancel, hη1] at he
        rw [hσ.2] at hb
        have hne := hη0 σ hσ.1
        calc β (decomp p σ⁻¹) = β (decomp p σ⁻¹) * η σ * (η σ)⁻¹ := by
              rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
          _ = η σ⁻¹ * η σ * (η σ)⁻¹ := by rw [← hb, he]
          _ = η σ⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]⟩ }
  let GF : Subgroup (GQp p) := F.fixingSubgroup
  have hmemGF : ∀ σ : GQp p, σ ∈ GF ↔ σ ∈ fixSet F := fun σ =>
    IntermediateField.mem_fixingSubgroup_iff _ _
  have hUGF : U ≤ GF := fun σ hσ => (hmemGF σ).mpr hσ.1
  -- the character `β/η : G_F → μ₄`
  let f : GF →* (PadicAlgCl ℓ)ˣ :=
    { toFun := fun σ => Units.mk0 (β (decomp p σ.1) * (η σ.1)⁻¹)
        (mul_ne_zero (hβ0 _) (inv_ne_zero (hη0 _ ((hmemGF _).mp σ.2))))
      map_one' := by
        ext
        show β (decomp p 1) * (η 1)⁻¹ = 1
        rw [hβd1, hη1, inv_one, mul_one]
      map_mul' := fun σ τ => by
        ext
        simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul]
        rw [hmul σ.1 ((hmemGF _).mp σ.2) τ.1 ((hmemGF _).mp τ.2),
          hηmul σ.1 ((hmemGF _).mp σ.2) τ.1 ((hmemGF _).mp τ.2), mul_inv]
        ring }
  have hker : U.subgroupOf GF = f.ker := by
    ext σ
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    have hσF := (hmemGF _).mp σ.2
    constructor
    · intro h
      ext
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, Units.val_one]
      rw [h.2, mul_inv_cancel₀ (hη0 _ hσF)]
    · intro h
      refine ⟨hσF, ?_⟩
      have h' := congrArg Units.val h
      simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, Units.val_one] at h'
      have hne := hη0 _ hσF
      calc β (decomp p σ.1) = β (decomp p σ.1) * (η σ.1)⁻¹ * η σ.1 := by
            rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
        _ = η σ.1 := by rw [h', one_mul]
  have hrange : f.range ≤ rootsOfUnity 4 (PadicAlgCl ℓ) := by
    rintro _ ⟨σ, rfl⟩
    rw [mem_rootsOfUnity]
    ext
    have hσF := (hmemGF _).mp σ.2
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_pow_eq_pow_val, Units.val_mk0,
      Units.val_one]
    rw [mul_pow, inv_pow, ← hη4 _ hσF, mul_inv_cancel₀ (pow_ne_zero 4 (hη0 _ hσF))]
  have hrel : U.relIndex GF ≤ 4 := by
    rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    exact (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity _ _)
  have hrel0 : U.relIndex GF ≠ 0 := by
    rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    haveI : Finite f.range :=
      Finite.of_injective (Subgroup.inclusion hrange) (Subgroup.inclusion_injective hrange)
    exact Nat.card_pos.ne'
  -- `U` is open: it contains `G_{F ⊔ F' ⊔ F₁}`
  let E₀ : Fld p := F ⊔ F' ⊔ F₁
  have hE₀U : E₀.fixingSubgroup ≤ U := by
    intro σ hσ
    have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ
    have hσF : σ ∈ fixSet F := fun x hx => hσ' x ((show F ≤ E₀ from le_sup_left.trans le_sup_left) hx)
    have hσF' : σ ∈ fixSet F' := fun x hx => hσ' x ((show F' ≤ E₀ from le_sup_right.trans le_sup_left) hx)
    have hσF₁ : σ ∈ fixSet F₁ := fun x hx => hσ' x ((show F₁ ≤ E₀ from le_sup_right) hx)
    exact ⟨hσF, by rw [hF' σ hσF', hF₁ σ hσF₁]⟩
  have hUopen : IsOpen (U : Set (GQp p)) :=
    Subgroup.isOpen_mono hE₀U (IntermediateField.fixingSubgroup_isOpen E₀)
  have hUclosed : IsClosed (U : Set (GQp p)) := Subgroup.isClosed_of_isOpen U hUopen
  let M : Fld p := IntermediateField.fixedField U
  have hMU : M.fixingSubgroup = U := InfiniteGalois.fixingSubgroup_fixedField ⟨U, hUclosed⟩
  have hMfr : Module.finrank ℚ_[p] M = U.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) M, hMU]
  have hFfr : Module.finrank ℚ_[p] F = GF.index :=
    IntermediateField.finrank_eq_fixingSubgroup_index (Kbar p) F
  have hUidx : U.index = U.relIndex GF * GF.index := (Subgroup.relIndex_mul_index hUGF).symm
  have hFpos : 0 < Module.finrank ℚ_[p] F := Module.finrank_pos
  have hMpos : 0 < Module.finrank ℚ_[p] M := by
    rw [hMfr, hUidx]
    exact Nat.mul_pos (Nat.pos_of_ne_zero hrel0) (hFfr ▸ hFpos)
  refine ⟨M, Module.finite_of_finrank_pos hMpos, ?_, ?_, ?_⟩
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    exact hτ.1 x hx
  · rw [hMfr, hUidx, ← hFfr]
    exact Nat.mul_le_mul_right _ hrel
  · intro σ hσ
    have hσM : σ ∈ M.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).mpr hσ.1
    rw [hMU] at hσM
    rw [hσM.2]
    exact hηI σ ⟨hσM.1, wildSet_subset_inertiaSet hσ.2⟩

/-! ### `Beta4Inertia` at `p = 2` from G7's clauses (proved) -/

/-- Inertia fixes the roots of unity of order prime to `p` (proved; as `wild_fix_prime_to_p`). -/
theorem inertia_fix_prime_to_p {σ : GQp p} (hσ : σ ∈ inertiaSet) {ζ : Kbar p} {m : ℕ}
    (hm0 : 0 < m) (hpm : ¬ p ∣ m) (hζ : ζ ^ m = 1) : σ ζ = ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl; rw [zero_pow hm0.ne'] at hζ; exact zero_ne_one hζ
  have h1 : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one hm0 hζ
  set η := σ ζ * ζ⁻¹ with hη
  have hηm : η ^ m = 1 := by
    rw [hη, mul_pow, ← map_pow, hζ, map_one, inv_pow, hζ, inv_one, one_mul]
  have hlt : ‖η - 1‖ < 1 := by
    have he : η - 1 = (σ ζ - ζ) * ζ⁻¹ := by rw [hη, sub_mul, mul_inv_cancel₀ hζ0]
    rw [he, norm_mul, norm_inv, h1, inv_one, mul_one]
    exact hσ ζ h1.le
  have := eq_one_of_pow_eq_one_of_norm_lt hm0 hpm hηm hlt
  rw [hη, mul_inv_eq_one₀ hζ0] at this
  exact this

/-- `σ²` fixes the fourth roots of unity (proved): `σ(i) = ±i`. -/
theorem sq_fix_four (σ : GQp p) {ζ : Kbar p} (hζ : ζ ^ 4 = 1) : σ (σ ζ) = ζ := by
  have h2 : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = 0 := by linear_combination hζ
  rcases mul_eq_zero.mp h2 with h | h
  · have h' : (ζ - 1) * (ζ + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · rw [sub_eq_zero.mp h1, map_one, map_one]
    · rw [eq_neg_of_add_eq_zero_left h1]
      simp
  · have hτ : (σ ζ - ζ) * (σ ζ + ζ) = 0 := by
      have e2 : σ ζ ^ 2 = ζ ^ 2 := by
        have e1 : ζ ^ 2 = -1 := by linear_combination h
        rw [← map_pow, e1, map_neg, map_one]
      linear_combination e2
    rcases mul_eq_zero.mp hτ with h1 | h1
    · rw [sub_eq_zero.mp h1, sub_eq_zero.mp h1]
    · have e : σ ζ = -ζ := eq_neg_of_add_eq_zero_left h1
      rw [e, map_neg, e, neg_neg]

/-- `chiLevel T₋ ∣ 4M` with `M` odd (proved; `lev 2 = 4`, `lev q = q` for odd `q`). -/
theorem chiLevel_dvd_four_mul_odd {Tm : Finset ℕ} (hTm : ∀ q ∈ Tm, q.Prime) :
    ∃ M : ℕ, ¬ 2 ∣ M ∧ GlueDescent.chiLevel Tm ∣ 4 * M := by
  refine ⟨∏ q ∈ Tm.erase 2, GlueDescent.lev q, ?_, ?_⟩
  · refine Finset.prod_induction _ (fun n => ¬ 2 ∣ n) (fun a b ha hb h => ?_) (by norm_num)
      (fun q hq => ?_)
    · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
      · exact ha h
      · exact hb h
    · have hq2 : q ≠ 2 := Finset.ne_of_mem_erase hq
      have hqp := hTm q (Finset.mem_of_mem_erase hq)
      unfold GlueDescent.lev
      rw [if_neg hq2]
      intro h
      rcases (Nat.Prime.eq_one_or_self_of_dvd hqp 2 h) with h' | h'
      · omega
      · exact hq2 h'.symm
  · by_cases h2 : 2 ∈ Tm
    · unfold GlueDescent.chiLevel
      rw [← Finset.mul_prod_erase Tm GlueDescent.lev h2]
      unfold GlueDescent.lev
      rw [if_pos rfl]
    · unfold GlueDescent.chiLevel
      rw [Finset.erase_eq_self.mpr h2]
      exact dvd_mul_left _ _

/-- At `p = 2`, `decomp(σ²)` fixes the `4M`-th roots of unity for inertia `σ`, `M` odd (proved). -/
theorem decomp_sq_fix_root (hp2 : p = 2) {σ : GQp p} (hσ : σ ∈ inertiaSet) {M : ℕ}
    (hM : ¬ 2 ∣ M) {x : PkgI4.Qbar} (hx : x ^ (4 * M) = 1) : decomp p (σ * σ) x = x := by
  apply (embP (p := p)).injective
  rw [decomp_spec]
  set ζ := embP (p := p) x
  have hζ : ζ ^ (4 * M) = 1 := by rw [← map_pow, hx, map_one]
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact hM (dvd_zero 2))
  have hζ0 : ζ ≠ 0 := by
    rintro h0; rw [h0, zero_pow (by omega)] at hζ; exact zero_ne_one hζ
  have hpM : ¬ p ∣ M := hp2 ▸ hM
  have hy : σ (ζ ^ 4) = ζ ^ 4 := inertia_fix_prime_to_p hσ hM0 hpM (by rw [← pow_mul, hζ])
  have hz : σ (σ (ζ ^ M)) = ζ ^ M := sq_fix_four σ (by rw [← pow_mul, mul_comm, hζ])
  have hcop : Nat.Coprime 4 M := by
    have := Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hM)
    norm_num at this
    exact this
  have hb : ((Nat.gcd 4 M : ℕ) : ℤ) = 4 * Nat.gcdA 4 M + M * Nat.gcdB 4 M := Nat.gcd_eq_gcd_ab 4 M
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have hdec : ζ = (ζ ^ 4) ^ (Nat.gcdA 4 M) * (ζ ^ M) ^ (Nat.gcdB 4 M) := by
    have hb' : ((4 : ℕ) : ℤ) * Nat.gcdA 4 M + (M : ℤ) * Nat.gcdB 4 M = 1 := by
      exact_mod_cast hb.symm
    rw [← zpow_natCast ζ 4, ← zpow_natCast ζ M, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, hb',
      zpow_one]
  show σ (σ ζ) = ζ
  rw [hdec, map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀, map_zpow₀, hz, hy, hy]

/-- At `p = 2`, the cyclotomic character mod `N ∣ 4M` (`M` odd) kills `decomp(σ²)` for inertia
`σ` (proved; as `cyc_decomp_wild`). -/
theorem cyc_decomp_sq_inertia (hp2 : p = 2) {σ : GQp p} (hσ : σ ∈ inertiaSet) {N M : ℕ}
    [NeZero N] (hM : ¬ 2 ∣ M) (hNM : N ∣ 4 * M) :
    GlueDescent.B2Q.cyc N (decomp p (σ * σ)) = 1 := by
  by_cases hN1 : N = 1
  · subst hN1; exact Subsingleton.elim _ _
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : Fact (1 < N) := ⟨by omega⟩
  haveI : NeZero ((N : ℕ) : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  apply Units.ext
  obtain ⟨k, hk⟩ := hNM
  have hu := modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
    (GlueDescent.B2Q.toRingAut (decomp p (σ * σ))) (c := 1) (fun t ht => by
      rw [ZMod.val_one, pow_one]
      have htN : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ N = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity N t).mp ht, Units.val_one]
      exact decomp_sq_fix_root hp2 hσ hM (by rw [hk, pow_mul, htN, one_pow]))
  have hc : GlueDescent.B2Q.cyc N (decomp p (σ * σ)) = modularCyclotomicCharacter
      (AlgebraicClosure ℚ)
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ) N)
      (GlueDescent.B2Q.toRingAut (decomp p (σ * σ))) := rfl
  rw [hc, Units.val_one]
  exact hu.symm

/-- **`Beta4Inertia` at `p = 2` from G7's clauses (proved).** `β⁴ = ι(χ(cyc_N σ))² =
ι(χ(cyc_N σ²))`, and `cyc_N(σ²) = 1` (`cyc_decomp_sq_inertia`, `chiLevel_dvd_four_mul_odd`). -/
theorem beta4Inertia_of_clauses (hp2 : p = 2) {β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) : Beta4Inertia (p := p) β L := by
  intro σ hσ
  obtain ⟨Tmin, hTmin, hNZ, χ, ι, hβχ⟩ := hC.2.2.2.2.2.1
  obtain ⟨M, hM, hNM⟩ := chiLevel_dvd_four_mul_odd hTmin
  have hc := cyc_decomp_sq_inertia hp2 hσ.2 hM hNM
  have h2 : (GlueDescent.B2Q.galChar χ (decomp p σ)) ^ 2 = 1 := by
    have hd : (GlueDescent.B2Q.galChar χ) (decomp p (σ * σ)) = 1 := by
      change χ.toUnitHom (GlueDescent.B2Q.cyc _ (decomp p (σ * σ))) = 1
      rw [hc, map_one]
    have hm := map_mul (GlueDescent.B2Q.galChar χ) (decomp p σ) (decomp p σ)
    rw [sq]
    refine hm.symm.trans ?_
    refine Eq.trans ?_ hd
    exact congrArg (⇑(GlueDescent.B2Q.galChar χ)) (map_mul (decomp p) σ σ).symm
  calc β (decomp p σ) ^ 4 = (β (decomp p σ) ^ 2) ^ 2 := by ring
    _ = ((ι (GlueDescent.B2Q.galChar χ (decomp p σ)) : PadicAlgCl ℓ)) ^ 2 := by rw [hβχ]
    _ = ((ι (GlueDescent.B2Q.galChar χ (decomp p σ) ^ 2) : PadicAlgCl ℓ)) := by
        rw [map_pow, Units.val_pow_eq_pow_val]
    _ = 1 := by rw [h2, map_one, Units.val_one]

/-- **`BetaTwist2` at `p = 2` from G7's clauses and the textbook Prop `UnramRoots` (proved).** -/
theorem betaTwist2_of_unramRoots (hp2 : p = 2) {β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {L : IntermediateField ℚ PkgI4.Qbar}
    (hC : G7Clauses β ε L) (hU : UnramRoots p ℓ) : BetaTwist2 (p := p) β L :=
  betaTwist2_of_roots hC hU (beta4Inertia_of_clauses hp2 hC)

variable {K : Type} [Field K] [NumberField K]

/-- **`LocalGlue p Tm a β L` on G7's data (proved)** from the leaves R6 and I2-Tors, the textbook
Prop `UnramRoots` (used at `p = 2`), and the glue `KerWild` (all `p`) and `DescentPts` (`p ≤ 5`). -/
theorem localGlue_of_unramRoots (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU : UnramRoots p ℓ) (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {c ε : GQ → GQ → PadicAlgCl ℓ}
    {a β : GQ → PadicAlgCl ℓ} {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ PkgI4.Qbar}
    [FiniteDimensional ℚ L] (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hD : p ≤ 5 → DescentPts A L) : LocalGlue (p := p) Tm a β L :=
  localGlue_of_descent hR6 hTors hpℓ h7 hC hK hD (fun h2 => betaTwist2_of_unramRoots h2 hC hU)

end TwistSec

end G15Ram

end


/-! ## §7f (local-glue). `DescentPts` for a base change (proved)

For `L ≤ L'` finite inside `ℚ̄`, `L/ℚ` Galois, and `A₀ : AbVar L` of dimension `2`,
`DescentPts (A₀)_{L'} L` holds (`descentPts_baseChange`), with `(A₀)_{L'}` the base change along
g0-mod-field's `incAlg` (as in g0-assemble's `TateBridge`). The model is the conjugate
`A₁ = A₀ ×_{L,γ} L`, where `γ ∈ Aut(L)` corrects the difference between the embeddings `L ↪ ℚ̄`
that Mathlib chooses inside `resQ L` and inside `resQ L'` (`jL L`, `jL' hLL'`; both have image
`L` since `L/ℚ` is normal). Points: `A₁(L̄) ≅ A₀(L̄_tw) ≅ A₀(L̄') ≅ (A₀)_{L'}(L̄')` by `bcPt`,
`trPt` along `θ = qEmb_{L'} ∘ qEmb_L⁻¹` (`L`-linear for the twisted structure `tw`), and `bcPt`. -/

noncomputable section

namespace G15Ram

open PkgI4 (GQ)
open CategoryTheory AlgebraicGeometry Limits MonObj

section BCDescentSec

attribute [local instance] RQ.numberField_of_fd

/-- `qEmb K` as a ring isomorphism `ℚ̄ ≃ K̄`. -/
def qEquiv (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective (G0Galois.qEmbRing K)
    ⟨(G0Galois.qEmbRing K).injective, qEmbRing_surjective K⟩

theorem qEquiv_apply (K : Type) [Field K] [NumberField K] (x : AlgebraicClosure ℚ) :
    qEquiv K x = G0Galois.qEmbRing K x := rfl

/-- The embedding `K ↪ ℚ̄` inside `resQ K`. -/
def jK (K : Type) [Field K] [NumberField K] : K →ₐ[ℚ] AlgebraicClosure ℚ :=
  ((qEquiv K).symm.toRingHom.comp (algebraMap K (AlgebraicClosure K))).toRatAlgHom

theorem qEquiv_jK (K : Type) [Field K] [NumberField K] (x : K) :
    qEquiv K (jK K x) = algebraMap K (AlgebraicClosure K) x := by
  show qEquiv K ((qEquiv K).symm _) = _
  exact (qEquiv K).apply_symm_apply _

variable {L L' : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L]
  [FiniteDimensional ℚ L'] (hLL' : L ≤ L')

/-- The embedding `L ↪ L' ↪ ℚ̄` inside `resQ L'`. -/
def jL' : L →ₐ[ℚ] AlgebraicClosure ℚ := (jK L').comp (IntermediateField.inclusion hLL')

variable [IsGalois ℚ L]

theorem mem_range_jK (x : L) : jL' hLL' x ∈ (jK L).fieldRange := by
  have h1 := AlgHom.fieldRange_of_normal (jK L)
  have h2 := AlgHom.fieldRange_of_normal (jL' hLL')
  have hx : jL' hLL' x ∈ (jL' hLL').fieldRange := ⟨x, rfl⟩
  rw [h2] at hx
  rw [h1]
  exact hx

/-- `γ = jK_L⁻¹ ∘ jL'`, a ring endomorphism of `L`. -/
def γL : L →+* L :=
  (AlgEquiv.ofInjectiveField (jK L)).symm.toRingEquiv.toRingHom.comp
    ((jL' hLL').toRingHom.codRestrict (jK L).fieldRange (mem_range_jK hLL'))

theorem jK_γL (x : L) : jK L (γL hLL' x) = jL' hLL' x := by
  have h := congrArg Subtype.val
    ((AlgEquiv.ofInjectiveField (jK L)).apply_symm_apply ⟨jL' hLL' x, mem_range_jK hLL' x⟩)
  exact h

theorem γL_bijective : Function.Bijective (γL hLL') := by
  have hinj : Function.Injective (γL hLL') := (γL hLL').injective
  refine ⟨hinj, ?_⟩
  exact (LinearMap.injective_iff_surjective
    (f := (γL hLL').toRatAlgHom.toLinearMap)).mp hinj

/-- g0-mod-field's `incAlg` (`L → L'`). -/
@[instance_reducible] def incAlgL : Algebra L L' := (IntermediateField.inclusion hLL').toRingHom.toAlgebra

/-- The `L`-algebra structure on `L` through `γ`. -/
@[instance_reducible] def γAlg : Algebra L L := (γL hLL').toAlgebra

/-- The twisted `L`-algebra structure on `L̄`: `x ↦ qEmb_L (jL' x)`. -/
@[instance_reducible] def twAlg : Algebra L (AlgebraicClosure L) :=
  ((qEquiv L).toRingHom.comp (jL' hLL').toRingHom).toAlgebra

/-- The `L`-algebra structure on `L̄'` through `L ⊆ L'`. -/
@[instance_reducible] def compAlg : Algebra L (AlgebraicClosure L') :=
  ((algebraMap L' (AlgebraicClosure L')).comp (IntermediateField.inclusion hLL').toRingHom).toAlgebra

theorem tower_tw : @IsScalarTower L L (AlgebraicClosure L) (γAlg hLL').toSMul
    Algebra.toSMul (twAlg hLL').toSMul :=
  @IsScalarTower.of_algebraMap_eq L L (AlgebraicClosure L) _ _ _ (γAlg hLL') _ (twAlg hLL')
    (fun x => by
      show qEquiv L (jL' hLL' x) = algebraMap L (AlgebraicClosure L) (γL hLL' x)
      rw [← qEquiv_jK, jK_γL])

theorem tower_comp : @IsScalarTower L L' (AlgebraicClosure L') (incAlgL hLL').toSMul
    Algebra.toSMul (compAlg hLL').toSMul :=
  @IsScalarTower.of_algebraMap_eq L L' (AlgebraicClosure L') _ _ _ (incAlgL hLL') _ (compAlg hLL')
    (fun x => rfl)

/-- `θ = qEmb_{L'} ∘ qEmb_L⁻¹ : L̄_tw ≃ L̄'`, `L`-linear. -/
def θL : @AlgEquiv L (AlgebraicClosure L) (AlgebraicClosure L') _ _ _ (twAlg hLL')
    (compAlg hLL') :=
  @AlgEquiv.ofRingEquiv L (AlgebraicClosure L) (AlgebraicClosure L') _ _ _ (twAlg hLL')
    (compAlg hLL') ((qEquiv L).symm.trans (qEquiv L')) (fun x => by
      show qEquiv L' ((qEquiv L).symm (qEquiv L (jL' hLL' x))) =
        algebraMap L' (AlgebraicClosure L') (IntermediateField.inclusion hLL' x)
      rw [RingEquiv.symm_apply_apply]
      exact qEquiv_jK L' _)

theorem θL_apply (x : AlgebraicClosure L) : θL hLL' x = qEquiv L' ((qEquiv L).symm x) := rfl

/-- `θ σ₀ = σ' θ` when `resQ_L σ₀ = resQ_{L'} σ'`. -/
theorem θL_galois (σ₀ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L')
    (h : G0Galois.resQ L σ₀ = G0Galois.resQ L' σ') (x : AlgebraicClosure L) :
    σ' (θL hLL' x) = θL hLL' (σ₀ x) := by
  obtain ⟨y, rfl⟩ := (qEquiv L).surjective x
  have hθ : ∀ z, θL hLL' (qEquiv L z) = qEquiv L' z := fun z => by
    rw [θL_apply, RingEquiv.symm_apply_apply]
  have h1 := G0Galois.resQ_spec L σ₀ y
  have h2 := G0Galois.resQ_spec L' σ' y
  calc σ' (θL hLL' (qEquiv L y)) = σ' (qEquiv L' y) := by rw [hθ]
    _ = qEquiv L' (G0Galois.resQ L' σ' y) := h2.symm
    _ = qEquiv L' (G0Galois.resQ L σ₀ y) :=
        congrArg (fun g : GQ => qEquiv L' (g y)) h.symm
    _ = θL hLL' (qEquiv L (G0Galois.resQ L σ₀ y)) := (hθ _).symm
    _ = θL hLL' (σ₀ (qEquiv L y)) := congrArg (θL hLL') h1

/-- The conjugate model `A₁ = A₀ ×_{L,γ} L`. -/
abbrev conjModel (A₀ : PkgI3.AbVar L) : PkgI3.AbVar L :=
  @PkgI3.AbVar.baseChange L _ A₀ L _ (γAlg hLL')

/-- The base change `(A₀)_{L'}` along `incAlg` (as in `TateBridge`). -/
abbrev bcL' (A₀ : PkgI3.AbVar L) : PkgI3.AbVar L' :=
  @PkgI3.AbVar.baseChange L _ A₀ L' _ (incAlgL hLL')

/-- `φ : A₁(L̄) ≅ A₀(L̄_tw) ≅ A₀(L̄') ≅ (A₀)_{L'}(L̄')`. -/
def φL (A₀ : PkgI3.AbVar L) :
    (conjModel hLL' A₀).Pt (AlgebraicClosure L) ≃* (bcL' hLL' A₀).Pt (AlgebraicClosure L') :=
  ((@UnramTate.bcPt L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _ (twAlg hLL')
      (tower_tw hLL')).trans
    (@UnramTate.trPt L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
      (compAlg hLL') (θL hLL'))).trans
    (@UnramTate.bcPt L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _ (compAlg hLL')
      (tower_comp hLL')).symm

/-- `φ` intertwines `σ₀ ∈ G_L` and `σ' ∈ G_{L'}` with the same image in `G_ℚ` (proved). -/
theorem φL_galAct (A₀ : PkgI3.AbVar L) (σ₀ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L)
    (σ' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L')
    (h : G0Galois.resQ L σ₀ = G0Galois.resQ L' σ')
    (P : (conjModel hLL' A₀).Pt (AlgebraicClosure L)) :
    φL hLL' A₀ ((conjModel hLL' A₀).galAct σ₀ P) =
      (bcL' hLL' A₀).galAct σ' (φL hLL' A₀ P) := by
  set b₁ := @UnramTate.bcPt L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _ (twAlg hLL')
      (tower_tw hLL') with hb₁
  set t := @UnramTate.trPt L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
      (compAlg hLL') (θL hLL') with ht
  set b₂ := @UnramTate.bcPt L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _ (compAlg hLL')
      (tower_comp hLL') with hb₂
  have e1 := @UnramTate.bcPt_galAct L L _ _ (γAlg hLL') A₀ (AlgebraicClosure L) _ _
    (twAlg hLL') (tower_tw hLL') σ₀ P
  have e3 := @UnramTate.bcPt_galAct L L' _ _ (incAlgL hLL') A₀ (AlgebraicClosure L') _ _
    (compAlg hLL') (tower_comp hLL') σ' (b₂.symm (t (b₁ P)))
  show b₂.symm (t (b₁ ((conjModel hLL' A₀).galAct σ₀ P))) =
    (bcL' hLL' A₀).galAct σ' (b₂.symm (t (b₁ P)))
  apply b₂.injective
  rw [MulEquiv.apply_symm_apply, e3, MulEquiv.apply_symm_apply]
  erw [e1]
  exact @UnramTate.trPt_galAct L _ A₀ (AlgebraicClosure L) (AlgebraicClosure L') _ (twAlg hLL') _
    (compAlg hLL') (θL hLL') _ _ (fun x => θL_galois hLL' σ₀ σ' h x) (b₁ P)

/-- The conjugate model has the dimension of `A₀` (proved): base change along the isomorphism
`Spec γ` is homeomorphic to `A₀`. -/
theorem dim_conjModel (A₀ : PkgI3.AbVar L) : (conjModel hLL' A₀).dim = A₀.dim := by
  let e : L ≃+* L := RingEquiv.ofBijective (γL hLL') (γL_bijective hLL')
  have hiso : IsIso (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))) :=
    e.toCommRingCatIso.isIso_hom
  have hiso2 : IsIso (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL')))) :=
    inferInstance
  have hiso3 : IsIso (pullback.fst (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))))) := inferInstance
  show topologicalKrullDim (pullback (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL'))))) =
    topologicalKrullDim A₀.X.left
  exact IsHomeomorph.topologicalKrullDim_eq _
    (Scheme.Hom.homeomorph (pullback.fst (C := Scheme) A₀.X.hom
      (Spec.map (CommRingCat.ofHom (@algebraMap L L _ _ (γAlg hLL')))))).isHomeomorph

/-- **`DescentPts` for a base change (proved).** For `L ≤ L'` finite in `ℚ̄`, `L/ℚ` Galois, and
`A₀ : AbVar L` with `dim A₀ = 2`, `DescentPts ((A₀)_{L'}) L` holds for G7Out's model field
`K = L'`, with the conjugate model `A₀ ×_{L,γ} L`. -/
theorem descentPts_baseChange (A₀ : PkgI3.AbVar L) (hdim : A₀.dim = 2) :
    DescentPts (K := L') (bcL' hLL' A₀) L :=
  ⟨inferInstance, conjModel hLL' A₀, φL hLL' A₀, (dim_conjModel hLL' A₀).trans hdim,
    fun σ₀ σ' h P => φL_galAct hLL' A₀ σ₀ σ' h P⟩

/-- **`LocalGlue` on G7's construction (proved).** For g0-mod-field's data: `L ≤ L'` finite
Galois in `ℚ̄`, `A₀ : AbVar L` with `dim A₀ = 2`, G7Out for `(A₀)_{L'}` over `K = L'`, G7's clauses,
the kernel-field clause `G_{L'} = G_L ∩ ker β_ℂ`, and the transport `β = ι ∘ β_ℂ` with `ι`
injective, `LocalGlue p Tm a β L` holds at every `p ≠ ℓ`, from the leaves R6 and I2-Tors and the
textbook Prop `UnramRoots` (used at `p = 2`). -/
theorem localGlue_of_baseChange {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : UnramRoots p ℓ) (hpℓ : p ≠ ℓ) [IsGalois ℚ L'] (A₀ : PkgI3.AbVar L)
    (hdim₀ : A₀.dim = 2)
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb (bcL' hLL' A₀) ℓ)}
    {c ε : GQ → GQ → PadicAlgCl ℓ} {a β : GQ → PadicAlgCl ℓ}
    {u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb (bcL' hLL' A₀) ℓ)}
    (h7 : G0Galois.G7Out (bcL' hLL' A₀) ℓ Tm c ε a β u) (hC : G7Clauses β ε L)
    (βC : GQ → ℂˣ) (hker : ∀ σ : GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ) (hι : Function.Injective ιC)
    (hβ : ∀ g, β g = (ιC (βC g) : PadicAlgCl ℓ)) :
    LocalGlue (p := p) Tm a β L :=
  localGlue_of_unramRoots hR6 hTors hU hpℓ h7 hC (kerWild_of_g7Data βC hker ιC hι hβ)
    (fun _ => descentPts_baseChange hLL' A₀ hdim₀)

end BCDescentSec


end G15Ram

end


noncomputable section

/-! ## §8 (local-glue). The packs: G8's data with the local glue replaced by Props on `A/K`

`G8LocalPack` is copied verbatim from scratch/local-data/tail_part.lean (the hypothesis of
local-data's tail `modularConstituent_tail_L`). `G7LocalPackK` asks instead for G7's data
(`G7Out`), G8's output, the clauses, `KerWild`, and the torsion-point Props `TorsFixWild`
(`p ≥ 7`), `TorsFixWildE` (`p ≤ 5`) and `BetaUpper` (`p = 2`) at the primes in `P`. -/

namespace G0ModNewform

open PkgI4 (Qbar GQ GaloisRep)
open PkgI3

attribute [local instance] RQ.numberField_of_fd

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

/-- **G7's data for `r` with the local glue at `p ∈ P` in leaf form (GLUE).**
At `p ≥ 7` nothing: the local glue there follows from the leaves R6 and I2-Tors
(`G15Ram.raynaudPlace_of_R6`, `G15Ram.ptFinite`); at
`p ∈ {3, 5}`: `TorsFixWildOdd`; at `p = 2`: `TorsFixWildE` and `BetaTwist2` (which replaces
`BetaUpper`, `G15Ram.betaUpper_of_twist`). With the leaves R6 and
I2-Tors and `p ≠ ℓ` on `P`, it gives `G7LocalPackK` (`g7LocalPackK_of_R`). -/
def G7LocalPackR (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (3 ≤ p → p ≤ 5 → @G15Ram.TorsFixWildOdd p ⟨hp⟩ K _ _ A ℓ _ L) ∧
      (p = 2 → @G15Ram.TorsFixWildE p ⟨hp⟩ K _ _ A ℓ _ β L ∧ @G15Ram.BetaTwist2 p ⟨hp⟩ ℓ _ β L)

/-- **`G7LocalPackK` from `G7LocalPackR`, the leaf I2-Tors and `p ≠ ℓ` on `P` (proved).** -/
theorem g7LocalPackK_of_R (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackR ℓ r P) :
    G7LocalPackK ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, c, ε, a, β, u, L, h7, h8, hC, hK, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hO, h2⟩ := hloc p hp hP
  refine ⟨fun h7p => ?_, fun h5 => ?_, fun h2' => G15Ram.betaUpper_of_twist hC (h2 h2').2⟩
  · exact G15Ram.torsFixWild_of_raynaud (Ne.symm (hPℓ p hP)) h7p
      (G15Ram.wildIter A) (G15Ram.torsGL_of_leaf hTors A h7.1 3 (by norm_num))
      (G15Ram.torsGL_of_leaf hTors A h7.1 7 (by norm_num))
      (fun _ => G15Ram.raynaudPlace_of_R6 hR6 hTors A h7.1 (by norm_num)
        (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega))
      (fun h13 => G15Ram.raynaudPlace_of_R6 hR6 hTors A h7.1 (by norm_num)
        (by rw [h13]; norm_num))
  · by_cases hp2 : p = 2
    · exact (h2 hp2).1
    · have h3 : 3 ≤ p := by have := hp.two_le; omega
      exact G15Ram.torsFixWildE_of_odd hp2 hC (hO h3 h5)

/-- **`G15RamG` from the leaf-and-bridge packs and I2-Tors (proved).** -/
theorem g15RamG_of_packR (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackR 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackR 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u :=
  g15RamG_of_packK D u (g7LocalPackK_of_R hR6 hTors (fun _ h => h) h5)
    (g7LocalPackK_of_R hR6 hTors (fun p h => by rw [h]; norm_num) h3) h11₅ h11₃

/-- **G7's data for `r` with the local glue at `p ∈ P` as the glue Props of §7d (GLUE).**
`KerWild` (G7Data's kernel-field clause), and at the primes `p ∈ P`: `DescentPts A L` (the model
of `A` over `L`) when `p ≤ 5`, `BetaTwist2` when `p = 2`. Nothing at `p ≥ 7`. With the leaves R6,
I2-Tors and `p ≠ ℓ` on `P` it gives `G8LocalPack` (`g8LocalPack_of_D`). -/
def G7LocalPackD (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ∀ (p : ℕ) (hp : p.Prime), P p →
      (p ≤ 5 → G15Ram.DescentPts A L) ∧ (p = 2 → @G15Ram.BetaTwist2 p ⟨hp⟩ ℓ _ β L)

/-- **`G8LocalPack` from `G7LocalPackD`, the leaves R6 and I2-Tors, and `p ≠ ℓ` on `P` (proved)**,
by `G15Ram.localGlue_of_descent`. -/
theorem g8LocalPack_of_D (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackD ℓ r P) :
    G8LocalPack ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, _, h7, h8, hC, hK, hloc⟩ := h
  refine ⟨K, _, _, A, Tm, a, β, ε, L, h8, hC, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hD, hB⟩ := hloc p hp hP
  exact G15Ram.localGlue_of_descent hR6 hTors (hPℓ p hP) h7 hC hK hD hB

/-- **`G15RamG` from the descent packs and the leaves R6, I2-Tors (proved).** -/
theorem g15RamG_of_packD (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackD 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackD 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ :=
    g8LocalPack_of_D hR6 hTors (fun _ h => h) h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ :=
    g8LocalPack_of_D hR6 hTors (fun p h => by rw [h]; norm_num) h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

/-- **G7's data for `r` with the local glue at `p ∈ P` reduced to two glue Props (GLUE).**
`KerWild` (G7Data's kernel-field clause) and, when some `p ∈ P` has `p ≤ 5`, `DescentPts A L`
(the model of `A` over `L`). At `p = 2` the twist is supplied by the textbook Prop
`G15Ram.UnramRoots` (`g8LocalPack_of_U`). -/
def G7LocalPackU (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) (P : ℕ → Prop) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K) (A : AbVar K)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (L : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L),
    G0Galois.G7Out A ℓ Tm c ε a β u ∧ G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧ G15Ram.KerWild K β L ∧
    ((∃ p, P p ∧ p.Prime ∧ p ≤ 5) → G15Ram.DescentPts A L)

/-- **`G8LocalPack` from `G7LocalPackU`, the leaves R6, I2-Tors, the textbook Prop `UnramRoots`
at `p = 2`, and `p ≠ ℓ` on `P` (proved)**, by `G15Ram.localGlue_of_unramRoots`. -/
theorem g8LocalPack_of_U (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : ∀ (hp : Nat.Prime 2), @G15Ram.UnramRoots 2 ⟨hp⟩ ℓ _)
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackU ℓ r P) :
    G8LocalPack ℓ r P := by
  obtain ⟨K, _, _, A, Tm, c, ε, a, β, u, L, _, h7, h8, hC, hK, hD⟩ := h
  refine ⟨K, _, _, A, Tm, a, β, ε, L, h8, hC, fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  refine G15Ram.localGlue_of_descent hR6 hTors (hPℓ p hP) h7 hC hK
    (fun h5 => hD ⟨p, hP, hp, h5⟩) (fun h2 => ?_)
  subst h2
  exact G15Ram.betaTwist2_of_unramRoots rfl hC (hU hp)

/-- **`G15RamG` from the packs `G7LocalPackU` (proved).** -/
theorem g15RamG_of_packU (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU2 : ∀ (hp : Nat.Prime 2) (ℓ : ℕ) [Fact ℓ.Prime],
      @G15Ram.UnramRoots 2 ⟨hp⟩ ℓ _) {L : Type} [Field L]
    [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackU 5 D.r5 (fun p => p ≠ 5)) (h3 : G7LocalPackU 3 D.r3 (fun p => p = 5))
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ :=
    g8LocalPack_of_U hR6 hTors (fun hp => hU2 hp 5) (fun _ h => h) h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ :=
    g8LocalPack_of_U hR6 hTors (fun hp => hU2 hp 3) (fun p h => by rw [h]; norm_num) h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

/-- **G7's data for `r` in the form of g0-mod-field's construction (GLUE: the output of an
augmented `TateBridge`).** `L ≤ L'` finite Galois in `ℚ̄`, `A₀ : AbVar L` with `dim A₀ = 2`,
G7Out and G8Out for `(A₀)_{L'}` (base change along `incAlg`), G7's clauses, the kernel-field
clause `G_{L'} = G_L ∩ ker β_ℂ` of `G7Data`, and the transport `β = ι ∘ β_ℂ` with `ι` injective.
No local Prop is asked at any prime (`g8LocalPack_of_BC`). -/
def G7LocalPackBC (ℓ : ℕ) [Fact ℓ.Prime] (r : GaloisRep ℓ 2) : Prop :=
  ∃ (L L' : IntermediateField ℚ Qbar) (_ : FiniteDimensional ℚ L) (_ : FiniteDimensional ℚ L')
    (_ : IsGalois ℚ L) (_ : IsGalois ℚ L') (hLL' : L ≤ L') (A₀ : AbVar L)
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb (G15Ram.bcL' hLL' A₀) ℓ))
    (c ε : GQ → GQ → PadicAlgCl ℓ) (a β : GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb (G15Ram.bcL' hLL' A₀) ℓ))
    (βC : GQ → ℂˣ) (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ),
    A₀.dim = 2 ∧ G0Galois.G7Out (G15Ram.bcL' hLL' A₀) ℓ Tm c ε a β u ∧
    G0Galois.G8Out (G15Ram.bcL' hLL' A₀) ℓ (GlueDescent.rho Tm a β) r ∧
    G15Ram.G7Clauses β ε L ∧
    (∀ σ : GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1) ∧
    Function.Injective ιC ∧ (∀ g, β g = (ιC (βC g) : PadicAlgCl ℓ))

/-- **`G8LocalPack` from `G7LocalPackBC`, the leaves R6, I2-Tors and the textbook Prop
`UnramRoots` (at `p = 2`), for `p ≠ ℓ` on `P` (proved)**, by `G15Ram.localGlue_of_baseChange`. -/
theorem g8LocalPack_of_BC (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : ∀ (p : ℕ) [Fact p.Prime], G15Ram.UnramRoots p ℓ)
    {r : GaloisRep ℓ 2} {P : ℕ → Prop} (hPℓ : ∀ p, P p → p ≠ ℓ) (h : G7LocalPackBC ℓ r) :
    G8LocalPack ℓ r P := by
  obtain ⟨L, L', _, _, _, _, hLL', A₀, Tm, c, ε, a, β, u, βC, ιC, hdim, h7, h8, hC, hker, hι,
    hβ⟩ := h
  refine ⟨L', _, RQ.numberField_of_fd L', G15Ram.bcL' hLL' A₀, Tm, a, β, ε, L, h8, hC,
    fun p hp hP => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  exact G15Ram.localGlue_of_baseChange hLL' hR6 hTors (hU p) (hPℓ p hP) A₀ hdim h7 hC βC hker ιC
    hι hβ

/-- **`G15RamG` from the packs `G7LocalPackBC` (proved).** -/
theorem g15RamG_of_packBC (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ) {L : Type}
    [Field L] [NumberField L] {A : AbVar L} (D : ModData L A) (u : ℚ)
    (h5 : G7LocalPackBC 5 D.r5) (h3 : G7LocalPackBC 3 D.r3)
    (h11₅ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5)
    (h11₃ : G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) : G15RamG D u := by
  obtain ⟨K₅, _, _, A₅, Tm₅, a₅, β₅, ε₅, L₅, h8₅, hC₅, hG₅⟩ :=
    g8LocalPack_of_BC (P := fun p => p ≠ 5) hR6 hTors (fun p _ => hU p 5) (fun _ h => h) h5
  obtain ⟨K₃, _, _, A₃, Tm₃, a₃, β₃, ε₃, L₃, h8₃, hC₃, hG₃⟩ :=
    g8LocalPack_of_BC (P := fun p => p = 5) hR6 hTors (fun p _ => hU p 3)
      (fun p h => by rw [h]; norm_num) h3
  exact G15Ram.g15RamG_of_g7 D u h8₅ hC₅ hG₅ h8₃ hC₃ (hG₃ 5 (by norm_num) rfl) h11₅ h11₃

end G0ModNewform

end

-- END verbatim body of scratch/local-glue/LocalGlue.lean
end

section G14BridgeSec
-- BEGIN verbatim body of scratch/g14-trace/G14Bridge.lean

/-!
# g0-mod-field: glue steps G2, G4, G7 of the H decomposition (first range of `ModularConstituent`)

Task g0-mod-field (2026-11-13). `ModularConstituent` (scratch/g0-split/Split.lean, piece 10)
covers G2, G4, G7-G16 of docs/research/h-decomposition.md §3. This file takes the range
G2 (fibre field `K`), G4 (Hom field `L`, `[L:ℚ] ≤ D`), G7 (scalar descent to `L'`,
`[L':ℚ] ≤ Q·M`), for `S = S_mul`, `R = D` (the instance `SixContactMin`).

Outputs (`def … : Prop`): `G2Out Y Φ u P` (with `RationalFibre`), `G4Out u P`, `G7Out u P`, and the clause list `G7Data`
with `G7OutUnr u P` (G7 with the twist: `L'` unramified outside `T`), for a `ℚ̄`-object `P` of
`Y₃` over `J(u)` (`FibreCtx`). The descent datum of B1 on the actual `A` is `DescentDatum`
(maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)`, `a_σ`, sign cocycle `ε`).

Proved (no `sorry`, standard axioms):
* `g2Out_of_cover`: G2's bookkeeping (a splitting field of a separable polynomial of degree
  `≤ 324` is Galois of degree `≤ 324!`).
* `descentDatum_of_conjugacy`: B1's normalization (N5 L645-663): conjugacy isogenies with
  rational discrepancy `c` give `a_σ = |ker m_σ|^{-1/4}` and the sign cocycle `ε = sgn c`.
* `g4Out_of_kernelField`: G4's bookkeeping (Hom field `L = E ⊔ K` Galois,
  `[L:ℚ] ≤ F₀·3^{r²} ≤ D` by Minkowski's bound, model by base change, B1).
* `g7Out_of_g4Out`, `g7OutUnr_of_g4Out`: G7 = B2-B3 on the actual descent datum
  (`b2_of_leaves`, `GlueB3Unram.unramified_outside_noLeaf`, `b3_of_cochain`, `degree_le_QM`) and the
  model over `L'` (`isModelOver_baseChange`, transitivity of base change).
* `fieldDescent`, `fieldDescentUnr`: the composite G2 → G4 → G7.
* `modularConstituent_of_ranges`: `ModularConstituentG` (part_split's `ModularConstituent` over
  `PkgI3.AbVar`) from this range and the next ranges bundled as `AfterG7`.

Remaining (named Props): `FibreCoverExists` (G2: Prop. TS + Lemma NV), `KernelFieldExists` (G4:
Weil restriction, Galois image in `GL_r(ℤ)`, inertia on the Tate module, the conjugacy isogenies
`ConjugacyData`), `UnramifiedSup` (compositum of unramified fields; STANDARD), the four B2 leaves
of glue-descent (`LeafHasse`, `LeafLocalTwo`, `LeafSqrtCrit`, `LeafUnramified`), and `AfterG7`
(G8-G16, the other two tasks).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField

/-- Intermediate fields of `ℚ̄/ℚ`. -/
abbrev IF : Type := IntermediateField ℚ Qbar

/-- `T = S_mul ∪ supp M_{S_mul}(u)`, the ramification set (N5 L528). -/
noncomputable def T (u : ℚ) : Finset ℕ := GlueDescent.ramSet Mult.S_mul u

/-- `A`, an abelian variety over the subfield `L ⊆ ℚ̄`, is a model of the surface of the
`ℚ̄`-object `P`: `A_{ℚ̄} ≅ P.A` as `ℚ̄`-schemes (base change along the inclusion `L ⊆ ℚ̄`). -/
def IsModelOver (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  Nonempty ((A.baseChange Qbar).X ≅ P.A.X)

/-- The algebra `L → L'` for `L ≤ L'`. -/
@[instance_reducible] noncomputable def incAlg {L L' : IF} (h : L ≤ L') : Algebra L L' :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- **`A/L` is a QM model of `P`**: the base change to `L` of the abelian surface of an object
`PK` of `Y₃`'s moduli problem (QM by `𝒪` with level-3 structure) over a subfield `K ≤ L`, itself a
model of `P`'s surface. Such an `A` has good reduction away from `3` (G3,
`LeafQM.AV.QML3.goodReduction`), unlike an arbitrary model (a twist by a cocycle ramified at
`p ∉ T` has bad reduction at `p`), so the later steps (G11, G15) hold for every such `A`. -/
def IsQMModel (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  ∃ (K : IF) (hKL : K ≤ L) (PK : QML3 K), IsModelOver K PK.A P ∧
    A = @PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)

/-- **The fibre context** (the hypotheses of `ModularConstituent`): moduli data `(Y, Φ, π)` with
R1-R2's clauses, `u ∉ 𝒞`, and a `ℚ̄`-point `y` of `Y₃` carrying the object `P` and lying over
`J(u)`. -/
def FibreCtx (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) : Prop :=
  R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ u ∉ contactSet ∧
  ∃ y : fieldPt Qbar ⟶ Y, Φ Qbar y = M3.mk P ∧
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u))

/-- **A rational fibre over `K`** (Glazer N5 L528: "Choose a fiber `A/K`"): `PK` is an object of
`Y₃` over `K ⊆ ℚ̄` at a `K`-point `yK` whose base change to `ℚ̄` carries `P` (so `yK` lies over the
`ℚ̄`-point of `P`, `Φ` being a bijection), and `PK.A` is a model of `P`'s surface. Unlike an
arbitrary `K`-model (a twist of `PK.A` by a cocycle ramified outside `T` can have bad
reduction there), `PK.A` is the fibre of the universal family and has good reduction away
from `3` (G3). -/
def RationalFibre (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (P : QML3 Qbar) (K : IF)
    (PK : QML3 K) : Prop :=
  (∃ yK : fieldPt K ⟶ Y, Φ K yK = M3.mk PK ∧ Φ Qbar (fieldMap K.val ≫ yK) = M3.mk P) ∧
    IsModelOver K PK.A P

/-! ## The outputs of G2, G4, G7 -/

/-- **G2's output (Lemma PR(i), N5 L524-529).** A finite Galois `K ⊆ ℚ̄` with `[K:ℚ] ≤ F₀ = 324!`,
unramified outside `T`, with a rational fibre `PK/K` over `P` (Glazer: "Choose a fiber `A/K`";
`RationalFibre`). -/
def G2Out (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (K : IF) (_ : FiniteDimensional ℚ K) (_ : IsGalois ℚ K),
    Module.finrank ℚ K ≤ heightF0 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) ∧
    ∃ PK : QML3 K, RationalFibre Y Φ P K PK

/-- `A(ℚ̄)` as an additive group, for `A` over `L ⊆ ℚ̄`. -/
abbrev PtQ (L : IF) (A : PkgI3.AbVar L) : Type := Additive (A.Pt Qbar)

/-- **The descent datum of B1 on the actual `A` (N5 L632-663).** `ε` is a normalized
locally constant sign 2-cocycle of `G_ℚ` inflated from `Gal(L/ℚ)`, and it is the cocycle of `A`:
there are maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` (`μ_σ : ^σA → A` the `B`-linear conjugacy isogeny over
`L`, `σ` acting on coordinates) and reals `a_σ > 0` (`a_σ = (deg μ_σ)^{-1/4}`) with
* `a` inflated from `Gal(L/ℚ)` with `a = 1` on `G_L`,
* `m_σ` the Galois action of `σ` for `σ ∈ G_L` (`μ_σ = 1` there),
* `m_{σk} = m_σ m_k`, `m_{kσ} = m_k m_σ` for `k ∈ G_L` (`μ` inflated from `Gal(L/ℚ)`, defined
  over `L`),
* `m_σ` commutes with every `L`-endomorphism of `A` (`μ_σ` is `B`-linear and `L` is the Hom
  field),
* `m_σ` surjective with finite kernel (an isogeny composed with a bijection),
* `m_σ m_τ = c(σ,τ) m_{στ}` with `c = n/d ∈ ℚ^×` (the discrepancy commutes with `B`), and
  `a_σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}` (N5 L651-660: `ν = aμ`, `ν_σ ^σν_τ = ε ν_{στ}`).
* `m_σ` is algebraic: it is induced by a finite surjective morphism of schemes
  `F_σ : A → A` (`μ_σ`, composed with the identification of the underlying schemes of `^σA` and
  `A`): `m_σ(x) = F_σ ∘ x ∘ Spec(σ)` (G14's trace identities reduce `F_σ` modulo primes).
The maps `m_σ` are on points, hence independent of `ℓ`; on `V_ℓ(A)` they give G8's
`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ σ` (N5 L725-727). -/
def DescentDatum (L : IF) (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) : Prop :=
  IsSignCocycle ε ∧ InflatedFrom L ε ∧ ε 1 1 = 1 ∧
  ∃ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ),
    (∀ σ, 0 < a σ) ∧
    (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) ∧
    (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
    (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
    (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
    (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
    (∀ σ τ, ∃ n d : ℤ, n ≠ 0 ∧ d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ) ∧
        (((a σ * a τ * ((n : ℝ) / d) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) ∧
    (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ)

/-! ## B1's normalization (proved): from conjugacy isogenies to the sign cocycle -/

/-- The sign of a rational, as `±1 ∈ ℂ^×` (`1` for `q > 0`). -/
noncomputable def sgnU (q : ℚ) : ℂˣ := if 0 < q then 1 else -1

theorem sgnU_sq (q : ℚ) : sgnU q ^ 2 = 1 := by
  unfold sgnU; split_ifs <;> simp

theorem sgnU_mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : sgnU (q * r) = sgnU q * sgnU r := by
  unfold sgnU
  rcases lt_or_gt_of_ne hq with hq' | hq' <;> rcases lt_or_gt_of_ne hr with hr' | hr'
  · rw [if_pos (mul_pos_of_neg_of_neg hq' hr'), if_neg (not_lt.2 hq'.le),
      if_neg (not_lt.2 hr'.le)]; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_neg_of_pos hq' hr').le), if_neg (not_lt.2 hq'.le),
      if_pos hr']; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_pos_of_neg hq' hr').le), if_pos hq',
      if_neg (not_lt.2 hr'.le)]; simp
  · rw [if_pos (mul_pos hq' hr'), if_pos hq', if_pos hr']; simp

/-- `sgn(q)·|q| = q`, in `ℂ`. -/
theorem sgnU_mul_abs (q : ℚ) : ((sgnU q : ℂˣ) : ℂ) * ((|(q : ℝ)| : ℝ) : ℂ) = ((q : ℝ) : ℂ) := by
  unfold sgnU
  split_ifs with h
  · have : (0 : ℝ) < q := by exact_mod_cast h
    rw [abs_of_pos this]; simp
  · have : (q : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 h
    rw [abs_of_nonpos this]; push_cast; ring

/-- **The conjugacy isogenies before normalization (N5 L632-645; the content of G4 + B1's
geometric half).** Maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` with the first four clauses of
`DescentDatum`; the discrepancy `c(σ,τ) = n/d ∈ ℚ^×` with `d·m_σ m_τ = n·m_{στ}`, a 2-cocycle
inflated from `Gal(L/ℚ)` with `c(1,1) = 1`; and degree multiplicativity in the form
`|ker m_σ|·|ker m_τ| = c(σ,τ)⁴·|ker m_{στ}|` (`deg μ = |ker μ(ℚ̄)|` in characteristic 0,
`deg[n] = n⁴` on a surface); and algebraicity: `m_σ(x) = F_σ ∘ x ∘ Spec(σ)` for a finite
surjective scheme morphism `F_σ : A → A`. -/
def ConjugacyData (L : IF) (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A))
    (c : GQ → GQ → ℚ) : Prop :=
  (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
  (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
  (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
  (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
  (∀ σ τ, c σ τ ≠ 0 ∧ ∃ n d : ℤ, d ≠ 0 ∧ c σ τ = n / d ∧
      d • (m σ).comp (m τ) = n • m (σ * τ)) ∧
  (∀ σ τ ρ, c (σ * τ) ρ * c σ τ = c τ ρ * c σ (τ * ρ)) ∧
  (∀ σ σ' τ τ' : GQ, (∀ x ∈ L, act σ x = act σ' x) → (∀ x ∈ L, act τ x = act τ' x) →
      c σ τ = c σ' τ') ∧
  c 1 1 = 1 ∧
  (∀ σ τ, (Nat.card (m σ).ker : ℚ) * Nat.card (m τ).ker = c σ τ ^ 4 * Nat.card (m (σ * τ)).ker) ∧
  (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ)

/-- The Galois action of `σ' ∈ Aut(ℚ̄/L)` on `A(ℚ̄)` is bijective. -/
theorem galAct_bijective {L : IF} (A : PkgI3.AbVar L) (σ' : Qbar ≃ₐ[L] Qbar) :
    Function.Bijective (A.galAct σ') := by
  have key : ∀ (g h : Qbar ≃ₐ[L] Qbar) (P : A.Pt Qbar),
      A.galAct g (A.galAct h P) = A.galAct (g * h) P := by
    intro g h P
    show PkgI3.AbVar.galHom g ≫ PkgI3.AbVar.galHom h ≫ P = PkgI3.AbVar.galHom (g * h) ≫ P
    rw [PkgI3.AbVar.galHom_mul, Category.assoc]
  have one : ∀ P : A.Pt Qbar, A.galAct 1 P = P := by
    intro P
    show PkgI3.AbVar.galHom 1 ≫ P = P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  refine ⟨fun P Q h => ?_, fun Q => ⟨A.galAct σ'⁻¹ Q, ?_⟩⟩
  · have := congrArg (A.galAct σ'⁻¹) h
    rwa [key, key, inv_mul_cancel, one, one] at this
  · rw [key, mul_inv_cancel, one]

/-- `k ∈ G_L` as an `L`-automorphism of `ℚ̄`. -/
noncomputable def toLAut {L : IF} (k : GQ) (hk : k ∈ GQL L) : Qbar ≃ₐ[L] Qbar :=
  AlgEquiv.ofRingEquiv (f := (act k).toRingEquiv) (fun x => mem_GQL.mp hk x x.2)

theorem toLAut_apply {L : IF} (k : GQ) (hk : k ∈ GQL L) (x : Qbar) : toLAut k hk x = act k x :=
  rfl

/-- The kernel sizes of `m_k`, `m_{σk}`, `m_{kσ}` for `k ∈ G_L` (from the first two clauses of
`ConjugacyData`). -/
theorem card_ker_GL {L : IF} {A : PkgI3.AbVar L} {m : GQ → (PtQ L A →+ PtQ L A)}
    (hgal : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (hinfl : ∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ))
    (σ k : GQ) (hk : k ∈ GQL L) :
    Nat.card (m k).ker = 1 ∧ Nat.card (m (σ * k)).ker = Nat.card (m σ).ker ∧
      Nat.card (m (k * σ)).ker = Nat.card (m σ).ker := by
  have hmk : m k = MonoidHom.toAdditive (A.galAct (toLAut k hk)) :=
    hgal k (toLAut k hk) (toLAut_apply k hk)
  have hbij : Function.Bijective (m k) := by
    rw [hmk]; exact galAct_bijective A (toLAut k hk)
  have hker : (m k).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : m k x = m k 0 := by rw [map_zero]; exact hx
    exact hbij.1 this
  refine ⟨by rw [hker]; simp, ?_, ?_⟩
  · rw [(hinfl σ k hk).1]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨m k x, x.2⟩) ⟨?_, ?_⟩)
    · intro x y h
      exact Subtype.ext (hbij.1 (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hbij.2 y
      exact ⟨⟨x, hy⟩, rfl⟩
  · have hk2 : ((m k).comp (m σ)).ker = (m σ).ker := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply]
      constructor
      · intro h
        have : m k (m σ x) = m k 0 := by rw [map_zero]; exact h
        exact hbij.1 this
      · intro h; rw [h, map_zero]
    rw [(hinfl σ k hk).2, hk2]

/-- `a_σ = |ker m_σ|^{-1/4}` (`= (deg μ_σ)^{-1/4}`, N5 L645). -/
noncomputable def normA {L : IF} {A : PkgI3.AbVar L} (m : GQ → (PtQ L A →+ PtQ L A)) (σ : GQ) :
    ℝ := (Nat.card (m σ).ker : ℝ) ^ (-(1 / 4 : ℝ))

/-- **B1's normalization, proved** (N5 L645-663): from the conjugacy isogenies, `ε = sgn c` is a
normalized locally constant sign cocycle inflated from `Gal(L/ℚ)`, and `(m, a = |ker m|^{-1/4},
ε)` is a descent datum. -/
theorem descentDatum_of_conjugacy (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) (c : GQ → GQ → ℚ)
    (h : ConjugacyData L A m c) : DescentDatum L A (fun σ τ => sgnU (c σ τ)) := by
  obtain ⟨hgal, hinfl, hend, hfin, hc, hcoc, hcinf, hc11, hdeg, halg⟩ := h
  have hkerL := card_ker_GL hgal hinfl
  have hcard : ∀ σ, 0 < Nat.card (m σ).ker := fun σ => by
    haveI : Finite (m σ).ker := (hfin σ).2.to_subtype
    exact Nat.card_pos
  -- the sign cocycle
  have hloc : IsLocallyConstant (Function.uncurry fun σ τ => sgnU (c σ τ)) := by
    refine isLocallyConstant_of_openSubgroup ((GQL L).prod (GQL L))
      (by rw [Subgroup.coe_prod]; exact L.fixingSubgroup_isOpen.prod L.fixingSubgroup_isOpen)
      _ ?_
    rintro ⟨σ, τ⟩ ⟨k₁, k₂⟩ hk
    rw [Subgroup.mem_prod] at hk
    simp only [Function.uncurry_apply_pair, Prod.mk_mul_mk]
    congr 1
    refine (hcinf σ (σ * k₁) τ (τ * k₂) ?_ ?_).symm
    · intro x hx
      show act σ x = act σ (act k₁ x)
      rw [mem_GQL.mp hk.1 x hx]
    · intro x hx
      show act τ x = act τ (act k₂ x)
      rw [mem_GQL.mp hk.2 x hx]
  refine ⟨⟨hloc, fun σ τ => sgnU_sq _, fun σ τ ρ => ?_⟩, ?_, ?_, m, normA m, ?_, ?_, hgal, hinfl,
    hend, hfin, ?_, halg⟩
  · rw [← sgnU_mul (hc _ _).1 (hc _ _).1, ← sgnU_mul (hc _ _).1 (hc _ _).1, hcoc]
  · exact fun σ σ' τ τ' h1 h2 => by simp only [hcinf σ σ' τ τ' h1 h2]
  · show sgnU (c 1 1) = 1
    rw [hc11]; unfold sgnU; simp
  · intro σ; unfold normA; exact Real.rpow_pos_of_pos (by exact_mod_cast hcard σ) _
  · intro σ k hk
    obtain ⟨h1, h2, h3⟩ := hkerL σ k hk
    unfold normA
    rw [h1, h2, h3]
    simp
  · intro σ τ
    obtain ⟨hc0, n, d, hd, hcnd, hnd⟩ := hc σ τ
    have hn : n ≠ 0 := by
      rintro rfl; apply hc0; rw [hcnd]; simp
    refine ⟨n, d, hn, hd, hnd, ?_⟩
    have hx : (0 : ℝ) < Nat.card (m σ).ker := by exact_mod_cast hcard σ
    have hy : (0 : ℝ) < Nat.card (m τ).ker := by exact_mod_cast hcard τ
    have hz : (0 : ℝ) < Nat.card (m (σ * τ)).ker := by exact_mod_cast hcard (σ * τ)
    have hdegR : (Nat.card (m σ).ker : ℝ) * Nat.card (m τ).ker =
        |(c σ τ : ℝ)| ^ 4 * Nat.card (m (σ * τ)).ker := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (hdeg σ τ)
      push_cast at this
      rw [this, pow_abs, abs_of_nonneg (by positivity)]
    have hcR : ((n : ℝ) / d) = (c σ τ : ℝ) := by rw [hcnd]; push_cast; rfl
    have habs : (0 : ℝ) < |(c σ τ : ℝ)| := abs_pos.mpr (by exact_mod_cast hc0)
    have key : normA m σ * normA m τ * |(c σ τ : ℝ)| = normA m (σ * τ) := by
      unfold normA
      rw [← Real.mul_rpow hx.le hy.le, hdegR, Real.mul_rpow (by positivity) hz.le]
      rw [show |(c σ τ : ℝ)| ^ 4 = |(c σ τ : ℝ)| ^ ((4 : ℕ) : ℝ) by norm_cast,
        ← Real.rpow_mul habs.le]
      rw [show ((4 : ℕ) : ℝ) * (-(1 / 4 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
      field_simp
    rw [hcR]
    have e1 : ((normA m σ * normA m τ * (c σ τ : ℝ) : ℝ) : ℂ) =
        ((sgnU (c σ τ) : ℂˣ) : ℂ) * ((normA m σ * normA m τ * |(c σ τ : ℝ)| : ℝ) : ℂ) := by
      have h := sgnU_mul_abs (c σ τ)
      push_cast at h ⊢
      linear_combination (-((normA m σ : ℂ) * (normA m τ : ℂ))) * h
    rw [e1, key]

/-! ## Sanity check: `DescentDatum` is satisfiable (an abelian variety over `ℚ`, `ε = 1`) -/

theorem mem_GQL_bot (σ : GQ) : σ ∈ GQL (⊥ : IF) := by
  rw [mem_GQL]
  intro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact (act σ).commutes r

theorem galAct_mul {L : IF} (A : PkgI3.AbVar L) (g h : Qbar ≃ₐ[L] Qbar) (P : A.Pt Qbar) :
    A.galAct g (A.galAct h P) = A.galAct (g * h) P := by
  show PkgI3.AbVar.galHom g ≫ PkgI3.AbVar.galHom h ≫ P = PkgI3.AbVar.galHom (g * h) ≫ P
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

/-- **Sanity check (proved).** For every abelian variety `A` over `ℚ` (here `L = ⊥ ⊆ ℚ̄`), the
Galois action itself is a descent datum with `ε = 1`, `a = 1`, `F_σ = id`. So `DescentDatum` is
not contradictory. -/
theorem descentDatum_bot (A : PkgI3.AbVar (⊥ : IF)) : DescentDatum ⊥ A (fun _ _ => 1) := by
  let m : GQ → (PtQ ⊥ A →+ PtQ ⊥ A) := fun σ =>
    MonoidHom.toAdditive (A.galAct (toLAut σ (mem_GQL_bot σ)))
  have hmul : ∀ σ τ : GQ, (m σ).comp (m τ) = m (σ * τ) := by
    intro σ τ
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (A.galAct _ (A.galAct _ (Additive.toMul x))) =
      Additive.ofMul (A.galAct _ (Additive.toMul x))
    rw [galAct_mul]
    rfl
  have hbij : ∀ σ, Function.Bijective (m σ) := fun σ => galAct_bijective A _
  refine ⟨⟨IsLocallyConstant.const 1, fun _ _ => by simp, fun _ _ _ => by simp⟩,
    fun _ _ _ _ _ _ => rfl, rfl, m, fun _ => 1, fun _ => one_pos, fun _ _ _ => ⟨rfl, rfl, rfl⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ σ' h
    have : σ' = toLAut σ (mem_GQL_bot σ) := AlgEquiv.ext h
    rw [this]
  · intro σ k _
    exact ⟨(hmul σ k).symm, (hmul k σ).symm⟩
  · intro σ f
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (PkgI3.AbVar.galHom _ ≫ (Additive.toMul x ≫ f.hom)) =
      Additive.ofMul ((PkgI3.AbVar.galHom _ ≫ Additive.toMul x) ≫ f.hom)
    rw [Category.assoc]
  · intro σ
    refine ⟨(hbij σ).2, ?_⟩
    have : ((m σ).ker : Set (PtQ ⊥ A)) = {0} := by
      ext x
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_singleton_iff]
      constructor
      · intro h; exact (hbij σ).1 (h.trans (map_zero _).symm)
      · rintro rfl; exact map_zero _
    rw [this]; exact Set.finite_singleton 0
  · intro σ τ
    refine ⟨1, 1, one_ne_zero, one_ne_zero, by rw [one_smul, one_smul, hmul], by simp⟩
  · refine ⟨fun _ => 𝟙 _, fun σ => ⟨inferInstance, inferInstance, fun x => ?_⟩⟩
    show (PkgI3.AbVar.galHom (toLAut σ (mem_GQL_bot σ)) ≫ Additive.toMul x).left =
      Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (Additive.toMul x).left ≫ 𝟙 _
    erw [Category.comp_id]
    rfl

/-- **G4's output (N5 L532-563 and the B1 normalization L632-663).** A finite Galois `L ⊆ ℚ̄`
(the Hom field) with `[L:ℚ] ≤ D`, unramified outside `T`, a QM model `A/L` of `P` (`IsQMModel`), and
the descent datum `ε` of `A` (`DescentDatum`). -/
def G4Out (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
    Module.finrank ℚ L ≤ heightD ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
    ∃ (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ), IsQMModel L A P ∧ DescentDatum L A ε

/-- **G7's output (B2-B3, N5 L664-716).** The data of G4 (`L`, `A/L`, `ε`), and: a Dirichlet
character `χ` mod `N`, a locally constant cochain `β : G_ℚ → ℂ^×` with `β² = χ` and `∂β = ε`, and
the kernel field `L' ⊇ L` of `β|_{G_L}`: finite Galois, `G_{L'} = G_L ∩ ker β`,
`[L':ℚ] ≤ Q_D · M_{S_mul}(u)`, and the base change `A_{L'}` is a model of `P`'s surface. -/
def G7Out (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ),
    IsQMModel L A P ∧ DescentDatum L A ε ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
  ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
    (∀ x y, β x * β y = ε x y * β (x * y)) ∧
    (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
    (Module.finrank ℚ L' : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
    IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P

/-! ## Transitivity of base change -/

/-- `(A_{L'})_{ℚ̄} ≅ A_{ℚ̄}` for `L ≤ L' ⊆ ℚ̄` (pasting of pullbacks). -/
noncomputable def baseChangeTrans {L L' : IF} (h : L ≤ L') (A : PkgI3.AbVar L) :
    ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg h)).baseChange Qbar).X ≅
      (A.baseChange Qbar).X := by
  letI := incAlg h
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap L' Qbar)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L L')) =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
    rw [← Spec.map_comp]
    congr 1
  exact ((Over.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap L' Qbar)))
      (Spec.map (CommRingCat.ofHom (algebraMap L L')))).app A.X).symm ≪≫
    eqToIso (congrArg (fun f => (Over.pullback f).obj A.X) hcomp)

theorem isModelOver_baseChange {L L' : IF} (h : L ≤ L') (A : PkgI3.AbVar L) (P : QML3 Qbar)
    (hA : IsModelOver L A P) :
    IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg h)) P := by
  obtain ⟨e⟩ := hA
  exact ⟨baseChangeTrans h A ≪≫ e⟩

theorem IsQMModel.isModelOver {L : IF} {A : PkgI3.AbVar L} {P : QML3 Qbar}
    (h : IsQMModel L A P) : IsModelOver L A P := by
  obtain ⟨K, hKL, PK, hPK, rfl⟩ := h
  exact isModelOver_baseChange hKL PK.A P hPK

/-! ## G7 from G4 (proved) -/

/-- `max S_mul ≤ D` (copied from `ZInQKernel/Main.lean`, `ZInQ.Mult.le_heightD_of_mem_S_mul`). -/
theorem le_heightD_of_mem_S_mul {p : ℕ} (hp : p ∈ Mult.S_mul) : p ≤ heightD :=
  (Mult.le_R_of_mem_S_mul hp).trans_eq ((Size.R_eq_D catalogueBound8).trans Mult.D_eq_heightD)

theorem admissible_S_mul :
    (∀ p ∈ Mult.S_mul, p.Prime) ∧ (∀ p ∈ Mult.S_mul, (p : ℝ) ≤ (heightD : ℝ)) ∧
      (10 : ℝ) ^ 12 ≤ (heightD : ℝ) :=
  ⟨fun _ hp => Mult.prime_of_mem_S_mul hp,
   fun _ hp => by exact_mod_cast le_heightD_of_mem_S_mul hp,
   by exact_mod_cast Compiler.Precision.ten_pow_twelve_le_heightD⟩

/-- **G7 (B2-B3 on the actual descent datum), proved** from G4's output and glue-descent's four
B2 leaves, by `GlueDescent.B3Q.b3_degree_le_QM` at `S = S_mul`, `R = D`, `η = 1`. -/
theorem g7Out_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7Out u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  obtain ⟨N, hN, χ, β, L', hβl, hβs, hβe, hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_degree_le_QM hHasse hTwo hSq hUnr Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u L hLD
      ε hε hinf h11 hram 1 (fun _ => by simp) (IsLocallyConstant.const 1)
  exact ⟨L, hfd, hgal, A, ε, hA, hD, hram, N, hN, χ, β, L', hfd', hgal', hle, hβl, hβs, hβe, hGL',
    hdeg, isModelOver_baseChange hle A P hA.isModelOver⟩

/-! ## G7 with the twist: `L'` unramified outside `T` (proved) -/

/-- **B2 over `G_ℚ` with the level of `χ` exposed** (the proof of
`GlueDescent.B2Q.b2_of_leaves`, copied; the only change is the extra output
`N = chiLevel T₋ = ∏_{p ∈ T₋} lev p` with `T₋ ⊆ T`, `lev 2 = 4`, `lev p = p`). -/
theorem b2_of_leaves_level (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ),
      (∃ Tm ⊆ T, N = chiLevel Tm) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T) ∧
      orderOf χ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      ∀ x y, β x * β y = ε x y * β (x * y) := by
  classical
  let Tm := T.filter (fun p => ∃ hp : p.Prime, ¬ SignCob (pull (resp ⟨p, hp⟩) ε))
  have hloc : ∀ p : Nat.Primes, ¬ SignCob (pull (resp p) ε) ↔ (p : ℕ) ∈ Tm := by
    intro p
    constructor
    · intro h
      refine Finset.mem_filter.2 ⟨?_, p.2, h⟩
      by_contra hpT
      exact h (hUnr L ε hε hinf p (hram p hpT))
    · intro h
      obtain ⟨_, hp, h'⟩ := Finset.mem_filter.1 h
      exact h'
  have hTmP : ∀ q ∈ Tm, q.Prime := fun q hq => hT q (Finset.filter_subset _ _ hq)
  haveI hN : NeZero (chiLevel Tm) := ⟨(chiLevel_pos Tm hTmP).ne'⟩
  obtain ⟨_, hsupp, hord⟩ := exists_chi T Tm hT (Finset.filter_subset _ _)
  let χ := chi Tm
  let β₀ : GQ → ℂˣ := fun x => sqrtU (galChar χ x)
  have hβ₀ : ∀ x, β₀ x ^ 2 = galChar χ x := fun x => sqrtU_sq _
  have hl : IsLocallyConstant β₀ := (galChar_isLocallyConstant χ).comp sqrtU
  have agree : ∀ p : Nat.Primes,
      SignCob (pull (resp p) ε) ↔ SignCob (pull (resp p) (dB β₀)) := by
    intro p
    rw [pull_dB, signCob_dB_iff ((galChar χ).comp (resp p)) (β₀ ∘ resp p) (fun x => hβ₀ _)
      (hl.comp_continuous (resp_continuous p))]
    obtain ⟨u, hu1, hu2⟩ := exists_crt_unit (chiLevel Tm) p p.2
    have hsq := hSq p (chiLevel Tm) χ u hu1 hu2
    have hsq' : (∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧
        ∀ x, φ x ^ 2 = ((galChar χ).comp (resp p)) x) ↔ χ.toUnitHom u = 1 := hsq
    rw [hsq', chi_toUnitHom_crt Tm hTmP p p.2 u hu1 hu2]
    by_cases h : (p : ℕ) ∈ Tm
    · rw [if_pos h]
      have hne : (-1 : ℂˣ) ≠ 1 := by
        intro h1
        have := congrArg (fun z : ℂˣ => (z : ℂ)) h1
        norm_num at this
      constructor
      · intro hc; exact absurd hc ((hloc p).mpr h)
      · intro h1; exact absurd h1 hne
    · rw [if_neg h]
      simp only [iff_true]
      by_contra hc
      exact h ((hloc p).mp hc)
  obtain ⟨β, hβl, hβs, hβe⟩ := exists_beta (G := GQ) GQp resp resp_continuous hHasse hTwo ε hε
    (galChar χ) β₀ hβ₀ hl agree
  exact ⟨chiLevel Tm, hN, χ, β, ⟨Tm, Finset.filter_subset _ _, rfl⟩, hsupp, hord, hβl, hβs, hβe⟩

/-- **B3 from a given B2 cochain** (the proof of `GlueDescent.B3Q.b3_of_leaves`, copied, with
`b2_of_leaves`' output taken as hypotheses so that the twist `η` may depend on it). -/
theorem b3_of_cochain
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (β₁ : GQ → ℂˣ) (hβl₁ : IsLocallyConstant β₁)
    (hβs₁ : ∀ x, β₁ x ^ 2 = galChar χ x) (hβe₁ : ∀ x y, β₁ x * β₁ y = ε x y * β₁ (x * y))
    (tw : GQ →* ℂˣ) (htw : ∀ x, tw x ^ 2 = 1) (htwl : IsLocallyConstant tw) :
    ∃ L' : IntermediateField ℚ (AlgebraicClosure ℚ),
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β₁ σ * tw σ = 1) ∧
      Module.finrank ℚ L' ≤ 2 * orderOf χ * Module.finrank ℚ L := by
  let β : GQ → ℂˣ := fun x => β₁ x * tw x
  have hβl : IsLocallyConstant β := hβl₁.mul htwl
  have hβs : ∀ x, β x ^ 2 = galChar χ x := twist_sq (galChar χ) hβs₁ tw htw
  have hβe : ∀ x y, β x * β y = ε x y * β (x * y) := twist hβe₁ tw
  have hεN := inflatedNormalized_of L ε hε hinf h11
  have hβ : IsCochainFor ε β := hβe
  let K' : Subgroup GQ := kernelSubgroup hβ hεN
  have hHopen : IsOpen ((GQL L : Subgroup GQ) : Set GQ) := L.fixingSubgroup_isOpen
  have hK'set : (K' : Set GQ) = (GQL L : Set GQ) ∩ β ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_kernelSubgroup hβ hεN
  have hK'open : IsOpen (K' : Set GQ) := by
    rw [hK'set]; exact hHopen.inter (hβl.isOpen_fiber 1)
  have hK'closed : IsClosed (K' : Set GQ) := Subgroup.isClosed_of_isOpen K' hK'open
  let K'c : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    { toSubgroup := K', isClosed' := hK'closed }
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField K'
  have hfix : L'.fixingSubgroup = K' := InfiniteGalois.fixingSubgroup_fixedField K'c
  have hGL' : ∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1 := by
    intro σ
    show σ ∈ L'.fixingSubgroup ↔ _
    rw [hfix]
    exact mem_kernelSubgroup hβ hεN
  have hm := orderOf_pos_dirichlet χ
  have hpow : ∀ s ∈ GQL L, β s ^ (2 * orderOf χ) = 1 := by
    intro s _
    rw [pow_mul, hβs]
    show (MulChar.mulEquivToUnitHom χ (cyc N s)) ^ orderOf χ = 1
    rw [← MonoidHom.pow_apply, ← map_pow, pow_orderOf_eq_one, map_one, MonoidHom.one_apply]
  haveI : (GQL L).Normal := (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hidx := index_kernel_le hβ hεN (2 * orderOf χ) (by positivity) hpow
  have hfd : FiniteDimensional ℚ L' :=
    (InfiniteGalois.isOpen_iff_finite L').mp (by rw [hfix]; exact hK'open)
  have hL : Module.finrank ℚ L = (GQL L).index := IntermediateField.finrank_eq_fixingSubgroup_index
      (L := L)
  have hL' : Module.finrank ℚ L' = K'.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := L'), hfix]
    rfl
  have hgal : IsGalois ℚ L' :=
    (InfiniteGalois.normal_iff_isGalois L').mp (by rw [hfix]; exact kernelSubgroup_normal hβ hεN)
  have hle : L ≤ L' := by
    intro x hx
    show x ∈ IntermediateField.fixedField K'
    exact fun k => mem_GQL.mp (kernelSubgroup_le hβ hεN k.2) x hx
  refine ⟨L', hle, hfd, hgal, hGL', ?_⟩
  rw [hL', hL]; exact hidx

theorem two_mem_T (u : ℚ) : 2 ∈ T u :=
  Finset.mem_union_left _ (Mult.mem_S_mul_of_le Nat.prime_two (by norm_num))

/-- **The data of G7, clause by clause** (the interface handed to G8-G16). For the fibre `P`
over `J(u)`: the Hom field `L` (finite Galois, unramified outside `T`), the model `A/L` with its
descent datum `ε` (B1), the Dirichlet character `χ` mod `N` (`N = ∏_{p ∈ T₋} lev p` for some
`T₋ ⊆ T`, `lev 2 = 4`, `lev p = p`: `χ` is a product of odd characters mod `p` and mod `4`, N5
L677-683, which bounds the conductor of `β` at every prime, as G15 needs), the
cochain `β` (locally constant, `β² = χ`, `∂β = ε`, twisted so that inertia outside `T` dies), and
the kernel field `L' ⊇ L` of `β|_{G_L}`: `G_{L'} = G_L ∩ ker β`, `[L':ℚ] ≤ Q_D·M_{S_mul}(u)`,
`L'` unramified outside `T` (Galois form), and `A_{L'}` a model of `P`'s surface. -/
def G7Data (u : ℚ) (P : QML3 Qbar) (L : IF) (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ)
    [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF) (hLL' : L ≤ L') : Prop :=
  IsQMModel L A P ∧ DescentDatum L A ε ∧
  (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
  (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T u) ∧
  (∃ Tm ⊆ T u, N = chiLevel Tm) ∧
  IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
  (∀ x y, β x * β y = ε x y * β (x * y)) ∧
  (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
  (Module.finrank ℚ L' : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
  GlueB3Unram.GalUnramifiedOutside L' (T u) ∧
  IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P

/-- **G7's output with the twist** (N5 L702-716): the data of `G7Data` exist. -/
def G7OutUnr (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
    (L' : IF) (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL'

/-- **G7 with the twist, proved** from G4's output and the four B2 leaves: B2
(`b2_of_leaves`), the twist killing inertia outside `T` (`GlueB3Unram.unramified_outside_noLeaf`,
no leaf), B3 (`b3_of_cochain`) and the constants (`degree_le_QM`). -/
theorem g7OutUnr_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7OutUnr u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  have hT : ∀ p ∈ T u, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact Nat.prime_of_mem_primeFactors h
  obtain ⟨N, hN, χ, β₁, hlev, hsupp, hord, hβl₁, hβs₁, hβe₁⟩ :=
    b2_of_leaves_level hHasse hTwo hSq hUnr L ε hε hinf (T u) hT hram
  have hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1 :=
    inflatedNormalized_of L ε hε hinf h11
  obtain ⟨Q, -, hη, hηl, hunr⟩ := GlueB3Unram.unramified_outside_noLeaf L (T u) (two_mem_T u)
    hram ε hεN χ hsupp β₁ hβl₁ hβs₁ hβe₁
  obtain ⟨L', hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_of_cochain L ε hε hinf h11 χ β₁ hβl₁ hβs₁ hβe₁ _ hη hηl
  have hdegR := degree_le_QM Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u
    (Module.finrank ℚ L) (orderOf χ) hLD hord
  refine ⟨L, hfd, hgal, A, ε, N, hN, χ, fun x => β₁ x * (∏ q ∈ Q, GlueB3Unram.etaP q) x,
    L', hfd', hgal', hle, hA, hD, hram, hsupp, hlev, hβl₁.mul hηl, twist_sq (galChar χ) hβs₁ _ hη,
    twist hβe₁ _, hGL', ?_, hunr L' hGL', isModelOver_baseChange hle A P hA.isModelOver⟩
  calc (Module.finrank ℚ L' : ℝ) ≤ ((2 * orderOf χ * Module.finrank ℚ L : ℕ) : ℝ) := by
        exact_mod_cast hdeg
    _ = 2 * (orderOf χ : ℝ) * Module.finrank ℚ L := by push_cast; ring
    _ ≤ _ := hdegR

theorem g7Out_of_g7OutUnr (u : ℚ) (P : QML3 Qbar) (h : G7OutUnr u P) : G7Out u P := by
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hA, hD, hram, -, -, hβl, hβs,
    hβe, hGL', hdeg, -, hM⟩ := h
  exact ⟨L, hfd, hgal, A, ε, hA, hD, hram, N, hN, χ, β, L', hfd', hgal', hle, hβl, hβs, hβe, hGL',
    hdeg, hM⟩

/-! ## G2's bookkeeping (proved) -/

/-- **G2's input, the fibre cover (Prop. TS + Lemma NV, N5 L509-529; remaining).** There is a
separable `f ∈ ℚ[X]` of degree `≤ 324` (the fibre of the normalized cover of `P¹_u` over `u`)
whose splitting field `K = ℚ(roots of f) ⊆ ℚ̄` is unramified outside `T` and contains the residue
field of the point of `P` (a rational fibre `PK/K`, `RationalFibre`). -/
def FibreCoverOut (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) :
    Prop :=
  ∃ f : Polynomial ℚ, f.Separable ∧ f.natDegree ≤ 324 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u →
      UnramifiedAt (IntermediateField.adjoin ℚ (f.rootSet Qbar)) p) ∧
    ∃ PK : QML3 (IntermediateField.adjoin ℚ (f.rootSet Qbar)),
      RationalFibre Y Φ P (IntermediateField.adjoin ℚ (f.rootSet Qbar)) PK

/-- **G2, proved from the fibre cover**: the splitting field is Galois of degree `≤ 324!`
(`GlueRepo.Numerics.splitting_degree_le`). -/
theorem g2Out_of_cover (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ)
    (P : QML3 Qbar) (h : FibreCoverOut Y Φ u P) : G2Out Y Φ u P := by
  obtain ⟨f, hs, hd, hram, A, hA⟩ := h
  have hsp : f.IsSplittingField ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    Polynomial.IsSplittingField.finiteDimensional _ f
  have hgal : IsGalois ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    IsGalois.of_separable_splitting_field hs
  have hdeg : Module.finrank ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) ≤ heightF0 := by
    rw [(Polynomial.IsSplittingField.algEquiv _ f).toLinearEquiv.finrank_eq]
    exact GlueRepo.Numerics.splitting_degree_le f hs hd
  exact ⟨_, hfd, hgal, hdeg, hram, A, hA⟩

/-! ## G4's bookkeeping (proved) -/

/-- **Compositum of unramified fields (STANDARD; remaining, not in Mathlib v4.35).** If `E`
and `K` are finite over `ℚ` and unramified at `p`, so is `E ⊔ K` (Neukirch, *Algebraic Number
Theory*, I (8.?)/III, UNVERIFIED locator; a prime is unramified in a compositum iff it is in both
factors, for Galois factors). -/
def UnramifiedSup : Prop :=
  ∀ (E K : IF) [FiniteDimensional ℚ E] [FiniteDimensional ℚ K] [IsGalois ℚ E] [IsGalois ℚ K]
    (p : ℕ), UnramifiedAt E p → UnramifiedAt K p → UnramifiedAt (E ⊔ K) p

/-- **G4's input, the kernel field (N5 L540-563 and B1, L632-663; remaining).** For a field `K`
and model `A/K` as in G2's output: `W₀ = Res_{K/ℚ} A` has endomorphism lattice of rank `r ≤ 16F₀²`;
the image of `G_ℚ` on it is a finite subgroup `G ≤ GL_r(ℤ)` with kernel field `E`
(`[E:ℚ] = |G|`), unramified outside `T` (inertia at `p ∉ T` acts trivially on the Tate module of
`W₀`, which has good reduction there); and the base change `A_L` of `A` to the Hom field
`L = E ⊔ K` carries conjugacy isogenies `μ_σ : ^σA → A` over `L`, `B`-linear after the
Skolem-Noether correction, with rational discrepancy (`ConjugacyData`; B1's normalization to a
sign cocycle is proved, `descentDatum_of_conjugacy`). -/
def KernelFieldOut (u : ℚ) (P : QML3 Qbar) (K : IF) (A : PkgI3.AbVar K) : Prop :=
  ∃ (r : ℕ), r ≤ 16 * heightF0 ^ 2 ∧
  ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IF) (_ : FiniteDimensional ℚ E)
    (_ : IsGalois ℚ E), Module.finrank ℚ E = Nat.card G ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt E p) ∧
    ∃ (m : GQ → (PtQ (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right)) →+
        PtQ (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right))))
      (c : GQ → GQ → ℚ),
      ConjugacyData (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right)) m c

/-- **G4, proved from the kernel field**: `L = E ⊔ K` is finite Galois, unramified outside `T`
(`UnramifiedSup`), `[L:ℚ] ≤ [K:ℚ]·[E:ℚ] ≤ F₀·3^{r²} ≤ D` (Minkowski,
`GlueRepo.TorsionFree.card_le_three_pow`; `GlueRepo.Numerics.a8_field`), `A_L = (PK.A)_L` is a QM
model of `P` (`IsQMModel`), and B1's normalization gives the descent datum
(`descentDatum_of_conjugacy`). -/
theorem g4Out_of_kernelField (hSup : UnramifiedSup) (u : ℚ) (P : QML3 Qbar) (K : IF)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (hK : Module.finrank ℚ K ≤ heightF0)
    (hramK : ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) (PK : QML3 K)
    (hPK : IsModelOver K PK.A P) (h : KernelFieldOut u P K PK.A) : G4Out u P := by
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, m, c, hCD⟩ := h
  have hE : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := hEG ▸ GlueRepo.TorsionFree.card_le_three_pow G
  have hdeg : Module.finrank ℚ ↥(E ⊔ K) ≤ heightD :=
    GlueRepo.Numerics.a8_field E K Compiler.Precision.heightD_eq hK hE hr
  have : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  exact ⟨E ⊔ K, inferInstance, inferInstance, hdeg,
    fun p hp => hSup E K p (hramE p hp) (hramK p hp), _, _,
    ⟨K, le_sup_right, PK, hPK, rfl⟩, descentDatum_of_conjugacy _ _ m c hCD⟩

/-! ## The remaining glue as Props, and the composite -/

/-- **Remaining (G2): Prop. TS + Lemma NV on the actual fibre** (h-decomposition G2: inputs
R1(d), R2, T1, T2; the valuation case analysis is proved, `GlueRepo.PR.inertia_orders_eq_one_iff`,
and Lemma NV step 2, `LeafQM.AV.residue_unramified_over_branch`). -/
def FibreCoverExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P → FibreCoverOut Y Φ u P

/-- **Remaining (G4 + B1): the kernel field of `Res_{K/ℚ} A` and the descent datum on the Hom
field**, for every field `K` and rational fibre `PK/K` as in G2's output (h-decomposition G4: inputs R2, R3, T6,
R7a, T28; A7 proved, `LeafQM.AV.fibre_conjugates_isomorphic`; B1's algebra proved,
glue-descent `B1Quat`, `Cochain`; uses NoCM (G6) for `End⁰(A_ℚ̄) = B`). -/
def KernelFieldExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K], Module.finrank ℚ K ≤ heightF0 →
      (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) →
      ∀ PK : QML3 K, RationalFibre Y Φ P K PK → KernelFieldOut u P K PK.A

/-- **G2 → G4 → G7 (proved)**: from the two remaining glue Props and the four B2 leaves, every
fibre context has G7's output. -/
theorem fieldDescent (hCover : FibreCoverExists) (hKer : KernelFieldExists) (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7Out u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  exact g7Out_of_g4Out hHasse hTwo hSq hUnr u P
    (g4Out_of_kernelField hSup u P K hK hramK PK hPK.2 (hKer Y Φ π u P hctx K hK hramK PK hPK))

/-- **G2 → G4 → G7 with the twist (proved)**: as `fieldDescent`, with `L'` unramified outside `T`
and the clause list `G7Data`. -/
theorem fieldDescentUnr (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7OutUnr u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  exact g7OutUnr_of_g4Out hHasse hTwo hSq hUnr u P
    (g4Out_of_kernelField hSup u P K hK hramK PK hPK.2 (hKer Y Φ π u P hctx K hK hramK PK hPK))

/-! ## How G7's output feeds `ModularConstituent` -/

/-- (copied from scratch/g0-split/part_split.lean, `G0Split.CommonConstituent`, verbatim) The
hypotheses of E1: for some prime `ℓ` and field `E ⊇ ℚ_ℓ`, `V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a
common nonzero constituent, as `G_K`-representations. -/
def CommonConstituent {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) : Prop :=
  ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (E : Type) (_ : Field E) (_ : Algebra ℚ_[ℓ] E)
    (U : Subrepresentation (GlueI3.repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (GlueI3.repBaseChange E (J.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule), U ≠ ⊥ ∧
    ∀ g (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = GlueI3.repBaseChange E (J.galRep ℓ) g (e u)

/-- A finite-dimensional `L ⊆ ℚ̄` is a number field. -/
theorem numberField_of_fd (L : IF) [FiniteDimensional ℚ L] : NumberField L := ⟨⟩

/-- **`ModularConstituent`** (scratch/g0-split/part_split.lean, piece 10), copied with
def-faltings' copy `ZInQ.DefFaltings.AbVar` and the bridge `LeafAdopt.abVarEquiv` (the identity on
the underlying scheme) replaced by the kernel's `PkgI3.AbVar`, which `ZInQKernel/HDecomp/`
already uses for both. -/
def ModularConstituentG : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* Qbar) (A : PkgI3.AbVar L.K) (N : ℕ)
      (J : PkgI3.AbVar ℚ),
      (letI : Algebra L.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) ∧
      0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      (Module.finrank ℚ L.K : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
      CommonConstituent A (J.baseChange L.K)

/-- **The remaining ranges G8-G16 (the next tasks' target), as one Prop.** For every fibre
context and every G7 data (`G7Data`): a level `1 ≤ M ≤ Q_D·M_{S_mul}(u)²`, a `J₁(M)` over `ℚ`, and a
common constituent of `V_ℓ(A_{L'})` and `V_ℓ(J₁(M)_{L'})` as `G_{L'}`-representations (G8: `ρ_ℓ`
from `β`, `a_σ`, `m_σ`; G9-G12: de Rham, odd, modular; G13-G16: newform, level, Eichler-Shimura). -/
def AfterG7 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∃ (M : ℕ) (J : PkgI3.AbVar ℚ), 0 < M ∧ LeafModCurves.IsJ1 M J ∧
      (M : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      @CommonConstituent L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) (J.baseChange L')

/-- **`ModularConstituent` from this range and the next (proved)**: G2, G4, G7 here
(`fieldDescentUnr`) and the ranges G8-G16 as `AfterG7`. -/
theorem modularConstituent_of_ranges (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG := by
  intro Y Φ π h1 h2 u hu y P hy hπ
  have hctx : FibreCtx Y Φ π u P := ⟨h1, h2, hu, y, hy, hπ⟩
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hdata⟩ :=
    fieldDescentUnr hCover hKer hSup hHasse hTwo hSq hUnr Y Φ π u P hctx
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ := hRest Y Φ π u P hctx L A ε N χ β L' hle hdata
  haveI : NumberField L' := numberField_of_fd L'
  exact ⟨⟨L'⟩, algebraMap L' Qbar, @PkgI3.AbVar.baseChange L _ A L' _ (incAlg hle), M, J,
    hdata.2.2.2.2.2.2.2.2.2.2.2, hM, hJ, hMle, hdata.2.2.2.2.2.2.2.2.2.1, hCC⟩

/-- **The same, with glue-descent's `LeafHasse`, `LeafLocalTwo` replaced by the bundle's T14-T15**
(`PkgI6.BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`; `GlueWP3.leafHasse_of_T14`,
`leafLocalTwo_of_T15`). -/
theorem modularConstituent_of_ranges_T14 (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup) (hH : PkgI6.BrauerHasse2C) (hR : PkgI6.BrauerReciprocity2C)
    (hC : PkgI6.LocalH2CardC) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG :=
  modularConstituent_of_ranges hCover hKer hSup (GlueWP3.leafHasse_of_T14 hH hR)
    (GlueWP3.leafLocalTwo_of_T15 hC) hSq hUnr hRest

/-! ## Feeding g0-mod-galois' inputs (G8-G12): their `G2Out`, `G7Out` -/

namespace GaloisCopy
/-! Copied from scratch/g0-mod-galois/part_galois.lean (branch wip/g0-mod-galois at 20fa1287),
definitions `resQ`, `Vb`, `tate`, `G2Out`, `G7Out`, verbatim (namespace renamed). -/

/-- (copied) The restriction map `G_K → G_ℚ` (Mathlib's `Field.absoluteGaloisGroup.map`). -/
noncomputable def resQ (K : Type) [Field K] [NumberField K] :
    Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- (copied) `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- (copied) The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
noncomputable def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- (copied) g0-mod-galois' input "output of G2": inertia at `p ∉ T` lies in `G_K`. -/
def G2Out (K : Type) [Field K] [NumberField K] (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ∈ (resQ K).range

/-- (copied) g0-mod-galois' input "output of G7 at the coefficient prime `ℓ`". -/
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

end GaloisCopy

/-- **Bridge 1 (Mathlib-level Galois theory; proved below, `resQRange`).** For a finite Galois `L' ⊆ ℚ̄`, the
image of `resQ L' : G_{L'} → G_ℚ` is `G_{L'} = Fix(L')` (true for every embedding of the
algebraic closures because `L'/ℚ` is normal). -/
def ResQRange : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'],
    (@GaloisCopy.resQ L' _ (numberField_of_fd L')).range = L'.fixingSubgroup

/-- An element of `G_ℚ` as an automorphism of `ℚ̄`. -/
def actQ (τ : Field.absoluteGaloisGroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := τ
/-- An element of `G_K` as an automorphism of `\bar K`. -/
def actK {K : Type} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- `resQ K σ` is `σ` transported along the embedding `g : ℚ̄ → \bar K` that
`Field.absoluteGaloisGroup.map` chooses. -/
theorem resQ_comm' (K : Type) [Field K] [NumberField K] :
    ∃ g : AlgebraicClosure ℚ →+* AlgebraicClosure K, ∀ σ x,
      g (actQ (GaloisCopy.resQ K σ) x) = actK σ (g x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  let g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := g.toAlgebra
  haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ) (AlgebraicClosure ℚ) x

/-- **`ResQRange` proved**: for finite Galois `L ⊆ ℚ̄`, the image of `resQ L` is `Fix(L)`
(normality of `L` gives `g(L) = L` inside `\bar L`; `g` is bijective because `\bar L/ℚ` is
algebraic). -/
theorem resQ_range (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] :
    (@GaloisCopy.resQ L _ (numberField_of_fd L)).range = L.fixingSubgroup := by
  haveI := numberField_of_fd L
  obtain ⟨g0, hcomm⟩ := resQ_comm' L
  let g : Qbar →ₐ[ℚ] AlgebraicClosure L := g0.toRatAlgHom
  have hg : ∀ x, g x = g0 x := fun _ => rfl
  -- `g` is bijective (`AlgebraicClosure L` is algebraic over `ℚ`)
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L) := by
    haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
    haveI : Algebra.IsAlgebraic L (AlgebraicClosure L) := AlgebraicClosure.isAlgebraic L
    exact Algebra.IsAlgebraic.trans ℚ L (AlgebraicClosure L)
  have hgbij : Function.Bijective g := by
    letI : Algebra Qbar (AlgebraicClosure L) := g.toAlgebra
    haveI : IsScalarTower ℚ Qbar (AlgebraicClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L) := inferInstance
    haveI : Algebra.IsIntegral Qbar (AlgebraicClosure L) := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : L →ₐ[ℚ] AlgebraicClosure L := IsScalarTower.toAlgHom ℚ L (AlgebraicClosure L)
  let e : L ≃ₐ[ℚ] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal ℚ ψ.fieldRange := Normal.of_algEquiv e
  let f : ψ.fieldRange →ₐ[ℚ] AlgebraicClosure L := (g.comp L.val).comp e.symm.toAlgHom
  have hf := AlgHom.fieldRange_of_normal f
  have hgL : ∀ x : L, ∃ y : L, g x = ψ y := by
    intro x
    have hx : g x ∈ f.fieldRange := ⟨e x, by simp [f]⟩
    rw [hf] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy.symm⟩
  have hLg : ∀ y : L, ∃ x : L, g x = ψ y := by
    intro y
    have hy : ψ y ∈ f.fieldRange := by rw [hf]; exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hy
    exact ⟨e.symm z, by simpa [f] using hz⟩
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    refine (IntermediateField.mem_fixingSubgroup_iff L (actQ (GaloisCopy.resQ L σ))).mpr ?_
    intro x hx
    apply g.toRingHom.injective
    show g (actQ (GaloisCopy.resQ L σ) x) = g x
    rw [hg, hcomm σ x, ← hg]
    obtain ⟨y, hy⟩ := hgL ⟨x, hx⟩
    have hy' : g x = ψ y := hy
    rw [hy']
    exact (actK σ).commutes y
  · intro hτ'
    have hτ := (IntermediateField.mem_fixingSubgroup_iff L (actQ τ)).mp hτ'
    let eg : Qbar ≃+* AlgebraicClosure L := RingEquiv.ofBijective g.toRingHom hgbij
    let τ' : Qbar ≃ₐ[ℚ] Qbar := τ
    let σ₀ : AlgebraicClosure L ≃+* AlgebraicClosure L := (eg.symm.trans τ'.toRingEquiv).trans eg
    have hσ₀ : ∀ x, σ₀ (g x) = g (τ' x) := by
      intro x
      show eg (τ' (eg.symm (eg x))) = g (τ' x)
      rw [RingEquiv.symm_apply_apply]; rfl
    have hfix : ∀ y : L, σ₀ (algebraMap L (AlgebraicClosure L) y) =
        algebraMap L (AlgebraicClosure L) y := by
      intro y
      obtain ⟨x, hx⟩ := hLg y
      have hx' : g x = algebraMap L (AlgebraicClosure L) y := hx
      rw [← hx', hσ₀, show τ' (x : Qbar) = x from hτ x x.2]
    let σ : Field.absoluteGaloisGroup L := AlgEquiv.ofRingEquiv (f := σ₀) hfix
    refine ⟨σ, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply g.toRingHom.injective
    show g (actQ (GaloisCopy.resQ L σ) x) = g (τ' x)
    rw [hg, hcomm σ x, ← hg]
    exact hσ₀ x


theorem resQRange : ResQRange := fun L' _ _ => resQ_range L'

/-- **g0-mod-galois' `G2Out` for `K = L'`, proved** from `G7Data` (B3(v): inertia outside `T`
fixes `L'`) and `ResQRange`. -/
theorem galoisG2Out_of_g7Data (hRes : ResQRange) (u : ℚ) (P : QML3 Qbar) (L : IF)
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (h : G7Data u P L A ε N χ β L' hLL') :
    @GaloisCopy.G2Out L' _ (numberField_of_fd L') (T u) := by
  intro p hp hpT v hv σ hσ
  rw [hRes L']
  have hv' : GlueB3Unram.LiesOver v p := hv
  exact h.2.2.2.2.2.2.2.2.2.2.1 p hp hpT v hv' (Subgroup.mem_map_of_mem _ hσ)

/-- **Bridge 2 (remaining; the Tate functor on the descent datum, §3 of the report).** From G7's
data, the rank-4 endomorphism ring and `dim A_{L'} = 2` (G5-G6, A9; `model_dim`), for every `ℓ`:
operators `Tm σ` (`ℚ̄_ℓ ⊗ T_ℓ(m_σ)` transported to `V_ℓ(A_{L'})`), `c = n/d`, `a`, `ε`, `β` mapped
into `ℚ̄_ℓ` by one embedding of the number field they generate, and matrix units of
`End_{L'}(A) ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`, satisfying g0-mod-galois' `G7Out`. -/
def TateBridge : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu

end G0ModField


/-!
# g14-trace, second file: the linked Tate bridge at `ℓ = 3, 5`

Appended to a verbatim copy of `scratch/g0-mod-field/ModField.lean` (g0-mod-field's `G7Data`,
`TateBridge`, `GaloisCopy.G7Out`). `TateBridge` gives the `ℓ`-adic data at each `ℓ` separately
(`∀ ℓ, ∃ Tm c ε' a β' uu, G7Out …`), which does not determine the traces of `r₃` against `r₅`
(g14-trace §1, `g7Out_twist`). `TateBridge35` is the linked form at `ℓ = 3, 5` that
`G14Trace.g12Spec_g14_of_galois` consumes: one pair `a, β : G_ℚ → ℚ̄` mapped to `ℚ̄₅`, `ℚ̄₃` by
embeddings `j₅`, `j₃` (TateBridge's own docstring: "mapped into `ℚ̄_ℓ` by one embedding of the
number field they generate"), and the operators `Tm_ℓ` (from one points-level `m_σ`) in the
Frobenius link at Frobenius elements. No `sorry`, no `axiom`.
-/

noncomputable section

namespace G14Bridge

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField
open GlueC10Link (FrobCompare)

/-- (copy of `G14Trace.FrobTraceLink`, over `GaloisCopy.Vb`) **The Frobenius trace link (GLUE,
AV side; N5 L781-786).** Outside a finite set `S`, at every arithmetic Frobenius `τ` above `p`,
`N·Tm_ℓ(τ)` is conjugate to `V_ℓ(α')` for one endomorphism `α'` of an abelian variety over a
field of characteristic `p`, at `ℓ = 3` and `ℓ = 5` (kernel's `GlueC10Link.FrobCompare`). -/
def FrobTraceLink {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5) (GaloisCopy.Vb A 5))
    (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3) (GaloisCopy.Vb A 3)) : Prop :=
  ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ∀ (v : ValuationSubring PkgI4.Qbar) (τ : PkgI4.GQ),
    PkgI4.LiesOver v p → PkgI4.IsArithFrob τ v p →
    ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (Ab : PkgI3.AbVar k) (α : PkgI3.AbVar.End Ab)
      (N : ℕ), N ≠ 0 ∧ FrobCompare 3 (Tm3 τ) α N ∧ FrobCompare 5 (Tm5 τ) α N

/-- **The linked Tate bridge at `ℓ = 3, 5` (GLUE; replaces the `ℓ = 3, 5` instances of
`G0ModField.TateBridge`).** From G7's data, `dim A_{L'} = 2` and `rank End = 4`: one pair
`a, β : G_ℚ → ℚ̄` (N5's `a_σ` and `β(σ)`, algebraic), embeddings `j₅ : ℚ̄ → ℚ̄₅`, `j₃ : ℚ̄ → ℚ̄₃`, and
for `ℓ = 5, 3` the operators `Tm_ℓ` (`ℚ̄_ℓ ⊗ V_ℓ(m_σ)`), `c_ℓ`, `ε_ℓ` and matrix units with
`G7Out` for the scalars `j_ℓ ∘ a`, `j_ℓ ∘ β`, `FrobTraceLink` for `Tm₅`, `Tm₃`, and `β` an
algebraic form of `G7Data`'s `β` (`ιC ∘ βQ = β`; G15 needs this `β`). `aQ` is not tied to
`DescentDatum`'s `a` in the statement (`a_σ = deg(μ_σ)^{-1/4}`, N5 L647, is algebraic), nor `Tm_ℓ` to
its `m_σ`, as in `TateBridge`; for G14 only the common `aQ` and `FrobTraceLink` matter (a joint
twist at both `ℓ` keeps the system compatible). -/
def TateBridge35 : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5 ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3 ∧
      @FrobTraceLink L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
      ∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)

instance fact_prime_five' : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance fact_prime_three' : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- `TateBridge35` contains the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridge` (proved): it is a
strengthening at these two primes. -/
theorem tateBridge_five_three_of_35 (h : TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    (∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β' : PkgI4.GQ → PadicAlgCl 5)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm c ε' a β' uu) ∧
    (∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3) (a β' : PkgI4.GQ → PadicAlgCl 3)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm c ε' a β' uu) := by
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, -, -⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  exact ⟨⟨Tm5, c5, ε5, _, _, u5, h5⟩, ⟨Tm3, c3, ε3, _, _, u3, h3⟩⟩

end G14Bridge

end

-- END verbatim body of scratch/g14-trace/G14Bridge.lean
end G14BridgeSec

section G0DimSec
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
open Order TensorProduct
-- BEGIN verbatim scratch/g0-dim/Dim.lean l.107-305, l.339-344
namespace G0Dim

/-! ## §1. Commutative algebra -/


/-- Integral injective extensions have the same Krull dimension (going up + incomparability;
Stacks 00OK, Matsumura Thm 9.4 — STANDARD). -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro P Q hPQ
    have h : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) h
  · refine iSup_le fun l => ?_
    obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A B x = 0 := by simpa using hx
        have : x = 0 := hinj (by simpa using this)
        simp [this])
    haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- **Stacks 00P4 (affine case), proved.** For a finitely generated algebra `R` over a field `K`
and any field extension `L/K`, `dim (R ⊗_K L) = dim R`. Proof: Noether normalization
`K[X_1..X_s] → R` (finite, injective) base-changes to `L[X_1..X_s] → R ⊗ L` (finite, injective
since `L` is flat over `K`). -/
theorem ringKrullDim_tensor_field (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (L : Type*) [Field L] [Algebra K L] :
    ringKrullDim (R ⊗[K] L) = ringKrullDim R := by
  rcases subsingleton_or_nontrivial R with h | h
  · haveI : Subsingleton (R ⊗[K] L) := by
      have h1 : (1 : R ⊗[K] L) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : R) 0, TensorProduct.zero_tmul]
      exact subsingleton_of_zero_eq_one h1.symm
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    have hR : ringKrullDim R = s := by
      letI := g.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
      rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
        ringKrullDim_mvPolynomial_field]
    let g' := Algebra.TensorProduct.map g (AlgHom.id K L)
    have g'inj : Function.Injective g' :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := L) g.toLinearMap ginj
    have g'fin : g'.toRingHom.Finite := RingHom.Finite.tensorProductMap gfin (by exact RingHom.Finite.id L)
    have hP : ringKrullDim (MvPolynomial (Fin s) K ⊗[K] L) = s := by
      rw [ringKrullDim_eq_of_ringEquiv ((Algebra.TensorProduct.comm K _ L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv), ringKrullDim_mvPolynomial_field]
    rw [hR, ← hP]
    letI := g'.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K ⊗[K] L) (R ⊗[K] L) := ⟨g'fin.to_isIntegral⟩
    exact ringKrullDim_eq_of_isIntegral_of_injective g'inj

/-- A finitely generated algebra over a field has finite Krull dimension (or is zero). -/
theorem ringKrullDim_le_of_finiteType (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] : ∃ n : ℕ, ringKrullDim R ≤ n := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨0, by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le⟩
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    letI := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
    refine ⟨s, le_of_eq ?_⟩
    rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_field]


/-! ## §2. Topology and schemes -/

open TopologicalSpace Topology


/-- The Krull dimension of a space is the supremum of the dimensions of the members of a cover
by open embeddings (Stacks 0055 for open covers; STANDARD). -/
theorem topologicalKrullDim_eq_iSup_of_openEmbedding {X : Type*} [TopologicalSpace X] {ι : Type*}
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, rfl⟩ := hcov x
    let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)
    have hmem : ∀ j, (f i ⁻¹' (p j : Set X)).Nonempty := fun j =>
      ⟨y, p.monotone (Fin.zero_le j) hx⟩
    let q : LTSeries {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
      { length := p.length
        toFun := fun j => ⟨p j, hmem j⟩
        step := fun j => p.step j }
    calc (p.length : WithBot ℕ∞) = q.length := rfl
      _ ≤ krullDim {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} := q.length_le_krullDim
      _ = topologicalKrullDim (Y i) := (Order.krullDim_eq_of_orderIso e).symm
      _ ≤ ⨆ i, topologicalKrullDim (Y i) := le_iSup (fun i => topologicalKrullDim (Y i)) i
  · exact iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le

open AlgebraicGeometry CategoryTheory Limits

theorem scheme_dim_eq_iSup_cover {X : Scheme} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) :=
  topologicalKrullDim_eq_iSup_of_openEmbedding (fun i => 𝒰.f i) (fun i => (𝒰.f i).isOpenEmbedding)
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)

theorem scheme_dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

theorem spec_dim (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R


/-- **Stacks 00P4, affine piece over `Spec K`.** For `m : Spec R → Spec K` locally of finite
type, `Spec R ×_K Spec L ≅ Spec (R ⊗_K L)` has the dimension of `Spec R`. -/
theorem dim_pullback_spec {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]
    (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType m] :
    topologicalKrullDim (pullback m (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim (Spec R) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  have e := scheme_dim_eq_of_iso (pullbackSpecIso K R L)
  refine e.trans ?_
  rw [spec_dim, spec_dim]
  exact ringKrullDim_tensor_field K R L

/-- A scheme of finite type over a field: each affine piece `Spec R → Spec K` has bounded
dimension. -/
theorem dim_spec_le {K : Type} [Field K] (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType m] : ∃ n : ℕ, topologicalKrullDim (Spec R) ≤ n := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  rw [spec_dim]
  exact ringKrullDim_le_of_finiteType K R

/-- **Dimension is invariant under field base change** (Stacks 00P4 globalized; proved). For a
scheme `X` locally of finite type over a field `K` and any field extension `L/K`,
`dim (X ×_K L) = dim X`. -/
theorem dim_baseChange {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (X : Scheme.{0})
    (h : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] :
    topologicalKrullDim (pullback h (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim X := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let 𝒰 := X.affineCover
  rw [scheme_dim_eq_iSup_cover 𝒰, scheme_dim_eq_iSup_cover (𝒰.pullback₁ (pullback.fst h g))]
  refine iSup_congr fun i => ?_
  have e : (𝒰.pullback₁ (pullback.fst h g)).X i ≅ pullback (𝒰.f i ≫ h) g :=
    (pullbackSymmetry _ _).trans (pullbackRightPullbackFstIso h g (𝒰.f i))
  rw [scheme_dim_eq_of_iso e]
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
  exact @dim_pullback_spec K _ L _ _ _ (𝒰.f i ≫ h) hc

theorem exists_nat_of_le (x : WithBot ℕ∞) (h0 : x ≠ ⊥) (N : ℕ) (h : x ≤ N) :
    ∃ n : ℕ, x = n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((N : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.mp h') (by simp)
    | coe n => exact ⟨n, rfl⟩

/-- **A nonempty scheme of finite type over a field has finite dimension** (proved). -/
theorem dim_finite {K : Type} [Field K] (X : Scheme.{0}) (h : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType h] [QuasiCompact h] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  let 𝒰 := X.affineCover.finiteSubcover
  have hb : ∀ i, ∃ n : ℕ, topologicalKrullDim (𝒰.X i) ≤ n := fun i => by
    haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
    exact @dim_spec_le K _ _ (𝒰.f i ≫ h) hc
  choose n hn using hb
  have hle : topologicalKrullDim X ≤ ((∑ i, n i : ℕ) : WithBot ℕ∞) := by
    rw [scheme_dim_eq_iSup_cover 𝒰]
    refine iSup_le fun i => (hn i).trans ?_
    exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hne : topologicalKrullDim X ≠ ⊥ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    haveI : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_ne_bot_iff.mpr inferInstance
  exact exists_nat_of_le _ hne _ hle

end G0Dim

/-- `dim (A_L) = dim A` for I3's `PkgI3.AbVar.baseChange` (the same proof as `dimBaseChange`). -/
theorem G0Dim.pkgI3_dim_baseChange {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]
    (A : PkgI3.AbVar K) : (A.baseChange L).dim = A.dim :=
  G0Dim.dim_baseChange L A.X.left A.X.hom

-- END verbatim scratch/g0-dim/Dim.lean
end G0DimSec

/-! ## lg-kerwild: `KerWild` from G7Data through the Tate bridge, `DescentPts` on G7Data's model

Task lg-kerwild (2026-11-13). local-glue (`G15Ram.localGlue_of_unramRoots`) left two glue Props:
`G15Ram.KerWild K β L` (G7Data's kernel-field clause, dropped by `G7Out` and by g0-mod-field's
`TateBridge`, local-glue finding G8) and `G15Ram.DescentPts A L` (used at `p ≤ 5`).

This part:
* `kerWild_of_ker`: `KerWild L' β L` from G7Data's clause `G_{L'} = G_L ∩ ker β_ℂ` and any
  transport with `β(g) = 1 → β_ℂ(g) = 1`; `kerWild_of_alg` for the transport of g14-trace's
  `TateBridge35` (`β = j ∘ β_ℚ̄`, `β_ℂ = ι_ℂ ∘ β_ℚ̄`, `j`, `ι_ℂ` field embeddings, so injective);
  `kerWild_of_g7Data_alg` reads the clause off `G7Data`.
* `TateBridgeK`: g0-mod-field's `TateBridge` with `KerWild` added to its output (the correction of
  finding G8); `TateBridgeT`: `TateBridge` with the scalar transport added to its output (as
  `TateBridge35` has it); `tateBridgeK_of_T`, `tateBridge_of_K` (proved).
* `TateBridge35K`: g14-trace's `TateBridge35` with `KerWild` at `ℓ = 5, 3` added;
  `tateBridge35K_of_35 : TateBridge35 → TateBridge35K` (proved: the clause is transported from
  `G7Data`, nothing new is assumed); `tateBridgeK_five_three_of_35` (the `ℓ = 5, 3` conclusions
  of `TateBridgeK` from `TateBridge35`).
* `dim_model_of_bc`: `dim A = 2` from `dim A_{L'} = 2` (g0-dim's `pkgI3_dim_baseChange`);
  `descentPts_of_g7` : `DescentPts (A_{L'}) L` for G7Data's model `A/L`.
* `localGlue_of_tateBridge35`: local-glue's `LocalGlue` on `TateBridge35`'s data at `ℓ = 5, 3`
  from R6, I2-Tors, `UnramRoots` and `G7Clauses`, with no `KerWild` or `DescentPts` hypothesis.
-/

section LGKerWildSec

noncomputable section

namespace LGKerWild

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent G0ModField

/-! ### §1. `KerWild` from the kernel-field clause -/

/-- **`KerWild` from G7Data's kernel-field clause and a transport that detects `β = 1`
(proved).** `G_{L'} = G_L ∩ ker β_ℂ` (G7Data, `GQL L = L.fixingSubgroup`), `L'` finite Galois, and
`β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1` give `KerWild L' β_ℓ L` for `G7Out`'s model field `K = L'`. -/
theorem kerWild_of_ker {ℓ : ℕ} [Fact ℓ.Prime] {L L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] (βC : PkgI4.GQ → ℂˣ)
    (hker : ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    {β : PkgI4.GQ → PadicAlgCl ℓ} (hβ : ∀ g, β g = 1 → βC g = 1) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') β L := by
  intro g hgL hg1
  have h3 : g ∈ L'.fixingSubgroup :=
    (hker g).mpr ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).mpr hgL, hβ g hg1⟩
  rw [RQ.resQ_range L']
  exact h3

/-- **The algebraic transport detects `β = 1` (proved).** If `β_ℓ = j ∘ β_ℚ̄` and
`β_ℂ = ι_ℂ ∘ β_ℚ̄` for `ℚ`-algebra maps `j : ℚ̄ → ℚ̄_ℓ`, `ι_ℂ : ℚ̄ → ℂ` (injective, `ℚ̄` a field),
then `β_ℓ(g) = 1 ⇒ β_ℂ(g) = 1`. -/
theorem transport_one {ℓ : ℕ} [Fact ℓ.Prime] (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (βC : PkgI4.GQ → ℂˣ)
    (hC : ∀ g, ιC (βQ g) = (βC g : ℂ)) (g : PkgI4.GQ) (h1 : j (βQ g) = 1) : βC g = 1 := by
  have hQ : βQ g = 1 := j.toRingHom.injective (by rw [h1, map_one])
  apply Units.ext
  rw [← hC g, hQ, map_one, Units.val_one]

/-- **`KerWild` for the algebraic transport (proved).** -/
theorem kerWild_of_alg {ℓ : ℕ} [Fact ℓ.Prime] {L L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] (βC : PkgI4.GQ → ℂˣ)
    (hker : ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (βC g : ℂ)) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') (fun g => j (βQ g)) L :=
  kerWild_of_ker βC hker (fun g h1 => transport_one βQ j ιC βC hC g h1)

/-- G7Data's kernel-field clause (clause 9), as an equality of fixing subgroups. -/
theorem g7Data_ker {u : ℚ} {P : QML3 Qbar} {L : IF} {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ}
    {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} {hLL' : L ≤ L'}
    (h : G7Data u P L A ε N χ β L' hLL') :
    ∀ σ : PkgI4.GQ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ β σ = 1 :=
  h.2.2.2.2.2.2.2.2.1

/-- **`KerWild` transported from `G7Data` (proved).** For G7's data and an algebraic form `β_ℚ̄`
of its `β` (`ι_ℂ ∘ β_ℚ̄ = β`), every `j : ℚ̄ → ℚ̄_ℓ` gives `KerWild L' (j ∘ β_ℚ̄) L`. -/
theorem kerWild_of_g7Data_alg {ℓ : ℕ} [Fact ℓ.Prime] {u : ℚ} {P : QML3 Qbar} {L : IF}
    {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L'] [IsGalois ℚ L'] {hLL' : L ≤ L'}
    (h : G7Data u P L A ε N χ β L' hLL') (βQ : PkgI4.GQ → PkgI4.Qbar)
    (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ)
    (hC : ∀ g, ιC (βQ g) = (β g : ℂ)) :
    @G15Ram.KerWild ℓ _ L' _ (RQ.numberField_of_fd L') (fun g => j (βQ g)) L :=
  kerWild_of_alg β (g7Data_ker h) βQ j ιC hC

/-! ### §2. The corrected bridges -/

/-- **Bridge 2 with the kernel-field clause (GLUE; correction of g0-mod-field's `TateBridge`,
local-glue finding G8).** `TateBridge`'s statement, with `KerWild L' β' L` (G7Data's clause
`G_{L'} = G_L ∩ ker β`, for the `ℚ̄_ℓ`-valued `β'`: `g ∈ G_L`, `β'(g) = 1` ⟹ `g ∈ G_{L'}`) added
to its output. Source: N5 L702-716 (`L'` is the kernel field of `β|G_L`). -/
def TateBridgeK : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') β' L

/-- **Bridge 2 with the scalar transport (GLUE; the form in which `TateBridge35` states it).**
`TateBridge`'s statement with, in its output, an algebraic form `β_ℚ̄ : G_ℚ → ℚ̄` of G7Data's
`β` (`ι_ℂ ∘ β_ℚ̄ = β`) and an embedding `j : ℚ̄ → ℚ̄_ℓ` with `β' = j ∘ β_ℚ̄` (N5 L719-722: the
values of `β` are algebraic and are mapped into `ℚ̄_ℓ` by one embedding). -/
def TateBridgeT : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∃ (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
        (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ), (∀ g, β' g = j (βQ g)) ∧ ∀ g, ιC (βQ g) = (β g : ℂ)

/-- **`TateBridgeK` contains `TateBridge` (proved).** -/
theorem tateBridge_of_K (h : TateBridgeK) : TateBridge := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk ℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, -⟩ := h u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  exact ⟨Tm, c, ε', a, β', uu, h7⟩

/-- **The transport form gives the kernel-field form (proved)**: `KerWild` is transported from
`G7Data` (`kerWild_of_g7Data_alg`). -/
theorem tateBridgeK_of_T (h : TateBridgeT) : TateBridgeK := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk ℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, βQ, j, ιC, hj, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  refine ⟨Tm, c, ε', a, β', uu, h7, ?_⟩
  have hβ' : β' = fun g => j (βQ g) := funext hj
  subst hβ'
  exact kerWild_of_g7Data_alg hD βQ j ιC hC

/-- **g14-trace's `TateBridge35` with the kernel-field clause at `ℓ = 5, 3` (GLUE).**
`TateBridge35`'s statement with `KerWild L' (j_ℓ ∘ β_ℚ̄) L` for `ℓ = 5, 3` added to the output.
It follows from `TateBridge35` (`tateBridge35K_of_35`). -/
def TateBridge35K : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5 ∧
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3 ∧
      @G14Bridge.FrobTraceLink L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm5 Tm3 ∧
      (∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      @G15Ram.KerWild 5 _ L' _ (numberField_of_fd L') (fun g => j5 (βQ g)) L ∧
      @G15Ram.KerWild 3 _ L' _ (numberField_of_fd L') (fun g => j3 (βQ g)) L

/-- **`TateBridge35` gives `TateBridge35K` (proved)**: the kernel-field clause at `ℓ = 5, 3` is
transported from `G7Data` through `TateBridge35`'s own clause `ι_ℂ ∘ β_ℚ̄ = β`. -/
theorem tateBridge35K_of_35 (h : G14Bridge.TateBridge35) : TateBridge35K := by
  intro u P L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrk
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ιC, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  exact ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, ⟨ιC, hC⟩,
    kerWild_of_g7Data_alg hD βQ j5 ιC hC, kerWild_of_g7Data_alg hD βQ j3 ιC hC⟩

/-- **`TateBridge35` gives the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridgeT` (proved).** -/
theorem tateBridgeT_at_of_35 (h : G14Bridge.TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    ∀ ℓ, (ℓ = 5 ∨ ℓ = 3) → ∀ [Fact ℓ.Prime],
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∃ (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
        (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ), (∀ g, β' g = j (βQ g)) ∧ ∀ g, ιC (βQ g) = (β g : ℂ) := by
  intro ℓ hℓ _
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, -, ιC, hC⟩ :=
    h u P L A ε N χ β L' hLL' hD hdim hrk
  rcases hℓ with rfl | rfl
  · exact ⟨Tm5, c5, ε5, _, _, u5, h5, βQ, j5, ιC, fun _ => rfl, hC⟩
  · exact ⟨Tm3, c3, ε3, _, _, u3, h3, βQ, j3, ιC, fun _ => rfl, hC⟩

/-- **`TateBridge35` gives the `ℓ = 5` and `ℓ = 3` conclusions of `TateBridgeK` (proved).** -/
theorem tateBridgeK_at_of_35 (h : G14Bridge.TateBridge35) (u : ℚ) (P : QML3 Qbar)
    (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4) :
    ∀ ℓ, (ℓ = 5 ∨ ℓ = 3) → ∀ [Fact ℓ.Prime],
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') β' L := by
  intro ℓ hℓ _
  obtain ⟨Tm, c, ε', a, β', uu, h7, βQ, j, ιC, hj, hC⟩ :=
    tateBridgeT_at_of_35 h u P L A ε N χ β L' hLL' hD hdim hrk ℓ hℓ
  refine ⟨Tm, c, ε', a, β', uu, h7, ?_⟩
  have hβ' : β' = fun g => j (βQ g) := funext hj
  subst hβ'
  exact kerWild_of_g7Data_alg hD βQ j ιC hC

/-! ### §3. `DescentPts` on G7Data's model -/

/-- **`dim A = 2` for the model `A/L` from `dim A_{L'} = 2` (proved)**, by g0-dim's
`pkgI3_dim_baseChange` (dimension is invariant under field base change, Stacks 00P4). -/
theorem dim_model_of_bc {L L' : IF} (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2) : A.dim = 2 :=
  (@G0Dim.pkgI3_dim_baseChange L _ L' _ (incAlg hLL') A).symm.trans hdim

/-- **`DescentPts` for `A_{L'}` and G7's model field `L` (proved)**: `TateBridge`'s abelian
variety is the base change `A_{L'}` of the model `A/L` (`G7Data`), so local-glue's
`descentPts_baseChange` (with the conjugate model when Mathlib's embeddings differ, finding G9)
applies; `dim A = 2` comes from `dim A_{L'} = 2` (`dim_model_of_bc`). -/
theorem descentPts_of_g7 {L L' : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L]
    [FiniteDimensional ℚ L'] (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2) :
    @G15Ram.DescentPts L' _ (numberField_of_fd L')
      (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) L _ :=
  G15Ram.descentPts_baseChange hLL' A (dim_model_of_bc hLL' A hdim)

/-! ### §4. `LocalGlue` on the Tate bridge's data, with no local glue Prop -/

/-- **`LocalGlue` on the data of the transport form of the Tate bridge (proved).** For G7's
data, `dim A_{L'} = 2`, `G7Out` at `ℓ` for `A_{L'}` with `β' = j ∘ β_ℚ̄` where `ι_ℂ ∘ β_ℚ̄ = β`
(the output of `TateBridgeT`, or of `TateBridge35` at `ℓ = 5, 3`), and G7's clauses
(`G7Clauses`): `LocalGlue p Tm a β' L` at every `p ≠ ℓ`, from the leaves R6 and I2-Tors and the
textbook Prop `UnramRoots` (used at `p = 2`). -/
theorem localGlue_of_transport (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {u : ℚ} {P : QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (βQ : PkgI4.GQ → PkgI4.Qbar) (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (β g : ℂ))
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a
        (fun g => j (βQ g)) uu)
    (hCl : G15Ram.G7Clauses (fun g => j (βQ g)) ε' L) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a (fun g => j (βQ g)) L := by
  haveI : NumberField L' := numberField_of_fd L'
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := h7.1
  exact G15Ram.localGlue_of_unramRoots hR6 hTors hU hpℓ h7 hCl
    (kerWild_of_g7Data_alg hD βQ j ιC hC) (fun _ => descentPts_of_g7 hLL' A hdim)

/-- **`LocalGlue` on `TateBridge35`'s data at `ℓ = 5` and `ℓ = 3` (proved).** For G7's data and the
output of g14-trace's `TateBridge35`, with G7's clauses for `j_ℓ ∘ β_ℚ̄`: `LocalGlue` at every
`p ≠ 5` for `Tm₅` and at every `p ≠ 3` for `Tm₃`, from R6, I2-Tors and `UnramRoots`. -/
theorem localGlue_of_tateBridge35 (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    {u : ℚ} {P : QML3 Qbar} {L : IF}
    [FiniteDimensional ℚ L] [IsGalois ℚ L] {A : PkgI3.AbVar L} {ε : GQ → GQ → ℂˣ} {N : ℕ}
    [NeZero N] {χ : DirichletCharacter ℂ N} {β : GQ → ℂˣ} {L' : IF} [FiniteDimensional ℚ L']
    [IsGalois ℚ L'] {hLL' : L ≤ L'} (hD : G7Data u P L A ε N χ β L' hLL')
    (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
    (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
    (Tm5 : PkgI4.GQ → Module.End (PadicAlgCl 5)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
    (c5 ε5 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
    (u5 : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
    (Tm3 : PkgI4.GQ → Module.End (PadicAlgCl 3)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
    (c3 ε3 : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
    (u3 : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
      (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
    (h5 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 _ Tm5 c5 ε5
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u5)
    (h3 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 _ Tm3 c3 ε3
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u3)
    (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (hC : ∀ g, ιC (βQ g) = (β g : ℂ))
    (hCl5 : G15Ram.G7Clauses (fun g => j5 (βQ g)) ε5 L)
    (hCl3 : G15Ram.G7Clauses (fun g => j3 (βQ g)) ε3 L) :
    (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 →
      @G15Ram.LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm5 (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) L) ∧
    (∀ (p : ℕ) (hp : p.Prime), p ≠ 3 →
      @G15Ram.LocalGlue p ⟨hp⟩ 3 _ _ _ _ Tm3 (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) L) := by
  refine ⟨fun p hp hp5 => ?_, fun p hp hp3 => ?_⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_transport hR6 hTors (hU p 5) hp5 hD βQ j5 ιC hC h5 hCl5
  · haveI : Fact p.Prime := ⟨hp⟩
    exact localGlue_of_transport hR6 hTors (hU p 3) hp3 hD βQ j3 ιC hC h3 hCl3

end LGKerWild

end

end LGKerWildSec

#print axioms LGKerWild.kerWild_of_ker
#print axioms LGKerWild.transport_one
#print axioms LGKerWild.kerWild_of_alg
#print axioms LGKerWild.g7Data_ker
#print axioms LGKerWild.kerWild_of_g7Data_alg
#print axioms LGKerWild.tateBridge_of_K
#print axioms LGKerWild.tateBridgeK_of_T
#print axioms LGKerWild.tateBridge35K_of_35
#print axioms LGKerWild.tateBridgeT_at_of_35
#print axioms LGKerWild.tateBridgeK_at_of_35
#print axioms LGKerWild.dim_model_of_bc
#print axioms LGKerWild.descentPts_of_g7
#print axioms LGKerWild.localGlue_of_transport
#print axioms LGKerWild.localGlue_of_tateBridge35
