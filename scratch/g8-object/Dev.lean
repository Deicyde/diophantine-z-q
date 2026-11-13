import ZInQKernel.HDecomp.Conductor.LadicCond
import ZInQKernel.HDecomp.Conductor.Breaks
import ZInQKernel.HDecomp.Textbook.Different
import ZInQKernel.HDecomp.Objects
import ZInQKernel.HDecomp.Descent.Constants
import ZInQKernel.Hypotheses.Height
import ZInQKernel.Multiplication.Certificate.Constants
import ZInQKernel.HDecomp.Descent.ProjRep
import ZInQKernel.HDecomp.I3Linalg.C2

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

#print axioms G15Ram.upperBreakFix_of_hilbertSerre
#print axioms G15Ram.g15RamG_of_pieces
#print axioms G15Ram.g15RamG_of_hilbertSerre
#print axioms G15Ram.upperWild
#print axioms G15Ram.hilbertSerre_of_model
#print axioms G15Ram.g15RamG_of_model
#print axioms G15Ram.wildFixTame
#print axioms G15Ram.g15RamG_of_dvrModel
#print axioms G15Ram.ladicDVRModel_of_Zp
#print axioms G15Ram.g15RamG_of_zpModel
#print axioms G15Ram.ladicDVRModelZp
#print axioms G15Ram.g15RamG_of_localData
#print axioms G15Ram.localData_trivRep

/-! Copied verbatim from scratch/g0-mod-galois/part_galois.lean L27-152 and part_matrix.lean L11-21. -/
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

/-- `resQ K τ` is the only `σ ∈ G_ℚ` with `qEmb K ∘ σ = τ ∘ qEmb K`. -/
lemma eq_resQ (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (σ : PkgI4.GQ) (h : ∀ x, qEmb K (σ x) = τ (qEmb K x)) : σ = resQ K τ := by
  apply AlgEquiv.ext; intro x
  exact (qEmbRing K).injective ((h x).trans (resQ_spec K τ x).symm)

/-- `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- The restriction of a representation to an invariant subspace. -/
def restrictRep {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (W : Submodule k V) (h : ∀ g, ∀ w ∈ W, ρ g w ∈ W) :
    Representation k G W where
  toFun g := (ρ g).restrict (h g)
  map_one' := by ext w; simp
  map_mul' g g' := by ext w; simp

/-- `e` intertwines the operators `f g` on `V` with `r(g) ⊕ r(g)` on `ℚ̄_ℓ² × ℚ̄_ℓ²`. -/
def Intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V] [Module (PadicAlgCl ℓ) V]
    (f : G → Module.End (PadicAlgCl ℓ) V) (m : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)) : Prop :=
  ∀ g v, e (f g v) = ((m g).mulVec (e v).1, (m g).mulVec (e v).2)

/-! ### Outputs of the earlier glue steps (inputs of this range) -/

/-- **Output of G2 (Lemma PR(i)), the part used here.** The field `K` (= `L'`, which contains
the fibre field and the Hom field, both unramified outside `T`, and the kernel field of `β`,
unramified outside `T` by B3(v)) is unramified at every prime `p ∉ T`: every inertia element
of `G_ℚ` at a place above `p` lies in (the image of) `G_K`. -/
def G2Out (K : Type) [Field K] [NumberField K] (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ∈ (resQ K).range

/-- **Output of G3 (Lemma PR(ii)) with R7a (Néron–Ogg–Shafarevich), the part used here.** `A`
has good reduction at the places above `p ∉ T`, so for `p ≠ ℓ` the inertia elements of `G_K`
at those places act trivially on `V_ℓ(A)` (the instantiation of
`PkgI2.inertiaTrivial_of_goodReduction` on the actual `A`, glue G3/G11). -/
def G3Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → p ≠ ℓ → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
    ∀ σ' : Field.absoluteGaloisGroup K,
      (∃ σ ∈ v.inertiaSubgroup ℚ, ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = resQ K σ') →
      tate A ℓ σ' = 1

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

/-- **Output of G5-G6 (QM dichotomy and NoCM), the part used by G10:** `End_K(A)` is a division
ring (`PkgI3.EndDivision`: every nonzero endomorphism is an isogeny) and is not commutative (so
`End⁰_K(A) = B`, not a field). -/
def G6Out {K : Type} [Field K] (A : PkgI3.AbVar K) : Prop :=
  PkgI3.EndDivision A ∧ ∃ x y : PkgI3.AbVar.End A, x * y ≠ y * x

/-! ### Outputs of this range -/

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


/-- **Burnside's theorem, absolutely irreducible form (textbook leaf; Lang, *Algebra*, XVII §3,
Cor. 3.4, and Curtis–Reiner §27 (Burnside, Frobenius–Schur); locators UNVERIFIED).** If a
finite-dimensional representation `ρ` of a monoid over a field `F` stays irreducible after every
field extension, then the matrices `ρ(g)` (in any basis) generate `M_n(F)` as an `F`-algebra.
Mathlib has the Jacobson density theorem (`jacobson_density`), from which it follows. -/
def BurnsideAbsIrred : Prop :=
  ∀ (F : Type) [Field F] (G : Type) [Monoid G] (W : Type) [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (n : ℕ) (b : Module.Basis (Fin n) F W) (ρ : Representation F G W),
    (∀ (F' : Type) [Field F'] [Algebra F F'], (GlueI3.repBaseChange F' ρ).IsIrreducible) →
    Algebra.adjoin F (Set.range fun g => LinearMap.toMatrix b b (ρ g)) = ⊤

end G0Galois
end

/-! ## g8-object: G8's `r_ℓ` as a Lean object; the G8-G16 interface over it

Task g8-object, 2026-11-13. g15-ram found that `G15RamG D u` is false for arbitrary
`D : ModData L A`: the fields `r₅`, `r₃` of `ModData` are bare representations, while G15 is a claim
about the `r_ℓ` that G8 builds from G7's descent data. This section

* §A defines that `r_ℓ` (`DescData.r`) from G7's output (`G0Galois.G7Out`) and `dim = 4` (T26),
  by the construction of g0-mod-galois' `g8Matrix_of_burnside` (a basis of `W = e₀₀ V`), and
  proves G8's intertwining for it (`DescData.intertwines`, `DescData.rho_resQ`) and, with C2 and
  Burnside, the full `G0Galois.G8Out` (`DescData.g8Out`);
* §B proves that **every** `r` intertwined with `ρ = β⁻¹ a Tm` (G8's output for any choice of
  basis) is pinned at each `g` where `ρ(g)` is a scalar (`mat_eq_scalar_of_intertwines`), and
  G11 for such `r` (`g11_of_intertwines`);
* §C restates g15-ram's `LocalData` on the descent data (`Tm`, `a`, `β`), not on `r`
  (`LocalDataG`), and proves `LocalDataG → G15Ram.LocalData` for every intertwined `r`
  (`localData_of_intertwines`);
* §D proves `G15RamG` for the constructed object (`ModObj.toModData`) from `LocalDataG`, `G2Out`
  and `G3Out` (`g15RamG_obj`), using g15-ram's `g15RamG_of_localData`. -/

noncomputable section

namespace G8Object

open PkgI4 (GQ GQp GaloisRep decomp)
open LadicCond
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type} [Field K] [NumberField K]

/-! ### §A. The object -/

/-- **G7's descent data at the coefficient prime `ℓ`, bundled (the input of G8).** The operators
`Tm σ = μ_σ ∘ σ` on `ℚ̄_ℓ ⊗ V_ℓ(A)`, the cocycle `c`, the scalars `a`, the sign cocycle `ε`, the
cochain `β`, and matrix units `u` (the image of `B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`), with g0-mod-galois'
`G7Out` and `dim (ℚ̄_ℓ ⊗ V_ℓ(A)) = 4` (from T26 `PkgI3.TateModuleFree` and `dim A = 2`;
`DescData.ofG7Out`). -/
structure DescData (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] where
  Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)
  c : GQ → GQ → PadicAlgCl ℓ
  ε : GQ → GQ → PadicAlgCl ℓ
  a : GQ → PadicAlgCl ℓ
  β : GQ → PadicAlgCl ℓ
  u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)
  g7 : G0Galois.G7Out A ℓ Tm c ε a β u
  dim4 : Module.finrank (PadicAlgCl ℓ) (G0Galois.Vb A ℓ) = 4

/-- `dim (ℚ̄_ℓ ⊗ V_ℓ(A)) = 4` from T26 and `dim A = 2` (the argument of g0-mod-galois' `g8`). -/
theorem finrank_Vb_of (hT : PkgI3.TateModuleFree) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hdim : A.dim = 2) : Module.finrank (PadicAlgCl ℓ) (G0Galois.Vb A ℓ) = 4 := by
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfree, hfin, hrk⟩ := hT K A ℓ hℓK
  haveI : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := inferInstance
  rw [Module.finrank_baseChange, Module.finrank_baseChange]
  rw [hdim] at hrk
  have h22 : (2 : WithBot ℕ∞) * 2 = (((4 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    norm_num
  rw [h22] at hrk
  exact_mod_cast hrk

/-- The object from G7's output and T26. -/
def DescData.ofG7Out (hT : PkgI3.TateModuleFree) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (c ε : GQ → GQ → PadicAlgCl ℓ)
    (a β : GQ → PadicAlgCl ℓ) (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (G0Galois.Vb A ℓ))
    (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) : DescData A ℓ :=
  ⟨Tm, c, ε, a, β, u, h7, finrank_Vb_of hT A ℓ h7.1⟩

namespace DescData

variable {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (D : DescData A ℓ)

theorem hTm : ∀ g h, D.Tm g * D.Tm h = D.c g h • D.Tm (g * h) := D.g7.2.2.1
theorem ha : ∀ g h, D.a g * D.a h * D.c g h = D.ε g h * D.a (g * h) := D.g7.2.2.2.1
theorem hβ : ∀ g h, D.β g * D.β h = D.ε g h * D.β (g * h) := D.g7.2.2.2.2.1
theorem hβ0 : ∀ g, D.β g ≠ 0 := D.g7.2.2.2.2.2.1
theorem hres : ∀ σ, D.Tm (G0Galois.resQ K σ) = G0Galois.tate A ℓ σ ∧
    D.a (G0Galois.resQ K σ) = 1 ∧ D.β (G0Galois.resQ K σ) = 1 := D.g7.2.2.2.2.2.2.1
theorem hcomm : ∀ g i j, Commute (D.Tm g) (D.u.e i j) := D.g7.2.2.2.2.2.2.2.1
theorem hcont : ∀ (f : Module.Dual (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)) (v : G0Galois.Vb A ℓ),
    Continuous fun g => f (GlueDescent.rho D.Tm D.a D.β g v) := D.g7.2.2.2.2.2.2.2.2

/-- `ρ(1) = 1`. -/
theorem rho_one : GlueDescent.rho D.Tm D.a D.β 1 = 1 := by
  have := D.hres 1
  rw [map_one] at this
  refine (GlueDescent.rho_eq_act D.Tm (fun _ => G0Galois.tate A ℓ 1) D.a D.β 1 this.1 this.2.1
    this.2.2).trans ?_
  exact map_one (G0Galois.tate A ℓ)

/-- **G8's descended representation** `ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ σ` (N5 L725-727), as a
representation of `G_ℚ` (glue-descent's `rhoRep`). -/
def rho : Representation (PadicAlgCl ℓ) GQ (G0Galois.Vb A ℓ) :=
  GlueDescent.rhoRep D.Tm D.c D.ε D.a D.β D.hTm D.ha D.hβ D.hβ0 D.rho_one

theorem rho_apply (g : GQ) : D.rho g = GlueDescent.rho D.Tm D.a D.β g := rfl

/-- `ρ` is the Tate action on `G_{L'}`. -/
theorem rho_resQ (σ : Field.absoluteGaloisGroup K) :
    GlueDescent.rho D.Tm D.a D.β (G0Galois.resQ K σ) = G0Galois.tate A ℓ σ :=
  GlueDescent.rho_eq_act D.Tm (fun _ => G0Galois.tate A ℓ σ) D.a D.β (G0Galois.resQ K σ)
    (D.hres σ).1 (D.hres σ).2.1 (D.hres σ).2.2

theorem comm (g : GQ) (i j : Fin 2) : Commute (D.rho g) (D.u.e i j) :=
  GlueDescent.rho_commute D.Tm D.a D.β (D.u.e i j) (fun g => D.hcomm g i j) g

theorem finiteDimensional (D : DescData A ℓ) : FiniteDimensional (PadicAlgCl ℓ) (G0Galois.Vb A ℓ) :=
  Module.finite_of_finrank_pos (by rw [D.dim4]; norm_num)

theorem finrank_W : Module.finrank (PadicAlgCl ℓ) D.u.W = 2 :=
  haveI := D.finiteDimensional
  D.u.finrank_W D.dim4

/-- A basis of `W = e₀₀(ℚ̄_ℓ ⊗ V_ℓ(A))` (chosen once; `dim W = 2`). -/
def basis : Module.Basis (Fin 2) (PadicAlgCl ℓ) D.u.W :=
  haveI := D.finiteDimensional
  Module.finBasisOfFinrankEq (PadicAlgCl ℓ) D.u.W D.finrank_W

/-- `ρ` restricted to `W` (the multiplicity space: `ρ ≅ r ⊕ r`). -/
def rW : Representation (PadicAlgCl ℓ) GQ D.u.W :=
  G0Galois.restrictRep D.rho D.u.W (fun g _ hw => D.u.mapsTo_W D.rho D.comm g hw)

/-- The matrices of `ρ|_W` in the basis `D.basis`. -/
def m : GQ →* Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) :=
  (LinearMap.toMatrixAlgEquiv D.basis).toRingEquiv.toMonoidHom.comp D.rW

theorem m_apply (g : GQ) : D.m g = LinearMap.toMatrix D.basis D.basis (D.rW g) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  exact LinearMap.toMatrixAlgEquiv_apply D.basis (D.rW g) i j

theorem continuous_m : Continuous fun g => D.m g := by
  refine continuous_matrix fun i j => ?_
  let f : Module.Dual (PadicAlgCl ℓ) (G0Galois.Vb A ℓ) :=
    (D.basis.coord i).comp ((D.u.e 0 0).codRestrict D.u.W (fun v => D.u.mem_W_of_e0 0 v))
  refine (D.hcont f (D.basis j : G0Galois.Vb A ℓ)).congr fun g => ?_
  rw [D.m_apply, LinearMap.toMatrix_apply, ← Module.Basis.coord_apply]
  change D.basis.coord i _ = D.basis.coord i _
  congr 1
  exact Subtype.ext (D.u.e00_of_mem (D.u.mapsTo_W D.rho D.comm g (D.basis j).2))

theorem continuous_toHom : Continuous (D.m.toHomUnits : GQ →* GL (Fin 2) (PadicAlgCl ℓ)) := by
  rw [Units.continuous_iff]
  refine ⟨D.continuous_m, ?_⟩
  have hinv : (fun g => (((D.m.toHomUnits g)⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) :
      Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))) = fun g => D.m g⁻¹ := by
    funext g
    rw [← map_inv]
    rfl
  rw [hinv]
  exact D.continuous_m.comp continuous_inv

/-- **G8's `r_ℓ`, as a Lean object** (N5 L729-730: "matrix units give `ρ_ℓ ≃ r_ℓ ⊕ r_ℓ`"): the
continuous representation `G_ℚ → GL₂(ℚ̄_ℓ)` given by `ρ_ℓ|_{e₀₀ V}` in the basis `D.basis`. -/
def r : GaloisRep ℓ 2 := ⟨D.m.toHomUnits, D.continuous_toHom⟩

theorem r_mat (g : GQ) : D.r.mat g = LinearMap.toMatrix D.basis D.basis (D.rW g) := D.m_apply g

/-- G8's isomorphism `ℚ̄_ℓ ⊗ V_ℓ(A) ≃ ℚ̄_ℓ² × ℚ̄_ℓ²` (`splitEquiv` and the basis). -/
def e : G0Galois.Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ) :=
  D.u.splitEquiv.trans (D.basis.equivFun.prodCongr D.basis.equivFun)

/-- **G8 (i) for the object, proved:** `e` intertwines `ρ_ℓ` with `r_ℓ ⊕ r_ℓ` on all of `G_ℚ`. -/
theorem intertwines : G0Galois.Intertwines (GlueDescent.rho D.Tm D.a D.β) D.r.mat D.e := by
  intro g v
  have h1 := D.u.splitEquiv_intertwines D.rho D.comm g v
  change D.e (D.rho g v) = _
  simp only [e, LinearEquiv.trans_apply, h1, LinearEquiv.prodCongr_apply,
    Module.Basis.equivFun_apply, D.r_mat]
  refine Prod.ext ?_ ?_
  · dsimp only
    rw [LinearMap.toMatrix_mulVec_repr]
    rfl
  · dsimp only
    rw [LinearMap.toMatrix_mulVec_repr]
    rfl

/-- **G8 for the object, proved** from C2's inputs (the leaves R9a `FaltingsSemisimple`, R9b
`FaltingsTate`, T26 `TateModuleFree`, T6 `HomFreeFinite`, glue-ssbc's `SemisimpleBaseChange`)
and Burnside (`G0Galois.BurnsideAbsIrred`): g0-mod-galois' `G8Out` holds for `D.r`. -/
theorem g8Out (hS : PkgI3.FaltingsSemisimple) (hF : PkgI3.FaltingsTate)
    (hT : PkgI3.TateModuleFree) (hH : PkgI3.HomFreeFinite) (hSS : GlueI3.SemisimpleBaseChange)
    (hB : G0Galois.BurnsideAbsIrred) :
    G0Galois.G8Out A ℓ (GlueDescent.rho D.Tm D.a D.β) D.r := by
  haveI := D.finiteDimensional
  haveI hVne : Nontrivial (G0Galois.Vb A ℓ) :=
    Module.nontrivial_of_finrank_pos (R := PadicAlgCl ℓ) (by rw [D.dim4]; norm_num)
  haveI : Nontrivial D.u.W := by
    by_contra hW
    rw [not_nontrivial_iff_subsingleton] at hW
    haveI := hW
    haveI : Subsingleton (D.u.W × D.u.W) := inferInstance
    exact not_subsingleton (G0Galois.Vb A ℓ) D.u.splitEquiv.toEquiv.subsingleton
  let rWK : Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) D.u.W :=
    D.rW.comp (G0Galois.resQ K)
  have he : ∀ σ v, D.u.splitEquiv (G0Galois.tate A ℓ σ v) =
      (rWK σ).prodMap (rWK σ) (D.u.splitEquiv v) := by
    intro σ v
    rw [← D.rho_resQ σ, ← D.rho_apply, D.u.splitEquiv_intertwines D.rho D.comm]
    rfl
  have hirr := fun (F : Type) [Field F] [Algebra (PadicAlgCl ℓ) F] =>
    PkgI3.C2_absolutelyIrreducible hS hF hT hH hSS A ℓ D.g7.2.1 (PadicAlgCl ℓ) rWK
      D.u.splitEquiv he F
  refine ⟨D.rho_resQ, D.e, D.intertwines, ?_⟩
  have hfun : (fun σ => D.r.mat (G0Galois.resQ K σ)) =
      fun σ => LinearMap.toMatrix D.basis D.basis (rWK σ) :=
    funext fun σ => D.r_mat _
  rw [hfun]
  exact hB (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) D.u.W 2 D.basis rWK hirr

end DescData

/-! ### §B. Every intertwined `r` is pinned where `ρ` is scalar; G11 -/

/-- **Scalar transfer (proved).** If `e` intertwines `f` with `m ⊕ m` and `f g = c • 1`, then
`m g` is the scalar matrix `c`. So any two `r` with G8's output on the same `ρ` agree at every
`g` where `ρ(g)` is a scalar (this is all that G11 and G15 use). -/
theorem mat_eq_scalar_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {G V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {f : G → Module.End (PadicAlgCl ℓ) V}
    {mm : G → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)}
    {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines f mm e) {g : G} {c : PadicAlgCl ℓ} (hf : f g = c • 1) :
    mm g = Matrix.scalar (Fin 2) c := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro w
  have h1 := h g (e.symm (w, 0))
  rw [hf, LinearMap.smul_apply, Module.End.one_apply, map_smul, LinearEquiv.apply_symm_apply]
    at h1
  have h2 := congrArg Prod.fst h1
  simp only [Prod.smul_mk] at h2
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← h2]
  ext i
  simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]

theorem toHom_eq_one_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] {f : GQ → Module.End (PadicAlgCl ℓ) V} {r : GaloisRep ℓ 2}
    {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines f r.mat e) {g : GQ} (hf : f g = 1) : r.toHom g = 1 := by
  have h1 := mat_eq_scalar_of_intertwines h (c := 1) (by rw [hf, one_smul])
  apply Units.ext
  change r.mat g = _
  rw [h1, map_one, Units.val_one]

/-- **G11 for every `r` intertwined with G8's `ρ` (proved; the argument of g0-mod-galois' `g11`).**
At `p ∉ T`, `p ≠ ℓ`, an inertia element above `p` is in `G_K` (G2), acts trivially on `V_ℓ(A)`
(G3 with R7a), so `ρ` of it is `1`, and `r` of it is `1`. -/
theorem g11_of_intertwines {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (T : Finset ℕ)
    (h2 : G0Galois.G2Out K T) (h3 : G0Galois.G3Out A ℓ T)
    {ρ : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)}
    (hres : ∀ σ, ρ (G0Galois.resQ K σ) = G0Galois.tate A ℓ σ) {r : GaloisRep ℓ 2}
    {e : G0Galois.Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines ρ r.mat e) : G0Galois.G11Out T r := by
  intro p hp hpT hpℓ v hv σ hσ
  obtain ⟨σ', hσ'⟩ := h2 p hp hpT v hv σ hσ
  have ht : G0Galois.tate A ℓ σ' = 1 := h3 p hp hpT hpℓ v hv σ' ⟨σ, hσ, hσ'.symm⟩
  refine toHom_eq_one_of_intertwines h ?_
  rw [← hσ', hres, ht]

/-! ### §C. `LocalData` restated on the descent data -/

section LocalG

variable (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
  [Module (PadicAlgCl ℓ) V]

/-- **Glue on G7's data (G7's `G_L`-clause + R6 + D2; N5 L819-823, L848-851).** On `G_F ∩ P_p`
(through the decomposition map `G_{ℚ_p} → G_ℚ`), `a = 1` and `Tm = 1`. Why true for Glazer's
data with `F` the Galois closure of `L_v(A[3])` (`A[5]` if `p = 3`) at `p ≤ D`, and of `L_v` at
`p > D`: `F ⊇ L_v` puts `decomp(G_F)` in `G_L`, where `a = 1` and `Tm` is the Galois action of
`A/L` (`DescentDatum`, `μ_σ = 1` on `G_L`, N5 L831); at `p ≤ D`, Raynaud's criterion (R6) makes
`A` semistable over `F`, so wild inertia acts trivially on `V_ℓ(A)`, `ℓ ≠ p` (D2,
`PkgI2.D2_fixed_of_raynaud`); at `p > D`, N5 L848-851 ("the surface has good reduction").
This is a statement about G7's data, not about `r`: `G7Out` pins `Tm`, `a` only on `G_{L'}`, and
`F` cannot contain `L'_v` (the bound `e(F/ℚ_p) ≤ (DG₀)!` does not see `[L':ℚ]`). -/
def TmWild (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, a (decomp p σ) = 1 ∧ Tm (decomp p σ) = 1

/-- **Glue on G7's `β` (D3 + T16; N5 L832-844).** `β` is trivial on `G_{ℚ_p}^t ∩ G_F` for
`t > U` (through the decomposition map). g15-ram's `TwistUpper`, for the local twist
`σ ↦ β(decomp σ)⁻¹`. -/
def BetaUpper (β : GQ → PadicAlgCl ℓ) (F : Fld p) (U : ℝ) : Prop :=
  ∀ t : ℝ, U < t → ∀ σ ∈ upperAbs p t ∩ fixSet F, β (decomp p σ) = 1

/-- **Glue on G7's `β` at tame primes (N5 L848-851).** `β` is trivial on `G_F ∩ P_p`. -/
def BetaTame (β : GQ → PadicAlgCl ℓ) (F : Fld p) : Prop :=
  ∀ σ ∈ fixSet F ∩ wildSet, β (decomp p σ) = 1

/-- **g15-ram's `SmallPrimeData`, on the descent data.** -/
def SmallPrimeG (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ∃ F : Fld p, IsFinGal F ∧ ramCard F 0 ≤ (ZInQ.heightD * ZInQ.heightG0).factorial ∧
    TmWild p Tm a F ∧ BetaUpper p β F G0ModNewform.U0

/-- **g15-ram's `LargePrimeData`, on the descent data.** -/
def LargePrimeG (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ∃ F : Fld p, IsFinGal F ∧ ¬ p ∣ ramCard F 0 ∧ TmWild p Tm a F ∧ BetaTame p β F

/-- **g15-ram's `LocalData`, restated on G7's descent data `(Tm, a, β)`** (the restatement this
task makes; g15-ram's `LocalData p r` is on a bare `r`). -/
def LocalDataG (Tm : GQ → Module.End (PadicAlgCl ℓ) V) (a β : GQ → PadicAlgCl ℓ) : Prop :=
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → SmallPrimeG p Tm a β) ∧
    ((ZInQ.heightD : ℝ) < p → LargePrimeG p Tm a β)

variable {p}

/-- On `G_F ∩ P_p`, `ρ = β⁻¹ a Tm` is the scalar `β⁻¹`, so an intertwined `r` is that scalar:
g15-ram's `TwistShape` for the local twist `σ ↦ β(decomp σ)⁻¹` (proved). -/
theorem twistShape_of_tmWild {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines (GlueDescent.rho Tm a β) r.mat e) {F : Fld p}
    (hw : TmWild p Tm a F) :
    G15Ram.TwistShape p r F (fun σ => (β (decomp p σ))⁻¹) := by
  intro σ hσ
  obtain ⟨ha, hT⟩ := hw σ hσ
  have hf : GlueDescent.rho Tm a β (decomp p σ) = (β (decomp p σ))⁻¹ • 1 := by
    simp [GlueDescent.rho, ha, hT]
  exact mat_eq_scalar_of_intertwines h hf

/-- **`LocalDataG` on the data gives g15-ram's `LocalData` for every intertwined `r` (proved).** -/
theorem localData_of_intertwines {Tm : GQ → Module.End (PadicAlgCl ℓ) V} {a β : GQ → PadicAlgCl ℓ}
    {r : GaloisRep ℓ 2} {e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)}
    (h : G0Galois.Intertwines (GlueDescent.rho Tm a β) r.mat e) (hd : LocalDataG p Tm a β) :
    G15Ram.LocalData p r := by
  refine ⟨fun hpD => ?_, fun hpD => ?_⟩
  · obtain ⟨F, hF, he, hw, hup⟩ := hd.1 hpD
    refine ⟨F, fun σ => (β (decomp p σ))⁻¹, hF, he, twistShape_of_tmWild h hw, ?_⟩
    intro t ht σ hσ
    simp only [hup t ht σ hσ, inv_one]
  · obtain ⟨F, hF, he, hw, htame⟩ := hd.2 hpD
    refine ⟨F, fun σ => (β (decomp p σ))⁻¹, hF, he, twistShape_of_tmWild h hw, ?_⟩
    intro σ hσ
    simp only [htame σ hσ, inv_one]

end LocalG

/-! ### §D. The interface over the object; `G15RamG` proved for it -/

/-- **The data of G8-G12 as an object**: the embeddings of g0-mod-newform's `ModData` and the two
descent data at `ℓ = 5`, `ℓ = 3`; the representations are *constructed* (`DescData.r`), not
free fields. -/
structure ModObj (A : PkgI3.AbVar K) where
  i : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K
  ιC : PkgI4.Qbar →ₐ[ℚ] ℂ
  ι5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5
  ι3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3
  D5 : DescData A 5
  D3 : DescData A 3

/-- The object as g0-mod-newform's `ModData` (`r₅ = D5.r`, `r₃ = D3.r`). The restated interface
is g0-mod-newform's `G12Spec`, `G14TraceCompat`, `G15RamG` applied to `M.toModData` only. -/
def ModObj.toModData {A : PkgI3.AbVar K} (M : ModObj A) : G0ModNewform.ModData K A :=
  ⟨M.i, M.ιC, M.ι5, M.ι3, M.D5.r, M.D3.r⟩

/-- **`G15RamG` for the constructed object (GLUE, proved).** From `LocalDataG` on the descent data
at `5` (for `p ≠ 5`) and at `3` (for `p = 5`), and G2, G3 (for G11's clause (iii)), by g15-ram's
`g15RamG_of_localData`. -/
theorem g15RamG_obj {A : PkgI3.AbVar K} (M : ModObj A) (u : ℚ)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataG p ⟨hp⟩ 5 _ _ _ _ M.D5.Tm M.D5.a M.D5.β)
    (h3 : LocalDataG 5 M.D3.Tm M.D3.a M.D3.β)
    (h2 : G0Galois.G2Out K (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h35 : G0Galois.G3Out A 5 (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h33 : G0Galois.G3Out A 3 (GlueDescent.ramSet ZInQ.Mult.S_mul u)) :
    G0ModNewform.G15RamG M.toModData u :=
  G15Ram.g15RamG_of_localData M.toModData u
    (fun p hp hp5 => @localData_of_intertwines p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ M.D5.intertwines
      (h5 p hp hp5))
    (localData_of_intertwines M.D3.intertwines h3)
    (g11_of_intertwines _ h2 h35 M.D5.rho_resQ M.D5.intertwines)
    (g11_of_intertwines _ h2 h33 M.D3.rho_resQ M.D3.intertwines)

/-- **`G15RamG` for every `ModData` whose `r₅`, `r₃` carry G8's intertwining on the data (proved).**
The same proof: only the intertwining is used, so the constructed basis plays no role. -/
theorem g15RamG_of_intertwines {A : PkgI3.AbVar K} (D : G0ModNewform.ModData K A) (u : ℚ)
    (D5 : DescData A 5) (D3 : DescData A 3)
    (e5 : G0Galois.Vb A 5 ≃ₗ[PadicAlgCl 5] (Fin 2 → PadicAlgCl 5) × (Fin 2 → PadicAlgCl 5))
    (e3 : G0Galois.Vb A 3 ≃ₗ[PadicAlgCl 3] (Fin 2 → PadicAlgCl 3) × (Fin 2 → PadicAlgCl 3))
    (hi5 : G0Galois.Intertwines (GlueDescent.rho D5.Tm D5.a D5.β) D.r5.mat e5)
    (hi3 : G0Galois.Intertwines (GlueDescent.rho D3.Tm D3.a D3.β) D.r3.mat e3)
    (h5 : ∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @LocalDataG p ⟨hp⟩ 5 _ _ _ _ D5.Tm D5.a D5.β)
    (h3 : LocalDataG 5 D3.Tm D3.a D3.β)
    (h2 : G0Galois.G2Out K (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h35 : G0Galois.G3Out A 5 (GlueDescent.ramSet ZInQ.Mult.S_mul u))
    (h33 : G0Galois.G3Out A 3 (GlueDescent.ramSet ZInQ.Mult.S_mul u)) :
    G0ModNewform.G15RamG D u :=
  G15Ram.g15RamG_of_localData D u
    (fun p hp hp5 => @localData_of_intertwines p ⟨hp⟩ 5 _ _ _ _ _ _ _ _ _ hi5 (h5 p hp hp5))
    (localData_of_intertwines hi3 h3)
    (g11_of_intertwines _ h2 h35 D5.rho_resQ hi5)
    (g11_of_intertwines _ h2 h33 D3.rho_resQ hi3)

end G8Object

end

#print axioms G8Object.DescData.intertwines
#print axioms G8Object.DescData.g8Out
#print axioms G8Object.mat_eq_scalar_of_intertwines
#print axioms G8Object.g11_of_intertwines
#print axioms G8Object.localData_of_intertwines
#print axioms G8Object.g15RamG_obj
#print axioms G8Object.g15RamG_of_intertwines
