import ZInQKernel.Contrib.OneProof.RC.Skeleton.Steps

/-!
# Theorem 5.3, Lane RC0: Elliot's deduction of the restricted converse, proved from its inputs

`restrictedConverse_of_steps` proves `SelmerTwoPower.RestrictedConverseGenuine` (Theorem 5.3 of the
11/5 manuscript over the genuine Selmer condition) from the inputs of `Steps.lean`, following the
order of Elliot's text:

1. **Branch split** (lines 2593–2602). If the intrinsic odd limit symbol is a unit at the empty
   configuration (`RCData.OddEmptyUnit`), choose an actual stage carrying that value with
   `M_θ > δ_o` (`oddEmptyUnit_stage`, PROVED from the ultrafilter); `D = 1` is in the support and
   `v₂ a_{M_θ}(1) = δ_o < M_θ`, so (O.8) gives `ord_{s=1} L(E,s) = 1`. No companion or determinant
   bound is used in this branch.
2. **Remaining branch.** Root number `−1` (Dokchitser–Dokchitser, lines 1793–1797) makes the order
   odd. Suppose it is not one; then it is at least three. Fix the final companion `k`
   (2604–2613): `L(E^{(k)},1) ≠ 0`; the forward theorem gives `s₂(E^{(k)}/ℚ) = 0`, so
   `s₂(E/K) = 1` (2627–2647); and `L'(E/K,1) = 0` (`lKDerivZero_of_order`, from
   `L(E/K,s) = L(E,s)L(E^{(k)},s)`).
3. **Constants in Elliot's order** (2706–2711, 5650–5662; App G 10898–10905): `C_o, C_e` (3.9),
   the period constant `C_per` of (3.4), `C_cal` (4.6) and `v₂L_*(h_*)` give
   `C_J = 2C_o + C_e − v₂L_*(h_*) + C_per + 2` and the upper bound
   `B = C_J + C_cal` (`central_upper_bound`, PROVED from (3.9), (3.4), (4.6), (4.7));
   then `K` gives `c_det, d_K` (5.9); then `M > max(c_det, B + 2c_det)`; then
   `b > (L_T(M) + 2)(2^M − 1)` with `L_T(M) = 16(d_K + 5)M`, and `b` large enough for (3.9);
   then the family over `𝔽₂^b` (3.9) and its coordinates, `f, d` (5.9).
4. **The missing address** (5.10)–(5.11): the `q = L_T(M) + 2` coefficient equalities give `x ≠ 0`
   (`BooleanAddress`), and the convolution estimate gives
   `v₂(ũ_x(0) − ũ_0(0)) ≥ M − 2c > B`.
5. **Base zero** (4319–4373): `L'(E/K,1) = 0` gives `ũ_0(0) = 0`, so `v₂ ũ_x(0) > B`,
   contradicting `v₂ ũ_x(0) ≤ B`. Hence the order is one.
-/

noncomputable section

namespace ZInQ.Manuscript.RC

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower Filter

attribute [local instance] Nat.fact_prime_two

/-! ## Elementary facts used by the deduction -/

/-- `q^* ≠ 0` for `q ≠ 0` (PROVED). -/
theorem qstar_ne_zero {q : ℕ} (hq : q ≠ 0) : qstar q ≠ 0 := by
  unfold qstar
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hq)

/-- The members of an admissible family are nonzero (PROVED). -/
theorem Family.h_ne_zero {S : Finset ℕ} {k : ℤ} {F : Family} (hF : F.Admissible S k)
    (x : Addr F.b) : F.h x ≠ 0 := by
  unfold Family.h
  rw [Finset.prod_ne_zero_iff]
  intro q hq
  exact pow_ne_zero _ (qstar_ne_zero (hF q hq).1.ne_zero)

/-- A prime dividing `h_x` belongs to `Q` (PROVED). -/
theorem Family.mem_Q_of_prime_dvd {S : Finset ℕ} {k : ℤ} {F : Family} (hF : F.Admissible S k)
    (x : Addr F.b) {p : ℕ} (hp : p.Prime) (hpd : (p : ℤ) ∣ F.h x) : p ∈ F.Q := by
  unfold Family.h at hpd
  obtain ⟨q, hq, hdvd⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp hp) _).mp hpd
  have h1 : (p : ℤ) ∣ qstar q := (Nat.prime_iff_prime_int.mp hp).dvd_of_dvd_pow hdvd
  unfold qstar at h1
  have h2 : (p : ℤ) ∣ (q : ℤ) := ((isUnit_neg_one (α := ℤ)).pow _).dvd_mul_left.mp h1
  have h3 : p ∣ q := Int.natCast_dvd_natCast.mp h2
  rwa [(Nat.prime_dvd_prime_iff_eq hp (hF q hq).1).mp h3]

/-- The 2-adic valuation of a unit of `ℤ₂` is `0` (PROVED). -/
theorem v2_coe_of_isUnit {z : ℤ_[2]} (hz : IsUnit z) : v2 (z : ℚ_[2]) = 0 := by
  have hz0 : z ≠ 0 := hz.ne_zero
  have hn := PadicInt.norm_eq_zpow_neg_valuation hz0
  rw [PadicInt.isUnit_iff.mp hz, zpow_neg, zpow_natCast] at hn
  have h2 : ((2 : ℕ) : ℝ) ^ z.valuation = 1 := by
    have := congrArg (·⁻¹) hn
    simpa using this.symm
  have hv : z.valuation = 0 := by
    have h3 : (2 : ℕ) ^ z.valuation = 1 := by exact_mod_cast h2
    simpa using h3
  rw [v2, Padic.addValuation.apply (by simpa using hz0), PadicInt.valuation_coe, hv]
  rfl

/-- `v₂` of a nonzero 2-adic integer is its `PadicInt.valuation` (PROVED). -/
theorem v2_coe_padicInt {z : ℤ_[2]} (hz : z ≠ 0) : v2 (z : ℚ_[2]) = ((z.valuation : ℕ) : ℤ) := by
  rw [v2, Padic.addValuation.apply (by simpa using hz), PadicInt.valuation_coe]

/-- A norm bound `‖y‖ ≤ 2^{−m}` is the valuation bound `v₂ y ≥ m` (PROVED). -/
theorem le_v2_of_norm_le {y : ℚ_[2]} {m : ℤ} (h : ‖y‖ ≤ (2 : ℝ) ^ (-m)) :
    (m : WithTop ℤ) ≤ v2 y := by
  by_cases hy : y = 0
  · simp [hy, v2]
  · rw [v2, Padic.addValuation.apply hy]
    apply WithTop.coe_le_coe.mpr
    rw [Padic.norm_eq_zpow_neg_valuation hy] at h
    have h2 : ((2 : ℕ) : ℝ) ^ (-y.valuation) ≤ ((2 : ℕ) : ℝ) ^ (-m) := by exact_mod_cast h
    have := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < ((2 : ℕ) : ℝ))).mp h2
    omega

/-- **A `Λ`-unit multiple has the same central valuation** (PROVED; the use of (4.7) at
lines 4153–4155: the identity `ũ_x = ε_x u_{prim,x}` preserves the central valuation). -/
theorem v2_central_lamUnit_mul {ε u : PowerSeries ℚ_[2]} (hε : LamUnit ε) :
    v2 (central (ε * u)) = v2 (central u) := by
  obtain ⟨e, rfl⟩ := hε
  have hc : IsUnit (PowerSeries.constantCoeff (e : PowerSeries ℤ_[2])) :=
    (PowerSeries.isUnit_iff_constantCoeff).mp e.isUnit
  have h0 : central (PowerSeries.map PadicInt.Coe.ringHom (e : PowerSeries ℤ_[2]) * u) =
      ((PowerSeries.constantCoeff (e : PowerSeries ℤ_[2]) : ℤ_[2]) : ℚ_[2]) * central u := by
    have hm : PowerSeries.constantCoeff (PowerSeries.map PadicInt.Coe.ringHom
        (e : PowerSeries ℤ_[2])) = ((PowerSeries.constantCoeff (e : PowerSeries ℤ_[2]) : ℤ_[2]) :
          ℚ_[2]) := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      rfl
    simp [central, hm]
  rw [h0, v2, AddValuation.map_mul, ← v2, ← v2, v2_coe_of_isUnit hc, zero_add]

/-- **Branch 1: an actual stage carrying the unit value** (PROVED; lines 2593–2596). If the odd
symbol is a unit at the empty configuration, some stage has `v₂ a_{M_θ}(1) = δ_o < M_θ`. -/
theorem oddEmptyUnit_stage {ℓ : ℕ} (D : RCData ℓ) (hU : D.OddEmptyUnit)
    (hM : Tendsto D.Mθ (D.stages : Filter ℕ) atTop) :
    ∃ θ : ℕ, vZ (D.aθ θ 1) = D.δo ∧ D.δo < (D.Mθ θ : ℤ) := by
  have hev : ∀ᶠ θ in (D.stages : Filter ℕ), D.δo.toNat + 1 ≤ D.Mθ θ :=
    tendsto_atTop.mp hM (D.δo.toNat + 1)
  obtain ⟨θ, h1, h2⟩ := (hU.and hev).exists
  refine ⟨θ, h1, ?_⟩
  have := Int.self_le_toNat D.δo
  omega

/-! ## The upper bound `B` at the nonzero addresses -/

/-- **The upper bound `v₂ ũ_x(0) ≤ B` at every nonzero address** (PROVED from (3.9), (3.4), (4.6),
(4.7) and the normalization of `L_*`; lines 2713–2714, 5728–5732, App G 10868–10884):
`2j_rc(h_x,k) ≤ 4ω(h_x) + C_J` with `C_J = 2C_o + C_e − v₂L_*(h_*) + C_per + 2`, and the finite `Ш` and
companion terms of (4.6) are nonnegative, so `v₂ ũ_x(0) ≤ C_J + C_cal`. -/
theorem central_upper_bound {ℓ : ℕ} {D : RCData ℓ} (S : RCSteps D) (hk0 : D.kfin ≠ 0)
    {Cper Ccal : ℤ}
    (h34 : ∀ h : ℤ, D.prepared h → AnalyticRankOne (Etw ℓ h) → D.Lstar (h * D.kfin) ≠ 0 →
      (∀ q : ℕ, q.Prime → (q : ℤ) ∣ h → q ∉ D.S ∧ jacobiSym D.kfin q = 1) →
      ∃ ε : ℤ, |ε| ≤ 2 ∧ 2 * D.jrc h D.kfin - 2 * D.jgen h =
        padicValRat 2 (D.Lstar (h * D.kfin)) - padicValRat 2 (D.Lstar D.hstar) + Cper + ε)
    (hcal : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∀ x : Addr F.b, AnalyticRankOne (Etw ℓ (F.h x)) →
        CentralNonzero (Etw ℓ (F.h x * D.kfin)) →
        ∃ (t : ℕ → ℕ) (err : ℤ), (∀ p, t p ≤ 2) ∧ |err| ≤ Ccal ∧
          v2 (central (D.uPrim F x)) =
            ((2 * D.jrc (F.h x) D.kfin - 4 * omega (F.h x) - shaLength (Etw ℓ (F.h x)) -
              shaLength (Etw ℓ (F.h x * D.kfin)) -
                ∑ p ∈ D.kfin.natAbs.primeFactors, (t p : ℤ) + err : ℤ) : WithTop ℤ))
    {Co Ce : ℤ} {F : Family} (hF : D.FinalFamilyAt Co Ce F) {x : Addr F.b} (hx : x ≠ 0) :
    v2 (central (D.uTilde F x)) ≤
      ((2 * Co + Ce - padicValRat 2 (D.Lstar D.hstar) + Cper + 2 + Ccal : ℤ) : WithTop ℤ) := by
  obtain ⟨hadm, hfx⟩ := hF
  obtain ⟨hprep, hsz, hLne, hjg, hvL⟩ := hfx x hx
  have hh0 : F.h x ≠ 0 := Family.h_ne_zero hadm x
  have hcn : CentralNonzero (Etw ℓ (F.h x * D.kfin)) :=
    (S.lstar_ne_zero_iff _ (mul_ne_zero hh0 hk0)).mp hLne
  -- (3.4) at `(h_x, k)`
  have hprimes : ∀ q : ℕ, q.Prime → (q : ℤ) ∣ F.h x → q ∉ D.S ∧ jacobiSym D.kfin q = 1 := by
    intro q hq hqd
    obtain ⟨-, -, hqS, hjac, -⟩ := hadm q (Family.mem_Q_of_prime_dvd hadm x hq hqd)
    exact ⟨hqS, hjac⟩
  obtain ⟨ε, hε, h34x⟩ := h34 (F.h x) hprep hsz hLne hprimes
  -- (4.6) at `(h_x, k)`
  obtain ⟨t, err, -, herr, h46⟩ := hcal Co Ce F ⟨hadm, hfx⟩ x hsz hcn
  -- (4.7)
  obtain ⟨ε', hε', h47⟩ := S.common_coordinate Co Ce F ⟨hadm, hfx⟩ x
  rw [h47, v2_central_lamUnit_mul hε', h46]
  apply WithTop.coe_le_coe.mpr
  have hT : 0 ≤ ∑ p ∈ D.kfin.natAbs.primeFactors, (t p : ℤ) :=
    Finset.sum_nonneg fun p _ => Int.natCast_nonneg _
  have hs1 : (0 : ℤ) ≤ shaLength (Etw ℓ (F.h x)) := Int.natCast_nonneg _
  have hs2 : (0 : ℤ) ≤ shaLength (Etw ℓ (F.h x * D.kfin)) := Int.natCast_nonneg _
  have hε2 := (abs_le.mp hε).2
  have herr2 := (abs_le.mp herr).2
  linarith

/-! ## The deduction -/

/-- **Branch 1** (lines 2593–2599, PROVED from (O.8)): if the intrinsic odd limit symbol is a unit at
the empty configuration, choose an actual stage carrying that value with `M_θ > δ_o`; the index
`D = 1` lies in every moving support and `v₂ a_{M_θ}(1) = δ_o < M_θ`, so (O.8) gives
`ord_{s=1} L(E,s) = 1`. No companion or determinant bound is used. -/
theorem rc_of_oddEmptyUnit {ℓ : ℕ} (D : RCData ℓ) (S : RCSteps D) (hU : D.OddEmptyUnit) :
    AnalyticRankOne (Eℓ ℓ) := by
  obtain ⟨θ, hval, hlt⟩ := oddEmptyUnit_stage D hU S.stages_advance
  obtain ⟨Cdet, hO8⟩ := S.visibility
  have hvis : vZ (D.aθ θ 1) < (D.Mθ θ : WithTop ℤ) := by
    rw [hval]
    exact_mod_cast hlt
  have h := (hO8 θ 1 (S.one_admissible θ) hvis).1
  simpa [Etw, Eℓ, twist_one_curve] using h

/-- **The missing address** (Proposition `ex:limits-coefficient-transfer`, lines 5647–5726, with
the order of choices of 2704–2711 and App G 10898–10905; PROVED from the inputs). In the remaining
branch there is one bound `B`, fixed before `b`, a family satisfying (3.9) and a nonzero address
`x` with `v₂ ũ_x(0) ≤ B` and `v₂(ũ_x(0) − ũ_0(0)) > B`. The constants are chosen in Elliot's
order: `C_o, C_e` (3.9), `C_per` (3.4), `C_cal` (4.6), hence `B`; then `c_det, d_K` (5.9, fixed
with `K`); then `M > max(c_det, B + 2c_det)`; then `b > (L_T(M) + 2)(2^M − 1)`, `b ≥ b₀`; then the
family over `𝔽₂^b` and its `f, d`. -/
theorem exists_address_gap {ℓ : ℕ} (hBool : BooleanAddress) (hConv : ConvolutionEstimate)
    (D : RCData ℓ) (S : RCSteps D) (hU : ¬ D.OddEmptyUnit) :
    ∃ (B Co Ce : ℤ) (F : Family) (x : Addr F.b), D.FinalFamilyAt Co Ce F ∧ x ≠ 0 ∧
      v2 (central (D.uTilde F x)) ≤ (B : WithTop ℤ) ∧
      (B : WithTop ℤ) < v2 (central (D.uTilde F x) - central (D.uTilde F 0)) := by
  obtain ⟨hkneg, -, -, -, -, -⟩ := S.companion hU
  have hk0 : D.kfin ≠ 0 := hkneg.ne
  -- Constants fixed before `b`: `C_o, C_e` (3.9), `C_per` (3.4), `C_cal` (4.6), hence `B`.
  obtain ⟨Co, Ce, b₀, hfam⟩ := S.final_family hU
  obtain ⟨Cper, h34⟩ := S.gz_comparison
  obtain ⟨Ccal, hcal⟩ := S.calibration
  set B : ℤ := 2 * Co + Ce - padicValRat 2 (D.Lstar D.hstar) + Cper + 2 + Ccal with hB
  -- `K` fixes `c_det, d_K` (5.9).
  obtain ⟨cdet, dK, hclr⟩ := S.clearing
  -- The choice (5.10): first `M`, then `b`.
  set M : ℕ := (max (cdet : ℤ) (B + 2 * cdet)).toNat + 1 with hMdef
  have hMmax : max (cdet : ℤ) (B + 2 * cdet) < (M : ℤ) := by
    have := Int.self_le_toNat (max (cdet : ℤ) (B + 2 * cdet))
    push_cast [hMdef]
    omega
  have hM1 : (cdet : ℤ) < M := lt_of_le_of_lt (le_max_left _ _) hMmax
  have hM2 : B + 2 * cdet < M := lt_of_le_of_lt (le_max_right _ _) hMmax
  set L : ℕ := 16 * (dK + 5) * M with hL
  set b : ℕ := max b₀ ((L + 2) * (2 ^ M - 1) + 1) with hbdef
  -- The final family over `𝔽₂^b` (3.9), and `f, d` (5.9) at the precision `M`.
  obtain ⟨F, hFb, hF⟩ := hfam b (le_max_left _ _)
  obtain ⟨f, d, hmul, hf0, hcv, hpole⟩ := hclr M Co Ce F hF
  -- The `q = L_T(M) + 2` coefficient equalities (5.10): the coefficients of `f` from `−L_T(M)`
  -- through `0` and the constant coefficient of `d`.
  let α : Fin (L + 2) → Addr F.b → ℤ_[2] := fun j g =>
    if (j : ℕ) ≤ L then (f g).coeff (-(j : ℤ)) else (d g).coeff 0
  have hq : (L + 2) * (2 ^ (M - 1) - 1) < F.b := by
    have h1 : 2 ^ (M - 1) - 1 ≤ 2 ^ M - 1 :=
      Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)) _
    have h2 : (L + 2) * (2 ^ (M - 1) - 1) ≤ (L + 2) * (2 ^ M - 1) := Nat.mul_le_mul_left _ h1
    have h3 : (L + 2) * (2 ^ M - 1) + 1 ≤ b := le_max_right _ _
    omega
  obtain ⟨x, hx0, hcong⟩ := hBool F.b M (L + 2) α hq
  -- `c = v₂ f_0(0) ≤ c_det`.
  have hne_top : v2 (evalCoeff f 0 0 : ℚ_[2]) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hcv
  have hf00 : evalCoeff f 0 0 ≠ 0 := by
    intro h
    rw [h] at hne_top
    simp [v2] at hne_top
  set c : ℕ := (evalCoeff f 0 0).valuation with hcdef
  have hccdet : (c : ℤ) ≤ cdet := by
    rw [v2_coe_padicInt hf00] at hcv
    exact_mod_cast hcv
  -- The congruences at the address `x`.
  have hcf : ∀ i : ℤ, -(L : ℤ) ≤ i → i ≤ 0 →
      (2 : ℤ_[2]) ^ M ∣ evalCoeff f x i - evalCoeff f 0 i := by
    intro i hi1 hi2
    have hj : (-i).toNat < L + 2 := by omega
    have h := hcong ⟨(-i).toNat, hj⟩
    have hjL : (-i).toNat ≤ L := by omega
    have hii : -(((-i).toNat : ℕ) : ℤ) = i := by omega
    simpa only [α, signVal, evalCoeff, hjL, ite_true, hii] using h
  have hcd : (2 : ℤ_[2]) ^ M ∣ evalCoeff d x 0 - evalCoeff d 0 0 := by
    have h := hcong ⟨L + 1, by omega⟩
    have hjL : ¬ (L + 1 ≤ L) := by omega
    simpa only [α, signVal, evalCoeff, hjL, ite_false] using h
  -- Every negative coefficient of `f_x` vanishes modulo `2^M`: below `−L_T(M)` by the pole bound,
  -- from `−L_T(M)` to `−1` by the congruences and `f_0 ∈ Λ`.
  have hneg : ∀ i < 0, (2 : ℤ_[2]) ^ M ∣ evalCoeff f x i := by
    intro i hi
    by_cases hiL : i < -(L : ℤ)
    · exact hpole x i hiL
    · have h := hcf i (by omega) hi.le
      rwa [hf0 i hi, sub_zero] at h
  -- The convolution estimate (5.11).
  obtain ⟨e, g, hg⟩ := S.height_one Co Ce F hF x
  have hconv := hConv (evalCoeff f 0) (evalCoeff f x)
    (fun n => PowerSeries.coeff n (D.uTilde F 0)) (fun n => PowerSeries.coeff n (D.uTilde F x))
    (evalCoeff d 0) (evalCoeff d x) c M ⟨e, g, hg⟩ (hmul 0 0) (hmul x) hf0 hf00 rfl
    (by omega) hneg (hcf 0 (by omega) le_rfl) hcd
  have hconv' : (((M : ℤ) - 2 * c : ℤ) : WithTop ℤ) ≤
      v2 (central (D.uTilde F x) - central (D.uTilde F 0)) := by
    apply le_v2_of_norm_le
    have : -((M : ℤ) - 2 * c) = 2 * (c : ℤ) - M := by ring
    rw [this]
    exact hconv
  -- `M − 2c > B`, and the upper bound at the nonzero address.
  have hlt : (B : WithTop ℤ) < (((M : ℤ) - 2 * c : ℤ) : WithTop ℤ) := by
    apply WithTop.coe_lt_coe.mpr
    omega
  exact ⟨B, Co, Ce, F, x, hF, hx0, central_upper_bound S hk0 h34 hcal hF hx0,
    hlt.trans_le hconv'⟩

/-- **`L'(E/K, 1) ≠ 0`** (Proposition `ex:limits-coefficient-transfer`, lines 5653–5656 and
5728–5734; PROVED from the inputs). If `L'(E/K,1) = 0`, the base-zero lemma makes `ũ_0(0) = 0`,
so `v₂ ũ_x(0) > B` at the address of `exists_address_gap`, contradicting `v₂ ũ_x(0) ≤ B`. -/
theorem baseDeriv_ne_zero {ℓ : ℕ} (hBool : BooleanAddress) (hConv : ConvolutionEstimate)
    (D : RCData ℓ) (S : RCSteps D) (hU : ¬ D.OddEmptyUnit)
    (hSelK : SelmerCorankOneOverK ℓ D.kfin) : ¬ LKDerivZero (Eℓ ℓ) D.kfin := by
  intro hLK
  obtain ⟨-, -, -, -, -, hkL⟩ := S.companion hU
  obtain ⟨B, Co, Ce, F, x, hF, -, hub, hgap⟩ := exists_address_gap hBool hConv D S hU
  rw [S.base_zero hSelK hkL hLK Co Ce F hF, sub_zero] at hgap
  exact absurd (hgap.trans_le hub) (lt_irrefl _)

/-- **Theorem 5.3 for one `ℓ`, from the inputs** (Elliot's deduction, both branches, PROVED). Root
number `−1` (Dokchitser–Dokchitser, lines 1793–1797) makes `ord_{s=1} L(E,s) = n` odd. Branch 1
is `rc_of_oddEmptyUnit`. In the remaining branch fix the final companion `k`: `L(E^{(k)},1) ≠ 0`,
the forward theorem gives `s₂(E^{(k)}/ℚ) = 0`, so `s₂(E/K) = 1` (2627–2647); then
`L'(E/K,1) ≠ 0` (`baseDeriv_ne_zero`), and since `L(E/K,s) = L(E,s)L(E^{(k)},s)` with
`L(E^{(k)},1) ≠ 0`, `n ≤ 1`, so `n = 1` (5736–5741). -/
theorem rc_at {ℓ : ℕ} (hℓ : 0 < ℓ) (hsf : Squarefree ℓ) (hmod : ℓ % 12 = 11)
    (hDD : DDSelmerParity) (hFwd : ForwardRankZero) (hBool : BooleanAddress)
    (hConv : ConvolutionEstimate) (D : RCData ℓ) (S : RCSteps D)
    (hSel : SelmerCorankOne (Eℓ ℓ)) : AnalyticRankOne (Eℓ ℓ) := by
  -- Root number `−1`: the analytic order is odd (lines 1793–1797).
  obtain ⟨n, hodd, hn⟩ := hDD ℓ hℓ hsf hmod hSel
  by_cases hU : D.OddEmptyUnit
  · -- Branch 1 (lines 2593–2599).
    exact rc_of_oddEmptyUnit D S hU
  · -- The remaining branch: the final companion `k` (lines 2604–2647).
    obtain ⟨hkneg, -, -, -, -, hkL⟩ := S.companion hU
    have hEk : (Etw ℓ D.kfin).IsElliptic := by
      rw [Etw, Eℓ, twist_curve]
      exact PoleRC.curve_isElliptic (mul_ne_zero (by exact_mod_cast hkneg.ne)
        (by exact_mod_cast hℓ.ne'))
    have hSelK : SelmerCorankOneOverK ℓ D.kfin := ⟨hSel, hFwd _ hEk hkL⟩
    -- `L'(E/K, 1) ≠ 0` (Proposition `ex:limits-coefficient-transfer`).
    have hLK := baseDeriv_ne_zero hBool hConv D S hU hSelK
    -- `L(E/K,s) = L(E,s) L(E^{(k)},s)` and `L(E^{(k)},1) ≠ 0` give `n ≤ 1`; `n` is odd.
    have hn1 : n = 1 := by
      by_contra hne
      have hn2 : 2 ≤ n := by
        obtain ⟨m, rfl⟩ := hodd
        omega
      exact hLK (lKDerivZero_of_order hn hn2 hkL)
    subst hn1
    exact (analyticOrder_one_iff _).mp hn

/-- **Theorem 5.3 (restricted converse, `hyp:RC`) from the inputs of Elliot's deduction.**
For the genuine Selmer condition (`SelmerTwoPower.RestrictedConverseGenuine`): if every input of
`Steps.lean` holds — the four data-free inputs (Dokchitser–Dokchitser parity, the forward theorem
in rank zero, the Boolean missing address and the convolution estimate (5.11)) and, for each
admissible `ℓ`, the inputs `RCSteps (D ℓ)` about interface data `D ℓ` — then for every positive
squarefree `ℓ ≡ 11 (mod 12)`, `corank_{ℤ₂} Sel_{2^∞}(E_ℓ/ℚ) = 1` implies `ord_{s=1} L(E_ℓ, s) = 1`. -/
theorem restrictedConverse_of_steps (hDD : DDSelmerParity) (hFwd : ForwardRankZero)
    (hBool : BooleanAddress) (hConv : ConvolutionEstimate) (D : ∀ ℓ : ℕ, RCData ℓ)
    (hS : ∀ ℓ : ℕ, 0 < ℓ → Squarefree ℓ → ℓ % 12 = 11 → RCSteps (D ℓ)) :
    RestrictedConverseGenuine := by
  intro ℓ hℓ hsf hmod hSel
  exact rc_at hℓ hsf hmod hDD hFwd hBool hConv (D ℓ) (hS ℓ hℓ hsf hmod) hSel

/-! ## Non-vacuity of the interface

The skeleton's inputs quantify over interface data. The checks below show that the quantifiers are
not empty and that the branch split is a genuine case distinction: the interface structure is
inhabited; the binary families quantified in (4.6), (4.7), (5.9), the height-one regularity and
the base-zero lemma include an actual family (`finalFamilyAt_trivial`), and admissible families
with nonzero addresses exist (`admissible_example`), so the conditions (3.9) imposes at `x ≠ 0` are
not vacuous; the coefficient-level product `MulRel` is satisfiable (`mulRel_one`); and the odd
empty-configuration symbol can be a unit or not (`toyData_oddEmptyUnit`,
`toyData_not_oddEmptyUnit`), with arbitrarily advanced stages along a nonprincipal ultrafilter
(`toyData_stages_advance`). -/

/-- Toy interface data, with constant odd coefficients `a`: the hyperfilter on stages, `M_θ = θ`. -/
def toyData (ℓ : ℕ) (a : ℤ) : RCData ℓ where
  S := ∅
  prepared := fun _ => True
  Lstar := fun _ => 1
  jgen := fun _ => 0
  jrc := fun _ _ => 0
  hstar := -1
  stages := Filter.hyperfilter ℕ
  Mθ := fun θ => θ
  aθ := fun _ _ => a
  admissible := fun _ _ => True
  δo := 0
  kfin := -7
  uPrim := fun _ _ => 1
  uTilde := fun _ _ => 1

instance (ℓ : ℕ) : Inhabited (RCData ℓ) := ⟨toyData ℓ 0⟩

/-- With unit odd coefficients the empty configuration is a unit (PROVED). -/
theorem toyData_oddEmptyUnit (ℓ : ℕ) : (toyData ℓ 1).OddEmptyUnit := by
  refine Filter.Eventually.of_forall fun θ => ?_
  simp [toyData, vZ, v2]

/-- With zero odd coefficients the empty configuration is not a unit (PROVED). -/
theorem toyData_not_oddEmptyUnit (ℓ : ℕ) : ¬ (toyData ℓ 0).OddEmptyUnit := by
  intro h
  have h' : ∀ᶠ _θ in ((toyData ℓ 0).stages : Filter ℕ), False := by
    filter_upwards [h] with θ hθ
    simp [toyData, vZ, v2] at hθ
  exact h'.exists.elim fun _ h => h

/-- The toy stages advance along the (nonprincipal) hyperfilter (PROVED). -/
theorem toyData_stages_advance (ℓ : ℕ) (a : ℤ) :
    Tendsto (toyData ℓ a).Mθ ((toyData ℓ a).stages : Filter ℕ) atTop := by
  have h : ((Filter.hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) ≤ atTop :=
    Filter.hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le
  exact tendsto_id.mono_left h

/-- The binary family of dimension `0` (`h_0 = 1` only). -/
def trivialFamily : Family := ⟨0, ∅, fun _ => 0⟩

/-- Every interface datum has a family satisfying (3.9) in dimension `0`, so the statements
quantified over final families are not vacuous (PROVED). -/
theorem finalFamilyAt_trivial {ℓ : ℕ} (D : RCData ℓ) (Co Ce : ℤ) :
    D.FinalFamilyAt Co Ce trivialFamily := by
  refine ⟨fun q hq => absurd hq (Finset.notMem_empty q), fun x hx => absurd ?_ hx⟩
  funext i
  exact i.elim0

/-- An admissible family with a nonzero address: `b = 1`, `Q = {11}`, `λ₁₁ = x ↦ x₀`, for the
companion `k = −7` (`(−7/11) = 1`) and empty support (PROVED). -/
theorem admissible_example :
    Family.Admissible ∅ (-7) ⟨1, {11}, fun _ => LinearMap.proj (R := ZMod 2)
      (φ := fun _ : Fin 1 => ZMod 2) 0⟩ := by
  intro q hq
  rw [Finset.mem_singleton] at hq
  subst hq
  refine ⟨by norm_num, by norm_num, Finset.notMem_empty _, by norm_num, ?_⟩
  intro h
  have := LinearMap.congr_fun h (fun _ => 1)
  simp at this

/-- The coefficient-level product is satisfiable: `1 · 1 = 1` (PROVED). -/
theorem mulRel_one :
    MulRel (fun i => if i = 0 then 1 else 0) 1 (fun i => if i = 0 then 1 else 0) := by
  intro n
  have h : HasSum (fun i : ℕ => ((((fun i : ℤ => if i = 0 then (1 : ℤ_[2]) else 0) (n - i)) :
      ℤ_[2]) : ℚ_[2]) * PowerSeries.coeff i (1 : PowerSeries ℚ_[2]))
      (((((fun i : ℤ => if i = 0 then (1 : ℤ_[2]) else 0) (n - (0 : ℕ))) : ℤ_[2]) : ℚ_[2]) *
        PowerSeries.coeff 0 (1 : PowerSeries ℚ_[2])) :=
    hasSum_single 0 fun i hi => by simp [PowerSeries.coeff_one, hi]
  simpa using h

/-- The unit `1 ∈ 𝒪` by its Laurent coefficients. -/
def oneO : OuterCoeff where
  coeff := fun i => if i = 0 then 1 else 0
  decay := fun _ => ⟨0, fun i hi => by simp [show i ≠ 0 by omega]⟩

/-- The conclusion of (5.9) is satisfiable: for the dimension-`0` family and a coordinate `ũ = 1`,
`f = d = 1 ∈ 𝒪[G]` satisfy `f ũ = d`, `f_0 ∈ Λ`, `v₂ f_0(0) = 0` and every pole bound (PROVED). -/
theorem clearing_conclusion_satisfiable (cdet dK M : ℕ) :
    ∃ f d : GrpRingO trivialFamily.b,
      (∀ x : Addr trivialFamily.b, MulRel (evalCoeff f x) 1 (evalCoeff d x)) ∧
      (∀ i : ℤ, i < 0 → evalCoeff f 0 i = 0) ∧
      v2 (evalCoeff f 0 0 : ℚ_[2]) ≤ (cdet : ℤ) ∧
      ∀ x : Addr trivialFamily.b, ∀ i : ℤ, i < -((16 * (dK + 5) * M : ℕ) : ℤ) →
        (2 : ℤ_[2]) ^ M ∣ evalCoeff f x i := by
  have hx : ∀ x : Addr trivialFamily.b, x = 0 := fun x => funext fun i => i.elim0
  have hev : ∀ (x : Addr trivialFamily.b) (i : ℤ),
      evalCoeff (fun _ => oneO) x i = if i = 0 then 1 else 0 := by
    intro x i
    rw [hx x]
    have h1 : ∀ g : Addr trivialFamily.b, chi (0 : Addr trivialFamily.b) g = 1 := by
      intro g
      simp [chi]
    simp only [evalCoeff, h1, Int.cast_one, one_mul, oneO]
    split_ifs
    · rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
      have hc : Fintype.card (Addr trivialFamily.b) = 1 := Fintype.card_eq_one_iff.mpr ⟨0, hx⟩
      rw [hc]
      simp
    · simp
  refine ⟨fun _ => oneO, fun _ => oneO, fun x => ?_, fun i hi => ?_, ?_, fun x i hi => ?_⟩
  · have h := mulRel_one
    intro n
    simpa only [hev] using h n
  · rw [hev]; simp [hi.ne]
  · rw [hev]; simp [v2]
  · rw [hev]
    have : i ≠ 0 := by omega
    simp [this]

end ZInQ.Manuscript.RC
