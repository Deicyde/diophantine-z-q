import Mathlib

/-!
# deg-det: the algebra of Mumford's proof of `deg φ = det T_ℓ(φ)` (Mathlib only)

Task deg-det (2026-11-16), report `docs/research/deg-det.md`, scratch `scratch/deg-det/`.

D. Mumford, *Abelian varieties* (1970), §19, Theorem 4 (UNVERIFIED locator): for `φ ∈ End(X)`,
`deg φ = det T_ℓ(φ)`. Mumford's proof has two geometric inputs (the degree is a homogeneous polynomial
function on `End(X)`, and `|deg ψ|_ℓ = |det T_ℓ ψ|_ℓ` from counting the kernel on `ℓ`-power torsion) and a
purely algebraic part, which this file proves in an abstract form, `det_eq_deg_abstract`:

1. `eq_Rs_of_mul`, `det_aeval_eq_Rs`: a multiplicative `φ : L[X] → L` with `φ(c) = cⁿ`, `φ(X − r) = (−1)ⁿ P(r)`
   is `F ↦ ∏_{P(a)=0} F(a)`; in particular `det F(M) = ∏_{χ_M(a)=0} F(a)`.
2. `eq_of_norm_RsZ`: the comparison lemma: two monic polynomials over `ℚ_ℓ` with
   `|∏_{P(a)=0} F(a)|_ℓ = |∏_{Q(b)=0} F(b)|_ℓ` for all `F ∈ ℤ[X]` (nonzero left side) are equal.
3. `Nt_mul`, `P0_monic`: a homogeneous polynomial function on `ℤ[X]/(R)` that is multiplicative on pairs of
   nonzero values extends to a multiplicative function on `S[X]/(R)` for every `ℚ`-algebra `S`
   (Combinatorial Nullstellensatz), and `N(t − X)` is monic of degree `n`.

`det_eq_deg_abstract_le` is the one-sided variant (`|deg ψ|_ℓ ≤ |det ρ ψ|_ℓ` and `#I = n`), with the one-sided
comparison lemma `eq_of_norm_RsZ_le`.
-/

open Polynomial

noncomputable section

namespace ZInQ.Contrib.OneProof.DegDet

/-! ## 1. Products over roots -/

section Roots
set_option linter.unusedSectionVars false

variable {L : Type*} [Field L] [IsAlgClosed L]

/-- `Rs P F = ∏_{P(a) = 0} F(a)`, the roots of `P` counted with multiplicity. -/
def Rs (P F : L[X]) : L := (P.roots.map (fun a => F.eval a)).prod

theorem Rs_mul_left {P P' : L[X]} (hP : P ≠ 0) (hP' : P' ≠ 0) (F : L[X]) :
    Rs (P * P') F = Rs P F * Rs P' F := by
  unfold Rs
  rw [roots_mul (mul_ne_zero hP hP'), Multiset.map_add, Multiset.prod_add]

theorem Rs_pow_left (P : L[X]) (e : ℕ) (F : L[X]) : Rs (P ^ e) F = Rs P F ^ e := by
  unfold Rs
  rw [roots_pow, Multiset.map_nsmul, Multiset.prod_nsmul]

theorem prod_map_neg' {ι : Type*} (s : Multiset ι) (f : ι → L) :
    (s.map (fun x => -f x)).prod = (-1) ^ Multiset.card s * (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, Multiset.map_cons, Multiset.prod_cons,
      Multiset.card_cons, pow_succ]
    ring

/-- **Abstract lemma.** A multiplicative `φ : L[X] → L` with `φ(c) = c^n` and
`φ(X - r) = (-1)^n P(r)` for a monic `P` of degree `n` is `F ↦ ∏_{P(a)=0} F(a)`. -/
theorem eq_Rs_of_mul (φ : L[X] →* L) (n : ℕ) (P : L[X]) (hPm : P.Monic) (hPd : P.natDegree = n)
    (hC : ∀ c, φ (C c) = c ^ n) (hlin : ∀ r, φ (X - C r) = (-1) ^ n * P.eval r) (F : L[X]) :
    φ F = Rs P F := by
  have hF := (IsAlgClosed.splits F).eq_prod_roots
  have hcard : Multiset.card P.roots = n := by
    rw [← hPd, (IsAlgClosed.splits P).natDegree_eq_card_roots]
  have hPev : ∀ r, P.eval r = (P.roots.map (r - ·)).prod :=
    (IsAlgClosed.splits P).eval_eq_prod_roots_of_monic hPm
  have hFev : ∀ a, F.eval a = F.leadingCoeff * (F.roots.map (a - ·)).prod :=
    (IsAlgClosed.splits F).eval_eq_prod_roots
  have lhs : φ F = F.leadingCoeff ^ n *
      (F.roots.map (fun r => (P.roots.map (fun a => a - r)).prod)).prod := by
    conv_lhs => rw [hF]
    rw [map_mul, hC, map_multiset_prod, Multiset.map_map]
    congr 2
    apply Multiset.map_congr rfl
    intro r _
    simp only [Function.comp_apply]
    rw [hlin, hPev, ← hcard, ← prod_map_neg']
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    ring
  rw [lhs]
  unfold Rs
  simp_rw [hFev]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard,
    Multiset.prod_map_prod_map]

end Roots

/-! ## 2. Determinants of polynomials in a matrix -/

section Matrix

variable {L : Type*} [Field L] [IsAlgClosed L] {I : Type*} [Fintype I] [DecidableEq I]

/-- `det F(M) = ∏_{χ_M(a) = 0} F(a)`. -/
theorem det_aeval_eq_Rs (M : Matrix I I L) (F : L[X]) :
    (aeval M F).det = Rs M.charpoly F := by
  let φ : L[X] →* L := (Matrix.detMonoidHom).comp (aeval M).toRingHom.toMonoidHom
  have hφ : ∀ G, φ G = (aeval M G).det := fun G => rfl
  rw [← hφ]
  refine eq_Rs_of_mul φ (Fintype.card I) M.charpoly (Matrix.charpoly_monic M)
    (Matrix.charpoly_natDegree_eq_dim M) ?_ ?_ F
  · intro c
    rw [hφ, aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.det_smul, Matrix.det_one, mul_one]
  · intro r
    rw [hφ, map_sub, aeval_X, aeval_C, Matrix.eval_charpoly, Algebra.algebraMap_eq_smul_one,
      ← Matrix.det_neg, neg_sub, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

end Matrix

/-! ## 3. The ℓ-adic comparison lemma -/

section Compare

open Filter Topology

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `∏_{P(a) = 0} F(a)` for `P` over `ℚ_ℓ` and `F` over `ℤ`, computed in `PadicAlgCl ℓ`. -/
def RsZ (P : ℚ_[ℓ][X]) (F : ℤ[X]) : PadicAlgCl ℓ :=
  Rs (P.map (algebraMap ℚ_[ℓ] (PadicAlgCl ℓ))) (F.map (Int.castRingHom (PadicAlgCl ℓ)))

omit hℓ in
theorem norm_sum_range_le {L : Type*} [NormedField L] [IsUltrametricDist L] (d : ℕ) (a : ℕ → L)
    (w : L) (ε B : ℝ) (hε : 0 ≤ ε) (hB : 1 ≤ B) (hw : ‖w‖ ≤ B)
    (ha : ∀ i ∈ Finset.range (d + 1), ‖a i‖ ≤ ε) :
    ‖∑ i ∈ Finset.range (d + 1), a i * w ^ i‖ ≤ ε * B ^ d := by
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg hε (pow_nonneg (zero_le_one.trans hB) _)) fun i hi => ?_
  rw [norm_mul, norm_pow]
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  calc ‖a i‖ * ‖w‖ ^ i ≤ ε * B ^ i :=
        mul_le_mul (ha i hi) (pow_le_pow_left₀ (norm_nonneg _) hw i) (by positivity) hε
    _ ≤ ε * B ^ d := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hid) hε

theorem norm_natCast_prime_pow (n : ℕ) : ‖((ℓ : PadicAlgCl ℓ)) ^ n‖ = ((ℓ : ℝ)⁻¹) ^ n := by
  have h := PadicAlgCl.norm_extends ℓ (ℓ : ℚ_[ℓ])
  rw [map_natCast, Padic.norm_p] at h
  rw [norm_pow, h]

theorem norm_multiset_prod_map {L : Type*} [NormedField L] {ι : Type*} (s : Multiset ι)
    (f : ι → L) : ‖(s.map f).prod‖ = (s.map (fun i => ‖f i‖)).prod := by
  have := map_multiset_prod (normHom : L →*₀ ℝ) (s.map f)
  rw [Multiset.map_map] at this
  exact this

/-- **Key estimate.** If `P = μ^e P₁`, `Q = μ^f Q₁` with `μ` irreducible monic not dividing `P₁, Q₁`, and
`|∏_{P(a)=0} F(a)| = |∏_{Q(b)=0} F(b)|` whenever the left side is nonzero, for all `F ∈ ℤ[X]`, then
`e = f`. -/
theorem mult_eq_of_norm_Rs {μ P1 Q1 : ℚ_[ℓ][X]} (hμ : Irreducible μ) (hμm : μ.Monic)
    (hP1 : P1 ≠ 0) (hQ1 : Q1 ≠ 0) (hPμ : ¬ μ ∣ P1) (hQμ : ¬ μ ∣ Q1) (e f : ℕ)
    (h : ∀ F : ℤ[X], RsZ (μ ^ e * P1) F ≠ 0 → ‖RsZ (μ ^ e * P1) F‖ = ‖RsZ (μ ^ f * Q1) F‖) :
    e = f := by
  classical
  set ι := algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) with hι
  set d := μ.natDegree with hd_def
  have hd : 0 < d := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hμ)
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  set a : ℝ := (ℓ : ℝ)⁻¹ with ha_def
  have ha0 : 0 < a := inv_pos.mpr (zero_lt_one.trans hℓ1)
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hℓ1
  -- scaling `μ` into `ℤ_ℓ[X]`
  obtain ⟨s, hs⟩ : ∃ s : ℕ, ∀ i, ‖(ℓ : ℚ_[ℓ]) ^ s * μ.coeff i‖ ≤ 1 := by
    obtain ⟨s, hsM⟩ := pow_unbounded_of_one_lt (∑ i ∈ Finset.range (d + 1), ‖μ.coeff i‖) hℓ1
    refine ⟨s, fun i => ?_⟩
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    have hci : ‖μ.coeff i‖ ≤ ∑ i ∈ Finset.range (d + 1), ‖μ.coeff i‖ := by
      by_cases hi : i ≤ d
      · exact Finset.single_le_sum (f := fun i => ‖μ.coeff i‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), norm_zero]
        exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hpos : (0 : ℝ) < (ℓ : ℝ) ^ s := pow_pos (zero_lt_one.trans hℓ1) s
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hci.trans hsM.le
  set c : ℕ → ℤ_[ℓ] := fun i => ⟨(ℓ : ℚ_[ℓ]) ^ s * μ.coeff i, hs i⟩ with hc
  set μ0 : ℚ_[ℓ][X] := C ((ℓ : ℚ_[ℓ]) ^ s) * μ with hμ0
  have hμ0nd : (μ0.map ι).natDegree < d + 1 := by
    refine Nat.lt_succ_of_le ((natDegree_map_le).trans ?_)
    exact (natDegree_C_mul_le _ _).trans le_rfl
  have hμ0ev : ∀ w, (μ0.map ι).eval w = ∑ i ∈ Finset.range (d + 1), ι (c i) * w ^ i := by
    intro w
    rw [eval_eq_sum_range' hμ0nd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, hμ0, coeff_C_mul]
  have hμ0μ : ∀ w, (μ0.map ι).eval w = ι ((ℓ : ℚ_[ℓ]) ^ s) * (μ.map ι).eval w := by
    intro w
    rw [hμ0, Polynomial.map_mul, map_C, eval_mul, eval_C]
  -- the test polynomials
  set Fn : ℕ → ℤ[X] := fun n => ∑ i ∈ Finset.range (d + 1),
    C ((PadicInt.appr (c i) (2 * n) : ℕ) : ℤ) * X ^ i + C ((ℓ : ℤ) ^ n) with hFn
  have hFev : ∀ n w, ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
      ∑ i ∈ Finset.range (d + 1), ((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) * w ^ i +
        (ℓ : PadicAlgCl ℓ) ^ n := by
    intro n w
    simp [hFn, Polynomial.map_sum, eval_finsetSum]
  have happr : ∀ n i, ‖((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) - ι (c i)‖ ≤
      a ^ (2 * n) := by
    intro n i
    have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr (PadicInt.appr_spec (2 * n) (c i))
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h1
    rw [← map_natCast ι, ← map_sub, hι, PadicAlgCl.norm_extends ℓ, norm_sub_rev]
    convert h1 using 1
    rw [ha_def, zpow_neg, zpow_natCast, inv_pow]
  have herr : ∀ n w (B : ℝ), 1 ≤ B → ‖w‖ ≤ B →
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
        (ℓ : PadicAlgCl ℓ) ^ n‖ ≤ a ^ (2 * n) * B ^ d := by
    intro n w B hB hw
    have hrw : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
        (ℓ : PadicAlgCl ℓ) ^ n = ∑ i ∈ Finset.range (d + 1),
          (((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) - ι (c i)) * w ^ i := by
      rw [hFev, hμ0ev]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      ring
    rw [hrw]
    exact norm_sum_range_le d _ w _ B (pow_nonneg ha0.le _) hB hw fun i _ => happr n i
  -- roots
  have hμmap : μ.map ι ≠ 0 := (hμm.map ι).ne_zero
  have hP1map : P1.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hP1
  have hQ1map : Q1.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hQ1
  have hcardμ : Multiset.card (μ.map ι).roots = d := by
    rw [← (IsAlgClosed.splits (μ.map ι)).natDegree_eq_card_roots, natDegree_map]
  have hμroot : ∀ w ∈ (μ.map ι).roots, (μ.map ι).eval w = 0 := fun w hw =>
    (mem_roots hμmap).mp hw
  have hnotroot : ∀ (R : ℚ_[ℓ][X]), R ≠ 0 → ¬ μ ∣ R → ∀ w ∈ (R.map ι).roots,
      (μ.map ι).eval w ≠ 0 := by
    intro R hR hRμ w hw hμw
    have hRw : aeval w R = 0 := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact (mem_roots ((Polynomial.map_ne_zero_iff ι.injective).mpr hR)).mp hw
    have hμw' : aeval w μ = 0 := by rw [aeval_def, eval₂_eq_eval_map]; exact hμw
    have hmin := minpoly.eq_of_irreducible_of_monic hμ hμw' hμm
    exact hRμ (hmin ▸ minpoly.dvd ℚ_[ℓ] w hRw)
  have hℓs : ι ((ℓ : ℚ_[ℓ]) ^ s) ≠ 0 := by
    rw [map_ne_zero_iff _ ι.injective]
    exact pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero)
  have hμ0ne : ∀ (R : ℚ_[ℓ][X]), R ≠ 0 → ¬ μ ∣ R → ∀ w ∈ (R.map ι).roots,
      0 < ‖(μ0.map ι).eval w‖ := by
    intro R hR hRμ w hw
    rw [norm_pos_iff, hμ0μ]
    exact mul_ne_zero hℓs (hnotroot R hR hRμ w hw)
  -- the bound `B`
  set Z : Finset (PadicAlgCl ℓ) :=
    ((μ.map ι).roots + (P1.map ι).roots + (Q1.map ι).roots).toFinset with hZ
  set B : ℝ := 1 + ∑ w ∈ Z, ‖w‖ with hB
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hBw : ∀ w ∈ Z, ‖w‖ ≤ B := fun w hw =>
    (Finset.single_le_sum (f := fun w => ‖w‖) (fun _ _ => norm_nonneg _) hw).trans
      (le_add_of_nonneg_left zero_le_one)
  have hmemZ1 : ∀ w ∈ (μ.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl hw)))
  have hmemZ2 : ∀ w ∈ (P1.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr hw)))
  have hmemZ3 : ∀ w ∈ (Q1.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inr hw)
  -- eventually
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1
  have ev1 : ∀ᶠ n in atTop, a ^ n * B ^ d < 1 := by
    have hBd : 0 < B ^ d := pow_pos (zero_lt_one.trans_le hB1) d
    filter_upwards [hlim.eventually (gt_mem_nhds (inv_pos.mpr hBd))] with n hn
    calc a ^ n * B ^ d < (B ^ d)⁻¹ * B ^ d := mul_lt_mul_of_pos_right hn hBd
      _ = 1 := inv_mul_cancel₀ hBd.ne'
  set S : Finset (PadicAlgCl ℓ) := (P1.map ι).roots.toFinset ∪ (Q1.map ι).roots.toFinset with hS
  have hSpos : ∀ w ∈ S, 0 < ‖(μ0.map ι).eval w‖ := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact hμ0ne P1 hP1 hPμ w (Multiset.mem_toFinset.mp hw)
    · exact hμ0ne Q1 hQ1 hQμ w (Multiset.mem_toFinset.mp hw)
  have ev2 : ∀ᶠ n in atTop, ∀ w ∈ S, a ^ n < ‖(μ0.map ι).eval w‖ := by
    rw [eventually_all_finset]
    intro w hw
    exact hlim.eventually (gt_mem_nhds (hSpos w hw))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ev1.and ev2)
  -- values of `F_n` at the roots
  have hsmall : ∀ n, N ≤ n → ∀ w ∈ Z, ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w -
      (μ0.map ι).eval w - (ℓ : PadicAlgCl ℓ) ^ n‖ < a ^ n := by
    intro n hn w hw
    refine (herr n w B hB1 (hBw w hw)).trans_lt ?_
    have := (hN n hn).1
    calc a ^ (2 * n) * B ^ d = a ^ n * (a ^ n * B ^ d) := by rw [two_mul, pow_add]; ring
      _ < a ^ n * 1 := mul_lt_mul_of_pos_left this (pow_pos ha0 n)
      _ = a ^ n := mul_one _
  have V1 : ∀ n, N ≤ n → ∀ w ∈ (μ.map ι).roots,
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w‖ = a ^ n := by
    intro n hn w hw
    set E := ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
      (ℓ : PadicAlgCl ℓ) ^ n with hE
    have hval : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
        (ℓ : PadicAlgCl ℓ) ^ n + E := by
      rw [hE, hμ0μ, hμroot w hw, mul_zero]; ring
    have hEl := hsmall n hn w (hmemZ1 w hw)
    rw [← hE] at hEl
    rw [hval, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_natCast_prime_pow]
    · exact max_eq_left hEl.le
    · rw [norm_natCast_prime_pow]; exact hEl.ne'
  have V2 : ∀ n, N ≤ n → ∀ w ∈ S,
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w‖ = ‖(μ0.map ι).eval w‖ := by
    intro n hn w hw
    have hwZ : w ∈ Z := by
      rcases Finset.mem_union.mp hw with hw | hw
      · exact hmemZ2 w (Multiset.mem_toFinset.mp hw)
      · exact hmemZ3 w (Multiset.mem_toFinset.mp hw)
    set E := ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
      (ℓ : PadicAlgCl ℓ) ^ n with hE
    have hval : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
        (μ0.map ι).eval w + ((ℓ : PadicAlgCl ℓ) ^ n + E) := by
      rw [hE]; ring
    have hEl := hsmall n hn w hwZ
    rw [← hE] at hEl
    have hsm : ‖(ℓ : PadicAlgCl ℓ) ^ n + E‖ < ‖(μ0.map ι).eval w‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt ?_
      rw [norm_natCast_prime_pow]
      exact max_lt ((hN n hn).2 w hw) (hEl.trans ((hN n hn).2 w hw))
    rw [hval, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsm.ne', max_eq_left hsm.le]
  -- the norms of the products
  have hRsP : ∀ (R : ℚ_[ℓ][X]) (k : ℕ), R ≠ 0 → ¬ μ ∣ R →
      (∀ w ∈ (R.map ι).roots, w ∈ S) → ∀ n, N ≤ n →
      ‖RsZ (μ ^ k * R) (Fn n)‖ = ((a ^ n) ^ d) ^ k *
        ((R.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod := by
    intro R k hR hRμ hRS n hn
    have hRmap : R.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hR
    unfold RsZ
    rw [Polynomial.map_mul, Polynomial.map_pow, Rs_mul_left (pow_ne_zero _ hμmap) hRmap,
      Rs_pow_left, norm_mul, norm_pow]
    unfold Rs
    rw [norm_multiset_prod_map, norm_multiset_prod_map]
    congr 2
    · rw [Multiset.map_congr rfl (V1 n hn), Multiset.map_const', Multiset.prod_replicate, hcardμ]
    · exact Multiset.map_congr rfl fun w hw => V2 n hn w (hRS w hw)
  have hP1S : ∀ w ∈ (P1.map ι).roots, w ∈ S := fun w hw =>
    Finset.mem_union.mpr (Or.inl (Multiset.mem_toFinset.mpr hw))
  have hQ1S : ∀ w ∈ (Q1.map ι).roots, w ∈ S := fun w hw =>
    Finset.mem_union.mpr (Or.inr (Multiset.mem_toFinset.mpr hw))
  set CP := ((P1.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod with hCP
  set CQ := ((Q1.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod with hCQ
  have hCPpos : 0 < CP := Multiset.prod_pos fun x hx => by
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
    exact hμ0ne P1 hP1 hPμ w hw
  have key : ∀ n, N ≤ n → ((a ^ n) ^ d) ^ e * CP = ((a ^ n) ^ d) ^ f * CQ := by
    intro n hn
    have h1 := hRsP P1 e hP1 hPμ hP1S n hn
    have h2 := hRsP Q1 f hQ1 hQμ hQ1S n hn
    rw [← h1, ← h2]
    refine h _ ?_
    rw [← norm_pos_iff, h1]
    exact mul_pos (pow_pos (pow_pos (pow_pos ha0 n) d) e) hCPpos
  have k1 := key N le_rfl
  have k2 := key (N + 1) (Nat.le_succ N)
  set x := (a ^ N) ^ d with hx
  set y := a ^ d with hy
  have hxpos : 0 < x := pow_pos (pow_pos ha0 N) d
  have hy0 : 0 < y := pow_pos ha0 d
  have hy1 : y < 1 := pow_lt_one₀ ha0.le ha1 hd.ne'
  have hk2 : (a ^ (N + 1)) ^ d = x * y := by rw [hx, hy, pow_succ, mul_pow]
  rw [hk2, mul_pow, mul_pow] at k2
  have hye : y ^ e = y ^ f := by
    have hne : x ^ e * CP ≠ 0 := (mul_pos (pow_pos hxpos e) hCPpos).ne'
    have : x ^ e * CP * y ^ e = x ^ e * CP * y ^ f := by
      calc x ^ e * CP * y ^ e = x ^ e * y ^ e * CP := by ring
        _ = x ^ f * y ^ f * CQ := k2
        _ = x ^ f * CQ * y ^ f := by ring
        _ = x ^ e * CP * y ^ f := by rw [k1]
    exact mul_left_cancel₀ hne this
  exact pow_right_injective₀ hy0 hy1.ne hye

theorem mult_le_of_norm_Rs_le {μ P1 Q1 : ℚ_[ℓ][X]} (hμ : Irreducible μ) (hμm : μ.Monic)
    (hP1 : P1 ≠ 0) (hQ1 : Q1 ≠ 0) (hPμ : ¬ μ ∣ P1) (hQμ : ¬ μ ∣ Q1) (e f : ℕ)
    (h : ∀ F : ℤ[X], RsZ (μ ^ e * P1) F ≠ 0 → ‖RsZ (μ ^ e * P1) F‖ ≤ ‖RsZ (μ ^ f * Q1) F‖) :
    f ≤ e := by
  classical
  set ι := algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) with hι
  set d := μ.natDegree with hd_def
  have hd : 0 < d := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hμ)
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.out.one_lt
  set a : ℝ := (ℓ : ℝ)⁻¹ with ha_def
  have ha0 : 0 < a := inv_pos.mpr (zero_lt_one.trans hℓ1)
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hℓ1
  -- scaling `μ` into `ℤ_ℓ[X]`
  obtain ⟨s, hs⟩ : ∃ s : ℕ, ∀ i, ‖(ℓ : ℚ_[ℓ]) ^ s * μ.coeff i‖ ≤ 1 := by
    obtain ⟨s, hsM⟩ := pow_unbounded_of_one_lt (∑ i ∈ Finset.range (d + 1), ‖μ.coeff i‖) hℓ1
    refine ⟨s, fun i => ?_⟩
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    have hci : ‖μ.coeff i‖ ≤ ∑ i ∈ Finset.range (d + 1), ‖μ.coeff i‖ := by
      by_cases hi : i ≤ d
      · exact Finset.single_le_sum (f := fun i => ‖μ.coeff i‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), norm_zero]
        exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hpos : (0 : ℝ) < (ℓ : ℝ) ^ s := pow_pos (zero_lt_one.trans hℓ1) s
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hci.trans hsM.le
  set c : ℕ → ℤ_[ℓ] := fun i => ⟨(ℓ : ℚ_[ℓ]) ^ s * μ.coeff i, hs i⟩ with hc
  set μ0 : ℚ_[ℓ][X] := C ((ℓ : ℚ_[ℓ]) ^ s) * μ with hμ0
  have hμ0nd : (μ0.map ι).natDegree < d + 1 := by
    refine Nat.lt_succ_of_le ((natDegree_map_le).trans ?_)
    exact (natDegree_C_mul_le _ _).trans le_rfl
  have hμ0ev : ∀ w, (μ0.map ι).eval w = ∑ i ∈ Finset.range (d + 1), ι (c i) * w ^ i := by
    intro w
    rw [eval_eq_sum_range' hμ0nd]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, hμ0, coeff_C_mul]
  have hμ0μ : ∀ w, (μ0.map ι).eval w = ι ((ℓ : ℚ_[ℓ]) ^ s) * (μ.map ι).eval w := by
    intro w
    rw [hμ0, Polynomial.map_mul, map_C, eval_mul, eval_C]
  -- the test polynomials
  set Fn : ℕ → ℤ[X] := fun n => ∑ i ∈ Finset.range (d + 1),
    C ((PadicInt.appr (c i) (2 * n) : ℕ) : ℤ) * X ^ i + C ((ℓ : ℤ) ^ n) with hFn
  have hFev : ∀ n w, ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
      ∑ i ∈ Finset.range (d + 1), ((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) * w ^ i +
        (ℓ : PadicAlgCl ℓ) ^ n := by
    intro n w
    simp [hFn, Polynomial.map_sum, eval_finsetSum]
  have happr : ∀ n i, ‖((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) - ι (c i)‖ ≤
      a ^ (2 * n) := by
    intro n i
    have h1 := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mpr (PadicInt.appr_spec (2 * n) (c i))
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h1
    rw [← map_natCast ι, ← map_sub, hι, PadicAlgCl.norm_extends ℓ, norm_sub_rev]
    convert h1 using 1
    rw [ha_def, zpow_neg, zpow_natCast, inv_pow]
  have herr : ∀ n w (B : ℝ), 1 ≤ B → ‖w‖ ≤ B →
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
        (ℓ : PadicAlgCl ℓ) ^ n‖ ≤ a ^ (2 * n) * B ^ d := by
    intro n w B hB hw
    have hrw : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
        (ℓ : PadicAlgCl ℓ) ^ n = ∑ i ∈ Finset.range (d + 1),
          (((PadicInt.appr (c i) (2 * n) : ℕ) : PadicAlgCl ℓ) - ι (c i)) * w ^ i := by
      rw [hFev, hμ0ev]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
      ring
    rw [hrw]
    exact norm_sum_range_le d _ w _ B (pow_nonneg ha0.le _) hB hw fun i _ => happr n i
  -- roots
  have hμmap : μ.map ι ≠ 0 := (hμm.map ι).ne_zero
  have hP1map : P1.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hP1
  have hQ1map : Q1.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hQ1
  have hcardμ : Multiset.card (μ.map ι).roots = d := by
    rw [← (IsAlgClosed.splits (μ.map ι)).natDegree_eq_card_roots, natDegree_map]
  have hμroot : ∀ w ∈ (μ.map ι).roots, (μ.map ι).eval w = 0 := fun w hw =>
    (mem_roots hμmap).mp hw
  have hnotroot : ∀ (R : ℚ_[ℓ][X]), R ≠ 0 → ¬ μ ∣ R → ∀ w ∈ (R.map ι).roots,
      (μ.map ι).eval w ≠ 0 := by
    intro R hR hRμ w hw hμw
    have hRw : aeval w R = 0 := by
      rw [aeval_def, eval₂_eq_eval_map]
      exact (mem_roots ((Polynomial.map_ne_zero_iff ι.injective).mpr hR)).mp hw
    have hμw' : aeval w μ = 0 := by rw [aeval_def, eval₂_eq_eval_map]; exact hμw
    have hmin := minpoly.eq_of_irreducible_of_monic hμ hμw' hμm
    exact hRμ (hmin ▸ minpoly.dvd ℚ_[ℓ] w hRw)
  have hℓs : ι ((ℓ : ℚ_[ℓ]) ^ s) ≠ 0 := by
    rw [map_ne_zero_iff _ ι.injective]
    exact pow_ne_zero _ (by exact_mod_cast hℓ.out.ne_zero)
  have hμ0ne : ∀ (R : ℚ_[ℓ][X]), R ≠ 0 → ¬ μ ∣ R → ∀ w ∈ (R.map ι).roots,
      0 < ‖(μ0.map ι).eval w‖ := by
    intro R hR hRμ w hw
    rw [norm_pos_iff, hμ0μ]
    exact mul_ne_zero hℓs (hnotroot R hR hRμ w hw)
  -- the bound `B`
  set Z : Finset (PadicAlgCl ℓ) :=
    ((μ.map ι).roots + (P1.map ι).roots + (Q1.map ι).roots).toFinset with hZ
  set B : ℝ := 1 + ∑ w ∈ Z, ‖w‖ with hB
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hBw : ∀ w ∈ Z, ‖w‖ ≤ B := fun w hw =>
    (Finset.single_le_sum (f := fun w => ‖w‖) (fun _ _ => norm_nonneg _) hw).trans
      (le_add_of_nonneg_left zero_le_one)
  have hmemZ1 : ∀ w ∈ (μ.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl hw)))
  have hmemZ2 : ∀ w ∈ (P1.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inr hw)))
  have hmemZ3 : ∀ w ∈ (Q1.map ι).roots, w ∈ Z := fun w hw => by
    rw [hZ, Multiset.mem_toFinset]; exact Multiset.mem_add.mpr (Or.inr hw)
  -- eventually
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one ha0.le ha1
  have ev1 : ∀ᶠ n in atTop, a ^ n * B ^ d < 1 := by
    have hBd : 0 < B ^ d := pow_pos (zero_lt_one.trans_le hB1) d
    filter_upwards [hlim.eventually (gt_mem_nhds (inv_pos.mpr hBd))] with n hn
    calc a ^ n * B ^ d < (B ^ d)⁻¹ * B ^ d := mul_lt_mul_of_pos_right hn hBd
      _ = 1 := inv_mul_cancel₀ hBd.ne'
  set S : Finset (PadicAlgCl ℓ) := (P1.map ι).roots.toFinset ∪ (Q1.map ι).roots.toFinset with hS
  have hSpos : ∀ w ∈ S, 0 < ‖(μ0.map ι).eval w‖ := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact hμ0ne P1 hP1 hPμ w (Multiset.mem_toFinset.mp hw)
    · exact hμ0ne Q1 hQ1 hQμ w (Multiset.mem_toFinset.mp hw)
  have ev2 : ∀ᶠ n in atTop, ∀ w ∈ S, a ^ n < ‖(μ0.map ι).eval w‖ := by
    rw [eventually_all_finset]
    intro w hw
    exact hlim.eventually (gt_mem_nhds (hSpos w hw))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ev1.and ev2)
  -- values of `F_n` at the roots
  have hsmall : ∀ n, N ≤ n → ∀ w ∈ Z, ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w -
      (μ0.map ι).eval w - (ℓ : PadicAlgCl ℓ) ^ n‖ < a ^ n := by
    intro n hn w hw
    refine (herr n w B hB1 (hBw w hw)).trans_lt ?_
    have := (hN n hn).1
    calc a ^ (2 * n) * B ^ d = a ^ n * (a ^ n * B ^ d) := by rw [two_mul, pow_add]; ring
      _ < a ^ n * 1 := mul_lt_mul_of_pos_left this (pow_pos ha0 n)
      _ = a ^ n := mul_one _
  have V1 : ∀ n, N ≤ n → ∀ w ∈ (μ.map ι).roots,
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w‖ = a ^ n := by
    intro n hn w hw
    set E := ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
      (ℓ : PadicAlgCl ℓ) ^ n with hE
    have hval : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
        (ℓ : PadicAlgCl ℓ) ^ n + E := by
      rw [hE, hμ0μ, hμroot w hw, mul_zero]; ring
    have hEl := hsmall n hn w (hmemZ1 w hw)
    rw [← hE] at hEl
    rw [hval, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, norm_natCast_prime_pow]
    · exact max_eq_left hEl.le
    · rw [norm_natCast_prime_pow]; exact hEl.ne'
  have V2 : ∀ n, N ≤ n → ∀ w ∈ S,
      ‖((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w‖ = ‖(μ0.map ι).eval w‖ := by
    intro n hn w hw
    have hwZ : w ∈ Z := by
      rcases Finset.mem_union.mp hw with hw | hw
      · exact hmemZ2 w (Multiset.mem_toFinset.mp hw)
      · exact hmemZ3 w (Multiset.mem_toFinset.mp hw)
    set E := ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w - (μ0.map ι).eval w -
      (ℓ : PadicAlgCl ℓ) ^ n with hE
    have hval : ((Fn n).map (Int.castRingHom (PadicAlgCl ℓ))).eval w =
        (μ0.map ι).eval w + ((ℓ : PadicAlgCl ℓ) ^ n + E) := by
      rw [hE]; ring
    have hEl := hsmall n hn w hwZ
    rw [← hE] at hEl
    have hsm : ‖(ℓ : PadicAlgCl ℓ) ^ n + E‖ < ‖(μ0.map ι).eval w‖ := by
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt ?_
      rw [norm_natCast_prime_pow]
      exact max_lt ((hN n hn).2 w hw) (hEl.trans ((hN n hn).2 w hw))
    rw [hval, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hsm.ne', max_eq_left hsm.le]
  -- the norms of the products
  have hRsP : ∀ (R : ℚ_[ℓ][X]) (k : ℕ), R ≠ 0 → ¬ μ ∣ R →
      (∀ w ∈ (R.map ι).roots, w ∈ S) → ∀ n, N ≤ n →
      ‖RsZ (μ ^ k * R) (Fn n)‖ = ((a ^ n) ^ d) ^ k *
        ((R.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod := by
    intro R k hR hRμ hRS n hn
    have hRmap : R.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hR
    unfold RsZ
    rw [Polynomial.map_mul, Polynomial.map_pow, Rs_mul_left (pow_ne_zero _ hμmap) hRmap,
      Rs_pow_left, norm_mul, norm_pow]
    unfold Rs
    rw [norm_multiset_prod_map, norm_multiset_prod_map]
    congr 2
    · rw [Multiset.map_congr rfl (V1 n hn), Multiset.map_const', Multiset.prod_replicate, hcardμ]
    · exact Multiset.map_congr rfl fun w hw => V2 n hn w (hRS w hw)
  have hP1S : ∀ w ∈ (P1.map ι).roots, w ∈ S := fun w hw =>
    Finset.mem_union.mpr (Or.inl (Multiset.mem_toFinset.mpr hw))
  have hQ1S : ∀ w ∈ (Q1.map ι).roots, w ∈ S := fun w hw =>
    Finset.mem_union.mpr (Or.inr (Multiset.mem_toFinset.mpr hw))
  set CP := ((P1.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod with hCP
  set CQ := ((Q1.map ι).roots.map (fun w => ‖(μ0.map ι).eval w‖)).prod with hCQ
  have hCPpos : 0 < CP := Multiset.prod_pos fun x hx => by
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
    exact hμ0ne P1 hP1 hPμ w hw
  have key : ∀ n, N ≤ n → ((a ^ n) ^ d) ^ e * CP ≤ ((a ^ n) ^ d) ^ f * CQ := by
    intro n hn
    have h1 := hRsP P1 e hP1 hPμ hP1S n hn
    have h2 := hRsP Q1 f hQ1 hQμ hQ1S n hn
    rw [← h1, ← h2]
    refine h _ ?_
    rw [← norm_pos_iff, h1]
    exact mul_pos (pow_pos (pow_pos (pow_pos ha0 n) d) e) hCPpos
  by_contra hfe
  push Not at hfe
  have hy0 : 0 < (a ^ d) ^ (f - e) := pow_pos (pow_pos ha0 d) _
  have hy1 : (a ^ d) ^ (f - e) < 1 :=
    pow_lt_one₀ (pow_pos ha0 d).le (pow_lt_one₀ ha0.le ha1 hd.ne') (by omega)
  have hlim2 := tendsto_pow_atTop_nhds_zero_of_lt_one hy0.le hy1
  have hCQ0 : 0 ≤ CQ := Multiset.prod_nonneg fun x hx => by
    obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hx
    exact norm_nonneg _
  have ev3 : ∀ᶠ n in atTop, ((a ^ d) ^ (f - e)) ^ n * CQ < CP := by
    have : Tendsto (fun n => ((a ^ d) ^ (f - e)) ^ n * CQ) atTop (𝓝 (0 * CQ)) := hlim2.mul_const CQ
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds hCPpos)
  obtain ⟨n, hn1, hn2⟩ := (ev3.and (eventually_ge_atTop N)).exists
  have k := key n hn2
  have hxe : 0 < ((a ^ n) ^ d) ^ e := pow_pos (pow_pos (pow_pos ha0 n) d) e
  have hsplit : ((a ^ n) ^ d) ^ f = ((a ^ n) ^ d) ^ e * ((a ^ d) ^ (f - e)) ^ n := by
    have hf : f = e + (f - e) := by omega
    calc ((a ^ n) ^ d) ^ f = ((a ^ n) ^ d) ^ (e + (f - e)) := by rw [← hf]
      _ = ((a ^ n) ^ d) ^ e * ((a ^ n) ^ d) ^ (f - e) := pow_add _ _ _
      _ = ((a ^ n) ^ d) ^ e * ((a ^ d) ^ (f - e)) ^ n := by ring
  rw [hsplit, mul_assoc] at k
  have := le_of_mul_le_mul_left k hxe
  linarith

/-- **Comparison lemma** (Mumford §19, the lemma in the proof of Thm 4; here over `ℚ_ℓ`): two monic
polynomials over `ℚ_ℓ` with `|∏_{P(a)=0} F(a)|_ℓ = |∏_{Q(b)=0} F(b)|_ℓ` for every `F ∈ ℤ[X]` with nonzero
left side are equal. -/
theorem eq_of_norm_RsZ {P Q : ℚ_[ℓ][X]} (hP : P.Monic) (hQ : Q.Monic)
    (h : ∀ F : ℤ[X], RsZ P F ≠ 0 → ‖RsZ P F‖ = ‖RsZ Q F‖) : P = Q := by
  classical
  have hP0 := hP.ne_zero
  have hQ0 := hQ.ne_zero
  have hcount : ∀ μ : ℚ_[ℓ][X], Irreducible μ → μ.Monic →
      (UniqueFactorizationMonoid.normalizedFactors P).count μ =
        (UniqueFactorizationMonoid.normalizedFactors Q).count μ := by
    intro μ hμ hμm
    obtain ⟨e, P1, hP1μ, hPe⟩ := WfDvdMonoid.max_power_factor hP0 hμ
    obtain ⟨f, Q1, hQ1μ, hQf⟩ := WfDvdMonoid.max_power_factor hQ0 hμ
    have hP1 : P1 ≠ 0 := by rintro rfl; rw [mul_zero] at hPe; exact hP0 hPe
    have hQ1 : Q1 ≠ 0 := by rintro rfl; rw [mul_zero] at hQf; exact hQ0 hQf
    have hef : e = f := mult_eq_of_norm_Rs hμ hμm hP1 hQ1 hP1μ hQ1μ e f (by
      rw [← hPe, ← hQf]; exact h)
    have hnd : ∀ (k : ℕ) (R : ℚ_[ℓ][X]), ¬ μ ∣ R → ¬ μ ^ (k + 1) ∣ μ ^ k * R := by
      intro k R hR hdvd
      rw [pow_succ] at hdvd
      exact hR ((mul_dvd_mul_iff_left (pow_ne_zero k hμ.ne_zero)).mp hdvd)
    rw [UniqueFactorizationMonoid.count_normalizedFactors_eq hμ hμm.normalize_eq_self
        ⟨P1, hPe⟩ (hPe ▸ hnd e P1 hP1μ),
      UniqueFactorizationMonoid.count_normalizedFactors_eq hμ hμm.normalize_eq_self
        ⟨Q1, hQf⟩ (hQf ▸ hnd f Q1 hQ1μ), hef]
  have hnf : UniqueFactorizationMonoid.normalizedFactors P =
      UniqueFactorizationMonoid.normalizedFactors Q := by
    ext μ
    by_cases hμ : μ ∈ UniqueFactorizationMonoid.normalizedFactors P ∨
        μ ∈ UniqueFactorizationMonoid.normalizedFactors Q
    · have hirr : Irreducible μ := by
        rcases hμ with hμ | hμ <;>
          exact UniqueFactorizationMonoid.irreducible_of_normalized_factor μ hμ
      have hnorm : normalize μ = μ := by
        rcases hμ with hμ | hμ <;>
          exact UniqueFactorizationMonoid.normalize_normalized_factor μ hμ
      have hmon : μ.Monic := by
        rw [← hnorm]; exact Polynomial.monic_normalize hirr.ne_zero
      exact hcount μ hirr hmon
    · push Not at hμ
      rw [Multiset.count_eq_zero.mpr hμ.1, Multiset.count_eq_zero.mpr hμ.2]
  have hPa := UniqueFactorizationMonoid.prod_normalizedFactors hP0
  have hQa := UniqueFactorizationMonoid.prod_normalizedFactors hQ0
  rw [hnf] at hPa
  exact eq_of_monic_of_associated hP hQ (hPa.symm.trans hQa)

/-- **One-sided comparison lemma.** Monic `P, Q` over `ℚ_ℓ` of the same degree with
`|∏_{P(a)=0} F(a)|_ℓ ≤ |∏_{Q(b)=0} F(b)|_ℓ` for every `F ∈ ℤ[X]` with nonzero left side are equal. -/
theorem eq_of_norm_RsZ_le {P Q : ℚ_[ℓ][X]} (hP : P.Monic) (hQ : Q.Monic)
    (hdeg : P.natDegree = Q.natDegree)
    (h : ∀ F : ℤ[X], RsZ P F ≠ 0 → ‖RsZ P F‖ ≤ ‖RsZ Q F‖) : P = Q := by
  classical
  have hP0 := hP.ne_zero
  have hQ0 := hQ.ne_zero
  have hcount : ∀ μ : ℚ_[ℓ][X], Irreducible μ → μ.Monic →
      (UniqueFactorizationMonoid.normalizedFactors Q).count μ ≤
        (UniqueFactorizationMonoid.normalizedFactors P).count μ := by
    intro μ hμ hμm
    obtain ⟨e, P1, hP1μ, hPe⟩ := WfDvdMonoid.max_power_factor hP0 hμ
    obtain ⟨f, Q1, hQ1μ, hQf⟩ := WfDvdMonoid.max_power_factor hQ0 hμ
    have hP1 : P1 ≠ 0 := by rintro rfl; rw [mul_zero] at hPe; exact hP0 hPe
    have hQ1 : Q1 ≠ 0 := by rintro rfl; rw [mul_zero] at hQf; exact hQ0 hQf
    have hfe : f ≤ e := mult_le_of_norm_Rs_le hμ hμm hP1 hQ1 hP1μ hQ1μ e f (by
      rw [← hPe, ← hQf]; exact h)
    have hnd : ∀ (k : ℕ) (R : ℚ_[ℓ][X]), ¬ μ ∣ R → ¬ μ ^ (k + 1) ∣ μ ^ k * R := by
      intro k R hR hdvd
      rw [pow_succ] at hdvd
      exact hR ((mul_dvd_mul_iff_left (pow_ne_zero k hμ.ne_zero)).mp hdvd)
    rw [UniqueFactorizationMonoid.count_normalizedFactors_eq hμ hμm.normalize_eq_self
        ⟨P1, hPe⟩ (hPe ▸ hnd e P1 hP1μ),
      UniqueFactorizationMonoid.count_normalizedFactors_eq hμ hμm.normalize_eq_self
        ⟨Q1, hQf⟩ (hQf ▸ hnd f Q1 hQ1μ)]
    exact hfe
  have hle : UniqueFactorizationMonoid.normalizedFactors Q ≤
      UniqueFactorizationMonoid.normalizedFactors P := by
    rw [Multiset.le_iff_count]
    intro μ
    by_cases hμ : μ ∈ UniqueFactorizationMonoid.normalizedFactors Q
    · have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor μ hμ
      have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor μ hμ
      have hmon : μ.Monic := by rw [← hnorm]; exact Polynomial.monic_normalize hirr.ne_zero
      exact hcount μ hirr hmon
    · rw [Multiset.count_eq_zero.mpr hμ]; exact Nat.zero_le _
  have hdvd : Q ∣ P := by
    rw [← (UniqueFactorizationMonoid.prod_normalizedFactors hQ0).dvd_iff_dvd_left,
      ← (UniqueFactorizationMonoid.prod_normalizedFactors hP0).dvd_iff_dvd_right]
    exact Multiset.prod_dvd_prod_of_le hle
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hP0 hc
  have hcm : c.Monic := by
    have := hP
    rw [hc] at this
    exact hQ.of_mul_monic_left this
  have hcd : c.natDegree = 0 := by
    have := congrArg natDegree hc
    rw [hQ.natDegree_mul hcm, ← hdeg] at this
    omega
  rw [hc, hcm.natDegree_eq_zero.mp hcd, mul_one]

end Compare

/-! ## 4. A polynomial function on `ℤ[φ]`, extended to `S[X]/(R)` -/

section PolyFn

variable {R : ℤ[X]} (N : MvPolynomial (Fin R.natDegree) ℚ)

variable (R) in
/-- The polynomial function `N` read on `S[X]/(R)` in the basis `1, X, …, X^{d-1}`. -/
def Nt (S : Type*) [CommRing S] [Algebra ℚ S] (F : S[X]) : S :=
  MvPolynomial.aeval (fun i : Fin R.natDegree => (F %ₘ R.map (Int.castRingHom S)).coeff i) N

theorem map_intCast_comp {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S') :
    (R.map (Int.castRingHom S)).map f = R.map (Int.castRingHom S') := by
  rw [Polynomial.map_map, RingHom.ext_int (f.comp (Int.castRingHom S)) (Int.castRingHom S')]

theorem Nt_map (hR : R.Monic) {S S' : Type*} [CommRing S] [Algebra ℚ S] [CommRing S']
    [Algebra ℚ S'] (f : S →ₐ[ℚ] S') (F : S[X]) :
    Nt R N S' (F.map (f : S →+* S')) = f (Nt R N S F) := by
  unfold Nt
  rw [← map_intCast_comp (f : S →+* S'), ← map_modByMonic _ (hR.map _),
    MvPolynomial.comp_aeval_apply]
  simp_rw [coeff_map]
  rfl

theorem Nt_modByMonic (S : Type*) [CommRing S] [Algebra ℚ S] (hR : R.Monic) (F : S[X]) :
    Nt R N S (F %ₘ R.map (Int.castRingHom S)) = Nt R N S F := by
  unfold Nt
  rw [modByMonic_eq_of_dvd_sub (hR.map _) (dvd_modByMonic_sub _ _)]

/-- A remainder mod `R` is the sum of its first `d` monomials. -/
theorem modByMonic_eq_sum (hR : R.Monic) (S : Type*) [CommRing S] [Nontrivial S] (F : S[X]) :
    F %ₘ R.map (Int.castRingHom S) = ∑ i : Fin R.natDegree,
      C ((F %ₘ R.map (Int.castRingHom S)).coeff i) * X ^ (i : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => C ((F %ₘ R.map (Int.castRingHom S)).coeff i) * X ^ i)]
  by_cases hd : R.natDegree = 0
  · have h1 : R = 1 := hR.natDegree_eq_zero.mp hd
    simp [h1]
  · have hne : R.map (Int.castRingHom S) ≠ 1 := by
      intro h
      apply hd
      have := congrArg natDegree h
      rwa [hR.natDegree_map, natDegree_one] at this
    conv_lhs => rw [as_sum_range' (F %ₘ R.map (Int.castRingHom S)) R.natDegree (by
      have := natDegree_modByMonic_lt F (hR.map (Int.castRingHom S)) hne
      rwa [hR.natDegree_map] at this)]
    simp_rw [C_mul_X_pow_eq_monomial]

/-- Homogeneous polynomials scale by `c^n`. -/
theorem aeval_mul_of_isHomogeneous {σ S : Type*} [CommRing S] [Algebra ℚ S]
    {M : MvPolynomial σ ℚ} {n : ℕ} (hM : M.IsHomogeneous n) (c : S) (x : σ → S) :
    MvPolynomial.aeval (fun i => c * x i) M = c ^ n * MvPolynomial.aeval x M := by
  conv_lhs => rw [M.as_sum]
  conv_rhs => rw [M.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  have hdeg := hM.degree_eq_sum_deg_support hv
  have : (v.prod fun i k => (c * x i) ^ k) = c ^ n * v.prod fun i k => x i ^ k := by
    simp_rw [mul_pow]
    rw [Finsupp.prod_mul]
    congr 1
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, ← hdeg]
  rw [this]
  ring

theorem Nt_C_mul {n : ℕ} (hN : N.IsHomogeneous n) (S : Type*) [CommRing S]
    [Algebra ℚ S] (c : S) (F : S[X]) : Nt R N S (C c * F) = c ^ n * Nt R N S F := by
  unfold Nt
  rw [← smul_eq_C_mul, smul_modByMonic]
  simp_rw [coeff_smul, smul_eq_mul]
  exact aeval_mul_of_isHomogeneous hN c _

/-- `NtZ F = N(coefficients of F mod R)` for `F ∈ ℤ[X]`. -/
abbrev NtZ (F : ℤ[X]) : ℚ := Nt R N ℚ (F.map (Int.castRingHom ℚ))

/-- **Generic multiplicativity.** If `N` read on `ℤ[X]/(R)` is multiplicative on pairs with nonzero
values and `N(1) = 1`, then `N` read on `S[X]/(R)` is multiplicative, for every `ℚ`-algebra `S`. -/
theorem Nt_mul (hR : R.Monic) (h1 : NtZ N 1 = 1)
    (hmulZ : ∀ F G : ℤ[X], NtZ N F ≠ 0 → NtZ N G ≠ 0 → NtZ N (F * G) = NtZ N F * NtZ N G)
    (S : Type*) [CommRing S] [Nontrivial S] [Algebra ℚ S] (F G : S[X]) :
    Nt R N S (F * G) = Nt R N S F * Nt R N S G := by
  classical
  let σ := Fin R.natDegree ⊕ Fin R.natDegree
  let Fg : (MvPolynomial σ ℚ)[X] := ∑ i : Fin R.natDegree, C (MvPolynomial.X (Sum.inl i)) * X ^ (i : ℕ)
  let Gg : (MvPolynomial σ ℚ)[X] := ∑ i : Fin R.natDegree, C (MvPolynomial.X (Sum.inr i)) * X ^ (i : ℕ)
  have hmapF : ∀ (T : Type) [CommRing T] [Algebra ℚ T] (x : σ → T),
      Fg.map (MvPolynomial.aeval x : MvPolynomial σ ℚ →ₐ[ℚ] T).toRingHom =
        ∑ i : Fin R.natDegree, C (x (Sum.inl i)) * X ^ (i : ℕ) := by
    intro T _ _ x
    simp [Fg, Polynomial.map_sum]
  have hmapG : ∀ (T : Type) [CommRing T] [Algebra ℚ T] (x : σ → T),
      Gg.map (MvPolynomial.aeval x : MvPolynomial σ ℚ →ₐ[ℚ] T).toRingHom =
        ∑ i : Fin R.natDegree, C (x (Sum.inr i)) * X ^ (i : ℕ) := by
    intro T _ _ x
    simp [Gg, Polynomial.map_sum]
  set S2 := MvPolynomial σ ℚ
  set a := Nt R N S2 Fg
  set b := Nt R N S2 Gg
  set ab := Nt R N S2 (Fg * Gg)
  -- evaluation at a point of `ℚ^σ`
  have hev : ∀ x : σ → ℚ, ∀ H : S2[X],
      MvPolynomial.eval x (Nt R N S2 H) =
        Nt R N ℚ (H.map (MvPolynomial.aeval x : S2 →ₐ[ℚ] ℚ).toRingHom) := by
    intro x H
    rw [← MvPolynomial.coe_aeval_eq_eval]
    exact (Nt_map N hR (MvPolynomial.aeval x : S2 →ₐ[ℚ] ℚ) H).symm
  -- the polynomial `(ab - a b) a b` vanishes on `ℕ^σ`
  have hint : ∀ y : σ → ℕ, MvPolynomial.eval (fun i => (y i : ℚ)) ((ab - a * b) * (a * b)) = 0 := by
    intro y
    set Fy : ℤ[X] := ∑ i : Fin R.natDegree, C ((y (Sum.inl i) : ℕ) : ℤ) * X ^ (i : ℕ)
    set Gy : ℤ[X] := ∑ i : Fin R.natDegree, C ((y (Sum.inr i) : ℕ) : ℤ) * X ^ (i : ℕ)
    have hF : Fg.map (MvPolynomial.aeval (fun i => (y i : ℚ)) : S2 →ₐ[ℚ] ℚ).toRingHom =
        Fy.map (Int.castRingHom ℚ) := by
      rw [hmapF]; simp [Fy, Polynomial.map_sum]
    have hG : Gg.map (MvPolynomial.aeval (fun i => (y i : ℚ)) : S2 →ₐ[ℚ] ℚ).toRingHom =
        Gy.map (Int.castRingHom ℚ) := by
      rw [hmapG]; simp [Gy, Polynomial.map_sum]
    simp only [map_mul, map_sub]
    rw [hev, hev, hev, Polynomial.map_mul, hF, hG, ← Polynomial.map_mul]
    change (NtZ N (Fy * Gy) - NtZ N Fy * NtZ N Gy) * (NtZ N Fy * NtZ N Gy) = 0
    by_cases hFy : NtZ N Fy = 0
    · rw [hFy]; ring
    by_cases hGy : NtZ N Gy = 0
    · rw [hGy]; ring
    rw [hmulZ Fy Gy hFy hGy, sub_self, zero_mul]
  have hK : (ab - a * b) * (a * b) = 0 := by
    set K := (ab - a * b) * (a * b)
    refine MvPolynomial.eq_zero_of_eval_zero_at_prod_finset K
      (fun i => (Finset.range (K.degreeOf i + 1)).image (fun k : ℕ => (k : ℚ))) (fun i => ?_) ?_
    · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
      exact Nat.lt_succ_self _
    · intro x hx
      choose y _ hy using fun i => Finset.mem_image.mp (hx i)
      have : x = fun i => (y i : ℚ) := funext fun i => (hy i).symm
      rw [this]
      exact hint y
  -- `a, b ≠ 0`: evaluate at the coefficients of `1 mod R`
  set u : Fin R.natDegree → ℚ := fun i => (((1 : ℤ[X]) %ₘ R).coeff i : ℚ)
  have hone : ∑ i : Fin R.natDegree, C (u i) * X ^ (i : ℕ) = (1 : ℚ[X]) %ₘ R.map (Int.castRingHom ℚ) := by
    rw [modByMonic_eq_sum hR ℚ 1]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    have := map_modByMonic (Int.castRingHom ℚ) (p := (1 : ℤ[X])) hR
    rw [Polynomial.map_one] at this
    rw [← this, coeff_map]
    rfl
  have hNt1 : Nt R N ℚ ((1 : ℚ[X]) %ₘ R.map (Int.castRingHom ℚ)) = 1 := by
    rw [Nt_modByMonic N ℚ hR, ← h1, NtZ, Polynomial.map_one]
  have ha : a ≠ 0 := by
    intro ha0
    have := hev (Sum.elim u u) Fg
    rw [hmapF] at this
    simp only [Sum.elim_inl] at this
    rw [hone, hNt1] at this
    have h2 : MvPolynomial.eval (Sum.elim u u) a = 1 := this
    rw [ha0, map_zero] at h2
    exact zero_ne_one h2
  have hb : b ≠ 0 := by
    intro hb0
    have := hev (Sum.elim u u) Gg
    rw [hmapG] at this
    simp only [Sum.elim_inr] at this
    rw [hone, hNt1] at this
    have h2 : MvPolynomial.eval (Sum.elim u u) b = 1 := this
    rw [hb0, map_zero] at h2
    exact zero_ne_one h2
  have hab : ab = a * b := by
    rcases mul_eq_zero.mp hK with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (mul_ne_zero ha hb)
  -- specialize at the coefficients of `F, G mod R`
  set R' := R.map (Int.castRingHom S)
  set x : σ → S := Sum.elim (fun i => (F %ₘ R').coeff i) (fun i => (G %ₘ R').coeff i)
  set f : S2 →ₐ[ℚ] S := MvPolynomial.aeval x
  have hFx : Fg.map f.toRingHom = F %ₘ R' := by
    rw [modByMonic_eq_sum hR S F]; simp [Fg, f, x, Polynomial.map_sum, R']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.aeval_X]
    rfl
  have hGx : Gg.map f.toRingHom = G %ₘ R' := by
    rw [modByMonic_eq_sum hR S G]; simp [Gg, f, x, Polynomial.map_sum, R']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPolynomial.aeval_X]
    rfl
  rw [← Nt_modByMonic N S hR (F * G), mul_modByMonic, Nt_modByMonic N S hR,
    ← Nt_modByMonic N S hR F, ← Nt_modByMonic N S hR G, ← hFx, ← hGx, ← Polynomial.map_mul]
  change Nt R N S ((Fg * Gg).map (f : S2 →+* S)) = Nt R N S (Fg.map (f : S2 →+* S)) *
    Nt R N S (Gg.map (f : S2 →+* S))
  rw [Nt_map N hR, Nt_map N hR, Nt_map N hR]
  change f ab = f a * f b
  rw [hab, map_mul]

/-- Degree and top coefficient of a product of powers of linear polynomials. -/
theorem prod_lin_pow {σ : Type*} (L : σ → ℚ[X]) (u : σ → ℚ) (hL : ∀ i, (L i).natDegree ≤ 1)
    (hLu : ∀ i, (L i).coeff 1 = u i) (k : σ → ℕ) (s : Finset σ) :
    (∏ i ∈ s, L i ^ k i).natDegree ≤ ∑ i ∈ s, k i ∧
      (∏ i ∈ s, L i ^ k i).coeff (∑ i ∈ s, k i) = ∏ i ∈ s, u i ^ k i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have hpa : (L a ^ k a).natDegree ≤ k a := by
      have := natDegree_pow_le_of_le (k a) (hL a)
      rwa [mul_one] at this
    refine ⟨(natDegree_mul_le).trans (add_le_add hpa ih.1), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le hpa ih.1, ih.2]
    congr 1
    have := coeff_pow_of_natDegree_le (m := k a) (hL a)
    rw [mul_one] at this
    rw [this, hLu]

/-- `N(u X - v)` is monic of degree `n` for `N` homogeneous of degree `n` with `N(u) = 1`. -/
theorem monic_aeval_lin {σ : Type*} {M : MvPolynomial σ ℚ} {n : ℕ} (hM : M.IsHomogeneous n)
    (u v : σ → ℚ) (hu : MvPolynomial.eval u M = 1) :
    (MvPolynomial.aeval (fun i => C (u i) * X - C (v i)) M).Monic ∧
      (MvPolynomial.aeval (fun i => C (u i) * X - C (v i)) M).natDegree = n := by
  classical
  set L : σ → ℚ[X] := fun i => C (u i) * X - C (v i) with hLdef
  have hL : ∀ i, (L i).natDegree ≤ 1 := fun i => by
    rw [hLdef]; exact (natDegree_sub_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans natDegree_X_le) (by simp))
  have hLu : ∀ i, (L i).coeff 1 = u i := fun i => by simp [hLdef]
  have hexp : MvPolynomial.aeval L M = ∑ d ∈ M.support, C (M.coeff d) * ∏ i ∈ d.support, L i ^ d i := by
    conv_lhs => rw [M.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_eq, Finsupp.prod]
  have hterm : ∀ d ∈ M.support, (C (M.coeff d) * ∏ i ∈ d.support, L i ^ d i).natDegree ≤ n ∧
      (C (M.coeff d) * ∏ i ∈ d.support, L i ^ d i).coeff n =
        M.coeff d * ∏ i ∈ d.support, u i ^ d i := by
    intro d hd
    have hdeg := hM.degree_eq_sum_deg_support hd
    obtain ⟨h1, h2⟩ := prod_lin_pow L u hL hLu d d.support
    rw [← hdeg] at h1 h2
    exact ⟨(natDegree_C_mul_le _ _).trans h1, by rw [coeff_C_mul, h2]⟩
  have hdeg : (MvPolynomial.aeval L M).natDegree ≤ n := by
    rw [hexp]; exact natDegree_sum_le_of_forall_le _ _ fun d hd => (hterm d hd).1
  have hcoeff : (MvPolynomial.aeval L M).coeff n = 1 := by
    rw [hexp, finsetSum_coeff, ← hu, MvPolynomial.eval_eq]
    exact Finset.sum_congr rfl fun d hd => (hterm d hd).2
  have hnd : (MvPolynomial.aeval L M).natDegree = n :=
    natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hcoeff]; exact one_ne_zero)
  exact ⟨by rw [Monic, leadingCoeff, hnd, hcoeff], hnd⟩

/-- The characteristic polynomial of `N` along `t - X`: `P₀(t) = N(t - X)`. -/
def P0 : ℚ[X] := Nt R N ℚ[X] (C X - X)

theorem Nt_C_sub_X (hR : R.Monic) (S : Type*) [CommRing S] [Algebra ℚ S] (t : S) :
    Nt R N S (C t - X) = ((P0 N).map (algebraMap ℚ S)).eval t := by
  have h := Nt_map N hR (Polynomial.aeval t : ℚ[X] →ₐ[ℚ] S) (C X - X)
  rw [Polynomial.map_sub, map_C, map_X] at h
  simp only [AlgHom.coe_toRingHom, aeval_X] at h
  rw [h, P0, aeval_def, eval₂_eq_eval_map]

theorem P0_monic (hR : R.Monic) {n : ℕ} (hN : N.IsHomogeneous n) (h1 : NtZ N 1 = 1) :
    (P0 N).Monic ∧ (P0 N).natDegree = n := by
  set u : Fin R.natDegree → ℚ := fun i => (((1 : ℤ[X]) %ₘ R).coeff i : ℚ)
  set v : Fin R.natDegree → ℚ := fun i => (((X : ℤ[X]) %ₘ R).coeff i : ℚ)
  have hu : MvPolynomial.eval u N = 1 := by
    rw [← h1, NtZ, Nt, Polynomial.map_one, ← MvPolynomial.coe_aeval_eq_eval]
    refine congrArg (fun x => MvPolynomial.aeval x N) (funext fun i => ?_)
    have := map_modByMonic (Int.castRingHom ℚ) (p := (1 : ℤ[X])) hR
    rw [Polynomial.map_one] at this
    rw [← this, coeff_map]
    rfl
  have hcoord : ∀ i : Fin R.natDegree,
      ((C X - X : ℚ[X][X]) %ₘ R.map (Int.castRingHom ℚ[X])).coeff i = C (u i) * X - C (v i) := by
    intro i
    have h1' := map_modByMonic (Int.castRingHom ℚ[X]) (p := (1 : ℤ[X])) hR
    have hX' := map_modByMonic (Int.castRingHom ℚ[X]) (p := (X : ℤ[X])) hR
    rw [Polynomial.map_one] at h1'
    rw [map_X] at hX'
    rw [sub_modByMonic, ← mul_one (C X : ℚ[X][X]), ← smul_eq_C_mul, smul_modByMonic, ← h1', ← hX',
      coeff_sub, coeff_smul, coeff_map, coeff_map, smul_eq_mul, mul_comm]
    simp [u, v]
  have := monic_aeval_lin hN u v hu
  unfold P0 Nt
  simp_rw [hcoord]
  exact this

end PolyFn

/-! ## 5. Mumford's theorem, abstract form -/

section Main

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem algebraMap_rat_comp (L : Type*) [Field L] [CharZero L] [Algebra ℚ_[ℓ] L] :
    (algebraMap ℚ_[ℓ] L).comp (algebraMap ℚ ℚ_[ℓ]) = algebraMap ℚ L :=
  RingHom.ext_rat _ _

/-- **Mumford's theorem `deg φ = det T_ℓ(φ)`, abstract form.** Let `E` be a ring, `deg : E → ℕ`, `φ ∈ E`
integral over `ℤ` (`R(φ) = 0`, `R` monic). Assume

* `deg` is a homogeneous polynomial function of degree `n` on `ℤ[φ]` (in the coordinates
  `x ↦ ∑ xᵢ φ^i`, `i < deg R`),
* `deg 1 = 1` and `deg(ψχ) = deg ψ · deg χ` when both are nonzero,
* `ρ : E → M_I(ℚ_ℓ)` is a ring homomorphism with `|det ρ(ψ)|_ℓ = |deg ψ|_ℓ` whenever `deg ψ ≠ 0`.

Then `det ρ(φ) = deg φ`. -/
theorem det_eq_deg_abstract {E : Type*} [Ring E] (φ : E) (deg : E → ℕ)
    (R : ℤ[X]) (hR : R.Monic) (hRφ : aeval φ R = 0)
    (n : ℕ) (N : MvPolynomial (Fin R.natDegree) ℚ) (hN : N.IsHomogeneous n)
    (hpoly : ∀ x : Fin R.natDegree → ℤ,
      (deg (∑ i, x i • φ ^ (i : ℕ)) : ℚ) = MvPolynomial.eval (fun i => (x i : ℚ)) N)
    (hdeg1 : deg 1 = 1)
    (hmul : ∀ ψ χ : E, deg ψ ≠ 0 → deg χ ≠ 0 → deg (ψ * χ) = deg ψ * deg χ)
    {I : Type*} [Fintype I] [DecidableEq I] (ρ : E →+* Matrix I I ℚ_[ℓ])
    (hlink : ∀ ψ : E, deg ψ ≠ 0 → ‖(ρ ψ).det‖ = ‖(deg ψ : ℚ_[ℓ])‖) :
    (ρ φ).det = (deg φ : ℚ_[ℓ]) := by
  classical
  set W := PadicAlgCl ℓ
  set ι := algebraMap ℚ_[ℓ] W with hι
  -- `deg` on `ℤ[X]`
  set D : ℤ[X] → ℕ := fun F => deg (aeval φ F) with hD
  have hRid : R.map (Int.castRingHom ℤ) = R := by
    rw [show Int.castRingHom ℤ = RingHom.id ℤ from RingHom.ext_int _ _, Polynomial.map_id]
  have hDN : ∀ F : ℤ[X], (D F : ℚ) = NtZ N F := by
    intro F
    have h1 : aeval φ F = ∑ i : Fin R.natDegree, ((F %ₘ R).coeff i) • φ ^ (i : ℕ) := by
      rw [← aeval_modByMonic_eq_self_of_root hRφ]
      have := modByMonic_eq_sum hR ℤ F
      rw [hRid] at this
      conv_lhs => rw [this]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul]
    rw [hD]
    simp only
    rw [h1, hpoly, NtZ, Nt, ← map_modByMonic _ hR, ← MvPolynomial.coe_aeval_eq_eval]
    simp_rw [coeff_map]
    rfl
  have h1 : NtZ N 1 = 1 := by
    rw [← hDN, hD]; simp [hdeg1]
  have hmulZ : ∀ F G : ℤ[X], NtZ N F ≠ 0 → NtZ N G ≠ 0 → NtZ N (F * G) = NtZ N F * NtZ N G := by
    intro F G hF hG
    rw [← hDN] at hF hG
    rw [← hDN, ← hDN, ← hDN, hD]
    simp only [map_mul]
    rw [hmul _ _ (by exact_mod_cast hF) (by exact_mod_cast hG), Nat.cast_mul]
  -- the extension to `W[X]`
  have hNtW : ∀ F : ℤ[X], Nt R N W (F.map (Int.castRingHom W)) = (D F : W) := by
    intro F
    have := Nt_map N hR (Algebra.ofId ℚ W) (F.map (Int.castRingHom ℚ))
    rw [Polynomial.map_map] at this
    rw [show (Int.castRingHom W) = ((Algebra.ofId ℚ W : ℚ →ₐ[ℚ] W) : ℚ →+* W).comp
      (Int.castRingHom ℚ) from RingHom.ext_int _ _, this]
    change algebraMap ℚ W (NtZ N F) = _
    rw [← hDN, map_natCast]
  have hNt1 : Nt R N W 1 = 1 := by
    have := hNtW 1
    rw [Polynomial.map_one] at this
    rw [this, hD]; simp [hdeg1]
  let φW : W[X] →* W :=
    { toFun := Nt R N W
      map_one' := hNt1
      map_mul' := Nt_mul N hR h1 hmulZ W }
  set P := (P0 N).map (algebraMap ℚ W) with hP
  obtain ⟨hP0m, hP0d⟩ := P0_monic N hR hN h1
  have hPm : P.Monic := hP0m.map _
  have hPd : P.natDegree = n := by rw [hP, natDegree_map, hP0d]
  have hφW : ∀ F : W[X], Nt R N W F = Rs P F := by
    refine eq_Rs_of_mul φW n P hPm hPd ?_ ?_
    · intro c
      change Nt R N W (C c) = c ^ n
      rw [← mul_one (C c), Nt_C_mul N hN, hNt1, mul_one]
    · intro r
      change Nt R N W (X - C r) = _
      rw [show (X - C r : W[X]) = C (-1) * (C r - X) by rw [C_neg, C_1]; ring, Nt_C_mul N hN,
        Nt_C_sub_X N hR]
  -- the two polynomials over `ℚ_ℓ`
  set Pℓ := (P0 N).map (algebraMap ℚ ℚ_[ℓ]) with hPℓ
  have hPℓm : Pℓ.Monic := hP0m.map _
  have hPPℓ : Pℓ.map ι = P := by
    rw [hPℓ, Polynomial.map_map, hι, algebraMap_rat_comp]
  set M := ρ φ with hM
  set Q := M.charpoly with hQ
  have hRsP : ∀ F : ℤ[X], RsZ Pℓ F = (D F : W) := by
    intro F
    unfold RsZ
    rw [← hι, hPPℓ, ← hφW, hNtW]
  have hRsQ : ∀ F : ℤ[X], RsZ Q F = ι ((ρ (aeval φ F)).det) := by
    intro F
    unfold RsZ
    rw [← hι, hQ, ← Matrix.charpoly_map, ← det_aeval_eq_Rs]
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
    have e1 : aeval (M.map ι) F = (ι.mapMatrix (aeval M F)) := by
      have := Polynomial.aeval_algHom_apply (ι.mapMatrix.toIntAlgHom : Matrix I I ℚ_[ℓ] →ₐ[ℤ] _) M F
      exact this
    have e2 : aeval M F = ρ (aeval φ F) := by
      rw [hM]
      exact Polynomial.aeval_algHom_apply (ρ.toIntAlgHom) φ F
    rw [e1, e2, RingHom.map_det]
  have hPQ : Pℓ = Q := by
    refine eq_of_norm_RsZ hPℓm (Matrix.charpoly_monic M) fun F hF => ?_
    rw [hRsP] at hF ⊢
    rw [hRsQ]
    have hDF : D F ≠ 0 := by
      intro h0; apply hF; rw [h0, Nat.cast_zero]
    have := hlink (aeval φ F) hDF
    rw [hι, PadicAlgCl.norm_extends ℓ, this, ← map_natCast ι, hι, PadicAlgCl.norm_extends ℓ]
  have hfin := hRsQ X
  rw [← hPQ, hRsP] at hfin
  simp only [hD, aeval_X] at hfin
  have : ι ((deg φ : ℕ) : ℚ_[ℓ]) = ι (ρ φ).det := by
    rw [map_natCast]
    exact hfin
  exact (ι.injective this).symm

/-- **One-sided variant of `det_eq_deg_abstract`**: `|deg ψ|_ℓ ≤ |det ρ(ψ)|_ℓ` and `#I = n` suffice. Let `E` be a ring, `deg : E → ℕ`, `φ ∈ E`
integral over `ℤ` (`R(φ) = 0`, `R` monic). Assume

* `deg` is a homogeneous polynomial function of degree `n` on `ℤ[φ]` (in the coordinates
  `x ↦ ∑ xᵢ φ^i`, `i < deg R`),
* `deg 1 = 1` and `deg(ψχ) = deg ψ · deg χ` when both are nonzero,
* `ρ : E → M_I(ℚ_ℓ)` is a ring homomorphism with `|det ρ(ψ)|_ℓ = |deg ψ|_ℓ` whenever `deg ψ ≠ 0`.

Then `det ρ(φ) = deg φ`. -/
theorem det_eq_deg_abstract_le {E : Type*} [Ring E] (φ : E) (deg : E → ℕ)
    (R : ℤ[X]) (hR : R.Monic) (hRφ : aeval φ R = 0)
    (n : ℕ) (N : MvPolynomial (Fin R.natDegree) ℚ) (hN : N.IsHomogeneous n)
    (hpoly : ∀ x : Fin R.natDegree → ℤ,
      (deg (∑ i, x i • φ ^ (i : ℕ)) : ℚ) = MvPolynomial.eval (fun i => (x i : ℚ)) N)
    (hdeg1 : deg 1 = 1)
    (hmul : ∀ ψ χ : E, deg ψ ≠ 0 → deg χ ≠ 0 → deg (ψ * χ) = deg ψ * deg χ)
    {I : Type*} [Fintype I] [DecidableEq I] (ρ : E →+* Matrix I I ℚ_[ℓ])
    (hI : Fintype.card I = n)
    (hlink : ∀ ψ : E, deg ψ ≠ 0 → ‖(deg ψ : ℚ_[ℓ])‖ ≤ ‖(ρ ψ).det‖) :
    (ρ φ).det = (deg φ : ℚ_[ℓ]) := by
  classical
  set W := PadicAlgCl ℓ
  set ι := algebraMap ℚ_[ℓ] W with hι
  -- `deg` on `ℤ[X]`
  set D : ℤ[X] → ℕ := fun F => deg (aeval φ F) with hD
  have hRid : R.map (Int.castRingHom ℤ) = R := by
    rw [show Int.castRingHom ℤ = RingHom.id ℤ from RingHom.ext_int _ _, Polynomial.map_id]
  have hDN : ∀ F : ℤ[X], (D F : ℚ) = NtZ N F := by
    intro F
    have h1 : aeval φ F = ∑ i : Fin R.natDegree, ((F %ₘ R).coeff i) • φ ^ (i : ℕ) := by
      rw [← aeval_modByMonic_eq_self_of_root hRφ]
      have := modByMonic_eq_sum hR ℤ F
      rw [hRid] at this
      conv_lhs => rw [this]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, aeval_C, map_pow, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        one_mul]
    rw [hD]
    simp only
    rw [h1, hpoly, NtZ, Nt, ← map_modByMonic _ hR, ← MvPolynomial.coe_aeval_eq_eval]
    simp_rw [coeff_map]
    rfl
  have h1 : NtZ N 1 = 1 := by
    rw [← hDN, hD]; simp [hdeg1]
  have hmulZ : ∀ F G : ℤ[X], NtZ N F ≠ 0 → NtZ N G ≠ 0 → NtZ N (F * G) = NtZ N F * NtZ N G := by
    intro F G hF hG
    rw [← hDN] at hF hG
    rw [← hDN, ← hDN, ← hDN, hD]
    simp only [map_mul]
    rw [hmul _ _ (by exact_mod_cast hF) (by exact_mod_cast hG), Nat.cast_mul]
  -- the extension to `W[X]`
  have hNtW : ∀ F : ℤ[X], Nt R N W (F.map (Int.castRingHom W)) = (D F : W) := by
    intro F
    have := Nt_map N hR (Algebra.ofId ℚ W) (F.map (Int.castRingHom ℚ))
    rw [Polynomial.map_map] at this
    rw [show (Int.castRingHom W) = ((Algebra.ofId ℚ W : ℚ →ₐ[ℚ] W) : ℚ →+* W).comp
      (Int.castRingHom ℚ) from RingHom.ext_int _ _, this]
    change algebraMap ℚ W (NtZ N F) = _
    rw [← hDN, map_natCast]
  have hNt1 : Nt R N W 1 = 1 := by
    have := hNtW 1
    rw [Polynomial.map_one] at this
    rw [this, hD]; simp [hdeg1]
  let φW : W[X] →* W :=
    { toFun := Nt R N W
      map_one' := hNt1
      map_mul' := Nt_mul N hR h1 hmulZ W }
  set P := (P0 N).map (algebraMap ℚ W) with hP
  obtain ⟨hP0m, hP0d⟩ := P0_monic N hR hN h1
  have hPm : P.Monic := hP0m.map _
  have hPd : P.natDegree = n := by rw [hP, natDegree_map, hP0d]
  have hφW : ∀ F : W[X], Nt R N W F = Rs P F := by
    refine eq_Rs_of_mul φW n P hPm hPd ?_ ?_
    · intro c
      change Nt R N W (C c) = c ^ n
      rw [← mul_one (C c), Nt_C_mul N hN, hNt1, mul_one]
    · intro r
      change Nt R N W (X - C r) = _
      rw [show (X - C r : W[X]) = C (-1) * (C r - X) by rw [C_neg, C_1]; ring, Nt_C_mul N hN,
        Nt_C_sub_X N hR]
  -- the two polynomials over `ℚ_ℓ`
  set Pℓ := (P0 N).map (algebraMap ℚ ℚ_[ℓ]) with hPℓ
  have hPℓm : Pℓ.Monic := hP0m.map _
  have hPPℓ : Pℓ.map ι = P := by
    rw [hPℓ, Polynomial.map_map, hι, algebraMap_rat_comp]
  set M := ρ φ with hM
  set Q := M.charpoly with hQ
  have hRsP : ∀ F : ℤ[X], RsZ Pℓ F = (D F : W) := by
    intro F
    unfold RsZ
    rw [← hι, hPPℓ, ← hφW, hNtW]
  have hRsQ : ∀ F : ℤ[X], RsZ Q F = ι ((ρ (aeval φ F)).det) := by
    intro F
    unfold RsZ
    rw [← hι, hQ, ← Matrix.charpoly_map, ← det_aeval_eq_Rs]
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
    have e1 : aeval (M.map ι) F = (ι.mapMatrix (aeval M F)) := by
      have := Polynomial.aeval_algHom_apply (ι.mapMatrix.toIntAlgHom : Matrix I I ℚ_[ℓ] →ₐ[ℤ] _) M F
      exact this
    have e2 : aeval M F = ρ (aeval φ F) := by
      rw [hM]
      exact Polynomial.aeval_algHom_apply (ρ.toIntAlgHom) φ F
    rw [e1, e2, RingHom.map_det]
  have hPQ : Pℓ = Q := by
    refine eq_of_norm_RsZ_le hPℓm (Matrix.charpoly_monic M)
      (by rw [hPℓ, natDegree_map, hP0d, hQ, Matrix.charpoly_natDegree_eq_dim, hI]) fun F hF => ?_
    rw [hRsP] at hF ⊢
    rw [hRsQ]
    have hDF : D F ≠ 0 := by
      intro h0; apply hF; rw [h0, Nat.cast_zero]
    have := hlink (aeval φ F) hDF
    rw [hι, PadicAlgCl.norm_extends ℓ, ← map_natCast ι, hι, PadicAlgCl.norm_extends ℓ]
    exact this
  have hfin := hRsQ X
  rw [← hPQ, hRsP] at hfin
  simp only [hD, aeval_X] at hfin
  have : ι ((deg φ : ℕ) : ℚ_[ℓ]) = ι (ρ φ).det := by
    rw [map_natCast]
    exact hfin
  exact (ι.injective this).symm

end Main

end ZInQ.Contrib.OneProof.DegDet
