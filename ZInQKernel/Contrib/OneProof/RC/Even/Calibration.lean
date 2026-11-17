import Mathlib
import ZInQKernel.Hypotheses.PoleManuscript
import ZInQKernel.Contrib.PoleRC.KummerF

/-!
# Theorem 5.3, Lane RC11-even: the central calibration bookkeeping (E.8)–(E.9) and `−2ω(h)`

The 11/5 manuscript (`diophantine_zq.tex`), Section 7.1 (tex 1958–1965) and Appendix E,
Proposition `ex:app-central-calibration` (tex 7614–7787). This file proves:

* `fixed_iff_two_nsmul_eq_zero` — if inertia acts by `−1` on a group `A` then its fixed points are
  `A[2]` (tex 1963, 7768–7769: at an active good odd prime the quadratic twist is ramified, so
  inertia acts on `E^h[2^∞] = E[2^∞] ⊗ χ_h` through `χ_h`, by `−1`, and `A^{I_v} = E[2]`);
* `card_two_torsion_curveF`, `length_two_torsion_curveF` — over every field `F` with `2, 3 ≠ 0`,
  `E_ℓ^{(h)}(F)[2] = {O, (0,0), (hℓ,0), (−3hℓ,0)}` has exactly four points, so length two
  (tex 7769: "of length two for the present curve"); `baseChange_curve` identifies the twist
  `E_ℓ^{(h)} = curve (hℓ)` over `ℚ` with `curveF (hℓ)` over `F`;
* `card_active_le_omega`, `omega_le_card_active_add` — `ω(h)` differs from the number of active
  good primes by at most `ω(N)` (the bad primes dividing `h`);
* `E8_of_E7_K3` — **(E.8)** (tex 7755–7775): from (E.7) and (K3), the unused-prime terms
  `v₂ #E^h(𝔽_q)` cancel against `g_q`, every active good prime contributes `g_q = 2`, the remaining
  local types are bounded, and
  `|v₂ u_h^{ev}(0) − (v₂ L_*(h) − 2ω(h) − s(h))| ≤ C_loc`
  with `C_loc` depending only on the fixed local data (not on the active or unused primes);
* `E9_of_E5_E8` — **(E.9)** (tex 7782–7785): `2^{c_E} u ∈ Λ` and (E.8) give
  `v₂ L_*(h) ≥ 2ω(h) + s(h) − c_E − C_loc`.

Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Even

open WeierstrassCurve

/-! ## Inertia acting by `−1` -/

/-- **Fixed points of `−1` are the `2`-torsion** (tex 1963, 7768–7769; PROVED): if `σ` acts on an
abelian group `A` by `−1`, then `σ m = m ↔ 2 • m = 0`. -/
theorem fixed_iff_two_nsmul_eq_zero {A : Type*} [AddCommGroup A] (σ : A →+ A)
    (hσ : ∀ m, σ m = -m) (m : A) : σ m = m ↔ 2 • m = 0 := by
  rw [hσ, two_nsmul]
  exact neg_eq_iff_add_eq_zero

/-! ## The two-torsion of `E_ℓ^{(h)}` -/

/-- The twist `E_ℓ^{(h)} = E_{hℓ}` (`curve (h * ℓ)` over `ℚ`) base-changed to a field `F ⊇ ℚ` is
the tree's `curveF` at the image of `hℓ` (PROVED). -/
theorem baseChange_curve {F : Type*} [Field F] [Algebra ℚ F] (q : ℚ) :
    (ZInQ.Manuscript.curve q).baseChange F = ZInQ.Manuscript.PoleRC.curveF (algebraMap ℚ F q) := by
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map, ZInQ.Manuscript.curve,
    ZInQ.Manuscript.PoleRC.curveF, map_zero, map_mul, map_neg, map_pow, map_ofNat]

/-- **`E_ℓ(F)[2]` has exactly four points** (PROVED): over a field with `2, 3 ≠ 0` and `ℓ ≠ 0`,
the kernel of multiplication by two on `E_ℓ(F)` is `{O, (0,0), (ℓ,0), (−3ℓ,0)}`. Applied at `hℓ`
it gives the two-torsion of every quadratic twist `E_ℓ^{(h)}`. -/
theorem card_two_torsion_curveF {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {ℓ : F} (hℓ : ℓ ≠ 0) :
    Nat.card (nsmulAddMonoidHom 2 :
      (ZInQ.Manuscript.PoleRC.curveF ℓ).toAffine.Point →+ _).ker = 4 := by
  open ZInQ.Manuscript.PoleRC WeierstrassCurve.Affine in
  set T₀ := tPtF h2 h3 hℓ (isRootF_zero ℓ)
  set T₁ := tPtF h2 h3 hℓ (isRootF_ell ℓ)
  set T₂ := tPtF h2 h3 hℓ (isRootF_neg3 ℓ)
  have htor : ∀ {e : F} (he : IsRootF ℓ e), 2 • tPtF h2 h3 hℓ he = 0 := by
    intro e he
    unfold tPtF
    rw [two_nsmul, Point.add_self_of_Y_eq (by rw [curveF_negY, neg_zero])]
  have hx : ∀ {e e' : F} (he : IsRootF ℓ e) (he' : IsRootF ℓ e'),
      tPtF h2 h3 hℓ he = tPtF h2 h3 hℓ he' → e = e' := by
    intro e e' he he' h
    unfold tPtF at h
    simp only [Point.some.injEq] at h
    exact h.1
  have hz : ∀ {e : F} (he : IsRootF ℓ e), (0 : (curveF ℓ).toAffine.Point) ≠ tPtF h2 h3 hℓ he := by
    intro e he h
    unfold tPtF at h
    exact Point.some_ne_zero _ h.symm
  -- the kernel of multiplication by two is exactly `{O, T₀, T₁, T₂}`
  have hker : ((nsmulAddMonoidHom 2 : (curveF ℓ).toAffine.Point →+ _).ker : Set _) =
      {0, T₀, T₁, T₂} := by
    ext P
    simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hP
      have hneg : P = -P := eq_neg_of_add_eq_zero_left (by rw [← two_nsmul]; exact hP)
      rcases P with _ | ⟨x, y, hxy⟩
      · exact Or.inl rfl
      · right
        rw [Point.neg_some, Point.some.injEq, curveF_negY] at hneg
        have hy : y = 0 := by
          have h2y : 2 * y = 0 := by linear_combination hneg.2
          exact (mul_eq_zero.mp h2y).resolve_left h2
        have hroot : IsRootF ℓ x := by
          have hq := (curveF_equation_iff x y).mp hxy.1
          rw [hy] at hq
          unfold IsRootF
          linear_combination -hq
        rcases isRootF_cases hroot with h0 | h0 | h0
        · exact Or.inl (some_eq_tPtF h2 h3 hℓ _ hxy h0)
        · exact Or.inr (Or.inl (some_eq_tPtF h2 h3 hℓ _ hxy h0))
        · exact Or.inr (Or.inr (some_eq_tPtF h2 h3 hℓ _ hxy h0))
    · rintro (rfl | rfl | rfl | rfl)
      · exact nsmul_zero 2
      · exact htor _
      · exact htor _
      · exact htor _
  have h4 : ({0, T₀, T₁, T₂} : Set (curveF ℓ).toAffine.Point).ncard = 4 := by
    have h01 : (0 : F) ≠ ℓ := fun h => hℓ h.symm
    have h03 : (0 : F) ≠ -3 * ℓ := fun h => mul_ne_zero (neg_ne_zero.mpr h3) hℓ h.symm
    have h13 : ℓ ≠ -3 * ℓ := fun h =>
      mul_ne_zero (mul_ne_zero h2 h2) hℓ (by linear_combination h)
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair]
    · exact fun h => h13 (hx _ _ h)
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => h01 (hx _ _ h), fun h => h03 (hx _ _ h)⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hz _, hz _, hz _⟩
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hker, h4]

/-- **Length two** (tex 7769; PROVED): `length_{ℤ₂} E_ℓ(F)[2] = log₂ 4 = 2`. -/
theorem length_two_torsion_curveF {F : Type*} [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    {ℓ : F} (hℓ : ℓ ≠ 0) :
    Nat.log 2 (Nat.card (nsmulAddMonoidHom 2 :
      (ZInQ.Manuscript.PoleRC.curveF ℓ).toAffine.Point →+ _).ker) = 2 := by
  rw [card_two_torsion_curveF h2 h3 hℓ, show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.log_pow (by norm_num)]

/-! ## `ω(h)` and the active good primes -/

/-- `ω(h)`: the number of distinct prime factors of `|h|`. -/
def omega (h : ℤ) : ℕ := h.natAbs.primeFactors.card

/-- The active good primes of `h` for a curve of conductor `N`: the primes of `h` not dividing `N`
(for odd `h` these are the good odd primes ramified in `χ_h`). -/
def activePrimes (h : ℤ) (N : ℕ) : Finset ℕ := h.natAbs.primeFactors.filter (fun p => ¬ p ∣ N)

/-- The number of active good primes is at most `ω(h)` (PROVED). -/
theorem card_active_le_omega (h : ℤ) (N : ℕ) : (activePrimes h N).card ≤ omega h := by
  unfold activePrimes omega
  exact Finset.card_filter_le _ _

/-- `ω(h)` exceeds the number of active good primes by at most `ω(N)` (PROVED; `N ≠ 0`). -/
theorem omega_le_card_active_add (h : ℤ) {N : ℕ} (hN : N ≠ 0) :
    omega h ≤ (activePrimes h N).card + N.primeFactors.card := by
  unfold omega activePrimes
  have hsplit := Finset.card_filter_add_card_filter_not (s := h.natAbs.primeFactors) (fun p => p ∣ N)
  have hsub : h.natAbs.primeFactors.filter (fun p => p ∣ N) ⊆ N.primeFactors := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp.1, hp.2, hN⟩
  have := Finset.card_le_card hsub
  omega

/-! ## (E.8) and (E.9) -/

/-- **(E.8) from (E.7) and (K3)** (tex 7755–7775; PROVED). The finite places of `S` are split into
the active good primes `act`, the unused good primes `unused` and the fixed places `fix` (two and
the bad primes). Assume
* (E.7): `v₂u = v₂exp − s − Σ_{v ∈ S} g_v + 2g + 1 − r₁ − e₂`,
* (K3): `v₂exp = v₂L + Σ_{q ∈ unused} n_q + ε_rec` with `|ε_rec| ≤ C_E`, where `n_q = v₂ #E^h(𝔽_q)`,
* `g_q = n_q` at unused good primes, `g_q = 2` at active good primes,
* `0 ≤ g_v ≤ C_fix` at the fixed places, `0 ≤ g ≤ C_g`, `0 ≤ r₁ ≤ C_r`, `|e₂| ≤ C_e`.

Then the unused terms cancel and
`|v₂u − (v₂L − 2·#act − s)| ≤ C_E + #fix·C_fix + 2C_g + 1 + C_r + C_e`:
the bound does not involve the active or unused primes. -/
theorem E8_of_E7_K3 (act unused fix : Finset ℕ) (hdau : Disjoint act unused)
    (hdaf : Disjoint act fix) (hduf : Disjoint unused fix)
    (gv nq : ℕ → ℤ) (v2u v2exp v2L s g r₁ e₂ εrec CE Cfix Cg Cr Ce : ℤ)
    (hE7 : v2u = v2exp - s - ∑ v ∈ act ∪ unused ∪ fix, gv v + 2 * g + 1 - r₁ - e₂)
    (hK3 : v2exp = v2L + ∑ q ∈ unused, nq q + εrec) (hrec : |εrec| ≤ CE)
    (hunused : ∀ q ∈ unused, gv q = nq q) (hact : ∀ q ∈ act, gv q = 2)
    (hfix : ∀ v ∈ fix, 0 ≤ gv v ∧ gv v ≤ Cfix) (hg : 0 ≤ g ∧ g ≤ Cg) (hr : 0 ≤ r₁ ∧ r₁ ≤ Cr)
    (he : |e₂| ≤ Ce) :
    |v2u - (v2L - 2 * (act.card : ℤ) - s)| ≤ CE + fix.card * Cfix + 2 * Cg + 1 + Cr + Ce := by
  have hsum : ∑ v ∈ act ∪ unused ∪ fix, gv v =
      2 * (act.card : ℤ) + ∑ q ∈ unused, nq q + ∑ v ∈ fix, gv v := by
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨hdaf, hduf⟩), Finset.sum_union hdau,
      Finset.sum_congr rfl hact, Finset.sum_congr rfl hunused, Finset.sum_const, nsmul_eq_mul,
      mul_comm]
  have hfix0 : 0 ≤ ∑ v ∈ fix, gv v := Finset.sum_nonneg fun v hv => (hfix v hv).1
  have hfix1 : ∑ v ∈ fix, gv v ≤ fix.card * Cfix := by
    rw [← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun v hv => (hfix v hv).2
  rw [hE7, hsum, hK3]
  obtain ⟨hrec1, hrec2⟩ := abs_le.mp hrec
  obtain ⟨he1, he2⟩ := abs_le.mp he
  rw [abs_le]
  constructor <;> linarith [hg.1, hg.2, hr.1, hr.2]

/-- **(E.8) with `ω(h)`** (tex 7774–7775; PROVED): if `|v₂u − (v₂L − 2·#act − s)| ≤ C` and
`#act ≤ ω(h) ≤ #act + ω(N)`, then `|v₂u − (v₂L − 2ω(h) − s)| ≤ C + 2ω(N)`. -/
theorem E8_omega {v2u v2L s C : ℤ} {nact om omN : ℕ}
    (h : |v2u - (v2L - 2 * (nact : ℤ) - s)| ≤ C) (h1 : nact ≤ om) (h2 : om ≤ nact + omN) :
    |v2u - (v2L - 2 * (om : ℤ) - s)| ≤ C + 2 * omN := by
  have h1' : (nact : ℤ) ≤ om := by exact_mod_cast h1
  have h2' : (om : ℤ) ≤ nact + omN := by exact_mod_cast h2
  have h3' : (0 : ℤ) ≤ omN := Nat.cast_nonneg omN
  obtain ⟨ha, hb⟩ := abs_le.mp h
  rw [abs_le]
  constructor <;> linarith

/-- **(E.9)** (tex 7782–7785; PROVED): if `2^{c_E} u(0) ∈ ℤ₂` (from (E.5) with `G = 1`),
`u(0) ≠ 0`, and (E.8) `v₂ u(0) = v₂L − 2ω − s + ε` with `|ε| ≤ C_loc`, then
`v₂L ≥ 2ω + s − c_E − C_loc`. -/
theorem E9_of_E5_E8 {u0 : ℚ_[2]} {cE : ℕ} (hint : ‖(2 : ℚ_[2]) ^ cE * u0‖ ≤ 1) (hu0 : u0 ≠ 0)
    {v2L om s ε Cloc : ℤ} (hE8 : u0.valuation = v2L - 2 * om - s + ε) (hε : |ε| ≤ Cloc) :
    2 * om + s - cE - Cloc ≤ v2L := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  have hv := (Padic.norm_le_one_iff_val_nonneg _).mp hint
  have hv2 : (2 : ℚ_[2]).valuation = 1 := by simp
  rw [Padic.valuation_mul (pow_ne_zero _ h2) hu0, Padic.valuation_pow, hv2, hE8] at hv
  have := (abs_le.mp hε).2
  linarith

end ZInQ.Manuscript.RC.Even
