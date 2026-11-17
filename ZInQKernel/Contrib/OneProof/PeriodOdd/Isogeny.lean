import ZInQKernel.Contrib.OneProof.CdOptimal
import ZInQKernel.Contrib.OneProof.PeriodOdd.LFunction

/-!
# period-odd: the 2-isogeny `C_d → E'_d`, analytically and on points

Task period-odd (2026-11-16). Report `docs/research/period-odd.md`.

For `C_d : y² = x³ − d² x` and `E'_d : y² = x³ + 4d² x` (`ePrime d`), the 2-isogeny with kernel
`{O, (0, 0)}` is `φ(x, y) = (x − d²/x, y (x² + d²)/x²)`, `φ(0, 0) = φ(O) = O` (`isogPt`). It is
defined over `ℚ`, so it commutes with every `ℚ`-embedding (`map_isogPt`).

Analytically: a period lattice `L` of `C_d` is `ℤ[i] ω` (Gaussian rounding, cd-optimal), and
`L' = ((1 + i)/2) L = L ∪ (h + L)`, `h = (1 + i) ω / 2`, is a period lattice of `E'_d`
(`isPeriodLattice_ePrime`). Splitting the series of `℘_{L'}` over the two cosets gives
`℘_{L'}(z) = ℘_L(z) + ℘_L(z − h) − ℘_L(h)`, `℘_L(h) = 0` (`℘_L(iz) = −℘_L(z)`), and the group law
`(x, y) + (0, 0) = (−d²/x, d² y/x²)` on `C_d` turns this into `φ`:

`weierPt_ePrime_eq : isogPt (weierPt C_d L z) = weierPt E'_d L' z` for every `z ∈ ℂ`.

No `sorry`, no `axiom`.
-/

noncomputable section

open Complex WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace ZInQ.PeriodOdd

/-! ## §1. Splitting `℘` over two cosets; `℘(iz)` -/

section Split

/-- **`℘_{L'}` for `L' = L ⊔ (h + L)`.** -/
theorem weierstrassP_split (L L' : PeriodPair) (h : ℂ) (e : L.lattice ⊕ L.lattice ≃ L'.lattice)
    (he1 : ∀ l, (e (Sum.inl l) : ℂ) = l) (he2 : ∀ l, (e (Sum.inr l) : ℂ) = h + l) (z : ℂ) :
    L'.weierstrassP z = L.weierstrassP z + L.weierstrassP (z - h) - L.weierstrassP (-h) := by
  let F : L'.lattice → ℂ := fun l => 1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2
  have H : HasSum (F ∘ e) (L'.weierstrassP z) := e.hasSum_iff.mpr (L'.hasSum_weierstrassP z)
  have h1 : (F ∘ e) ∘ Sum.inl = fun l : L.lattice => 1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2 := by
    funext l
    simp only [Function.comp_apply, F, he1]
  have h2 : (F ∘ e) ∘ Sum.inr = fun l : L.lattice =>
      (1 / (z - h - l) ^ 2 - 1 / (l : ℂ) ^ 2) - (1 / (-h - l) ^ 2 - 1 / (l : ℂ) ^ 2) := by
    funext l
    simp only [Function.comp_apply, F, he2]
    rw [show z - (h + (l : ℂ)) = z - h - l by ring, show (h + (l : ℂ)) ^ 2 = (-h - l) ^ 2 by ring]
    ring
  have H1 : HasSum ((F ∘ e) ∘ Sum.inl) (L.weierstrassP z) := by
    rw [h1]; exact L.hasSum_weierstrassP z
  have H2 : HasSum ((F ∘ e) ∘ Sum.inr) (L.weierstrassP (z - h) - L.weierstrassP (-h)) := by
    rw [h2]; exact (L.hasSum_weierstrassP (z - h)).sub (L.hasSum_weierstrassP (-h))
  rw [H.unique (HasSum.sum (f := F ∘ e) H1 H2)]
  ring

/-- **`℘'_{L'}` for `L' = L ⊔ (h + L)`.** -/
theorem derivWeierstrassP_split (L L' : PeriodPair) (h : ℂ) (e : L.lattice ⊕ L.lattice ≃ L'.lattice)
    (he1 : ∀ l, (e (Sum.inl l) : ℂ) = l) (he2 : ∀ l, (e (Sum.inr l) : ℂ) = h + l) (z : ℂ) :
    L'.derivWeierstrassP z = L.derivWeierstrassP z + L.derivWeierstrassP (z - h) := by
  let F : L'.lattice → ℂ := fun l => -2 / (z - l) ^ 3
  have H : HasSum (F ∘ e) (L'.derivWeierstrassP z) :=
    e.hasSum_iff.mpr (L'.hasSum_derivWeierstrassP z)
  have h1 : (F ∘ e) ∘ Sum.inl = fun l : L.lattice => -2 / (z - l) ^ 3 := by
    funext l
    simp only [Function.comp_apply, F, he1]
  have h2 : (F ∘ e) ∘ Sum.inr = fun l : L.lattice => -2 / (z - h - l) ^ 3 := by
    funext l
    simp only [Function.comp_apply, F, he2]
    rw [show z - (h + (l : ℂ)) = z - h - l by ring]
  have H1 : HasSum ((F ∘ e) ∘ Sum.inl) (L.derivWeierstrassP z) := by
    rw [h1]; exact L.hasSum_derivWeierstrassP z
  have H2 : HasSum ((F ∘ e) ∘ Sum.inr) (L.derivWeierstrassP (z - h)) := by
    rw [h2]; exact L.hasSum_derivWeierstrassP (z - h)
  exact H.unique (HasSum.sum (f := F ∘ e) H1 H2)

/-- **`℘_L(iz) = −℘_L(z)`** for a lattice stable under multiplication by `i`. -/
theorem weierstrassP_I_mul (L : PeriodPair) (hLI : ∀ y ∈ L.lattice, I * y ∈ L.lattice) (z : ℂ) :
    L.weierstrassP (I * z) = -L.weierstrassP z := by
  let eI : L.lattice ≃ L.lattice :=
    { toFun := fun l => ⟨I * l, hLI _ l.2⟩
      invFun := fun l => ⟨-I * l, by
        have := hLI _ (hLI _ (hLI _ l.2))
        convert this using 1
        linear_combination (-(I * (l : ℂ))) * Complex.I_sq⟩
      left_inv := fun l => by
        ext; simp only
        linear_combination (-(l : ℂ)) * Complex.I_sq
      right_inv := fun l => by
        ext; simp only
        linear_combination (-(l : ℂ)) * Complex.I_sq }
  have H := L.hasSum_weierstrassP (I * z)
  rw [← eI.hasSum_iff] at H
  refine H.unique ?_
  convert (L.hasSum_weierstrassP z).neg using 1
  funext l
  simp only [Function.comp_apply, eI, Equiv.coe_fn_mk]
  rw [show I * z - I * (l : ℂ) = I * (z - l) by ring, mul_pow, mul_pow, Complex.I_sq]
  simp only [neg_one_mul, one_div, inv_neg]
  ring

end Split

/-! ## §2. The lattice `L' = ((1 + i)/2) L` -/

/-- `λ = (1 + i)/2`. -/
abbrev lam : ℂ := (1 + I) / 2

theorem lam_ne_zero : lam ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem lam_pow_four : lam ^ 4 = -1 / 4 := by
  rw [lam, div_pow]
  have : (1 + I) ^ 4 = -4 := by linear_combination (I ^ 2 + 4 * I + 5) * Complex.I_sq
  rw [this]; norm_num

/-- `L' = λ L`. -/
abbrev latP (L : PeriodPair) : PeriodPair := ZInQ.GZWeil.scalePP L lam lam_ne_zero

section Lattice

variable {L : PeriodPair} (hLI : ∀ y ∈ L.lattice, I * y ∈ L.lattice) {ω : ℂ} (hω : ω ∈ L.lattice)
  (hω0 : ω ≠ 0) (hrep : ∀ ν ∈ L.lattice, ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * ω)

include hLI in
theorem le_latP {y : ℂ} (hy : y ∈ L.lattice) : y ∈ (latP L).lattice := by
  refine (ZInQ.GZWeil.mem_scalePP lam_ne_zero).mpr ⟨(1 - I) * y, ?_, ?_⟩
  · have : (1 - I) * y = y - I * y := by ring
    rw [this]; exact sub_mem hy (hLI y hy)
  · rw [lam]
    linear_combination (y / 2) * Complex.I_sq

include hω in
theorem h_mem_latP : lam * ω ∈ (latP L).lattice :=
  (ZInQ.GZWeil.mem_scalePP lam_ne_zero).mpr ⟨ω, hω, rfl⟩

include hω0 hrep in
theorem h_notMem : lam * ω ∉ L.lattice := by
  intro h
  obtain ⟨m, n, hmn⟩ := hrep _ h
  have := congrArg Complex.re (mul_right_cancel₀ hω0 hmn)
  simp at this
  have h2 : ((2 * m : ℤ) : ℝ) = 1 := by push_cast; linarith
  have h3 : (2 * m : ℤ) = 1 := by exact_mod_cast h2
  omega

include hLI hω in
/-- Gaussian integers `(a + b i)` with `a ≡ b (mod 2)` times `λ` lie in `ℤ[i]`. -/
theorem lam_gauss_mem {m n : ℤ} (hmn : Even (m + n)) : lam * (((m : ℂ) + n * I) * ω) ∈ L.lattice := by
  obtain ⟨k, hk⟩ := hmn
  have e : lam * (((m : ℂ) + n * I) * ω) = (((m - k : ℤ) : ℂ) + ((k : ℤ) : ℂ) * I) * ω := by
    have hn : (n : ℂ) = 2 * k - m := by
      have : (n : ℤ) = 2 * k - m := by omega
      exact_mod_cast this
    rw [lam, hn]; push_cast
    linear_combination (-(m : ℂ) / 2 + k) * ω * Complex.I_sq
  rw [e]
  exact ZInQ.CdOpt.gauss_mul_mem hLI _ _ hω

include hLI hω hrep in
theorem mem_latP_iff {x : ℂ} : x ∈ (latP L).lattice ↔ x ∈ L.lattice ∨ x - lam * ω ∈ L.lattice := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := (ZInQ.GZWeil.mem_scalePP lam_ne_zero).mp hx
    obtain ⟨m, n, rfl⟩ := hrep y hy
    rcases Int.even_or_odd (m + n) with he | ho
    · exact Or.inl (lam_gauss_mem hLI hω he)
    · right
      have e : lam * (((m : ℂ) + n * I) * ω) - lam * ω =
          lam * ((((m - 1 : ℤ) : ℂ) + n * I) * ω) := by push_cast; ring
      rw [e]
      exact lam_gauss_mem hLI hω (by
        obtain ⟨k, hk⟩ := ho; exact ⟨k, by omega⟩)
  · rintro (h | h)
    · exact le_latP hLI h
    · have := add_mem (le_latP hLI h) (h_mem_latP hω)
      rwa [sub_add_cancel] at this

include hLI hω hω0 hrep in
/-- **`L' = L ⊔ (h + L)`** as an equivalence of index sets. -/
def latPEquiv : L.lattice ⊕ L.lattice ≃ (latP L).lattice := by
  classical
  exact
  { toFun := Sum.elim (fun l => ⟨l, le_latP hLI l.2⟩)
      (fun l => ⟨lam * ω + l, add_mem (h_mem_latP hω) (le_latP hLI l.2)⟩)
    invFun := fun x => if hx : (x : ℂ) ∈ L.lattice then Sum.inl ⟨x, hx⟩ else
      Sum.inr ⟨x - lam * ω, ((mem_latP_iff hLI hω hrep).mp x.2).resolve_left hx⟩
    left_inv := by
      rintro (l | l)
      · simp [l.2]
      · have hnot : lam * ω + (l : ℂ) ∉ L.lattice := fun h =>
          h_notMem hω0 hrep (by have := sub_mem h l.2; rwa [add_sub_cancel_right] at this)
        simp [hnot]
    right_inv := by
      intro x
      by_cases hx : (x : ℂ) ∈ L.lattice
      · simp [hx]
      · simp [hx] }

theorem latPEquiv_inl (l : L.lattice) :
    ((latPEquiv hLI hω hω0 hrep (Sum.inl l)) : ℂ) = l := rfl

theorem latPEquiv_inr (l : L.lattice) :
    ((latPEquiv hLI hω hω0 hrep (Sum.inr l)) : ℂ) = lam * ω + l := rfl

end Lattice

/-! ## §3. The isogeny on points -/

section Points

variable {K : Type*} [Field K] [Algebra ℚ K] [DecidableEq K]

omit [DecidableEq K] in
theorem cd_equation_iff (d : ℕ) (x y : K) :
    ((shortCurve (-(d : ℚ) ^ 2))⁄K).Equation x y ↔ y ^ 2 = x ^ 3 - (d : K) ^ 2 * x := by
  rw [Affine.equation_iff]
  simp [shortCurve]
  constructor <;> intro h <;> linear_combination h

omit [DecidableEq K] in
theorem ePrime_equation_iff (d : ℕ) (x y : K) :
    ((ePrime d)⁄K).Equation x y ↔ y ^ 2 = x ^ 3 + 4 * (d : K) ^ 2 * x := by
  rw [Affine.equation_iff]
  simp [ePrime, shortCurve, map_mul, map_pow, map_natCast, map_ofNat]

theorem ePrime_isElliptic {d : ℕ} (hd : d ≠ 0) : (ePrime d).IsElliptic :=
  shortCurve_isElliptic (mul_ne_zero (by norm_num) (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hd)))

theorem short_ePrime (d : ℕ) : ZInQ.GZOptimal.IsShortModel (ePrime d) := ⟨rfl, rfl, rfl⟩

omit [DecidableEq K] in
/-- The image of a point under `φ` satisfies the equation of `E'_d`. -/
theorem isog_nonsingular {d : ℕ} (hd : d ≠ 0) {x y : K}
    (h : ((shortCurve (-(d : ℚ) ^ 2))⁄K).Nonsingular x y) (hx : x ≠ 0) :
    ((ePrime d)⁄K).Nonsingular (x - (d : K) ^ 2 / x) (y * (x ^ 2 + (d : K) ^ 2) / x ^ 2) := by
  have := ePrime_isElliptic hd
  rw [← Affine.equation_iff_nonsingular, ePrime_equation_iff]
  have h1 := (cd_equation_iff d x y).mp h.1
  have key : (y * (x ^ 2 + (d : K) ^ 2) / x ^ 2) ^ 2 - ((x - (d : K) ^ 2 / x) ^ 3 +
      4 * (d : K) ^ 2 * (x - (d : K) ^ 2 / x)) =
      (x ^ 2 + (d : K) ^ 2) ^ 2 / x ^ 4 * (y ^ 2 - (x ^ 3 - (d : K) ^ 2 * x)) := by
    field_simp; ring
  rw [h1, sub_self, mul_zero, sub_eq_zero] at key
  exact key

open Classical in
/-- **The 2-isogeny `φ : C_d → E'_d`** with kernel `{O, (0, 0)}`:
`(x, y) ↦ (x − d²/x, y (x² + d²)/x²)` for `x ≠ 0`, `(0, 0) ↦ O`, `O ↦ O`. -/
def isogPt {d : ℕ} (hd : d ≠ 0) : ((shortCurve (-(d : ℚ) ^ 2))⁄K).Point → ((ePrime d)⁄K).Point
  | .zero => 0
  | .some x _ h => if hx : x = 0 then 0 else .some _ _ (isog_nonsingular hd h hx)

/-- `φ` is defined over `ℚ`: it commutes with every `ℚ`-algebra map. -/
theorem map_isogPt {F : Type*} [Field F] [Algebra ℚ F] [DecidableEq F] {d : ℕ} (hd : d ≠ 0) (ι : K →ₐ[ℚ] F)
    (P : ((shortCurve (-(d : ℚ) ^ 2))⁄K).Point) :
    Affine.Point.map ι (isogPt hd P) = isogPt hd (Affine.Point.map ι P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.map_some]
    by_cases hx : x = 0
    · simp only [isogPt, hx, ↓reduceDIte, map_zero]
    · have hx' : ι x ≠ 0 := fun h0 => hx (ι.injective (h0.trans (map_zero ι).symm))
      simp only [isogPt, hx, hx', ↓reduceDIte, Affine.Point.map_some, Affine.Point.some.injEq]
      constructor
      · simp [map_sub, map_div₀, map_pow, map_natCast]
      · simp [map_mul, map_div₀, map_add, map_pow, map_natCast]

end Points

/-! ## §4. `φ` on the analytic parametrization -/

section Analytic

open ZInQ.GZOptimal ZInQ.GZHL3

/-- `weierPt` of a short model off the lattice. -/
theorem weierPt_short {E : WeierstrassCurve ℚ} [E.IsElliptic] (hE : IsShortModel E)
    {L : PeriodPair} (hL : IsPeriodLattice E L) {z : ℂ} (hz : z ∉ L.lattice) :
    ∃ hns, weierPt E L z = .some (L.weierstrassP z) (L.derivWeierstrassP z / 2) hns := by
  rw [ZInQ.GZHeegner.weierPt_eq_some _ hL hz]
  have hns := weierPt_some E hL hz
  simp only [bc_b₂ hE, bc_a₁ hE, bc_a₃ hE, zero_div, sub_zero, zero_mul] at hns ⊢
  exact ⟨hns, trivial⟩

/-- **`L' = ((1 + i)/2) L` is a period lattice of `E'_d`**: `g₂(L') = (λ⁴)⁻¹ 4d² = −16 d²`,
`g₃(L') = 0`. -/
theorem isPeriodLattice_ePrime {d : ℕ} {L : PeriodPair}
    (hL : IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) : IsPeriodLattice (ePrime d) (latP L) := by
  obtain ⟨h2, h3⟩ := (ZInQ.GZWeil.isPeriodLattice_cd_iff d L).mp hL
  constructor
  · rw [ZInQ.GZWeil.g₂_scalePP, h2, lam_pow_four]
    simp [ePrime, shortCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  · rw [ZInQ.GZWeil.g₃_scalePP, h3]
    simp [ePrime, shortCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]

/-- **The 2-isogeny on the analytic parametrization.** For a period lattice `L` of `C_d`
(`d ≠ 0`) and `L' = ((1 + i)/2) L`: `φ(weierPt C_d L z) = weierPt E'_d L' z` for every `z`. -/
theorem weierPt_ePrime_eq {d : ℕ} (hd : d ≠ 0) {L : PeriodPair}
    (hL : IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) (z : ℂ) :
    isogPt hd (weierPt (shortCurve (-(d : ℚ) ^ 2)) L z) = weierPt (ePrime d) (latP L) z := by
  have hEc := ZInQ.GZDecomp.shortCurve_cd_isElliptic hd
  have hEe := ePrime_isElliptic hd
  have hLI : ∀ y ∈ L.lattice, I * y ∈ L.lattice := fun y hy => ZInQ.CdOpt.I_mul_mem_of_cd hL hy
  obtain ⟨ω, hω, hω0, hωmin⟩ :=
    ZInQ.CdOpt.exists_min L L.lattice le_rfl L.ω₁_mem_lattice (ω₁_ne_zero L)
  have hrep : ∀ ν ∈ L.lattice, ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * ω :=
    fun ν hν => ZInQ.CdOpt.gauss_rep hLI hω hω0 hωmin hν
  have hL' : IsPeriodLattice (ePrime d) (latP L) := isPeriodLattice_ePrime hL
  set h : ℂ := lam * ω with hh
  have hsplitP := weierstrassP_split L (latP L) h (latPEquiv hLI hω hω0 hrep)
    (latPEquiv_inl hLI hω hω0 hrep) (latPEquiv_inr hLI hω hω0 hrep)
  have hsplitD := derivWeierstrassP_split L (latP L) h (latPEquiv hLI hω hω0 hrep)
    (latPEquiv_inl hLI hω hω0 hrep) (latPEquiv_inr hLI hω hω0 hrep)
  -- `℘_L(h) = 0`
  have hIh : I * h = h - ω := by
    rw [hh, lam]; linear_combination (ω / 2) * Complex.I_sq
  have hPh : L.weierstrassP h = 0 := by
    have h1 := weierstrassP_I_mul L hLI h
    rw [hIh, show h - ω = h - ((⟨ω, hω⟩ : L.lattice) : ℂ) from rfl, L.weierstrassP_sub_coe] at h1
    linear_combination h1 / 2
  have hPmh : L.weierstrassP (-h) = 0 := by rw [L.weierstrassP_neg, hPh]
  have hhL : h ∉ L.lattice := h_notMem hω0 hrep
  have hmh : -h ∉ L.lattice := fun hm => hhL (by simpa using L.lattice.neg_mem hm)
  obtain ⟨hns0, hW0⟩ := weierPt_short (short_cd d) hL hmh
  have hy0 : L.derivWeierstrassP (-h) / 2 = 0 := by
    have := (cd_equation_iff d _ _).mp hns0.1
    rw [hPmh] at this
    simpa using this
  by_cases hzL : z ∈ L.lattice
  · rw [ZInQ.GZHeegner.weierPt_eq_zero _ _ hzL,
      ZInQ.GZHeegner.weierPt_eq_zero _ _ (le_latP hLI hzL)]
    rfl
  obtain ⟨hns, hW⟩ := weierPt_short (short_cd d) hL hzL
  have hxy := (cd_equation_iff d _ _).mp hns.1
  by_cases hx : L.weierstrassP z = 0
  · -- `z ∈ h + L ⊆ L'`: both sides are `O`
    have hy : L.derivWeierstrassP z / 2 = 0 := by
      rw [hx] at hxy; simpa using hxy
    have heq : weierPt (shortCurve (-(d : ℚ) ^ 2)) L z =
        weierPt (shortCurve (-(d : ℚ) ^ 2)) L (-h) := by
      rw [hW, hW0]
      simp only [Affine.Point.some.injEq]
      exact ⟨by rw [hx, hPmh], by rw [hy, hy0]⟩
    have hzh : z + h ∈ L.lattice := by
      rw [← weierPt_eq_zero_iff _ hL, weierPt_add' (short_cd d) hL, heq,
        ← weierPt_add' (short_cd d) hL, neg_add_cancel]
      exact ZInQ.GZHeegner.weierPt_eq_zero _ _ L.lattice.zero_mem
    have hzP : z ∈ (latP L).lattice := by
      have := sub_mem (le_latP hLI hzh) (h_mem_latP hω)
      rwa [add_sub_cancel_right] at this
    rw [hW, ZInQ.GZHeegner.weierPt_eq_zero _ _ hzP]
    simp only [isogPt, hx, ↓reduceDIte]
  · -- `z ∉ L'`
    have hzP : z ∉ (latP L).lattice := by
      intro hzP
      rcases (mem_latP_iff hLI hω hrep).mp hzP with h1 | h1
      · exact hzL h1
      · apply hx
        have e : z = h + ((⟨z - h, h1⟩ : L.lattice) : ℂ) := by simp
        rw [e, L.weierstrassP_add_coe, hPh]
    have hzh : z - h ∉ L.lattice := fun h1 => hzP ((mem_latP_iff hLI hω hrep).mpr (Or.inr h1))
    obtain ⟨hns', hW'⟩ := weierPt_short (short_ePrime d) hL' hzP
    obtain ⟨hns2, hW2⟩ := weierPt_short (short_cd d) hL hzh
    have hadd : weierPt (shortCurve (-(d : ℚ) ^ 2)) L (z - h) =
        weierPt (shortCurve (-(d : ℚ) ^ 2)) L z + weierPt (shortCurve (-(d : ℚ) ^ 2)) L (-h) := by
      rw [sub_eq_add_neg, weierPt_add' (short_cd d) hL]
    rw [hW2, hW, hW0, Affine.Point.add_some (fun hc => hx (hc.1.trans hPmh))] at hadd
    simp only [Affine.Point.some.injEq] at hadd
    obtain ⟨hX2, hY2⟩ := hadd
    rw [hW, hW']
    simp only [isogPt, hx, ↓reduceDIte, Affine.Point.some.injEq]
    rw [hPmh, hy0, Affine.slope_of_X_ne hx] at hX2 hY2
    simp [shortCurve, Affine.addX, Affine.addY, Affine.negAddY, Affine.negY] at hX2 hY2
    set x := L.weierstrassP z with hxdef
    set y := L.derivWeierstrassP z / 2 with hydef
    constructor
    · rw [hsplitP z, hPmh, hX2]
      field_simp
      linear_combination (-1 : ℂ) * hxy
    · have e2 : (latP L).derivWeierstrassP z / 2 = y + L.derivWeierstrassP (z - h) / 2 := by
        rw [hsplitD z, hydef]; ring
      rw [e2, hY2]
      field_simp
      linear_combination y * hxy

end Analytic

end ZInQ.PeriodOdd
