import ZInQKernel.Contrib.OneProof.PeriodOdd.Isogeny
import ZInQKernel.Contrib.OneProof.PeriodOdd.NeZero

/-!
# period-odd: the Gross–Zagier formula for `C_d` without `CdTwistedPeriodOdd`

Task period-odd (2026-11-16). Report: `docs/research/period-odd.md`; scratch and log:
`scratch/period-odd/`.

cd-optimal reduced `GZHL3.GrossZagierFormulaCd` to gz-optimal's leaf `GrossZagierModuliOptCd`, the
printed leaf `EtaW32Character` and the glue `CdTwistedPeriodOdd` (some period of `f_d` lies outside
`(1 + i) L`), which separates "`C_d` is optimal" from "the 2-isogenous `E'_d : y² = x³ + 4d² x` is
optimal". This file removes `CdTwistedPeriodOdd`: the Gross–Zagier formula is transported along the
2-isogeny in the second case.

* `lattice_cases`: if `Λ_d ⊆ L` (`EtaW32Character`, cd-optimal) and `Λ_d ≠ 0`, then either
  `L = c₀ Λ_d` (`C_d` optimal) or `L' = ((1 + i)/2) L = c Λ_d` (`E'_d` optimal), `c₀, c ∈ ℚ`.
* `core_isog`: in the second case, gz-optimal's leaf at `E'_d` (it covers every short model with the
  L-function of `C_d`: `LFunction_ePrime_eq`) and the explicit 2-isogeny `φ : C_d → E'_d`
  (`isogPt`, `weierPt_ePrime_eq`, `map_isogPt`) give the formula at `C_d`.
* `periodLattice_ne_zero` (`PeriodOdd/NeZero.lean`): `Λ_f ≠ 0` for every weight-2 newform
  (a `Γ₀(N)`-invariant Eichler integral would be a weight-0 modular form, hence constant).
* `grossZagierFormulaCd_of_etaW32`: **`GrossZagierFormulaCd` from `GrossZagierModuliOptCd` and
  `EtaW32Character`** alone.

No `sorry`, no `axiom`.
-/

noncomputable section

open Complex WeierstrassCurve HeckeRing.GL2 ZInQ.GZDecomp
open scoped WeierstrassCurve.Affine

namespace ZInQ.PeriodOdd

open ZInQ.CdOpt ZInQ.GZOptimal

/-! ## §1. The classification of `Λ_d ⊆ L` -/

section Gauss

variable {Λ : Submodule ℤ ℂ} {L : PeriodPair} (hLI : ∀ y ∈ L.lattice, I * y ∈ L.lattice)
  (hΛI : ∀ y ∈ Λ, I * y ∈ Λ) {ω μ : ℂ} (hω : ω ∈ L.lattice) (hμ : μ ∈ Λ)
  (repL : ∀ ν ∈ L.lattice, ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * ω)
  (repΛ : ∀ ν ∈ Λ, ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * μ)
include hLI hΛI hω hμ repL repΛ

/-- `μ = k u ω`, `u ∈ {1, i}`: `L = (1/k) Λ`. -/
theorem lattice_eq_of_mu {k : ℤ} {u : ℂ} (hk0 : k ≠ 0) (hu : u = 1 ∨ u = I)
    (hμku : μ = k * u * ω) : L.lattice = Λ.map (LinearMap.mulLeft ℤ (((1 / k : ℚ)) : ℂ)) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, ((a : ℂ) + b * I) * u = 1 := by
    rcases hu with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, -1, by push_cast; ring_nf; rw [Complex.I_sq]; ring⟩
  obtain ⟨a', b', hab'⟩ : ∃ a b : ℤ, ∀ m n : ℤ, ((m : ℂ) + n * I) * u = (a * m - b * n : ℤ) +
      (b * m + a * n : ℤ) * I := by
    rcases hu with rfl | rfl
    · exact ⟨1, 0, fun m n => by push_cast; ring⟩
    · exact ⟨0, 1, fun m n => by push_cast; ring_nf; rw [Complex.I_sq]; ring⟩
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk0
  ext x
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · intro hx
    obtain ⟨m, n, rfl⟩ := repL x hx
    refine ⟨((m : ℂ) + n * I) * ((a + b * I) * μ), ?_, ?_⟩
    · exact gauss_mul_mem hΛI m n (gauss_mul_mem hΛI a b hμ)
    · rw [hμku]
      have : ((m : ℂ) + n * I) * ((a + b * I) * (k * u * ω)) =
          k * ((m + n * I) * ω) * (((a : ℂ) + b * I) * u) := by ring
      rw [this, hab]; push_cast; field_simp
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨m, n, rfl⟩ := repΛ y hy
    rw [hμku]
    have : (((1 / k : ℚ) : ℂ)) * (((m : ℂ) + n * I) * (k * u * ω)) =
        (((m : ℂ) + n * I) * u) * ω := by push_cast; field_simp
    rw [this, hab' m n]
    exact gauss_mul_mem hLI _ _ hω

/-- `μ = p (1 ± i) ω`: `L' = ((1 + i)/2) L = (1/(2p)) Λ`. -/
theorem latP_eq_of_mu {p : ℤ} (hp0 : p ≠ 0)
    (hμp : μ = p * (1 + I) * ω ∨ μ = p * (1 - I) * ω) :
    (latP L).lattice = Λ.map (LinearMap.mulLeft ℤ (((1 / (2 * p) : ℚ)) : ℂ)) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
  ext x
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply, ZInQ.GZWeil.mem_scalePP]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨m, n, rfl⟩ := repL y hy
    rcases hμp with hμp | hμp
    · refine ⟨((m : ℂ) + n * I) * μ, gauss_mul_mem hΛI m n hμ, ?_⟩
      rw [hμp]; push_cast; field_simp
    · refine ⟨(((-n : ℤ) : ℂ) + (m : ℤ) * I) * μ, gauss_mul_mem hΛI _ _ hμ, ?_⟩
      rw [hμp, lam]; push_cast; field_simp
      linear_combination (-((m : ℂ) + n) * ω) * Complex.I_sq
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨r, s, rfl⟩ := repΛ l hl
    rcases hμp with hμp | hμp
    · refine ⟨((r : ℂ) + s * I) * ω, gauss_mul_mem hLI r s hω, ?_⟩
      rw [hμp, lam]; push_cast; field_simp
    · refine ⟨(((s : ℤ) : ℂ) + ((-r : ℤ) : ℂ) * I) * ω, gauss_mul_mem hLI _ _ hω, ?_⟩
      rw [hμp, lam]; push_cast; field_simp
      linear_combination (((r : ℂ) - s) * ω) * Complex.I_sq

end Gauss

/-- **Classification.** Let `L` be a period lattice of `C_d` with `Λ_d ⊆ L` and `Λ_d ≠ 0`. Then
`L = c₀ Λ_d` (`c₀ ∈ ℚ`), or `L' = ((1 + i)/2) L = c Λ_d` (`c ∈ ℚ`). As in cd-optimal's
`lattice_eq_of_periods`: `L = ℤ[i] ω`, `Λ_d = ℤ[i] μ`, `μ = (p + q i) ω` with `q = 0`, `p = 0` or
`p = ±q`; the last two cases give `Λ_d = 2p L'`. -/
theorem lattice_cases {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L)
    (hU : LamCd d ≤ L.lattice) (hne : ∃ l ∈ LamCd d, l ≠ 0) :
    (∃ c₀ : ℚ, L.lattice = (LamCd d).map (LinearMap.mulLeft ℤ (c₀ : ℂ))) ∨
      (∃ c : ℚ, (latP L).lattice = (LamCd d).map (LinearMap.mulLeft ℤ (c : ℂ))) := by
  obtain ⟨l, hl, hl0⟩ := hne
  have hLI : ∀ y ∈ L.lattice, I * y ∈ L.lattice := fun y hy => I_mul_mem_of_cd hL hy
  have hΛI : ∀ y ∈ LamCd d, I * y ∈ LamCd d := fun y hy => I_mul_mem_LamCd d hy
  obtain ⟨μ, hμ, hμ0, hμmin⟩ := exists_min L (LamCd d) hU hl hl0
  obtain ⟨ω, hω, hω0, hωmin⟩ := exists_min L L.lattice le_rfl L.ω₁_mem_lattice (ω₁_ne_zero L)
  have repL := fun {ν : ℂ} (hν : ν ∈ L.lattice) => gauss_rep hLI hω hω0 hωmin hν
  have repΛ := fun {ν : ℂ} (hν : ν ∈ LamCd d) => gauss_rep hΛI hμ hμ0 hμmin hν
  obtain ⟨m₀, n₀, hc₀⟩ := repL (conj_mem_of_cd hL hω)
  obtain ⟨m₁, n₁, hc₁⟩ := repΛ (conj_mem_LamCd hd4 hsq hμ)
  have hu₀ : m₀ ^ 2 + n₀ ^ 2 = 1 :=
    gauss_norm_eq_one hω0 (by rw [← hc₀, Complex.norm_conj])
  have hu₁ : m₁ ^ 2 + n₁ ^ 2 = 1 :=
    gauss_norm_eq_one hμ0 (by rw [← hc₁, Complex.norm_conj])
  obtain ⟨p, q, hpq⟩ := repL (hU hμ)
  have hrel : ((p : ℂ) - q * I) * ((m₀ : ℂ) + n₀ * I) =
      ((m₁ : ℂ) + n₁ * I) * ((p : ℂ) + q * I) := by
    have h1 : (starRingEnd ℂ) μ = ((p : ℂ) - q * I) * ((m₀ : ℂ) + n₀ * I) * ω := by
      rw [hpq, map_mul, hc₀]; simp only [map_add, map_mul, map_intCast, Complex.conj_I]; ring
    have h2 : (starRingEnd ℂ) μ = ((m₁ : ℂ) + n₁ * I) * ((p : ℂ) + q * I) * ω := by
      rw [hc₁, hpq]; ring
    exact mul_right_cancel₀ hω0 (h1.symm.trans h2)
  have e1 : p * m₀ + q * n₀ = m₁ * p - n₁ * q := by
    have := congrArg Complex.re hrel
    simp at this
    exact_mod_cast this
  have e2 : p * n₀ - q * m₀ = m₁ * q + n₁ * p := by
    have := congrArg Complex.im hrel
    simp at this
    exact_mod_cast this
  have repL' : ∀ ν ∈ L.lattice, ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * ω := fun ν hν => repL hν
  have repΛ' : ∀ ν ∈ LamCd d, ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * μ := fun ν hν => repΛ hν
  rcases gauss_conj_cases hu₀ hu₁ e1 e2 with hq | hp | hpq' | hpq'
  · -- `μ = p ω`: `C_d` optimal
    have hp0 : p ≠ 0 := by rintro rfl; apply hμ0; rw [hpq, hq]; simp
    exact Or.inl ⟨_, lattice_eq_of_mu hLI hΛI hω hμ repL' repΛ' hp0 (Or.inl rfl)
      (by rw [hpq, hq]; push_cast; ring)⟩
  · -- `μ = q i ω`: `C_d` optimal
    have hq0 : q ≠ 0 := by rintro rfl; apply hμ0; rw [hpq, hp]; simp
    exact Or.inl ⟨_, lattice_eq_of_mu hLI hΛI hω hμ repL' repΛ' hq0 (Or.inr rfl)
      (by rw [hpq, hp]; push_cast; ring)⟩
  · -- `μ = p (1 − i) ω`: `E'_d` optimal
    have hp0 : p ≠ 0 := by
      rintro rfl
      have hq0 : q = 0 := by omega
      apply hμ0; rw [hpq, hq0]; simp
    exact Or.inr ⟨_, latP_eq_of_mu hLI hΛI hω hμ repL' repΛ' hp0
      (Or.inr (by rw [hpq, show q = -p by omega]; push_cast; ring))⟩
  · -- `μ = p (1 + i) ω`: `E'_d` optimal
    have hp0 : p ≠ 0 := by rintro rfl; apply hμ0; rw [hpq, ← hpq']; simp
    exact Or.inr ⟨_, latP_eq_of_mu hLI hΛI hω hμ repL' repΛ' hp0
      (Or.inl (by rw [hpq, ← hpq']; ring))⟩

/-! ## §2. The formula at `C_d` from the optimal leaf at `E'_d` -/

open ZInQ.GZHeegner (ParamSetting)
open ZInQ.Contrib.TYZGenus.CM (HeegnerForm)

section Core

variable {d : ℕ} (hd0 : d ≠ 0) (hodd : Odd d) (hsq : Squarefree d) {N : ℕ} [NeZero N]
  {f : Newform N 2} (hχ : f.χ = 1)
  (hcoeff : ∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ))
  {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) {c : ℚ}
  (hc : c ≠ 0) (hP : ZInQ.GZHL3.PeriodsIn f c L) {D β : ℤ} (hD : IsOddImagFundDisc D)
  (hD4 : D < -4) (hH : HeegnerHyp N D) (hβ : (4 * N : ℤ) ∣ D - β ^ 2) {R : Type} [Fintype R]
  {τ : R → UpperHalfPlane} (hτ : ZInQ.GZModuli.IsHeegnerPointReps N D β τ) {K : Type} [Field K]
  [NumberField K] [DecidableEq K] (hK : Module.finrank ℚ K = 2) {δ : K} (hδ : δ ^ 2 = (D : K))
  {ι : K →ₐ[ℚ] ℂ} (hι : ι δ = Complex.I * (Real.sqrt (-(D : ℝ)) : ℂ))
  (y : ((shortCurve (-(d : ℚ) ^ 2))⁄K).Point)
  (hy : Affine.Point.map ι y = ZInQ.GZHL3.weierPt (shortCurve (-(d : ℚ) ^ 2)) L
    (c * ∑ r, ZInQ.GZHL3.eichler f (τ r)))
  {F G : ℂ → ℂ} (hF : IsEntireCont (coeff f) 2 F) (hG : IsEntireCont (twistCoeff f D) 2 G)
include hd0 hodd hsq hχ hcoeff hL hc hP hD hD4 hH hβ hτ hK hδ hι hy hF hG

/-- **Core of the `E'_d` case**: `E'_d` is optimal (`L' = c' Λ_f`). With `P' = φ(y) ∈ E'_d(K)`,
`ι(P') = weierPt E'_d L' (c u) = n · y_K(φ_opt)` (`c = n c'`), the leaf at `E'_d` gives
`L'(E/K, 1) = κ' ĥ(P')`, and `y`, `P'` are torsion together (`L ⊆ L' ⊆ ½ L`). -/
theorem core_isog (hGZ : GrossZagierModuliOptAt (ePrime d)) {c' : ℚ}
    (hlat' : (latP L).lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c' : ℂ))) :
    ∃ κ : ℝ, 0 < κ ∧ deriv (fun s => F s * G s) 1 = κ * y.canonicalHeight := by
  have hEc := ZInQ.GZDecomp.shortCurve_cd_isElliptic hd0
  have hEe := ePrime_isElliptic hd0
  have hLI : ∀ y ∈ L.lattice, I * y ∈ L.lattice := fun y hy => I_mul_mem_of_cd hL hy
  have hL' := isPeriodLattice_ePrime hL
  have hc' := ne_zero_of_lattice hlat'
  have hcoeff' : ∀ n : ℕ, n ≠ 0 → coeff f n = ((ePrime d).LFunction n : ℂ) := fun n hn => by
    rw [hcoeff n hn, LFunction_ePrime_eq hodd hsq]
  have hs' : ParamSetting (ePrime d) f (latP L) c' :=
    ⟨hχ, hcoeff', hL', hc', periodsIn_of_lattice hlat'⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, c / c' = n := by
    apply rat_mem_int (L := latP L)
    have h1 := (latP L).ω₁_mem_lattice
    rw [hlat'] at h1
    obtain ⟨w, hw, hw1⟩ := h1
    have : ((c / c' : ℚ) : ℂ) * (latP L).ω₁ = c * w := by
      rw [← hw1]; simp only [LinearMap.mulLeft_apply]; push_cast; field_simp
    rw [this]
    exact le_latP hLI (mul_mem_of_periodsIn hP hw)
  have hcn : (c : ℂ) = n * c' := by
    have : c = n * c' := by rw [← hn]; field_simp
    exact_mod_cast this
  have hn0 : n ≠ 0 := by
    rintro rfl; apply hc; simpa using hcn
  set u : ℂ := ∑ r, ZInQ.GZHL3.eichler f (τ r) with hu
  have hP'w : Affine.Point.map ι (isogPt hd0 y) = ZInQ.GZHL3.weierPt (ePrime d) (latP L) (c * u) := by
    rw [map_isogPt, hy, weierPt_ePrime_eq hd0 hL]
  have hP'u : Affine.Point.map ι (isogPt hd0 y) =
      ZInQ.GZHL3.weierPt (ePrime d) (latP L) (n * (c' * u)) := by
    rw [hP'w, hcn, mul_assoc]
  obtain ⟨κ', hκ', hA⟩ := hGZ N f hχ hcoeff' _ _ (ZInQ.GZModuli.isModularParam_of hs')
    ⟨latP L, c', hL', hlat', ZInQ.GZModuli.modPt_eq hs'⟩ D β hD hD4 hH hβ R τ hτ K hK δ hδ ι hι n
    hn0 (isogPt hd0 y)
    (by rw [hP'u, sum_modPt_eq' (short_ePrime d) hs', weierPt_zsmul (short_ePrime d) hL'])
    F G hF hG
  refine exists_pos_of_torsion_iff y (isogPt hd0 y) hκ' hA ?_
  rw [isOfFinAddOrder_iff (short_cd d) hL ι y hy,
    isOfFinAddOrder_iff (short_ePrime d) hL' ι (isogPt hd0 y) hP'w]
  constructor
  · rintro ⟨k, hk, hm⟩
    exact ⟨k, hk, le_latP hLI hm⟩
  · rintro ⟨k, hk, hm⟩
    refine ⟨2 * k, by omega, ?_⟩
    obtain ⟨y', hy', e⟩ := (ZInQ.GZWeil.mem_scalePP lam_ne_zero).mp hm
    have e2 : ((2 * k : ℕ) : ℂ) * (c * u) = y' + I * y' := by
      push_cast
      rw [mul_assoc, e, lam]; ring
    rw [e2]
    exact add_mem hy' (hLI y' hy')

end Core

/-- **`C_d` or its 2-isogenous curve `E'_d : y² = x³ + 4d² x` is the strong Weil curve** (up to a
rational factor), from the eta-quotient law alone: for the newform `f` of `C_d` and a period lattice
`L` of `C_d`, either `L = c₀ Λ_f`, or `L' = ((1 + i)/2) L`, a period lattice of `E'_d`, is `c Λ_f`
(`c₀, c ∈ ℚ`). cd-optimal's `CdTwistedPeriodOdd` is what selects the first case; it is not needed for
the Gross–Zagier formula (`grossZagierFormulaCd_of_etaW32`). -/
theorem cd_or_ePrime_optimal (hW : EtaW32Character) {d : ℕ} (hd8 : d % 8 = 5) (hsq : Squarefree d)
    {N : ℕ} [NeZero N] (f : Newform N 2) (hχ : f.χ = 1)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ))
    {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) :
    (∃ c₀ : ℚ, L.lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c₀ : ℂ))) ∨
      (ZInQ.GZHL3.IsPeriodLattice (ePrime d) (latP L) ∧
        ∃ c : ℚ, (latP L).lattice = (periodLattice f).map (LinearMap.mulLeft ℤ (c : ℂ))) := by
  have hd4 : d % 4 = 1 := by omega
  have hΛ := periodLattice_eq_LamCd hd4 hsq f hχ hcoeff
  have hne : ∃ l ∈ LamCd d, l ≠ 0 := by rw [← hΛ]; exact periodLattice_ne_zero f
  rw [hΛ]
  rcases lattice_cases hd4 hsq hL (LamCd_le_of_etaW32 hW hd4 (by omega) hsq hL) hne with h | h
  · exact Or.inl h
  · exact Or.inr ⟨isPeriodLattice_ePrime hL, h⟩

/-! ## §3. The consumer -/

/-- **`GZHL3.GrossZagierFormulaCd` from gz-optimal's optimal-parametrization leaf, the eta-quotient
transformation law**: cd-optimal's route A without `CdTwistedPeriodOdd` (`Λ_d ≠ 0`:
`periodLattice_ne_zero`). Either
`C_d` is optimal (route A, `core_selfOptimal`) or `E'_d` is (`core_isog`). -/
theorem grossZagierFormulaCd_of_etaW32 (hGZ : GrossZagierModuliOptCd) (hW : EtaW32Character) :
    ZInQ.GZHL3.GrossZagierFormulaCd := fun d hd8 hsq => by
  have hd0 : d ≠ 0 := by omega
  have hd4 : d % 4 = 1 := by omega
  have hd1 : 1 < d := by omega
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  have := ZInQ.GZDecomp.shortCurve_cd_isElliptic hd0
  intro N _ f hχ hcoeff D β hD hD4 hH hβ S hS L c hL hc hP K _ _ _ hK δ hδ ι hι y hy F G hF hG
  have hΛ := periodLattice_eq_LamCd hd4 hsq f hχ hcoeff
  have hU := LamCd_le_of_etaW32 hW hd4 hd1 hsq hL
  have hτ := ZInQ.GZModuli.isHeegnerPointReps_of hD hS
  have hy' := (by rw [hy, heegnerC_eq (short_cd d) hL] :
    Affine.Point.map ι y = ZInQ.GZHL3.weierPt (shortCurve (-(d : ℚ) ^ 2)) L
      (c * ∑ r : S, ZInQ.GZHL3.eichler f r.1.tauH))
  have hne : ∃ l ∈ LamCd d, l ≠ 0 := by rw [← hΛ]; exact periodLattice_ne_zero f
  rcases lattice_cases hd4 hsq hL hU hne with ⟨c₀, hlat⟩ | ⟨c', hlat'⟩
  · rw [← hΛ] at hlat
    exact core_selfOptimal (short_cd d) hχ hcoeff hL hc hP hD hD4 hH hβ hτ hK hδ hι y hy' hF hG
      (hGZ d hd8 hsq _ (short_cd d) fun _ _ => rfl) hlat
  · rw [← hΛ] at hlat'
    have hEe := ePrime_isElliptic hd0
    exact core_isog hd0 hodd hsq hχ hcoeff hL hc hP hD hD4 hH hβ hτ hK hδ hι y hy' hF hG
      (hGZ d hd8 hsq (ePrime d) (short_ePrime d) fun n _ => by
        rw [LFunction_ePrime_eq hodd hsq]) hlat'

end ZInQ.PeriodOdd
