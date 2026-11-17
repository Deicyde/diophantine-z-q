import ZInQKernel.Contrib.OneProof.CdOptimal.Unif
import ZInQKernel.Contrib.OneProof.GrossZagierOptimal

/-!
# cd-optimal: the period lattice of `f_d` is a `ℤ[i]`-module stable under complex conjugation

Task cd-optimal (2026-11-16). Report: `docs/research/cd-optimal.md`; log: `scratch/cd-optimal/log.md`.

`Λ_d` (`LamCd d`) is the subgroup of `ℂ` spanned by the periods `Φ_d(γτ) − Φ_d(τ)`, `γ ∈ Γ₀(32d²)`, of
gz-weil's Eichler integral `Φ_d = Σ heckeCoeff d n / n · qⁿ` (for a newform `f` of `C_d` it is
gz-optimal's `periodLattice f`: `periodLattice_eq_LamCd`).

* `Φ_d(τ + 1/4) = i Φ_d(τ)` (`aₙ = 0` unless `n ≡ 1 mod 4`), and `γ ↦ T^{1/4} γ T^{-1/4}` preserves
  `Γ₀(32d²)`: `i Λ_d ⊆ Λ_d` (`I_mul_mem_LamCd`).
* `aₙ ∈ ℤ`, so `conj Φ_d(τ) = Φ_d(−τ̄)`, and `γ ↦ diag(1,−1) γ diag(1,−1)` preserves `Γ₀(32d²)`:
  `conj Λ_d ⊆ Λ_d` (`conj_mem_LamCd`).
* every period lattice `L` of `C_d` is `i`-stable and conjugation-stable (uniqueness of the lattice,
  `Unif.lean`).
* a lattice stable under `i` is `ℤ[i] ω` for a shortest `ω` (Gaussian rounding); stability under
  conjugation forces the ratio of two such generators into `ℤ · {1, i, 1 ± i}`.

Hence (`lattice_eq_of_periods`): if `Λ_d ⊆ L` and some period is not in `(1 + i) L`, then `L = c₀ Λ_d`
with `c₀ ∈ ℚ`. No `sorry`, no `axiom`.
-/

noncomputable section

open Complex CongruenceSubgroup Filter Topology
open scoped UpperHalfPlane
open ZInQ.Contrib.HeckeFE (heckeCoeff unitOf normFiber mem_normFiber gz)
open ZInQ.GZWeil (eichlerCd)
open Matrix.GeneralLinearGroup (upperRightHom)
open Matrix.SpecialLinearGroup (mapGL)
open scoped MatrixGroups ComplexConjugate

namespace ZInQ.CdOpt

/-! ## §1. `aₙ(C_d) = 0` unless `n ≡ 1 (mod 4)` -/

theorem unitOf_eq_zero {t : ZMod 4 × ZMod 4} (h : t.1 ^ 2 + t.2 ^ 2 ≠ 1) : unitOf t = 0 := by
  obtain ⟨a, b⟩ := t
  fin_cases a <;> fin_cases b <;> first | (simp (config := {decide := true}) [unitOf]; done) |
    exact absurd h (by decide)

theorem heckeCoeff_eq_zero (d : ℕ) {n : ℕ} (hn : n % 4 ≠ 1) : heckeCoeff d n = 0 := by
  unfold heckeCoeff
  rw [Finset.sum_eq_zero, mul_zero]
  intro p hp
  have hp' := mem_normFiber.mp hp
  rw [unitOf_eq_zero, mul_zero, zero_mul]
  intro h
  apply hn
  have h1 : (((p.1 ^ 2 + p.2 ^ 2 : ℤ)) : ZMod 4) = 1 := by push_cast; exact h
  rw [hp'] at h1
  have h2 : ((n : ℕ) : ZMod 4) = 1 := by exact_mod_cast h1
  have := ZMod.val_natCast (n := 4) n
  rw [h2] at this
  rw [← this]; rfl

/-! ## §2. `Φ_d(z + 1/4) = i Φ_d(z)` and `conj Φ_d(z) = Φ_d(−z̄)` -/

theorem eichlerCd_add_quarter (d : ℕ) (z : ℂ) : eichlerCd d (z + 1 / 4) = I * eichlerCd d z := by
  unfold eichlerCd
  rw [← tsum_mul_left]
  congr 1
  funext n
  by_cases h : (n + 1) % 4 = 1
  · obtain ⟨k, hk⟩ : ∃ k, n = 4 * k := ⟨n / 4, by omega⟩
    have he : cexp (2 * Real.pi * I * ((n : ℂ) + 1) * (z + 1 / 4)) =
        I * cexp (2 * Real.pi * I * ((n : ℂ) + 1) * z) := by
      have : 2 * Real.pi * I * ((n : ℂ) + 1) * (z + 1 / 4) =
          2 * Real.pi * I * ((n : ℂ) + 1) * z + ((k : ℕ) * (2 * Real.pi * I) + Real.pi / 2 * I) := by
        rw [hk]; push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I,
        Complex.exp_pi_div_two_mul_I]
      ring
    rw [he]; ring
  · rw [heckeCoeff_eq_zero d h]; simp

theorem heckeCoeff_conj {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {n : ℕ} (hn : n ≠ 0) :
    conj (heckeCoeff d n) = heckeCoeff d n := by
  rw [← ZInQ.GZStatements.LFunction_cd_eq_heckeCoeff hd4 hsq hn]
  exact map_intCast _ _

theorem conj_eichlerCd {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) (z : ℂ) :
    conj (eichlerCd d z) = eichlerCd d (-conj z) := by
  unfold eichlerCd
  rw [Complex.conj_tsum]
  congr 1
  funext n
  rw [map_mul, map_div₀, heckeCoeff_conj hd4 hsq (Nat.succ_ne_zero n), ← Complex.exp_conj]
  congr 2
  · simp
  · simp only [map_mul, map_add, map_natCast, map_one, Complex.conj_ofReal, Complex.conj_I,
      map_ofNat]
    ring

/-! ## §3. The period lattice `Λ_d` -/

/-- **`Λ_d`**: the subgroup of `ℂ` spanned by the periods `Φ_d(γτ) − Φ_d(τ)`, `γ ∈ Γ₀(32 d²)`,
`τ ∈ ℍ`. -/
def LamCd (d : ℕ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {w | ∃ γ ∈ Gamma0 (32 * d ^ 2), ∃ τ : ℍ,
    w = eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ)}

/-- For a newform `f` of `C_d`, gz-optimal's `periodLattice f` is `Λ_d` (level `32 d²`, Eichler
integral `Φ_d`). -/
theorem periodLattice_eq_LamCd {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {N : ℕ} [NeZero N]
    (f : HeckeRing.GL2.Newform N 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ)) :
    ZInQ.GZOptimal.periodLattice f = LamCd d := by
  have hN := ZInQ.GZStatements.level_eq_of_coeff_cd hd4 hsq f hχ hf
  subst hN
  unfold ZInQ.GZOptimal.periodLattice LamCd
  congr 1
  ext w
  simp only [Set.mem_ofPred_eq, ZInQ.GZWeil.eichler_eq_eichlerCd hd4 hsq f hf]

theorem gamma0_data {d : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (32 * d ^ 2)) :
    ∃ k : ℤ, γ 1 0 = 32 * d ^ 2 * k ∧ γ 1 1 % 2 = 1 := by
  rw [Gamma0_mem] at hγ
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) (32 * d ^ 2)).1 hγ
  refine ⟨k, by exact_mod_cast hk, ?_⟩
  have hdet0 : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  rw [hk] at hdet0
  have hodd : Odd (γ 0 0 * γ 1 1) :=
    ⟨16 * (γ 0 1 * d ^ 2 * k), by push_cast at hdet0; linear_combination hdet0⟩
  exact Int.odd_iff.1 (Int.odd_mul.1 hodd).2

theorem sq_odd_zmod4 {e : ℤ} (he : e % 2 = 1) : ((e : ZMod 4)) ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, e = 2 * m + 1 := ⟨e / 2, by omega⟩
  have : ((2 * m + 1 : ℤ) : ZMod 4) ^ 2 = (((4 * (m ^ 2 + m) + 1 : ℤ)) : ZMod 4) := by
    push_cast; ring
  rw [this]
  push_cast
  rw [show (4 : ZMod 4) = 0 from rfl]
  ring

/-- **`i Λ_d ⊆ Λ_d`.** -/
theorem I_mul_mem_LamCd (d : ℕ) {w : ℂ} (hw : w ∈ LamCd d) : I * w ∈ LamCd d := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, τ, rfl⟩ := hx
    obtain ⟨k, hk, hodd⟩ := gamma0_data hγ
    obtain ⟨γ', -, hγ'1, -, hγ'eq⟩ :=
      TauCeti.exists_upperRightHom_mul_mapGL_eq_mapGL_mul_upperRightHom (M := 4) γ
        (c := 2 * d ^ 2 * k) (a := 1) (a' := 1) (by rw [hk]; push_cast; ring)
        (by push_cast; rw [sq_odd_zmod4 hodd]; ring)
    set τ' : ℍ := (((1 : ℤ) : ℝ) / (4 : ℕ)) +ᵥ τ with hτ'
    have hmove : ((γ • τ : ℍ) : ℂ) + 1 / 4 = ((γ' • τ' : ℍ) : ℂ) := by
      have h := congrArg (fun g : GL (Fin 2) ℝ => g • τ) hγ'eq
      simp only [mul_smul, TauCeti.Matrix.GeneralLinearGroup.upperRightHom_smul] at h
      have h' := congrArg (fun z : ℍ => (z : ℂ)) h
      simp only [UpperHalfPlane.coe_vadd] at h'
      rw [ModularGroup.sl_moeb, ModularGroup.sl_moeb, TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL,
        TauCeti.Matrix.SpecialLinearGroup.coe_GL_eq_mapGL, ← h']
      push_cast
      ring
    have hτc : ((τ' : ℍ) : ℂ) = (τ : ℂ) + 1 / 4 := by
      rw [hτ', UpperHalfPlane.coe_vadd]; push_cast; ring
    refine Submodule.subset_span ⟨γ', ?_, τ', ?_⟩
    · rw [Gamma0_mem, hγ'1]; exact (Gamma0_mem.mp hγ)
    · rw [← hmove, hτc, eichlerCd_add_quarter, eichlerCd_add_quarter]; ring
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | smul n x _ hx =>
    rw [show I * (n • x) = n • (I * x) by rw [zsmul_eq_mul, zsmul_eq_mul]; ring]
    exact Submodule.smul_mem _ n hx

/-- `diag(1, −1) γ diag(1, −1)`. -/
def flipSL (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this
    rw [Matrix.det_fin_two_of]; linear_combination this⟩

/-- `−τ̄`. -/
def negConj (τ : ℍ) : ℍ := ⟨-conj (τ : ℂ), by simpa using τ.im_pos⟩

theorem negConj_coe (τ : ℍ) : ((negConj τ : ℍ) : ℂ) = -conj (τ : ℂ) := rfl

theorem flip_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((flipSL γ • negConj τ : ℍ) : ℂ) = -conj ((γ • τ : ℍ) : ℂ) := by
  rw [ZInQ.GZWeil.coe_smul_eq_moeb, ZInQ.GZWeil.coe_smul_eq_moeb]
  simp only [ZInQ.GZWeil.moeb, flipSL, negConj, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, map_div₀, map_add, map_mul, map_intCast, Int.cast_neg]
  ring

/-- **`conj Λ_d ⊆ Λ_d`.** -/
theorem conj_mem_LamCd {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {w : ℂ}
    (hw : w ∈ LamCd d) : conj w ∈ LamCd d := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, τ, rfl⟩ := hx
    refine Submodule.subset_span ⟨flipSL γ, ?_, negConj τ, ?_⟩
    · rw [Gamma0_mem] at hγ ⊢
      simp only [flipSL, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
        Int.cast_neg, hγ, neg_zero]
    · rw [map_sub, conj_eichlerCd hd4 hsq, conj_eichlerCd hd4 hsq, flip_smul]
      rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul n x _ hx =>
    rw [show conj (n • x) = n • conj x by rw [zsmul_eq_mul, zsmul_eq_mul, map_mul, map_intCast]]
    exact Submodule.smul_mem _ n hx

/-! ## §4. Lattices stable under `i`: Gaussian rounding -/

section Gauss

variable (L : PeriodPair)

theorem finite_ball (R : ℝ) : {x : ℂ | x ∈ L.lattice ∧ ‖x‖ ≤ R}.Finite := by
  have h := ZSpan.setFinite_inter L.basis (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R))
  refine h.subset fun x hx => ⟨mem_closedBall_zero_iff.2 hx.2, ?_⟩
  have := hx.1
  rw [L.lattice_eq_span_range_basis] at this
  exact this

/-- A shortest nonzero vector of a nonzero subgroup `Λ ⊆ L`. -/
theorem exists_min (Λ : Submodule ℤ ℂ) (hΛ : Λ ≤ L.lattice) {x : ℂ} (hx : x ∈ Λ) (hx0 : x ≠ 0) :
    ∃ μ ∈ Λ, μ ≠ 0 ∧ ∀ ν ∈ Λ, ν ≠ 0 → ‖μ‖ ≤ ‖ν‖ := by
  set S : Set ℂ := {y | y ∈ Λ ∧ y ≠ 0 ∧ ‖y‖ ≤ ‖x‖} with hSdef
  have hS : S.Finite := (finite_ball L ‖x‖).subset fun y hy => ⟨hΛ hy.1, hy.2.2⟩
  obtain ⟨μ, hμS, hmin⟩ := Set.exists_min_image S (fun y => ‖y‖) hS ⟨x, hx, hx0, le_rfl⟩
  refine ⟨μ, hμS.1, hμS.2.1, fun ν hν hν0 => ?_⟩
  by_cases h : ‖ν‖ ≤ ‖x‖
  · exact hmin ν ⟨hν, hν0, h⟩
  · push Not at h
    linarith [hμS.2.2]

/-- `Λ` is closed under multiplication by Gaussian integers if it is closed under `i`. -/
theorem gauss_mul_mem {Λ : Submodule ℤ ℂ} (hI : ∀ y ∈ Λ, I * y ∈ Λ) (m n : ℤ) {y : ℂ}
    (hy : y ∈ Λ) : ((m : ℂ) + n * I) * y ∈ Λ := by
  have h1 : ((m : ℂ) + n * I) * y = m • y + n • (I * y) := by
    simp only [zsmul_eq_mul]; ring
  rw [h1]
  exact add_mem (Λ.smul_mem m hy) (Λ.smul_mem n (hI y hy))

theorem norm_sub_gauss_lt (z : ℂ) : ‖z - ((round z.re : ℤ) + (round z.im : ℤ) * I)‖ < 1 := by
  have hre := abs_sub_round z.re
  have him := abs_sub_round z.im
  set w := z - ((round z.re : ℤ) + (round z.im : ℤ) * I) with hw
  have hwre : w.re = z.re - round z.re := by simp [hw]
  have hwim : w.im = z.im - round z.im := by simp [hw]
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : w.re ^ 2 ≤ 1 / 4 := by
    rw [hwre]; have := abs_le.mp hre; nlinarith
  have h2 : w.im ^ 2 ≤ 1 / 4 := by
    rw [hwim]; have := abs_le.mp him; nlinarith
  by_contra h
  push Not at h
  nlinarith [norm_nonneg w]

/-- **Gaussian rounding.** If `Λ` is closed under `i` and `μ` is a shortest nonzero vector of `Λ`,
then `Λ = ℤ[i] μ`. -/
theorem gauss_rep {Λ : Submodule ℤ ℂ} (hI : ∀ y ∈ Λ, I * y ∈ Λ) {μ : ℂ} (hμ : μ ∈ Λ)
    (hμ0 : μ ≠ 0) (hmin : ∀ ν ∈ Λ, ν ≠ 0 → ‖μ‖ ≤ ‖ν‖) {ν : ℂ} (hν : ν ∈ Λ) :
    ∃ m n : ℤ, ν = ((m : ℂ) + n * I) * μ := by
  set z := ν / μ with hz
  refine ⟨round z.re, round z.im, ?_⟩
  set g : ℂ := ((round z.re : ℤ) : ℂ) + ((round z.im : ℤ) : ℂ) * I with hg
  have hmem : ν - g * μ ∈ Λ := sub_mem hν (gauss_mul_mem hI _ _ hμ)
  by_contra hne
  have hne' : ν - g * μ ≠ 0 := sub_ne_zero.mpr hne
  have h2 := hmin _ hmem hne'
  have heq : ν - g * μ = (z - g) * μ := by rw [hz]; field_simp
  rw [heq, norm_mul] at h2
  have hμpos : 0 < ‖μ‖ := norm_pos_iff.mpr hμ0
  have hlt := norm_sub_gauss_lt z
  nlinarith

end Gauss

/-- The units of `ℤ[i]`. -/
theorem unit_cases {m n : ℤ} (h : m ^ 2 + n ^ 2 = 1) :
    (m = 1 ∧ n = 0) ∨ (m = -1 ∧ n = 0) ∨ (m = 0 ∧ n = 1) ∨ (m = 0 ∧ n = -1) := by
  have hm : m ^ 2 ≤ 1 := by nlinarith [sq_nonneg n]
  have hn : n ^ 2 ≤ 1 := by nlinarith [sq_nonneg m]
  have hm' : -1 ≤ m ∧ m ≤ 1 := by constructor <;> nlinarith
  have hn' : -1 ≤ n ∧ n ≤ 1 := by constructor <;> nlinarith
  obtain ⟨hm1, hm2⟩ := hm'
  obtain ⟨hn1, hn2⟩ := hn'
  interval_cases m <;> interval_cases n <;> simp_all

theorem gauss_norm_eq_one {m n : ℤ} {ω : ℂ} (hω : ω ≠ 0)
    (h : ‖((m : ℂ) + n * I) * ω‖ = ‖ω‖) : m ^ 2 + n ^ 2 = 1 := by
  rw [norm_mul] at h
  have hω' : 0 < ‖ω‖ := norm_pos_iff.mpr hω
  have h1 : ‖((m : ℂ) + n * I)‖ = 1 := by
    have := mul_right_cancel₀ hω'.ne' (h.trans (one_mul _).symm)
    exact this
  have h2 : ‖((m : ℂ) + n * I)‖ ^ 2 = (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [h1] at h2
  have : ((m ^ 2 + n ^ 2 : ℤ) : ℝ) = 1 := by push_cast; linarith
  exact_mod_cast this

/-! ## §5. The conjugate and `i`-rotated lattices -/

/-- The period pair `(ω̄₁, ω̄₂)`. -/
def conjPP (L : PeriodPair) : PeriodPair where
  ω₁ := conj L.ω₁
  ω₂ := conj L.ω₂
  indep := by
    have hinj : Function.Injective (Complex.conjLIE.toLinearEquiv.toLinearMap : ℂ →ₗ[ℝ] ℂ) :=
      Complex.conjLIE.injective
    have := L.indep.map' _ (LinearMap.ker_eq_bot.mpr hinj)
    convert this using 1
    ext i
    fin_cases i <;> simp

theorem mem_conjPP {L : PeriodPair} {x : ℂ} :
    x ∈ (conjPP L).lattice ↔ ∃ y ∈ L.lattice, x = conj y := by
  simp only [PeriodPair.mem_lattice, conjPP]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m * L.ω₁ + n * L.ω₂, ⟨m, n, rfl⟩, by simp⟩
  · rintro ⟨y, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by simp⟩

theorem G_conjPP (L : PeriodPair) (n : ℕ) : (conjPP L).G n = conj (L.G n) := by
  let e : L.lattice ≃ (conjPP L).lattice :=
    { toFun := fun l => ⟨conj l, mem_conjPP.mpr ⟨l, l.2, rfl⟩⟩
      invFun := fun l => ⟨conj l, by
        obtain ⟨y, hy, hl⟩ := mem_conjPP.mp l.2
        rw [hl, Complex.conj_conj]; exact hy⟩
      left_inv := fun l => by ext; simp
      right_inv := fun l => by ext; simp }
  rw [PeriodPair.G, PeriodPair.G, ← e.tsum_eq, Complex.conj_tsum]
  congr 1
  funext l
  simp [e, map_pow, map_inv₀]

theorem g₂_conjPP (L : PeriodPair) : (conjPP L).g₂ = conj L.g₂ := by
  rw [PeriodPair.g₂, PeriodPair.g₂, G_conjPP, map_mul, map_ofNat]

theorem g₃_conjPP (L : PeriodPair) : (conjPP L).g₃ = conj L.g₃ := by
  rw [PeriodPair.g₃, PeriodPair.g₃, G_conjPP, map_mul, map_ofNat]

/-- A period lattice of `C_d` is stable under `i`. -/
theorem I_mul_mem_of_cd {d : ℕ} {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) {y : ℂ}
    (hy : y ∈ L.lattice) : I * y ∈ L.lattice := by
  obtain ⟨h2, h3⟩ := (ZInQ.GZWeil.isPeriodLattice_cd_iff d L).mp hL
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have heq := lattice_eq_of_g₂_g₃ (L := ZInQ.GZWeil.scalePP L I hI) (L' := L)
    (by rw [ZInQ.GZWeil.g₂_scalePP]; simp [show I ^ 4 = (1 : ℂ) by norm_num [pow_succ]])
    (by rw [ZInQ.GZWeil.g₃_scalePP, h3, mul_zero])
  rw [← heq]
  exact (ZInQ.GZWeil.mem_scalePP hI).mpr ⟨y, hy, rfl⟩

/-- A period lattice of `C_d` is stable under complex conjugation. -/
theorem conj_mem_of_cd {d : ℕ} {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) {y : ℂ}
    (hy : y ∈ L.lattice) : conj y ∈ L.lattice := by
  obtain ⟨h2, h3⟩ := (ZInQ.GZWeil.isPeriodLattice_cd_iff d L).mp hL
  have heq := lattice_eq_of_g₂_g₃ (L := conjPP L) (L' := L)
    (by rw [g₂_conjPP, h2]; simp [map_ofNat])
    (by rw [g₃_conjPP, h3, map_zero])
  rw [← heq]
  exact mem_conjPP.mpr ⟨y, hy, rfl⟩

/-! ## §6. The classification -/

/-- The four possibilities for a Gaussian integer `p + q i` with `(p + qi)` stable under
conjugation up to units: `q = 0`, `p = 0`, `p = −q`, `p = q`. -/
theorem gauss_conj_cases {p q m₀ n₀ m₁ n₁ : ℤ} (h₀ : m₀ ^ 2 + n₀ ^ 2 = 1)
    (h₁ : m₁ ^ 2 + n₁ ^ 2 = 1) (e1 : p * m₀ + q * n₀ = m₁ * p - n₁ * q)
    (e2 : p * n₀ - q * m₀ = m₁ * q + n₁ * p) : q = 0 ∨ p = 0 ∨ p = -q ∨ p = q := by
  rcases unit_cases h₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases unit_cases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

/-- **Classification.** Let `L` be a period lattice of `C_d`. If every period of `f_d` lies in `L`
(`Λ_d ⊆ L`) and some period is not in `(1 + i) L`, then `L = c₀ Λ_d` for a rational `c₀`.

Both lattices are `ℤ[i]`-modules (`I_mul_mem_LamCd`, `I_mul_mem_of_cd`), so `L = ℤ[i] ω`,
`Λ_d = ℤ[i] μ` for shortest vectors, `μ = (p + q i) ω`; both are stable under conjugation
(`conj_mem_LamCd`, `conj_mem_of_cd`), which forces `p + qi ∈ ℤ · {1, i, 1 ± i}`; the last two
cases put `Λ_d` inside `(1 + i) L`. -/
theorem lattice_eq_of_periods {d : ℕ} (hd4 : d % 4 = 1) (hsq : Squarefree d) {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L)
    (hU : LamCd d ≤ L.lattice)
    (hN : ∃ l ∈ LamCd d, l ∉ L.lattice.map (LinearMap.mulLeft ℤ (1 + I))) :
    ∃ c₀ : ℚ, L.lattice = (LamCd d).map (LinearMap.mulLeft ℤ (c₀ : ℂ)) := by
  obtain ⟨l, hl, hlN⟩ := hN
  have hl0 : l ≠ 0 := by
    rintro rfl; exact hlN ⟨0, L.lattice.zero_mem, by simp⟩
  have hLI : ∀ y ∈ L.lattice, I * y ∈ L.lattice := fun y hy => I_mul_mem_of_cd hL hy
  have hΛI : ∀ y ∈ LamCd d, I * y ∈ LamCd d := fun y hy => I_mul_mem_LamCd d hy
  -- shortest vectors
  obtain ⟨μ, hμ, hμ0, hμmin⟩ := exists_min L (LamCd d) hU hl hl0
  have hω₁0 : L.ω₁ ≠ 0 := ZInQ.GZOptimal.ω₁_ne_zero L
  obtain ⟨ω, hω, hω0, hωmin⟩ := exists_min L L.lattice le_rfl L.ω₁_mem_lattice hω₁0
  have repL := fun {ν : ℂ} (hν : ν ∈ L.lattice) => gauss_rep hLI hω hω0 hωmin hν
  have repΛ := fun {ν : ℂ} (hν : ν ∈ LamCd d) => gauss_rep hΛI hμ hμ0 hμmin hν
  -- conjugates
  obtain ⟨m₀, n₀, hc₀⟩ := repL (conj_mem_of_cd hL hω)
  obtain ⟨m₁, n₁, hc₁⟩ := repΛ (conj_mem_LamCd hd4 hsq hμ)
  have hu₀ : m₀ ^ 2 + n₀ ^ 2 = 1 :=
    gauss_norm_eq_one hω0 (by rw [← hc₀, Complex.norm_conj])
  have hu₁ : m₁ ^ 2 + n₁ ^ 2 = 1 :=
    gauss_norm_eq_one hμ0 (by rw [← hc₁, Complex.norm_conj])
  obtain ⟨p, q, hpq⟩ := repL (hU hμ)
  -- `(p − q i)(m₀ + n₀ i) = (m₁ + n₁ i)(p + q i)`
  have hrel : ((p : ℂ) - q * I) * ((m₀ : ℂ) + n₀ * I) = ((m₁ : ℂ) + n₁ * I) * ((p : ℂ) + q * I) := by
    have h1 : conj μ = ((p : ℂ) - q * I) * ((m₀ : ℂ) + n₀ * I) * ω := by
      rw [hpq, map_mul, hc₀]; simp only [map_add, map_mul, map_intCast, Complex.conj_I]; ring
    have h2 : conj μ = ((m₁ : ℂ) + n₁ * I) * ((p : ℂ) + q * I) * ω := by rw [hc₁, hpq]; ring
    exact mul_right_cancel₀ hω0 (h1.symm.trans h2)
  have e1 : p * m₀ + q * n₀ = m₁ * p - n₁ * q := by
    have := congrArg Complex.re hrel
    simp at this
    exact_mod_cast this
  have e2 : p * n₀ - q * m₀ = m₁ * q + n₁ * p := by
    have := congrArg Complex.im hrel
    simp at this
    exact_mod_cast this
  -- `μ = k u ω` with `u ∈ {1, i}`
  obtain ⟨k, u, hk0, hu, hμku⟩ : ∃ (k : ℤ) (u : ℂ), k ≠ 0 ∧ (u = 1 ∨ u = I) ∧ μ = k * u * ω := by
    rcases gauss_conj_cases hu₀ hu₁ e1 e2 with hq | hp | hpq' | hpq'
    · refine ⟨p, 1, ?_, Or.inl rfl, by rw [hpq, hq]; push_cast; ring⟩
      rintro rfl; apply hμ0; rw [hpq, hq]; simp
    · refine ⟨q, I, ?_, Or.inr rfl, by rw [hpq, hp]; push_cast; ring⟩
      rintro rfl; apply hμ0; rw [hpq, hp]; simp
    · exfalso
      obtain ⟨r, s, hrs⟩ := repΛ hl
      apply hlN
      refine ⟨-I * (((r : ℂ) + s * I) * (p * ω)), ?_, ?_⟩
      · have h1 : ((r : ℂ) + s * I) * (p * ω) ∈ L.lattice :=
          gauss_mul_mem hLI r s (by have := L.lattice.smul_mem p hω; rwa [zsmul_eq_mul] at this)
        have h2 := hLI _ (hLI _ (hLI _ h1))
        have hI3 : I * (I * (I * (((r : ℂ) + s * I) * (p * ω)))) =
            -I * (((r : ℂ) + s * I) * (p * ω)) := by
          linear_combination (I * (((r : ℂ) + s * I) * (p * ω))) * Complex.I_sq
        rw [← hI3]; exact h2
      · simp only [LinearMap.mulLeft_apply]
        rw [hrs, hpq]
        subst hpq'
        push_cast
        linear_combination (((r : ℂ) + s * I) * q * ω) * Complex.I_sq
    · exfalso
      obtain ⟨r, s, hrs⟩ := repΛ hl
      apply hlN
      refine ⟨((r : ℂ) + s * I) * (p * ω), ?_, ?_⟩
      · exact gauss_mul_mem hLI r s (by have := L.lattice.smul_mem p hω; rwa [zsmul_eq_mul] at this)
      · simp only [LinearMap.mulLeft_apply]
        rw [hrs, hpq, hpq']; ring
  -- `u⁻¹ = conj u` is a Gaussian integer
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
  refine ⟨(1 / k : ℚ), ?_⟩
  ext x
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · intro hx
    obtain ⟨m, n, rfl⟩ := repL hx
    refine ⟨((m : ℂ) + n * I) * ((a + b * I) * μ), ?_, ?_⟩
    · have h1 : ((a : ℂ) + b * I) * μ ∈ LamCd d := gauss_mul_mem hΛI a b hμ
      exact gauss_mul_mem hΛI m n h1
    · rw [hμku]
      have : ((m : ℂ) + n * I) * ((a + b * I) * (k * u * ω)) =
          k * ((m + n * I) * ω) * (((a : ℂ) + b * I) * u) := by ring
      rw [this, hab]; push_cast; field_simp
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨m, n, rfl⟩ := repΛ hy
    rw [hμku]
    have : (((1 / k : ℚ) : ℂ)) * (((m : ℂ) + n * I) * (k * u * ω)) =
        (((m : ℂ) + n * I) * u) * ω := by push_cast; field_simp
    rw [this, hab' m n]
    exact gauss_mul_mem hLI _ _ hω

end ZInQ.CdOpt
