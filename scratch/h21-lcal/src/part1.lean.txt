
/-!
# h21-lcal, part 1: the functional equation of `L(C_d, s)` with root number `+1` (`d ≡ 1, 3 (mod 8)`)

From the tree's Hecke theory over `ℤ[i]` (`Contrib/HeckeFE/Basic.lean`, `Contrib/HeckeAll/`): Deuring's identity
at `d = 1` (proved from Gauss's point count), the quadratic twist `cdCoeff d n = (d/n) cdCoeff 1 n`, quadratic
reciprocity on the norms `N α ≡ 1 (mod 4)`, the finite Fourier identity of `c_d` for `d ≡ 3 (mod 4)` (new: the
`d ≡ 1 (mod 4)` case is in the tree) and the odd Gauss sums (proved in the tree for all odd squarefree `d`).
-/

open Complex Real Set Filter

namespace ZInQ.Contrib.H21Lcal

open ZInQ.Contrib.HeckeFE ZInQ.Contrib.HeckeAll ZInQ.Literature

/-! ### Step 1: `L(C_d, s) = T_c(s)` with `c = ¼ c_d`, for every odd squarefree `d` -/

theorem unitG_ne_zero_norm : ∀ a b : ZMod 4, unitG (a, b) ≠ 0 → a ^ 2 + b ^ 2 = 1 := by decide

/-- On a norm fibre, `(d / N α) u(α) = (N α / d) u(α)` (reciprocity; `N α ≡ 1 (mod 4)` when `u(α) ≠ 0`). -/
theorem jacobi_unit_swap {d : ℕ} (hd : Odd d) {n : ℕ} {q : ℤ × ℤ} (hq : q ∈ normFiber n) :
    (jacobiSym d n : ℂ) * unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) =
      (jacobiSym (q.1 ^ 2 + q.2 ^ 2) d : ℂ) * unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) := by
  have hN := mem_normFiber.mp hq
  by_cases hu : unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) = 0
  · rw [hu]; ring
  have hu' : unitG ((q.1 : ZMod 4), (q.2 : ZMod 4)) ≠ 0 := by
    intro h; apply hu; rw [unitOf_eq_unitG, h]; simp
  have h1 := unitG_ne_zero_norm _ _ hu'
  have hc : ((q.1 : ZMod 4) ^ 2 + (q.2 : ZMod 4) ^ 2) = ((n : ℕ) : ZMod 4) := by
    have : ((q.1 ^ 2 + q.2 ^ 2 : ℤ) : ZMod 4) = ((n : ℤ) : ZMod 4) := by rw [hN]
    push_cast at this; exact this
  rw [hc] at h1
  have hn4 : n % 4 = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' n 1 4).mp (by rw [h1]; simp)
    simpa using this
  rw [hN, jacobiSym.quadratic_reciprocity_one_mod_four hn4 hd]

/-- **`L(C_d, s) = T_{¼c_d}(s)` on `Re s > 3/2`** for every odd squarefree `d`. -/
theorem lseries_eq_twistedL {d : ℕ} (hd : Odd d) (hsq : Squarefree d) {s : ℂ} (hs : 3 / 2 < s.re) :
    (ZInQ.shortCurve (-(d : ℚ) ^ 2)).LSeries s =
      twistedL (4 * d) (fun x => (1 / 4) * cdChar d x) s := by
  have : NeZero d := ⟨hsq.ne_zero⟩
  have : NeZero (4 * d) := ⟨by have := NeZero.ne d; omega⟩
  have hD1 : DeuringCd 1 :=
    deuringCd_of_gaussPointCount (by norm_num) squarefree_one ZInQ.Contrib.GaussFE.gaussPointCount
  rw [LSeries_cd_eq' hsq s]
  refine LSeries_eq_twistedL (4 * d) _ _ (fun n hn => ?_) hs
  rw [cdCoeff_twist d hn, hD1 n hn, heckeCoeff, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [cdChar_intCast, jacobiSym.one_right]
  have := jacobi_unit_swap hd hq
  push_cast
  linear_combination (1 / 4 : ℂ) * gz 0 0 q * this

/-! ### Step 2: the Fourier identity for `d ≡ 3 (mod 4)` -/

theorem unitG_neg : ∀ a b : ZMod 4, unitG (-a, -b) = -unitG (a, b) := by decide

theorem unitOf_neg (a b : ZMod 4) : unitOf (-a, -b) = -unitOf (a, b) := by
  rw [unitOf_eq_unitG, unitOf_eq_unitG, unitG_neg]; simp

/-- **Factorization of `ĉ_d` for `d ≡ 3 (mod 4)`**: `ĉ_d = −(2-part)(odd part)` (copy of the tree's
`fourierHat_cd_eq`, where `d ≡ 1 (mod 4)`; here `d·a ≡ −a (mod 4)` and `u(−α) = −u(α)`). -/
theorem fourierHat_cd_eq3 {d : ℕ} (hd4 : d % 4 = 3) (ν : ℤ × ℤ) :
    fourierHat (4 * d) (cdChar d) ν = -(g2Sum ν * oddSum d ν) := by
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd0 : 0 < d := hodd.pos
  have : NeZero d := ⟨hd0.ne'⟩
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd0.ne'
  have hMC : ((4 * d : ℕ) : ℂ) ≠ 0 := by push_cast; exact mul_ne_zero (by norm_num) hdC
  set F : ℤ → ℤ → ℂ := fun x y => (jacobiSym (x ^ 2 + y ^ 2) d : ℂ) *
    unitOf ((x : ZMod 4), (y : ZMod 4)) *
      cexp (2 * π * I * ((x : ℂ) * ν.1 + (y : ℂ) * ν.2) / ((4 * d : ℕ) : ℂ)) with hFdef
  have hmodd : ∀ x : ℤ, x % ((4 * d : ℕ) : ℤ) ≡ x [ZMOD d] := fun x => by
    have : (x % ((4 * d : ℕ) : ℤ)) ≡ x [ZMOD ((4 * d : ℕ) : ℤ)] :=
      Int.emod_emod_of_dvd x (dvd_refl _)
    push_cast at this
    exact this.of_mul_left 4
  have hmod4 : ∀ x : ℤ, ((x % ((4 * d : ℕ) : ℤ) : ℤ) : ZMod 4) = (x : ZMod 4) := fun x => by
    have : (x % ((4 * d : ℕ) : ℤ)) ≡ x [ZMOD ((4 * d : ℕ) : ℤ)] :=
      Int.emod_emod_of_dvd x (dvd_refl _)
    push_cast at this
    exact (ZMod.intCast_eq_intCast_iff _ _ 4).mpr (this.of_mul_right d)
  have hperx : ∀ x y : ℤ, F x y = F (x % ((4 * d : ℕ) : ℤ)) y := fun x y => by
    simp only [F]
    rw [hmod4, jacobiSym.mod_left' (((hmodd x).pow 2).add_right _).symm, intCast_emod_eq,
      add_mul, add_right_comm, cexp_shift hMC]
  have hpery : ∀ x y : ℤ, F x y = F x (y % ((4 * d : ℕ) : ℤ)) := fun x y => by
    simp only [F]
    rw [hmod4, jacobiSym.mod_left' (((hmodd y).pow 2).add_left _).symm, intCast_emod_eq,
      add_mul, ← add_assoc, cexp_shift hMC]
  have h1 : fourierHat (4 * d) (cdChar d) ν =
      ∑ j1 : Fin (4 * d), ∑ j2 : Fin (4 * d), F j1 j2 := by
    rw [fourierHat, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j1 _ => Finset.sum_congr rfl fun j2 _ => ?_
    rw [cdChar_intCast (d := d) ((j1 : ℤ), (j2 : ℤ))]
    simp only [F, ech]
    congr 2
    push_cast
    ring
  have h2 : ∑ j1 : Fin (4 * d), ∑ j2 : Fin (4 * d), F j1 j2 =
      ∑ a1 : Fin 4, ∑ b1 : Fin d, ∑ a2 : Fin 4, ∑ b2 : Fin d,
        F (d * a1 + 4 * b1) (d * a2 + 4 * b2) := by
    have hin : ∀ x : ℤ, ∑ j2 : Fin (4 * d), F x j2 =
        ∑ a2 : Fin 4, ∑ b2 : Fin d, F x (d * a2 + 4 * b2) := fun x =>
      sum_crt hodd (F x) fun y => hpery x y
    simp_rw [hin]
    exact sum_crt hodd (fun x => ∑ a2 : Fin 4, ∑ b2 : Fin d, F x (d * a2 + 4 * b2))
      fun x => Finset.sum_congr rfl fun a2 _ =>
        Finset.sum_congr rfl fun b2 _ => hperx x _
  have hd4' : (d : ZMod 4) = -1 := by rw [← ZMod.natCast_mod, hd4]; rfl
  have hJ16 : jacobiSym 16 d = 1 := by
    have h4 : Int.gcd 4 d = 1 := by
      rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, Int.gcd_natCast_natCast]
      exact Nat.Coprime.pow_left 2 ((Nat.coprime_two_left).mpr hodd)
    have := jacobiSym.sq_one' h4
    norm_num at this; exact this
  have h3 : ∀ (a1 a2 : Fin 4) (b1 b2 : Fin d),
      F (d * a1 + 4 * b1) (d * a2 + 4 * b2) =
        -(unitOf ((((a1 : ℕ) : ℤ) : ZMod 4), (((a2 : ℕ) : ℤ) : ZMod 4)) *
          cexp (2 * π * I * (((a1 : ℕ) : ℂ) * ν.1 + ((a2 : ℕ) : ℂ) * ν.2) / 4)) *
        ((jacobiSym (((b1 : ℕ) : ℤ) ^ 2 + ((b2 : ℕ) : ℤ) ^ 2) d : ℂ) *
          cexp (2 * π * I * (((b1 : ℕ) : ℂ) * ν.1 + ((b2 : ℕ) : ℂ) * ν.2) / d)) := by
    intro a1 a2 b1 b2
    simp only [F]
    have hj : jacobiSym ((d * a1 + 4 * b1 : ℤ) ^ 2 + (d * a2 + 4 * b2 : ℤ) ^ 2) d =
        jacobiSym (((b1 : ℕ) : ℤ) ^ 2 + ((b2 : ℕ) : ℤ) ^ 2) d := by
      rw [jacobiSym.mod_left' (b := d) (a₂ := 16 * (((b1 : ℕ) : ℤ) ^ 2 + ((b2 : ℕ) : ℤ) ^ 2)),
        jacobiSym.mul_left, hJ16, one_mul]
      exact Int.modEq_of_dvd ⟨-(d * ((a1 : ℕ) : ℤ) ^ 2 + 8 * ((a1 : ℕ) : ℤ) * ((b1 : ℕ) : ℤ) +
        d * ((a2 : ℕ) : ℤ) ^ 2 + 8 * ((a2 : ℕ) : ℤ) * ((b2 : ℕ) : ℤ)), by ring⟩
    have hu : (((d * a1 + 4 * b1 : ℤ) : ZMod 4), ((d * a2 + 4 * b2 : ℤ) : ZMod 4)) =
        (-(((a1 : ℕ) : ℤ) : ZMod 4), -(((a2 : ℕ) : ℤ) : ZMod 4)) := by
      push_cast
      rw [hd4', show (4 : ZMod 4) = 0 from rfl]
      simp
    have he : cexp (2 * π * I * (((d * a1 + 4 * b1 : ℤ) : ℂ) * ν.1 +
        ((d * a2 + 4 * b2 : ℤ) : ℂ) * ν.2) / ((4 * d : ℕ) : ℂ)) =
        cexp (2 * π * I * (((a1 : ℕ) : ℂ) * ν.1 + ((a2 : ℕ) : ℂ) * ν.2) / 4) *
        cexp (2 * π * I * (((b1 : ℕ) : ℂ) * ν.1 + ((b2 : ℕ) : ℂ) * ν.2) / d) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      field_simp
      ring
    rw [hj, hu, unitOf_neg, he]
    ring
  rw [h1, h2, ← neg_mul, g2Sum, ← Finset.sum_neg_distrib, oddSum, Fintype.sum_prod_type,
    Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a1 _ => ?_
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a2 _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b1 _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b2 _ => h3 a1 a2 b1 b2

/-- **The Fourier relation for `d ≡ 3 (mod 4)`**: `κ = −4d(1+i)(2/d)` (copy of `cdFourier_of_oddGauss`). -/
theorem cdFourier3_of_oddGauss {d : ℕ} (hd4 : d % 4 = 3) (hO : OddGauss d) :
    FourierRel (4 * d) (cdChar d) (-(4 * d * (1 + I) * (jacobiSym 2 d : ℂ))) := by
  have : NeZero d := ⟨by omega⟩
  refine ⟨fun μ => ?_, fun ν hν => ?_⟩
  · rw [fourierHat_cd_eq3 hd4, g2Sum_eq, hO, cdChar_intCast]
    push_cast
    rw [g2G_table.1, map_mul, map_mul, ← unitOf_eq_unitG]
    have hN : (μ.1 - μ.2) ^ 2 + (μ.1 + μ.2) ^ 2 = 2 * (μ.1 ^ 2 + μ.2 ^ 2) := by ring
    simp only [hN, jacobiSym.mul_left]
    push_cast
    have h4 : GaussianInt.toComplex 4 = 4 := map_ofNat _ 4
    simp [GaussianInt.toComplex_def', h4]
    ring
  · rw [fourierHat_cd_eq3 hd4, g2Sum_eq]
    have hpar : (((ν.1 : ZMod 4) + (ν.2 : ZMod 4))).val % 2 = 1 := by
      have h := ZMod.val_intCast (n := 4) (ν.1 + ν.2)
      push_cast at h
      obtain ⟨k, hk⟩ := hν
      have : ((((ν.1 : ZMod 4) + (ν.2 : ZMod 4))).val : ℤ) % 2 = 1 := by rw [h]; omega
      omega
    rw [g2G_table.2 _ _ hpar]
    simp

theorem oddGauss_of_odd_squarefree {d : ℕ} (hd : Odd d) (hsq : Squarefree d) : OddGauss d :=
  oddGauss_of_prime (fun p hp hp2 => by have : Fact p.Prime := ⟨hp⟩; exact oddGauss_prime hp2) d hd hsq

theorem jacobiSym_two_one {d : ℕ} (hd : d % 8 = 1) : jacobiSym 2 d = 1 := by
  rw [jacobiSym.at_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : d % 2 ≠ 0 := by omega
  simp [h2, hd]

theorem jacobiSym_two_three {d : ℕ} (hd : d % 8 = 3) : jacobiSym 2 d = -1 := by
  rw [jacobiSym.at_two (Nat.odd_iff.mpr (by omega)), ZMod.χ₈_nat_eq_if_mod_eight]
  have h2 : d % 2 ≠ 0 := by omega
  simp [h2, hd]

/-- **The Fourier relation with `κ = 4d(1+i)`** for squarefree `d ≡ 1, 3 (mod 8)` (root number `+1`). -/
theorem fourierRel_plus {d : ℕ} (hcl : d % 8 = 1 ∨ d % 8 = 3) (hsq : Squarefree d) :
    FourierRel (4 * d) (fun x => (1 / 4) * cdChar d x) (4 * d * (1 + I)) := by
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  refine fourierRel_const_mul ?_ (1 / 4)
  rcases hcl with h | h
  · have := cdFourier_of_oddGauss (by omega) (oddGauss_of_odd_squarefree hodd hsq)
    rwa [CdFourier, jacobiSym_two_one h, Int.cast_one, mul_one] at this
  · have := cdFourier3_of_oddGauss (by omega) (oddGauss_of_odd_squarefree hodd hsq)
    rwa [jacobiSym_two_three h, Int.cast_neg, Int.cast_one, mul_neg_one, neg_neg] at this

/-! ### Step 3: the functional equation `Λ(2 − s) = +Λ(s)` -/

/-- **Functional equation of `L(C_d, s)` with root number `+1`, `d ≡ 1, 3 (mod 8)`**, on the strip
`0 < Re s < 2` (as `FunctionalEquation5`, with `+`): `Λ(2 − s) = Λ(s)`, `Λ(s) = N^{s/2}(2π)^{−s}Γ(s)L(C_d, s)`,
`N = 32d²`. Literature: Deuring/Hecke (functional equation), Birch–Stephens, Topology 5 (1966) (root number
`+1` for `d ≡ 1, 2, 3 (mod 8)`; locator UNVERIFIED). Proved below. -/
def FunctionalEquationPlus : Prop :=
  ∀ d : ℕ, (d % 8 = 1 ∨ d % 8 = 3) → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F →
      ∀ s : ℂ, 0 < s.re → s.re < 2 →
        completedL (32 * d ^ 2) F (2 - s) = completedL (32 * d ^ 2) F s

theorem functionalEquationPlus_proof : FunctionalEquationPlus := by
  intro d hcl hsq F hF s hs0 hs2
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  have hd0 : 0 < d := hodd.pos
  have : NeZero d := ⟨by omega⟩
  have : NeZero (4 * d) := ⟨by omega⟩
  set M := 4 * d with hMdef
  set c : ZMod M × ZMod M → ℂ := fun x => (1 / 4) * cdChar d x
  set κ : ℂ := 4 * d * (1 + I)
  have hFc : FourierRel M c κ := fourierRel_plus hcl hsq
  have hκ : -I * κ * (1 + I) = 8 * d := by
    simp only [κ]
    linear_combination (-(4 * (d : ℂ) * I + 8 * d)) * I_sq
  have step1 : ∀ s : ℂ, 3 / 2 < s.re → F s = twistedL M c s := by
    intro s hs
    rw [hF.2 s hs, lseries_eq_twistedL hodd hsq hs]
  have hM2 : (((M : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne M))
  have : NeZero (((M : ℝ) ^ 2 : ℝ) : ℂ) := ⟨hM2⟩
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have : NeZero (π : ℂ) := ⟨hpi⟩
  set U : Set ℂ := {s : ℂ | 0 < s.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hGam : ∀ s ∈ U, DifferentiableAt ℂ Complex.Gamma s := fun s hs =>
    Complex.differentiableAt_Gamma s fun m hm => by
      have : s.re = -(m : ℝ) := by rw [hm]; simp
      have h0 : (0 : ℝ) < s.re := hs
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
  have step2 : ∀ s ∈ U, (π : ℂ) ^ (-s) * Complex.Gamma s * F s =
      (M : ℂ) * (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * lambdaC M c s := by
    have hf : AnalyticOnNhd ℂ (fun s => (π : ℂ) ^ (-s) * Complex.Gamma s * F s) U := by
      refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo
      exact ((((differentiable_const_cpow_of_neZero (π : ℂ)).comp differentiable_id.neg) s).mul
        (hGam s hs) |>.mul (hF.1 s)).differentiableWithinAt
    have hg : AnalyticOnNhd ℂ (fun s => (M : ℂ) * (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) *
        lambdaC M c s) U := by
      refine DifferentiableOn.analyticOnNhd (fun s _ => ?_) hUo
      exact (((((differentiable_const_cpow_of_neZero _).comp differentiable_id.neg).const_mul
        _).mul (differentiable_lambdaC M c)) s).differentiableWithinAt
    have hU2 : {s : ℂ | 3 / 2 < s.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have hev : (fun s => (π : ℂ) ^ (-s) * Complex.Gamma s * F s) =ᶠ[nhds (2 : ℂ)]
        (fun s => (M : ℂ) * (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * lambdaC M c s) := by
      refine Filter.mem_of_superset hU2 fun s hs' => ?_
      have hs : 3 / 2 < s.re := hs'
      show (π : ℂ) ^ (-s) * Complex.Gamma s * F s = _
      rw [step1 s hs, lambdaC_eq M c hs]
    exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt 0).isPreconnected
      (show (2 : ℂ) ∈ U by simp [U]) hev
  have hsU : s ∈ U := hs0
  have hsU' : 2 - s ∈ U := show 0 < (2 - s).re by rw [sub_re]; norm_num; linarith
  have hsplit : ∀ z : ℂ, (2 * Real.pi : ℂ) ^ (-z) = (2 : ℂ) ^ (-z) * (π : ℂ) ^ (-z) := fun z => by
    have := mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) pi_pos.le (-z)
    push_cast at this; exact this
  have hL : ∀ z ∈ U, completedL (32 * d ^ 2) F z =
      ((32 * d ^ 2 : ℕ) : ℂ) ^ (z / 2) * (2 : ℂ) ^ (-z) * ((M : ℂ) *
        (((M : ℝ) ^ 2 : ℝ) : ℂ) ^ (-z) * lambdaC M c z) := fun z hz => by
    rw [completedL, hsplit, ← step2 z hz]; ring
  rw [hL _ hsU', hL _ hsU, lambdaC_two_sub M c hFc s, hκ]
  have hc := const_identity hd0 s
  simp only [M] at *
  linear_combination -(lambdaC (4 * d) c s * hc)

end ZInQ.Contrib.H21Lcal

