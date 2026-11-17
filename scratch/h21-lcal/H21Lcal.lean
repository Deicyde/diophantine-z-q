import ZInQKernel.Contrib.HeckeAll.Provider
import ZInQKernel.Contrib.OneProof.TYZThm21Span
import ZInQKernel.Contrib.OneProof.TYZLcalOne

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


/-! # h21-lcal, part 2: the order of `L(C_d, s)` at `s = 1` is not `1` for `d ≡ 1, 3 (mod 8)` -/

namespace ZInQ.Contrib.H21Lcal

open ZInQ.Literature

/-- An analytic function symmetric about `1` (`G(2 − s) = G(s)` near `1`) does not have a simple zero at `1`. -/
theorem analyticOrderAt_ne_one_of_symm {G : ℂ → ℂ} (hG : AnalyticAt ℂ G 1)
    (hsym : ∀ᶠ s in nhds (1 : ℂ), G (2 - s) = G s) : analyticOrderAt G 1 ≠ 1 := by
  intro h
  obtain ⟨g, hg, hg1, hfg⟩ :=
    (hG.analyticOrderAt_eq_natCast (n := 1)).mp (by rw [h]; rfl)
  have hcont : Continuous (fun s : ℂ => 2 - s) := continuous_const.sub continuous_id
  have ht : Tendsto (fun s : ℂ => 2 - s) (nhds 1) (nhds 1) := by
    have := hcont.tendsto 1
    norm_num at this
    exact this
  have hfg2 := ht.eventually hfg
  have hk : ∀ᶠ s in nhds (1 : ℂ), (s - 1) * (g s + g (2 - s)) = 0 := by
    filter_upwards [hfg, hfg2, hsym] with s h1 h2 h3
    simp only [pow_one, smul_eq_mul] at h1 h2
    rw [h1, h2] at h3
    linear_combination -h3
  have hkc : ContinuousAt (fun s => g s + g (2 - s)) 1 :=
    hg.continuousAt.add (ContinuousAt.comp_of_eq hg.continuousAt hcont.continuousAt (by norm_num))
  have hk0 : (fun s => g s + g (2 - s)) =ᶠ[nhdsWithin 1 {1}ᶜ] fun _ => (0 : ℂ) := by
    filter_upwards [nhdsWithin_le_nhds hk, self_mem_nhdsWithin] with s hs hs1
    exact (mul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr hs1)
  have hlim1 := hkc.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
  have hlim2 : Tendsto (fun s => g s + g (2 - s)) (nhdsWithin 1 {1}ᶜ) (nhds 0) :=
    tendsto_const_nhds.congr' hk0.symm
  have h0 := tendsto_nhds_unique hlim1 hlim2
  norm_num at h0
  apply hg1
  linear_combination h0

/-- **The order of `L(C_d, s)` at `s = 1` is not `1`** for squarefree `d ≡ 1, 3 (mod 8)` (root number `+1`):
from `functionalEquationPlus_proof`. -/
theorem analyticOrderAt_ne_one {d : ℕ} (hcl : d % 8 = 1 ∨ d % 8 = 3) (hsq : Squarefree d) {F : ℂ → ℂ}
    (hF : IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F) : analyticOrderAt F 1 ≠ 1 := by
  have hd0 : d ≠ 0 := hsq.ne_zero
  set N : ℕ := 32 * d ^ 2
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (by positivity : 32 * d ^ 2 ≠ 0)
  have : NeZero (N : ℂ) := ⟨hN⟩
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have : NeZero (2 * Real.pi : ℂ) := ⟨h2pi⟩
  set P : ℂ → ℂ := fun s => (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s
  set U : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < 2}
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hU1 : U ∈ nhds (1 : ℂ) := hUo.mem_nhds (by norm_num [U])
  have hPd : DifferentiableOn ℂ P U := by
    intro s hs
    have hG : DifferentiableAt ℂ Complex.Gamma s := Complex.differentiableAt_Gamma s fun m hm => by
      have : s.re = -(m : ℝ) := by rw [hm]; simp
      have h0 : (0 : ℝ) < s.re := hs.1
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact ((((differentiable_const_cpow_of_neZero (N : ℂ)).comp (differentiable_id.div_const 2)) s).mul
      (((differentiable_const_cpow_of_neZero _).comp differentiable_id.neg) s) |>.mul hG).differentiableWithinAt
  have hP : AnalyticAt ℂ P 1 := hPd.analyticAt hU1
  have hP1 : P 1 ≠ 0 := by
    simp only [P, Complex.Gamma_one, mul_one]
    exact mul_ne_zero ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr hN)
      ((Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by norm_num)).mpr h2pi)
  have hFa : AnalyticAt ℂ F 1 := hF.1.analyticAt 1
  have hΛ : AnalyticAt ℂ (P * F) 1 := hP.mul hFa
  have hsym : ∀ᶠ s in nhds (1 : ℂ), (P * F) (2 - s) = (P * F) s := by
    filter_upwards [hU1] with s hs
    have := functionalEquationPlus_proof d hcl hsq F hF s hs.1 hs.2
    simpa [completedL, P, N] using this
  have hne := analyticOrderAt_ne_one_of_symm hΛ hsym
  rw [analyticOrderAt_mul hP hFa, (analyticOrderAt_eq_zero.mpr (Or.inr hP1)), zero_add] at hne
  exact hne

end ZInQ.Contrib.H21Lcal

/-! # h21-lcal, part 3: TYZ's `𝓛(n)²` as printed, and `h21C`/`h21S` restated with it

TYZ (arXiv:1411.4728v1, L338–353, as transcribed by the project: `scratch/rv-tyz-inputs/tyzcalc.py`,
`docs/research/h33-sign.md`, `rv-tyz-inputs.md` §1.7; the source is not on this host) define `𝓛(n)` for odd
squarefree `n` by cases on `r = ord_{s=1} L(E_n, s)`: `𝓛(n) = 0` if `r > 1`; `𝓛(n)² = L(E_n, 1)/(2^{2k−2−a}Ω_n)`
if `r = 0`; `𝓛(n)² = L′(E_n, 1)/(2^{2k−2−a}Ω_n R_n)` if `r = 1` (`R_n` the regulator), with `a = 1` for odd `n`.
The project's `lcalSq m = L(C_m, 1)/(2^{2k−3}Ω_m)` is the `r = 0` branch; it agrees with the printed
definition on the classes `1, 3 (mod 8)` because `r ≠ 1` there (`analyticOrderAt_ne_one`, root number `+1`),
and when `r ≥ 2` both are `0`. -/

namespace ZInQ.Contrib.H21Lcal

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp
open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.TYZDecomp.H29Genus NumberField
open ZInQ.Contrib.T21Proof ZInQ.Contrib.HfxProof ZInQ.Contrib.TYZGenusFold ZInQ.Contrib.H21CSteps
open scoped Quaternion

open Classical in
/-- **TYZ's `𝓛(n)²` as printed (L338–353), odd `n`**, for a given regulator function `R` (`R n` stands for TYZ's
`R_n`, twice the Néron–Tate height of a generator of `E_n(ℚ)/E_n(ℚ)_tors` in rank one; it enters only the
branch `ord = 1`, which never occurs on the classes `1, 3 (mod 8)`, so the value there does not depend on `R`:
`lcalSqPrinted_eq`). `F` is the entire continuation of Mathlib's `L(C_n, s)` (`C_n ≅ E_n : ny² = x³ − x` over
`ℚ`), unique by `IsLContinuation.eq`; `k = #{p ∣ n}`, `a = 1`; `Ω_n = omegaTYZ n = (2/√n)∫₁^∞ dx/√(x³ − x)`.
Junk `0` if there is no continuation (there always is: `ZInQ.Contrib.heckeContinuation`). -/
noncomputable def lcalSqPrinted (R : ℕ → ℝ) (n : ℕ) : ℂ :=
  if h : ∃ F : ℂ → ℂ, IsLContinuation (ZInQ.Contrib.TYZDecomp.curveC n) F then
    if analyticOrderAt h.choose 1 = 0 then
      h.choose 1 / ((2 : ℂ) ^ ((2 * n.primeFactors.card : ℤ) - 3) * (omegaTYZ n : ℂ))
    else if analyticOrderAt h.choose 1 = 1 then
      deriv h.choose 1 /
        ((2 : ℂ) ^ ((2 * n.primeFactors.card : ℤ) - 3) * (omegaTYZ n : ℂ) * (R n : ℂ))
    else 0
  else 0

set_option linter.deprecated false in
/-- **Step (a) of the queue10 verdict on `h21C`**: on squarefree `m ≡ 1, 3 (mod 8)`, the project's `lcalSq m`
is TYZ's printed `𝓛(m)²`, for every regulator function `R`. -/
theorem lcalSqPrinted_eq (R : ℕ → ℝ) {m : ℕ} (hsq : Squarefree m) (hcl : m % 8 = 1 ∨ m % 8 = 3) :
    lcalSqPrinted R m = lcalSq m := by
  have hex : ∃ F : ℂ → ℂ, IsLContinuation (ZInQ.Contrib.TYZDecomp.curveC m) F :=
    ZInQ.Contrib.heckeContinuation m hsq.ne_zero
  have hF := hex.choose_spec
  have hL : lValOne m = hex.choose 1 := lValOne_eq hF
  have h1 := analyticOrderAt_ne_one hcl hsq hF
  rw [lcalSqPrinted, dif_pos hex, lcalSq, hL]
  by_cases h0 : analyticOrderAt hex.choose 1 = 0
  · rw [if_pos h0]
  · rw [if_neg h0, if_neg h1]
    have hz : hex.choose 1 = 0 := by
      by_contra hne
      exact h0 (analyticOrderAt_eq_zero.mpr (Or.inr hne))
    rw [hz, zero_div]

/-- `ℓ` is a complex sign choice of TYZ's printed `𝓛` on the squarefree classes `1, 3 (mod 8)`. -/
def IsLcalSignPrinted (R : ℕ → ℝ) (ℓ : ℕ → ℂ) : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ℓ m ^ 2 = lcalSqPrinted R m

theorem isLcalSignPrinted_iff (R : ℕ → ℝ) (ℓ : ℕ → ℂ) : IsLcalSignPrinted R ℓ ↔ IsLcalSignC ℓ :=
  ⟨fun h m hsq hcl => (h m hsq hcl).trans (lcalSqPrinted_eq R hsq hcl),
   fun h m hsq hcl => (h m hsq hcl).trans (lcalSqPrinted_eq R hsq hcl).symm⟩

/-- **TYZ Theorem 2.1 (L554–559) with TYZ's printed `𝓛` (L338–353)**: `TYZThm21PairsC` (tyz-genus) with the
sign choices `ℓ(m)² = 𝓛(m)²` taken against `lcalSqPrinted R` (the case split on `ord_{s=1}` as printed) for every
regulator function `R`, instead of the project's `lcalSq`. Same restrictions as `TYZThm21PairsC` (odd classes,
`n > 1`, the first assertion only for pairs with no factor `≡ 1 (mod 8)`). Equivalent to `TYZThm21PairsC`
(`tyzThm21PairsC_of_printed`, `tyzThm21PairsPrinted_of_C`), and to its instance at any single `R`. -/
def TYZThm21PairsPrinted : Prop :=
  ∀ R : ℕ → ℝ, ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ ℓ : ℕ → ℂ, IsLcalSignPrinted R ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriod n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          (quadPeriod n τ f d₂ : ℂ) = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) * (ℓ d₁ * ℓ d₂))

theorem tyzThm21PairsC_of_printed (h : TYZThm21PairsPrinted) : TYZThm21PairsC := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h (fun _ => 0) n hsq h1 hcl τ hτ f hf ℓ ((isLcalSignPrinted_iff _ ℓ).mpr hℓ) d₁ d₂ hd

theorem tyzThm21PairsPrinted_of_C (h : TYZThm21PairsC) : TYZThm21PairsPrinted := by
  intro R n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h n hsq h1 hcl τ hτ f hf ℓ ((isLcalSignPrinted_iff R ℓ).mp hℓ) d₁ d₂ hd

/-- **TYZ Theorem 2.1 with `π^U` of Theorem 2.4(1) (h21c-steps' `TYZThm21Span`) and TYZ's printed `𝓛`**:
`TYZThm21Span` with `lcalSqPrinted R` for every `R` in place of `lcalSq`. Equivalent to `TYZThm21Span`
(`tyzThm21Span_of_printed`, `tyzThm21SpanPrinted_of_span`), hence to `TYZThm21PairsC`. -/
def TYZThm21SpanPrinted : Prop :=
  ∀ R : ℕ → ℝ, ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVectorSpan n τ f →
      ∀ ℓ : ℕ → ℂ, IsLcalSignPrinted R ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriod n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          (quadPeriod n τ f d₂ : ℂ) = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) * (ℓ d₁ * ℓ d₂))

theorem tyzThm21Span_of_printed (h : TYZThm21SpanPrinted) : TYZThm21Span := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h (fun _ => 0) n hsq h1 hcl τ hτ f hf ℓ ((isLcalSignPrinted_iff _ ℓ).mpr hℓ) d₁ d₂ hd

theorem tyzThm21SpanPrinted_of_span (h : TYZThm21Span) : TYZThm21SpanPrinted := by
  intro R n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h n hsq h1 hcl τ hτ f hf ℓ ((isLcalSignPrinted_iff R ℓ).mp hℓ) d₁ d₂ hd

/-- `h21C` from the printed span form (the fold used on `frozenTarget`). -/
theorem tyzThm21PairsC_of_spanPrinted (h : TYZThm21SpanPrinted) : TYZThm21PairsC :=
  tyzThm21PairsC_of_span (tyzThm21Span_of_printed h)

/-- **Non-vacuity of the printed definition**: `𝓛(1)² = 1` (TYZ L1082), from lcal-one's proof of `TYZLcalOne`
through `lcalSqPrinted_eq`; so `IsLcalSignPrinted R ℓ` forces `ℓ 1 = ±1`. -/
theorem lcalSqPrinted_one (R : ℕ → ℝ) : lcalSqPrinted R 1 = 1 :=
  (lcalSqPrinted_eq R squarefree_one (Or.inl rfl)).trans ZInQ.Contrib.LcalOne.tyzLcalOne_proof

end ZInQ.Contrib.H21Lcal

#print axioms ZInQ.Contrib.H21Lcal.functionalEquationPlus_proof
#print axioms ZInQ.Contrib.H21Lcal.analyticOrderAt_ne_one
#print axioms ZInQ.Contrib.H21Lcal.lcalSqPrinted_eq
#print axioms ZInQ.Contrib.H21Lcal.lcalSqPrinted_one
#print axioms ZInQ.Contrib.H21Lcal.tyzThm21PairsC_of_printed
#print axioms ZInQ.Contrib.H21Lcal.tyzThm21PairsPrinted_of_C
#print axioms ZInQ.Contrib.H21Lcal.tyzThm21Span_of_printed
#print axioms ZInQ.Contrib.H21Lcal.tyzThm21SpanPrinted_of_span
