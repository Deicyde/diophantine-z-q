import sys
R = {
'ZInQKernel/Contrib/HeckeFE/Basic.lean': [
("      (((oddKernel a t * evenKernel b t : ℝ) : ℂ) + I * ((evenKernel a t * oddKernel b t : ℝ) : ℂ)) :=",
 "      (((oddKernel a t * evenKernel b t : ℝ) : ℂ) +\n        I * ((evenKernel a t * oddKernel b t : ℝ) : ℂ)) :="),
("      ((oddKernel a t * evenKernel b t : ℝ) : ℂ) + I * ((evenKernel a t * oddKernel b t : ℝ) : ℂ) := by",
 "      ((oddKernel a t * evenKernel b t : ℝ) : ℂ) +\n        I * ((evenKernel a t * oddKernel b t : ℝ) : ℂ) := by"),
("    Summable fun p : ℤ × ℤ => c ((p.1 : ZMod M), (p.2 : ZMod M)) * gz 0 0 p / (gq 0 0 p : ℂ) ^ s := by",
 "    Summable fun p : ℤ × ℤ =>\n      c ((p.1 : ZMod M), (p.2 : ZMod M)) * gz 0 0 p / (gq 0 0 p : ℂ) ^ s := by"),
("  choose G hG hGeq using fun j : Fin M × Fin M => gaussL_continuation ((j.1 : ℝ) / M) ((j.2 : ℝ) / M)",
 "  choose G hG hGeq using fun j : Fin M × Fin M =>\n    gaussL_continuation ((j.1 : ℝ) / M) ((j.2 : ℝ) / M)"),
("    have h1 : p.1 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg p.1, sq_nonneg p.2])",
 "    have h1 : p.1 = 0 :=\n      (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg p.1, sq_nonneg p.2])"),
("    have h2 : p.2 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg p.1, sq_nonneg p.2])",
 "    have h2 : p.2 = 0 :=\n      (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg p.1, sq_nonneg p.2])"),
("    PowerSeries.map f (PowerSeries.invOfUnit φ 1) = PowerSeries.invOfUnit (PowerSeries.map f φ) 1 := by",
 "    PowerSeries.map f (PowerSeries.invOfUnit φ 1) =\n      PowerSeries.invOfUnit (PowerSeries.map f φ) 1 := by"),
("  rw [cdCoeff_eq_LFunction hd hsq hpp.out.ne_zero, ZInQ.Literature.LFunction_cd_apply_prime hd hsq p]",
 "  rw [cdCoeff_eq_LFunction hd hsq hpp.out.ne_zero,\n    ZInQ.Literature.LFunction_cd_apply_prime hd hsq p]"),
("/-- **CRT for sums**: for a `4d`-periodic `g`, `Σ_{j mod 4d} g(j) = Σ_{a mod 4} Σ_{b mod d} g(da + 4b)`. -/",
 "/-- **CRT for sums**: for a `4d`-periodic `g`,\n`Σ_{j mod 4d} g(j) = Σ_{a mod 4} Σ_{b mod d} g(da + 4b)`. -/"),
("theorem g2Sum_eq (ν : ℤ × ℤ) : g2Sum ν = ((g2G ((ν.1 : ZMod 4), (ν.2 : ZMod 4)) : GaussianInt) : ℂ) := by",
 "theorem g2Sum_eq (ν : ℤ × ℤ) :\n    g2Sum ν = ((g2G ((ν.1 : ZMod 4), (ν.2 : ZMod 4)) : GaussianInt) : ℂ) := by"),
("      rw [jacobiSym.mod_left' (b := m) (a₂ := (n : ℤ) ^ 2 * (((a1 : ℕ) : ℤ) ^ 2 + ((a2 : ℕ) : ℤ) ^ 2)),",
 "      rw [jacobiSym.mod_left' (b := m)\n          (a₂ := (n : ℤ) ^ 2 * (((a1 : ℕ) : ℤ) ^ 2 + ((a2 : ℕ) : ℤ) ^ 2)),"),
("      rw [jacobiSym.mod_left' (b := n) (a₂ := (m : ℤ) ^ 2 * (((b1 : ℕ) : ℤ) ^ 2 + ((b2 : ℕ) : ℤ) ^ 2)),",
 "      rw [jacobiSym.mod_left' (b := n)\n          (a₂ := (m : ℤ) ^ 2 * (((b1 : ℕ) : ℤ) ^ 2 + ((b2 : ℕ) : ℤ) ^ 2)),"),
("theorem unitOf_eq_zero_of_even {a b : ZMod 4} (h : (a.val + b.val) % 2 = 0) : unitOf (a, b) = 0 := by",
 "theorem unitOf_eq_zero_of_even {a b : ZMod 4} (h : (a.val + b.val) % 2 = 0) :\n    unitOf (a, b) = 0 := by"),
("  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb⟩",
 "  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp ha,\n    (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mp hb⟩"),
("/-- **Inert primes**: `heckeCoeff d (p^(k+2)) = −p · heckeCoeff d (p^k)` for `p ≡ 3 (mod 4)`, `p ∤ d`. -/",
 "/-- **Inert primes**: `heckeCoeff d (p^(k+2)) = −p · heckeCoeff d (p^k)` for `p ≡ 3 (mod 4)`,\n`p ∤ d`. -/"),
("  have hb1 : -1 ≤ c.1 ∧ c.1 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (c.1 + 1), sq_nonneg (c.1 - 1)]",
 "  have hb1 : -1 ≤ c.1 ∧ c.1 ≤ 1 := by\n    constructor <;> nlinarith [sq_nonneg (c.1 + 1), sq_nonneg (c.1 - 1)]"),
("  have hb2 : -1 ≤ c.2 ∧ c.2 ≤ 1 := by constructor <;> nlinarith [sq_nonneg (c.2 + 1), sq_nonneg (c.2 - 1)]",
 "  have hb2 : -1 ≤ c.2 ∧ c.2 ≤ 1 := by\n    constructor <;> nlinarith [sq_nonneg (c.2 + 1), sq_nonneg (c.2 - 1)]"),
("""    refine ⟨EuclideanDomain.gcdA γ (m : GaussianInt) * (γ * EuclideanDomain.gcdA γ (n : GaussianInt) +
      (n : GaussianInt) * EuclideanDomain.gcdB γ (n : GaussianInt)) +
      (m : GaussianInt) * EuclideanDomain.gcdB γ (m : GaussianInt) * EuclideanDomain.gcdA γ (n : GaussianInt) +
      star γ * EuclideanDomain.gcdB γ (m : GaussianInt) * EuclideanDomain.gcdB γ (n : GaussianInt), ?_⟩""",
"""    refine ⟨EuclideanDomain.gcdA γ (m : GaussianInt) *
        (γ * EuclideanDomain.gcdA γ (n : GaussianInt) +
          (n : GaussianInt) * EuclideanDomain.gcdB γ (n : GaussianInt)) +
      (m : GaussianInt) * EuclideanDomain.gcdB γ (m : GaussianInt) *
        EuclideanDomain.gcdA γ (n : GaussianInt) +
      star γ * EuclideanDomain.gcdB γ (m : GaussianInt) *
        EuclideanDomain.gcdB γ (n : GaussianInt), ?_⟩"""),
("  have h1 : q.1 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg q.1, sq_nonneg q.2])",
 "  have h1 : q.1 = 0 :=\n    (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg q.1, sq_nonneg q.2])"),
("  have h2 : q.2 = 0 := (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg q.1, sq_nonneg q.2])",
 "  have h2 : q.2 = 0 :=\n    (pow_eq_zero_iff two_ne_zero).mp (by nlinarith [sq_nonneg q.1, sq_nonneg q.2])"),
("theorem sum_mul_bij {z : ℤ × ℤ} {p n : ℕ} (hz : z.1 ^ 2 + z.2 ^ 2 = p) (hp : 0 < p) (f : ℤ × ℤ → ℂ) :",
 "theorem sum_mul_bij {z : ℤ × ℤ} {p n : ℕ} (hz : z.1 ^ 2 + z.2 ^ 2 = p) (hp : 0 < p)\n    (f : ℤ × ℤ → ℂ) :"),
],
'ZInQKernel/Contrib/HeckeAll/Continuation.lean': [
("/-- **The twist identity at prime powers**: `[T^k] 1/cdEulerPoly d p = (d/p)^k [T^k] 1/cdEulerPoly 1 p`. -/",
 "/-- **The twist identity at prime powers**:\n`[T^k] 1/cdEulerPoly d p = (d/p)^k [T^k] 1/cdEulerPoly 1 p`. -/"),
],
'ZInQKernel/Contrib/HeckeAll/Iso.lean': [
("    (shortCurve (-((m ^ 2 * d : ℕ) : ℚ) ^ 2)).LFunction = (shortCurve (-(d : ℚ) ^ 2)).LFunction := by",
 "    (shortCurve (-((m ^ 2 * d : ℕ) : ℚ) ^ 2)).LFunction =\n      (shortCurve (-(d : ℚ) ^ 2)).LFunction := by"),
("    (shortCurve (-((m ^ 2 * d : ℕ) : ℚ) ^ 2)).LSeries s = (shortCurve (-(d : ℚ) ^ 2)).LSeries s := by",
 "    (shortCurve (-((m ^ 2 * d : ℕ) : ℚ) ^ 2)).LSeries s =\n      (shortCurve (-(d : ℚ) ^ 2)).LSeries s := by"),
],
'ZInQKernel/Contrib/PSide/Convergence.lean': [
("  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn, ite_eq_right hn, convolution_one_one, Complex.norm_natCast]",
 "  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn, ite_eq_right hn,\n    convolution_one_one, Complex.norm_natCast]"),
],
}
for p, rs in R.items():
    s = open(p).read()
    for a, b in rs:
        n = s.count(a)
        if n != 1: print("COUNT", n, p, a[:60]); continue
        s = s.replace(a, b)
    open(p, 'w').write(s)
