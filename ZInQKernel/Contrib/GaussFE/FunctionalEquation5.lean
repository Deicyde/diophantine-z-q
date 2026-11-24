import ZInQKernel.Contrib.HeckeFE.Basic
import ZInQKernel.Contrib.GaussFE.Gauss

/-!
# `ZInQ.Literature.FunctionalEquation5`, proved

`ZInQKernel.Contrib.HeckeFE.Basic` (the bp-hecke-fe development, shared with `HeckeAll/`) proves
`HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5` from `GaussPointCount`, Gauss's count
of the points of `y² = x³ − x` over `𝔽_p` at primes `p ≡ 1 (mod 4)`. `Gauss.lean` proves that count
in the form `#{y² = x³ − x} = p + 2A` with `A + Bi` of norm `p` and `−(A + Bi)` primary
(`gauss_jacobi`). This file matches the two forms (`gaussPointCount`) and closes the provider
`ZInQ.Contrib.functionalEquation5`.
-/

namespace ZInQ.Contrib.GaussFE

open Complex ZInQ.Contrib.HeckeFE

/-- `ψ₁(z) + ψ₁(z̄)`. -/
noncomputable def psiPair (z : ℤ × ℤ) : ℂ := psi 1 z + psi 1 (conjZ z)

theorem psiPair_neg (z : ℤ × ℤ) : psiPair (gmul (-1, 0) z) = psiPair z := by
  have h : conjZ (gmul (-1, 0) z) = gmul (-1, 0) (conjZ z) := by
    simp only [conjZ, gmul]; ext <;> simp
  rw [psiPair, h, (psi_unit_mul 1 z).2, (psi_unit_mul 1 (conjZ z)).2, psiPair]

theorem psiPair_conj (z : ℤ × ℤ) : psiPair (conjZ z) = psiPair z := by
  have h : conjZ (conjZ z) = z := by simp [conjZ]
  rw [psiPair, h, psiPair, add_comm]

theorem unitOf_primary {x y : ℤ} (h : (x % 4 = 1 ∧ y % 4 = 0) ∨ (x % 4 = 3 ∧ y % 4 = 2)) :
    unitOf ((x : ZMod 4), (y : ZMod 4)) = 1 := by
  rw [← ZMod.intCast_mod x 4, ← ZMod.intCast_mod y 4, unitOf_eq_unitG]
  have h4 : ((4 : ℕ) : ℤ) = 4 := rfl
  rw [h4]
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> rw [hx, hy]
  · have : unitG (((1 : ℤ) : ZMod 4), ((0 : ℤ) : ZMod 4)) = 1 := by decide
    rw [this]; simp
  · have : unitG (((3 : ℤ) : ZMod 4), ((2 : ℤ) : ZMod 4)) = 1 := by decide
    rw [this]; simp

/-- For primary `π = x + yi` (`π ≡ 1 mod 2 + 2i`), `ψ₁(π) + ψ₁(π̄) = 2x`. -/
theorem psiPair_primary {x y : ℤ} (h : (x % 4 = 1 ∧ y % 4 = 0) ∨ (x % 4 = 3 ∧ y % 4 = 2)) :
    psiPair (x, y) = 2 * x := by
  have h' : ((x % 4 = 1 ∧ (-y) % 4 = 0) ∨ (x % 4 = 3 ∧ (-y) % 4 = 2)) := by omega
  simp only [psiPair, psi, conjZ, jacobiSym.one_right, Int.cast_one, one_mul]
  rw [unitOf_primary h, unitOf_primary h']
  simp only [gz]
  push_cast
  ring

/-- **Gauss's point count** (`GaussPointCount` of bp-hecke-fe), proved. -/
theorem gaussPointCount : GaussPointCount := by
  intro p hp hp4
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, B, hAB, hA2, hB4, hN⟩ := gauss_jacobi (p := p) hp4
  set a := A.natAbs with ha
  set b := B.natAbs with hb
  have hab : a ^ 2 + b ^ 2 = p := by
    have : ((a ^ 2 + b ^ 2 : ℕ) : ℤ) = p := by
      push_cast
      rw [ha, hb, Int.natCast_natAbs, Int.natCast_natAbs, sq_abs, sq_abs]
      exact hAB
    exact_mod_cast this
  -- the right-hand side is `ψ₁(π₀) + ψ₁(π̄₀)` with `π₀ = a + bi`
  have hpsi : ∀ q : ℤ × ℤ, unitOf ((q.1 : ZMod 4), (q.2 : ZMod 4)) * gz 0 0 q = psi 1 q := by
    intro q; simp [psi, jacobiSym.one_right]
  have hsplit : ∑ q ∈ normFiber p, psi 1 q = 4 * psiPair (piZ a b) := by
    classical
    rw [sum_normFiber_prime hp hp4 hab,
      Finset.sum_congr rfl fun e he => psi_gmul_unit 1 he (piZ a b),
      Finset.sum_congr rfl fun e he => psi_gmul_unit 1 he (conjZ (piZ a b)),
      Finset.sum_const, Finset.sum_const, card_unitsZ, psiPair]
    simp only [nsmul_eq_mul]; push_cast; ring
  -- `π₀` is `±π₁` or `±π̄₁` for the primary `π₁ = −(A + Bi)`
  have hprim : psiPair (-A, -B) = 2 * (-A : ℤ) := psiPair_primary (by omega)
  have hkey : psiPair (piZ a b) = psiPair (-A, -B) := by
    have hpa : (a : ℤ) = |A| := by rw [ha, Int.natCast_natAbs]
    have hpb : (b : ℤ) = |B| := by rw [hb, Int.natCast_natAbs]
    rcases le_or_gt 0 A with hA | hA <;> rcases le_or_gt 0 B with hB | hB
    · have : piZ a b = gmul (-1, 0) (-A, -B) := by
        simp only [piZ, gmul, hpa, hpb, abs_of_nonneg hA, abs_of_nonneg hB]; ext <;> simp
      rw [this, psiPair_neg]
    · have : piZ a b = gmul (-1, 0) (conjZ (-A, -B)) := by
        simp only [piZ, gmul, conjZ, hpa, hpb, abs_of_nonneg hA, abs_of_neg hB]; ext <;> simp
      rw [this, psiPair_neg, psiPair_conj]
    · have : piZ a b = conjZ (-A, -B) := by
        simp only [piZ, conjZ, hpa, hpb, abs_of_neg hA, abs_of_nonneg hB]; ext <;> simp
      rw [this, psiPair_conj]
    · have : piZ a b = (-A, -B) := by
        simp only [piZ, hpa, hpb, abs_of_neg hA, abs_of_neg hB]
      rw [this]
  have hN' : (Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - xy.1} : ℂ) =
      (p : ℂ) + 2 * (A : ℂ) := by exact_mod_cast hN
  rw [hN', Finset.sum_congr rfl fun q _ => hpsi q, hsplit, hkey, hprim]
  push_cast
  ring

/-- Both bp-hecke-fe literature Props, with no hypothesis. -/
theorem literature_hecke_fe : HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5 :=
  literature_hecke_fe_of_gaussPointCount gaussPointCount

end ZInQ.Contrib.GaussFE

/-- **Provider for `ZInQ.Literature.FunctionalEquation5`**: the functional equation
`Λ(2 − s) = −Λ(s)` of `L(C_d, s)` on `0 < Re s < 2`, for squarefree `d ≡ 5 (mod 8)`. -/
theorem ZInQ.Contrib.functionalEquation5 : ZInQ.Literature.FunctionalEquation5 :=
  ZInQ.Contrib.GaussFE.literature_hecke_fe.2
