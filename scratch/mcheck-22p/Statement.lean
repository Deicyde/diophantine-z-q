import Mathlib

/-!
# mcheck-22p: Proposition `prop:fixed-prime-pattern` (diophantine_zq.tex L1267-1297), stated

Mathlib-only restatement, written independently of the kernel's `ZInQ.FixedPrimePattern`
(`ZInQKernel/Hypotheses/PrimePattern.lean`); `docs/research/mcheck-22p.md` compares the two.
No proof: the file only has to compile.
-/

namespace MCheck22P

/-- `P_s = ∏_{p ≤ 324} p`. -/
def Ps : ℕ := ∏ p ∈ (Finset.range 325).filter Nat.Prime, p

/-- `W = 4 P_s`. -/
def W : ℕ := 4 * Ps

/-- `𝓑 = {0, -15, -20, -24, -30, -60, 1}`. -/
def Bset : Finset ℤ := {0, -15, -20, -24, -30, -60, 1}

/-- `𝓗`: the first twenty-two primes `> 324` in each unit residue class mod `W` (tex L238-239,
L1273-1274). Every prime `> 324` is a unit mod `W`, so `h ∈ 𝓗` iff fewer than 22 primes in
`(324, h)` are congruent to `h` mod `W`. -/
def Hcat : Set ℕ :=
  {h | h.Prime ∧ 324 < h ∧
    ((Finset.Ioo 324 h).filter (fun q => q.Prime ∧ q ≡ h [MOD W])).card < 22}

/-- `𝓚 = {d h : d ∣ P_s⁴, d > 0, h ∈ 𝓗}`. -/
def Kset : Set ℤ := {k | ∃ d h : ℕ, 0 < d ∧ d ∣ Ps ^ 4 ∧ h ∈ Hcat ∧ k = (d * h : ℕ)}

/-- `#E_δ(𝔽_p)` for `E_δ : y² = x³ - δ² x`, point at infinity included. -/
def ord (p : ℕ) [NeZero p] (δ : ZMod p) : ℕ :=
  ((Finset.univ : Finset (ZMod p × ZMod p)).filter
      (fun xy => xy.2 ^ 2 = xy.1 ^ 3 - δ ^ 2 * xy.1)).card + 1

/-- The conditions on a prime value: `p` splits in `ℚ(√2)` (odd, `2` a square mod `p`); with
`r² = 2`, the two reductions of `d = 75 - 53√2` are `75 ∓ 53 r`; both reductions of
`E : y² = x³ - d² x` are good (discriminant `64 δ⁶ ≠ 0`); their orders `d₁, d₂` satisfy
`gcd(d₁,d₂) = 4` and `p ∤ d₁ d₂`. (`r ↦ -r` swaps `d₁, d₂`, so `∃ r` loses nothing.) -/
def GoodP (p : ℕ) : Prop :=
  ∃ hp : p.Prime, p ≠ 2 ∧
    haveI : NeZero p := ⟨hp.ne_zero⟩
    ∃ r : ZMod p, r ^ 2 = 2 ∧
      (64 * (75 - 53 * r) ^ 6 : ZMod p) ≠ 0 ∧ (64 * (75 + 53 * r) ^ 6 : ZMod p) ≠ 0 ∧
      Nat.gcd (ord p (75 - 53 * r)) (ord p (75 + 53 * r)) = 4 ∧
      ¬ p ∣ ord p (75 - 53 * r) * ord p (75 + 53 * r)

/-- The shape `ε k p` of each value. -/
def Shape (B0 : ℝ) (w : ℤ) : Prop :=
  ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∃ k ∈ Kset, ∃ p : ℕ, B0 < p ∧ GoodP p ∧ w = ε * k * p

/-- **Proposition (tex L1267-1297).** For every `A ∈ ℤ` and real `B₀` there are integers
`u₁, u₂, v`, `v ≠ 0`, such that with `u₃ = A v - u₁ - u₂` each of the 22 values
`v`, `u_j - b v` (`1 ≤ j ≤ 3`, `b ∈ 𝓑`) has the shape `ε k p`. -/
def FixedPrimePattern : Prop :=
  ∀ (A : ℤ) (B0 : ℝ), ∃ u1 u2 v : ℤ, v ≠ 0 ∧ Shape B0 v ∧
    ∀ b ∈ Bset, Shape B0 (u1 - b * v) ∧ Shape B0 (u2 - b * v) ∧
      Shape B0 ((A * v - u1 - u2) - b * v)

end MCheck22P
