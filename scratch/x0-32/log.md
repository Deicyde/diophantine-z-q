# x0-32 results log

## 2026-11-13 06:40 start (fresh; no earlier log)

- VERIFIED (computed, `eta.py`, exact integer q-series to q^79): the Γ₀(32) eta quotients (Ligozat
  conditions) with poles only at ∞ and order ≤ 3 there: X = η(2τ)²η(16τ)/(η(4τ)η(32τ)²) (order −2),
  Y1 = η(8τ)⁴η(16τ)²/(η(4τ)²η(32τ)⁴) and Y2 = η(τ)²η(16τ)⁴/(η(2τ)η(8τ)η(32τ)⁴) (order −3); none of order −1
  (genus 1).
- VERIFIED (`fit.py`): x = X + 2, y = ±Y1 satisfy y² = x³ + 4x to O(q³⁴) (window of 40 coefficients).
- VERIFIED (`newf.py`): f = η(4τ)²η(8τ)² = Σ aₙ qⁿ with aₙ from the Euler product of point counts of
  y² = x³+4x (a₂ = 0), n < 80. q dx/dq = −2·Y1·f exactly to q^77, so with y = −Y1: dx/(2y) = 2πi f dτ.
- VERIFIED (`cusps.py`, floating point, τ = r + 10⁻³ i): cusp images [0]↦(2,−4), [1/2]↦(2,4),
  [1/4]↦(−2,−4i), [−1/4]↦(−2,4i), [1/8]↦(−2i,0), [−1/8]↦(2i,0), [1/16]↦(0,0); agrees with
  rv-tyz-inputs §1.5a (PARI modular symbols).
- Tools: no cypari2/sympy/mpmath on this host (~/pyenv absent; uv would need network) — all computations
  in plain Python (fractions, cmath).
- COMPILED: ZInQKernel/Contrib/TYZGenus/X0.lean skeleton (defs + leaves X0-EQ, X0-INV, X0-BIJ, X0-DIFF,
  X0-NEWFORM, X0-CUSP, X0-DICT; `lake env lean`, no errors).
