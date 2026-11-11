import ZInQKernel.RouteK.Redei.Primes
import ZInQKernel.RouteK.Slots.Symbols

/-!
# Rédei's formula: the Rédei matrix (`docs/research/redei-plan.md` §3.2)

`redeiEntry n q p` is the entry `R_{qp}` of the Rédei matrix of `ℚ(√−n)`, with rows indexed by the
primes `q ∣ n` and columns by `ramSet n`. The genus characters (step 4) compute `χ_q` on the class
of `𝔭_p` as `R_{qp}`, and the 4-rank statement (step 6) and the bridge to the bits (step 8) are
phrased with it. The definition is that of `scratch/redei-plan/Probe.lean` §3.4.
-/

noncomputable section

namespace ZInQ.RouteK.Redei

/-- The Rédei matrix: `χ_q(ψ(e)) = Σ_p R_{qp} e_p`, with `R_{qp} = (p/q)` for `p ≠ q`,
`R_{qq} = (n/q / q)`, and `R_{q2} = (2/q)`. -/
def redeiEntry (n : ℕ) (q : n.primeFactors) (p : ramSet n) : ZMod 2 :=
  if (p : ℕ) = 2 then legBit q 2
  else if (p : ℕ) = q then legBit q ((n / q : ℕ) : ℤ) else legBit q (p : ℤ)

end ZInQ.RouteK.Redei
