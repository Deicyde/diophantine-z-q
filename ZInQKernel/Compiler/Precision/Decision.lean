import ZInQKernel.Compiler.Precision.Relation
import ZInQKernel.Compiler.Precision.CappedTest
import ZInQKernel.Compiler.Precision.ScalarMul

/-!
# The exact decision program

Blueprint: `compiler/natural/precision/decision-program.md`.

`decide5 : ℕ⁵ → Bool` decodes `(n, κ, a, l, j)`, applies the early tests, computes the Jacobian
representatives `mul(k)` for `k ∈ {l, a, j}` over `ℤ[s]`, rejects if some `Z_k` or `Y_k`
vanishes, puts `ν_k = -X_k Z_k Ȳ_k` and `N_k = N(Y_k)`, compares the closeness test as an integer
inequality, and evaluates the precision test with the cap `L = ⌊(V - 1)/(4U)⌋` by the capped
bound and the division-by-four loop. Every quantity is an integer, an element of `ℤ[s]` or a
natural number; every test is exact. The function is total: the scalar loop halves its
counter, and the factorial, capped-power and division-by-four loops are bounded.
-/

namespace ZInQ.Compiler.Precision

open JTriple

/-- `ν = -X Z Ȳ ∈ ℤ[s]`, so that `z = ν / N`. -/
def nuJ (T : JTriple Zs) : Zs := -(T.X * T.Z * star T.Y)

/-- `N = N(Y) = Y Ȳ ∈ ℤ`. -/
def normJ (T : JTriple Zs) : ℤ := QuadraticAlgebra.norm T.Y

/-- `U = |p| + |p'|` where `ν_l = p + p' s`. -/
def epsU (T : JTriple Zs) : ℕ := (nuJ T).re.natAbs + (nuJ T).im.natAbs

/-- `V = |N_l|`. -/
def epsV (T : JTriple Zs) : ℕ := (normJ T).natAbs

/-- `δ = N_j N(ν_a)`. -/
def ratioDen (Ta Tj : JTriple Zs) : ℤ := normJ Tj * QuadraticAlgebra.norm (nuJ Ta)

/-- `θ`, the rational component of `ν_j ν̄_a N_a`. -/
def ratioNum (Ta Tj : JTriple Zs) : ℤ := (nuJ Tj * star (nuJ Ta) * (normJ Ta : Zs)).re

/-- The cap `L = ⌊(V - 1)/(4U)⌋`. -/
def capL (T : JTriple Zs) : ℕ := (epsV T - 1) / (4 * epsU T)

instance (n κ a l j : ℤ) : Decidable (EarlyTestsInt n κ a l j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- The decision program on decoded inputs `(n, κ, a, l, j)`. -/
def decideInt (n κ a l j : ℤ) : Bool :=
  if EarlyTestsInt n κ a l j then
    let Tl := jmul l
    let Ta := jmul a
    let Tj := jmul j
    if Tl.Z = 0 ∨ Ta.Z = 0 ∨ Tj.Z = 0 ∨ Tl.Y = 0 ∨ Ta.Y = 0 ∨ Tj.Y = 0 then false
    else
      let U := epsU Tl
      let V := epsV Tl
      let δ := ratioDen Ta Tj
      let θ := ratioNum Ta Tj
      if |θ - n * δ| * (V : ℤ) < (U : ℤ) * |δ| then
        let L := capL Tl
        if L = 0 then false
        else
          let M := (κ * sixF n).natAbs
          decide (1 ≤ divFourLoop L (cappedBound L M))
      else false
  else false

/-- **The exact decision program** `decide : ℕ⁵ → Bool`. -/
def decide5 (c : Fin 5 → ℕ) : Bool :=
  decideInt (dec (c 0)) (dec (c 1)) (dec (c 2)) (dec (c 3)) (dec (c 4))

end ZInQ.Compiler.Precision
