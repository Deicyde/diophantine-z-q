import Mathlib.NumberTheory.ModularForms.Cusps

/-! # Elkik's torsion theorem at `Γ₀(N)` -/

namespace ZInQ.Manuscript.RC.ElkikPrint

/-- **LEAF-candidate (page read by the reviewer; pending the lead's skeptic pass).**
R. Elkik, *Le théorème de Manin–Drinfeld*, Astérisque 183 (1990), p. 59, Théorème
(`diophantine_zq.tex` 11158–11160). The reviewer read the printed statement:

> THÉORÈME. Si Γ est un sous-groupe de congruence, la classe de tout diviseur de degré 0
> de X_Γ à support dans les pointes, est un élément de torsion de Pic⁰(X_Γ).

Specialize to the congruence subgroup `Γ₀(N)` and the degree-zero divisors `[c(r)] − [∞]`,
where `c(r)` is the cusp represented by `r ∈ ℙ¹(ℚ)`. Identifying `J` with `J₀(N)(ℚ̄)` and
`cuspClass r` with that divisor class is GLUE. These are parameters for the printed objects.
Finiteness of the subgroup they generate (tex 2937–2940) is a separate deduction. -/
def ManinDrinfeldTorsion (N : ℕ) [NeZero N] {J : Type*} [AddCommGroup J]
    (cuspClass : OnePoint ℚ → J) : Prop :=
  ∀ r, ∃ n : ℕ, 0 < n ∧ n • cuspClass r = 0

end ZInQ.Manuscript.RC.ElkikPrint
