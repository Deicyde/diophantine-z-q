# rc-j0-cusps3

**Scoped stop: the group law on the fixed projective Weierstrass model.**
The complex points of this exact model are homeomorphic to the chosen
`ℂ/Lat`, with the class of `z` evaluating to the manuscript's
`weierPt E Lat z`. The proof includes the point at infinity. Given a
scheme group object on the model, `projectiveAbVar` supplies properness,
smoothness and geometric integrality in the existing abelian variety package.

The existing Elkik torsion print is specialized to the represented
`J₀(N)(Qbar)` and the actual `algebraicCuspClass`. The cusp orbit
factorization gives finite range. With compatible group addition,
`algebraicCuspClass_comparison_atScale` identifies every finite rational
cusp label with its scaled torus symbol via the based Abel–Jacobi map.
This supplies the comparison at every nonzero quadratic weight, and
`hElkikMD_atScale_of_projectiveGroup` composes it with Elkik's reduction.

The remaining target statement is exactly
```lean
∃ g : GrpObj (projectiveTarget E), letI := g
  ∀ p q : AbVar.ptObj (K := ℚ) ℂ ⟶ projectiveTarget E,
    projectiveValue (p * q).left = projectiveValue p.left + projectiveValue q.left
```
The rational-scale witness `∃ c : ℚ, (c : ℂ) = κ` remains an explicit
input to the at-scale construction. The independent maps `q_f`, `α` and
the matching cusp tail still belong to the scale-rationality argument.

Six new files passed serial standalone Lean checks; all 50 axiom audits
used only the three standard axioms. No prior file or print changed.
No new manuscript error was found; inherited citation issues are in the
report.

Result and report SHA: `9f131bd7b8846c571bf9398f3b861ffb6a8f854e`.
Report: `docs/research/rc-j0-cusps3.md`. Log: `scratch/rc-j0-cusps3/log.md`.
