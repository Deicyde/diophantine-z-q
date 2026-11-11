# redei-stmt report

Cheap step from the redei-plan report: CR₃ stated with Tian–Yuan–Zhang's own class numbers, and
Rédei's formula stated as a Prop.

## Lean names

New module `ZInQKernel/RouteK/Rank5b/Sec3/RedeiStatement.lean`, imported from the root module
`ZInQKernel/RouteK/Rank5bSec3.lean`. Everything is in the namespace `ZInQ.RouteK.Rank5b`:

- `QNeg n := QuadraticAlgebra ℚ (-(n:ℚ)) 0`, with instances `QNeg.factNotIsSquare` and
  `QNeg.numberField` (for `[NeZero n]`), plus `neZero_dProd`.
- `gCl n := Nat.card (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* _).range`, i.e. `#2Cl(ℚ(√−n))`.
- `T5bCl d`: `T5b` with `((gCl (dProd B) : ℕ) : ZMod 2)` in place of `gBit d B`.
- `CertifiedRankTYZCl`: `CertifiedRankTYZ` with `T5bCl d = 1` in place of `T5b d = 1`. Its trust
  statement cites TYZ (Theorem 3.5 and the proof of Theorem 3.5(2), as completed in nt-tyz.md §4,
  Proposition N) and Gross–Zagier with an auxiliary imaginary quadratic field (Bump–Friedberg–Hoffstein
  or Murty–Murty; pc-audit.md RK7, RK9).
- `RedeiFormula : Prop`. Its docstring cites Rédei (J. Reine Angew. Math. 171 (1934), 55–60) and
  tyz-5b Prop. 2.3, and says it is a classical theorem stated here so that a later formalization can
  discharge it (plan: docs/research/redei-plan.md).
- `T5bCl_eq_T5b (hR : RedeiFormula) (hd : Odd d) (hsq : Squarefree d) : T5bCl d = T5b d`
- `certifiedRankTYZ_iff_of_redeiFormula : RedeiFormula → (CertifiedRankTYZCl ↔ CertifiedRankTYZ)`

Root module, namespace `ZInQ`:
- `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZCl
   (hH : SixContactMin) (hCR : RouteK.Rank5b.CertifiedRankTYZCl) (hR : RouteK.Rank5b.RedeiFormula) :
   FrozenTarget`

## Exact statement of RedeiFormula

```lean
def RedeiFormula : Prop :=
  ∀ d : ℕ, Odd d → Squarefree d → ∀ B : Finset d.primeFactors, B.Nonempty →
    (dProd B % 8 = 7 ∨ dProd B % 8 = 3 ∨ dProd B % 8 = 1) →
      ((gCl (dProd B) : ℕ) : ZMod 2) = gBit d B
```

Why this scope is right: `T5b d` sums over `Finpartition`s `P` of the prime factors of `d`, and
reads `gBit d B` only for `B ∈ P.parts` when `Admissible5bNat d P` holds (Sec3/Defs.lean:85). Parts
of a finpartition are nonempty (`P.ne_bot`), and `Admissible5bNat` requires every part to have
`d_B ≡ 7, 3 or 1 (mod 8)` (its third conjunct, `hP.2.2`). So these are exactly the blocks the genus
sum uses: the classes `≡ 5 (mod 8)` and `B = ∅` are left out. `T5bCl_eq_T5b` uses exactly these two
facts. The only hypotheses on `d` are oddness and squarefreeness, which is the form of the probe's
`gCl_eq_gBit`. `CertifiedRankTYZ` uses `d ≡ 5 (mod 8)` squarefree, which implies both.

## Build and checks

- `lake build ZInQKernel`: Build completed successfully (9892 jobs). No sorry and no errors. No new
  warnings: the only warnings are the existing module-system and unused-simp-argument ones in other
  files.
- `python3 scripts/check_target.py`: FrozenTarget matches lean/Frozen/BoundedIntegerPolynomial.lean.
- `#print axioms` (scratch file, deleted afterwards) on `T5bCl_eq_T5b`,
  `certifiedRankTYZ_iff_of_redeiFormula` and the root variant: `[propext, Classical.choice, Quot.sound]`
  for each.

Only the new module and the root module were edited under ZInQKernel/.
