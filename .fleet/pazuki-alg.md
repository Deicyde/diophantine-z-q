# pazuki-alg (fleet note)

**Verdict.** The target (pazuki fold at −1 GLUE) is **not met**. `PazukiDict.AnalyticPPAlgebraic` cannot be proved from
what the fold has (`uniformizationLeafAll`, AbVar projectivity, `gagaMorphism`, `SerreGAGAMorphism`). Two inputs are
missing:
- **The theta line bundle.** GAGA for morphisms only gives pullbacks of `O(1)`, i.e. `nΘ` with `n ≥ 2`, never the
  `h⁰ = 1` bundle of `Θ`. That needs GAGA for line bundles or Weil divisors, which cannot be stated in Lean today.
- **The descent from ℂ to a number field.** This needs `NS(A_ℚ̄) = NS(A_ℂ)`, and nothing in the fold provides it.

No statement was changed, and none is false or vacuous.

**Main result (compiled, standard axioms).** `ZInQKernel/Contrib/OneProof/PazukiAlg.lean` proves pazuki-dict's analytic
half `ThetaDivisorAlgebraicC` from three inputs:
- a new statement about `Ω` alone, `RiemannPPAV`: Riemann's theorem that `ℂ²/(Ωℤ²+ℤ²)` is a principally polarized
  abelian surface whose theta divisor is the zero set of `θ(·+c, Ω)`;
- the existing field `gagaMorphism`, used twice to get an isomorphism `B ≅ B₀`;
- `SymmPrincipalTransport`, proved in the file: ampleness, symmetry, `h⁰` and the divisor all transport along an
  isomorphism of abelian varieties.

The file also proves that `Ωℤ²+ℤ²` is discrete, and the functional equation of `θ` (the zero set is periodic), which
shows the new statement is consistent.

The final theorem `PazukiAlg.pazukiCor13Upper_of_riemann` discharges the field `pazukiCor13Upper`. Its remaining
hypotheses are `GAGAMorphism` (an existing field), `PazukiCor13UpperPP` (LEAF), `RiemannPPAV` (composite) and
`SymmPrincipalDescends` (composite).

**Checks.** All passed:
- full build of Main + Discharges + PazukiAlg: 14103 jobs;
- `#discharges` shows the field discharged with the standard axioms;
- verbatim `rfl` check of `AnalyticPPAlgebraic`;
- autofold dry run: `scratch/pazuki-alg/autofold.json`; the generated module compiles.

**Count.** The fold costs +1 GLUE (`16/21 → 17/22`) and needs `--allow-rise`. `RiemannPPAV` is rated composite: the
print is analytic, and reading it for schemes goes through Chow/GAGA. pazuki-dict's coarser spec is neutral. The fine
fold becomes neutral if a reading finds the scheme form of Riemann's theorem in print (Mumford AV §3 is the
candidate), and −1 if `SymmPrincipalDescends` is also proved.

**What remains.**
- `SymmPrincipalDescends` (Néron–Severi invariance, the `Pic⁰[2]` torsor, descent of ampleness; the `H⁰` base
  change is already in the vendored library).
- The reading of `RiemannPPAV`.
- pazuki-dict's Def. 2.6 reading risk.

Report: `docs/research/pazuki-alg.md`. Log: `scratch/pazuki-alg/log.md`.
