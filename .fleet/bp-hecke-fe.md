# bp-hecke-fe (fleet summary)

**Main result (VERIFIED: compiled with `lake env lean`, no `sorry`, axioms propext/Classical.choice/Quot.sound).**
`scratch/bp-hecke-fe/HeckeFE.lean` proves

    literature_hecke_fe_of_heckeEuler_gaussPointCount :
      (∀ d, d % 8 = 5 → Squarefree d → HeckeEuler d) → GaussPointCount →
      HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5

`FunctionalEquation5` is the project's Prop itself (conductor 32d², root number −1, strip 0 < Re s < 2).
`HeckeContinuation5` is `Literature.HeckeContinuation` restricted to squarefree d ≡ 5 (mod 8); that is
the only case the headline uses (`tyzRow5b_of_readingA_five` is proved).

**What compiles.** All of the analysis, Fourier analysis and point counting:
- weight-2 theta kernels of shifted ℤ[i] as products of Mathlib's Hurwitz kernels, giving a strong FE-pair,
  an entire Mellin transform, Mellin = lattice Dirichlet series, and entire continuation of every periodic twist;
- grouping by the norm, so Mathlib's L(C_d, s) (via `LFunctionCd.lean`) equals L(ψ_d, s) given Deuring's
  coefficient identity `DeuringCd`;
- the functional equation of the twisted series under a finite-Fourier relation; the conductor constants;
  the root number from (2/d) = −1;
- the finite Fourier identity `CdFourier`: CRT, the 2-part by `decide`, and the 2-D quadratic Gauss sum over 𝔽_p
  (`gauss2D`) with multiplicativity;
- `DeuringCd` at p ≡ 3 (mod 4), p | d and p = 2 (point counts); the split primes for all d from d = 1
  (quadratic twist, reciprocity); ψ_d completely multiplicative and unit-invariant (`decide`).

**What remains (two elementary statements; both checked numerically with PARI, 0 failures).**
- `HeckeEuler d`: Euler product of heckeCoeff d n = ¼ Σ_{N α = n} (Nα/d) u(α) α. This is unique-factorization
  glue in ℤ[i]; tier M.
- `GaussPointCount`: Gauss (1814), p − #{y² = x³ − x over 𝔽_p} = π + π̄ for primary π, p ≡ 1 (mod 4).
  Classical and refereed (Ireland–Rosen Ch. 18 §4, theorem number UNVERIFIED); a legitimate leaf, or tier M via
  quartic Jacobi sums.

**Integration suggestion.** Replace `Literature.HeckeContinuation` (all d ≠ 0) by `HeckeContinuation5`.
Report: docs/research/bp-hecke-fe.md. Scratch file imports `ZInQKernel.RouteK.Rank.LFunctionCd` and
`ZInQKernel.Hypotheses.CR3Literature` (run `lake build` on them first).
