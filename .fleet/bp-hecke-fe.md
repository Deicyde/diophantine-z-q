# bp-hecke-fe (fleet summary)

**Main result (VERIFIED: compiled with `lake env lean`, no `sorry`, axioms propext/Classical.choice/Quot.sound).**
`scratch/bp-hecke-fe/HeckeFE.lean` (≈2100 lines) proves

    literature_hecke_fe_of_mult_split_gaussPointCount :
      (∀ d ≡ 5 (8) sqfree, HeckeMult d) → (∀ such d, HeckePrimePowSplit d) → GaussPointCount →
      HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5

`FunctionalEquation5` is the project's Prop itself (conductor 32d², root number −1, strip 0 < Re s < 2).
`HeckeContinuation5` is `Literature.HeckeContinuation` restricted to squarefree d ≡ 5 (mod 8), the only case the
headline uses (`tyzRow5b_of_readingA_five` is proved).

**What compiles.** All of the analysis, Fourier analysis and point counting:
- weight-2 theta kernels of shifted ℤ[i] as products of Mathlib's Hurwitz kernels, giving a strong FE-pair,
  Mellin = lattice Dirichlet series, and entire continuation of every periodic twist;
- Mathlib's L(C_d, s) (via `LFunctionCd.lean`) = L(ψ_d, s) given Deuring's coefficient identity `DeuringCd`;
- the functional equation, conductor constants, and root number (2/d) = −1;
- the finite Fourier identity `CdFourier`: CRT, the 2-part by `decide`, the 2-D quadratic Gauss sum over 𝔽_p;
- `DeuringCd` from `HeckeEuler` + split primes. Point counts at inert/bad primes; twist to d = 1;
- ψ_d completely multiplicative; `HeckeEuler` from multiplicativity + prime-power recursion; the recursion at
  inert, ramified and bad primes.

**What remains (three elementary statements; numerically VERIFIED with PARI, 0 failures).**
- `HeckeMult d`: heckeCoeff d is multiplicative, where heckeCoeff d n = ¼ Σ_{Nα=n} (Nα/d)u(α)α. Bezout/gcd in ℤ[i];
  proof sketch in the report.
- `HeckePrimePowSplit d`: the Hecke recursion at split primes p ≡ 1 (4).
- `GaussPointCount`: Gauss (1814), p − #{y² = x³ − x over 𝔽_p} = π + π̄ (π primary), p ≡ 1 (4). Classical and
  refereed (Ireland–Rosen Ch. 18 §4, theorem number UNVERIFIED), so a legitimate leaf.

**Integration suggestion.** Replace `Literature.HeckeContinuation` (all d ≠ 0) by `HeckeContinuation5`.
Report: docs/research/bp-hecke-fe.md (verdict, Mathlib inventory, dependency graph, Lean table). The scratch file
imports `ZInQKernel.RouteK.Rank.LFunctionCd` and `ZInQKernel.Hypotheses.CR3Literature`; `lake build` them first.
