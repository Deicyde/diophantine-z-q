# bp-hecke-fe (fleet summary)

**Main result (VERIFIED: compiled with `lake env lean`, no `sorry`, axioms propext/Classical.choice/Quot.sound).**
`scratch/bp-hecke-fe/HeckeFE.lean` (about 2720 lines, compiles in under a minute) proves

    literature_hecke_fe_of_gaussPointCount :
      GaussPointCount → HeckeContinuation5 ∧ ZInQ.Literature.FunctionalEquation5

- `FunctionalEquation5` is the project's Prop itself: conductor 32d², root number −1, strip 0 < Re s < 2.
- `HeckeContinuation5` is `Literature.HeckeContinuation` restricted to squarefree d ≡ 5 (mod 8). That is the only
  case the headline uses; `tyzRow5b_of_readingA_five` is proved.
- `certifiedRankTYZClRk_of_gaussPointCount` gives CR₃ from TYZ reading A, Gross–Zagier and `GaussPointCount`.

**The single remaining hypothesis, `GaussPointCount`.** For primes p ≡ 1 (mod 4),
p − #{(x,y) ∈ 𝔽_p² : y² = x³ − x} = π + π̄, with ππ̄ = p and π ≡ 1 (mod 2+2i). This is Gauss's theorem (1814;
Ireland–Rosen Ch. 18 §4, theorem number UNVERIFIED). It is classical and refereed, a legitimate leaf, and is stated
over 𝔽_p and ℤ² only. Numerically VERIFIED at 29 primes. A Lean proof via quartic Jacobi sums is tier M.

**What compiles (everything else).**
- Analysis: weight-2 theta kernels of shifted ℤ[i] as products of Mathlib's Hurwitz kernels, giving a strong
  FE-pair, Mellin = lattice Dirichlet series, entire continuation of periodic twists, and the functional
  equation under a finite-Fourier relation. The conductor constants; root number (2/d) = −1.
- Fourier: `CdFourier` via CRT, the 2-part by `decide`, and the 2-D quadratic Gauss sum over 𝔽_p.
- Arithmetic: Mathlib's L(C_d, s) = L(ψ_d, s) (`DeuringCd`) from `GaussPointCount`. This includes ψ_d completely
  multiplicative; the Euler product of L(ψ_d, s) (gcd/Bezout in ℤ[i] for multiplicativity, the Hecke relation at
  split primes, inert/ramified/bad primes); point counts at p ≡ 3 (4); and the quadratic twist to d = 1.

**Integration suggestion.** Replace `Literature.HeckeContinuation` (all d ≠ 0) by `HeckeContinuation5`, and both
textbook Props by `GaussPointCount`. Report: docs/research/bp-hecke-fe.md. The scratch file imports
`ZInQKernel.RouteK.Rank.LFunctionCd` and `ZInQKernel.Hypotheses.CR3Literature`; `lake build` them first.
