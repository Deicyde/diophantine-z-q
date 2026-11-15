# x0-moduli results log

Task: hypothesis `hX = T5Glue.X0ModuliGalois` (ZInQKernel/Contrib/OneProof/RingClassLattice.lean:673).

1. Build: copied `.lake/build` and `lean/.lake/build` from the sgr-split worktree (same commit 6edf020d).
2. `Copy.lean`: verbatim copy `X0ModuliGaloisCopy`, `example : X0ModuliGaloisCopy = T5Glue.X0ModuliGalois := rfl`
   compiles (VERIFIED, 80 s).
3. `Split.lean` (VERIFIED, compiles, axioms [propext, Classical.choice, Quot.sound]):
   * `jInv_eq_jL : jInv τ = jL (pp τ)` (Klein's E₄³/Δ = 1728 g₂³/(g₂³ − 27g₃²) of ⟨1,τ⟩);
   * `x0ModuliGalois_isolated : RatX0Rep → JNConj → (X0ModuliGalois at isolated τ)`;
   * `x0ModuliGalois_of_split : RatX0Rep → JNConj → X0ModuliGaloisNonIsolated → T5Glue.X0ModuliGalois`.
4. Numerical checks (PARI/GP via cypari2, 50 digits; VERIFIED):
   * Vélu in analytic form `N⁴ g₂(⟨1,Nτ⟩) = g₂ + Σ_{m=1}^{N-1}(60℘(m/N)² − 5g₂)`,
     `N⁶ g₃(⟨1,Nτ⟩) = g₃ + Σ(140℘³ − 21g₂℘ − 14g₃)`: 5 samples (τ, N) = (0.3+1.1i, 3), (0.3+1.1i, 5),
     (−0.17+0.8i, 4), (0.41+0.93i, 7), (i, 2): residuals ≤ 1e-49 (1e-14 at τ = i, N = 2, PARI's
     lower precision there).
   * chord and tangent formulas for ℘, ℘' (the clauses of `WeierstrassGroupLaw`): 2 samples each, residuals
     ≤ 1e-53.
