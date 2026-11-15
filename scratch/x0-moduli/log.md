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
5. `X0Moduli.lean` (VERIFIED, compiles, standard axioms):
   * textbook Props `WeierstrassGroupLaw` (clauses (a) ℘z = ℘w ⇒ z ≡ ±w; (b) ℘'z = 0 ⇒ 2z ∈ Λ; (c) chord;
     (d) tangent) and `VeluCyclic` (analytic Vélu for ⟨1/N⟩);
   * `conj_multiples`: σ(℘_τ(m/N)) = μ²℘_{τ'}(mk/N), σ(℘'_τ(m/N)) = μ³℘'_{τ'}(mk/N), N ∤ mk, 1 ≤ m < N;
   * `coprime_of_multiples`, `sum_perm` (m ↦ mk mod N on {1..N−1});
   * `jnConj_of_leaves : WeierstrassGroupLaw → VeluCyclic → JNConj`;
   * `x0ModuliGalois_of_leaves : WeierstrassGroupLaw → VeluCyclic → RatX0Rep → X0ModuliGaloisNonIsolated →
     T5Glue.X0ModuliGalois`.
6. `ZInQKernel/Contrib/OneProof/X0ModuliGalois.lean` (the same body; `lake build` OK). `#discharges`
   (`scratch/x0-moduli/Discharges.lean`, output `Discharges-output.txt`, VERIFIED):
   `DISCHARGES [hX] by X0Moduli.x0ModuliGalois_of_leaves still assumes: [WeierstrassGroupLaw, VeluCyclic,
   RatX0Rep, X0ModuliGaloisNonIsolated]`, standard axioms; also `[hX] by x0ModuliGalois_of_split`.
7. `autofold.json` written; `autofold.py --dry-run` refuses: `autofold: not a field of the current bundles: ['hX']`
   (hX is a plain argument of frozenTarget; a fold is a hand edit of Main.lean, as for hS in gt-ringclass).
   The split would raise the strict GLUE count (1 → 4), so it is not proposed as a fold.
