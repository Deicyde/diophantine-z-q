# shimura-modfn (2026-11-14)

**Verdict.** tyz-cm's CM leaf `Shimura.ShimuraReciprocityModFn` is correctly stated. It is a
consequence of Shimura 1971 Thm. 5.4 (main theorem of CM *with torsion*) plus the canonical model
of `X₀(N)` (equivalently Shimura Thm. 6.31; numbers UNVERIFIED), and no stronger. The weaker
`CMValueRingClass` does **not** cover every use: `TYZSigmaFixesZn` and `TYZThm36Seven` need
non-trivial ideal classes.

**It cannot be replaced by the `j`-form of the main theorem of CM via `ℚ(X₀(N)) = ℚ(j, j_N)`.**
At Heegner points where the plane model `(j, j_N)` is singular, the values `j(τ), j(Nτ)` do not
determine `g(τ)`. Example (VERIFIED numerically): `Q = [32,10,1]`, `D = −28`,
`j(τ) = j(32τ) = 255³`, but `x(τ) = −1 + √−7`. Such points occur where the project uses the leaf:
TYZ's class-7 forms for exactly the 32 values `n ≤ 4087` with `[𝔭₂]^{10} = 1`
(`n = 7, 15, 47, 79, …`). Recommendation: keep `ShimuraReciprocityModFn` as the CM leaf.

**What compiles** (`scratch/shimura-modfn/ModFn.lean`; 0 errors; axioms
`[propext, Classical.choice, Quot.sound]`):
* verbatim copies with `rfl` checks;
* new leaf `MainTheoremCMj` (CM for `j = E₄³/Δ`, ideal-class form, over Mathlib and Tau Ceti), new
  non-CM leaf `RatX0Rep`, and `ShimuraReciprocityModFnSingular` (the leaf restricted to
  non-isolated points);
* `shimuraReciprocityModFn_of_split : MainTheoremCMj → RatX0Rep → ShimuraReciprocityModFnSingular →
  ShimuraReciprocityModFn`;
* `jPair_reciprocity` (the `j`, `j_N` part at Heegner pairs from `MainTheoremCMj`);
* `reciprocity_of_rep` (evaluation glue);
* the q-expansion bookkeeping `isRatModFn_jInv`, `isRatModFn_jN` (`j`, `j_N ∈ ℚ(X₀(N))`) and
  `jPair_of_modFn` (consistency: tyz-cm's leaf implies the `j`-part).

**What remains.** The CM leaf itself. Optional: the Frobenius-at-primes form of `MainTheoremCMj`
and its passage to the class form (not done). `RatX0Rep` (modular polynomial + function field of
`X₀(N)`) is not formalized.
Report: `docs/research/shimura-modfn.md`.
