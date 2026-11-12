# bp-faltings (fleet report)

**Result.** `docs/research/bp-faltings.md` is the formalization blueprint for the stable Faltings
height, which blocks the leaves R18-R22. It gives a dependency graph of about 35 nodes from
Mathlib v4.35 to the stable height, each with a size tier, a route and its status in Mathlib,
other libraries or the literature. The graph covers:
- models;
- Hermitian lines and the Arakelov degree;
- the archimedean term;
- independence of choices;
- the acceptance tests.

The verdict: define the stable height as an infimum, in `EReal`, of model heights over smooth
separated finite-type group models `𝒢/𝓞_L` (node H3). Then Néron models and semistable reduction
are needed only for the theorem that the infimum is finite and equals the Néron value (node H5),
not to define the height or to state the leaves. The critical path is the analytic uniformization
`A(ℂ) ≅ ℂ^g/Λ` (node AN3, XL). The next largest pieces are Néron models and semistable reduction
(M5-M7, XL each), and elliptic curves and Jacobians as `AbVar`s (AV7).

**What compiles (VERIFIED).** `lake env lean` on `scratch/bp-faltings/Hodge.lean` (about 1 100
lines) and `scratch/bp-faltings/Models.lean`: 0 errors, 0 warnings, no `sorry`. Every
`#print axioms` lists `[propext, Classical.choice, Quot.sound]`. Mathlib only. `Hodge.lean`
contains:
- Hermitian lines on `Spec 𝓞_K` (`HermitianLattice`) and the Arakelov degree, independent of the
  section (product formula plus the index lemma `#(M/𝓞·as) = |N a|·#(M/𝓞·s)`);
- for fractional ideals:
  - the index formula `#(I/𝓞x)·N(I) = |N x|` and the closed formula
    `deg = −log N(I) − ∑ log ρ_σ`;
  - tensor products, rescaling;
  - base change `deg_L = [L:K]·deg_K`, using `N_L(I𝓞_L) = N_K(I)^{[L:K]}` and the count of
    embeddings;
- the archimedean metric `(i/2)^g∫_{ℂ^g/Λ} η∧η̄`, written `torusMetricSq`:
  - as an integral over any fundamental domain;
  - independent of the linear coordinates, via `covol(e⁻¹Λ)·|det e| = covol Λ` and
    `det_ℝ = |det_ℂ|²`;
- `HodgeData`, an abelian variety given with a model and its uniformizations, with:
  - `modelHeight` and Faltings' formula for every `η`;
  - independence of the coordinates;
  - the change-of-model formula and monotonicity, which make the Néron lattice the minimum;
  - base-change invariance in dimension 1;
  - an inhabited example of height 0 (`covol(ℤ + ℤi) = 1`);
- **acceptance test AT1 in conditional form** (`modelHeight_ofIdeal_eq_faltingsHeightEC'`): for
  any Weierstrass model with Néron lattice `𝔞·ω`, the model height equals pkg-I5's
  `faltingsHeightEC`. Its three hypotheses are exactly the missing inputs:
  - the area formula `PeriodAreaFormula`;
  - the period-pair identification;
  - the Néron identity `−12 log N𝔞 = ∑ log⁺|j|_v − ∑ log|σΔ|`.

`Models.lean` typechecks `GroupModel A L`, a smooth separated quasi-compact group object over
`Spec 𝓞_L` with a group isomorphism `𝒢_L ≅ A_L`, over the project's `AbVar`.

**What remains.**
- Node constructions:
  - AV3/M2, the cotangent lattice `e*Ω¹_{𝒢/𝓞_L}`;
  - AN3, the uniformization;
  - M4/H2-H3, assembling `GroupModel.hodgeData` and the infimum;
  - AV7, elliptic curves and Jacobians as `AbVar`s.
- Unproved: `PeriodAreaFormula` (AN5) and AT1a (Néron lattice of semistable elliptic curves).
- AT2 (genus 2) and H5 (Néron and semistable theory).
- AR3 for an abstract `HermitianLattice` (reduce to the fractional-ideal case).
- Literature locators in §6 of the report are UNVERIFIED (no network); size tiers are
  SPECULATIVE.
