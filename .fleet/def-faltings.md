# def-faltings (2026-11-12)

**Main result.** The stable Faltings height is a Lean definition over Mathlib's objects, with no
`sorry` and no `axiom` (`scratch/def-faltings/Faltings.lean`, compiled with no errors or
warnings; axioms are `propext`, `Classical.choice`, `Quot.sound`):

`stableFaltingsHeight A : EReal := ⨅ L g (M : MetrizedModel A L g), M.hodge.modelHeight`

- The infimum runs over number fields `L ⊇ K` and smooth separated finite-type group models
  `𝒢/𝓞_L` of `A_L`.
- The lattice `⋀^g ω_𝒢` is built in Lean from the local rings of `𝒢` along the unit section:
  - `ω_{A_L} = 𝔪_ξ/𝔪_ξ²`;
  - `ω_𝒢 = ⋂_s image(I_{e(s)})`;
  - `hodgeSpace = L ⊗ ⋀^g`;
  - the sanity theorem `omegaAt_genericPt` is proved.
- The archimedean data are constrained by a concrete Prop, `IsAnalyticUniformization`. It
  requires `Φ : ℂ^g → 𝒢(ℂ)_τ` to be a surjective homomorphism with kernel `Λ`, along which
  regular functions are holomorphic. The coefficient map is fixed by
  `coeff(1 ⊗ df₁∧⋯∧df_g) = det ∂(fᵢ∘Φ)/∂z_j(0)`.

**The AN3 gap is a stated theorem, not a hole in a definition.** It is split into three Props:
- `AnalyticUniformizationExists` (unproved);
- `AnalyticUniformizationUnique` (unproved);
- the algebraic `HodgeLatticeTheorem` (unproved).

Until they are proved, nothing excludes `h = ⊤`.

**Proved:**
- the height does not depend on the uniformization, given uniqueness
  (`MetrizedModel.modelHeight_eq_of_model_eq`, using a wedge-extensionality lemma and the chain
  rule for `jacDet`);
- `GroupModel.height`, and `h = inf_{L,𝒢} 𝒢.height`;
- Deligne's normalization `h_D = h_F + (g/2) log π` for the infimum;
- AT1 (any `b₂`) and AT2 in conditional form: the general definition equals pkg-I5's
  `faltingsHeightEC` / `faltingsHeightGood`, given the outputs of AN4/AN5/AT1a (resp. M8/AN6).
  The hypothesis `hmin` is the `≥` half of the conclusion, i.e. the output H5 must supply.

**Stated, unproved:**
- `AcceptanceEC` (via `IsEllipticCurveOf`: `A∖{O}` affine with ring `K[x,y]/(W)`);
- the Néron mapping property `IsNeronModel`, `StableHeightFinite`, `NeronModelMinimal` (H5);
- the leaves R19 (Gaudron-Rémond), R20 (Faltings Lemma 5) and R21 (Bost via GR), over
  `stableFaltingsHeight` with genuine isogenies and degrees, using the locators.md
  normalizations.

**Not stated:** R18 and R22. They need curves with genus, Belyi maps, Jacobians, polarizations
and theta heights.

**Review:** an independent model review found no faithfulness errors; its three fixes were
applied.

**Remaining work:**
- `HodgeLatticeTheorem` (M-L);
- `PeriodAreaFormula` and AN4;
- AN3 (XL);
- elliptic curves as `AbVar` (AV7);
- H5 (Néron models, semistable reduction);
- the objects needed for R18 and R22.

Note: `docs/research/def-faltings.md`. Log: `scratch/def-faltings/log.md`.
