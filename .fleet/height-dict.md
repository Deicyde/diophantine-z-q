# height-dict (fleet note)

**Result: the kernel-height dictionary is proved, and both rows are restated over a printed stable height
(VERIFIED: compiled, standard axioms).** The 11-16 pass gave three reasons for rating `bostLowerBound` and
`gaudronRemondThm14` as consequences:

1. Φ biholomorphic onto `A^an`;
2. the torus integral of `|ω ∧ ω̄|`;
3. `ω = e*Ω¹` (EGA IV 17.2.5).

All three are now Lean theorems. `ZInQ.HeightDict.IsPrintedStableHeight` builds Faltings' stable height as
the print does, with no uniformization in the definition:

- the Néron model over a semistable field;
- `ω = ⋀^g Γ(S, e*Ω¹)` from the Kähler stalks `𝒪_{S,s} ⊗ Ω[𝒪_{𝒩,e(s)}/𝓞_L]`;
- the metric `(i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄`, as the total mass of the invariant measure on `A_τ(ℂ)` (analytic
  topology `anTop`) normalized at `1` in algebraic coordinates.

What compiles, all new files under `ZInQKernel/Contrib/OneProof/` (`lake build
ZInQKernel.Contrib.OneProof.HeightDictionary` succeeds):

- `HeightDictionary.lean`:
  - the printed definitions;
  - the leaves `BostLowerBoundPrinted` and `GaudronRemondThm14Printed`;
  - `bostLowerBound_of_printed` and `gaudronRemondThm14_of_printed`, which give the two fields from the
    printed leaves plus the existing textbook fields `uniformizationLeafAll` and `mumfordTorsionAlgClosed`
    (for T35);
  - `isPrintedStableHeight_iff` (the printed height equals the kernel's);
  - `exists_isNormalizedBy` and `isFaltingsMetricSq_iff` (the printed metric is non-vacuous and has a single
    value);
  - also `JavanpeykarBoundPrinted` and `PazukiCor13UpperPrinted` with their consumer forms.
- `HeightDictionary/TorusVolume.lean` (Mathlib only): the volume of a compact group uniformized by `ℂ^g/Λ`,
  via Haar uniqueness, a fundamental domain containing a ball, and Jacobian estimates.
- `HeightDictionary/Holomorphic.lean` (Mathlib only): holomorphic ⇒ strictly differentiable in several
  variables, via the Cauchy integral. This is a Mathlib 4.35 gap.
- `HeightDictionary/Conormal.lean`: `θ = kerCotangentToTensor`. The kernel's conormal lattice `omegaAt s` maps
  onto the image of `(e*Ω¹)_s` (`omegaAt_map`), `θ` is injective, and `printedOmega_eq`.

Checks:

- `#discharges` (`scratch/height-dict/discharges.txt`): `bostLowerBound` and `gaudronRemondThm14` are
  discharged by `ZInQ.HeightDict.*_of_printed`. Each still assumes its printed leaf, `UniformizationLeafAll`
  and `MumfordTorsionAlgClosed`. Axioms are standard.
- Autofold spec `scratch/height-dict/autofold.json`: dry run exit 0, 34/11 → 34/11 (this base's `kinds.tsv`
  rates both rows LEAF; −2 GLUE under the 11-16 consequence rating). `FoldDryRun.lean` compiles;
  `sixContactMin_of_open36` has standard axioms.
- Optional `autofold-all4.json` also replaces the Javanpeykar and Pazuki rows. Same counts; it compiles.

Ratings: both new leaves are **printed form**. They are the old statements with the height replaced by the
printed definition. The remaining readings are definition-level:

- R1: the stalks of `Ω_{𝒩/S}` are Kähler differentials of the local rings, and global sections are the
  intersection of the stalks. Mathlib has no relative Ω sheaf.
- R2: `anTop` is the analytic topology of `A_τ(ℂ)`.
- R3: "∫ of the invariant form" is the total mass of the invariant measure normalized at `1`.

Route: (a), which also gives (b). Route (b) alone is not shorter, since its consumer form needs "printed ⇒
kernel". sga1-etale's manifold atlas is not needed.

What remains:

- Statement checks of the two leaves against the prints. Bost's display is UNVERIFIED.
- Proposed `locators.md` rows are in the report.
- `gaudronRemondThm14` is also claimed by gr14-narrow. The two pieces of work compose (restate its form over
  `IsPrintedStableHeight`).

Report: `docs/research/height-dict.md`.
