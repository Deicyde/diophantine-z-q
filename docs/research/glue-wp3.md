# glue-wp3: glue-descent's `LeafHasse`, `LeafLocalTwo` from the announced leaves T14-T15

## Result (VERIFIED: compiled with `lake env lean`, no sorry, axioms propext, Classical.choice, Quot.sound)

WP3's first item (rv-hsyn repair 3) is closed. In `scratch/glue-wp3/WP3.lean`:

| theorem | statement |
|---|---|
| `GlueWP3.leafHasse_of_T14` | `PkgI6.BrauerHasse2C → PkgI6.BrauerReciprocity2C → GlueDescent.B2Q.LeafHasse` |
| `GlueWP3.leafLocalTwo_of_T15` | `PkgI6.LocalH2CardC → GlueDescent.B2Q.LeafLocalTwo` |
| `GlueWP3.b3_degree_le_QM_of_T14_T15` | glue-descent's `GlueDescent.B3Q.b3_degree_le_QM` (B2-B3 with the constants `[L':ℚ] ≤ Q_R·M_S(u)`) with `LeafHasse`, `LeafLocalTwo` replaced by `BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`; its other hypotheses are `LeafSqrtCrit` (T30) and `LeafUnramified` (T31) |
| `GlueWP3.brauerHasse2C_of_leafHasse` | `LeafHasse → BrauerHasse2C` |
| `GlueWP3.leafHasse_iff` | given `BrauerReciprocity2C`: `LeafHasse ↔ BrauerHasse2C` |
| `GlueWP3.leafLocalTwo_iff` | `LeafLocalTwo ↔` the "two nontrivial classes differ by a coboundary" half of `H2TwoClasses (G_{ℚ_p})` for every `p` |

So B2-B3 now follow from fields of the leaf bundle `TextbookLeaves` of
`scratch/h-decomposition/Leaves.lean`: `t14a`, `t14b`, `t15`, `t30`, `t31`. No gap remains
between glue-descent's forms and the announced T14-T15. The converses show that glue-descent's forms
say no more than the announced leaves: each is equivalent to the announced leaf or to part of it, given
reciprocity.

## The glue

1. **±1 versus ℤ/2 coefficients.** glue-descent uses locally constant `ℂˣ`-valued cochains with
   square `1` and multiplicative cocycle and coboundary conditions (`IsSignCocycle`, `SignCob`, `dB`).
   pkg-I6 uses continuous `ZMod 2`-valued inhomogeneous cochains (`IsCocycle2`, `IsCoboundary2`).
   The dictionary `sgn : ZMod 2 → ℂˣ` (`0 ↦ 1`, `1 ↦ -1`) with inverse `unsgn` on `{±1}`
   satisfies `isCocycle2_iff : IsCocycle2 ε ↔ IsSignCocycle (sgn ∘ ε)` and
   `isCoboundary2_iff : IsCoboundary2 ε ↔ SignCob (sgn ∘ ε)` over any topological group, and every
   sign cocycle has the form `sgn ∘ ε` (`exists_of_isSignCocycle`). Continuity into `ZMod 2` is local
   constancy because Mathlib's topology on `ZMod N` is discrete (`Mathlib/Topology/Instances/ZMod.lean`).
   The sign conventions match: pkg-I6's `ε b c - ε (ab) c + ε a (bc) - ε a b = 0` is glue-descent's
   `η(xy,z)η(x,y) = η(y,z)η(x,yz)`, and `f b - f(ab) + f a` is `γ x γ y γ(xy)⁻¹`.
2. **Restriction.** glue-descent's `pull (resp p)` and pkg-I6's `resC ℚ_[p]` compose with the same
   Mathlib map `Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])`, so `pull_resp_sgnC` holds by `rfl`.
3. **The real place.** `LeafHasse` has hypotheses at the finite places only, while `BrauerHasse2C`
   also asks for triviality at `ℝ`. `real_of_finite` supplies it from `BrauerReciprocity2C`: with no
   locally nontrivial finite place, the parity `0 + [nontrivial at ∞]` must be even. (pkg-I6's
   `cob_of_same_finite_support` uses the same argument.)
4. **Inflation.** In B2, inflation from `Gal(L/ℚ)` enters only through T31 (`LeafUnramified`,
   `InflatedFrom`). The cochain `ε` of B2 is a cochain on `G_ℚ`, which is what I6.2′ quantifies over,
   so no comparison is needed for T14-T15.

Unused parts of the announced leaves: the existence half of `H2TwoClasses`, and the real half of
`LocalH2CardC`.

## Files (all in `scratch/glue-wp3/`)

- `WP3.lean`: new. It also holds verbatim copies of pkg-I6's definitions `IsCocycle2`, `IsCoboundary2`,
  `resC`, `BrauerHasse2C`, `BrauerReciprocity2C`, `H2TwoClasses` and `LocalH2CardC`. A substring check
  found each block, verbatim, in `scratch/pkg-I6/I6.lean` and in `Leaves.lean` L4153-4196.
- `Cochain`, `Constants`, `Chi`, `B2Glue`, `B2Assembly`, `B3Assembly.lean`: byte-identical copies of
  `scratch/glue-descent/` (checked with `cmp`).
- `build.sh`: compiles the chain to `scratch/glue-wp3/.lake/out` (about 1 min 45 s), then `WP3.lean`
  (5 s). `Constants` needs the project's `ZInQKernel.Compiler.Precision.HeightConstant` olean.
- `log.md`: the results log.

## Integration into `Leaves.lean`

`Leaves.lean` contains `GlueDescent.B2Q` and the `PkgI6` cochain definitions, so the section
`GlueWP3` of `WP3.lean` (from `sgn` to `b3_degree_le_QM_of_T14_T15`) can be pasted after both. Then
`TextbookLeaves → LeafHasse` is `leafHasse_of_T14 t.t14a t.t14b`, and
`TextbookLeaves → LeafLocalTwo` is `leafLocalTwo_of_T15 t.t15`.

## What remains (outside this item of WP3)

T30 (`LeafSqrtCrit`) and T31 (`LeafUnramified`) are still leaves, and their local-field parts are glue
that glue-I6-rest left open. Also open: L' is unramified outside T (this needs T32), and ε has not been
instantiated on the actual algebra A. The other WP3 items (A6, C2/E1, D1, ...) are untouched.
