# S1/S2 semisimplicity transport — separate source snapshot

This optional directory publishes the independently checked S1/S2 sources without changing the repository's default libraries, original C10 consumer, pins, cache, workflows or in-flight PRs. It is not a PR, a required-review acceptance or a main-branch integration.

## Generic results

- `S1Twist.lean`: a pointwise nonzero scalar twist preserves the invariant-subspace lattice and semisimplicity. It also proves the carrier-level transport facts and derives nonvanishing of a scalar presenting a group representation on a nontrivial carrier.
- `S2RelativeMaschke.lean`: semisimplicity of restriction to `H` implies semisimplicity of the full representation when `(H.index : k) ≠ 0`. The proof averages over finite left cosets; it requires neither a finite whole group, normality of `H`, finite-dimensionality nor topology.
- `CoreCheck.lean`: explicit statement applications and axiom reports for those generic results.
- `neg/S1Necessity.lean` and `neg/NegS2.lean`: compiled counterexamples showing why scalar nonvanishing, finite index and invertibility of the index matter. `neg/BadS1ZeroScalar.lean` must be rejected.

The copied proof/control files retain their exact reviewed bytes and original module names. Their references to a private packet and to S2 as a future task are historical authoring context: S2 is now proved in `S2RelativeMaschke.lean` and fills that interface in `S2Fill.lean`.

## Conditional C10 application — not arithmetic closure

`S1Mapped.lean`, `S1Checks.lean` and `S2Fill.lean` use the original `GlueC10Link`/`GlueI3` definitions. They are preserved applications, not substitutes for the actual geometry. The mapped helper trades `hr` for a stronger global supplier bundle: one number field, one abelian variety, a group map with finite invertible index, and one global Tate-action comparison up to a nonzero scalar. That bundle is **not constructed**. The per-Frobenius existential `hSq` does not imply that global comparison.

The original C10 inputs for modular semisimplicity, C9, continuity, the actual Frobenius squares and `hM` remain binders. S2 removes only the generic relative-Maschke premise. The positive `neg/HelperAppliesOverQ.lean` is a typed application test with the geometry still as binders, not a non-vacuity witness. `neg/BadS1HelperNoNumberField.lean` must fail at the helper's number-field requirement; the older `neg/BadS1NoNumberField.lean` is only a class fixture.

**C10, H and Hilbert10 remain unfinished.**

## Pinned environment and dependencies

The source snapshot is based on upstream `fb2f78e143af2f6de71ca43e37498c229cde1c6b`, with Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The generic S1/S2 modules need only their Mathlib imports. The mapped files additionally need the two unchanged selected PR62 modules at `e303a42543e9adf89aa70075372b622f4870a770`:

- [`ZInQKernel/HDecomp/C10/Link.lean`](https://github.com/elliotglazer/diophantine-z-q/blob/e303a42543e9adf89aa70075372b622f4870a770/ZInQKernel/HDecomp/C10/Link.lean), SHA-256 `0c72f9e57e7557aa61dd7c1fc847111f639d7b86105b9939aabb46e1e7e81b55`.
- [`ZInQKernel/HDecomp/I3Linalg/C2.lean`](https://github.com/elliotglazer/diophantine-z-q/blob/e303a42543e9adf89aa70075372b622f4870a770/ZInQKernel/HDecomp/I3Linalg/C2.lean), SHA-256 `365d409cde18016e314d4a867c5aad057d99ff91ed8ca5e4e93439fd015c22c4`.

They were compiled from those exact sources in the focused private validation environment, with the canonical project modules. They are not duplicated or silently installed by this snapshot. There is no assertion that a full mapped package can build from upstream main alone before those dependencies are supplied and reconciled.

To replay the generic modules, work in this directory with absolute search paths for the pinned Mathlib/package outputs; place all new outputs in a private directory:

```sh
out=$(mktemp -d)
export LEAN_PATH="$out:$LEAN_PATH"
lean -j1 -o "$out/S1Twist.olean" S1Twist.lean
lean -j1 -o "$out/S2RelativeMaschke.olean" S2RelativeMaschke.lean
lean -j1 CoreCheck.lean
lean -j1 neg/S1Necessity.lean
lean -j1 neg/NegS2.lean
# This must fail on the missing nonzero-scalar obligation:
lean -j1 neg/BadS1ZeroScalar.lean
```

## Evidence boundary

The existing evidence includes ordinary private compilation, standard-axiom reports, source/type/caller comparisons, retained failures and an independent bounded replay. Reporting and control-label corrections are preserved separately; old unretained timing figures are not replay measurements. This is not a clean-room run, replay of every imported-library proof, current hosted CI or designated Protocol B/App acceptance. `SOURCE-MANIFEST.json` binds this source snapshot; it is not an approval certificate.
