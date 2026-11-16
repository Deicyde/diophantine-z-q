# Fixed de Rham scalars over finite extensions

This is **support only**, not a proof or reduction of either open comparison:
`ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` or
`ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar`.

For every prime `p` and every finite extension `F/ℚ_p`, without an `IsGalois`
assumption, it constructs `F →ₐ[ℚ_p] BdR p` fixed by the existing action
`bdrAct p (gfToGqp p F σ)`. It then proves that `[F:ℚ_p]` divides the
`ℚ_p`-dimension of the existing Hom-form de Rham space and, for finite input,
its tensor-dual form. This is divisibility, not the comparison equality.

The source uses the existing `embF`/`gfToGqp`, the existing separable Hensel
lift through Fontaine's theta map, and the existing tensor-dual comparison
in `OneProof/H/TailS`. No new period ring, surrogate representation,
comparison premise, dependency, axiom, or printed leaf is introduced.
The local `algPlus` instance is confined to the scalar-construction section.

Two further lemmas record the generic `finrank = 0` degeneracy for infinite
input and infinite invariants, and the finiteness guard for finite nonzero
input. That degeneracy is **not** a counterexample to the actual
abelian-variety comparison: its Tate module is mathematically finite.
The existing `finiteDimensional_of_decomp` establishes that finiteness from
the Hodge–Tate decomposition.

## Verification

Base: `0caafe66103a89994198e26d8d68af6ae227ed0e`.
Lean: `v4.35.0`; Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Both new Lean modules were compiled directly from source with the pinned
compiler and explicit single-thread/resource bounds. Literal interface
checks passed. All 14 core declarations and all 3 entry theorems print
exactly `[propext, Classical.choice, Quot.sound]`.

A separate non-author AI reviewer independently rebuilt both modules in a
separate output root, checked the three literal interfaces, their
specialization at `F = ℚ_p`, scalar injectivity and fixedness in the exact
`drAct` form, all 17 axiom lists, and the prohibited-code/public-hygiene
scan. That review passed for these two modules. It is not a cold rebuild of
all imported libraries, a human literature reading, or a full-field closure.
The two benign core style/unused-section warnings and all failed development
checks are retained in the private evidence; entry and final check were clean.

The contribution imports only the defining `TailS` module and existing G9
material, never `OneProof.Main`. Existing source modules and pins are
untouched. The tensor-map proof is extracted from the existing `TailS`
proof; no external proof source is newly vendored.

The prescribed current-main `#discharges` result is reported separately in
the pull request. No comparison discharge is claimed. The support directory
is outside the automatic OneProof-only check's scope, and the default
`lake build` does not certify this contribution.

AI-assisted construction and independent AI native/source review.
No serving-model attestation or human mathematical acceptance is claimed.
Private evidence bundle available to the maintainer.
