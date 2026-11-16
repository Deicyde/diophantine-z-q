# Atlas Legendre three-square source port

## Upstream source

- Repository: https://github.com/facebookresearch/atlas-lean
- Commit: `8860f7b55276b96e51df600021845dd5eb48f5ab`
- Original file: `MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquare.lean`
- Source link: https://github.com/facebookresearch/atlas-lean/blob/8860f7b55276b96e51df600021845dd5eb48f5ab/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquare.lean
- Original file SHA-256: `a902763f2e8c6ca272f03774536d58b93c99f5843214288efe226f5e767da284`
- Original copyright header is preserved in `Atlas.lean`.
- The complete upstream `LICENSE`, including its first-line prefatory text, is preserved byte-for-byte in this directory. SHA-256: `fc78801eadec58b04e0d5cabe735eb6808e23f47b0cb92b89b55792019b54131`.
- The pinned upstream root directory lists no separate `NOTICE` file.

## Changes made in this contribution

1. Relocate the file to `ZInQKernel/Contrib/OneProof/LegendreThreeSquares/Atlas.lean`.
2. Add this source/change record and a prominent comment in the modified source.
3. Enclose the original declarations in `ZInQ.Contrib.OneProof.LegendreThreeSquares.Atlas`, avoiding additions to the project's root `Nat` namespace.

The original import list and proof bodies are unchanged. No new dependency or Lake configuration is introduced. Upstream and this project both use Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The separate entry module `ZInQKernel.Contrib.OneProof.LegendreThreeSquares` imports the exact defining module `ZInQKernel.Contrib.OneProof.TYZLemma29Mod2`, never `ZInQKernel.OneProof.Main`. Its bridge turns `∀ a b, n ≠ 4^a(8b+7)` into the equivalent negated existential, casts natural witnesses to integers, and reverses the equality. The exported theorem has type `ZInQ.Contrib.TYZDecomp.H29Split.LegendreThreeSquares`, with no extra outer assumptions.

## Proof content and scope

The upstream proof implements Ankeny's route: Dirichlet's theorem on primes in arithmetic progressions, quadratic reciprocity, a genuine Minkowski lattice point, and the two-square valuation criterion. It treats zero explicitly and removes fourth powers and square factors before treating the squarefree residue classes. It does not take Legendre, a local-global theorem, a finite computation, or the desired conclusion as an additional assumption.

This is an AI-assisted formal-source port and bridge. Reading the formal source is not a printed-edition statement check and clears no literature-reading flag. This contribution supplies only `hL3s`; it makes no claim that the full unconditional H10/Q project is complete. Compiler/type/axiom/discharge receipts and independent review are supplied in the PR, separately from this source notice.
