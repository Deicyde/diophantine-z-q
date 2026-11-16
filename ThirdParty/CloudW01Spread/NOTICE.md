# Source provenance and modification notice

The vendored `StacksCore/` and `StacksFrontier/` files in this directory are
ported from **AxiomMath/Stacks**, immutable revision
`c496df0d9beea9deaeabcea8492605f9a0a2313b`:
https://github.com/AxiomMath/Stacks/tree/c496df0d9beea9deaeabcea8492605f9a0a2313b

They are released by that project under **Apache-2.0**. The complete upstream
license is retained here as `LICENSE`; existing source comments are retained.
`SOURCE_MANIFEST.json` records every copied source path, its immutable raw URL,
its SHA-256 digest, and its destination. Only the explicit dependency closures
needed by these proofs are included, not the upstream root library.

## Port modifications (2026-11-14)

- Import paths beginning `StacksCore` or `StacksFrontier` are remapped beneath
  `ZInQKernel.Contrib.CloudW01Spread`; mathematical declaration namespaces are
  retained. Each copied file carries a prominent modification notice.
- `LimitDescentGlueing/Glueing.lean`: the unrelated `Limits.FlatImageSystem`
  import, its final `hasFinitePresentationModels` corollary, and the corresponding
  documentation bullet are omitted. The essential-surjectivity proofs are unchanged.
- `LimitDescentGlueing/GlueingAux1.lean`: one trailing whitespace character is
  removed; its statements and proofs are unchanged.
- `RingTheory/SpreadingOut/Smooth.lean`: `formallySmooth_bcHom_iff` transports
  formal smoothness using `(Algebra.FormallySmooth.iff_of_equiv e).symm` instead of
  separately elaborating two `of_equiv` terms. This fixes a Lean 4.35 instance
  elaboration failure; the statement and mathematical argument are unchanged.

## Exact target bridges

The new bridge modules `FinitePresentation.lean` and `Smooth.lean` are authored
for this contribution, with Metamate/agentcloud assistance. They target the
unchanged Props in `Contrib/SpreadOut/Spread.lean` at project revision
`cba8157f7d5d09a4a3c8462aba2f3245494a870e`.

- Finite presentation: upstream
  `AlgebraicGeometry.LimitDescent.exists_model_of_finitePresentation_of_essentiallySmall`,
  `StacksFrontier/AlgebraicGeometry/LimitDescentGlueing/Glueing.lean`, lines 626–635
  (Stacks 01ZM(1)). The bridge only unpacks the conjunction defining finite
  presentation and reverses the isomorphism.
- Smoothness: upstream
  `AlgebraicGeometry.exists_smooth_baseChange_of_smooth_limitBaseChange`,
  `StacksFrontier/AlgebraicGeometry/Limits/DescendingMorphisms/Smooth.lean`,
  lines 350–410 (Stacks 0C0C; EGA IV 17.7.8(ii)). The bridge applies it to the
  structure map viewed as a morphism to the identity object in an over category.
- The generic identity-object helper adapts
  `AlgebraicGeometry.overPullback_map_terminal_iff` from
  `StacksFrontier/AlgebraicGeometry/Limits/ProperImageSystemModels.lean`,
  lines 101–109, at the same immutable revision. That large module is not imported.

The upstream Stacks manifest and this project's manifest both pin Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` (Lean 4.35.0). No dependency pin,
original target definition, root import, or Lake configuration is changed.
No nonexistent `wip/axiom-bridge` equivalence is assumed.

Build and axiom evidence is recorded in the worker report. A compiled helper
or conditional theorem is not represented as closure of a fixed target.
