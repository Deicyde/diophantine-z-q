# Vendored extract of Axiom Stacks

This directory holds 652 Lean files taken from [AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) at commit
`f56a316ddf7a930906d88b78d6f9a2668cffd0cf`, licensed under the Apache License 2.0 (`LICENSE` in this directory).
They are the import closure of the two upstream results used by `ZInQKernel/Contrib/OneProof/EllAdic/AxiomStacksFiniteHOneV1.lean`:

- `AlgebraicGeometry.ProEtale.isIso_unit_app_and_isZero_rightDerived_epsilonDirectImage` in
  `StacksFrontier/AlgebraicGeometry/ProEtale/Cohomology/ComparisonWithEtale.lean` (Stacks Project, Tag 099V);
- `Stacks.Cohomology.RightDerivedDelta.epi_map_g_of_isZero_rightDerived_one` in
  `StacksFrontier/Algebra/Homology/RightDerivedDeltaEpi.lean`.

Upstream, the same commit builds against the Lean (v4.35.0) and Mathlib (`56a005855ea1`) versions that this repository pins.

## Changes from upstream

Proofs are unchanged. The changes are:

1. **Bounded extraction.** Three files differ from upstream so that the import closure stays small:
   - `ComparisonWithEtale.lean` keeps the comparison through the full 099V proof and omits the separate 099W part
     and its derived-composition import;
   - `LimitDescentGlueing/Glueing.lean` imports the leaf `Limits/FinitePresentationModels.lean`;
   - `Limits/FinitePresentationModels.lean` holds `LimitDescent.HasFinitePresentationModels`, copied verbatim
     from upstream's `FlatImageSystem`.
2. **Module paths.** Upstream's top-level modules `StacksFrontier.*` and `StacksCore.*` are placed under
   `ZInQKernel.Contrib.OneProof.AxiomStacks.*`. Every import line is rewritten to match. Lean namespaces are unchanged.
3. **No build-time code.** Upstream's tag attributes `ega …`, `sga …` and `stacks_fixed …` (in `@[…]` and
   `attribute […]`), the commands `add_to_stacks …`, `add_to_ega …`, `add_to_sga …` and `#stacks_tags?`, and the two
   files that define them (`StacksCore/Tactic/StacksAttribute.lean` and `StacksCore/Tactic/EgaSgaAttribute.lean`)
   are removed: 1,077 attribute entries and 301 commands. Their imports are replaced by Mathlib's `Mathlib.Tactic.CrossRefAttribute`, which
   provides the `@[stacks …]` attribute that the files keep. These attributes only record bibliographic tags.
4. **Options.** Upstream compiles the package with `autoImplicit false`, `relaxedAutoImplicit false` and
   `maxSynthPendingDepth 3`. Each file sets these three options after its imports.

`PACKAGE-MANIFEST.txt` (JSON) lists, for every file, the upstream source hash and the hash of the file here.

Two files keep a `local notation`: `StacksFrontier/Homology/DerivedCategory/Monoidal/Basic.lean` here, and
`../EllAdic/ConstantSheafTransport.lean`.
