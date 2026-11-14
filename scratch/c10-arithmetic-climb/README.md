# Optional C10 arithmetic primitives

This source set adds three independently checked primitives to the already published S1/S2 source branch. It does not change the default Lean root, pins, caches, workflows, PR53/PR68, or main.

## Contents

- `index/`: the actual subgroup fixing a given number-field embedding has exact index equal to its rational degree. Existing Mathlib Galois theory is reused. The S1/S2 caller binding fills its index cast only after an explicit range identification.
- `character/`: descent of the actual `GlueDescent.chi Tm` through the caller's fixed complex place, retaining its level, exact order, oddness and nonunit zero values.
- `beta/`: transport of a given complex B2 cochain through that same place, with literal value images, square/cochain equations and local constancy. The sign cocycle can also be lifted from its own given square-one values. The actual B2 adapter derives a Qbar datum conditionally under the original four leaves and L/epsilon/T hypotheses; it proves none of those arithmetic inputs.
- `specs/`: the independently frozen statement definitions consumed by the proofs. Compiling a specification is not a proof of it.
- `controls/`: positive application twins and structural rejection fixtures. They are not mathematical counterexamples; the characteristic and infinite-dimension guards in the index source are conditional/symbolic as documented.

Source proof bytes are identical to the private compiled and independently replayed inputs; `SOURCE-MANIFEST.json` gives their SHA256 identities. The public history retains the original S1/S2 commit and sources.

## Remaining inputs

The reverse Galois map's actual range, the global abelian variety/Tate comparison/scalar bundle and all B2 literature/geometry inputs remain unconstructed here. No normalization is slipped in: beta(1)=1 requires epsilon(1,1)=1. The beta result is unit-valued; the field-valued C10 adapter and common C/Qbar/finite-E identifications are separate joins. Nothing here proves C10, a stable height bound or Hilbert10.

The Hodge coefficient core/first-jet investigation is a separate source world and is deliberately not included as an integrated provider in this branch.

## Reproduction

Use the repository's pinned Lean 4.35.0 and Mathlib revision. First build the existing project imports `ZInQKernel.HDecomp.C10.C10`, `ZInQKernel.HDecomp.Descent.Chi` and `ZInQKernel.HDecomp.Descent.B2Assembly`. The optional index caller bind additionally consumes the unchanged #62 `ZInQKernel.HDecomp.C10.Link` and `ZInQKernel.HDecomp.I3Linalg.C2` sources identified in the original S1Mapped header; those are separate, non-default input sources, not newly constructed here. Do not change the pins or substitute definitions to make a candidate compile.

Set an isolated output directory at the front of the existing Lake `LEAN_PATH`. Compile each source from its own directory with `lean -j1 -R . -o <output>/<module>.olean <module>.lean`, so its original bare import name is preserved. Build the previously published S1Twist, S2RelativeMaschke, S1Mapped and S2Fill modules first for the index caller binding; then the specs, index, character and beta modules in dependency order. Checks and boundary files must compile. Each `Bad*` file is expected to fail for the cause named in its header; the positive range-gate twin must pass.

Evidence is private pinned-source compilation plus bounded independent replay, not designated review-App acceptance or a fresh proof check of every imported library theorem. Historical failed sources that were edited without retaining bytes are explicitly unretained in the evidence archive; their diagnostics are not providers.
