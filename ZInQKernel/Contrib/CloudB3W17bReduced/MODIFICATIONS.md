# Port modifications

Source: AxiomMath/Stacks, revision `c496df0d9beea9deaeabcea8492605f9a0a2313b`.
Target: Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Mechanical transformations

- Remap the bounded StacksCore/StacksFrontier import closure to
  `ZInQKernel.Contrib.CloudB3W17bReduced.Port`.
- Omit imports of the metadata-only Stacks and EGA/SGA attribute modules.
- Omit only Stacks/SGA/EGA metadata attributes. Ordinary proof-related
  attributes such as `instance`, `simp`, `reassoc` and `expose` are retained.
- Omit the remaining metadata-only `add_to_stacks`, `add_to_sga` and
  `add_to_ega` commands in PerfectClosure and Kaehler/BaseChange, and the
  metadata-only `sga` attribute on the existing IsSeparablyGenerated declaration.
- Preserve upstream licence, source credits, mathematical definitions and theorem statements.

## Proof-API adaptations

Only `StacksFrontier/RingTheory/FormallySmooth/Field.lean` needs a proof-API
adaptation beyond metadata removal:

- Specify the actual localization target instead of leaving it as an inferred placeholder.
- Make the existing intermediate-field/tensor algebra and ring instances explicit where
  fixed-pin inference cannot choose the intended instance path.
- Use a private generic `IsDomain → IsReduced` theorem specialized explicitly to the actual
  subtype tensor carrier. This avoids a carrier-inference diamond; it introduces no premise
  and proves the same ordinary reducedness fact by existing instances.
- Use the actual explicit F/K/T parameters of the separable base-change theorem with
  reducible-instance elaboration. The mathematical statement and tensor product are unchanged.
- Use declaration elaboration transparency options for these instance wrappers, and ordinary
  `let` proof-local instances rather than unnecessary inlining `letI`.

No new axiom, admitted proof, evaluator, parser, notation definition, macro or elaborator is added.
The independent verification should compile the delivered sources and run the prescribed checker;
the package is not an analytic GAGA proof.
