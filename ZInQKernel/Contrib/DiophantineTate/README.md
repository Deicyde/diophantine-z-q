# Valuation and local-étale suppliers

This contribution provides three concrete inputs for geometric reduction:

- `DiophantineTate.ActualResidue.isAlgClosed_residueField`: for every algebraically closed field `Ω : Type` and every actual `ValuationSubring Ω`, its actual residue field is algebraically closed.
- `DiophantineTate.ActualHenselian.henselianLocalRing`: that same valuation subring is Henselian, without a DVR, Noetherian or completeness premise. The proof uses monic splitting and matches the prescribed residue class.
- `AxiomBridge.LocalEtaleSectionInjectivity.sections_reduction_injective`: existing sections of an étale scheme over any local commutative ring are determined by restriction to the actual residue quotient. This proves uniqueness, not existence or lifting.

`ActualResidue.monic_root_mem` supplies the integral-root containment used by the Henselian proof. It does not require the ambient field to be algebraically closed. No global instances are registered.

## Reuse and scope

The fork already proves the rational-closure specialization in `AlgFrobRedRed.residueAlgClosed` (`Contrib/FrobChain/AlgFrobRed.lean`). This contribution does **not** reimplement its residue-field identification or claim that specialization is an open gap. The all-`Ω` API and root-containment helper support the separate Henselian construction.

The three proof modules import only Mathlib and the sibling `ActualResidue` module. No Objects, Mordell, Stacks, old private bridge, Tate equivalence, model-existence or Frobenius result is imported or replaced. The original Type0 targets, actual carriers and residue maps are preserved. Pins and existing sources are unchanged.

These inputs are not a proof of reduction surjectivity, C10, or Hilbert 10.

## Verification

Tested on Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and the repository's unchanged Mathlib pin `56a005855ea17e0b0958f73ec801ae140b0a1679`.

Each source module and `Expected.lean` was compiled separately with `lean -j1` in `lake env`. `Audit.lean` then imported a separate trust-zero validation environment and checked four complete actual types against independent literal proposition **values**, the actual stored bodies, LP[] fresh checking-additions, annotation-sensitive readbacks and returned-environment bodies. Four extra-premise and four corrupt-body controls were also checked. All eight type/available-opaque-value dependency walks use only `propext`, `Classical.choice`, and `Quot.sound`.

Run the checks with:

```sh
lake build +ZInQKernel.Contrib.DiophantineTate.ActualResidue
lake build +ZInQKernel.Contrib.DiophantineTate.ActualHenselian
lake build +ZInQKernel.Contrib.DiophantineTate.LocalEtaleSectionInjectivity
lake build +ZInQKernel.Contrib.DiophantineTate.Expected
lake build +ZInQKernel.Contrib.DiophantineTate.Audit
```

The audit's completion marker records four checked stored theorems and eight closures; the file also prints the four axiom reports. Original style/unused-tactic warnings are retained, not suppressed. The preexisting transparency setting is scoped to one local-étale helper and is an elaborator setting, not a kernel-check bypass.

These are selected theorem/body and dependency checks, **not** raw replay of every imported library proof, a recursor-rule serialization audit, or whole-project/hosted-CI acceptance.

## Provenance

AI tools assisted the proof construction and independent source review. The mathematical code was transported without changing its executable proof lines; private development comments were replaced by this public explanation. The fresh compilation and selected kernel/axiom checks are distinct from earlier development-stage checks. Mathlib supplies the integral-closure, polynomial, open-diagonal and local-spectrum primitives.
