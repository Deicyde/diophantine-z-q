# H-76: Néron mapping property, surjective half

This directory proves the exact fixed proposition
`ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{u}` from
`ZInQKernel/Contrib/NeronC/NMPInjective.lean`, fixed at
`cba8157f7d5d09a4a3c8462aba2f3245494a870e`:

```lean
theorem ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj_proof :
    ZInQ.Contrib.NeronC.NeronMappingAbelianSchemeSurj.{u}
```

It extends **arbitrary scheme morphisms** between the generic fibres of abelian schemes
over any DVR `O : ValuationSubring K`. It assumes neither a Néron mapping property nor a
model-existence proposition. No additional field, residue-field, characteristic, henselian,
number-field or group-homomorphism hypothesis is imposed.

## Proof and source

The proof ports the finite extension-proof dependency closure of
[`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem)
at `6e837e75355538c7f80bab5b956861e86c4eacc2`. Its entry point is
`P2M/Sol/S_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle.lean`.
That theorem proves the stronger full Néron mapping property for arbitrary smooth test schemes.
The mathematical argument is properness at codimension one followed by Weil's extension
argument (Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2 Prop. 8 and §4.4 Thm. 1).

- `Vendor/` retains the original relative file paths of the 81-file proof closure.
  All project declarations are isolated beneath `ZInQ.Contrib.CloudW03NeronSurj.FLT`,
  rather than added to Mathlib's or other workers' namespaces.
- `PortUtil.lean` adapts the source's namespace/alias commands. Its reverting `exact`
  rejects unresolved metavariables; it changes elaboration, not the kernel's proof rules.
- `Basic.lean` supplies the source's relative group law from the kernel's existing `GrpObj`.
- `Main.lean` constructs the source abelian-scheme property bundle from the kernel's proper,
  smooth, geometrically connected group object and transfers the restriction map between
  the source's `SchemeHomOver` subtype and Mathlib's `Over` morphisms.
- `Audit.lean` verifies that the result is a theorem, has exactly the fixed Prop type,
  prints its expanded quantified type, and reports its axioms.

The port changes imports and namespaces, corrects qualified namespace closers and one-based
`TFAE.out` indices, and uses the fixed version's definitional-equality options. The annihilator
kernel proof uses explicit quotient-map computation. Two duplicate depth proof cores reuse the
same source theorem, removing 3,331 repeated lines without changing their statements. Six
unreferenced carrier self-tests were omitted; the actual extension proof was retained. Required
regular-stalk self-tests that other source modules reference were retained and adapted.

## Verification

The work is based on `f70ec251fd4bca6ae3115741c21fe661e7aaac3e`; the fixed target, its
`Objects.lean` definitions and all Lake/toolchain pins are byte-identical to the fixed revision.
Lean is `v4.35.0`, with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
No Lake configuration or pin was changed.

Run the focused checks (one compile lane; `LEAN_NUM_THREADS=2`):

```sh
lake build +ZInQKernel.Contrib.CloudW03NeronSurj.Main:olean
lake build +ZInQKernel.Contrib.CloudW03NeronSurj.Audit:olean
```

The theorem's axiom output is:

```text
[propext, Classical.choice, Quot.sound]
```

Build-by-module logs and the complete type audit are returned to the parent reviewer. No
push, merge, PR submission or independent-acceptance claim is made by this local proof port.

## Attribution

`LICENSE`, `NOTICE` and `ATTRIBUTION.md` reproduce the original project license and notices.
`NOTICE.md` and the per-file headers record the modifications. Copyright 2026 Anthropic, PBC;
the depth material also credits Imperial College London's FLT authors as recorded in the
original attribution. The source and imported Mathlib material are Apache-2.0.
