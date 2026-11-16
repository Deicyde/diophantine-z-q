# Multiplication étaleness over an arbitrary commutative base

This contribution proves **H-101**, the exact native proposition
`AvSplit.T4.MulEtaleAbelianScheme`.

The main theorem is
`H101DirectFieldRoute.multiplication_etale` in [`Direct/AllBase.lean`](Direct/AllBase.lean).
It quantifies over every `O : Type` with `CommRing O`, the given
`A : Grp (Over (Spec (.of O)))` with `PkgI2.IsAbelianScheme A`, and every natural
`m` satisfying `IsUnit (m : O)`. Its conclusion is native `Etale` for the
pointwise multiplication morphism `(𝟙 A.X ^ m).left`.

There is no field, Noetherian, DVR, Henselian, nontrivial-base or positive-index
restriction. No desired flatness, étaleness, cotangent-bijection or comparison
square is supplied as a new assumption. Neither the native target, its group
carrier, its group law, the root dependencies nor the Lean/Mathlib pins are changed.

## Proof route

1. Native tangent multiplication at the identity is transported to the actual
   relative derivations and actual cotangent map, retaining the stalk and residue
   scalar structures.
2. The local cotangent criterion proves formal étaleness of the actual identity
   stalk map. An actual affine neighbourhood promotes it to an étale open.
3. Translation, algebraic-closure base change, closed-point coverage and native
   descent prove multiplication étaleness over every field.
4. The actual residue fibres of the given abelian scheme have the required
   smoothness, properness and geometric integrality. Their actual multiplication
   maps are identified through the proved `Over.w` equality-domain isomorphism.
5. A smooth fibre detector proves étaleness over the arbitrary base. Its quotient
   stalk maps, quotient-to-fibre equivalences, coefficient algebras, scalar towers
   and two pushouts are constructed, rather than supplied as compatibility inputs.

[`Direct/NativeChecks.lean`](Direct/NativeChecks.lean) supplies the unchanged native
H-101 proposition and applies the existing native T4
`reductionTorsionBijective_of_mulEtale` consumer to it.

## Reproduce the checks

Use the repository's pinned toolchain and dependencies; do not run `lake update`.
After the normal Mathlib cache setup, run:

```sh
lake build ZInQKernel.Contrib.MulEtale.Direct.AllBase
lake build ZInQKernel.Contrib.MulEtale.Direct.AllBaseAudit
lake build ZInQKernel.Contrib.MulEtale.Direct.NativeChecks
```

[`Direct/AllBaseAudit.lean`](Direct/AllBaseAudit.lean) checks the full theorem TYPE
against an independently written literal proposition VALUE in
[`Expected.lean`](Expected.lean). It checks the actual stored proof body, empty
universe-parameter lists and ordered outer binder flags, makes a fresh unchanged
kernel checking-addition, verifies type/body/name readback and rechecks the body
in the returned environment. An extra-`False` premise and a corrupt `True.intro`
body are negative controls. Two dependency walks reject unsafe, partial, missing
or nonstandard-axiom dependencies. The permitted axiom set is only `propext`,
`Classical.choice` and `Quot.sound`.

The validation imports use trust level zero. The resource arguments to
`addDeclCore` are bounds, not trust settings. Expression readback is not proof
serialization, and the type/available-opaque-value dependency walk is not a raw
replay of every imported library proof or recursor-rule body.

## Source provenance and scope

See [`NOTICE.md`](NOTICE.md) for the reused AxiomMath/Stacks sources. Original
tangent declaration namespaces are retained. The four shared fibre-stalk helper
modules retain their isolated mathematical declarations and share one genuine
citation-attribute module pair, avoiding duplicate tactic registrations.

This contribution was developed with AI assistance through Metamate. The source,
exact contract, selected audit execution and native consumer were independently
reviewed; that qualification is distinct from hosted CI or a merge.

**H-101 is one leaf, not the entire Diophantine Z–Q/Hilbert 10 proof.** This module
does not discharge the remaining arithmetic/geometric or literature inputs of
the headline theorem.
