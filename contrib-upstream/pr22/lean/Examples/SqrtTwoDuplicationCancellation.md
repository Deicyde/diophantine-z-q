# Local cancellation for square-root-two duplication

This standalone helper formalizes an existing arithmetic calculation. Its public
endpoint is
`ZInQ.ModelDuplicationCancellation.primitive_duplication_local` in
[SqrtTwoDuplicationCancellation.lean](../../ZInQKernel/Contrib/SqrtTwoDuplicationCancellation.lean).
For arbitrary `a b : Zsqrtd 2` with `Ideal.span {a, b} = ⊤`, put
`root = √2`, `delta = 3 - root`,
`F = (a^2 + delta^2*b^2)^2`, `G = 4*a*b*(a^2 - delta^2*b^2)` and
`I = Ideal.span {F, G}`. The theorem proves all three statements:

- `¬ I ≤ (Ideal.span {root})^7`;
- `¬ I ≤ (Ideal.span {delta})^5`;
- every prime ideal containing `I` equals `(root)` or `(delta)`.

There are no nonzero-coordinate or nonzero-form assumptions. This is an ideal
statement in an explicit integral order. Identifying that order with a number
field's integers, choosing primitive projective representatives, interpreting
ideal powers as valuations, estimating ideal norms and deriving the height
inequality remain separate obligations. No elliptic-curve, generator, height or
Z-in-Q theorem is claimed. The external-open-problem KPI increment is zero.

## Provenance and application scope

The proof was ported from
`D5/S3/Factorization/QuadraticIdeals/SqrtTwoDuplicationCancellation.lean`, source
commit `c3cac72be938ba25b9045b306f34f5b71a5e55b0`, SHA-256
`7d661808e5203ef2637d6034a70c4b3f098233dcc7d54853151b763eebd7a877`.
Only module/public syntax, namespace, notices and diagnostic placement changed;
the mathematical definitions, theorem telescope and proof bodies are unchanged.
Codex performed this packaging and CLI validation; it supplies no independent
acceptance of its own port. Earlier supplied review claims are not adopted as
review of this revision.

The existing mathematical source is
[`prop:generator`, lines 370–386](https://github.com/elliotglazer/diophantine-z-q/blob/9c0b3aba60d90fdcac82115f0582a6f52f1054f7/manuscripts/quartic_v13.tex#L370).
That manuscript's SHA-256 is
`9db71bbfcefb37db56eabcf40a5f9dd85de9ed58294635da3dbf6d4f5caa8fcd`.
The local cancellation assertion feeds the lower duplication-height inequality
with `log 392`. The port implements an explicit-order part of that assertion;
it does not supply the bridges to the manuscript's number-field height or alter
the manuscript. No historical objection is classified or closed here, and no
global priority or historical completeness claim is made.

The endpoint depends on the private dyadic numerator bound, norm-seven
numerator bound, prime-support lemma and the two maximal-ideal lemmas in the
same file. Its five Mathlib imports are listed there, at revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`; all nine Git dependency pins are in the
unchanged root [manifest](../../lake-manifest.json), alongside the local `z_in_q`
package. Important applications include
`Zsqrtd.lift` and `norm_eq_one_iff` in `Mathlib/NumberTheory/Zsqrtd/Basic.lean`,
`RingHom.ker_isPrime` and `ker_isMaximal_of_surjective` in
`Mathlib/RingTheory/Ideal/Maps.lean`, and `Ideal.mem_span_pair`,
`span_singleton_pow` and `span_singleton_prime` in the imported ideal API.
These formal dependencies are used through their checked statements; there is
no admitted arithmetic premise or new appeal to an unpublished external theorem.

The application comparison for this partial endpoint is as follows. Independent
review of both this inventory and these comparisons remains pending.

| Obligation | Required and constructed inputs; derivation and evidence |
| --- | --- |
| Source hypotheses | The primitive-pair hypothesis is exactly `Ideal.span {a,b} = ⊤`. The endpoint derives `IsCoprime a b` with `Ideal.mem_span_pair`; no assumption is added. |
| Constructed objects | `Order`, `root`, `delta`, `numerator`, `denominator` and `commonIdeal` are explicit definitions in the supplying file, over `Zsqrtd 2`. |
| Domain and index coverage | Both coordinates range over the entire order, and the support conclusion quantifies over every prime ideal containing the common ideal. No family or index restriction is introduced. |
| Transition and comparison maps | Private ring maps to `ZMod 2` and `ZMod 7` send `root` to `0` and `3`, respectively. Their kernel equalities and surjectivity are proved in `root_maximal` and `delta_maximal`; no number-field comparison map is asserted. |
| Consumed-object identity | Membership of the actual numerator and denominator in their span is used in `primitive_duplication_local`. `Ideal.span_singleton_pow` converts containment to divisibility by the same `root^7` and `delta^5`. |
| Coefficients and normalization | All coefficients are integral, in the basis `1, root` of the explicit order. No valuation or height normalization is used; translating to the manuscript's conventions remains open. |
| Local conditions | `dyadic_numerator` excludes divisibility by `root^7`; `delta_numerator` excludes `delta^5`, using the checked finite fact that a sum of two squares vanishes in `ZMod 7` only when both vanish. `prime_support` and maximality exclude all other prime ideals. |
| Exceptional cases | The proof makes no division by a coordinate or form. Zero coordinates and zero denominator are included whenever the primitive hypothesis holds; the nonprimitive pair `(0,0)` is not an input. |
| Downstream consumption | The separate generic importer below consumes the whole exact endpoint. There is no current Lean height consumer. The manuscript's `log 392` step needs the additional bridges stated above. |

## Reproduction and coverage

Lean is pinned to `leanprover/lean4:v4.35.0`. Run the following from the
**repository root**, using its native `z_in_q_kernel` Lake package, with `lake`
and `lean` available through `elan`. If the pinned dependencies and their
published compiled caches are not yet available, first run `lake exe cache get`
there. With those dependencies available:

```sh
lake build +ZInQKernel.Contrib.SqrtTwoDuplicationCancellation \
  +ZInQKernel.Contrib.SqrtTwoDuplicationCancellationAxioms
lake env lean -j1 -Ddebug.skipKernelTC=false \
  ZInQKernel/Contrib/SqrtTwoDuplicationCancellationAxioms.lean
duplication_output=$(mktemp -d "${TMPDIR:-/tmp}/duplication.XXXXXX")
```

The selected build prepares both current modules; it may reuse valid cached
artifacts. The second command freshly executes the actual axiom consumer with
kernel checking enabled. Lake supplies the project and dependency import paths;
no manual `LEAN_PATH` is needed. The accepted 48-module snapshot under `lean/`
is a separate package: its check alone does not validate this contribution.

Check ordinary exported use by saving the following as
`"$duplication_output/Import.lean"` in the same shell:

```lean
module
import ZInQKernel.Contrib.SqrtTwoDuplicationCancellation
open ZInQ.ModelDuplicationCancellation
example (a b : Zsqrtd 2) (hab : Ideal.span {a, b} = ⊤) :
    ¬ commonIdeal a b ≤ (Ideal.span {root}) ^ 7 ∧
    ¬ commonIdeal a b ≤ (Ideal.span {delta}) ^ 5 ∧
    ∀ q : Ideal (Zsqrtd 2), q.IsPrime → commonIdeal a b ≤ q →
      q = Ideal.span {root} ∨ q = Ideal.span {delta} :=
  primitive_duplication_local a b hab
```

Then, still from the repository root, run:

```sh
lake env lean -j1 -Ddebug.skipKernelTC=false "$duplication_output/Import.lean"
```

The supplying source is
[`ZInQKernel/Contrib/SqrtTwoDuplicationCancellation.lean`](../../ZInQKernel/Contrib/SqrtTwoDuplicationCancellation.lean),
and the actual consumer is
[`ZInQKernel/Contrib/SqrtTwoDuplicationCancellationAxioms.lean`](../../ZInQKernel/Contrib/SqrtTwoDuplicationCancellationAxioms.lean).
The source's SHA-256 is
`72a7273597722a492ab3c6fdb0c8e15f99a0c32117749548e87dc407b123fbad`;
the current audit file's is
`a39924bba3d0ad14d9e9ae02b2abd53cb9d025e03d780659ab3b56d9a4becb28`.
The endpoint's reported axioms are exactly `propext`, `Classical.choice`,
`Quot.sound`; the audit rejects any others. The source header's former `Checks/`
placement and license basename record the original port layout. The current
audit is linked above and the retained license is linked below.

Historically, the original port, its ordinary importer and its separate axiom
audit compiled with exit 0 on November 9, 2026, using fresh project output and
a private pinned dependency cache. The then-current audit SHA-256 was
`febdf4f94007977d03a2ac4dd99817d3386d4d9d9eed7834ff4616e54b219d5b`.
That validation also recorded the unchanged 48-module source check and
`python -B scripts/check_audit_history.py --self-test` passing (7 historical
and 19 application negative controls). Those dated results describe the former
layout, not a fresh execution of the current commands. The commands above use
the current root-package interface and published dependency caches; they do
not independently rebuild Lean or Mathlib or prove an arithmetic theorem beyond
the stated endpoint.
The unchanged proof emits tactic-style and `push_neg` deprecation warnings.

This is non-release contribution preparation. Manuscript/PDF synchronization,
construction replays, cumulative release handoff, release manifests and mirror
publication do not apply: none of those artifacts or claims changes. The frozen
snapshot and its root, manifest, checkers, pins and CI configuration are intact.
The contribution remains outside the frozen snapshot, under `ZInQKernel/Contrib`.
Non-author mathematical review, findings/inventory assessment and exact-final-
revision protocol closure remain pending with the caller. No PR, push, merge,
upstream acceptance or completed research-release review is claimed.

## License boundary

The port retains Copyright 2026 The Omega Institute and Apache-2.0 terms, with
modified-file attribution. A copy of the outgoing license accompanies it in
[SqrtTwoDuplicationCancellation.LICENSE](SqrtTwoDuplicationCancellation.LICENSE).
The new contribution documentation and audit are supplied on the same terms.
The cited upstream manuscript and other repository material retain their own
terms; no blanket upstream license or right to relicense them is inferred. No
manuscript proof text or upstream implementation is transplanted by this port.
