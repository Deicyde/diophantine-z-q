# Deicyde main-theorem index, 2026-11-13

This dated index binds the fork to inspected source revision
`8ec807114805afd96d90c468ec2cf40c6f9cc634`. It is an organization supplement,
not a new mathematical proof certificate or a replacement for historical
status records. The separate [frozen upstream roadmap](https://github.com/Deicyde/diophantine-z-q/blob/b9389e7b53b3976dfc32bccf346697831b79bd2c/docs/hilbert10-roadmap.md)
remains the full contribution guide. Its source revision and the fork's main
revision must not be treated as interchangeable.

## Finish line

The immediate formal goal is [`ZInQ.FrozenTarget`](https://github.com/Deicyde/diophantine-z-q/blob/8ec807114805afd96d90c468ec2cf40c6f9cc634/ZInQKernel/Target.lean#L17-L26):
one integer-coefficient polynomial in **292,890,231,905 variables**, with the
unchanged strict degree and coefficient bounds, defines exactly the embedded
integers using **292,890,231,904 rational witnesses** for every rational input.
The quantifier order is one polynomial followed by every rational input, not
a different polynomial for each input. A 214-variable quartic or another
manuscript snapshot is not silently substituted for this target.

The end-to-end Hilbert10 objective additionally needs the effective reduction
from integer Diophantine solvability to rational Diophantine solvability and
its checked undecidability consumer. This update does not establish that
consumer or assert that none exists outside the inspected scope.

## Existing consumer cut

These are dependency sketches, not replacements for the full source types:

```text
Canonical source form:
  SixContactMin + TYZThm35ReadingA + HeckeContinuation
    + FunctionalEquation5 + GrossZagier -> FrozenTarget

Available folded fork form:
  SixContactMin + TYZThm35ReadingA + GrossZagier -> FrozenTarget
```

The [canonical five-input theorem](https://github.com/Deicyde/diophantine-z-q/blob/8ec807114805afd96d90c468ec2cf40c6f9cc634/ZInQKernel/MainLiterature.lean#L53-L57)
is preserved. The [folded three-input theorem](https://github.com/Deicyde/diophantine-z-q/blob/8ec807114805afd96d90c468ec2cf40c6f9cc634/ZInQKernel/Contrib/GaussFE/Headline.lean#L18-L28)
uses the existing Gauss/analytic route. Neither theorem supplies its remaining
arguments. A standard-only axiom report for a conditional theorem does not
prove those arguments.

The remaining inputs of the folded source form are:

- **H:** [`SixContactMin`](https://github.com/Deicyde/diophantine-z-q/blob/8ec807114805afd96d90c468ec2cf40c6f9cc634/ZInQKernel/Hypotheses/HeightMin.lean#L44-L52),
  the effective, uniform height inequality for all rational `u` outside the
  contact set, at the original `Mult.S_mul` and `heightD`.
- **TYZ reading A:** [`Literature.TYZThm35ReadingA`](https://github.com/Deicyde/diophantine-z-q/blob/8ec807114805afd96d90c468ec2cf40c6f9cc634/ZInQKernel/Hypotheses/CR3Literature.lean#L137-L144),
  for squarefree `d` with `d % 8 = 5`, the stated continuation and analytic
  order at least two force **both** `T5aCl d` and `T5bCl d` to be zero.
- **Gross-Zagier:** [`Literature.GrossZagier`](https://github.com/Deicyde/diophantine-z-q/blob/8ec807114805afd96d90c468ec2cf40c6f9cc634/ZInQKernel/Hypotheses/CR3Literature.lean#L61-L72),
  the actual rational affine point of nonfinite additive order for the stated
  elliptic curve and continuation when the analytic order is exactly one.

Use the existing roadmap's H10-H, H10-TYZ, H10-GZ and H10-END contribution
cards. Input-package equivalence or a theorem from numerical output data is
not a constructor of the required literature or object-backed input. In
particular, [the H assembly source](https://github.com/Deicyde/diophantine-z-q/blob/8ec807114805afd96d90c468ec2cf40c6f9cc634/ZInQKernel/HDecomp/Assembly.lean#L493-L505)
explicitly warns that `GlueOutputs` is not a faithful object-backed statement
of the abelian-variety literature.

## Progress states that must stay separate

| State | Required evidence | What it does not establish |
| --- | --- | --- |
| Source-inspected | Exact revision, declaration type and definitions | Fresh kernel validation or a premise's truth |
| Proved supplier | Full intended type, proof and declared hypotheses | Actual downstream objects or consumer wiring |
| Conditional consumer | Proof from its explicit input package | Proof of that package |
| Actual wiring | Same objects, maps, primes and scalar data used downstream | Validation of an untested combined tree |
| Validated candidate | Exact combined source and unchanged applicable checks | Integration into a different main revision |
| Integrated | Provider and consumer on the intended main revision | Closure of remaining mathematical premises |
| End-to-end complete | Intended theorem and Hilbert10 consequence with premises discharged | Not earned by module counts or green helper CI |

Priority follows the unfilled headline inputs and their consumer joins. H,
TYZ and Gross-Zagier are the existing source obligations; the 13 November
Frobenius checkpoints are recent infrastructure. Under a recency-corrected
ordering, actual-input construction stays above another generic Frobenius
lemma.

## Frobenius-to-C10 bridge

The local Frobenius checkpoint through `eec823474ed6919117e2328b24e3e7f96c452d11`
contains 45 checked declarations across six implementation modules: relative
group-map packaging, prime-field specialization, finite-field q-power maps,
perfect-extension point action, same-field n-torsion restriction, and
geometric finite/surjective properties. These are scoped local supplier
checks, not an integrated proof of a main-theorem input or protected
acceptance. Their source availability and integration must be recorded
separately from their local verification.

The next relevant bridge is the **actual shared-model input** of
[`GlueC10Link.c10_of_squares`](https://github.com/Deicyde/diophantine-z-q/blob/8ec807114805afd96d90c468ec2cf40c6f9cc634/ZInQKernel/HDecomp/C10/Link.lean#L398-L455),
not a reproof of the existing square-to-comparison glue. For each relevant
`g,p`, its `hSq` uses the **same** `L,k,A,Aσ,mu,Ab,Ab',F,mub,N` with `N != 0`
for both coefficient primes **3 and 5**, together with the three genuine
transport/reduction squares. All other original coefficient, trace,
continuity, semisimplicity and arithmetic hypotheses must also be retained.

A same-field Frobenius automorphism or torsion bijection does not establish
reduction-map bijectivity, global `GQ` Frobenius identification or those
squares. Do not hide a desired square in a payload, choose an unrelated
zero group, or identify an arbitrary characteristic-p twist with its source.
The point/base-change, same-M Tate and Frobenius prerequisite lanes are
already allocated; coordinate their exact output-to-consumer types rather
than duplicating them.

## Integration queue

1. Reuse the [frozen source-preserving upstream ledger](https://github.com/Deicyde/diophantine-z-q/blob/b9389e7b53b3976dfc32bccf346697831b79bd2c/docs/issue37-consolidation/SOURCE-MAP.json)
   at its stated revision. Its source union is not a claim that the fork has
   integrated it or that the combined candidate passed its full gate.
2. Keep the eight-file optional Frobenius handoff frozen at `ac278bc3`.
   The later `fe98db36` torsion and `eec82347` geometry supplements remain
   separate; do not silently fold them into an in-flight checked snapshot.
3. For each new contribution, record one **exact input -> output -> next
   consumer** edge, its full type, existing owner, source/proof evidence and
   integration revision. Closing a source edge matters more than adding an
   unconsumed theorem.
4. After an actual main input is supplied, apply the native consumer and
   validate that coherent revision. Identify the final effective Hilbert10
   consumer before reporting end-to-end completion.

## Verification scope of this index

The source files were read and their Git blob identities checked. The
repository's `scripts/check_target.py` reports that `FrozenTarget` matches
`lean/Frozen/BoundedIntegerPolynomial.lean`. This documentation-only update
does not rerun the full main Lean build or certify every dependency body.
Current CI and acceptance states must be read at the candidate head; none
are inferred from an old review, another PR, or a helper's compilation.

The accompanying [machine-readable index](2026-11-13-deicyde-theorem-index.json)
records the source bindings and consumer cut. Historical README/status
prose, frozen statement, theorem sources, dependency pins and CI gates are
preserved. The work is not marked finished while the selected main inputs
and the intended end-to-end consequence remain unsupplied.
