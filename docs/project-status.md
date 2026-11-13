# Project status

**Source summary: November 13, 2026.** Main interface inspected: `8799c581c8c327fca153ef31b8042f1dc053c62d`. Mirror source inspected: `83651ea9055114b7042d21aa867fc6cd56b3a827`. These are source cutoffs, checked through 19:50 UTC, not a new CI or acceptance judgment; later revisions may differ. Use [issue #37](https://github.com/elliotglazer/diophantine-z-q/issues/37) for live claims and [the work guide](contributing-work.md) before starting another PR.

## Three proof contexts—not one status

| Context | Result and boundary |
|---|---|
| **Manuscript, Version 17** | The [README](../README.md) and [research index](../research/version17/README.md) present a **214-variable quartic family** and its arithmetic argument. The defining threshold is ineffective; the coefficient calculation for N >= 53 does not certify a defining member. This is not the root Lean target. |
| **Root Lean kernel on main** | The original **292,890,231,905-variable** construction is conditional. [MainLiterature](../ZInQKernel/MainLiterature.lean) and [Contract](../ZInQKernel/Contract.lean) retain five explicit proposition arguments: **SixContactMin/H, TYZ Reading A, HeckeContinuation, FunctionalEquation5, GrossZagier**. They are arguments, not axioms; this is not a claim that all five lack proofs elsewhere. |
| **Development mirror and PRs** | The mirror `deicyde/kernel-formalization` contains later suppliers and reductions. At the stated source cutoff, [GaussFE/Headline](https://github.com/elliotglazer/diophantine-z-q/blob/83651ea9055114b7042d21aa867fc6cd56b3a827/ZInQKernel/Contrib/GaussFE/Headline.lean) derives the original target from **H, Reading A and Gross–Zagier**, using the continuation needed by that route and the exact FunctionalEquation5 provider. Source presence, checked proposals, protected acceptance and main integration remain separate. |

The mirror is a source for reuse, **not the base of a new main PR**. Read its exact supplier and current claim before re-proving an input that is merely unmerged. A separate checked discharge application is required to change the intended headline's inputs.

## Where contributions help

| Workstream | A useful completion test |
|---|---|
| **H objects/geometry** | Supply a current consumer with the actual QM surface, maps, Jacobian/modular object or compatible realization. Reuse [Axiom bridge #53](https://github.com/elliotglazer/diophantine-z-q/pull/53) and existing mirror geometry/dimension work. A generic nonzero variety is not the required surface or J1(N). |
| **Points/Tate data** | Construct the actual pullback point map and Tate/endomorphism naturality, then finite-space input for the **same A**. This work is coordinated; check #37. Original-dimension rank, reduction/Frobenius compatibility and semisimplicity are separate. |
| **C10 representations/traces** | Produce the actual representations, coefficient embeddings, bases, continuity, semisimplicity and compatible traces in [C10](../ZInQKernel/HDecomp/C10/C10.lean). Reuse [#50](https://github.com/elliotglazer/diophantine-z-q/pull/50), [#47](https://github.com/elliotglazer/diophantine-z-q/pull/47), and main's already proved `frobLift`. Scheme/reduction Frobenius comparison is a different task. |
| **Conductor/height assembly** | Apply existing bounds to the real field/prime/index and prove the height comparisons on the same objects. Reuse global T20/T21 [#58](https://github.com/elliotglazer/diophantine-z-q/pull/58)/[#56](https://github.com/elliotglazer/diophantine-z-q/pull/56), D1 [#59](https://github.com/elliotglazer/diophantine-z-q/pull/59), and [#61](https://github.com/elliotglazer/diophantine-z-q/pull/61). [JHeight](../ZInQKernel/Hypotheses/JHeight.lean) already proves JHeightBound → SixContactMin, not JHeightBound itself. |
| **Positive-rank inputs** | Work on the exact current TYZ or Gross–Zagier decomposition input listed in #37. Reuse mirror Gauss/Hecke/theta work; convergence on Re(s)>3/2 is not entire continuation. |

These are workstreams, **not unclaimed assignments**. The tracker may contain newer results, a refined statement or an active owner. H still needs its explicit construction/glue as well as literature leaves.

## PR dependencies and overlap

- **#51 + #42/#47 → #54:** target registration and thin algebraic bindings; #54's review staging base is not accepted main.
- **#55 → #58; #56 + #58 → #59:** local Hilbert foundations, global Hilbert/Serre suppliers and D1. D1 removes two literature inputs but retains fourteen residual binders; repeated dependency sources are not new independent milestones.
- **#48/#55/#56/#58/#59/#61:** related/shared ramification and transport foundations. Compare exact paths, bytes, namespaces and consumers before merging copies.
- **#46 source dependencies → #60:** T31 does not assume #46's local-KW conclusion. Avoid redeclaring its existing H.T31_holds name during later registered-module adoption.
- **#53/cache:** separate opt-in engineering and geometry interfaces; do not incidentally add Stacks/Mordell to default root dependencies.
- **#41/#44/#62:** evaluate target, tooling and statement/conditional-glue changes separately from proof-only suppliers.

Use the [PR listing](https://github.com/elliotglazer/diophantine-z-q/pulls) and #37 for the linked proposals. **Integration order:** settle baseline/shared-supplier identities; review chosen canonical proof revisions; integrate dependencies through one lane; reduce and recheck thin consumers on the resulting main. Preserve authors and history. This map authorizes no PR closure, retarget or merge.

## Progress and maintenance

For each task record **consumer → constructed input/supplier → residual hypotheses → source revision**, plus separate fields for:

- **Verification:** draft, scoped checked, or full candidate/public CI checked.
- **Review:** unreviewed, preliminary, or required protected acceptance at the exact revision.
- **Integration:** proposed or merged, and whether the actual consumer/headline has been discharged.

PR/module counts and copied dependencies are not the metric. Update this page when these facts change, retain dated/failed evidence, and keep #37 the single claim tracker. Detailed checks are in [Lean contributions](lean-contributions.md); acceptance is in [the review guide](research-review/README.md). This summary changes no theorem or policy.
