# Reviewed EndTrace / rational C10 — separate draft source proposal

**This is source publication, not a merged result, a current-head CI pass, a cache
release or an official manuscript record.** The active Axiom bridge PR #53 is
unchanged by this separate branch. No new PR or automatic merge is enabled here.

The branch preserves the published bridge history and the reviewed private
EndTrace preparation, then incorporates current accepted main
`fb2f78e143af2f6de71ca43e37498c229cde1c6b` by a normal merge. Existing default-root
sources, compiler/dependency pins, protected statement/checker contracts,
manuscript, released cache-v1/v2 metadata and required workflows are not rewritten.
The new proof files retain their reviewed bytes; comments marking them uncompiled
or private describe the authorship cutoff and are not silently edited into a
new proof or package-validation claim.

## Exact source and optional layout

- `NativeEndTrace.lean` retains SHA256
  `2a3518cab2d90718d622b723aac6154cc443f37c2b5e7e78ed397f4e6d951a76`.
  It remains a standalone root of the non-default `TateConsumers` library.
- `RationalC10Link.lean` retains SHA256
  `bd26ef697fcd5cd5f5b6db1d6dafd74b1f5c73866372861d1e04b4d69f0bc736`.
  `RationalC10Consumers` is a new non-default source-proposal library.
- `original-c10/ZInQKernel/HDecomp/C10/Link.lean` retains the original module
  `ZInQKernel.HDecomp.C10.Link` and exact SHA256
  `0c72f9e57e7557aa61dd7c1fc847111f639d7b86105b9939aabb46e1e7e81b55`.
  Its source is from [the original e303 Link](https://github.com/elliotglazer/diophantine-z-q/blob/e303a42543e9adf89aa70075372b622f4870a770/ZInQKernel/HDecomp/C10/Link.lean).
  It is owned by the opt-in `OriginalC10Link` library, not added under the
  repository-root source tree. Canonical Objects is retained, not replaced by
  the differing fork Objects/QM/I3Leaves snapshot or the whole PR62 tree.
- Positive cases and independent specifications are under `validation/endtrace`
  and `validation/rational-c10`. Their libraries are non-default. Full checkers
  and expected-failure controls are separate source files, not build roots.
  `validation/history` contains rejected/unrun fixtures and is never a provider.

`REVIEWED-SOURCES.json` binds the exact source bytes and distinguishes executed
validation from the newly proposed package layout. The original bridge default
remains `AxiomBridge`; repository-root default remains `ZInQKernel` with no newly
introduced Mordell/Stacks dependency. Later Frobenius/native-point/trace-pairing
work in other lanes is not included.

## What the mathematical source delivers

EndTrace supplies one **monic rational** characteristic polynomial and a common
rational trace for the same original abelian variety and endomorphism, under the
original allowed-prime guards and actual scalar-extension maps. It does not
prove the original all-field **integer** `PkgI3.CharPolyIndepOfEll` predicate.

Rational C10 proves the exact original conditional `c10_of_trace_link` and
`c10_of_squares` equivalence conclusions with **only the unused integer-polynomial
premise hM removed**. Original fields, basis/index universes, scalar/cochain and
matrix-unit data, C9/Eichler–Shimura trace families, coefficient maps, both
continuity inputs, both semisimplicity inputs, the shared A/A_sigma/mu/reductions/
F/mu-bar and nonzero N at three and five, and all original squares remain required.
It supplies none of those remaining arithmetic objects by assuming a desired
trace Fact or replacing them with equal-rank model spaces. Removing hM is not a
proof of hM, unconditional C10, H, the height bound or Hilbert10.

## Recorded focused checks — attributed, not public CI

The producing private lane compiled the original Link against canonical Objects,
then exact RationalC10Link and the independent specification. Its fresh
trust-level-zero checker passed five full expected-type/actual-body/stored-readback
comparisons, ten candidate/specification standard-three safety walks and three
comparisons to the original complete ordered types minus only the named typed
unused hM binder. Positive cases passed. The zero-N and characteristic controls
each had exactly the intended decide-false guard error, not an unrelated type,
parser/import error or an accepted forbidden-parameter theorem. The first zero-N
mixed literal/Nat-cast rejection is preserved; only its fixture denominator was
corrected, with proof/spec/checker sources unchanged.

A non-author internal source-and-captured-evidence review reconciled those exact
conditional types, applications and records. It was not another reviewer Lean
run, complete serialized-proof inspection, raw replay of all external libraries,
or designated Protocol B/Astra acceptance. The same distinction applies to the
separate reviewed EndTrace source/canonical/private-cache experiment.

The earlier private EndTrace preparation at commit
`721a345a7b4cd35fcdb34ed30454eb8a8c49878b` recorded a real canonical four-library
build, seven dedicated full type/body checks, original-nine/expanded-sixteen
lightweight reports, a clean dependency-cache restore, 23 local cold consumers
with zero Stacks/Mordell recompilation, and warm no-build replay. These are
historical source-bound measurements on that private layout, not new tests of
this complete branch or the newly placed RationalC10 source.

## Explicitly pending before production adoption

1. **Actual destination/package validation:** this new optional layout has not
   been canonical-Lake built as a whole. Original module names are retained,
   but module ownership/import-search/private/global-instance context changed.
   Bind that actual context and repeat the relevant full-type/body/case checks
   before claiming as-built adoption. Historical Trace/ProjRep output reuse in
   private direct checks is not current-head CI.
2. **Production cache coverage/admission:** released v2 remains unchanged and
   does not certify the additional EndTrace CharPoly dependency closure or this
   new RationalC10 layout. The private future cache is not published or activated.
   No cache-v3 release or metadata/hash refresh is performed by this branch.
3. **Disk preflight:** the existing standalone restorer validates the positive
   metadata minimum but actually enforces only the unpacked tar-size budget.
   It does not itself enforce a 30 GiB admission threshold. The existing public
   v2 workflow's external preflight is a separate check, not a general helper
   or post-install capacity guarantee. A future change requires explicit tests.
4. **Phase-specific memory:** canonical and source-cold process-group RSS were
   sampled every five seconds, so their observed peaks are not true upper
   bounds or future runner-fit certificates. The recorded dedicated EndTrace
   validator maximum RSS of 26,240,364 KiB and rational checker 26,593,676 KiB
   need separate phase budgets; the lighter sampled cold build alone is not
   sufficient. Canonical FIFO enforces a source/hash allowlist; cold FIFO only
   gates compilers and records the source ledger.
5. **Current-head CI and designated review:** no new-head kernel/optional
   workflow/Protocol B pass is asserted for this fork branch. Publication does
   not update the frozen PR53 review head, authorize landing, or establish an
   official new manuscript record. Current ruleset/review/source-to-consumer
   gates and the existing single integration owner still govern adoption.

Use the exact existing [contributor policy](../../docs/lean-contributions.md) and
[audit-history protocol](../../docs/audit-history/PROTOCOL.md). Failed or unrun
fixtures are not providers. Preserve all old source/pin/failure/CI cutoffs rather
than changing checks or hypotheses to manufacture a pass.
