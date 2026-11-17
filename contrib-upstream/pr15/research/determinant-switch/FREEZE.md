# Six-lemma packet freeze

**The scoped research packet is reviewed and frozen locally, pending the later
Open Math OS paranoid run.** This does not establish the arithmetic
class-functional determinant compatibility. No push, PR publication, merge or
Open Math OS dispatch is part of this freeze.

The scope is the six abstract lemmas in
[`Research.DerivativeSwitchBoundary`](../../lean/Research/DerivativeSwitchBoundary.lean),
their [contract](CONTRACT.md), exact finite-model controls, and the separate
[verification handoff](verification/README.md). The original six proof bodies
remain unchanged. Development assurance is **MET**; release/critical assurance
is not claimed. See the [gate report](VERIFICATION.md).

## Review decisions

| Finding | Resolution and evidence |
| --- | --- |
| M1: boundary kernel dimension does not alone imply cohomology dimension one | The contract now names `H¹(C_str)=0` and derives it from the source's old-class spanning and nonzero-localization assumptions. This clarification uses an existing V13 argument; it is not a new repair to the manuscript. |
| M2: quotient/Fitting comparison needs integral lattices | The contract explicitly uses free rank-two lattices `F_R,S_R`, their cyclic quotients, finitely generated torsion submodules, and integral determinant triangles. The field quotients are not used for this claim. |
| V1: inherited default Lake target excludes the six lemmas | A separate generated project defaults to the solution's named module. Its challenge library is separate and excluded from the default target. The inherited `lean/lakefile.toml` is unchanged. |
| V2: challenge statements and definitions require their own check | The separately written challenge lists all six signatures and three concrete definitions, imports no solution, and permits no definition replacements. A non-author model reviewer checked their meanings and exact coverage. |

The [initial review](evidence/freeze-20261108/math-review.md) and
[final rereview](evidence/freeze-20261108/final-review.md) were authored by
`/root/packet_math_review`, a separate Codex model agent. Reports are copied
without edits. The reviewer re-derived the elementary algebra and cofactor
normalization, checked boundary cases, read the owning V13 passages for M1/M2,
and reviewed the corrected contract and challenge. This is non-author model
review of the named packet; distinct model identities do not establish
uncorrelated reasoning. It is not human or whole-manuscript acceptance.

## Frozen inputs and observed checks

- Lean solution SHA-256:
  `63a9215fa55568069d2d1a7b2c3a7345ec21c7ad6a82203f42c5451ee4b8bbea`.
- Final contract SHA-256:
  `01be1c4182cd5c7483ad2253b93b975ddced22396372e726aa808614d525516b`.
- Generated handoff input manifest SHA-256:
  `e37368316a682d30f9358d7cf1c1ebd01e622e7896c99ca020ae5f94288f6188`.
- Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
  and all nine inherited dependency revisions are pinned. The repository's
  inherited baseline remains `9c0b3aba60d90fdcac82115f0582a6f52f1054f7`.

The [fresh native result](evidence/freeze-20261108/RESULT.json) records successful
compilation of the named module and audits of all six declarations,
with transitive axioms exactly `propext` and `Quot.sound` for every theorem.
The exact models, frozen 48-module source guard and
audit-history controls pass. No inherited helper rebuild is claimed.

The [handoff checks](evidence/freeze-20261108/LOCAL_HANDOFF_CHECK.json) record
the default solution build, separate challenge build, deterministic generation,
and a direct export-structure/axiom probe. The probe rejected missing targets,
altered statements, altered protected definitions and `sorryAx` proofs. It
uses the installed comparator routines without executing the protected Linux
command or any replay kernel. The probe's complete log and final exit status
are required; its intermediate PASS message alone is insufficient.

Local checks ran on macOS **without `--paranoid`**. Published dependency
caches were reused and remain trusted inputs. The default build produced
legacy-module import guidance; the separate challenge additionally produced
its six intentional specification-hole warnings. No placeholder appears in
the solution's transitive axiom set.

## Handoff and remaining gate

Generate a new standalone project from this frozen repository:

```sh
python3 -B research/determinant-switch/verification/prepare.py --output NEW_DIR
```

The generator copies an explicit source list, records source hashes, preserves
all dependency revisions, and changes only the lockfile's root package name.
It performs no build, network access or dispatch. Fresh generation has been
checked for byte-identical output. `SOURCES.json` labels the authority and
transformation of every generated input. Do not edit generated copies.

The later authorized Linux run is:

```sh
lake comparator --config comparator.json --paranoid
```

The [handoff instructions](verification/README.md) specify manifest checks,
dependencies, sandbox requirements, conventional axioms and individual outcomes
for `Lean default`, `Lean paranoid`, `lean4lean`, `nanoda`, `con-leche`, and
`con-ron`. Protected comparison, native export replay, all external checkers,
and clean Linux reproduction remain **NOT_RUN**. Open Math OS runtime and
resource setup have not been tested or authorized by this preparation.

Actual integral tensor compatibility, the Poitou–Tate boundary–cup adjunctions,
the arithmetic normalization, human acceptance and manuscript integration
remain outside this completed six-lemma scope. No conclusion about those
obligations follows from the local checks or the future paranoid suite.

The [current manifest](MANIFEST.sha256) binds this packet. The
[original ingestion records](history/ingest-20261108/README-history.md), received
ZIP and previous evidence remain preserved. The final local Git commit and
archive receipt are recorded in the workspace delivery record after freezing;
neither changes a remote branch or an upstream acceptance record.
