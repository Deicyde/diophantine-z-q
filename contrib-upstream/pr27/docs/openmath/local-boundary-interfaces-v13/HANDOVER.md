# Open Math OS: bounded local-boundary PR

Scope: review this PR in **CheyLoveday/diophantine-z-q**, and run Lean **4.35.0**
with all bundled paranoid checkers on its four modules / 41 named proof roots.
This is the fork PR, not upstream foundation PR #15 or its frozen 39 targets.
Do not enlarge this task into global arithmetic research or a new theorem.

The owner authorized publication and integration into the fork after local
checks on 2026-11-10. The records under `research/local-boundary-interfaces/`
describe the earlier local-preparation stage and remain frozen. This handover
adds checking support; it changes no mathematical source or earlier acceptance.

## Checkout and scope

Use the immutable PR head commit supplied in the PR description and handover
message. Fetch it from `https://github.com/CheyLoveday/diophantine-z-q.git` and
check out that SHA detached in a fresh isolated Linux workspace. Record the PR
number, base, head and any later merge SHA separately. A merged fork PR is still
the exact diff to review; integration does not imply cloud or mathematical
acceptance. Do not silently follow a moving branch or substitute a merge SHA.

The reviewed core snapshot is `43664fd17014018461d6dfd64cf052c1e4afe298`, based on
V13 `9c0b3aba60d90fdcac82115f0582a6f52f1054f7`. Verify its four source blobs and
62-file core manifest, SHA-256
`ce59e6667e58c1858a0bb87830c35f4142dc1f69c805f2e4daaa169f130220e3`.
The final two core-review attestations are intentionally outside that manifest;
their bytes are bound by the core Git commit. The publication support has its
own `MANIFEST.sha256` beside this file. Preserve both.

Read `research/local-boundary-interfaces/README.md`, `APPLICATION.md`,
`TARGETS.json`, `ORIGIN.json`, `FINDINGS.md`, `VERIFICATION.md` and the separately
authored reviews. Check exactly four mathematical modules, 41 distinct proof
roots (including two homotopy-valued definitions), and 16 printed definitions.
The original mathematical source commit is
`33483f751e6dcd3f91fb303969838aca33ad0458`.

## Three review layers

1. **Meaning and application.** Independently compare every declared root and
   referenced definition with the specification, including quantified domains,
   implicit instances and possible vacuity. Check the original/conjugate
   coefficient distinction, the finite-stage `ell = -1` premise, opposite
   local-coordinate signs, closedness and trace hypotheses, and the supplied
   right homotopy inverse/common projection. Recheck the manuscript consumer
   map. Report precisely which arithmetic realizations remain inputs.
2. **Formal artifacts.** Freshly compile the four modules, audit every root's
   transitive axioms, retain a source-bound scoped export, and run native Lean
   plus all five bundled additional checkers. The allowed axioms are only
   `propext`, `Quot.sound`, `Classical.choice`.
3. **Independent diagnostics and provenance.** Read and rerun the finite
   controls and existing protocol self-test; verify their recorded negative
   witnesses and before/after input hashes. These tests do not prove arithmetic
   instances. Compare substantive JSON fields exactly; disclose platform or
   Python-version metadata differences instead of changing expected results.

These layers are not three independent proofs or a numerical confidence score.
Keep kernel acceptance, statement meaning and arithmetic occurrence distinct.

## Prepare and build the selected project

Do not run the repository's default Lean target and call that coverage of this
packet: it selects `ZInQ`, not these Research modules. From the checkout root:

```sh
python3 -B scripts/prepare_local_boundary_openmath.py --output lean/.checks/openmath-local-boundary
python3 -B research/local-boundary-interfaces/check_controls.py
python3 -B scripts/check_audit_history.py --self-test
cd lean/.checks/openmath-local-boundary
lean --version
lake --version
lake build
```

The preparation is offline, refuses an existing output directory, copies only
the four mathematical files and pins, and supplies a `Packet.lean` import file
with no new theorem. Its Lake library explicitly lists all four modules and
Packet. The only lockfile transformation is the root package name. It retains
all nine dependency revisions, including Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Toolchain commit:
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

Obtain Linux-compatible dependency caches for those exact revisions using Open
Math's normal procedure, or rebuild them. Record cache origin and hashes; do
not reuse macOS binaries. Check the original lockfile remains unchanged and do
not upgrade dependencies. Kernel checking must remain enabled. The generated
manifest hashes source inputs, not dependency caches or produced binaries.

Also run the existing `verify_native.py` from the checkout root with a new
output directory, after making the exact pinned dependency caches available
under that checkout's `lean/.lake/packages`. Retain its complete statement and
axiom output. Verify every root is present and no forbidden axiom occurs.

## Retain the exact export and run paranoid checking

In the generated project, after a successful `lake build`, run the following
Python to preserve the exporter command, output, stderr and exit code. Execute
the build/export in the isolated Open Math environment; record its actual
isolation. This is not a protected comparator challenge.

```python
from pathlib import Path
import hashlib, json, subprocess

roots = Path("roots.txt").read_text().splitlines()
if len(roots) != 41 or len(set(roots)) != 41:
    raise SystemExit("Expected exactly 41 distinct proof roots")
if roots != json.loads(Path("TARGETS.json").read_text())["proof_roots"]:
    raise SystemExit("Proof-root list differs from the frozen selection")
evidence = Path("openmath-evidence")
evidence.mkdir(exist_ok=False)
argv = ["lake", "env", "leanexport", "Packet", "--", *roots]
with (evidence / "packet.ndjson").open("wb") as out, \
     (evidence / "export.stderr.txt").open("wb") as err:
    result = subprocess.run(argv, stdout=out, stderr=err)
receipt = {
    "command": argv, "exit_code": result.returncode,
    "export_sha256": hashlib.sha256((evidence / "packet.ndjson").read_bytes()).hexdigest(),
    "roots": roots,
}
(evidence / "export.json").write_text(json.dumps(receipt, indent=2) + "\n")
if result.returncode:
    raise SystemExit("Export failed; preserve the failure and stop")
```

Then run and capture stdout, stderr and the actual process exit status:

```sh
lake check --from-export openmath-evidence/packet.ndjson --paranoid
```

This supported Lean 4.35 command replays the **named roots and their transitive
proof closure** from the retained export. It does not independently prove that
an arbitrary supplied export came from the checkout. Establish that link using
the recorded fresh build, exact exporter invocation, source/generated manifests,
module artifacts, target list and before/after hashes. Do not describe it as a
protected challenge comparison, or claim that `--from-export` itself rebuilt
the sources. Do not run a self-comparison and call it independent statement
validation. Source-to-statement review is layer1 above.

The requested checker set is Lean default, Lean paranoid, lean4lean, nanoda,
con-leche and con-ron. Require each actual acceptance and the overall exit code
0; missing/unavailable/skipped is not passed. Record exact tool versions and
executable hashes. Do not disable a checker, kernel checking or sandboxing to
turn failure into success. Record Linux/bubblewrap and the isolation actually
used; no blanket sandbox claim follows from the presence of `--paranoid`.

The flags and export argument order were checked against installed Lean 4.35
help/source and the [official release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/#checking-projects-with-lake-check-and-lake-comparator)
on 2026-11-10. The pinned Lake source uses `leanexport MODULE -- ROOTS...` and
documents `lake check --from-export FILE --paranoid`. Consult the installed
version if anything differs; preserve the discrepancy instead of improvising
a stronger assurance claim.

## Deliver evidence, not a rewritten proof

Return an evidence-only branch/PR in **CheyLoveday/diophantine-z-q** containing:

- Exact reviewed/executed checkout and PR/merge identities, all input manifests
  and dependency pins, generated-project manifest, all 41 names and axiom sets.
- Complete commands, stdout/stderr, real exit codes, actual per-checker outcomes
  and executable hashes; versions/platform/cache/isolation provenance.
- The retained `packet.ndjson` and SHA-256 (or an immutable downloadable artifact
  with its hash if too large), plus the compiled module artifact hashes. Record
  unavailable artifacts accurately; do not claim retention of deleted streams.
- Independent statement/application review, finite/control results, differences
  and findings with exact scope. Keep initial failed attempts and their repairs.
- A short verification guide mapping every claimed result to evidence and an
  honest summary of any unchecked or rejected item.

Do not modify the four proofs, frozen39 packet, old receipts, manuscript or
research bank in the evidence delivery. If a proof defect appears, retain a
minimal witness and report it before proposing a separately reviewed repair.
Do not merge your evidence PR automatically. A successful cloud run supports
these conditional interfaces; it does not establish global cup/trace
realization, every inverse, stored-functional identification, determinant
normalization, retained-limit descent or the main Diophantine theorem.
