# Verified H102 curve-support source port

**All six owned FLT source edges compile on fixed Lean 4.35.0. Every original
`solution` export has exactly `[propext, Classical.choice, Quot.sound]` as its
axioms. This is supporting source verification, not an H102 discharge.**

## Provenance and ownership

Upstream: `anthropics/fermats-last-theorem`, immutable revision
`6e837e75355538c7f80bab5b956861e86c4eacc2` (Lean 4.33.1).
Initial base: `0e70c94e4a2d26838f0766cd69b39bd02f48fb85`; restored base:
`2dc949d688c407e32823c4e751679d66b2f40e65`; final review base:
`e22df37cdef936f5b0f29ec09501854bea6c7316`.
The Lean/Mathlib pins and H102's `TailQ.lean` statement are unchanged across these
bases. Changes are new files only: the assigned five edges, the parent-transferred
`tateChainRule`, their factoring helpers, notices, and verification evidence.
No other author's module, target, pin, configuration, claim, or final bridge is
changed by this lane.

The canonical original paths remain six import-only facades under
`ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol`.
All original `P2MW.S_AlgebraicCurve_<source>.solution` names, explicit signatures,
and universe generality are preserved. `SOURCE_AUDIT.json` records exact
byte-comparison of each original signature through `:=`.

## Factoring and compatibility

Twenty-three proof parts retain complete original declarations and contiguous
source-line ranges; the largest is 136,967 bytes. One small proved linear-algebra
helper makes inverse-conjugation cancellation explicit. There are thirty Lean
files in total including the six facades.

Compatibility edits are documented per source in `CURVE_SOURCE_MANIFEST.json`:
ordinary absolute namespace/open/export commands replace P2M scope metadata;
local notation is expanded; promoted private helpers have transparent private
root bridges at import boundaries; attribute-prefixed private data is handled;
confirmed absent optional export members are omitted; tensor induction,
definition/equality targets, original implicit scope closure, and 1-based TFAE
indices are made explicit where Lean 4.35 requires it. No result is supplied as an
assumption, no statement is weakened, and no new mathematical axiom or runtime
elaborator is introduced.

The RR edge's original `hRTK : ResidueTheoremK K F` argument remains unchanged.
The separate newly compiled global residue edge supplies that genuine theorem.
The Tate finiteness inputs also remain their original inputs, with the RR55
owner's matching finiteness prerequisite compiled separately.

## Native checks actually run

On the parent-granted dedicated host, every Lean process used a private lane
lock, `lean -j 4 -M 16000`, and a 20 GiB address-space cap; at most two processes
were run with the parent-approved 40 GiB aggregate budget. The main cache was a
private reflink copy; parent/other-author prerequisites were copied read-only.
The exact RR55 source/cache update was SHA-validated at
`a8726b2de09c54a71cc36e9b44002578fd94c391` and is not in this change set.

All 23 parts, six facades, and the auxiliary helper have successful stock Lean
compiler logs. Maximum observed compiler RSS was 10,853,532 KiB.
`Compile/verified/CurveProofCheck.log` contains all six full `#check` statements
and all six complete `#print axioms` outputs. Each is exactly AX3. Per-module raw
compiler logs are also retained. Earlier failed/cancelled attempts are labelled
historical, never presented as successful evidence.

The source audit checks original SHA provenance, contiguous source partitions,
all six unchanged solution signatures, the 150 KB Lean-file limit, all thirty
successful compiler logs, and absence of prohibited Lean forms after parsing
nested comments/strings. There is no `sorry`, new `axiom`, `native_decide`,
`#eval`, `run_cmd`, `initialize`, new syntax/notation/macro/elaborator, or import
of `OneProof.Main` in the owned Lean contribution.

## What this does not establish

The exact final geometric bridges, H102 `#discharges`, independent review, PR,
and integration are the primary author's responsibility. None is claimed here.
Full source, matching compiled objects, hashes, notices, and raw logs are provided
as a read-only broker payload and a private artifact for those downstream checks.
