# H102 compatibility lane C32 — verified source and exports

## Exact scope and snapshots

This lane owns only the 32 modules in `compat-ownership.json` key `lane_c`.
Their corresponding existing theorem wrappers and all other dependencies were
compiled read-only. The primary retains its 22 math/API modules, 7 definitions,
shared code, and the final H102 leaf. Other lanes and the completed group/flatness
helpers were not edited. No child agent was spawned.

Base: `3d010dcf38c274630c8dd1efb9cd247e3d81ed09`, including the primary's earlier
98 namespace/export repairs. This lane did not repeat those historical patches:
fresh compilation identified the next nested alias and API failures in current code.
Dedicated private checkout: `devvm68160`, `~/cloud-b3/w16/h102-core-c`.
GitHub writes only ran in the private `devvm19064` broker checkout, with
`push.default=nothing` and full explicit own-branch refspecs.

Source remains anthropics/fermats-last-theorem
`6e837e75355538c7f80bab5b956861e86c4eacc2`, Lean 4.35.0, and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Original source copyright/credits,
vendor LICENSE/NOTICE/ATTRIBUTION, import mapping, manifests, targets, and pins
remain unchanged. The 32 solution declaration telescopes were compared with
base source and remain textually unchanged; none of the 32 wrapper files was edited.

## Cache validation

Before copying any inherited olean, its source SHA256 was checked against the
current private checkout and its archive bytes/size/SHA256 against the supplied
manifest. All **334/334** matched; no stale artifact was copied. The manifest's
historical snapshot is `bf6da311a45c3cfed8969921c447427535dad7e1`, but matching was
against actual current source, not inferred from that snapshot label.

Cache archive SHA256:
`95a93f5b74456fcd7407777a533301e811a283a9aa4f4c1358d956cc32779d07`.
Private `validated-cache.json` records the per-module source/olean hashes.
Subsequent cache reuse was keyed by source and recursive dependency signatures;
inherited reuse required transitive matching of validated dependencies.

## Actual repairs

Only 21 of the 32 owned source files needed changes:

* Qualify existing root namespaces in nested `export` commands. The fresh errors
  were namespace self-exports after the primary's initial open-scope repairs.
* Keep private NoncritGeom, P2mIsogFin, QuotFLF, and IsoTransfer helper declarations
  in their module-local namespaces rather than exporting nonexistent root namespaces.
  Proof arguments and resulting solution types are unchanged.
* Remove redundant `rfl` commands only where the preceding rewrite/simplification
  now closes the goal in Lean 4.35.
* Use the current maximal-ideal contraction API, passing the actual ring hom,
  its existing integrality proof, and the maximal ideal explicitly. Its signature
  was confirmed with a real Mathlib `#check` before changing calls.
* Activate the source's existing L8 scoped local-hom instance where the source uses
  it outside namespace L8. No new instance or mathematical assumption was introduced.
* Normalize the existing transport identity after `pullbackComp_paste_app`.
  For `sqIso_hom_app`, use the already proved `τ_inv_app` formula and restricted
  iso-composition simplification instead of unfolding the entire pullback functor.
  The former broad simplification timed out even at 3.2 million heartbeats;
  the replacement proves the same original statement.

No new axiom, weakened hypothesis, target restatement, runtime code, syntax,
notation, macro, or elaborator was introduced. All owned Lean files remain below
150000 bytes (the original maximum was 112298 bytes).

## Kernel compilation and exact exported APIs

The dependency cone of all 32 owned solutions and their 32 existing wrappers is
**92 modules**, not the whole 1332-module H102 provider DAG. The final actual run
is **92/92 successful, 32/32 owned solutions successful, 32/32 wrappers successful,
zero failures, zero blocked modules, and zero other-owner failures**.

Commands were serialized through the private `lane-build.lock`, at most one Lean
process, `LEAN_NUM_THREADS=4`, `lean -M16000`, no virtual-memory limit. Host
available memory was checked before every invocation (at least 30 GiB). Maximum
latest compile-log RSS: **7586268 KiB**, below the 20 GiB process bound.

The direct compile command form was:

```sh
lake env lean -M16000 -o .lake/build/lib/lean/<module>.olean <module>.lean
```

Fresh `CheckC32.lean` imports all 32 wrappers, prints their exact public signatures,
and prints axioms of all 32 public exports and all 32 P2M solution proofs.
Actual exit **0**, **5.18 seconds**, peak RSS **7352776 KiB**. All **64** genuine
compiler axiom lists were parsed and checked and are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

`EXPORTED_APIS.txt` is the byte-exact compiler output, including all 32 complete
signatures and 64 axiom lists. It supplies the exact reusable APIs without a
restatement or extra assumption. SHA256:
`1a903dcd9064e07b3b88e07567c6920a7f3187a4242c1b0cf4145cead2d8550b`.

## Actual checkpoints, not historical diagnostic counts

* First current-code run: 11/32 owned successful, 21 owned failures. The supplied
  historical diagnostics were used only as locators, not as fresh results.
* Second run: 28/32 successful, 4 owned API/tactic failures.
* Third run: 31/32 successful, one broad-simplification heartbeat failure.
* Fourth run: 32/32 successful, all 32 wrappers and the whole 92-module cone green.
* Fresh all-export check: 64/64 exact AX3 lists, no extra hypothesis or axiom.

All failed attempts remain failed attempts. Their raw logs were retained under
private `c-logs-pass1`, `c-logs-pass2`, and `c-logs-pass3`, with corresponding
stage JSON files. The genuine first/second-pass archive was banked on `devvm19064`
with SHA256
`05b5cd8758af31f83e91ad3ba326acd90c0bee720e0f17cd0165abb402ee3a73`.
Source compiler linter/deprecation warnings remain visible and were not hidden.

Final raw evidence in the private checkout includes `c-stage.json`, `c-logs/`,
`c-all-axioms.log`, `CheckC32.lean`, and the validated cache ledger. The final
source bundle and complete raw evidence archive are also banked through the broker.

This result closes only the assigned C32 compatibility work. It does not claim
H102 or the full OneProof goal: the primary owns the degree/root/leaf work and
its `#discharges` check. No Main build, issue/comment/PR/upstream/main push, merge,
other-lane write, or edit to the frozen group/flatness helper families was made.
