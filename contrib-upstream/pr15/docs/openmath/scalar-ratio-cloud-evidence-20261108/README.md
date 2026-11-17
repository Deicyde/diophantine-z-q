# Frozen 39-target comparator verification — PASS

## Delivery identity

- Repository: `https://github.com/CheyLoveday/diophantine-z-q.git`
- Requested branch: `codex/derivative-switch-boundary-v13`
- Detached checkout: `e653d6ff295ae4e0535710a7d64aa255d294d211`
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Lean prefix: `/opt/lean.4.35.0-56a005855ea1`
- Lake: Lake version 5.0.0-src+eb6cafb (Lean version 4.35.0)
- Bubblewrap: 0.11.1; independent execution probe exit 0
- Current research packet manifest: `d313ec3ff5ad0e91d555d26b2beef6ad401d7e9c86cdfe77adbe119062498610`
- Generated project manifest: `117f9ca2c28c42e45198f790dd8c3f324e1bed9d3af11ea9707575363304b811`

The preparation receipt identifies the reviewed scalar-ratio snapshot as
`3d2243ff141f9681fbd6a659ca28ffddfae9b000`. The actual execution checkout above is newer,
and that distinction is preserved rather than rewriting either identity.

## Outcomes

- Preparation checked 128 prior inputs and 99 current inputs.
- The generated manifest has 24 signed input entries; including
  `MANIFEST.sha256`, the source package has 25 files. The separately
  generated `OPENMATH_PREPARATION.json` receipt is not a signed input.
- Exactly 39 distinct theorem names were selected. `definition_names` is empty.
- Only propext, Quot.sound, and Classical.choice are allowed.
- All 39 intended challenge proof holes were seen exactly once.
- No selected solution proof emitted a sorry warning.
- The final comparator and post-comparator manifest checks both exited 0.
- The complete comparator stderr is supplied and is empty.
- The standard non-module and three unused-DecidableEq warnings were preserved
  exactly as emitted; no linter was changed or suppressed.

| Checker | Outcome |
| --- | --- |
| Lean default | PASS |
| Lean paranoid | PASS |
| lean4lean | PASS (checked 11492 declarations) |
| nanoda | PASS |
| con-leche | PASS (accepted 11495 declarations) |
| con-ron | PASS (accepted 11495 declarations) |

All nine dependency revisions match their locks and have clean tracked source.
`dependencies.json` records both expected and actual Git revisions. The
checker-executable paths and SHA-256 digests are in `checker-identities.json`.

The protected execution was performed with bubblewrap; no sandbox, checker,
dependency, timeout or resource restriction was removed or disabled.

## Retained artifacts

The bundled exporter processes a scoped temporary NDJSON file inside the
sandbox. Lean's documented `IO.FS.withTempFile` deletes that export after use,
so no standalone NDJSON proof export is retained or claimed here.

All 24 retained `.olean`, `.ilean`, and `.trace` compile artifacts for the seven
solution research modules and `Solution` are preserved under
`compiled-artifacts/`, with SHA-256 and byte size recorded in `RESULT.json`.
These compiled artifacts are not relabeled as the stream that the kernel checks
consumed.

## Scope

This verifies the frozen conditional algebraic packet, including all six
checkers. It does not prove arithmetic Selmer/Poitou–Tate boundary–cup
compatibility, the restricted converse, or the main Diophantine theorem. Those
remain unproved and are not marked as covered by this comparator result.
