# Y3 tangent-trace prerequisite: verification and limits

**Partial helper draft only.** This contribution does not prove or discharge
`LeafQM.AV.R1UnivRigid.R1fpAb` in `ZInQKernel/OneProof/H/TailZ16.lean`.
The continuing goal is that exact shared witness; it is not replaced by this lemma.
Claim: https://github.com/Deicyde/diophantine-z-q/issues/14#issuecomment-6917934144 .

## Export and actual remaining inputs

The main export is
`ZInQ.Contrib.OneProof.Y3FineModuli.literal_order_charZero_tangent_trace`.
Its full type is in `CharZeroTrace.lean`, lines 31–58.
It concerns the **literal `LeafQM.O`** acting on an actual scheme of smooth
relative dimension 2 over an affine base, with the source-style
`RelativeGroupLaw` and an exhaustive compatible model of its dual-number
identity tangent points. It retains all scheme-action homomorphism/one/mul/add
clauses, `Field k`, `IsAlgClosed k`, `CharZero k`, finite `V`, injective/exhaustive
`τ`, addition/scalar compatibility, actual intertwining with `Φ`, and an integer
reduced-trace equality. The tangent dimension and operator ring homomorphism
are conclusions of the proof, not additional inputs.

This is **not yet a projection from the target `QMAbScheme`**. Its
`GrpObj`-to-`RelativeGroupLaw` bridge remains unsupplied. Also unsupplied:
full geometric 81-torsion, level-3 generation/annihilator and all-test-scheme
transport, the proper smooth relative-dimension-one moduli curve, its `Qbar`
point, natural `PtEquiv` over every characteristic-zero field, the global
universal `QMAbScheme` family and classification/gluing on proper curves.

## Source and checked revision

- Public source: `anthropics/fermats-last-theorem` at
  `6e837e75355538c7f80bab5b956861e86c4eacc2`; see `SOURCE_MAP.md` and `NOTICE.md`.
- Frozen comparison target: `0e70c94e4a2d26838f0766cd69b39bd02f48fb85`.
- Full 13-module source-check base: `2880fef1e827a05ab9238cd200e555c585f00e30`.
- Publication-base refresh: `0caafe66103a89994198e26d8d68af6ae227ed0e`.
  The intervening commit changes only `STATUS.md`; all six imported project
  sources, target definition, rules and dependency pins are unchanged.
- `TailZ16.lean` remains byte-identical to the frozen comparison, Git blob
  `0dbec9de824d8428c81eccdd821b6f7b79073865`.
- Lean 4.35.0; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
  No Lake dependency or pin was changed.

## Results actually obtained

All **13 actual project modules** (six existing definitions and seven new
modules) compiled from source into a fresh output directory using ordinary
Lean, two threads and a 12,000-MB per-process limit. The search path excluded
all earlier project outputs and the project's normal build directory.

Full literal order/geometry/dimension contracts and all five tangent-definition
guards pass. Nine axiom lists for the principal exports are exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The initial combined reference contract failed because its *test* dimension
type inserted `IsAlgClosed` and `Module.Finite` binders absent from the original
dimension theorem. Reference2 removes those two spurious test binders. No proof
bytes changed; the original failed source/output is retained. The final three
scratch checks were repeated with explicit compiler, search-path and source-hash
receipts. Existing lint warnings are retained, not suppressed or called errors.

**`#discharges`: NOT RUN. No open-field discharge is claimed.** This bounded
helper cone does not import `OneProof.Main`; the draft is not a merge-ready
open-statement proof and does not infer a discharge from default CI.

Standard-library inputs are previously retained public Mathlib cache archives
matched against source-derived keys, all 9,031 per-file hashes/sizes/comments
and the dependency pins. That is ordinary hash-checked public input, **not**
a signed-origin certificate, a full standard-library source rebuild, private
project-prefix adoption, or an independent kernel replay.

## Portable command templates

The following are **redacted portable templates, not literal execution receipts**.
`$ROOT`, `$OUT`, `$LEAN`, `$PINNED_PUBLIC_LIBRARY_PATHS` and `$CHECK` stand for
locally chosen paths; the literal commands and raw hash/environment receipts
are retained separately and are not copied into public metadata.

```sh
export LEAN_PATH="$OUT:$PINNED_PUBLIC_LIBRARY_PATHS"
"$LEAN" --threads=2 -M 12000 -R "$ROOT" \
  -o "$OUT/$MODULE.olean" -i "$OUT/$MODULE.ilean" "$ROOT/$MODULE.lean"
"$LEAN" --threads=2 -M 12000 -R "$CHECK_ROOT" "$CHECK"
```

The module list is the entry's explicit project import graph, in dependency
order; these commands do not substitute a different source world.

## AI and review

AI assistance performed source porting, proof construction and compiler/type/
axiom checks. The producer's serving-model identity is not independently
attested; no model identity is inferred from a requested configuration.
A non-author AI source review read all seven complete proof sources and original
bodies, the literal contracts and all producer receipts, and independently
hashed the source packets. A supplement checked the notice/evidence repairs.
The operator's final source/receipt gate also passed. These are source reviews
plus the reported compiler results, **not human-reading evidence or independent
kernel replay**. The prerequisite grade is PASS only within the stated scope.
