# Verified H102 curve-support source port

**The six frozen FLT source edges compile on Lean 4.35.0. Each original
`solution` export has exactly `[propext, Classical.choice, Quot.sound]` as its
axioms. This is supporting source verification, not an H102 discharge.**

## Provenance and immutable proof scope

Upstream: `anthropics/fermats-last-theorem`, revision
`6e837e75355538c7f80bab5b956861e86c4eacc2` (Lean 4.33.1).
Frozen verified proof snapshot: `42a9645da2ffe4390cfbc6053aeb3836a9d59515`.
Initial base: `0e70c94e4a2d26838f0766cd69b39bd02f48fb85`; restored base:
`2dc949d688c407e32823c4e751679d66b2f40e65`; proof review base:
`e22df37cdef936f5b0f29ec09501854bea6c7316`.
The Lean/Mathlib pins and H102's `TailQ.lean` statement are unchanged across these
bases. The separate public-evidence update changes documentation only and omits
raw logs from the public tree. It does not modify Lean files, APIs, proof/source
hash values, LICENSE, NOTICE, or attribution.

The canonical original paths remain six import-only facades under
`ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol`.
All original `P2MW.S_AlgebraicCurve_<source>.solution` names, explicit signatures,
and universe parameters are preserved. The original source audit compared each
signature byte-for-byte through `:=`.

## Factoring and compatibility

Twenty-three proof parts retain complete original declarations and contiguous
source-line ranges; the largest is 136,967 bytes. One small proved linear-algebra
helper makes inverse-conjugation cancellation explicit. There are 30 Lean files
including six facades.

Compatibility edits are documented in `CURVE_SOURCE_MANIFEST.json`: absolute
namespace/open/export commands replace scope metadata; local notation is
expanded; promoted private helpers have transparent root bridges at import
boundaries; attribute-prefixed private data is handled; confirmed absent optional
export members are omitted; tensor induction, definition/equality targets,
implicit scope closure, and 1-based TFAE indices are made explicit where needed.
No result is supplied as a new assumption, no statement is weakened, and no new
mathematical axiom or runtime elaborator is introduced.

The RR edge's original `hRTK : ResidueTheoremK K F` argument remains unchanged.
The separate global residue edge supplies that theorem. The Tate finiteness
inputs retain their original statements; their matching prerequisite was
compiled separately. The recorded prerequisite revision is
`a8726b2de09c54a71cc36e9b44002578fd94c391`.

## Recorded checks and public evidence policy

The original build used stock Lean 4.35.0 with four threads per process,
`-M 16000`, a 20 GiB per-process address-space bound, and at most two concurrent
processes within a 40 GiB aggregate budget. Each invocation was protected by a
build lock. Dependency caches and other contributors' prerequisites were
read-only inputs to the isolated verification environment.

All 23 parts, six facades, and the auxiliary helper have recorded successful
compiler checks. Maximum observed compiler RSS was 10,853,532 KiB. A combined
scratch check printed all six full types and complete axiom lists; each solution
uses exactly the three standard axioms.

`Compile/PUBLIC_TYPE_AXIOM_EXCERPTS.md` contains labeled, verbatim selections of
that original output. It is not a raw compiler transcript and contains no timing,
command, warning, or diagnostic lines. Complete raw successful, failed, and
cancelled output remains unchanged in private archival storage. This public tree
omits those raw logs rather than rewriting them and calling the result raw.
`REPRODUCING.md` provides generic local commands, explicitly not an original
command transcript.

The recorded source audit checked original SHA provenance, source partitions,
all six original signatures, the 150 KB file limit, 30 successful compiler logs,
and absence of prohibited Lean forms. There is no `sorry`, new `axiom`,
`native_decide`, `#eval`, `run_cmd`, `initialize`, new syntax/notation/macro/
elaborator, or import of `OneProof.Main` in the owned Lean contribution.

## Limitations

No final geometric bridge, H102 `#discharges` result, integration, or independent
review is established by this source-support package. Its original inputs remain
visible in the public type excerpts. Such downstream checks must be performed
on the integrated proof separately.
