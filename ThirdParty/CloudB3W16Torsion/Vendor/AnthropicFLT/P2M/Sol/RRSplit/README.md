# H102 curve support — verified FLT source port

The six source edges at frozen proof snapshot
`42a9645da2ffe4390cfbc6053aeb3836a9d59515` compile on Lean 4.35.0. Their original
`P2MW.S_AlgebraicCurve_<source>.solution` signatures and universe parameters are
preserved. Each solution uses exactly
`[propext, Classical.choice, Quot.sound]`.
**This source-support verification is not an H102 discharge.**

The five assigned giants plus `tateChainRule` are factored into 23 proof parts
and six original-path import facades. One additional proved linear-conjugation
helper makes cancellation explicit. All 30 Lean files are at most 136,967 bytes.
No proof file, dependency pin, target definition, or upstream notice is changed
by the separate public-evidence documentation update.

* `VERIFICATION.md`: provenance, compatibility edits, recorded checks, and limits.
* `CURVE_SOURCE_MANIFEST.json`: original source hashes, source-line ranges, helper
  mappings, unchanged proof-file hashes, and recorded verification.
* `SOURCE_AUDIT.json`: recorded source audit and unchanged original signatures.
* `Compile/PUBLIC_TYPE_AXIOM_EXCERPTS.md`: clearly labeled, verbatim selections
  of the original type and axiom output; not a raw compiler transcript.
* `REPRODUCING.md`: generic local reproduction commands, not the original command
  transcript.
* `Compile/ATTEMPTS.md` and `PREFLIGHT.md`: historical summaries.

Original FLT revision: `6e837e75355538c7f80bab5b956861e86c4eacc2` (Lean 4.33.1).
Full upstream Apache-2.0 LICENSE, NOTICE, and attribution accompany this directory.
The proof review base is `e22df37cdef936f5b0f29ec09501854bea6c7316`.

Complete successful, failed, and cancelled raw output remains preserved unchanged
in private archival storage. It is deliberately not distributed in this public
source tree. Public excerpts are selections, not edited output presented as raw.
The RR theorem's original residue-theorem input is retained; the separately
proved global residue theorem supplies it. Final geometric bridges, H102
`#discharges`, independent review, and integration are separate work.
