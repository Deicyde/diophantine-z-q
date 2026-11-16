# Tian–Yuan–Zhang Theorem 2.1 at (3, 1)

This contribution reuses the complete proof of `ZInQ.Contrib.TYZDecomp.H29Split.TYZThm21At31` from the existing project source at revision `f597c34cd6f6a43e076138209c638c47978753f5`.

The entry point is `ZInQ.Contrib.OneProof.TYZAtThree.hT21_proof` in `ZInQKernel/Contrib/OneProof/TYZThm21At31.lean`. Fifteen supporting proof modules are included in this directory, with their original mathematics and provenance retained. Existing modules, target definitions and dependency pins are not changed.

Verified on Lean 4.35.0 and unchanged Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`:

- All fifteen helpers and the entry passed serialized named source compilation. The final attribution-comment clarification was rebuilt before repeating the checks.
- Closed named and fully expanded original-type assignments compile. The entry and its four principal suppliers report exactly `[propext, Classical.choice, Quot.sound]`.
- The prescribed three-import `#discharges` check reports `DISCHARGES [hT21] by ZInQ.Contrib.OneProof.TYZAtThree.hT21_proof`, `still assumes: []`, with those same three axioms. Full output is in the pull request.
- Source scans reject proof holes, new axioms, native proof bypasses, build-time code and a contribution import of Main.

The integrator's hfx work can consume these canonical `CloudB3SC7T21` modules, which keep the original `ZInQ.Contrib.T21Proof` declaration names, instead of including a second copy of the historical T21 modules.

Independent source, mathematics and recorded-evidence review is reported separately in the pull request. The claim-only version remains in Git history. This supplies hT21 only; no unconditional Hilbert's tenth problem result, human review or independent imported-library raw replay is claimed.

AI-assisted contribution operated by Jack McCarthy. Private evidence bundle available to the maintainer.
