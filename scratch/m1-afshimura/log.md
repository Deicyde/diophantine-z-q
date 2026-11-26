# AfShimura proof log

- Verified the branch base at `29bfbc3f6793d98b7c1ac637f9728fe51e701e5b` and the locally available quotient revision at `64f6912cfd365add865dc13c540f6191ecadee86`. The configured HTTPS proxy denied the fetch with HTTP 403. The direct retry could not resolve GitHub.
- Imported the six requested quotient modules in commit `2951ee765`.
- Restarted the first Lake build after seeding the local build directory with prebuilt artifacts from the same Lean toolchain and package manifest. Lake checks those artifacts against the pinned sources. The Lake invocations are serial, the compiler launches are serialized with a lock, and the systemd limit is `MemoryMax=60G`.
- Traced the direct import headers from `ZInQKernel/OneProof/Main.lean`. The four bundle assignment modules are in the import closure. The H proof enters the NOS copy at `ZInQKernel/OneProof/H/TailZ91.lean:106`.
- All six quotient modules built with their original sources. The source
  scan had no matches, and the three quotient theorems passed the axiom
  audit. See `builds.txt` and `axioms-quotient.txt`.
- Checked the quotient and finite-dimensionality proofs, then checked the
  complete action and theorem with Lean. The full `AfShimuraProof` module
  build passed. The 46 theorem entries in `axioms.txt` each use only
  `propext`, `Classical.choice` and `Quot.sound`.
- Ran `lake build ZInQKernel.Contrib.OneProof.NOSNarrowChain` successfully
  (15778 jobs). Then `lake env lean -j1 scratch/m1-afshimura/FoldCheck.lean`
  exited successfully with no diagnostics.
