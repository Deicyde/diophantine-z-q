# Appendix F: explicit ramification and level-one split profile

**Result.** For a prime \(\ell_0\equiv3\pmod4\), the algebra \((-1,-\ell_0)_{\mathbb Q}\) satisfies the exact `AppF.RamifiedExactlyAtEll0Infty` predicate. For every prime \(p\ne\ell_0\), including two, `explicit_split_profile` gives a local algebra equivalence taking the completion of `explicitOrderAt` onto `standardLevel p 0`. The matrix inverse only divides by \(-\ell_0\), a unit at those primes.

**Verification.** The four files under `ZInQKernel/Contrib/OneProof/RC/ExplicitSplit/` compile individually with `lake env lean`. All 15 theorem audits use only `propext`, `Classical.choice`, and `Quot.sound`. No prints were added. See [the report](../docs/research/rc-explicit-split.md) and [the results log](../scratch/rc-explicit-split/log.md).

**Remaining.** Pass the detecting-prime maximality clause to `explicit_isEichler_of_ramified_maximal` to get `IsEichler ell 1 (explicitOrderAt ell h)`. No new manuscript error was found in the checked steps. The known missing reduction bar at tex 8559 is outside this calculation and is recorded in the local division report.

Final proof and report SHA: `910f26854bc5b92d1a6056fd883aed8a89ef2c10`. This handoff is the sole change in the following commit; its SHA is available with `git log -1 --format=%H -- .fleet/rc-explicit-split.md`.
