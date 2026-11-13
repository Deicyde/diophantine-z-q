# cheb-bridge: fleet report

**Main result.** Leaf I6.4 (`ChebotarevExists`, the finite form of T18) and leaf T18
(`HSyn.FrobeniusDense`) are proved outright from Tau Ceti's Chebotarev density theorem. The
theorems below have no hypotheses, and `#print axioms` lists only propext, Classical.choice and
Quot.sound for each:

- `ZInQ.Contrib.chebotarevExists : PkgI6.ChebotarevExists` (ZInQKernel/Contrib/Chebotarev/Exists.lean)
- `ZInQ.Contrib.chebotarevExists_c10 : GlueC10.ChebotarevExists` (same file)
- `ZInQ.Contrib.frobeniusDense : ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense`
  (ZInQKernel/Contrib/Chebotarev/FrobeniusDense.lean). This is `HSyn.FrobeniusDense` restated
  verbatim from scratch/h-decomposition/Leaves.lean; a script found it textually identical.
- Also: `ZInQ.Contrib.ChebFD.HSyn.frobeniusDense_of_chebotarev : PkgI6.ChebotarevExists → …FrobeniusDense`
  (Contrib/Chebotarev/FrobeniusDenseOfExists.lean, t-skolem-kw's proof copied) and the Mathlib-only
  bridge lemma `ZInQ.Contrib.ChebBridge.exists_of_infinite`.

**What compiles.** `lake build ZInQKernel.Contrib.Chebotarev.FrobeniusDense` succeeds (9344 jobs).
The branch merges origin/wip/tc-port at f22bb604 for the vendored
`ZInQKernel.Contrib.TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount`. This task
vendored no Tau Ceti modules itself and edited no existing files.

**Proof idea.** The Frobenius prime set of `[σ]` has density `#[σ]/#G ≠ 0`, so it is infinite. Drop
the finitely many primes whose generator `natGenerator` lies in `S`. Tau Ceti's
`exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk` gives σ itself (not a conjugate) as a Frobenius
at some prime `Q` above the remaining prime. Moving from the base `𝓞 ℚ` to the base `ℤ` (residue
cardinality, `Q.under ℤ = (p)`, unramifiedness via `FormallyUnramified.comp`) uses only Mathlib.

**Remains.** Nothing for this task. The consumers in ZInQKernel/HDecomp still take these leaves as
hypotheses, because existing files may not be edited; wiring them in needs a new Contrib file in a
later wave. Details: docs/research/cheb-bridge.md, scratch/cheb-bridge/log.md.
