# cheb-bridge results log

## 2026-11-13
- Target: `PkgI6.ChebotarevExists` (ZInQKernel/HDecomp/Conductor/I6Base.lean:273), `GlueC10.ChebotarevExists`
  (ZInQKernel/HDecomp/C10/C10.lean:21), verbatim identical. VERIFIED (read).
- Tau Ceti oct16 source: `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet`
  (Chebotarev/PrimeCounting/FrobeniusPrimeCount.lean), density `#C/#G`;
  `NumberField.Set.HasNaturalDensity.infinite` (ArithmeticDirichletSeries/NaturalDensity.lean:195);
  `exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk` (Chebotarev/FrobeniusPrimeSet.lean) gives σ itself
  (not a conjugate) as `IsArithFrobAt (𝓞 K) σ Q` at some `Q ∈ 𝔭.primesOver (𝓞 L)`;
  `isUnramifiedAt_of_mem_frobeniusPrimeSet` gives `Algebra.IsUnramifiedAt (𝓞 K) Q`. VERIFIED (read).
- Mathlib lacks `SMulCommClass Gal(M/ℚ) (𝓞 ℚ) (𝓞 M)`; Tau Ceti provides it
  (`NumberField.RingOfIntegers.smulCommClass`, NumberField/AutomorphismAction.lean). VERIFIED (compile error / read).
- tc oct16 checkout has no build; wip/tc-port not yet on origin at 03:06.
- scratch/cheb-bridge/BridgeCore.lean (Mathlib only): `exists_of_infinite` — infinite set of
  unramified primes of `𝓞 ℚ` with σ a Frobenius (unfolded congruence over `𝓞 ℚ`) above each ⇒ leaf
  conclusion for (M, S, σ). Uses `Rat.HeightOneSpectrum.natGenerator`/`primesEquiv` (Mathlib) for
  𝔭 ↦ p, `FormallyUnramified.comp` + `of_surjective` for 𝓞ℚ→ℤ unramified transfer,
  `Ideal.quotientEquiv` for `#(ℤ/p) = #(𝓞ℚ/𝔭)`. COMPILED (lake env lean, no errors). VERIFIED.
- ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean: copy of scratch/t-skolem-kw/FrobeniusDense.lean
  (namespaces → `ZInQ.Contrib.ChebFD.{C10,HSyn}`, local leaf copy → `PkgI6.ChebotarevExists`), HSyn defs
  (`Qbar`, `GQ`, `LiesOver`, `IsArithFrob`, `FrobeniusDense`) pasted verbatim from Leaves.lean lines 21099-21112,
  21211-21216. `lake build` OK. `frobeniusDense_of_chebotarev : PkgI6.ChebotarevExists → ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense`,
  axioms [propext, Classical.choice, Quot.sound]. VERIFIED (compiled).
- Merged origin/wip/tc-port (f22bb604). `lake build …PrimeCounting.FrobeniusPrimeCount` OK (4573 jobs, 1m44s). VERIFIED.
- ZInQKernel/Contrib/Chebotarev/Exists.lean: `ZInQ.Contrib.chebotarevExists : PkgI6.ChebotarevExists`,
  `ZInQ.Contrib.chebotarevExists_c10 : GlueC10.ChebotarevExists` (bridge core copied into
  namespace `ZInQ.Contrib.ChebBridge`). Compiled first try. VERIFIED.
- ZInQKernel/Contrib/Chebotarev/FrobeniusDense.lean: `ZInQ.Contrib.frobeniusDense : ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense`.
  `lake build ZInQKernel.Contrib.Chebotarev.FrobeniusDense` OK (9344 jobs). VERIFIED.
- #print axioms (scratch/cheb-bridge/Axioms.lean): all five theorems [propext, Classical.choice, Quot.sound]. VERIFIED.
- A script found the restated HSyn defs (LiesOver, IsArithFrob, FrobeniusDense, Qbar, GQ) textually identical to Leaves.lean. VERIFIED.
