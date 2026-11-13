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
