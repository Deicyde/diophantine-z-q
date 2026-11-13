# cheb-bridge: leaf I6.4 / T18 (Chebotarev) proved from Tau Ceti

## Main result (VERIFIED: compiled, `lake build ZInQKernel.Contrib.Chebotarev.FrobeniusDense`)

| declaration | type | file |
|---|---|---|
| `ZInQ.Contrib.chebotarevExists` | `PkgI6.ChebotarevExists` | `ZInQKernel/Contrib/Chebotarev/Exists.lean` |
| `ZInQ.Contrib.chebotarevExists_c10` | `GlueC10.ChebotarevExists` | `ZInQKernel/Contrib/Chebotarev/Exists.lean` |
| `ZInQ.Contrib.frobeniusDense` | `ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense` | `ZInQKernel/Contrib/Chebotarev/FrobeniusDense.lean` |
| `ZInQ.Contrib.ChebFD.HSyn.frobeniusDense_of_chebotarev` | `PkgI6.ChebotarevExists → ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense` | `ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean` |
| `ZInQ.Contrib.ChebBridge.exists_of_infinite` | bridge lemma (below) | `ZInQKernel/Contrib/Chebotarev/Exists.lean` |

The leaf statement, `ZInQKernel/HDecomp/Conductor/I6Base.lean:273` (identical in `C10.lean:21`):

```lean
def ChebotarevExists : Prop :=
  ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (S : Finset ℕ) (σ : M ≃ₐ[ℚ] M),
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ Q : Ideal (𝓞 M), ∃ _ : Q.IsPrime,
      Q.under ℤ = Ideal.span {(p : ℤ)} ∧ Algebra.IsUnramifiedAt ℤ Q ∧ IsArithFrobAt ℤ σ Q
```

The theorems' types are the project's own defs `PkgI6.ChebotarevExists` and `GlueC10.ChebotarevExists`
(imported, not restated), with no hypotheses. `ZInQ.Contrib.ChebFD.HSyn.FrobeniusDense` is
`HSyn.FrobeniusDense` of `scratch/h-decomposition/Leaves.lean` (lines 21211-21216 at 883c4ddf). It is
restated together with `HSyn.Qbar`, `HSyn.GQ`, `HSyn.LiesOver` and `HSyn.IsArithFrob` (lines
21099-21112), because `HSyn` exists only in scratch. A script compared the def blocks with
`Leaves.lean` and found them textually identical (VERIFIED).

`#print axioms` output (`scratch/cheb-bridge/Axioms.lean`):

```
'ZInQ.Contrib.chebotarevExists' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.chebotarevExists_c10' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.frobeniusDense' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.ChebFD.HSyn.frobeniusDense_of_chebotarev' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.ChebBridge.exists_of_infinite' depends on axioms: [propext, Classical.choice, Quot.sound]
```

So leaves I6.4 (`ChebotarevExists`, both copies) and T18 (`HSyn.FrobeniusDense`) leave the leaf list.

## Dependencies

- `ZInQKernel.Contrib.TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount`, vendored by
  task tc-port (merged from origin/wip/tc-port at f22bb604; Tau Ceti oct16, commit 5a01f5fe). This task
  vendored no Tau Ceti modules itself.
- `ZInQKernel.HDecomp.Conductor.I6Base` and `ZInQKernel.HDecomp.C10.C10` (for the statements).
- The proof of T18 from I6.4 is task t-skolem-kw's `scratch/t-skolem-kw/FrobeniusDense.lean`, copied
  with only the namespaces renamed.

## Proof of `chebotarevExists` (VERIFIED: compiled)

Tau Ceti inputs, all read in the oct16 source:
- `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet ℚ M C`: the set `frobeniusPrimeSet ℚ M C`
  has natural density `#C / #Gal(M/ℚ)`. This is the set of primes `𝔭` of `𝓞 ℚ` that are unramified
  in `M` and have Artin class `C`.
- `NumberField.Set.HasNaturalDensity.infinite` and `ConjClasses.card_carrier_div_card_ne_zero`: a set
  with nonzero density is infinite.
- `exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk`: for `𝔭` in the set for `[σ]`, the element σ
  itself (not a conjugate) satisfies `IsArithFrobAt (𝓞 ℚ) σ Q` at some `Q ∈ 𝔭.primesOver (𝓞 M)`. So
  the conjugation step mentioned in the task was not needed.
- `isUnramifiedAt_of_mem_frobeniusPrimeSet`: `Algebra.IsUnramifiedAt (𝓞 ℚ) Q` for every `Q` over `𝔭`.

The bridge lemma `ChebBridge.exists_of_infinite` uses only Mathlib. Given an infinite set `T` of
primes of `𝓞 ℚ` with these two properties, it proves the leaf's conclusion:
- The map `𝔭 ↦ p` is `Rat.HeightOneSpectrum.natGenerator`, which is injective via `primesEquiv`.
  Its preimage of `S` is finite, so `T` minus that preimage still contains some `𝔭`.
- `Q.under ℤ = span {p}` follows from `span_natGenerator`, `Ideal.under_under` and `LiesOver.over`.
- `#(ℤ ⧸ Q.under ℤ) = #(𝓞 ℚ ⧸ Q.under (𝓞 ℚ))` holds via `Ideal.quotientEquiv` along
  `(intEquiv (𝓞 ℚ)).symm`. Hence `IsArithFrobAt (𝓞 ℚ)` implies `IsArithFrobAt ℤ`; the congruence
  is stated unfolded because Mathlib has no `SMulCommClass Gal(M/ℚ) (𝓞 ℚ) (𝓞 M)` (Tau Ceti supplies
  it as `NumberField.RingOfIntegers.smulCommClass`).
- For unramifiedness, `Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime Q)` is applied,
  with `FormallyUnramified ℤ (𝓞 ℚ)` from `of_surjective` because `ℤ → 𝓞 ℚ` is surjective.

## Remaining

None for this task. Not done: the new theorems are not wired into `ZInQKernel/HDecomp` consumers,
since existing files may not be edited.
