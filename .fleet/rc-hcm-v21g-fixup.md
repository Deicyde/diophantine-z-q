# rc-hcm-v21g-fixup hand-off

**Retired frozen field:** none yet.

**Error verdicts:** none.

**The fix.** The review's error (the 42.3.2 bijection candidate reached arbitrary curves, so injectivity carried hidden GLUE) is fixed with reach premises. `VoightThm4232Etale` (reach premises for `E`, `E′`) and `VoightCor4237` (reach premise for `E`) now require `∃ φ₀ : Hom E₀ E, IsSeparableIsogeny φ₀`; their conclusions are unchanged. `IsNonconstant`, `IsSeparableMor` (generic stalks) and `IsSeparableIsogeny` are Silverman §II.2 representations, and `SeparableReach E₀` is the source-fixed instance of `SeparableIsogenyExists`. That instance is checked in Lean by `separableReach_of_separableIsogenyExists`. `SeparableIsogenyExists` itself is stated and used by no proof: it is GLUE in every Voight edition, because the errata delete the p. 786 sentence and replace it with Cor. 42.2.28, which is itself GLUE.
- **Injectivity:** `levelDeuringClass_injective` now takes `hR : SeparableReach E₀`. It rests on `hEt` (with its five separable-scope inputs, listed in the report's audit table), `hInv` and `hR`.
- **Order lemma:** proved by inclusion plus maximality (ON THE SPOT). The right action `End(E) → B` extends to a ℚ-algebra automorphism (`exists_algEquiv_extend`), and maximality of `End(E)` through its frame gives equality (`exists_endRight_eq_of_mem_rightRing`). It rests on `hInv`, `hT` and `hV` only, so `VoightCor4237` is stated but unused. The fallback was not needed.

**Item 3 outcome (built).** `RC/HCMV21/PrimeModelReach.lean` proves `separableReach_of_primeModel`: for a reference `A_k` with `A` over `F_q`, `SeparableReach (A.baseChange k)` follows from `SilvermanII212PrimeModel`, `hInv`, `hT`, `hV` and `hq`.
- The one new printed candidate, `SilvermanII212PrimeModel`, is UNVERIFIED until the owner's page check, with rating UNCERTAIN. No fall in the GLUE count is claimed.
- The proof also builds the absolute Frobenius `primeFrob`/`primeFrobBC` (`IsMonHom`) and `primeFrobBC_pt` (the `q`-power map on `k`-points). It shows that a nonzero homomorphism is nonconstant, and the factor lemma `isMonHom_of_frob_comp`.
- Teeth (a), generic point to generic point, is proved. Teeth (b), "`primeFrobBC` is not `IsSeparableMor`", is **open**: it needs the generic stalk map of the Frobenius and the non-perfectness of a curve's function field, about 300–500 lines. Until then the candidate is flagged for the skeptic reader's vacuity check.
- Corollary: `levelDeuringClass_injective_primeModel` rests on `SilvermanII212PrimeModel`, `hEt`, `hInv`, `hT` and `hV`. The part (2) theorems keep `SeparableReach E₀` as their binder. The reach is recorded as a rating ("derivable in Lean from SilvermanII212PrimeModel (UNVERIFIED, rating UNCERTAIN)"), never as LEAF.
- Waterhouse 1969 §3.2 was weighed and not used (the report gives the reason).
- `isSeparableIsogeny_of_isEtaleIsogeny` (optional) was not attempted and is open.

**O-threading.** `RC/GoodRowWire/Assembly.lean` takes the binder `O : ∀ i, PMAdelic.OperatorComparison … (J i)` right after `J` and passes it through `Reference`, `referenceComparisons`, `actualRows`, `actualRowFamily`, `pointInputs`, `actualFamily`, `hCuspAt` and `oddStagedOfGoodRows`. `oddStagedOfSamePlace` builds. `docs/research/rc-goodrow-wire.md` and `.fleet/rc-goodrow-wire.md` are updated: binder order, the `O` row, the `X.frobenius` pin through `O.frobenius` (ELLIOT) read through `J.classes` (GLUE), and the locators `:222` and `:170–176`.

**For the integrator.**
- Stale locators: `RC/GoodRowWire/Row.lean:12` and `:72` cite `RC/PMWire/Assembly.lean:120–122` for `G`, which is now at `:122–124`.
- These reports still assert the v21f scope error: `docs/research/pm-adelic-join.md:115–121`, `:131`, `docs/research/rc-pm-geometry.md:93–99`, `docs/research/rc-stage-kummer.md:55`, `:66`.

**Build.** One at a time, under the throttle:
- `RC.HCMV21.LevelDeuringInjective` OK (13568 jobs);
- `RC.HCMV21.PrimeModelReach` OK (13571);
- `RC.Odd.Statements` OK (9058);
- `RC.GoodRowWire.Assembly` OK (13747).

`#print axioms` was run on 61 declarations, and every one depends only on `propext`, `Classical.choice` and `Quot.sound` (`scratch/rc-hcm-v21g-fixup/axioms.txt`).

Report: `docs/research/rc-hcm-v21g.md` (fixup block at the top). Log: `scratch/rc-hcm-v21g-fixup/log.md`.

**Final SHA:** this commit (the commit that adds this file; its parent is 79d33de34).
