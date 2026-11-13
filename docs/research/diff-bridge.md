# diff-bridge: the global different leaves T20 and T21, proved

## Main result

Both global leaves that `GlueConductor.D1_genuine` (`ZInQKernel/HDecomp/Conductor/Breaks.lean`)
consumes are proved. Each theorem has exactly the leaf's Prop as its type, takes no hypotheses, and
uses only the three standard axioms (VERIFIED: compiled, `#print axioms`):

```lean
-- ZInQKernel/Contrib/Different/Global.lean
theorem ZInQ.Contrib.Different.hilbertDifferentFormula : GlueConductor.HilbertDifferentFormula
theorem ZInQ.Contrib.Different.serreDifferentBound : GlueConductor.SerreDifferentBound
theorem ZInQ.Contrib.Different.D1_genuine_closed (L : Type) [Field L] [NumberField L]
    [IsGalois ℚ L] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (a : ℕ) (ha : 1 ≤ a)
    (hea : P.ramificationIdx ℤ ≤ a.factorial) (b : ℕ) (hb : GlueConductor.ramGroup L P b ≠ ⊥) :
    GlueConductor.phi (GlueConductor.ramCard L P) b ≤ 4 * a ^ 2
```

Here are the two leaves (Breaks.lean:341 and :350, unchanged):

```lean
def HilbertDifferentFormula : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
    ∃ n, ramGroup L P n = ⊥ ∧
      P ^ (∑ i ∈ range n, (ramCard L P i - 1)) ∣ differentIdeal ℤ (𝓞 L) ∧
      ¬ P ^ (∑ i ∈ range n, (ramCard L P i - 1) + 1) ∣ differentIdeal ℤ (𝓞 L)

def SerreDifferentBound : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → ∀ (P : Ideal (𝓞 L)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    ¬ P ^ (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L)
```

The `#print axioms` output (`scratch/diff-bridge/AxiomsGlobal.lean`, which also checks
`example : GlueConductor.HilbertDifferentFormula := ZInQ.Contrib.Different.hilbertDifferentFormula`
and the same for T21):

```
'ZInQ.Contrib.Different.hilbertDifferentFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.Different.serreDifferentBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.Different.D1_genuine_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The four local leaves of task t-different can now be imported (VERIFIED: compiled, same axioms).
They have exactly the `PkgI6` types of `ZInQKernel/HDecomp/Conductor/I6Base.lean`:

```lean
-- ZInQKernel/Contrib/Different/Local.lean
theorem PkgI6.hilbertDifferentFormula : PkgI6.HilbertDifferentFormula
theorem PkgI6.differentBound : PkgI6.DifferentBound
theorem PkgI6.herbrandQuotient : PkgI6.HerbrandQuotient
theorem PkgI6.herbrandTransitivity : PkgI6.HerbrandTransitivity
```

`#print axioms` (`scratch/diff-bridge/AxiomsLocal.lean`): `[propext, Classical.choice, Quot.sound]`
for all four.

Builds (VERIFIED): `lake build ZInQKernel.Contrib.Different.Local` and
`lake build ZInQKernel.Contrib.Different.Global` both end with "Build completed successfully"
(warnings only).

## 1. Files

| file | content |
|---|---|
| `ZInQKernel/Contrib/Different/Global.lean` | T20 and T21 (global) and `D1_genuine_closed` |
| `ZInQKernel/Contrib/Different/Local.lean` | t-different's local T20, T21, T22a, T22b proofs, built on I6Base's definitions |
| `ZInQKernel/Contrib/TauCeti/…` (11 files, list in `scratch/diff-bridge/wild-extra.txt`) | Tau Ceti oct16 modules vendored by this task (see §3) |
| `scratch/diff-bridge/AxiomsGlobal.lean`, `AxiomsLocal.lean` | type and axiom checks |

`Local.lean` is `scratch/t-different/All.lean` with two kinds of block removed: its local copies of
`lowerRam`, `mem_lowerRam`, `lowerRamR`, `herbrandPhi`, `upperRam` and `lowerRam_tower`, and of the
four leaf defs. It imports `ZInQKernel.HDecomp.Conductor.I6Base` instead. The proofs are not
changed.

## 2. How the global proofs work

Tau Ceti already proves both statements for number fields, over `𝓞 K` and in the language of
`multiplicity`. It transports the local theorems through the completion (STANDARD: Neukirch,
*Algebraic Number Theory*, III (2.2), (2.6); Serre, *Corps locaux*, IV §1 Prop. 4 and III §6;
locators UNVERIFIED). The Tau Ceti inputs are:

* `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one`
  (`LocalGlobal/Different/Exponent.lean`, vendored by tc-port). For `L/K` Galois:
  `multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) = ∑ᶠ i, (Nat.card (w.asIdeal.ramificationGroup Gal(L/K) i) - 1)`.
* `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_le_ramificationIdx_sub_one_add_multiplicity_span`
  (`LocalGlobal/Different/Wild.lean`, vendored by this task). It states
  `multiplicity w 𝔇 ≤ e(w/v) - 1 + multiplicity w (span {e(w/v)})`.
* `Ideal.exists_forall_ramificationGroup_eq_bot` (`RingTheory/Ideal/RamificationGroup.lean`): if the
  action is faithful and the inertia group is finite, then `G_i = 1` for all large `i`.

**How the definitions match (all VERIFIED, compiled).**
* Ramification groups. Tau Ceti's `Ideal.ramificationGroup G Q i` is defined as
  `(Q ^ (i + 1)).inertia G`, which is the same term as `GlueConductor.ramGroup L P i` with
  `G = Gal(L/ℚ)`. This is the lemma `ramificationGroup_eq_ramGroup`, proved by
  `Ideal.ramificationGroup_def`. Inside Tau Ceti, `card_ramificationGroup_eq_card_lowerRamificationGroup`
  compares these global groups with the lower ramification groups of the completion `L_w/ℚ_p`. That
  comparison is Tau Ceti's proof, and this task did not need to redo it.
  t-different's `PkgI6.lowerRam` (for a DVR extension `B/A`) is the same construction with
  `maximalIdeal B` in place of `P`. The global proofs do not use it.
* `ℤ` versus `𝓞 ℚ`.
  * `range_algebraMap_ringOfIntegers_rat`: `(algebraMap (𝓞 ℚ) ℚ).range = (algebraMap ℤ ℚ).range`
    (`ℤ` is integrally closed).
  * `differentIdeal_int_eq_differentIdeal_ringOfIntegers_rat`:
    `differentIdeal ℤ (𝓞 L) = differentIdeal (𝓞 ℚ) (𝓞 L)`. Both sides are `(traceDual)⁻¹` by
    `coeSubmodule_differentIdeal`, and the two trace duals are cut out by the same subring of `ℚ`.
  * `ramificationIdx_int_eq`: `P.ramificationIdx ℤ = P.ramificationIdx (𝓞 ℚ)`. Unfold
    `Ideal.ramificationIdx_def`, then use that `ℤ → 𝓞 ℚ` is surjective, so
    `(P.under ℤ)·(𝓞 ℚ) = P.under (𝓞 ℚ)`.
* `multiplicity`, `finsum` and divisibility. `Ideal.finiteMultiplicity` (`P ≠ ⊤`, `𝔇 ≠ ⊥` by
  `differentIdeal_ne_bot`), `pow_multiplicity_dvd`, `FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt`,
  and `finsum_eq_sum_of_support_subset` with `n = N` taken from `exists_forall_ramificationGroup_eq_bot`.
  Faithfulness comes from `IsGaloisGroup.faithful (𝓞 ℚ)`.
* `v_P(e) = e · v_p(e)` (`multiplicity_span_ramificationIdx_le`; only `≤` is used). Write
  `e = p^k m` with `p ∤ m`. `P` is a prime element of the ideal monoid, so
  `emultiplicity P ((p)^k (m)) = k · v_P(p) + v_P(m)`. Here `v_P(p) = e` by
  `Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity`, and `v_P(m) = 0` because
  `P.under ℤ = (p)`.

## 3. Tau Ceti modules vendored by this task

`LocalGlobal/Different/Wild.lean` is in neither port1.txt nor kw-rest.txt. Its oct16 import closure
has 177 modules, and 11 of them are outside both lists (VERIFIED, `closure.py` plus `comm`). This
task vendored those 11 with `tcport.py ~/tc-oct16` (commit 5a01f5fe). Each keeps its Tau Ceti
copyright header and gets the provenance line; no other change was made:

```
TauCeti.NumberTheory.LocalField.Different.Eisenstein
TauCeti.NumberTheory.LocalField.Different.Tower
TauCeti.NumberTheory.LocalField.Different.Wild
TauCeti.NumberTheory.LocalField.Eisenstein.PowerBasis
TauCeti.NumberTheory.LocalField.Eisenstein.TotallyRamified
TauCeti.NumberTheory.LocalField.Unramified.Factorization
TauCeti.NumberTheory.NumberField.LocalGlobal.Different.Wild
TauCeti.RingTheory.DedekindDomain.AdicValuation.NatCastValuation
TauCeti.RingTheory.Polynomial.Eisenstein.Basic
TauCeti.RingTheory.Polynomial.Eisenstein.DiscreteValuationRing
TauCeti.RingTheory.Polynomial.Eisenstein.Minpoly
```

They build unmodified at our Mathlib pin (VERIFIED: `lake build …LocalGlobal.Different.Wild`,
4051 jobs, after merging origin/wip/tc-port at f22bb604).

## 4. What remains

Nothing remains for T20 and T21. The h-decomposition leaf list can drop T20 and T21 (global forms)
and the local forms I6.6 and I6.7, and T22a and T22b are importable from `Local.lean`.
`HSyn.TextbookLeaves.t20/t21/t22a/t22b` (`scratch/h-decomposition/Leaves.lean:21511-21514`) can be filled with
`ZInQ.Contrib.Different.hilbertDifferentFormula`, `ZInQ.Contrib.Different.serreDifferentBound`,
`PkgI6.herbrandQuotient` and `PkgI6.herbrandTransitivity`. The same two theorems discharge the
`hH`, `hS` hypotheses of `GlueD1Local.D1_local`, `D1_local'`, `D1_krasner` and `D1_krasner'`
(`ZInQKernel/HDecomp/Conductor/D1Local.lean`). This task did not edit those existing files.
