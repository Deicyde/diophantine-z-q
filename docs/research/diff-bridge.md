# diff-bridge: the global different leaves T20 and T21, proved

## Main result

Both global leaves that `GlueConductor.D1_genuine` (`ZInQKernel/HDecomp/Conductor/Breaks.lean`)
consumes are proved. Each theorem has exactly the leaf's Prop as its type, takes no hypotheses, and
uses only the three standard axioms (VERIFIED: compiled, `#print axioms`):

```lean
-- ZInQKernel/Contrib/Different/Bridge.lean
theorem ZInQ.Contrib.Different.hilbertDifferentFormula : GlueConductor.HilbertDifferentFormula
-- ZInQKernel/Contrib/Different/SerreLocal.lean   (T21 from t-different's local bound)
theorem ZInQ.Contrib.Different.serreDifferentBound_of_local : GlueConductor.SerreDifferentBound
-- ZInQKernel/Contrib/Different/Global.lean       (T21 from Tau Ceti's Wild.lean; second proof)
theorem ZInQ.Contrib.Different.serreDifferentBound : GlueConductor.SerreDifferentBound
```

Each T21 proof also gives the closed form of D1: `D1_genuine_closed_of_local` in `SerreLocal.lean`,
and `D1_genuine_closed` in `Global.lean`. Both have the hypotheses of `GlueConductor.D1_genuine`,
with `hH` and `hS` dropped:

```lean
theorem ZInQ.Contrib.Different.D1_genuine_closed_of_local (L : Type) [Field L] [NumberField L]
    [IsGalois ℚ L] (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 L)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (a : ℕ) (ha : 1 ≤ a)
    (hea : P.ramificationIdx ℤ ≤ a.factorial) (b : ℕ) (hb : GlueConductor.ramGroup L P b ≠ ⊥) :
    GlueConductor.phi (GlueConductor.ramCard L P) b ≤ 4 * a ^ 2
```

There are two proofs of T21 for a reason. `SerreLocal.lean` follows the route the task set: the
local bound `PkgI6.differentBound` of task t-different, applied to `ℤ_p ⊆ 𝒪_{L_w}`, then
transported to `𝓞 L`. It needs only Tau Ceti modules in tc-port's port1 list (VERIFIED: the import closure of `SerreLocal.lean` contains 154 Tau Ceti modules, all of them in port1.txt). `Global.lean` uses
Tau Ceti's own global bound instead (`LocalGlobal/Different/Wild.lean`). That needs 11 more Tau
Ceti modules, which this task vendored (§3). An integrator who wants fewer vendored files can keep
`Bridge.lean`, `Local.lean` and `SerreLocal.lean`, and drop `Global.lean` together with those 11
modules.

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

The `#print axioms` output (`scratch/diff-bridge/AxiomsGlobal.lean` and `AxiomsSerreLocal.lean`).
These files also check `example : GlueConductor.HilbertDifferentFormula := …` and
`example : GlueConductor.SerreDifferentBound := …`:

```
'ZInQ.Contrib.Different.hilbertDifferentFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.Different.serreDifferentBound_of_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.Different.D1_genuine_closed_of_local' depends on axioms: [propext, Classical.choice, Quot.sound]
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

Builds (VERIFIED): `lake build` of `ZInQKernel.Contrib.Different.Local`, `.Bridge`, `.SerreLocal`
and `.Global` each end with "Build completed successfully" (warnings only, all in other files).

## 1. Files

| file | content |
|---|---|
| `ZInQKernel/Contrib/Different/Bridge.lean` | T20 (global), plus the bridge lemmas (`ℤ` vs `𝓞 ℚ`, `ramGroup` vs Tau Ceti, `v_P(e)`) |
| `ZInQKernel/Contrib/Different/SerreLocal.lean` | T21 (global) from `PkgI6.differentBound`, and `D1_genuine_closed_of_local` |
| `ZInQKernel/Contrib/Different/Global.lean` | T21 (global) from Tau Ceti `Wild.lean`, and `D1_genuine_closed` |
| `ZInQKernel/Contrib/Different/Local.lean` | t-different's local T20, T21, T22a, T22b proofs, built on I6Base's definitions |
| `ZInQKernel/Contrib/TauCeti/…` (11 files, list in `scratch/diff-bridge/wild-extra.txt`) | Tau Ceti oct16 modules vendored by this task (see §3) |
| `scratch/diff-bridge/Axioms{Global,SerreLocal,Local}.lean` | type and axiom checks |

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
* `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_adicCompletionIntegers_eq_multiplicity_asIdeal`
  (`Exponent.lean`): `v_{𝔪_w}(𝔇(𝒪_w/𝒪_v)) = v_w(𝔇(𝓞 L/𝓞 K))`. Also
  `multiplicity_map_adicCompletionIntegers` (`AdicValuation/Multiplicity.lean`):
  `v_{𝔪_w}(I·𝒪_w) = v_w(I)`. Both are used by `SerreLocal.lean`.
* `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_le_ramificationIdx_sub_one_add_multiplicity_span`
  (`LocalGlobal/Different/Wild.lean`, vendored by this task; only `Global.lean` uses it). It states
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

**T21 from the local bound (`SerreLocal.lean`, VERIFIED, compiled).** Let `v = w ∩ 𝓞 ℚ`,
`A = v.adicCompletionIntegers ℚ` (that is, `ℤ_p`) and `B = w.adicCompletionIntegers L`.
* All instance arguments of `PkgI6.DifferentBound` are found for `A`, `B` in the scope
  `AdicCompletionExtension`: DVR, `isAdicComplete_adicCompletionIntegers`, a perfect residue field
  (finite), `Module.Finite`, `IsTorsionFree`, and separability (perfect field). So
  `PkgI6.differentBound A B : 𝔇(B/A) ∣ 𝔪_B^(e_loc - 1) · (e_loc)`, where
  `e_loc = Ideal.ramificationIdx 𝔪_B A`.
* `map_asIdeal_eq_maximalIdeal`: `v·A = 𝔪_A`. In the DVR `A`, `v·A = 𝔪_A^n`, and
  `multiplicity 𝔪_A (v·A) = multiplicity v v = 1`.
* `ramificationIdx_maximalIdeal_adicCompletionIntegers`: `e_loc = w.asIdeal.ramificationIdx (𝓞 ℚ)`.
  We have `e_loc = v_{𝔪_B}(𝔪_A B)` (`ramificationIdx_eq_multiplicity`). Next,
  `𝔪_A B = (v·𝓞 L)·B` (square `adicCompletionIntegersExtension_algebraMap`), and
  `v_{𝔪_B}((v 𝓞 L) B) = v_w(v 𝓞 L) = e(w/v)`.
* Then `v_w(𝔇) = v_{𝔪_B}(𝔇(B/A)) ≤ (e - 1) + v_{𝔪_B}((e)) = (e - 1) + v_w((e)) ≤ e - 1 + e·v_p(e)`.

Comparison of the definitions of ramification groups: see the first bullet above. t-different's
`PkgI6.lowerRam A B i = (𝔪_B^(i+1)).toAddSubgroup.inertia (B ≃ₐ[A] B)` is not compared with
`ramGroup` here, because neither global proof uses the local groups. The T20 proof uses Tau
Ceti's comparison, and T21 involves no ramification groups.

## 3. Tau Ceti modules vendored by this task (used only by `Global.lean`)

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
`ZInQ.Contrib.Different.hilbertDifferentFormula`, `ZInQ.Contrib.Different.serreDifferentBound_of_local`
(or `serreDifferentBound`),
`PkgI6.herbrandQuotient` and `PkgI6.herbrandTransitivity`. The same two theorems discharge the
`hH`, `hS` hypotheses of `GlueD1Local.D1_local`, `D1_local'`, `D1_krasner` and `D1_krasner'`
(`ZInQKernel/HDecomp/Conductor/D1Local.lean`). This task did not edit those existing files.
