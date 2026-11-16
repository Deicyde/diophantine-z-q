# bg-explicit: `babaGranathRationalAb` proved from fields already in the bundles (no new leaf)

Task bg-explicit, 2026-11-15. Base 43513d87 (leaf-fold25, top `sixContactMin_of_open29`). Lean:
`ZInQKernel/Contrib/OneProof/BabaGranathRationalAb.lean` (the contribution; it imports `ZInQKernel.OneProof.H.TailZ22`,
which defines the statement, plus the folded contributions `ElkiesX6Star` and `QMLattice`). Scratch:
`scratch/bg-explicit/` (log, draft, `#discharges` check and output, autofold spec and dry-run). No other file under
`ZInQKernel/` was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (no network).

## 1. Result

**The research LEAF `babaGranathRationalAb` is a theorem from four fields already in the bundles, with no new leaf.**
VERIFIED: compiled (`lake build ZInQKernel.Contrib.OneProof.BabaGranathRationalAb`), standard axioms only.

```lean
theorem BGExplicit.babaGranathRationalAb_of_printed
    (h : HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : HDec.QMSplit.Moduli.BabaGranathRationalAb

theorem BGExplicit.babaGranathRationalAb_of_AL
    (h : HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted)
    (hW : HDec.HeckeRest.ALFixedPoints) : HDec.QMSplit.Moduli.BabaGranathRationalAb
```

```
'BGExplicit.babaGranathRationalAb_of_AL' depends on axioms: [propext, Classical.choice, Quot.sound]
'BGExplicit.babaGranathRationalAb_of_printed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The hypotheses of `babaGranathRationalAb_of_printed` are bundle fields of the base:
* `h` = `OpenResearchLeaves22.elkiesX6StarPrinted` (same bundle as the discharged field; Elkies 1998 §3);
* `hU`, `hG`, `hM` = `OpenTextbookLeaves11.uniformizationLeafAll`, `.gagaMorphism`, `.mumfordTorsionAlgClosed`.

`HDec.HeckeRest.ALFixedPoints` (TailG.lean:9485) is obtained from the last three exactly as the chain already does
(`HDec.QMSplit.Aut.rows_of_C (HDec.QMLattice.qmCentralizerCMC_of hU hG hM) (HDec.AVB2.t11b_of_exists
HDec.HSyn.t11bExists_lf8)`, TailU.lean:1526, Contrib/OneProof/QMLattice.lean:507, TailZ4.lean:60; the same term as
leaf-fold18's fold of `qmCentralizerCMC`).

## 2. `#discharges` and the fold

`scratch/bg-explicit/Discharges.lean`, run after `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.BabaGranathRationalAb` (full output `scratch/bg-explicit/discharges.txt`; the other 7
lines are the base's existing contributions). VERIFIED:

```
DISCHARGES [OpenResearchLeaves22.babaGranathRationalAb] by BGExplicit.babaGranathRationalAb_of_AL
  still assumes: [HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted, HDec.HeckeRest.ALFixedPoints]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.babaGranathRationalAb] by BGExplicit.babaGranathRationalAb_of_printed
  still assumes: [HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 ZInQ.HomLattice.GAGAMorphism,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1815 theorems checked, 9 discharge one
```

("still assumes" lists the hypotheses of each theorem; for `babaGranathRationalAb_of_printed` all four are open
bundle fields of the base, so the fold adds no leaf. `ALFixedPoints` in `babaGranathRationalAb_of_AL` is a chain
theorem from those textbook fields.)

**Autofold spec** `scratch/bg-explicit/autofold.json` (no new leaves; one cross-bundle `{t}` reference):

```json
{"name": "bg-explicit",
 "imports": ["ZInQKernel.Contrib.OneProof.BabaGranathRationalAb"],
 "discharges": [
   {"field": "babaGranathRationalAb",
    "proof": "_root_.BGExplicit.babaGranathRationalAb_of_printed {n}.elkiesX6StarPrinted {t}.uniformizationLeafAll {t}.gagaMorphism {t}.mumfordTorsionAlgClosed"}]}
```

`python3 scripts/one_proof/autofold.py scratch/bg-explicit/autofold.json --dry-run` (output
`scratch/bg-explicit/autofold-dryrun.txt`) reports `strict count: 46/10 on 56 -> 45/10 on 55; strictest 45/11 -> 44/11`
(one LEAF fewer, GLUE unchanged). Its generated module (line 1 stripped: `scratch/bg-explicit/FoldDryRun.lean`,
`OpenResearchLeaves23`, `sixContactMin_of_open30`) compiles: `'HDec.HSyn.sixContactMin_of_open30' depends on axioms:
[propext, Classical.choice, Quot.sound]`. VERIFIED. No consumer rerouting is needed (the field is filled by the
theorem in the fold's conversion `openResearchLeaves22_of_OpenResearchLeaves23`).

## 3. The instances used, and what the field asked beyond Elkies

The field (TailZ22.lean:91) asks for one witness `(Y, Φ, X, Ψ, fY)` with a coordinate `π : X → P¹` and three distinct
rational values `t₄, t₃, t₂₄` such that (fibre clause) `π(x) = π(x')` iff the QM pairs are `Aut(𝒪)`-twists, and
(CM clauses) `HasCM4 P ↔ π(x) = t₄`, `HasCM3 P ↔ π(x) = t₃`, `HasCM24 P ↔ π(x) = t₂₄`.

**Instances used** (VERIFIED, the proof's `refine`): Elkies' witness and coordinate `π := t` on `X₆ = X₀(6,1)`, with
`t₄ = 1`, `t₃ = ∞`, `t₂₄ = 0` (`t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3`), all three in `P¹(ℚ)`.
The CM points used are the two points of each of the fibres over `1`, `0`, `∞` of Elkies' conic model
`Y² + 3X² + 3Z² = 0`, `t = −X²/Z²`: `(X : Y : Z) = (±i : 0 : 1)` (CM by `ℤ[i]`), `(0 : ±√−3 : 1)` (CM by `ℤ[√−6]`),
`(1 : ±√−3 : 0)` (CM by `ℤ[ζ₃]`), over `ℚ̄` (no smaller field is needed).

* The fibre clause is gt-elkies' `elkiesEquationsX6Ab_of_printed` (the `W`-orbit clause of Elkies' leaf through the
  proved moduli step `orbit_iff_twist`).
* The forward CM clauses (`HasCM4 → t = 1` etc.) are Elkies' CM values.
* What Baba–Granath added is the converse: a point over `1` (resp. `∞`, `0`) has CM by `ℤ[i]` (resp. `ℤ[ζ₃]`,
  `ℤ[√−6]`). Given the fibre clause and the invariance of the CM predicates under twists and isomorphisms
  (`hasCM4_twist`, `HasCM4.of_iso`), this is equivalent to the existence of one CM point of each type (the kernel's
  `cm_of_val`, Leaves.lean:200, is the same argument). This existence is what the proof supplies.

So the reading flagged on the field (the CM assignment of the §3.1 elliptic-order table, UNVERIFIED) is no longer
needed: the assignment now rests on Elkies' CM values (already a clause of `elkiesX6StarPrinted`, with its own `0/∞`
orientation flag) and on the proved fibre computation.

## 4. Method (the finite computation)

1. **Fibres of `t` over `1, 0, ∞` have two points** (VERIFIED, `fibre_one`, `fibre_zero`, `fibre_infty`, `sep_of_sq`).
   Elkies' charts give the conic model on `ℚ̄`-points (`X6Glue.conicModelT_of_charts`, TailZ21.lean:1353: a bijection
   `e : X(ℚ̄) ≃ ConicPt` with `t = −X²` on the affine part and `t = ∞` at infinity). Over `t = 1`: `X² = −1`, then
   `Y² = −3X² − 3 = 0`; over `t = 0`: `X = 0`, `Y² = −3`; over `∞`: `b² = −3`. In each case one coordinate `c`
   is injective on the fibre and satisfies `c² = r²` for a fixed `r` (`r = i` or `√−3`), so the Boolean `c = r`
   separates the fibre's points.
2. **A point of such a fibre has CM** (VERIFIED, `key` in `babaGranathRationalAb_of_AL`). `X6Props` gives, for each
   `k : Fin 4`, an automorphism `g_k` of `X` acting on moduli by `P ↦ P.twist (rep k)` (`rep k` = conjugation by
   `1, i, j, ij`). The four points `x ≫ g_k` lie in the fibre of `x` (fibre clause with `α = rep k`). A map
   `Fin 4 → Bool` is not injective (`Fintype.exists_ne_map_eq_of_card_lt`), so `x ≫ g_a = x ≫ g_b` for some `a ≠ b`,
   whence `P.twist (rep a) ≅ P.twist (rep b)`. Re-indexing by `rep b` (`HDec.HeckeRest.qmCongr`, `rep_rep`,
   `xr_self`, `rep_zero`, TailG.lean:9508, 9769-9779) gives `P.twist (rep (xr a b)) ≅ P` with `xr a b ∈ {1, 2, 3}`
   (`xr_cases`, `decide`), and `ALFixedPoints` gives `HasCM4`, `HasCM3` or `HasCM24` (`cm_of_twist_iso`).
3. **Which CM** (VERIFIED): Elkies' forward CM values put `HasCM3` at `∞` and `HasCM24` at `0`, so the points over
   `1` have `HasCM4`; likewise the points over `0` have `HasCM24` and those over `∞` have `HasCM3`.
4. **The converse clauses** follow from one CM point per fibre by the fibre clause and invariance (step 3 of
   `babaGranathRationalAb_of_AL`).

## 5. Rating of new leaves

None. The theorem uses only bundle fields and proved chain theorems, so the fold removes a LEAF (strict count
unchanged in GLUE; one LEAF fewer).

## 6. Notes for the integrator

* **Interaction with elkies-coord** (`origin/wip/elkies-coord`, not on this base): that task discharges
  `elkiesX6StarPrinted` by `HDec.QMSplit.Moduli.ElkiesCoord.elkiesX6StarPrinted_of_functionField` from a new leaf
  `ElkiesX6StarFunctionField` (as its `.fleet` file reports; not checked here). If that fold lands first, the proof
  term of this fold becomes `_root_.BGExplicit.babaGranathRationalAb_of_printed (<elkies-coord's term for
  ElkiesX6StarPrinted from {n}.elkiesX6StarFunctionField>) {t}.uniformizationLeafAll {t}.gagaMorphism
  {t}.mumfordTorsionAlgClosed`; no change to this file is needed.
* The theorem does not need Mumford rigidity: the field is in abelian-scheme form (`R1fpPropsAb`) and Elkies' leaf
  carries the same `R1fpPropsAb` witness.
