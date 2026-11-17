# elkies-print: `elkiesX6StarFunctionField` discharged from Elkies' statement on every witness, without the bundled moduli witness

Task elkies-print, 2026-11-16. Base: wip/elkies-print 5e235a40 merged with origin/main c1e4ed1b (leaf-fold32, top
`sixContactMin_of_open38`; wip/integrate-w82 was already on main). Lean: `ZInQKernel/Contrib/OneProof/ElkiesX6StarEvery.lean`
(the contribution). It imports only `ZInQKernel.Contrib.OneProof.ElkiesX6StarPrinted`, the module that declares the
statement. Working copy and checks are in `scratch/elkies-print/`. No other file under `ZInQKernel/` or `blueprint/`
was edited. This is model work with no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a locator recalled without a source (no network; Elkies' paper not
available on this host).

## 1. Main result

**The research field `elkiesX6StarFunctionField` is a theorem from one new leaf, `ElkiesX6StarEvery`, together with
the moduli witness that the bundle already supplies (field `gonzalezRotgerX6Ab`).** The new leaf is Elkies' coordinate
statement, unchanged from elkies-coord's function-field form, stated for **every** witness of the moduli description
of `X₀(6,1)`. It makes no existence claim, which was the defect behind the 11-16 re-rating ("it carries the same R1
moduli witness rated composite elsewhere"). The leaf is **not stronger than the field it replaces**. Given a witness
and T5, the two are equivalent, and that equivalence is proved in Lean (`every_iff_functionField`). The transport to
every witness is the comparison of witnesses, which is a Lean proof (§3). VERIFIED: compiled, standard axioms only.

Autofold dry-run (`scratch/elkies-print/autofold.json`):
`strict count: 16/21 on 37 -> 17/20 on 37; strictest 16/21 -> 17/20`, i.e. **one GLUE field fewer** in both
columns, provided the new leaf is rated published (§4 discusses that rating). VERIFIED.

```
DISCHARGES [OpenResearchLeaves28.elkiesX6StarFunctionField] by HDec.QMSplit.Moduli.ElkiesPrint.elkiesX6StarFunctionField_of_every
  still assumes: [HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery, HDec.QMSplit.Moduli.ElkiesPrint.X6WitnessAb]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves28.elkiesX6StarFunctionField] by HDec.QMSplit.Moduli.ElkiesPrint.elkiesX6StarFunctionField_of_every_gr
  still assumes: [HDec.QMSplit.Moduli.ElkiesPrint.ElkiesX6StarEvery, HDec.QMSplit.Moduli.GonzalezRotgerX6Ab]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 45 open hypotheses, 6702 theorems checked, 15 discharge one
```

This was run after `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.ElkiesX6StarEvery` (14102 jobs, success; `frozenTarget` uses the standard axioms),
output in `scratch/elkies-print/discharges.txt`. `X6WitnessAb` is not a new field: the fold fills it from
`{n}.gonzalezRotgerX6Ab`, the second line. The generated fold module (`scratch/elkies-print/FoldDryRun.lean`,
`OpenResearchLeaves29`, `sixContactMin_of_open39`) compiles, and `#print axioms HDec.HSyn.sixContactMin_of_open39`
gives the standard three. VERIFIED.

## 2. The statements (namespace `HDec.QMSplit.Moduli.ElkiesPrint`)

```lean
def X6WitnessAb : Prop :=                -- not a leaf: from gonzalezRotgerX6Ab, or GRDict.X6ModuliWitness
  ∃ Y Φ X Ψ fY, R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY

def ElkiesX6StarEvery : Prop :=          -- the new LEAF
  ∀ Y Φ X Ψ fY, R1fpPropsAb Y Φ → X6Props Y Φ X Ψ fY →
    ∃ t : ToP1 X.left,
      (∀ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
        fixedByW Ψ = Subfield.closure {germ t.U η hη t.f}) ∧         -- ℚ(X₆)^W = ℚ(t)
      (CM clause: t = 0, 1, ∞ at HasCM24, HasCM4, HasCM3) ∧
      X6Glue.ElkiesCharts X t                                      -- s² = −t, r² = 3(t − 1)

theorem elkiesX6StarFunctionField_of_every (h : ElkiesX6StarEvery) (hW : X6WitnessAb) :
    ElkiesCoord.ElkiesX6StarFunctionField
theorem x6WitnessAb_of_gonzalezRotgerX6Ab : GonzalezRotgerX6Ab → X6WitnessAb
theorem every_of_functionField (h : ElkiesCoord.ElkiesX6StarFunctionField) (hT : ObjBridge.TorsionStructure) :
    ElkiesX6StarEvery
theorem every_iff_functionField (hW : X6WitnessAb) (hT : ObjBridge.TorsionStructure) :
    ElkiesX6StarEvery ↔ ElkiesCoord.ElkiesX6StarFunctionField
```

(Binders are abbreviated here; the file has the exact text.) The clauses after `∃ t` are those of
`ElkiesX6StarFunctionField`, copied verbatim. The only change is `∃ witness, …` → `∀ witness, … → ∃ t, …`.

## 3. The proof (all VERIFIED, compiled)

* **Discharge.** Take the witness from `X6WitnessAb` and apply the leaf to it. That gives the field's `∃`.
* **Converse (`every_of_functionField`).** This shows the leaf is not stronger than the field.
  1. *Fine comparison* (`phi_part_ab`, `compare_iso_ab`). Two fine witnesses with `R1fpPropsAb` are isomorphic
     compatibly with `Φ`. This is the kernel's `compare_iso` (TailU) for the abelian-scheme clauses: the universal
     property `R1univAbProps` applied to the other witness's family `R1famAbProps`, then `eq_id_of_fieldPts`.
  2. *Coarse comparison over one fine witness* (`coarse_compare_ab`). Two coarse witnesses over the same `(Y, Φ)`
     are isomorphic compatibly with `Ψ`. This is the kernel's `coarseFactor_of` and `coarseCompare_of` (TailZ20),
     restated with `R1fpPropsAb`, with these inputs:
     * `PairsLift` from T5 (`ShimuraSplit.pairsLift_of_T5`: every QM pair over `ℚ̄` has a level-3 structure);
     * `CoarseFactorAG.factorThroughSurj` (proved);
     * `HSyn.curveBijIso_lf7` (proved).
     Between them sits `x6Props_transport`, which moves the old coarse witness onto the new fine witness.
  3. *Transport of Elkies' clauses* along `k : X ≅ X₀` with `Ψ₀ ∘ k = Ψ` (§3 of the file):
     * `ffMap`: the comorphism of an open immersion on Mathlib's function fields, with `ffMap_germ`, `ffMap_comp`
       and `ffMap_id`;
     * `isAtkinLehner_conj`/`'`: `g ↦ k⁻¹ g k` is a bijection between the Atkin–Lehner groups;
     * `fixedByW_eq_image`: `ℚ(X)^W = k^*(ℚ(X₀)^W)`;
     * `ff_transport`: integrality and the generic point transfer, and `Subfield.closure` commutes with ring maps
       (`RingHom.map_field_closure`);
     * `cm_transport`: through `ToP1.val_comp_right`;
     * `charts_transport`: affine opens via `IsAffineOpen.preimage_of_isIso`, the ring isos composed with `k.app`,
       and the gluing equations by naturality.
     The coordinate on the new witness is `t₀.comp k.hom.left`.

`#print axioms` on `elkiesX6StarFunctionField_of_every`, `every_of_functionField` and `every_iff_functionField`
gives `[propext, Classical.choice, Quot.sound]` (`scratch/elkies-print/Axioms.lean`). VERIFIED.

## 4. Leaf and glue table, and the rating

| statement | kind | source | rating |
|---|---|---|---|
| `ElkiesX6StarEvery` | new leaf | Elkies 1998 (ANTS-III, LNCS 1423) §3 (section, display, `0/∞` orientation UNVERIFIED) | **printed form, under the moduli reading of `X(6)` that every `X₆` leaf uses** (see below) |
| `X6WitnessAb` | existence of the moduli witness, not a leaf | from the field `gonzalezRotgerX6Ab` (already GLUE, composite) or from grx6ab-print's `GRX6AbPrint.x6ModuliWitness_of_coarse` | not counted (no new field) |
| `ffMap`, `phi_part_ab`, `compare_iso_ab`, `coarse_compare_ab`, transport lemmas | glue | proved | proved |

**Rating of `ElkiesX6StarEvery`: printed form.** SPECULATIVE judgement; the paper was not read.
* *The defect that made the field GLUE is gone.* The field asserted that a fine `Y₃` and a coarse `X₆` exist with
  the clause lists `R1fpPropsAb`, `X6Props`. No print states that. The new leaf asserts nothing about existence: if
  no witness existed, it would hold vacuously. The existence is carried by `gonzalezRotgerX6Ab`, which is already
  rated composite for exactly this reason, so no glue is hidden in a leaf.
* *Not stronger than the field.* Given T5 (a theorem of the build from the textbook field `mumfordTorsionAlgClosed`,
  via `AvSplit.torsionStructure_of_mumford`), the field implies the leaf (`every_of_functionField`). The universal
  quantifier over witnesses costs nothing beyond the field, because the witness is unique up to compatible
  isomorphism, and that uniqueness is proved in Lean. The clauses themselves are elkies-coord's function-field
  reading of Elkies, whose rating arguments (integrality presupposed and proved from the charts; `ℚ(X/W) = ℚ(X)^W`)
  carry over unchanged (docs/research/elkies-coord.md §4).
* *Same shape as an accepted precedent.* `GRCountX6.GonzalezRotgerProp56X6` (gt-grcount) is a printed statement on
  every witness, with the witness from `gonzalezRotgerX6Ab`; its statement review (11-14) rated it faithful.
* *Residual reading risk, stated plainly.* `X(6)`, its `W` and its CM points are read through the moduli
  interpretation: Lean's `X₆` is a coarse witness with `Ψ`, `W` is `atkinLehnerW` (twists by `Ad μ_m`), and the CM
  points are pairs with `HasCM24`, `HasCM4`, `HasCM3` (Shimura 1967; Rotger 2004; locators UNVERIFIED). Elkies works
  on Shimura's canonical model. On 11-16 the dictionary pass re-rated `gonzalezRotgerProp56X6` as a consequence for
  the CM-point half of this reading ("CM(R) read as polarization-free ℚ̄ pairs only through Shimura 1967 and descent
  of CM pairs"). If the integrator applies the same ruling to the CM clause here, the new leaf is a consequence too,
  and the net count change is 0 instead of −1. Even then the field is no longer a composite: one source, one
  dictionary. Before folding, the reviewer should decide this one question, which applies to every `X₆` leaf alike.

**Proposed kinds.tsv row:** kind `published`, flag `locator UNVERIFIED (section, display, 0/infinity orientation)`
(this is what the spec does). If the dictionary ruling is applied: kind `consequence`, flag "moduli reading of the CM
points (as gonzalezRotgerProp56X6)".

## 5. What remains, and caveats

* **Elkies' wording**: the section, the display and the `0/∞` orientation are UNVERIFIED, as for gt-elkies and
  elkies-coord. A reader with the paper should confirm `t = 0, 1, ∞` at `D = −24, −4, −3` and the function field
  `ℚ(t)(√−t, √(3(t − 1)))`.
* **Fold order with grx6ab-print** (coordinated by message on 11-16). Task grx6ab-print folds `gonzalezRotgerX6Ab`.
  It builds the witness as `GRX6AbPrint.x6ModuliWitness_of_coarse : ShimuraMainThmIDeligneY3AbU → X6CoarseModuli →
  GRDict.X6ModuliWitness`, whose body equals `X6WitnessAb` binder for binder. My spec takes the witness from
  `{n}.gonzalezRotgerX6Ab`. If grx6ab-print's fold lands first, `gonzalezRotgerX6Ab` leaves the bundle, and the proof
  in my spec should read
  `elkiesX6StarFunctionField_of_every {n}.elkiesX6StarEvery (GRX6AbPrint.x6ModuliWitness_of_coarse {n}.shimuraMainThmIDeligneY3AbU {n}.x6CoarseModuli)`.
  The witness types are definitionally equal, so `id` converts. Neither task consumes the other's field, so the
  folds are not circular.
* No kernel computation applies: the statement is not about explicit equations alone. It asserts a coordinate on a
  moduli witness.

## 6. Files and checks

* `ZInQKernel/Contrib/OneProof/ElkiesX6StarEvery.lean`: the contribution.
* `scratch/elkies-print/ElkiesPrint.lean`: the working copy (identical text).
* `scratch/elkies-print/Axioms.lean`: the `#print axioms` checks.
* `scratch/elkies-print/Discharges.lean`, `discharges.txt`: the `#discharges` check.
* `scratch/elkies-print/autofold.json`, `autofold-dryrun.txt`, `FoldDryRun.lean`: the fold spec, its dry-run, and
  the generated module with line 1 stripped.
* `scratch/elkies-print/log.md`: the results log.

## 7. For the integrator

* Fold: `python3 scripts/one_proof/autofold.py scratch/elkies-print/autofold.json`. It removes
  `elkiesX6StarFunctionField` from the research bundle and adds `elkiesX6StarEvery` (kind `published`, flag
  `locator UNVERIFIED (...)`).
* Proposed `docs/research/locators.md` row (not added here, since that file belongs to other tasks):
  `ElkiesX6StarEvery` | Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998), §3 (`X*(6)`): "`t` is a
  coordinate on `X*(6) = X(6)/W`", the CM values `t = 0, 1, ∞` at `D = −24, −4, −3`, and
  `ℚ(X(6)) = ℚ(t)(√−t, √(3(t − 1)))`; stated on every witness of the moduli description | section, display and the
  `0/∞` orientation UNVERIFIED (not read; recalled) |
