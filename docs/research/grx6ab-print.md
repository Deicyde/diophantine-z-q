# grx6ab-print: `gonzalezRotgerX6Ab` from printed statements, one object per leaf

Task grx6ab-print (2026-11-16/17). Base: integrate-w82 5e235a40, with fork main c1e4ed1b merged (leaf-fold32, top
`sixContactMin_of_open38`, TailZ45) and origin/wip/gr-dict 48db1227 merged (`GR56Lattice.lean`, `GRDict.lean`).
Contributor file: `ZInQKernel/Contrib/OneProof/GRX6AbPrint.lean` (namespace `GRX6AbPrint`; imports `…GRDict` and
`…UniformizationLeafAll`, never `Main`; no `sorry`). Scratch: `scratch/grx6ab-print/` (log: `log.md`). Marks:
VERIFIED (compiled, or read in the tree), STANDARD (published, exact reference), SPECULATIVE, UNVERIFIED (theorem
numbers from memory; no network on this host).

## 1. Result

**`gonzalezRotgerX6Ab` (GLUE, composite) is proved in Lean from two new printed leaves, one object each, plus the
existing research field `shimuraMainThmIDeligneY3AbU` and two textbook fields:**

```
GRX6AbPrint.gonzalezRotgerX6Ab_of_print :
  GRDict.GonzalezRotgerThm512X6 → RayClassCFT.ShimuraMainThmIDeligneY3AbU → GRX6AbPrint.X6CoarseModuli →
    ZInQ.HomLattice.GAGAMorphism → AvSplit.MumfordTorsionAlgClosed → HDec.QMSplit.Moduli.GonzalezRotgerX6Ab
```

| new leaf | what it says | locator | printed form? |
|---|---|---|---|
| `gonzalezRotgerThm512X6` (gr-dict's statement, unchanged) | González–Rotger Thm 5.12 at `(6,1)`: degree of `ℚ(x)` and `k ⊂ ℚ(x)` at CM points as GR define them, on every witness (no existence) | J. Math. Soc. Japan 58 (2006) Thm 5.12, p. 946; arXiv math/0612732 v1/v2 pp. 18–19 (VERIFIED in `locators.md`, row "R5: fields of definition", read by the audit) | **yes** (degree and embedding clauses of the printed theorem; §3) |
| `x6CoarseModuli` (new) | `X₀(6,1)/ℚ` is a proper smooth curve and a coarse moduli scheme for QM abelian surfaces: Galois-equivariant bijection on `ℚ̄`-points, `Aut 𝒪`-twists by automorphisms (Atkin–Lehner), classifying map of a level-3 family over a proper smooth curve | Shimura 1967 §§2–3; Deligne Sém. Bourbaki 389 §§4–5; Buzzard, Duke 87 (1997) §1 — **UNVERIFIED** | **yes, with reading risk** (one object and its coarse-moduli property; §4) |

The combining steps are Lean proofs (VERIFIED, standard axioms; §5):
* `x6ModuliWitness_of_coarse`: the moduli witness `GRDict.X6ModuliWitness` (`∃ Y Φ X Ψ fY, R1fpPropsAb ∧ X6Props`)
  from `Y₃` of `shimuraMainThmIDeligneY3AbU` and `X6CoarseModuli`. The forgetful map `fY : Y₃ → X₆` is the
  classifying map of the universal family of `Y₃` (`R1famAbProps`); its fibres are objects since `Φ` is onto.
* `x6CoarseModuli_of_witness`: the converse, so the new leaf is never stronger than the witness it replaces.
* gr-dict's `gonzalezRotgerX6Ab_of_witness` and the CM-point dictionary `isGRCMPoint_of_com` (from the textbook
  fields; `uniformizationLeafAll` is now `uniformizationLeafAll_proof`, a theorem).

**Count**: the field `gonzalezRotgerX6Ab` (GLUE) is replaced by two `published` leaves: **−1 GLUE** in strict and
strictest (autofold `--dry-run`, §6), independent of the Elkies row. The witness is no longer asserted by any new
field: `Y₃` comes from a field already in the bundle, `X₆` is a single published object.

## 2. Consumers (VERIFIED, grep at c1e4ed1b)

* TailZ23 L715 (`x6Rows_of_open14`) → TailZ21 `r1r2fpRep_of_printedW`: uses the witness
  (`geomConnX6W_of_gr`) **and** `R5ptProps` (`ShimuraSplit.r5fp_of_point`).
* TailZ27 L105: `gonzalezRotgerCountX6Ab_of_printed n.gonzalezRotgerProp56X6 n.gonzalezRotgerX6Ab` (the witness).

Both the witness and the residue-field clause are read, so the field cannot be traded for a weaker one; the full
statement is proved.

## 3. What was still missing after gr-dict, and why this closes it

* kinds.tsv row 12 (11-16 dictionary pass): "asserts the witness `R1fpPropsAb` plus `X6Props`, which no print
  states". gr-dict moved Thm 5.12 to a printed every-witness leaf, but took the witness from
  `elkiesX6StarFunctionField`, which the same pass re-rated GLUE for the same witness, and which the concurrent task
  elkies-print is splitting into an every-witness leaf plus a witness Prop. Two folds each taking the witness from
  the other's field would be circular.
* Here the witness is split: `Y₃` (with `R1fpPropsAb`) is read from `shimuraMainThmIDeligneY3AbU` (already a field,
  composite for its own reasons, unchanged), `X₆` is the coarse-moduli leaf, and the H-168 shape (two moduli spaces
  plus the forgetful map in one `∃`) is a Lean proof.
* elkies-print agreed (cross-session, 11-16) to consume a witness Prop with exactly the body of
  `GRDict.X6ModuliWitness`, so `x6ModuliWitness_of_coarse` serves both folds.

**Thm 5.12 rating** (as gr-dict §3.3, re-checked): GR's `CM(R)` is GR's own notion (`IsGRCMPoint`: the torus
`ℂ²/ι(𝒪)(z,1)ᵀ` at `z` fixed by an optimal embedding); the every-witness form is equivalent to the canonical-model
form because `ℚ(x)` is the fixed field of the stabilizer of `Ψ x` (Galois-equivariant `Ψ`); at `(6,1)`,
`D(R) ≠ 1` iff some `p ∣ 6` is inert, `N* = 1`, `[H_R : ℚ] = 2h(R)` (STANDARD ring class field theory). Printed form.

## 4. The new leaf `X6CoarseModuli` and its rating

```lean
def X6CoarseModuli : Prop :=
  ∃ (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)),
    IsProper X.hom ∧ SmoothOfRelativeDimension 1 X.hom ∧ Nonempty (fieldPt Qbar ⟶ X) ∧
    (∀ σ x P, Ψ x = ⟦P⟧ → ∃ Q, Ψ (fieldMap σ ≫ x) = ⟦Q⟧ ∧ IsBaseChangeOfPair σ P Q) ∧
    (∀ α : O ≃+* O, ∃ g : X ≅ X, ∀ x P, Ψ x = ⟦P⟧ → Ψ (x ≫ g.hom) = ⟦P.twist α⟧) ∧
    (∀ S, IsProper S.hom → SmoothOfRelativeDimension 1 S.hom → ∀ 𝒜' : QMAbScheme S.left,
      (∀ K s, ∃ P, IsFibreOf 𝒜'.toQMFamily s.left P) →
      ∃ g : S ⟶ X, ∀ (s : fieldPt Qbar ⟶ S) P, IsFibreOf 𝒜'.toQMFamily s.left P → Ψ (s ≫ g) = ⟦P.forget⟧)
```

(abbreviated; the file has the full binders.) The first five clauses are `X6Props` without `Y` and `fY`, verbatim.

**Printed form: yes, flagged "locator UNVERIFIED; reading risk".**
* *The print.* The canonical model `X₀(D,N)` over `ℚ` is a coarse moduli scheme for abelian surfaces with QM by an
  Eichler order of level `N` (Shimura 1967; Deligne 389 for the moduli interpretation; Buzzard 1997 §1 for the
  coarse statement with level structures). Numbers and pages UNVERIFIED (no network). A locators.md row is proposed
  in §7.
* *Clause by clause* against the definition of a coarse moduli scheme (Mumford, GIT Def. 5.6: a natural
  transformation `F → Hom(-, X)`, bijective on algebraically closed fields, initial):
  * bijection on `ℚ̄`-points: the definition;
  * Galois equivariance: naturality at `Spec ℚ̄ → Spec ℚ̄` (the moduli functor over `ℚ`);
  * the family clause: the natural transformation at a proper smooth curve base, applied to the `(A, ι)` underlying
    a level-3 family, read on `ℚ̄`-points (a specialization: fewer bases, more structure, an extra hypothesis);
  * the twist clause: an automorphism of the moduli functor induces an automorphism of the coarse space
    (initiality); at `D = 6` these are the Atkin–Lehner involutions (gt-elkies `IsAtkinLehner`).
    **Reading risk**: the print defines `w_m` through the ideal `I_m`; the twist form is the standard description
    when every `I_m` is principal (`D = 6`, class number one). This is the same reading `X6Props` already uses.
  * proper smooth curve with a `ℚ̄`-point: Shimura's canonical model is a smooth projective curve; `ℚ̄`-points exist.
* *Over genuine definitions.* Mathlib schemes, the kernel's `QMPair`, `QML3`, `QMAbScheme`, `IsFibreOf` (the same
  objects as the existing `R1fpPropsAb`), nothing invented for the purpose.
* *Never stronger than the composite it replaces*: `x6CoarseModuli_of_witness` (VERIFIED) derives it from
  `X6ModuliWitness`, through `R1univAbProps` and `fY`.
* *What a skeptic may still say*: no print states the clause list in this exact form. The difference from the
  H-168 shape is that it describes one published object by the defining property of a coarse moduli space; a
  statement check should confirm the coarse-moduli locator and the twist reading.

## 5. Lean (VERIFIED unless marked)

* `lake build +ZInQKernel.Contrib.OneProof.GRX6AbPrint` succeeds on c1e4ed1b + gr-dict (VERIFIED,
  `scratch/grx6ab-print/build2.txt`). gr-dict's `GR56Lattice.lean` and `GRDict.lean` compile on the current main
  unchanged.
* The file (VERIFIED, all `[propext, Classical.choice, Quot.sound]`):
  * `X6CoarseModuli : Prop` (the new leaf);
  * `x6ModuliWitness_of_coarse : ShimuraMainThmIDeligneY3AbU → X6CoarseModuli → GRDict.X6ModuliWitness`;
  * `x6CoarseModuli_of_witness : GRDict.X6ModuliWitness → X6CoarseModuli` (never stronger);
  * `gonzalezRotgerX6Ab_of_coarse` (with `uniformizationLeafAll` as a hypothesis) and
    `gonzalezRotgerX6Ab_of_print` (with `uniformizationLeafAll_proof`).
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`: 0 errors (`build3.txt`).

## 6. `#discharges` and the autofold dry-run

`scratch/grx6ab-print/Discharges.lean`, output `discharges.txt` (VERIFIED):

```
DISCHARGES [OpenResearchLeaves28.gonzalezRotgerX6Ab] by GRX6AbPrint.gonzalezRotgerX6Ab_of_print
  still assumes: [GRDict.GonzalezRotgerThm512X6,
 RayClassCFT.ShimuraMainThmIDeligneY3AbU,
 GRX6AbPrint.X6CoarseModuli,
 ZInQ.HomLattice.GAGAMorphism,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 45 open hypotheses, 6871 theorems checked, 21 discharge one
```

(`gonzalezRotgerX6Ab_of_coarse`, gr-dict's `_of_printed` and `_of_witness` are listed too.)

**Autofold.** `scratch/grx6ab-print/autofold.json` discharges `gonzalezRotgerX6Ab` by `gonzalezRotgerX6Ab_of_print`.
It adds the leaves `gonzalezRotgerThm512X6` and `x6CoarseModuli` (kind `published`). The flag of
`gonzalezRotgerThm512X6` is empty, so autofold sets it to "unread". The flag of `x6CoarseModuli` is "locator
UNVERIFIED; reading risk: …". `--dry-run` (VERIFIED, `autofold-dryrun.txt`):
**strict 16/21 on 37 → 18/20 on 38; strictest 16/21 → 18/20 (−1 GLUE).** The generated module
(`FoldCheck.lean`, the dry-run output minus line 1) compiles: `sixContactMin_of_open39` uses the standard axioms only.

**Combined with elkies-print** (its branch, 168bbb39, is merged here). `autofold-combined.json` discharges both
`gonzalezRotgerX6Ab` and `elkiesX6StarFunctionField`. The Elkies witness comes from
`x6ModuliWitness_of_coarse {n}.shimuraMainThmIDeligneY3AbU {n}.x6CoarseModuli` instead of from
`{n}.gonzalezRotgerX6Ab`. Results (VERIFIED):
* **strict 16/21 on 37 → 19/19 on 38 (−2 GLUE)**;
* `FoldCheckCombined.lean` compiles with standard axioms;
* elkies-print's `X6WitnessAb` and `GRDict.X6ModuliWitness` unify.

**For the integrator**: land this fold first, or use the combined spec. elkies-print's own spec reads
`{n}.gonzalezRotgerX6Ab`, which this fold removes. gr-dict's spec (witness from the Elkies field) is superseded by
this one; folding both would add `gonzalezRotgerThm512X6` twice.

## 7. Proposed locators.md row (for the integrator)

| R1/X6: coarse moduli | Shimura, Ann. of Math. 85 (1967); Deligne, Sém. Bourbaki 389 (1971); Buzzard, Duke Math. J. 87 (1997) | UNVERIFIED (to read: the coarse-moduli statement for `X₀(D,N)`, and the definition of `w_m`) | — | pending reading |

## 8. What remains

* A reading of the coarse-moduli locator and of the Atkin–Lehner twist form (statement check).
* Thm 5.12, the coarse moduli theorem and the canonical model are not formalized (no Shimura curves in Mathlib).
* `shimuraMainThmIDeligneY3AbU` stays composite GLUE; it is unchanged here (it already supplies `Y₃`).
