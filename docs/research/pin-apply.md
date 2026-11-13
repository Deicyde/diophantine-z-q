# pin-apply: integration of the qm-pin repair (the QM leaf R1 now pins `Φ`)

Task pin-apply, 2026-11-13. Base 2dd83306 (`origin/wip/integrate-w36b`) merged with
`origin/wip/qm-pin` (40c17c32). Scratch: `scratch/pin-apply/` (results log `log.md`). Model work
only, no human review.

## 1. Main result

qm-pin's full edit is applied and compiles, with no `sorry` and only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`. Two clauses are added to `R1fpProps`:
- `R1famProps`: `Φ` is induced by a family `𝒜 → Y`.
- `R1univProps`: every family over a proper smooth curve is classified by a morphism to `Y`.

It is applied in two places:
- the kernel (`ZInQKernel/HDecomp/QM/Leaves.lean`, plus the new module `QM/Pin.lean`);
- `scratch/h-decomposition/Leaves.lean`.

All VERIFIED by running Lean:

- **Kernel.** `lake build ZInQKernel` succeeds (10013 jobs). `scripts/print_axioms.lean` has 542
  lines (16 new for `Pin`), and every one gives the standard three axioms
  (`scratch/pin-apply/axioms2.txt`).
- **`Leaves.lean`.** `lake env lean scratch/h-decomposition/Leaves.lean` gives 0 errors and no
  `sorryAx`. It has 190 `#print axioms` lines, all standard, and they include:
  - `HSyn.sixContactMin_of_leaves r t gp`, unchanged;
  - the new `HSyn.sixContactMin_of_leaves_pin` (`scratch/pin-apply/run_hdec2.txt`, 7m56s).
- **The three QM pieces reduce to one triple.** `FibreSimple`, `ThetaPointOfFibre` and
  `ModularConstituent` quantify over every triple `(Y, Φ, π)` that satisfies `R1fpProps` and
  `R2fpProps`. Given the named glue Prop `LeafQM.AV.Pin.MobiusGlue`, each piece is equivalent to
  its statement for any single such triple, for example the leaf's own (§3).
- **The relabeling attack no longer applies** (§4, compiled).
  - rv-g0pieces' proof of `r1fp_relabel` fails verbatim against the new clauses.
  - Any relabeling `τ` that survives has the form `y ↦ y ≫ g` for a morphism `g : Y → Y`
    (`relabel_is_morphism`, proved from `R1univProps` alone, without `MobiusGlue`).
  - rv-g0pieces' exotic relabeling `relabelOver s φ` survives only if `s` is the map on points of
    such a `g`. So a non-continuous `s` is excluded (`not_r1fp_exotic`).
  - Caveat: swapping two closed points of a curve is continuous in the Zariski topology. That case
    is excluded only by the morphism statement plus an argument that is not compiled (§4).

## 2. Step 1: the kernel

- **`ZInQKernel/HDecomp/QM/Leaves.lean`.** `scratch/qm-pin/QM-Leaves-full.patch` is applied. The
  result is byte-identical to `scratch/qm-pin/QMLeavesFull.lean`. The patch makes these changes:
  - it adds `QMFamily`, `IsFibreOf`, `R1famProps` and `R1univProps`;
  - it appends `∧ R1famProps Y Φ ∧ R1univProps Y Φ` to `R1fpProps`;
  - it changes the two `obtain` patterns in `conj_twist_of_rational` and `conj_iso_of_rational`;
  - it updates the R1fp docstrings.
- **`ZInQKernel/HDecomp/QM/Pin.lean`** (new). It holds qm-pin's `namespace Pin … end Pin` block
  (lines 629-938 of `scratch/qm-pin/QMPinKernelFull.lean`) inside `LeafQM.AV`, under the header
  `import ZInQKernel.HDecomp.QM.Leaves`. pin-apply added one theorem, `relabel_is_morphism`. The
  module is imported from `ZInQKernel/HDecomp.lean`.
- **`scripts/print_axioms.lean`.** 16 lines are added, `LeafQM.AV.Pin.*`:
  - the projections `R1fpProps.fam` and `R1fpProps.univ`;
  - the attack lemmas `r1fpPin_relabel_iff`, `r1fpPin_aut`, `r2fp_aut`, `sameTriple_aut`,
    `relabel_geometric` and `relabel_is_morphism`;
  - the transfer lemmas `transfer_pointwise`, `transfer_exists`, `transfer_pointwise_mor`,
    `pointwise_of_witness` and `pointwise_of_witness_mor`;
  - the comparison `phi_part` and `sameTripleMor_of_mobius`;
  - `cm_objects_of_R1R2fp`.

  All 16 are standard.
- Nothing else in `ZInQKernel/` mentions `R1fpProps` (checked by grep).

## 3. Step 2: `scratch/h-decomposition/Leaves.lean`

Reproducible from the pre-edit file in two steps:

1. `python3 scratch/pin-apply/apply_edit.py IN OUT full` applies the same clause block. This is
   qm-pin's script; it now reads the pre-edit kernel file from
   `/tmp/pinapply_kernel_orig.lean` = `git show 2dd83306:ZInQKernel/HDecomp/QM/Leaves.lean`. It
   also changes the two `obtain` patterns.
2. `python3 scratch/pin-apply/apply_hdec.py` inserts the following:
   - **the `Pin` block** in `LeafQM.AV`, identical to the kernel's. `check_identical.py` confirms
     that the clause block and the `Pin` block match the kernel text;
   - **in `HSyn.G0Split`:**
     - the one-triple forms `FibreSimpleAt`, `ThetaPointOfFibreAt` and `ModularConstituentAt`,
       with `…_eq_forall_at` (`Iff.rfl`: each piece is its `…At` form for every triple);
     - `fibreOver_of_sameTripleMor`, which transfers the `∃`-form `FibreOver`;
     - `sameTripleMor_of_leaves (hM : MobiusGlue) (hQM : R1R2fp)`: any two triples are compared
       by a morphism, using `cm_objects_of_R1R2fp` for the CM objects;
     - `fibreSimple_of_at`, `thetaPointOfFibre_of_at`, `modularConstituent_of_at`, and the
       equivalences `fibreSimple_iff_at`, `thetaPointOfFibre_iff_at`,
       `modularConstituent_iff_at`. For instance `FibreSimple ↔ FibreSimpleAt Y₀ Φ₀ π₀`, for any
       triple satisfying the clauses;
     - the `∃`-forms `FibreSimpleW`, `ThetaPointOfFibreW`, `ModularConstituentW`, and
       `qmPieces_iff_w hM hQM`, which shows that each of the three pieces is equivalent to its
       `∃`-form;
   - **in `HSyn`:**
     - `structure GluePiecesPin`: the fields of `GluePieces`, with pieces 4, 9, 10 in `∃`-form,
       plus `mobius : LeafQM.AV.Pin.MobiusGlue`;
     - `gluePieces_of_pin r : GluePiecesPin → GluePieces` and
       `gluePiecesPin_of r : GluePieces → MobiusGlue → GluePiecesPin`;
     - `sixContactMin_of_leaves_pin (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePiecesPin) : ZInQ.SixContactMin`.

`GluePieces` and `sixContactMin_of_leaves` are unchanged. `MobiusGlue` is not proved here; it is a
named glue Prop. The parallel task mobius-glue (`origin/wip/mobius-glue`, not merged here) proves
it from `CurveRatFactor`, `CurveSurj`, `AutOInnerFinite` and the leaf T5.

The `∃`-forms and `GluePiecesPin` answer a soundness question: each piece is true exactly when it
is true for the genuine `Y₃`. As proof targets, the `∀`-forms in `GluePieces` remain the natural
ones, because a prover only knows the clauses of the triple in either form.

## 4. Step 4: the attack (`scratch/pin-apply/AttackCheck.lean`, compiled)

The file imports the kernel's `QM.Pin`. The kernel's clause block and `Pin` block are textually
identical to those in `Leaves.lean`, so its conclusions apply to `Leaves.lean`.

1. **The old proof fails.** rv-g0pieces' proof of `r1fp_relabel`, verbatim, no longer proves
   `R1fpProps Y (relabel Φ τ)`: `fail_if_success` succeeds. The proof breaks at `intro`, because
   the fourth conjunct is now naturality ∧ `R1famProps` ∧ `R1univProps`.
2. **Only the old part survives.** That same old proof still proves the old part of the list
   (`relabel_keeps_old_part`).
3. **A surviving relabeling needs a family.** `attack_needs_family` (from `r1fpPin_relabel_iff`):
   if the relabeled triple satisfies the list, some `QMFamily` over `Y` has the class of `τ y` as
   its fibre at every `y`.
4. **A surviving relabeling is a morphism.** `relabel_is_morphism` (in the kernel): if `Φ` and
   `Φ ∘ τ` both satisfy the list, then `τ = (· ≫ g)` for a morphism `g : Y ⟶ Y`.
5. **The exotic relabeling.** This part uses rv-g0pieces' `relabelPt`, `relabelOver` and
   `relabelOver_natural`, copied verbatim from `scratch/rv-g0pieces/Exotic.lean`.
   - `exotic_relabel_morphism`: if `relabel Φ (relabelOver Y s φ)` satisfies the repaired list,
     then `s x = g.left x` for every point `x`, for some morphism `g`. The proof evaluates the
     relabeling at the point `Spec κ(x) → Y`, with `κ(x)` given its `ℚ`-algebra structure from
     `Y → Spec ℚ`.
   - `not_r1fp_exotic`: if `s` is not continuous, the relabeled triple fails `R1fpProps`.

All axioms lines are standard (`scratch/pin-apply/run_attack.txt`).

**Caveat.** qm-pin §3.4's concrete exotic example swaps two closed points with isomorphic residue
fields in one fibre. On a curve this `s` is a homeomorphism, so item 5's corollary does not reach
it. Item 4 still applies: the swap would have to be the map on points of a morphism `g : Y → Y`.
That morphism would fix every other closed point, so it is the identity on the component, which
contradicts the swap. This last step is argued only, not compiled: it is algebraic geometry of
curves, the same kind of glue as `MobiusGlue`.

## 5. Step 3: docs

`docs/research/h-decomposition.md` has these changes:
- the R1 paragraph (§2.1) states the pin clauses, with their source: Shimura–Deligne R1(a) under
  Lemma P. Rigidity (Mumford GIT Ch. 6) and the extension of the polarization (Faltings–Chai
  I.2.7) are given with UNVERIFIED numbers;
- a §0 bullet;
- the §2.3 Lean check;
- in the glue table, rows 4, 9, 10 (the one-triple equivalences) and a new row 12 (`MobiusGlue`,
  in `GluePiecesPin`);
- a paragraph "The QM pieces and the pin".

`docs/research/g0-split.md` line 99 belongs to another task and was not edited. The change qm-pin
§5 suggests there is still pending.

## 6. What remains

- **`MobiusGlue`** is a named glue Prop. The mobius-glue reduction exists and is still to be
  integrated.
- **Faithfulness of `R1univProps`** needs the extension of the type-`μ` polarization over a normal
  base. A human check of qm-pin §2.1 is advisable, and the locator numbers are UNVERIFIED.
- **The Props held back by the defect** (FS5 `FibreComTrivial`, `FibreQMPeriod`,
  `KernelFieldExists`) can now be stated for the pinned triple. This was not done here.
- **The closed-point-swap step in §4** is argued only.
