# qm-pin results log

Base: 883c4ddf + merges origin/wip/rv-g0pieces, origin/wip/g0-split (already in), origin/wip/notes-fix (6ff45ea6).

## Build
- `lake build ZInQKernel.HDecomp.QM.Leaves`: success, 9051 jobs, 3m24s (build0.txt).

## Design (step 1)
- Chosen: option 1 of rv-g0pieces §4, pin Φ by the universal family. New clause `R1famProps Y Φ`:
  ∃ 𝒜 : QMFamily Y.left (𝒜 → Y proper, smooth of rel. dim 2, ι(a) over Y, sections η(a)),
  ∀ K y P, Φ K y = [P] → IsFibreOf 𝒜 y.left P (pullback square + ι, η compatibility).
- `R1fpPropsPin` = old four clauses ∧ R1famProps (appended as 5th conjunct). R2fpProps unchanged.

## Lean (step 2-3), scratch/qm-pin/QMPin.lean (imports ZInQKernel.HDecomp.QM.Leaves)
- run1: 3 errors (isFibreOf_transport). run2: 2 errors. run3: 0 errors, 5.9 s. VERIFIED.
- `#print axioms` (13 declarations): all [propext, Classical.choice, Quot.sound]. VERIFIED (run3.txt).
- Compiled: QMFamily, IsFibreOf, R1famProps, R1fpPropsPin, R1R2fpPin, R1R2fp_of_pin, QMLeavesPin;
  glue re-proved on the repaired list: conj_twist_of_rational_pin (A7), conj_iso_of_rational_pin,
  unramified_over_branch_pin, residue_unramified_over_branch_pin (NV step 2, via cm_of_val = M9),
  exists_fibre_object_pin (A4), fibre_conjugates_isomorphic_pin (notes-fix form), leaves_on_one_witness_pin.
- Attack re-run: r1fpPin_relabel_iff (natural τ keeps the repaired list iff a QMFamily realizes the
  relabeled classes as fibres); r1fpPin_aut, r2fp_aut (automorphism relabelings keep both lists);
  sameTriple_aut; transfer_pointwise, transfer_exists; PinUnique (def, not proved); pointwise_of_witness.

## Integration edits checked (step 3)
- QMLeavesEdited.lean = ZInQKernel/HDecomp/QM/Leaves.lean + edit (QM-Leaves.patch: QMFamily, IsFibreOf,
  R1famProps before R1fpProps; 5th conjunct `R1famProps Y Φ`; two patterns `⟨-, -, -, hnat, -⟩`; R1fp
  docstring). Compiled as scratch importing ZInQKernel.HDecomp.QM.Pairs: 0 errors, 6.7 s. VERIFIED.
  Only ZInQKernel/HDecomp.lean imports QM.Leaves; no other kernel file mentions R1fpProps (grep). VERIFIED.
- SplitEdited.lean = scratch/g0-split/Split.lean + same def block + 2 patterns (Split.patch, apply_edit.py).
  Needed `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` (11 s).
  `lake env lean`: 0 errors, 0 sorry, 2m28s; `HSyn.glueOutputs_of_leaves`, `sixContactMin_of_leaves`,
  `thetaPazuki`, ... all [propext, Classical.choice, Quot.sound]. VERIFIED (run_split.txt).
  The ten pieces' text is unchanged: they quantify over R1fpProps, which now contains the family.
- HDecLeavesEdited.lean = scratch/h-decomposition/Leaves.lean + same edit (HDecLeaves.patch): 0 errors,
  2m41s; one `sorry` warning at the known `HSyn.glueOutputs_of_leaves` (line 21577 of the copy). VERIFIED.
- QMPin.lean run4 (adds relabel_geometric, PinUniqueOld, relabel_geometric_old): 0 errors, 5.6 s;
  15 `#print axioms`, all [propext, Classical.choice, Quot.sound]. VERIFIED (run4.txt).
- QMPinKernel.lean = QMLeavesEdited.lean + QMPin §3 (renamed to the patched `R1fpProps`, namespace
  `LeafQM.AV.Pin`, without the old-list lemmas): candidate content of a new kernel module
  `QM/Pin.lean`. run 2: 0 errors, 6.6 s; 10 `#print axioms`, all standard. VERIFIED (run_pinkernel.txt).
  (run 1: 4 errors from dot notation on `R1fpProps`/`QMFamily` across namespaces; fixed.)
