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
