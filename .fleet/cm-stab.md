# cm-stab (fleet summary)

**Proved** (`ZInQKernel/Contrib/OneProof/CMStab.lean`, imports only `…Contrib.OneProof.QMLattice`; no sorry; every
theorem `#print axioms` = [propext, Classical.choice, Quot.sound], VERIFIED in `scratch/cm-stab/axioms.txt`):

```lean
theorem GapGlue.cmStabObj_of (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hT : ObjBridge.TorsionStructure) : CMStabObj
theorem GapGlue.cmStabObjWeak_of (hU) (hG) (hM) (hT) : CMStabObjWeak
theorem GapGlue.cmStabObj_of_textbook (hU) (hG) (hM) : CMStabObj          -- T5 from hM (kernel lemma)
theorem GapGlue.cmStabObjWeak_of_textbook (hU) (hG) (hM) : CMStabObjWeak
theorem GapGlue.atkinLehnerFixesCM24_of (hU) (hG) (hM) : HDec.CMStabAL.AtkinLehnerFixesCM24
```
`CMStabObj` is copied verbatim from `scratch/mcr-quot/MCRQuot.lean` L7639-7653 (identical to the one p1-quot's
`FixedDisjoint.lean` uses, `QuotientP1/MCRQuotB.lean` L976-990); `CMStabObjWeak` is byte-identical to
`FixedDisjoint.lean` L540-546 (wip/p1-quot f30ece89); `AtkinLehnerFixesCM24` (p1-quot's LEAF, QuotientP1/CMStab.lean
L435-446 at d984b2547) is copied verbatim and is now a theorem. hU, hG, hM are fields of `OpenTextbookLeaves11`.
Both clauses of the involution/non-identity part are proved: T² ≅ id on every class through [±1]; T moves the class
of `rightMul w P` by an 𝔽₉ computation plus commutativity of End_𝒪(A) (lattice model, gt-qm).

**#discharges** (`scratch/cm-stab/discharges.txt`): 63 open hypotheses, 5 discharged, none by CMStab (expected:
CMStabObj is not a bundle field). No autofold spec.

**Fold** (docs/research/cm-stab.md §3): in p1-quot's `quotientP1Coordinate_of_printed'` pass
`hO := GapGlue.cmStabObjWeak_of_textbook hU hG hM`; this removes p1-quot's leaf `AtkinLehnerFixesCM24` (and `hQ`,
`hAL`) from `quotientP1Coordinate_of_printed`; mcr-quot's `hO : CMStabObj` gets `GapGlue.cmStabObj_of_textbook hU hG hM`.
Bridge the GapGlue/HDec.MCRQuot copies by `rfl`.

**Remains:** nothing for this task. Not done: the `rfl` bridge to p1-quot's constants in a tree where both modules
are built (checked only by elaborating their text in my tree, `scratch/cm-stab/nscheck.txt`).
