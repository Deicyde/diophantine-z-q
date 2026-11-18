import ZInQKernel.Contrib.OneProof.CMBranch2
import ZInQKernel.Contrib.OneProof.CoxProperLattice

/-! # cox-lattice: the CM-branch hand-fold with `CoxProperLattice` filled by this task's proof (dry run)

cm-branch2's top (`CMBranch2.lean`) takes `c : CMBranch.CMInputs3` (its `CMInputs2` without `coxProperLattice`) and
fills the leaf with its own proof `CMBranch.coxProperLattice_proof` (`CMBranch/CoxProof.lean`). This dry run fills
it with the independent proof of this task, `CMBranch.CoxLattice.coxProperLattice_proof`
(`Contrib/OneProof/CoxProperLattice.lean`): either proof discharges the leaf. -/

namespace HDec.HSyn

/-- **Theorem 1.1's height hypothesis from the open statements and the five remaining CM-branch inputs**, the leaf
`CoxProperLattice` given by `CMBranch.CoxLattice.coxProperLattice_proof` (cox-lattice dry run). -/
theorem sixContactMin_of_open72_coxlattice (r : OpenResearchLeaves53) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) (c : CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  sixContactMin_of_open72_cm2_r5 r t l
    ⟨c.cmFibreSplit, c.fowlerProp27, c.cmjDegree, c.cmPotentialGood, c.cmHeight62,
      CMBranch.CoxLattice.coxProperLattice_proof⟩

end HDec.HSyn
