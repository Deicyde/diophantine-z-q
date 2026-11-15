import ZInQKernel.Contrib.OneProof.CMStab
#check @AvSplit.torsionStructure_of_mumford
example (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) : GapGlue.CMStabObj :=
  GapGlue.cmStabObj_of hU hG hM (AvSplit.torsionStructure_of_mumford hM)
