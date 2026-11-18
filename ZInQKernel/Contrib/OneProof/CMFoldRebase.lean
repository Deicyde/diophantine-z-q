import ZInQKernel.Contrib.OneProof.CMFoldRebase.Open77
import ZInQKernel.Contrib.OneProof.CMBranch2

/-! # cm-fold-rebase: the CM-branch fold on main's top (`sixContactMin_of_open76`, TailZ83)

The deliverable of docs/research/cm-fold-rebase.md. cm-branch2's fold (the manuscript's CM branch, diophantine_zq.tex
L581-605, in place of the chain's NoCM base; González–Rotger's Thm 5.12 dropped as unread) regenerated on main's top,
whose chain runs through bost-gr9's copied bundles `HDec.HSyn.GR9` (TailZ80):

* `HDec.HSyn.sixContactMin_of_open77_cm (r : OpenResearchLeaves58CM) t l` (`CMFoldRebase/Open77.lean`): the next
  generation, `OpenResearchLeaves57` without `gonzalezRotgerThm512X6RCF` and with the five CM-branch inputs;
* `HDec.HSyn.sixContactMin_of_open76_cmfold` below: main's top theorem with one extra hypothesis
  `c : CMBranch.CMInputs3` (the five CM-branch inputs), the field `gonzalezRotgerThm512X6RCF` of `r` unread.
-/

namespace HDec.HSyn

/-- **Main's top theorem on the CM branch** (cm-fold-rebase): `sixContactMin_of_open76`'s bundles plus the CM-branch
inputs `CMInputs3` (the GLUE `CMFibreSplit`, the leaves `FowlerProp27`, `CMjDegree`, `CMPotentialGood`, `CMHeight62`);
the route does not read `r.gonzalezRotgerThm512X6RCF`. -/
theorem sixContactMin_of_open76_cmfold (r : OpenResearchLeaves57) (t : OpenTextbookLeaves18)
    (l : OpenAddedLeaves27) (c : CMBranch.CMInputs3) : ZInQ.SixContactMin :=
  sixContactMin_of_open77_cm
    { r with
      cmFibreSplit := c.cmFibreSplit
      fowlerProp27 := c.fowlerProp27
      cmjDegree := c.cmjDegree
      cmPotentialGood := c.cmPotentialGood
      cmHeight62 := c.cmHeight62 } t l

end HDec.HSyn

#print axioms HDec.HSyn.sixContactMin_of_open77_cm
#print axioms HDec.HSyn.sixContactMin_of_open76_cmfold
