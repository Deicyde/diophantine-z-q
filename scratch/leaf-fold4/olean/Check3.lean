import TailI
open HDec.HSyn in
#check @HDec.HSyn.sixContactMin_of_open3
/-- The conclusion is the kernel's own `ZInQ.SixContactMin` (`ZInQKernel/Hypotheses/HeightMin.lean`). -/
example : (∀ (r : HDec.HSyn.OpenResearchLeaves2) (t : HDec.HSyn.OpenTextbookLeaves3)
    (l : HDec.HSyn.OpenAddedLeaves3) (g : HDec.HSyn.OpenGlue3), _root_.ZInQ.SixContactMin) :=
  HDec.HSyn.sixContactMin_of_open3
#print axioms HDec.HSyn.sixContactMin_of_open3
