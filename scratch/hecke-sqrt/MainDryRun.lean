import ZInQKernel.OneProof.H.TailZ83
import ZInQKernel.Contrib.OneProof.Y3X6Fold
import ZInQKernel.MainGreenTao
import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.HeckeSqrtFold

namespace ZInQ.OneProof

/-- **Theorem 1.1, from every statement still open:** the open H bundles and pole completeness PC
(the manuscript's Theorem 5.2). -/
theorem _root_.ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves60Y3) (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves27)
    (hPC : ZInQ.PoleCompleteness) :
    ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (HDec.HSyn.sixContactMin_of_open79_heckeSqrt r t l) hPC

end ZInQ.OneProof

#print axioms ZInQ.OneProof.frozenTarget
