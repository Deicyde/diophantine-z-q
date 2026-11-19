import ZInQKernel.Contrib.OneProof.JDescent4Genus
import ZInQKernel.Contrib.OneProof.JDescent5

/-! # The CM degree row from Fowler's printed statement

`abVarFunctionFieldGenusOne` (the genus of the function field of a dimension-one abelian
variety over a number field is one) and `cmjDegree_of_print_of_genusOne` (the short coordinates
with their double pole along the period, from the genus) give the row `cmjDegree` from
`CMjDegreePrint` (Fowler, §2·1, p. 613) alone. Both are on-the-spot glue (provenance (c)). -/

namespace HDec.CMBranch.CMjBridges

/-- The row `cmjDegree` from Fowler's printed degree statement alone. -/
theorem cmjDegree_of_print_closed : CMjDegreePrint → CMjDegree :=
  cmjDegree_of_print_of_genusOne abVarFunctionFieldGenusOne

end HDec.CMBranch.CMjBridges
