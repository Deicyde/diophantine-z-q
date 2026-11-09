import ZInQKernel.Model.Heights.SearchCheck

/-!
# The kernel run of the small-height search

`searchCheck = true`, checked by the kernel (`decide +kernel`, no `native_decide`).
-/

namespace ZInQ.Search

theorem searchCheck_eq_true : searchCheck = true := by decide +kernel

end ZInQ.Search
