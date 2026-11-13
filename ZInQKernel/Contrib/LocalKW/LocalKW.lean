import ZInQKernel.Contrib.LocalKW.Basic
import ZInQKernel.HDecomp.Conductor.I6Base

/-!
# Leaf T16 (I6.3): local Kronecker–Weber for `ℚ_p`, proved

`PkgI6.LocalKroneckerWeber p` asks that every finite abelian extension `L` of `ℚ_p` inside
`PadicAlgCl p = AlgebraicClosure ℚ_[p]` lie in `ℚ_p({x | x ^ m = 1})` for some `m > 0`. This is
`ZInQ.Contrib.LocalKW.le_adjoin_rootsOfUnity` (`ZInQKernel/Contrib/LocalKW/Basic.lean`), proved
from Tau Ceti's local class field theory (vendored under `ZInQKernel/Contrib/TauCeti/`).
-/

namespace ZInQ.Contrib

/-- **Local Kronecker–Weber (leaf T16 / I6.3).** For every prime `p`, every finite abelian
extension of `ℚ_p` inside `PadicAlgCl p` lies in `ℚ_p(μ_m)` for some `m ≥ 1`. -/
theorem localKroneckerWeber (p : ℕ) [Fact p.Prime] : PkgI6.LocalKroneckerWeber p := by
  intro L _ _
  exact LocalKW.le_adjoin_rootsOfUnity p L

end ZInQ.Contrib
