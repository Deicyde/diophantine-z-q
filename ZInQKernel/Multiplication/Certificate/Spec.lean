import ZInQKernel.Multiplication.Certificate.Multiply
import ZInQKernel.Multiplication.Certificate.ConstantsProperties
import ZInQKernel.Syntax.Recipes.Polynomial

/-!
# The constructors of the specification

The unfolding of the multiplication template (`multiply_rel_iff`) and the guard lemmas are
stated for a constructor meaning `I`, with the semantics of the fixed-scalar template `S_{c_*}`
and the guard polynomial as hypotheses. For the constructors of the specification,
`specConstructors`, both hold: the guard of `specConstructors` is `G_T` by definition, and
`S_{c_*}` multiplies `ι(m)` by `c_* = 4 M₀ ≥ 4` (`scalarTemplate_rel_iff_iota`).
-/

namespace ZInQ.Mult

open Syntax

/-- **The fixed scalar `S_{c_*}`** for the constructors of the specification:
`Rel_{S_{c_*}}(ι(m), r) ⟺ r = ι(c_* m)`. -/
theorem spec_scalar_cstar_rel_iff (m : ℤ) (r : Fin 5 → ℚ) :
    (scalarTemplate specConstructors (Syntax.cstar : ℤ)).Rel (Fin.append (iota m) r) ↔
      r = iota (Syntax.cstar * m) :=
  scalarTemplate_rel_iff_iota specConstructors rfl
    (by exact_mod_cast le_trans (by norm_num) four_le_cstar) m r

end ZInQ.Mult
