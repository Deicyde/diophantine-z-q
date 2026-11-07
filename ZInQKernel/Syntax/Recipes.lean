import ZInQKernel.Syntax.Recipes.FixedScalar
import ZInQKernel.Syntax.Recipes.Translate
import ZInQKernel.Syntax.Recipes.PowerValue
import ZInQKernel.Syntax.Recipes.Outer
import ZInQKernel.Syntax.Recipes.Arith
import ZInQKernel.Syntax.Recipes.Precision
import ZInQKernel.Syntax.Recipes.Scope
import ZInQKernel.Syntax.Recipes.Accounting
import ZInQKernel.Syntax.Recipes.Polynomial
import ZInQKernel.Syntax.Recipes.Literal

/-!
# Recipes and the specified polynomial

The semantics of the fixed-scalar templates, the translation of natural circuits into
model-evaluation recipes, the recipes `power_value`, `precision`, `close`, `main`,
`value_union`, `value` and `integers`, their witness accounting, and the specified polynomial
`P_*` with its rational zero projection (blueprint chapter `syntax/`, section `recipes/`).
-/
