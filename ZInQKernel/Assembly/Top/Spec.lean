import ZInQKernel.Assembly.Values
import ZInQKernel.Syntax.Recipes.Literal

/-!
# The specification at the program literal

The relations of the assembly chapter are those of the specification `specLib` with the
constructors `specConstructors`, the named constants `c_*`, `ℓ`, `T`, the program literal
`c₃ = code(𝒲)` and the natural precision circuit `𝒩 = precisionCircuitOf c₃`. This file names the
denotations `topLib`, the relations `Rel_close` and `Rel_value` at this specification, and the
multiplication statement M for its constructors.
-/

namespace ZInQ.Assembly

open Syntax Compiler.Universal

/-- The denotations of the seven recipes of the specification at the program literal
`c₃ = code(𝒲)` and the natural precision circuit `precisionCircuitOf c₃`. -/
noncomputable abbrev topLib : List ExPoly :=
  specLib specConstructors FixedConst.cstar.value FixedConst.ell.value FixedConst.T.value
    (c3 : ℤ) (precisionCircuitOf c3)

/-- `Rel_close(N, K, t)` of the specification (recipe `2`). -/
def CloseRel (N K : Fin 5 → ℚ) (t : ℚ) : Prop :=
  ValRel (getEx topLib 2) (List.ofFn N ++ (List.ofFn K ++ [t]))

/-- `Rel_value(N, t)` of the specification (recipe `5`). -/
def ValueRel (N : Fin 5 → ℚ) (t : ℚ) : Prop :=
  ValRel (getEx topLib 5) (List.ofFn N ++ [t])

/-- The multiplication statement M for the constructors and constants of the specification. -/
abbrev SpecMultiplicationExact : Prop :=
  Translation.MultiplicationExact specConstructors FixedConst.cstar.value FixedConst.ell.value
    FixedConst.T.value

end ZInQ.Assembly
