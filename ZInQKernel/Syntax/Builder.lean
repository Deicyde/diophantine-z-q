import ZInQKernel.Syntax.Builder.Construction
import ZInQKernel.Syntax.Builder.Scope
import ZInQKernel.Syntax.Builder.Recipes

/-!
# Template construction and witness scope

Blueprint: `syntax/language/formula-compilation.md`, `syntax/language/builder-soundness.md`,
`syntax/language/builder-well-formed.md`.

* `ZInQKernel.Syntax.Builder.Construction`: constructions allocate from one counter
  (`Build.Allocates`), and the template of an allocating construction has the parameter and
  variable counts, the polynomial `κ(⋀(E_1, …, E_r, φ))` and the constant-variable ranges of the
  formula-compilation article (`Build.template_construction`).
* `ZInQKernel.Syntax.Builder.Scope`: the witness scope of an existential polynomial
  (`ExPoly.WitnessScope`), its consequences (well-formedness, relations through private blocks),
  and the witness scope of every template of the library (`templateLibrary_witnessScope`).
* `ZInQKernel.Syntax.Builder.Recipes`: the witness scope of composition recipes and of the
  model-evaluation translation, the block disjointness of the five composition recipes of the
  specification, and the witness scope of every recipe of the specification
  (`specLib_witnessScope`, `specLib_precisionCircuit_witnessScope`).
-/
