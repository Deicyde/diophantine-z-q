import Mathlib
import ZInQKernel.Contrib.HeightBC.StalkPullback
import ZInQKernel.Contrib.HeightBC.LocalStructure

/-! leaf-fold2: scratch/infra-stalks/HeightBCGlue.lean lines 3-850 (its Part 1: general stalk lemmas), verbatim; root namespace. -/

/-! # infra-stalks: height-bc glue `CotangentSpanBC` and `UniformizationLiftAnalytic` proved
Part 1: general lemmas (`StalkPullback.lean`, `local_structure.lean.part`). Part 2: verbatim
`scratch/height-bc/Final.lean` (after its import). Part 3: `bc_proof.lean.part`,
`ula_proof.lean.part`, `hbc_final.lean.part`. -/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-! ### Maximal ideals and residue fields -/

section MaximalIdeal

variable {T X Y S : Scheme.{u}} {p : T ⟶ X} {q : T ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}

end MaximalIdeal

/-! ### Sections and points with field stalks -/

/-! ### Stalk maps between given points -/

end AlgebraicGeometry



/-! # Local structure of a fibre product at points with values in a field

For `f : X ⟶ Spec R`, `g : Y ⟶ Spec R` and points `p₁ : Spec F ⟶ X`, `p₂ : Spec F ⟶ Y` over
`Spec R` (`F` a field), a regular function on an open of `X ×_R Y` (pulled back along any
`W : X ×_R Y ⟶ P`) is, near `(p₁, p₂)`, a quotient of sums of products of regular functions on
opens `V₁ ∋ p₁`, `V₂ ∋ p₂`, uniformly for all `F`-points of `V₁ × V₂` where the denominator does
not vanish (`exists_localStructure_pullback`). Proof: affine charts `Spec A → X`, `Spec B → Y`,
the open chart `Spec (A ⊗[R] B) → X ×_R Y`, a basic open `D(h)` around the point inside the open,
`s = a / h^n` on `D(h)`, and pure tensors evaluate to products. -/

namespace AlgebraicGeometry

open CategoryTheory Limits TensorProduct

end AlgebraicGeometry
