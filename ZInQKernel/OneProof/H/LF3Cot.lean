import ZInQKernel.OneProof.H.LF2Stalks
import ZInQKernel.Contrib.HeightBC.StalkTensor
import ZInQKernel.Contrib.HeightBC.CotangentBC

/-! leaf-fold3: scratch/infra-stalks/CotangentBaseChange.lean lines 523-end verbatim (its lines 1-522 are module LF2Stalks); `#print` lines dropped. -/

universe u



/-! # The stalk of a fibre product is a localization of the tensor product of stalks

For `z ∈ X ×_S Y` over `x ∈ X`, `y ∈ Y`, `s ∈ S`, the ring map
`Φ : 𝒪_{X,x} ⊗_{𝒪_{S,s}} 𝒪_{Y,y} → 𝒪_{X ×_S Y, z}` is a localization at the prime `Φ⁻¹(𝔪_z)`:
every element of `𝒪_z` is `Φ a / Φ u` with `Φ u` a unit, and `Φ t = 0` implies `u t = 0` for some
`u` with `Φ u` a unit (`pullback_stalk_tensor_isLocalization`; Stacks 01JT, EGA I 3.6.5,
UNVERIFIED locators). -/

namespace AlgebraicGeometry

open CategoryTheory Limits TensorProduct

end AlgebraicGeometry




/-! # Cotangent space of a base change by a field extension (bijective)

For `z ∈ X ×_S Y` with `𝒪_{S,s}` and `𝒪_{Y,y}` fields (e.g. `S = Spec L`, `Y = Spec L'`) and `x`
rational over `s`, the map `𝒪_y ⊗_{𝒪_s} 𝔪_x/𝔪_x² → 𝔪_z/𝔪_z²`, `c ⊗ da ↦ c · d(fst^♯ a)`, is
injective (`cotangent_baseChange_injective`); it is onto by `cotangent_span_pullback`. The proof
combines Mathlib's `Ideal.tensorCotangentHom` (flat base change of `I/I²`) with the localization
`pullback_stalk_tensor_isLocalization` and an algebraic lemma on cotangent spaces of localizations
at a maximal ideal (`mem_sq_of_map_mem_sq`). -/

namespace AlgebraicGeometry

open CategoryTheory Limits TensorProduct

end AlgebraicGeometry


