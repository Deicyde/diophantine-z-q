import ZInQKernel.Contrib.OneProof.RayClassShimura

set_option linter.all false

noncomputable section

namespace DCY3Used

open LeafQM ShimuraCFT RayClassCFT

/-! ## The mod-3 table: `𝒪¹ ∪ 𝒪¹·(1+i+j)` covers `(𝒪/3𝒪)^×` -/

/-- Coordinates (basis `1, i, (1+j)/2, (i+k)/2`) of the conjugate (`star_ofInt`). -/
def conjC (m : Fin 4 → ℤ) : Fin 4 → ℤ := ![m 0 + m 2, -m 1, -m 2, -m 3]

/-- 36 elements of `𝒪` of reduced norm 1, one in each class of `{x ∈ (𝒪/3𝒪)^× : nrd x = 1}`. -/
def L36 : List (Fin 4 → ℤ) :=
  [![0, 0, 1, 0], ![1, 0, 0, 0], ![-1, 0, 0, 0], ![0, 0, -1, 0], ![-1, 0, 1, 0], ![1, 0, -1, 0],
   ![1, -1, 1, 0], ![1, 0, 1, -1], ![1, 0, 1, 1], ![1, 1, 1, 0], ![-1, -1, -1, 0], ![-1, 0, -1, -1],
   ![-1, 0, -1, 1], ![-1, 1, -1, 0], ![1, -1, 1, 1], ![1, 1, 1, -1], ![-1, -1, -1, 1], ![-1, 1, -1, -1],
   ![-3, 2, 0, 0], ![-3, 0, 0, 2], ![-3, 0, 0, -2], ![-3, -2, 0, 0], ![-2, 1, -1, 1], ![-2, -1, -1, -1],
   ![-1, 1, -2, 1], ![-1, -1, -2, -1], ![-3, 1, 1, 1], ![3, 1, -1, 1], ![-3, -1, 1, -1], ![3, -1, -1, -1],
   ![1, 1, -3, 1], ![1, -1, -3, -1], ![-1, 1, 3, 1], ![-1, -1, 3, -1], ![-3, 2, 0, -2], ![-3, -2, 0, 2]]

theorem L36_norm : ∀ γ ∈ L36, ShimuraGlue.N4 γ = 1 := by decide

/-- Reduction mod 3 of a coordinate vector. -/
def red3 (m : Fin 4 → ℤ) : Fin 4 → ZMod 3 := fun i => (m i : ZMod 3)

set_option maxRecDepth 100000 in
theorem table3 : ∀ a b c d : ZMod 3, ShimuraGlue.N4 ![a, b, c, d] ≠ 0 →
    ∃ γ ∈ L36, ShimuraGlue.mulCoordR (red3 (conjC γ)) ![a, b, c, d] = ![1, 0, 0, 0] ∨
      ShimuraGlue.mulCoordR (red3 (conjC γ)) ![a, b, c, d] = ![0, 1, 2, 0] := by
  decide

end DCY3Used
