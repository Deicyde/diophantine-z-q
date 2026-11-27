import ZInQKernel.Contrib.OneProof.DeligneY3Bridges.Statement
import ZInQKernel.Contrib.OneProof.Y3Lattice412.Lattice

/-! # A5. The convention check: `𝒪̂ g⁻¹ = k⁻¹(V̂_ℤ)`

In the bridges' notation (`DeligneY3Bridges.PEL`): `G(𝔸_f)` is `GAf`, `toGAf : (B ⊗ 𝔸_f)^× ≃* G(𝔸_f)` is
`g ↦ (x ↦ x g⁻¹)`, `V̂_ℤ = VZhat = 𝒪̂`. The kernel writes points as `B^× \ ℍ^± × (B ⊗ 𝔸_f)^× / K₃`;
Deligne's 1.8 writes `K \ X × G(𝔸^f) / G(ℚ)`, and `PEL.dcRelDel_iff_PM` matches Deligne's class of
`toGAf g` with the kernel's class of `g⁻¹`. So the kernel's point `[h, g]` is Deligne's point with
group element `k = toGAf g⁻¹` (`x ↦ x g`), and Deligne's lattice `k⁻¹(V̂_ℤ)` (4.12, `T̂(B) = k⁻¹(V̂_ℤ)`)
is `𝒪̂ g⁻¹`. Its rational points are `latticeAt g` (`latticeAt_eq_deligne`). -/

noncomputable section

namespace Y3Lattice412

open ShimuraCFT DeligneY3Bridges.PEL

/-- The element of `G(𝔸_f)` that Deligne's 1.8 attaches to the kernel's `g`
(`PEL.dcRelDel_iff_PM`: Deligne's `toGAf g` is the kernel's `g⁻¹`). -/
def delElt (g : BAQˣ) : GAf := toGAf g⁻¹

/-- `k⁻¹(V̂_ℤ)` for `k = delElt g`. -/
def delLattice (g : BAQˣ) : Set BAQ := DeligneY3Bridges.app (delElt g)⁻¹ '' VZhat

/-- `k⁻¹(V̂_ℤ) = 𝒪̂ g⁻¹`. -/
theorem delLattice_eq (g : BAQˣ) :
    delLattice g = (fun v => v * ((g⁻¹ : BAQˣ) : BAQ)) '' OhatQ := by
  unfold delLattice delElt
  rw [← map_inv, inv_inv]
  rfl

/-- **A5. `L_g = B ∩ k⁻¹(V̂_ℤ)`** with `k` Deligne's element of `G(𝔸_f)` for the kernel's `g`
(through `toGAf` and the `g ↦ g⁻¹` of `PEL.dcRelDel_iff_PM`). -/
theorem latticeAt_eq_deligne (g : BAQˣ) (b : LeafQM.B) :
    b ∈ latticeAt g ↔ bEmb b ∈ delLattice g := by
  rw [delLattice_eq, mem_latticeAt]
  constructor
  · intro h
    refine ⟨bEmb b * (g : BAQ), h, ?_⟩
    show bEmb b * (g : BAQ) * ((g⁻¹ : BAQˣ) : BAQ) = bEmb b
    rw [mul_assoc, Units.mul_inv, mul_one]
  · rintro ⟨v, hv, he⟩
    change v * ((g⁻¹ : BAQˣ) : BAQ) = bEmb b at he
    rw [← he, mul_assoc, Units.inv_mul, mul_one]
    exact hv

/-- The match of `delElt` with Deligne's double cosets (`PEL.dcRelDel_iff_PM` restated). -/
theorem delElt_dcRel (z z' : Y3Hodge.HPM) (g g' : BAQˣ) :
    DCRelDel z (delElt g) z' (delElt g') ↔ Y3Hodge.DCRelPM z' g' z g := by
  rw [delElt, delElt, dcRelDel_iff_PM, inv_inv, inv_inv]

end Y3Lattice412

end
