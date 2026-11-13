-- (leaf-fold2: copied from scratch/g0-assemble2/parts/z85_modelg3g6.lean; 0 HDec name-resolution edits)
/-! ## g0-assemble2: g0-assemble's `ModelG3G6` split

`ModelG3G6` (part 87) asks, on G7's model `A_{L'}`: `G6Out` (`End` a division ring, and
noncommutative) and `G3Out` at `ℓ = 5, 3`. The division-ring half is NoCM on the model; it follows
from g0-split's piece `FibreSimple` (which `GluePieces3` already supplies through FS5), because
G7's model is a `FibreOver` of the fibre context (G7Data's last clause `IsModelOver`). What remains
is split into two smaller glue Props. -/

noncomputable section

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry
open G0ModField

/-- **Glue: `End(A_{L'})` is noncommutative** on G7's model (g0-assemble2). Elementary given the QM
structure of `IsQMModel` (`ι(𝒪) ⊆ End(PK.A)`, base change `End(PK.A) → End(A_{L'})`, unram-tate's
`endBaseChange`, and `[24] ≠ 0`); not formalized. No NoCM content. -/
def ModelNoncomm : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∃ x y : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')), x * y ≠ y * x

/-- **Glue G3 on G7's model** (g0-assemble2; the G3 half of `ModelG3G6`): inertia at primes outside
`T(u)` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A_{L'})`, `ℓ = 5, 3` (good reduction of the QM model away from
`T`, `QML3.goodReduction`, with Néron–Ogg–Shafarevich R7a). -/
def ModelG3 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 (T u) ∧
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 (T u)

/-- **`ModelG3G6` from `FibreSimple`, `ModelNoncomm` and `ModelG3`** (g0-assemble2). The
`EndDivision` clause of G6 is `FibreSimple` at the `FibreOver` given by G7Data's `IsModelOver`. -/
theorem modelG3G6_of (hFS : G0Split.FibreSimple) (hNC : ModelNoncomm) (hG3 : ModelG3) :
    ModelG3G6 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨h1, h2, hu, y, hy, hπ⟩ := hctx
  have hdiv := hFS Y Φ π h1 h2 u hu ⟨L'⟩
    ((LeafAdopt.abVarEquiv L').symm (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')))
    ⟨algebraMap L' Qbar, y, P, hy, hπ, hD.2.2.2.2.2.2.2.2.2.2.2⟩
  rw [Equiv.apply_symm_apply] at hdiv
  obtain ⟨g5, g3⟩ := hG3 Y Φ π u P ⟨h1, h2, hu, y, hy, hπ⟩ L A ε N χ β L' hLL' hD
  exact ⟨⟨hdiv, hNC Y Φ π u P ⟨h1, h2, hu, y, hy, hπ⟩ L A ε N χ β L' hLL' hD⟩, g5, g3⟩

end HSyn.G0AssembleMod

end
