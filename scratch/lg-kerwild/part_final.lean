
/-! ## lg-kerwild §6: `LocalGlue` on the data of `TateBridgeK`, every coefficient prime `ℓ` -/

section LGFinalSec

open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q G0ModField

namespace LGKerWild

/-- **`LocalGlue` from `G7Out` on `A_{L'}`, `KerWild` and `G7Clauses` (proved).** For a model
`A/L` with `L ≤ L'` finite Galois, `G7Out` at `ℓ` for `A_{L'}` (base change along `incAlg`, as in
`TateBridge`), the kernel-field clause and G7's clauses: `LocalGlue` at every `p ≠ ℓ`, from R6,
I2-Tors and `UnramRoots`. `DescentPts` is discharged by `descentPts_of_g7`. -/
theorem localGlue_of_kerWild (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hU : G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) {L L' : IF} [FiniteDimensional ℚ L]
    [IsGalois ℚ L] [FiniteDimensional ℚ L'] (hLL' : L ≤ L') (A : PkgI3.AbVar L)
    {Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    {c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ} {a β' : PkgI4.GQ → PadicAlgCl ℓ}
    {uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)}
    (h7 : @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu)
    (hK : @G15Ram.KerWild ℓ _ L' _ (numberField_of_fd L') β' L)
    (hCl : G15Ram.G7Clauses β' ε' L) :
    @G15Ram.LocalGlue p _ ℓ _ _ _ _ Tm a β' L := by
  haveI : NumberField L' := numberField_of_fd L'
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 := h7.1
  exact G15Ram.localGlue_of_unramRoots hR6 hTors hU hpℓ h7 hCl hK
    (fun _ => descentPts_of_g7 hLL' A hdim)

/-- **`TateBridgeK`'s data satisfy `LocalGlue` given G7's clauses (proved).** For G7's data,
`dim A_{L'} = 2`, `rank End(A_{L'}) = 4` and every coefficient prime `ℓ`, there are operator data
with `G7Out` at `ℓ` such that `G7Clauses β' ε' L` gives `LocalGlue p Tm a β' L` at every `p ≠ ℓ`,
from R6, I2-Tors and `UnramRoots`. No `KerWild` or `DescentPts` hypothesis. -/
theorem exists_localGlue_of_tateBridgeK (hB : TateBridgeK) (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ → G15Ram.G7Clauses β' ε' L →
        @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β' L := by
  obtain ⟨Tm, c, ε', a, β', uu, h7, hK⟩ := hB u P L A ε N χ β L' hLL' hD hdim hrk ℓ
  refine ⟨Tm, c, ε', a, β', uu, h7, fun p hp hpℓ hCl => ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  exact localGlue_of_kerWild hR6 hTors (hU p ℓ) hpℓ hLL' A h7 hK hCl

/-- **The same from the leaf I3.M0 (proved)**: `TateBridgeK` is `tateBridgeK_of_tateModuleFree`. -/
theorem exists_localGlue_of_tateModuleFree (hT : PkgI3.TateModuleFree)
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    (hU : ∀ (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime], G15Ram.UnramRoots p ℓ)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu ∧
      ∀ (p : ℕ) (hp : p.Prime), p ≠ ℓ → G15Ram.G7Clauses β' ε' L →
        @G15Ram.LocalGlue p ⟨hp⟩ ℓ _ _ _ _ Tm a β' L :=
  exists_localGlue_of_tateBridgeK (UnramTate.tateBridgeK_of_tateModuleFree hT) hR6 hTors hU
    u P L A ε N χ β L' hLL' hD hdim hrk ℓ

end LGKerWild

end LGFinalSec

#print axioms LGKerWild.localGlue_of_kerWild
#print axioms LGKerWild.exists_localGlue_of_tateBridgeK
#print axioms LGKerWild.exists_localGlue_of_tateModuleFree
