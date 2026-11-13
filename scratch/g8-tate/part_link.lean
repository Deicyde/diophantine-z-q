/-! # g8-tate, part 3: g8-object's `LinkedTateObjS` reduced to `TateBridgeOnL`

`TateBridgeOnL` is the text of g8-object's `LinkedTateObjS` with its two `LocalDataS` conjuncts
deleted: g14-trace's `TateBridge35` data and `OnL` for `Tm₅`, `Tm₃`, for G7 data with `[L:ℚ] ≤ D`.
`linkedTateObjS_of_onL` proves `LinkedTateObjS` from it, the leaves R6, I2-Tors and `UnramRoots 2 5`
(part 2 supplies `LocalDataS`; `dim A = 2` comes from `G7Out`'s `dim A_{L'} = 2` and the kernel's
`PkgI3.AbVar.dim_baseChange`). With T7, g8-object's `linkedTateDataD_of_S` then gives
`LinkedTateDataD`. -/

noncomputable section

namespace G8Tate

open PkgI4 (GQ GQp GaloisRep decomp)
open LadicCond G0ModField G8Object
open CategoryTheory AlgebraicGeometry
open ZInQ LeafQM.AV GlueDescent.B2

/-- **GLUE: the Tate functor on G7's descent datum at `ℓ = 5, 3`, linked, with its `G_L`-clause**
(N5 L632-716, L781-786; g14-trace's `TateBridge35` + g8-object's `OnL`). The text of g8-object's
`LinkedTateObjS` without its `LocalDataS` conjuncts, which part 2 proves. For G7 data with
`[L:ℚ] ≤ D`: one pair `aQ, βQ : G_ℚ → ℚ̄`, embeddings `j₅, j₃`, operators `Tm_ℓ` on
`ℚ̄_ℓ ⊗ V_ℓ(A_{L'})` with `G7Out` for `j_ℓ ∘ aQ`, `j_ℓ ∘ βQ`, `FrobTraceLink`, `ιC ∘ βQ = β`, and
on `G_L` the operators are the Tate action of `A/L` transported by isomorphisms `ψ_ℓ`. -/
def TateBridgeOnL : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    Module.finrank ℚ L ≤ ZInQ.heightD →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (aQ βQ : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (ψ₅ : G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 ≃ₗ[PadicAlgCl 5]
        G0Galois.Vb A 5)
      (ψ₃ : G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 ≃ₗ[PadicAlgCl 3]
        G0Galois.Vb A 3),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (aQ g)) (fun g => j5 (βQ g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (aQ g)) (fun g => j3 (βQ g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      (∃ ιC : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ g, ιC (βQ g) = (β g : ℂ)) ∧
      OnL L A Tm₅ (fun g => j5 (aQ g)) ψ₅ ∧ OnL L A Tm₃ (fun g => j3 (aQ g)) ψ₃


/-- **`LinkedTateObjS` from `TateBridgeOnL` and the leaves (proved).** -/
theorem linkedTateObjS_of_onL (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU : G15Ram.UnramRoots 2 5) (hB : TateBridgeOnL) :
    LinkedTateObjS := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata hLD
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, ψ₅, ψ₃, h75, h73, hF, hι, hOn5,
    hOn3⟩ := hB Y Φ π u P hctx L A ε N χ β L' hLL' hdata hLD
  have hdim : A.dim = 2 := by
    rw [← @PkgI3.AbVar.dim_baseChange L _ A L' _ (incAlg hLL')]
    exact h75.1
  refine ⟨aQ, βQ, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, ψ₅, ψ₃, h75, h73, hF, hι, hOn5, hOn3,
    fun p hp hp5 => ?_, ?_⟩
  · exact @localDataS_of_g7Data hR6 hTors p ⟨hp⟩ 5 _
      (fun h2 => by subst h2; exact hU) hp5 u P L _ _ A ε N _ χ β L' hLL' hdata hLD hdim
  · exact localDataS_of_g7Data hR6 hTors (fun h2 => absurd h2 (by norm_num)) (by norm_num)
      hdata hLD hdim

/-- **g0-assemble's `LinkedTateData`, restricted to `[L:ℚ] ≤ D` (g8-object's `LinkedTateDataD`),
from T7, R6, I2-Tors, `UnramRoots 2 5` and `TateBridgeOnL` (proved).** -/
theorem linkedTateDataD_of_onL (hM : PkgI3.CharPolyIndepOfEll) (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU : G15Ram.UnramRoots 2 5) (hB : TateBridgeOnL) :
    LinkedTateDataD :=
  linkedTateDataD_of_S hM (linkedTateObjS_of_onL hR6 hTors hU hB)

end G8Tate

end

#print axioms G8Tate.linkedTateObjS_of_onL
#print axioms G8Tate.linkedTateDataD_of_onL
