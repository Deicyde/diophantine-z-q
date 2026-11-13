
/-!
# frob-trace: composite with g14-trace's `g12Spec_g14_of_linked`

In one environment with verbatim copies of g14-trace's `G14Trace.lean` parts
(`part_c9_src`, `part_e1_src`, `part_new`, `part_g14`): G7's data, the leaves I3.M0
(`TateModuleFree`) and T7 (`CharPolyIndepOfEll`), the glue `AlgFrobRed` and g0-mod-newform's
`DirichletOfFinite`, and G8-G12 at `ℓ = 5, 3` as hypotheses (in the shapes of g0-mod-galois'
`g8_g12`, `g8_g11`) give G8's `r₅`, `r₃` and data `D` with `G12Spec D ∧ G14TraceCompat D`.
The two copies of `G7Out`, `Vb`, `resQ`, `tate` and `FrobTraceLink` (g0-mod-field's
`GaloisCopy`, `G14Bridge` vs g0-mod-newform's / g14-trace's) are identified by unfolding.
-/

noncomputable section

namespace FrobTraceCompose

open ZInQ LeafQM.AV GlueDescent G0ModField

theorem g12Spec_g14_of_G7Data (hT : PkgI3.TateModuleFree) (hR : FrobTrace.AlgFrobRed)
    (hDF : G0ModNewform.DirichletOfFinite) (hM : PkgI3.CharPolyIndepOfEll)
    (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] [NumberField L']
    (hLL' : L ≤ L')
    (hD : G7Data u P L A ε N χ β L' hLL')
    (hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2)
    (hrk : Module.finrank ℤ
      (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4)
    (hG5 : ∀ (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0ModNewform.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c e : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a b : PkgI4.GQ → PadicAlgCl 5)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0ModNewform.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5)),
      G14Trace.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm c e a b uu →
      ∃ r5 : PkgI4.GaloisRep 5 2,
        G0ModNewform.GalG8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5
          (GlueDescent.rho Tm a b) r5 ∧ G0ModNewform.GalG12Out r5)
    (hG3 : ∀ (Tm : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0ModNewform.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c e : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3) (a b : PkgI4.GQ → PadicAlgCl 3)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0ModNewform.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G14Trace.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm c e a b uu →
      ∃ r3 : PkgI4.GaloisRep 3 2,
        G0ModNewform.GalG8Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3
          (GlueDescent.rho Tm a b) r3) :
    ∃ (r5 : PkgI4.GaloisRep 5 2) (r3 : PkgI4.GaloisRep 3 2)
      (D : G0ModNewform.ModData L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))),
      D.r5 = r5 ∧ D.r3 = r3 ∧ G0ModNewform.G12Spec D ∧ G0ModNewform.G14TraceCompat D := by
  obtain ⟨aQ, βQ, j5, j3, Tm5, c5, ε5, u5, Tm3, c3, ε3, u3, h5, h3, hF, -⟩ :=
    FrobTrace.tateBridge35_of_algFrobRed hT hR u P L A ε N χ β L' hLL' hD hdim hrk
  obtain ⟨r5, r3, D, -, -, hD5, hD3, hs, hc⟩ :=
    G14Trace.g12Spec_g14_of_linked hDF hM (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))
      aQ βQ j5 j3 Tm5 c5 ε5 u5 Tm3 c3 ε3 u3 h5 h3 hF (hG5 _ _ _ _ _ _) (hG3 _ _ _ _ _ _)
  exact ⟨r5, r3, D, hD5, hD3, hs, hc⟩

end FrobTraceCompose

end

#print axioms FrobTraceCompose.g12Spec_g14_of_G7Data
