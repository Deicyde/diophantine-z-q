/-! # shimura-glue: the bundle with Deligne's `π₀` in printed form -/

namespace HDec.QMSplit.Moduli

/-- **shimura-split's bundle with both Deligne leaves in printed form** (`DelignePi0` at levels `𝒪̂^×`
and `K₃`); the other seven fields are those of `ShimuraSplitLeaves`. -/
structure ShimuraGlueLeaves : Prop where
  deligneX6P : ShimuraGlue.DeligneComponentsX6Printed
  geomConn : GeomConnOfAlgClosure
  t5 : PkgI2.TorsionStructure.{0}
  babaGranath : BabaGranathX6'
  reciprocity : ReciprocityCanonical
  gonzalezRotger : GonzalezRotgerX6
  gonzalezRotgerCount : ShimuraSplit.GonzalezRotgerCountX6
  deligneY3P : ShimuraGlue.DeligneComponentsY3Printed
  elkies : ElkiesConicX6

/-- `ShimuraSplitLeaves` from `ShimuraGlueLeaves`: the two Deligne fields are theorems
(`ShimuraGlue.deligneComponentsX6_of_printed`, `ShimuraGlue.deligneComponentsY3_of_printed`). -/
theorem shimuraSplitLeaves_of_glue (L : ShimuraGlueLeaves) : ShimuraSplitLeaves :=
  ⟨ShimuraGlue.deligneComponentsX6_of_printed L.deligneX6P, L.geomConn, L.t5, L.babaGranath,
    L.reciprocity, L.gonzalezRotger, L.gonzalezRotgerCount,
    ShimuraGlue.deligneComponentsY3_of_printed L.deligneY3P, L.elkies⟩

/-- **Rows `r1r2`, `r1rec`, `r5`, `r5count`, `y3Connected`, `x6ConicModel` from the printed-Deligne
bundle.** -/
theorem rows_of_shimuraGlueLeaves (L : ShimuraGlueLeaves) :
    LeafAdopt.R1R2fpRep ∧ LeafQM.AV.R1rec ∧ LeafQM.AV.R5fp ∧ LeafQM.AV.R5fpCount ∧
      TSHecke.Y3Connected ∧ X6Kummer.X6ConicModel :=
  rows_of_shimuraSplitLeaves (shimuraSplitLeaves_of_glue L)

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.shimuraSplitLeaves_of_glue
#print axioms HDec.QMSplit.Moduli.rows_of_shimuraGlueLeaves

example : HDec.QMSplit.Moduli.ShimuraGlueLeaves →
    HDec.LeafAdopt.R1R2fpRep ∧ _root_.LeafQM.AV.R1rec ∧ _root_.LeafQM.AV.R5fp ∧
      _root_.LeafQM.AV.R5fpCount ∧ HDec.TSHecke.Y3Connected ∧ HDec.X6Kummer.X6ConicModel :=
  HDec.QMSplit.Moduli.rows_of_shimuraGlueLeaves
