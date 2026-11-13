
/-- **`TateBridgeK` from the leaf I3.M0 alone (proved)**: g0-mod-field's `TateBridge` with the
kernel-field clause `KerWild L' β' L` in its output (lg-kerwild's correction of local-glue finding
G8), by unram-tate's construction (`tatePoints`, `endBaseChange`, `tateCont_of_tateModuleFree`,
`resQEmbedding`) and `scalarTransferK`. -/
theorem tateBridgeK_of_tateModuleFree (hT : PkgI3.TateModuleFree) : LGKerWild.TateBridgeK :=
  tateBridgeK_of_piecesK tatePoints endBaseChange scalarTransferK
    (tateCont_of_tateModuleFree hT) resQEmbedding

end UnramTate

/-- **`TateBridge35K` from I3.M0 and frob-trace's `AlgFrobRed` (proved)**: frob-trace's
`tateBridge35_of_algFrobRed` composed with `tateBridge35K_of_35`. -/
theorem LGKerWild.tateBridge35K_of_algFrobRed (hT : PkgI3.TateModuleFree)
    (hR : FrobTrace.AlgFrobRed) : LGKerWild.TateBridge35K :=
  LGKerWild.tateBridge35K_of_35 (FrobTrace.tateBridge35_of_algFrobRed hT hR)

end LGTateBridgeKSec

#print axioms UnramTate.scalarTransferK
#print axioms UnramTate.tateBridgeK_of_piecesK
#print axioms UnramTate.tateBridgeK_of_tateModuleFree
#print axioms LGKerWild.tateBridge35K_of_algFrobRed
