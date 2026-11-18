# Tate polarization and S16

**Proved.** `HodgeFil1.tatePolarizationSymmetry_proof` gives a nondegenerate cyclotomic pairing on the rational Tate module of every abelian variety in the local comparison row. The construction uses the native finite quotient for a very ample bundle over the base field. Its descended family gives the torsion classes for the Weil formula; the resulting perfect, compatible finite pairings give the Tate module form. No Picard representability or Picard-zero properness input is used.

`HodgeFil1.scholzeH1AbVar_of_dR` recovers the full row in every dimension from the de Rham and filtration-range clauses and the existing T10 Tate duality. This proves the Fil¹ clause that supplies the surface Hodge numbers at L10996 on the comparison side. The manuscript gives those numbers without justification; no mathematical error was found there.

All four Lean modules compile. All 34 new theorems report only `propext`, `Classical.choice`, and `Quot.sound`. The transitive audit excludes both the removed Picard hypotheses and the old Fil¹ clause. `#discharges` matches the exact headline field and lists only the narrowed comparison and T10 as premises.

The dry run keeps **5 LEAF / 26 GLUE** on 31 H rows. The proposed narrower comparison is a consequence rated GLUE pending review. The comparison and T10 remain inputs; the fold is left to the integrator. See [the report](../docs/research/tate-polar-sym.md) and [verification artifacts](../scratch/tate-polar-sym/).
