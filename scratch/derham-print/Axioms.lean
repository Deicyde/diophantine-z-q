import ZInQKernel.Contrib.OneProof.DeRhamPrint

#print axioms DeRhamPrint.deRhamH1AbVarT_of_leaves
#print axioms DeRhamPrint.isDeRhamOver_of_leaves
#print axioms DeRhamPrint.TDict.bdREquivAwayT
#print axioms DeRhamPrint.TDict.tt_eq_varpi_mul_unit
#print axioms DeRhamPrint.TDict.ker_theta_eq_omega
#print axioms DeRhamPrint.TDict.ext_of_extends
#print axioms DeRhamPrint.TDict.transport_extends
#print axioms DeRhamPrint.TDict.logPlus_unique
#print axioms DeRhamPrint.TDict.rootSystem

/-- The two leaves are exactly dict-galois's statements (`DeRhamDict.DeRhamVpAbVarT`, `DeRhamDict.BdRInvariantsOver`
on `origin/wip/dict-galois`), restated here; non-vacuity of the hypotheses of the dictionary: -/
example (p : ℕ) [Fact p.Prime] : Nonempty (DeRhamPrint.TDict.RootSystem p) := ⟨DeRhamPrint.TDict.rootSystem p⟩
