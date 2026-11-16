# sga1-etale results log

- Build tree: copied .lake/build and lean/.lake/build from ~/dzq-wt/pel-hodge (descends from dbf043a4);
  `lake build ZInQKernel.Contrib.OneProof.UniformizationTopology` OK (9052 jobs). VERIFIED
- Mathlib 4.35 has `RingHom.IsStandardSmooth.exists_etale_mvPolynomial` (RingTheory/RingHom/StandardSmooth.lean:257):
  standard smooth f ⇒ ∃ n g, g.comp C = f ∧ g.Etale (g : R[X_1..X_n] → S). So "standard smooth ⇒ étale over the
  polynomial ring in the free variables" is in the pin. VERIFIED (read)
- A.lean (compiled, no errors): `eval₂Hom_res`, `etale_res` (étale coordinates restrict to basic opens),
  `exists_etale_chart` (Smooth X.hom ⇒ every point has an affine U and f : Fin n → Γ(U) with
  eval₂Hom (algC X U) f étale), `exists_cPt_of_mem` (nonempty open of loc. finite type ℂ-scheme has a ℂ-point). VERIFIED
- B.lean (compiled): leaf `SGA1_XII_3_1_Etale`; `regFun_local`, `chart_rep`, `chart_rep_pi`,
  `eq_of_local_inverse` (fderiv of mutually inverse maps ⇒ n = m). VERIFIED
- C.lean (compiled): `dim_eq`, `EChart`, `exists_echart` (irreducible ⇒ one n), `chartedSpaceOf`, `isManifold_of`. VERIFIED
- D.lean (compiled): `contMDiffOn_xevalAt`, `chartDiffeo`, `smoothComplexManifoldAn_of_etale`. VERIFIED
- E.lean (compiled): `ConnectedPreconnectedAn` (PreconnectedSpace), `connectedConnectedAn_of_preconnected` (Nonempty
  from `exists_cPt_of_mem`, for every proper irreducible X, not only abelian varieties), `uniformizationLeafAll_of_etale`.
  #print axioms: all [propext, Classical.choice, Quot.sound]. VERIFIED
- ZInQKernel/Contrib/OneProof/SmoothComplexManifoldEtale.lean (25.9 KB) = E.lean minus #print + docstring;
  `lake build ZInQKernel.Contrib.OneProof.SmoothComplexManifoldEtale` OK (9053 jobs). VERIFIED
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` OK (12994 jobs); DischargesCheck.lean output in
  discharges.txt: `DISCHARGES [OpenTextbookLeaves11.uniformizationLeafAll] by SGA1Etale.uniformizationLeafAll_of_etale
  still assumes: [UnifPrinted.MumfordComplexTorus, SGA1Etale.SGA1_XII_3_1_Etale, UnifTopology.ProperCompactAn,
  SGA1Etale.ConnectedPreconnectedAn]`, axioms standard; "#discharges: 63 open hypotheses, 1916 theorems checked,
  11 discharge one". VERIFIED
- autofold.json `--dry-run`: exit 0, "strict count: 46/10 on 56 -> 49/10 on 59; strictest 45/11 -> 48/11" (field still
  LEAF in this base's kinds.tsv). FoldDryRun.lean (dry-run output minus line 1) compiles;
  `HDec.HSyn.sixContactMin_of_open30` axioms [propext, Classical.choice, Quot.sound]. VERIFIED
