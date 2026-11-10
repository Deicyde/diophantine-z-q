# cr5b-sec3 log
- Start: read tyz-5b §§1-4, cr5b-lean log, Rank5b files. Plan in plan.md (forest/permanent route,
  det M5b reduced by a rank-one lemma to a bordered P = [[D_y,Lᵀ],[L,D_z]]).
- Defs.lean (lapl, kappa, redeiG, genusSum5b, gBit, T5b), Perm.lean (pmin, det bridge, row ops), Forest.lean (Lemma 2.1 pmin_lapl_eq_forests): all compile, no sorry.
- Redei.lean: kappa_eq_forests, Lemma 2.2(1)-(3) (kappa_add_kappa via row-sum trick), (2.1),(2.2). Compiles.
- DetAlg.lean (matrix det lemma w/o invertibility, border, quad form), DetForest.lean (det P(c,d) forest sum via pmin block decomposition + transversal sum): compile.
- M5bForest.lean: det_M1G, det_M5bG, det_M5bG_forest (Prop 3.4 forest form). Compiles.
- Glue.lean: allF, ofPartFun, gluing prod_sum_allF. Compiles.
- Count.lean: card_fpfi (pairings parity), card_setA (compatible partitions ↔ pairings). Compiles.
- Genus.lean: block weights w7/w3/w1 as forest sums (w1 via Lemma 2.2(3)); marked form of T5b. Compiles.
- Thm36.lean: genusSum5b_eq_forest, det_M5bG_eq_genusSum5b (Theorem 3.6 for bits, reciprocity + y(V)=0). Compiles, no sorry.
- TYZ.lean: T5b_eq_genusSum5b, det_M5b_eq_T5b (Thm 3.6), CertifiedRankTYZ, certifiedRank5b_of_certifiedRankTYZ; root Rank5bSec3 with variant main theorem. #print axioms clean.
- Props.lean: card_setAgen, sum_prod_uniform, Prop 3.3 (det_M1G_eq_class3, det_M1G_eq_zero), Prop 3.5 (sum_class1_eq_sum_class3). Compiles.
- Prop34.lean: Prop 3.4 partition form det_M5bG_eq_class73. Compiles.
