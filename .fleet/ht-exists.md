# ht-exists (2026-11-15)

**Result.** The research field `eigenformHTNew` (Kato HT for newforms) is discharged, autofold-compatibly, by a
new leaf in the existence form in which the theorem is printed: `EigenformHTExists.KatoHTExists` (for each newform
f of weight k >= 2 there is a semisimple rho, geometric Frobenius trace a_p, with Hodge-Tate weights {0, k-1} at l;
Kato 2004 for V_{F_lambda}(f)). Report: docs/research/ht-exists.md.

**Compiles (VERIFIED, standard axioms).** `ZInQKernel/Contrib/OneProof/EigenformHTExists.lean` (imports ht-bypass's
`EigenformHTWeak`, not Main):
- `eigenformHTNew_of_katoHTExists : KatoHTExists -> TateTwistInvariants -> AxSenTate -> EigenformHTNew`
  (duality `HTDual` proved from Tate's two theorems; transport to every semisimple attached rho by the kernel's
  `attachedConj_proof` (Chebotarev + Brauer-Nesbitt) and `htConj_proof`);
- converse `katoHTExists_of_eigenformHTNew` over the LEAF fields dsThm965, dsThm966, tateTwistInvariants,
  axSenTate (the leaf is no stronger than the field), `katoHTExists_iff`;
- restricted leaf `KatoHTExists5Ge3` (l = 5, k >= 3, the only use per ht-bypass) -> `EigenformHTNew5Ge3`,
  converse, and `afterG7_of3Kato5` (AfterG7 via ht-bypass's afterG7_of3Weak).
- `#discharges`: `DISCHARGES [OpenResearchLeaves21.eigenformHTNew] by EigenformHTExists.eigenformHTNew_of_katoHTExists`,
  still assumes [KatoHTExists, TateTwistInvariants, AxSenTate]; 63 open, 1703 checked, 6 discharge one.
- autofold spec `scratch/ht-exists/autofold.json` (leaf `katoHTExists`, kind published, flag pending reading):
  dry run 46/10 -> 46/10 (neutral), generated `sixContactMin_of_open29` compiles.

**Rating.** Not printed form verbatim (existential over Kato's V_{F_lambda}(f), which Mathlib cannot define); a
consequence of the print, flagged pending reading. Neutral now; -1 strict GLUE once a reading confirms Kato 2004
sections 11.3-11.4 pp. 205-207 (filtration jumps 0, k-1), sections 6.3/8.3 pp. 161-162/181-182 (geometric Frobenius
trace a_p) and Ribet 1977/1985 (semisimplicity); (9.2.2) pp. 187-188 was read by the locator audit.

**Remains.** The reading; the fold itself (integrator); optional bypass fold to the l = 5, k >= 3 leaf (no count gain).
