# logp-transc results log

Base: fork main 5500325f + merge origin/wip/htmult-model (36bbcafa) = 5074f66b.

## Findings (no Lean)
- VERIFIED (search of .lake/packages/mathlib/Mathlib/RingTheory/DividedPowers/): Mathlib v4.35 has Basic, DPMorphism,
  Padic, RatAlgebra, SubDPIdeal; no divided-power envelope (no file mentions "envelope").
- VERIFIED (grep): no Frobenius on A_max/B_max in ZInQKernel/Contrib/OneProof (A_max is defined as a subring of B_dR^+,
  and phi does not preserve ker theta, so phi is not the restriction of a map of B_dR^+).
- VERIFIED (grep): B_dR^{G_F} = F is proved in tree (ZInQKernel/Contrib/OneProof/BdRInvariants.lean,
  bdRInvariantsPrinted_proof, dimension form); not imported here (heavy import chain via ZInQKernel.OneProof.H.TailS).
- The manuscript cites Brinon-Conrad only for Thm 5.2.1, Props 6.3.3, 6.3.8 (L10975, L10994, bibitem L11019-11022);
  L738-741 cites Berger 2002 for "de Rham => pst", L755-758 Pan Thm 1.0.4; neither mentions B_st's embedding.

## Lean
- build1: lake build ZInQKernel.Contrib.OneProof.PanBergerFontaine (needed: oleans of the merged files absent).
- build1: EXIT 0 (10669 jobs).
- LogPTranscendence.lean: VERIFIED compiles (`lake env lean`, both the scratch copy and
  ZInQKernel/Contrib/OneProof/LogPTranscendence.lean), no sorry, no warnings; 29 declarations, all
  [propext, Classical.choice, Quot.sound] (scratch/logp-transc/axioms.txt, from LogPTranscendenceAxioms.lean).
  Compile pitfalls: IsField.toField instance ops are not reducible-defeq to BdR's ring ops (NoZeroDivisors /
  IsSimpleRing synth fail); use IsDomain via isField.isDomain and explicit inverses from IsField.mul_inv_cancel.
  Sub on (↥B)[X] for a Subalgebra B times out in typeclass search: write P + C (-c) instead of P - C c.
- build2: lake build ZInQKernel.Contrib.OneProof.BdRInvariants EXIT 0; lake build ZInQKernel.Contrib.OneProof.LogPTranscendence OK.
- LogPTranscendenceBdR.lean: VERIFIED compiles (scratch copy and ZInQKernel/Contrib/OneProof/LogPTranscendenceBdR.lean),
  no sorry; 5 theorems, all [propext, Classical.choice, Quot.sound]. Result: LogPTildeTranscendental <->
  (forall p, log[p~] not in Frac(B_max)) (logPTildeTranscendental_iff_notInFrac), using the tree's B_dR^{G_Qp} = Q_p
  (bdr_invariant_eq_algebraMap, element form from BdRInv.bdRInvariantsPrinted_proof at F = Q_p).
- LogPTranscendence.lean §6 (units): VERIFIED compiles; new: sub_one_mem_ith, logOne, logOne_congr, logOne_teich,
  logOne_mem_amax (log z in A_max for every z in A_inf with theta z = 1), logOne_mul, bdrAct_logOne, theta_unit,
  bdrAct_logUnit, rootsOf*, flatOf, untilt_flatOf (sharp is onto O_Cp), coeff_pow_pow, isUnit_of_isUnit_untilt,
  exists_uSigma_unit, unit_log_mem_amax (for every v in Z_p^x: log([nu]/v) in A_max with sigma-shift log[u_sigma]).
  Whole file: 48 declarations, all standard axioms; BdR file: 5, all standard (scratch/logp-transc/axioms.txt, 53 lines).
