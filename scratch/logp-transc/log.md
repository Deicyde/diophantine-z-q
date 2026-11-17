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
