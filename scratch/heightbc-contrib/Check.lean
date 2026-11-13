import ZInQKernel.MainLiterature
import ZInQKernel.Contrib.HeckeAll.Provider
import ZInQKernel.Contrib.GaussFE.Headline
import ZInQKernel.Contrib.PSide.APZero
import ZInQKernel.Contrib.PSide.BadPrimes
import ZInQKernel.Contrib.PSide.Coeff
import ZInQKernel.Contrib.PSide.Convergence
import ZInQKernel.Contrib.PSide.Hasse
import ZInQKernel.Contrib.PSide.Supersingular
import ZInQKernel.Contrib.PSide.TYZInputsIff
import ZInQKernel.Contrib.GZDecomp.Decomp
import ZInQKernel.Contrib.T14.Main
import ZInQKernel.Contrib.T28.Assemble
import ZInQKernel.Contrib.RLeaf.T36Torsion
import ZInQKernel.Contrib.RLeaf.T37GoodReduction
import ZInQKernel.Contrib.AbVarBC.Main
import ZInQKernel.Contrib.HeightBC.Main

/-! The two closed providers fed into the unchanged headline theorem: Theorem 1.1 from
`SixContactMin`, `TYZThm35ReadingA` and `GrossZagier` alone. -/

theorem contribCheck_headline (hH : ZInQ.SixContactMin) (hA : ZInQ.Literature.TYZThm35ReadingA)
    (hG : ZInQ.Literature.GrossZagier) : ZInQ.FrozenTarget :=
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_tyzThm35ReadingA_heckeContinuation_functionalEquation5_grossZagier
    hH hA ZInQ.Contrib.heckeContinuation ZInQ.Contrib.functionalEquation5 hG

#print axioms ZInQ.Contrib.functionalEquation5
#print axioms ZInQ.Contrib.heckeContinuation
#print axioms contribCheck_headline
#print axioms ZInQ.Contrib.GaussFE.frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagier
#print axioms ZInQ.Contrib.PSide.tyzInputs_iff_readingA
#print axioms ZInQ.Contrib.PSide.LSeriesSummable_cd
#print axioms ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves
#print axioms ZInQ.Contrib.T14.brauerHasse2C
#print axioms ZInQ.Contrib.T14.brauerReciprocity2C
#print axioms T28.igusaClebschSeparation_proved
#print axioms ZInQ.RLeaf.t36_torsionStructure
#print axioms ZInQ.RLeaf.T37.t37_goodReductionUnramified
#print axioms ZInQ.Contrib.AbVarBC.abVarBaseChange

/-! heightbc-contrib (scratch/heightbc-contrib/Check.lean = scratch/contrib-check/Check.lean plus the
import of `ZInQKernel.Contrib.HeightBC.Main` and the lines below): the closed height base-change
chain. -/

example : ZInQ.H5Neron.ModelHeightBaseChange := ZInQ.Contrib.HeightBC.modelHeightBaseChange
example : ZInQ.H5Neron.OpenSubgroupHeight := ZInQ.Contrib.HeightBC.openSubgroupHeight
example : ZInQ.DefFaltings.NeronModelMinimal := ZInQ.Contrib.HeightBC.neronModelMinimal
example : ZInQ.HeightBC.HodgeBCInjective := ZInQ.HeightBC.hodgeBCInjective
example : ZInQ.HeightBC.OmegaBaseChange := ZInQ.HeightBC.omegaBaseChange
example : ZInQ.HeightBC.OmegaLocalization := ZInQ.HeightBC.omegaLocalization
example : ZInQ.HeightBC.CotangentSpanBC := ZInQ.HeightBC.cotangentSpanBC
example : ZInQ.HeightBC.UniformizationLiftAnalytic := ZInQ.HeightBC.uniformizationLiftAnalytic
example : ZInQ.HeightBC.HodgeLineBaseChange := ZInQ.HeightBC.hodgeLineBaseChange
example : G0StableBC.StableHeightBaseChange := ZInQ.HeightBC.stableHeightBaseChange

#print axioms ZInQ.HeightBC.hodgeBCInjective
#print axioms ZInQ.HeightBC.omegaBaseChange
#print axioms ZInQ.HeightBC.omegaLocalization
#print axioms ZInQ.HeightBC.cotangentSpanBC
#print axioms ZInQ.HeightBC.uniformizationLiftAnalytic
#print axioms ZInQ.HeightBC.modelHeightBaseChange
#print axioms ZInQ.HeightBC.hodgeLineBaseChange
#print axioms ZInQ.HeightBC.stableHeightBaseChange
#print axioms ZInQ.HeightBC.stableFaltingsHeight_eq_neron_of_N1N2
#print axioms ZInQ.H5Glue.neronModelMinimal
#print axioms ZInQ.H5Glue.openSubgroupHeight
#print axioms ZInQ.Contrib.HeightBC.modelHeightBaseChange
#print axioms ZInQ.Contrib.HeightBC.openSubgroupHeight
#print axioms ZInQ.Contrib.HeightBC.neronModelMinimal
#print axioms ZInQ.Contrib.HeightBC.stableFaltingsHeight_eq_neron_of_N1N2
