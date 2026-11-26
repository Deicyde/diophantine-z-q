import ZInQKernel.Contrib.OneProof.RC.ClassicalEulerFactors.Receiver
import ZInQKernel.Contrib.OneProof.RC.ClassicalEulerFactors.Parity
import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Descent

/-! # The combined source boundary for the existing restricted converse -/

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Manuscript.ForwardRankLiterature ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.RC53Assist.BCDTPrint
open ZInQ.Contrib.RC53Assist.NewformGlueG0
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
open ZInQ.Contrib.RC53Assist.G0Prints
open ZInQ.Contrib.RC53Assist.TateCurve

/-- Apply the exact Theorem 5.3 receiver with the BCDT and parity adapters
proved in Lean. Both local-factor fields are constructed from the
same bad-prime dictionary. The actual Shimura geometric reading and
all remaining manuscript data and hypotheses stay explicit. -/
theorem restrictedConverseGenuine_of_classicalLocalFactors_and_annals419
    (hM : ForwardRankAtMostOne) (hB : BCDTThmAPrinted)
    (hD : PrintsAnalytic.DokchitserAnnalsThm419AtTwo) (hCst : CST.CSTThm11Split)
    (L : RCLeavesWithoutEulerFactors) (hGeom : Shimura1973RationalGeometricReading)
    (hC : Carayol1986CorollaireRational) (hF : Faltings1983Korollar2iiiivPrint)
    (hT : SilvermanC141TateUniformizationLiteral) (hS : SGA7IX38LocalEllipticCriterion) :
    RestrictedConverseGenuine := by
  obtain ⟨hC', hF'⟩ := g0_fields_of_classical hGeom hC hF hT
    (grothendieckSemistableReductionPrint_of_sga7 hS)
  have hB' := bcdtThmA_of_printed hB
  have hMod := PrintsAnalytic.modularNewform_of_printed hB'
    (Shimura1973ConjugateEigenforms.of_embedded L.shimuraEmbeddings)
    li1975StrongMultiplicityOneWeightTwo_proved hC' hF'
  exact restrictedConverseGenuine_of_miller hM hB'
    (PrintsAnalytic.dokchitserThm18_of_annals419 hD hMod) hCst (L.complete hC' hF')

end ZInQ.Manuscript.RC.Wiring
