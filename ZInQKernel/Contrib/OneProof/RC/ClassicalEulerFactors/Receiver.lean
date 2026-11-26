import ZInQKernel.Contrib.OneProof.RC.ClassicalEulerFactors.LocalFactors
import ZInQKernel.Contrib.OneProof.MillerForwardRank

/-! # Classical local factors in the exact Theorem 5.3 receiver

Keep the manuscript data and the quantifier order of `RCLeaves` unchanged.
Reconstruct the old Euler-factor fields from their sources before calling
the existing assembly; they are not retained as duplicate premises. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53 Filter Topology
open ZInQ.Manuscript.ForwardRankLiterature
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
open ZInQ.Contrib.RC53Assist.G0Prints
open ZInQ.Contrib.RC53Assist.TateCurve

attribute [local instance] Nat.fact_prime_two

/-- The original leaves other than the two Euler-factor interfaces
supplied at this receiver. -/
structure RCLeavesWithoutEulerFactors where
  hlPrint : PrintsAnalytic.HoffsteinLuoTheorem
  shimuraEmbeddings : Shimura1973EmbeddedEigenforms
  data : ∀ ℓ : ℕ, ℤ → WData ℓ
  pre : ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) → ∀ h : ℤ, IsGenusPartner ℓ h →
    PreLeaves ((data ℓ h).withHstar h)
  post : ∀ ℓ : ℕ, Adm ℓ → SelmerCorankOne (Ecurve ℓ) → ∀ h : ℤ, IsGenusPartner ℓ h →
    ∀ δ : ℤ, IsLeast (data ℓ h).depthSet δ → PostLeaves ((data ℓ h).withChoices h δ)

/-- Reconstruct exactly the existing structure, retaining every data field. -/
def RCLeavesWithoutEulerFactors.complete (L : RCLeavesWithoutEulerFactors)
    (hC : Carayol1986RationalNewformEulerFactors)
    (hF : Faltings1983EulerFactorRigidityQ) : RCLeaves where
  hlPrint := L.hlPrint
  shimuraEmbeddings := L.shimuraEmbeddings
  carayolEulerFactors := hC
  faltingsRigidity := hF
  data := L.data
  pre := L.pre
  post := L.post

/-- The original restricted converse with just the Faltings field reduced.
The separate associated-curve (Carayol) field is not taken as solved. -/
theorem restrictedConverseGenuine_of_faltings_classical
    (hM : ForwardRankAtMostOne) (hB : PoleS12.BCDTThmA) (hD : DokchitserThm18)
    (hCst : CST.CSTThm11Split) (L : RCLeavesWithoutEulerFactors)
    (hC : Carayol1986RationalNewformEulerFactors)
    (hF : Faltings1983Korollar2iiiivPrint) (hT : SilvermanC141TateUniformizationLiteral)
    (hS : SGA7IX38LocalEllipticCriterion) : RestrictedConverseGenuine :=
  restrictedConverseGenuine_of_miller hM hB hD hCst
    (L.complete hC (faltingsRigidity_of_classical hF hT
      (grothendieckSemistableReductionPrint_of_sga7 hS)))

/-- The joint cut. The geometric reading for Shimura's actual rational
quotient is not part of the cited Carayol statement and remains explicit. -/
theorem restrictedConverseGenuine_of_localFactors_classical
    (hM : ForwardRankAtMostOne) (hB : PoleS12.BCDTThmA) (hD : DokchitserThm18)
    (hCst : CST.CSTThm11Split) (L : RCLeavesWithoutEulerFactors)
    (hGeom : Shimura1973RationalGeometricReading) (hC : Carayol1986CorollaireRational)
    (hF : Faltings1983Korollar2iiiivPrint) (hT : SilvermanC141TateUniformizationLiteral)
    (hS : GrothendieckSemistableReductionPrint) : RestrictedConverseGenuine := by
  obtain ⟨hC', hF'⟩ := g0_fields_of_classical hGeom hC hF hT hS
  exact restrictedConverseGenuine_of_miller hM hB hD hCst (L.complete hC' hF')

end ZInQ.Manuscript.RC.Wiring
