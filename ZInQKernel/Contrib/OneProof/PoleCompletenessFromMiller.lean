import ZInQKernel.Contrib.OneProof.CasselsTatePairing
import ZInQKernel.Contrib.OneProof.ForwardRankLiterature

/-!
# The forward rank input to pole completeness

The rank and finiteness conclusions of Miller's Theorem 4.4 give the forward
rank implication used in the manuscript's proof of Theorem 5.2. The
Cassels–Tate pairing still supplies Lemma 5.4, and Theorem 5.3 still supplies
the restricted converse over the genuine two-power Selmer group.
-/

set_option autoImplicit false

namespace ZInQ.Manuscript.ForwardRankLiterature

/-- The forward theorem for ranks at most one has the rank-one consequence
required by the pole descent. -/
theorem kolyvaginRankOne_of_forwardRankAtMostOne
    (h : ForwardRankAtMostOne) : PoleRC.KolyvaginRankOne :=
  fun E hE hA => (rankOne_and_finiteSha h E hE hA).1

/-- Pole completeness from the restricted converse, the Cassels–Tate pairing,
and the rank and finiteness part of Miller's Theorem 4.4. The forward supplier
makes separate modularity and Kolyvagin premises unnecessary in this assembly. -/
theorem poleCompleteness_of_millerThm44
    (hRC : SelmerTwoPower.RestrictedConverseGenuine)
    (hCT : PoleS12.CasselsTatePairingCurves)
    (hM : ForwardRankAtMostOne) :
    ZInQ.Manuscript.PoleCompleteness :=
  PoleRC.poleCompleteness_of_crm
    (PoleRC.crm_of_restrictedConverse_proved SelmerTwoPower.SelmerCorankOne hRC
      (PoleS12.lemma54At_of_casselsTatePairing hCT)
      (kolyvaginRankOne_of_forwardRankAtMostOne hM))
    PoleS12.simultaneousConstruction

end ZInQ.Manuscript.ForwardRankLiterature
