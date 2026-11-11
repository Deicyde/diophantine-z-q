import ZInQKernel.RouteK.RankVariants
import ZInQKernel.RouteK.RankDL
import ZInQKernel.RouteK.RankInf

open ZInQ ZInQ.RouteK

/-- F1: CR₃^TYZ_Cl,Rk implies the three forms with the premise `#Sel₂ = 8`. -/
theorem rv_tyz_of_tyzClRk (h : Rank.CertifiedRankTYZClRk) : Rank5b.CertifiedRankTYZ :=
  Rank.certifiedRankTYZ_of_certifiedRankTYZRk' (Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk h)

theorem rv_tyzCl_of_tyzClRk (h : Rank.CertifiedRankTYZClRk) : Rank5b.CertifiedRankTYZCl :=
  Rank.certifiedRankTYZCl_of_certifiedRankTYZClRk' h

theorem rv_5b_of_tyzClRk (h : Rank.CertifiedRankTYZClRk) : Rank5b.CertifiedRank5b :=
  Rank5b.certifiedRank5b_of_certifiedRankTYZ (rv_tyz_of_tyzClRk h)

theorem rv_dlAdm_of_tyzClRk (h : Rank.CertifiedRankTYZClRk) : Rank.CertifiedRankDLAdmRk :=
  Rank.certifiedRankDLAdmRk_of_certifiedRankDLRk
    (Rank.certifiedRankDLRk_of_certifiedRankTYZRk (Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk h))

#print axioms rv_tyz_of_tyzClRk
#print axioms rv_tyzCl_of_tyzClRk
#print axioms rv_5b_of_tyzClRk
#print axioms rv_dlAdm_of_tyzClRk
#print axioms exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank5b
#print axioms exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankDLAdmRk
#print axioms exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk
#print axioms Rank.certifiedRankTYZClInf_iff_certifiedRankTYZClRk
