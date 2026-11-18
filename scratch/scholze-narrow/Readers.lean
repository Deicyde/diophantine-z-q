import ZInQKernel.Contrib.OneProof.ScholzeNarrow

open CategoryTheory AlgebraicGeometry Module
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit
open DeRhamScholze DeRhamScholze.HT DeRhamScholze.HTMerge

section
variable (h : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality)
variable (hM : AvSplit.MumfordTorsionAlgClosed) (hW : DeRhamHodgeTate01)
variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (hd : A.dim = (2 : WithBot ℕ∞))

-- The original rank, dual comparison and direct comparison outputs at a surface.
include h hd in
example : finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * 2 :=
  hodgeNumberH1AbSurf_of_narrow p F A hd (narrow_of_abVar h)

include h hT hM hd in
example : IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧ HodgeRange p (fun σ => (A.galRep p).dual σ) 1 :=
  dual_deRhamSurf_of_narrow p F A hd (narrow_of_abVar h) hT hM

include h hT hM hd in
example : finrank (fieldF p F) (DeRhamPrint.Direct.ddrF p (A.galRep p)) = finrank ℚ_[p] (A.V p) :=
  deRhamVpAbSurfDirect_of_narrow p F A hd (narrow_of_abVar h) hT hM

include h hT hd in
example : finrank (fieldF p F) (DeRhamPrint.Direct.ddrF p (A.galRep p)) = finrank ℚ_[p] (A.V p) :=
  deRhamVpAbSurfDirect_of_narrowMilne p F A hd (narrow_of_abVar h) hT

include h hT hM hW in
example : HodgeTateDecompHomSurf :=
  hodgeTateDecompHomSurf_of_narrow (narrow_of_abVar h) hT hM hW

include h hT in
example : HodgeTateDecompOrSurf :=
  hodgeTateDecompOrSurf_of_narrowMilne (narrow_of_abVar h) hT

include h hT in
example : HodgeTateDecompAbSurf :=
  hodgeTateDecompAbSurf_of_narrow (narrow_of_abVar h) hT

include h in
example : ScholzeH1AbSurf := narrow_iff_abSurf.mp (narrow_of_abVar h)
end

example (old : ScholzeH1AbVar) (t10 : T10Etale.T10_TateDuality)
    (tate : TateTwistInvariants) (ax : AxSenTate) (dr : DeRhamH1AbVarT) : HDec.PkgI4.R10Surface :=
  HDec.HSyn.HodgeLF7.r10Surface
    (r10Surface_of_leaves (hodgeTateDecompAbSurf_of_narrow (narrow_of_abVar old) t10) tate ax dr)

#print axioms narrow_of_abVar
#print axioms narrow_iff_abSurf
#print axioms hodgeNumberH1AbSurf_of_narrow
#print axioms dual_deRhamSurf_of_narrow
#print axioms deRhamVpAbSurfDirect_of_narrow
#print axioms deRhamVpAbSurfDirect_of_narrowMilne
#print axioms hodgeTateDecompHomSurf_of_narrow
#print axioms hodgeTateDecompOrSurf_of_narrowMilne
#print axioms hodgeTateDecompAbSurf_of_narrow
#print axioms r10Surface_of_leaves
#print axioms r10Surface_of_abVar
#print axioms HDec.HSyn.HodgeLF7.r10Surface
#print axioms HDec.ZInQ.Contrib.G9.g9GlueFromSurfaces_of_fieldEmb
#print axioms HDec.ZInQ.Contrib.G9.g9GlueFromSurfaces
