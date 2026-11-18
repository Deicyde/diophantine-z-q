import ZInQKernel.Contrib.OneProof.HTAbVarScholzeDims
import ZInQKernel.Contrib.OneProof.DeRhamScholzeT

/-!
# ht-abvar, part 2: the field `hodgeTateDecompAbVar` from Scholze, Milne and the Hodge numbers

Task ht-abvar (2026-11-17; report `docs/research/ht-abvar.md`). The leaf `HodgeNumberH1AbVar` and the dimension
count `hodgeTate01_dims` are in `HTAbVarScholzeDims.lean` (which imports only `DeRhamScholzeHT`: in the larger
environment of `DeRhamScholzeT` the instance search for `StrongRankCondition ℚ_[p]` times out); `fontaineTwistT`
is in `DeRhamScholzeT.lean`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace DeRhamScholze.HTAbVar

open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open DeRhamScholze.HT
open scoped TensorProduct

noncomputable section

/-! ## §3. The field -/

/-- `Fil¹` of `D_dR(V_p(A)^∨)` has the dimension of `Fil¹ D_dR(H¹_ét)` (Milne's identification, `milneE`). -/
theorem finrank_filD_dual (hT : T10Etale.T10_TateDuality) (hH : HodgeNumberH1AbVar) (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F)
    (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) :
    finrank ℚ_[p] (filD p (fun σ => (A.galRep p).dual σ) 1) = finrank ℚ_[p] F * g := by
  have hM := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hp : (p : F) ≠ 0 := DeRhamPrint.natCast_p_ne_zero p F
  obtain ⟨hfree, hfin, -⟩ := DeRhamPrint.tateModuleFree_of_mumford hM F (DeRhamPrint.toKer A) p hp
  obtain ⟨φ, hφ⟩ := hT F (DeRhamPrint.toKer A) p hp
  rw [← map_filD p (milneE p A φ) (milneE_comm p A φ hφ) 1, LinearEquiv.finrank_map_eq]
  exact hH p F A g hg

/-- **The H-bundle field `hodgeTateDecompAbVar` from the manuscript's route**: Scholze's comparison
(`ScholzeDeRhamAlg`), Milne's identification (`T10_TateDuality`) and the Hodge numbers (`HodgeNumberH1AbVar`).
No Picard scheme, no dual abelian variety, no Weil pairing. -/
theorem hodgeTateDecompAbVar_of_scholze (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality)
    (hH : HodgeNumberH1AbVar) : HodgeTateDecompAbVar := by
  intro p _ F _ _ _ A g hg
  have hM := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hp : (p : F) ≠ 0 := DeRhamPrint.natCast_p_ne_zero p F
  obtain ⟨hfdV, hdimV⟩ := DeRhamPrint.finrank_V_of_tateModuleFree p (DeRhamPrint.tateModuleFree_of_mumford hM) hp A g hg
  obtain ⟨h1, h2⟩ := dual_deRham_of_scholze p hS hT hM F A
  obtain ⟨a, b, e, he, hab, hb⟩ :=
    hodgeTate01_dims (A.galRep p) DeRhamScholze.TT.fontaineTwistT h1 h2 g (finrank_filD_dual hT hH p F A g hg)
  rw [hdimV] at hab
  obtain rfl : a = g := by omega
  subst hb
  exact ⟨ZInQ.Contrib.HodgeTateOr.dualEquiv p e, ZInQ.Contrib.HodgeTateOr.dualEquiv_map p (A.galRep p) e he⟩

end

end DeRhamScholze.HTAbVar
