import ZInQKernel.Contrib.OneProof.T10Narrow
import ZInQKernel.Contrib.OneProof.ScholzeH1AbVar

/-! The Scholze readers with only the local hypothesis. The equivariant transport, the
finite-freeness argument, and the dimension calculations are those of `ScholzeH1AbVar`. -/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace DeRhamScholze.HTMerge

open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open DeRhamScholze.HT
open scoped TensorProduct

noncomputable section

section One

variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- Transport de Rhamness, the Hodge range, and the first filtration dimension to the rational Tate dual. -/
theorem dual_of_H1_loc (hT : T10Etale.T10_TateDualityLocal) (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (n : ℕ)
    (h : IsDeRhamFam p (F := F) (rhoH A.X p 1) ∧ HodgeRange p (F := F) (rhoH A.X p 1) 1 ∧
      finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = n) :
    IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧ HodgeRange p (fun σ => (A.galRep p).dual σ) 1 ∧
      finrank ℚ_[p] (filD p (fun σ => (A.galRep p).dual σ) 1) = n := by
  have hp : (p : F) ≠ 0 := DeRhamPrint.natCast_p_ne_zero p F
  obtain ⟨hfree, hfin, -⟩ := DeRhamPrint.tateModuleFree_of_mumford hM F (DeRhamPrint.toKer A) p hp
  obtain ⟨φ, hφ⟩ := hT p F (DeRhamPrint.toKer A)
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨isDeRhamFam_of_equiv p (milneE p A φ) (milneE_comm p A φ hφ) h1,
    hodgeRange_of_equiv p (milneE p A φ) (milneE_comm p A φ hφ) 1 h2, ?_⟩
  rw [← map_filD p (milneE p A φ) (milneE_comm p A φ hφ) 1, LinearEquiv.finrank_map_eq]
  exact h3

/-- Recover the dimension-indexed Hodge–Tate decomposition for one abelian variety. -/
theorem htDecomp_of_H1_loc (hT : T10Etale.T10_TateDualityLocal) (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞))
    (h : IsDeRhamFam p (F := F) (rhoH A.X p 1) ∧ HodgeRange p (F := F) (rhoH A.X p 1) 1 ∧
      finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * g) :
    ∃ e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k))) := by
  have hM := ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hp : (p : F) ≠ 0 := DeRhamPrint.natCast_p_ne_zero p F
  obtain ⟨hfdV, hdimV⟩ := DeRhamPrint.finrank_V_of_tateModuleFree p (DeRhamPrint.tateModuleFree_of_mumford hM) hp A g hg
  obtain ⟨h1, h2, h3⟩ := dual_of_H1_loc p hT hM A _ h
  obtain ⟨a, b, e, he, hab, hb⟩ :=
    DeRhamScholze.HTAbVar.hodgeTate01_dims (A.galRep p) DeRhamScholze.TT.fontaineTwistT h1 h2 g h3
  rw [hdimV] at hab
  obtain rfl : a = g := by omega
  subst hb
  exact ⟨ZInQ.Contrib.HodgeTateOr.dualEquiv p e, ZInQ.Contrib.HodgeTateOr.dualEquiv_map p (A.galRep p) e he⟩

end One

/-- The rational Tate dual is de Rham with Hodge jumps in `[0, 1]`. -/
theorem dual_deRham_of_scholzeH1_loc (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDualityLocal)
    (hM : AvSplit.MumfordTorsionAlgClosed) (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧ HodgeRange p (fun σ => (A.galRep p).dual σ) 1 := by
  obtain ⟨g, hg⟩ := dim_finite_I4 A
  obtain ⟨h1, h2, -⟩ := dual_of_H1_loc p hT hM A _ (hN p F A g hg)
  exact ⟨h1, h2⟩

/-- Pass from de Rhamness of the dual to de Rhamness of the rational Tate module. -/
theorem deRhamVpAbVarDirect_of_scholzeH1_loc (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDualityLocal)
    (hM : AvSplit.MumfordTorsionAlgClosed) : DeRhamPrint.Direct.DeRhamVpAbVarDirect :=
  fun p _ F _ _ _ A => (DeRhamPrint.Direct.isDeRhamTensorOver_iff p (A.galRep p)).mp
    (isDeRhamTensorOver_of_H1 p hM A (dual_deRham_of_scholzeH1_loc hN hT hM p F A).1)

/-- Supply the finite-free Tate module using the existing Mumford torsion theorem. -/
theorem deRhamVpAbVarDirect_of_scholzeH1Milne_loc (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDualityLocal) :
    DeRhamPrint.Direct.DeRhamVpAbVarDirect :=
  deRhamVpAbVarDirect_of_scholzeH1_loc hN hT ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof

/-- Recover the representation-theoretic Hodge–Tate decomposition. -/
theorem hodgeTateDecompHom_of_scholzeH1_loc (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDualityLocal)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hW : DeRhamHodgeTate01) : ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom := by
  intro p _ F _ _ _ A
  obtain ⟨h1, h2⟩ := dual_deRham_of_scholzeH1_loc hN hT hM p F A
  exact hW p F (A.V p) (A.galRep p) h1 h2

/-- Recover the Hodge–Tate disjunction with the torsion and period inputs discharged. -/
theorem hodgeTateDecompOr_of_scholzeH1Milne_loc (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDualityLocal) :
    ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr :=
  ZInQ.Contrib.HodgeTateOr.or_of_hom (hodgeTateDecompHom_of_scholzeH1_loc hN hT
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof DeRhamScholze.TT.deRhamHodgeTate01_proof)

/-- Recover the Hodge–Tate decomposition in all dimensions. -/
theorem hodgeTateDecompAbVar_of_scholzeH1_loc (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDualityLocal) :
    HodgeTateDecompAbVar :=
  fun p _ F _ _ _ A g hg => htDecomp_of_H1_loc p hT A g hg (hN p F A g hg)

/-- Compatibility with the previous pair of Scholze and Hodge number inputs. -/
theorem hodgeTateDecompAbVar_of_old_loc (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDualityLocal)
    (hH : DeRhamScholze.HTAbVar.HodgeNumberH1AbVar) : HodgeTateDecompAbVar :=
  hodgeTateDecompAbVar_of_scholzeH1_loc (scholzeH1AbVar_of_old hS hH) hT

/-- Recover the surface specialization from the surface version of the comparison. -/
theorem hodgeTateDecompAbSurf_of_scholzeH1AbSurf_loc (hN : ScholzeH1AbSurf) (hT : T10Etale.T10_TateDualityLocal) :
    HodgeTateDecompAbSurf := by
  intro p _ F _ _ _ A hA
  obtain ⟨h1, h2, h3⟩ := hN p F A hA
  exact htDecomp_of_H1_loc p hT A 2 hA ⟨h1, h2, h3.trans (mul_comm _ _)⟩

end

end DeRhamScholze.HTMerge

#print axioms DeRhamScholze.HTMerge.dual_of_H1_loc
#print axioms DeRhamScholze.HTMerge.htDecomp_of_H1_loc
#print axioms DeRhamScholze.HTMerge.dual_deRham_of_scholzeH1_loc
#print axioms DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1_loc
#print axioms DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1Milne_loc
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompHom_of_scholzeH1_loc
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne_loc
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1_loc
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_old_loc
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompAbSurf_of_scholzeH1AbSurf_loc
