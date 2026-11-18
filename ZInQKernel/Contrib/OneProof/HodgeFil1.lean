import ZInQKernel.Contrib.OneProof.ScholzeH1AbVar
import ZInQKernel.Contrib.OneProof.HodgeTatePairingDecomp

/-!
Conditional glue for the Hodge-number clause of the degree-one Scholze row.
The extra input below pinpoints the missing arithmetic statement; it is not a provider
or a proposed headline hypothesis.
-/

namespace HodgeFil1

open DeRhamScholze DeRhamScholze.HT DeRhamScholze.HTAbVar
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open ZInQ.Contrib.HodgeTateFromPairing
open scoped TensorProduct

/-- The degree-one Scholze row with just the de Rham and filtration-range clauses. -/
def ScholzeH1AbVarDR : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    IsDeRhamFam p (F := F) (rhoH A.X p 1) ∧ HodgeRange p (F := F) (rhoH A.X p 1) 1

/-- Missing input: cyclotomic self-duality on the rational Tate module of each abelian
variety in the row. A nondegenerate pairing supplies this isomorphism; alternation and
integral perfection are unnecessary here. -/
def TatePolarizationSymmetry : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ B : LinearMap.BilinForm ℚ_[p] (A.V p), B.Nondegenerate ∧
      ∀ (σ : Field.absoluteGaloisGroup F) (x y : A.V p),
        B (A.galRep p σ x) (A.galRep p σ y) = cycPow p (gfToGqp p F σ) 1 * B x y

/-- A perfect pairing with cyclotomic multiplier balances the two Hodge–Tate
multiplicities. The two comparison bounds then give the dimension of `Fil¹`. -/
theorem finrank_filD_dual_of_pairing (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    {V : Type} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (B : LinearMap.BilinForm ℚ_[p] V) (hB : B.Nondegenerate)
    (hχ : ∀ σ x y, B (ρ σ x) (ρ σ y) = cycPow p (gfToGqp p F σ) 1 * B x y)
    (g : ℕ) (hdim : finrank ℚ_[p] V = 2 * g)
    (hDR : IsDeRhamFam p (fun σ => ρ.dual σ))
    (hRange : HodgeRange p (fun σ => ρ.dual σ) 1) :
    finrank ℚ_[p] (filD p (fun σ => ρ.dual σ) 1) = finrank ℚ_[p] F * g := by
  have hT := ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
  have hA := ZInQ.Contrib.CloudB3W11.axSenTate_proof
  obtain ⟨a, b, e, he⟩ := DeRhamScholze.TT.deRhamHodgeTate01_proof p F V ρ hDR hRange
  let E := ZInQ.Contrib.HodgeTateOr.dualEquiv p e
  have hE := ZInQ.Contrib.HodgeTateOr.dualEquiv_map p ρ e he
  have hab : b = a := eq_of_pairing p ρ B hB hχ E hE hT hA
  have hs : b + a = 2 * g := (add_eq_finrank p E).trans hdim
  have ha : a = g := by omega
  have hb : b = g := hab.trans ha
  have := fd_fixSp_range p (F := F) hT hA (-1)
  have := fd_fixSp_range p (F := F) hT hA 0
  have := fd_fixSp_range p (F := F) hT hA 1
  have hHT0 : finrank ℚ_[p] (htSpaceOver p ρ 0) = finrank ℚ_[p] F * g := by
    rw [finrank_htSpaceOver_of_decomp2 p ρ E hE 0, show (0 : ℤ) - 1 = -1 by omega,
      finrank_PSub2, finrank_fixSp_range p hT hA, finrank_fixSp_range p hT hA]
    simp [hb, ha, mul_comm]
  have hHT1 : finrank ℚ_[p] (htSpaceOver p ρ 1) = finrank ℚ_[p] F * g := by
    rw [finrank_htSpaceOver_of_decomp2 p ρ E hE 1, show (1 : ℤ) - 1 = 0 by omega,
      finrank_PSub2, finrank_fixSp_range p hT hA, finrank_fixSp_range p hT hA]
    simp [hb, ha, mul_comm]
  have hfil (j : ℕ) :
      Submodule.map (tensorDualEquiv p).toLinearMap (filD p (fun σ => ρ.dual σ) j) =
        ddrSpaceOver p ρ ⊓ filH p j := by
    rw [filD, Submodule.map_inf _ (tensorDualEquiv p).injective, map_ddrFam_dual, map_filRange_dual]
  have h0 : ddrSpaceOver p ρ ≤ filH p 0 := by
    have h := hfil 0
    rw [hRange.1, map_ddrFam_dual] at h
    exact inf_eq_left.mp h.symm
  have h2 : ddrSpaceOver p ρ ⊓ filH p 2 = ⊥ := by
    rw [← hfil 2, hRange.2, Submodule.map_bot]
  have hd : finrank ℚ_[p] (ddrSpaceOver p ρ) = finrank ℚ_[p] F * g + finrank ℚ_[p] F * g := by
    rw [← map_ddrFam_dual ρ, LinearEquiv.finrank_map_eq, hDR.2, Subspace.dual_finrank_eq,
      hdim, two_mul, mul_add]
  obtain ⟨t, ht, hσ⟩ := DeRhamScholze.TT.fontaineTwistT p
  have := (fd_htF0 ρ hT hA).1
  have := (fd_htF1 ρ hT hA).1
  have := fd_htSpaceOver ρ (0 : ℤ)
  have := fd_htSpaceOver ρ (1 : ℤ)
  obtain ⟨hu, hl⟩ := finrank_fil1_bounds ρ ht hσ h0 h2
  rw [← hfil 1, LinearEquiv.finrank_map_eq, hHT1] at hu
  rw [← hfil 1, LinearEquiv.finrank_map_eq, hd, hHT0] at hl
  exact le_antisymm hu (Nat.le_of_add_le_add_left hl)

/-- Pointwise Hodge number over the tree's étale cohomology, using Milne to identify
it with the dual of the paired Tate module. -/
theorem finrank_fil1_of_dR_of_pairing (hT : T10Etale.T10_TateDuality)
    (hP : TatePolarizationSymmetry)
    (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞))
    (hDR : IsDeRhamFam p (F := F) (rhoH A.X p 1))
    (hRange : HodgeRange p (F := F) (rhoH A.X p 1) 1) :
    finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * g := by
  have hf := DeRhamPrint.tateModuleFree_of_mumford
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  have hp := DeRhamPrint.natCast_p_ne_zero p F
  obtain ⟨hfree, hfinite, -⟩ := hf F (DeRhamPrint.toKer A) p hp
  obtain ⟨hfd, hdim⟩ := DeRhamPrint.finrank_V_of_tateModuleFree p hf hp A g hg
  obtain ⟨φ, hφ⟩ := hT F (DeRhamPrint.toKer A) p hp
  obtain ⟨B, hB, hχ⟩ := hP p F A
  let e := milneE p A φ
  have he := milneE_comm p A φ hφ
  have hD := isDeRhamFam_of_equiv p e he hDR
  have hR := hodgeRange_of_equiv p e he 1 hRange
  have h := finrank_filD_dual_of_pairing p F (A.galRep p) B hB hχ g hdim hD hR
  rwa [← map_filD p e he 1, LinearEquiv.finrank_map_eq] at h

/-- Conditional recovery of the current row in every dimension. -/
theorem fil1_of_dR (hDR : ScholzeH1AbVarDR) (hT : T10Etale.T10_TateDuality)
    (hP : TatePolarizationSymmetry) : DeRhamScholze.HTMerge.ScholzeH1AbVar := by
  intro p _ F _ _ _ A g hg
  obtain ⟨h₁, h₂⟩ := hDR p F A g hg
  exact ⟨h₁, h₂, finrank_fil1_of_dR_of_pairing hT hP p F A g hg h₁ h₂⟩

/-- The surface case by taking `g = 2` in the pointwise result. -/
theorem fil1_surf_of_dR (hDR : ScholzeH1AbVarDR) (hT : T10Etale.T10_TateDuality)
    (hP : TatePolarizationSymmetry) : DeRhamScholze.HTMerge.ScholzeH1AbSurf := by
  intro p _ F _ _ _ A hg
  obtain ⟨h₁, h₂⟩ := hDR p F A 2 hg
  exact ⟨h₁, h₂, (finrank_fil1_of_dR_of_pairing hT hP p F A 2 hg h₁ h₂).trans (mul_comm _ _)⟩

end HodgeFil1

#print axioms HodgeFil1.finrank_filD_dual_of_pairing
#print axioms HodgeFil1.finrank_fil1_of_dR_of_pairing
#print axioms HodgeFil1.fil1_of_dR
#print axioms HodgeFil1.fil1_surf_of_dR
