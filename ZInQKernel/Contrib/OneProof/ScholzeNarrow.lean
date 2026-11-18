import ZInQKernel.Contrib.OneProof.ScholzeH1AbVar
import ZInQKernel.OneProof.H.TailE
import ZInQKernel.OneProof.H.TailV

/-!
The degree-one comparison input restricted to the abelian surfaces used by G9.
The manuscript (diophantine_zq.tex L10939–10965, L10996) uses this case.
The Scholze locators and the algebraic/analytic cohomology dictionary retain
the same review status as for `ScholzeH1AbVar`.
-/

namespace DeRhamScholze.HTMerge

open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open DeRhamScholze.HT
open scoped TensorProduct

noncomputable section

/-- The three original clauses, restricted to dimension two. Pending review. -/
def ScholzeH1Narrow : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), A.dim = (2 : WithBot ℕ∞) →
    IsDeRhamFam p (F := F) (rhoH A.X p 1) ∧ HodgeRange p (F := F) (rhoH A.X p 1) 1 ∧
      finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * 2

theorem narrow_of_abVar (h : ScholzeH1AbVar) : ScholzeH1Narrow :=
  fun p _ F _ _ _ A hd => h p F A 2 hd

theorem narrow_iff_abSurf : ScholzeH1Narrow ↔ ScholzeH1AbSurf := by
  constructor <;> intro h p _ F _ _ _ A hd
  · obtain ⟨h1, h2, h3⟩ := h p F A hd
    exact ⟨h1, h2, h3.trans (mul_comm _ _)⟩
  · obtain ⟨h1, h2, h3⟩ := h p F A hd
    exact ⟨h1, h2, h3.trans (mul_comm _ _)⟩

section One

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
variable (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (hd : A.dim = (2 : WithBot ℕ∞))

include hd

theorem hodgeNumberH1AbSurf_of_narrow (h : ScholzeH1Narrow) :
    finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * 2 :=
  (h p F A hd).2.2

theorem dual_deRhamSurf_of_narrow (h : ScholzeH1Narrow) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) :
    IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧ HodgeRange p (fun σ => (A.galRep p).dual σ) 1 := by
  obtain ⟨h1, h2, -⟩ := dual_of_H1 p hT hM A _ (h p F A hd)
  exact ⟨h1, h2⟩

theorem deRhamVpAbSurfDirect_of_narrow (h : ScholzeH1Narrow) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) :
    finrank (fieldF p F) (DeRhamPrint.Direct.ddrF p (A.galRep p)) = finrank ℚ_[p] (A.V p) :=
  (DeRhamPrint.Direct.isDeRhamTensorOver_iff p (A.galRep p)).mp
    (isDeRhamTensorOver_of_H1 p hM A (dual_deRhamSurf_of_narrow p F A hd h hT hM).1)

theorem deRhamVpAbSurfDirect_of_narrowMilne (h : ScholzeH1Narrow) (hT : T10Etale.T10_TateDuality) :
    finrank (fieldF p F) (DeRhamPrint.Direct.ddrF p (A.galRep p)) = finrank ℚ_[p] (A.V p) :=
  deRhamVpAbSurfDirect_of_narrow p F A hd h hT
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof

end One

/-- The dimensionless Hom formulation specialized to dimension two. -/
def HodgeTateDecompHomSurf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), A.dim = (2 : WithBot ℕ∞) →
    ∃ (a b : ℕ) (e : (A.V p →ₗ[ℚ_[p]] ℂ_[p]) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (f : A.V p →ₗ[ℚ_[p]] ℂ_[p]),
        e (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ A.galRep p σ⁻¹) =
          ((fun k => cpAct p (gfToGqp p F σ) ((e f).1 k)),
            (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e f).2 k)))

def HodgeTateDecompExistsSurf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), A.dim = (2 : WithBot ℕ∞) →
    ∃ (a b : ℕ) (e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k)))

/-- The original disjunction with each alternative specialized to surfaces. -/
def HodgeTateDecompOrSurf : Prop :=
  HodgeTateDecompExistsSurf ∨ HodgeTateDecompHomSurf

theorem hodgeTateDecompHomSurf_of_narrow (h : ScholzeH1Narrow) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hW : DeRhamHodgeTate01) : HodgeTateDecompHomSurf := by
  intro p _ F _ _ _ A hd
  obtain ⟨h1, h2⟩ := dual_deRhamSurf_of_narrow p F A hd h hT hM
  exact hW p F (A.V p) (A.galRep p) h1 h2

theorem hodgeTateDecompOrSurf_of_narrowMilne (h : ScholzeH1Narrow) (hT : T10Etale.T10_TateDuality) :
    HodgeTateDecompOrSurf :=
  Or.inr (hodgeTateDecompHomSurf_of_narrow h hT
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
    DeRhamScholze.TT.deRhamHodgeTate01_proof)

theorem hodgeTateDecompAbSurf_of_narrow (h : ScholzeH1Narrow) (hT : T10Etale.T10_TateDuality) :
    HodgeTateDecompAbSurf :=
  fun p _ F _ _ _ A hd => htDecomp_of_H1 p hT A 2 hd (h p F A hd)

/-- Amended R10 at precisely the local models used in G9. -/
def R10Surface : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), A.dim = (2 : WithBot ℕ∞) →
    IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = 2 ∧
      htMultOver p (A.galRep p) (-1) = 2 ∧
        ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p (A.galRep p) w = 0

/-- The existing R10 proof specialized before forming the two clauses.
Keep its independent tensor-form input for the de Rham assertion about `V_p(A)`. -/
theorem r10Surface_of_leaves (hHT : HodgeTateDecompAbSurf) (hT : TateTwistInvariants)
    (hA : AxSenTate) (hdR : DeRhamH1AbVarT) : R10Surface := by
  intro p _ F _ _ _ A hd
  obtain ⟨e, he⟩ := hHT p F A hd
  have := finiteDimensional_of_decomp p e
  have hmult w := htMultOver_of_decomp p (A.galRep p) e he hT hA w
  refine ⟨(isDeRhamOver_iff_tensor_dual p (A.galRep p)).mp (hdR p F A), ?_, ?_, ?_⟩
  · rw [hmult 0]
    decide
  · rw [hmult (-1)]
    decide
  · intro w hw0 hw1
    rw [hmult w]
    simp [hw0, hw1]

theorem r10Surface_of_abVar (h : ZInQ.Contrib.R10.DeRhamComparisonHT) : R10Surface := by
  intro p _ F _ _ _ A hd
  obtain ⟨h1, h2⟩ := h p F A
  obtain ⟨h3, h4, h5⟩ := h1 2 hd
  exact ⟨h3, h4, h5, h2⟩

end

end DeRhamScholze.HTMerge


namespace HDec

namespace PkgI4

/-- The surface form of R10 over the assembly's copies of the objects. -/
def R10Surface : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : I3.AbVar F), A.dim = (2 : WithBot ℕ∞) →
    IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = 2 ∧
      htMultOver p (A.galRep p) (-1) = 2 ∧
        ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p (A.galRep p) w = 0

end PkgI4

namespace HSyn.HodgeLF7

/-- The surface instance of the existing transport between the two Tate modules. -/
theorem r10Surface (h : _root_.DeRhamScholze.HTMerge.R10Surface) : PkgI4.R10Surface := by
  intro p _ F _ _ _ A hd
  obtain ⟨h1, h2, h3, h4⟩ := h p F (toG9AbVar A) hd
  have hR := isDeRhamOver_congr p ((toG9AbVar A).galRep p) (A.galRep p) (vEquiv p A) (vEquiv_galRep p A)
  have hM := htMultOver_congr p ((toG9AbVar A).galRep p) (A.galRep p) (vEquiv p A) (vEquiv_galRep p A)
  exact ⟨hR.1 h1, (hM 0).symm.trans h2, (hM (-1)).symm.trans h3,
    fun w hw0 hw1 => (hM w).symm.trans (h4 w hw0 hw1)⟩

end HSyn.HodgeLF7

namespace G0Galois

open _root_.PkgI4 (GaloisRep)

/-- The G9 consumer of R10, with all four conclusions required at the same surface only. -/
def G9GlueFromSurfaces : Prop :=
  PkgI4.R10Surface →
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G9Out r

end G0Galois

namespace ZInQ.Contrib.G9

open _root_.HDec.PkgI4 _root_.HDec.ZInQ.Contrib.G9.PkgI4 Module G0Galois
open scoped TensorProduct

noncomputable section

/-- The proof of `g9GlueNoT23_of_fieldEmb`, taking R10 only at its local surface `A'`. -/
theorem g9GlueFromSurfaces_of_fieldEmb (hLM : G9Bridge.LocalModel)
    (hB : G9Bridge.FieldEmbBdR) : G9GlueFromSurfaces := by
  intro hR10 K _ _ A ℓ _ r e hdim hint
  obtain ⟨F, _, _, _, _, A', j, c, g, hdim', hc, hg⟩ := hLM K A ℓ hdim
  obtain ⟨hdR, h0, h1, hw⟩ := hR10 ℓ F A' hdim'
  obtain ⟨ιB, hιB⟩ := hB ℓ F
  let cb : PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A'.V ℓ ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A.V ℓ :=
    LinearEquiv.baseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ c
  let e' := (cb.trans e).trans (twistPair r g)
  have hcb : ∀ σ x, cb ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      tate A ℓ (j σ) (cb x) := by
    intro σ x
    induction x using TensorProduct.inductionOn with
    | tmul a v =>
      change cb (a ⊗ₜ (A'.galRep ℓ σ v)) = (A.galRep ℓ (j σ)).baseChange (PadicAlgCl ℓ) (cb (a ⊗ₜ v))
      simp only [cb, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, hc]
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have he' : ∀ σ x, e' ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      ((r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec (e' x).1,
        (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec
          (e' x).2) := by
    intro σ x
    have hR : (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) := rfl
    have hconj : r.mat g⁻¹ * r.mat (resQ K (j σ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) * r.mat g⁻¹ := by
      rw [hg σ, galoisRep_mat_mul, galoisRep_mat_mul, ← mul_assoc, ← mul_assoc,
        galoisRep_mat_inv_mul, one_mul]
    simp only [e', LinearEquiv.trans_apply, hcb, twistPair_apply, hint _ (cb x), hR,
      Matrix.mulVec_mulVec, hconj]
  obtain ⟨E, hE, ρE, eE, hmap, he⟩ :=
    coef_descent ℓ F (A'.galRep ℓ) (r.restrictLocal ℓ) e' he'
  exact ⟨⟨E, hE, ρE, hmap, core_dR_F ℓ F ιB hιB (A'.galRep ℓ) ρE eE he hdR⟩,
    ⟨E, hE, ρE, hmap, core_ht ℓ F (A'.galRep ℓ) ρE eE he h0 h1 hw⟩⟩

/-- The restricted G9, with the same local model and period-ring embedding as the base. -/
theorem g9GlueFromSurfaces : G9GlueFromSurfaces :=
  g9GlueFromSurfaces_of_fieldEmb
    (localModel_of_abVarBaseChange _root_.HDec.HSyn.g9AbVarBaseChange_proved) fieldEmbBdR

end

end ZInQ.Contrib.G9

end HDec
