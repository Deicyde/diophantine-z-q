import ZInQKernel.Contrib.CloudB3RC53.CoordLink.E1a
import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.PlaceSupport

/-!
# E1a, part 3: consistency of the two inputs (LESSON 2)

* `kmCoord_zero_class`: the coordinate of the zero class vanishes (the augmented complex is not
  exact in degree zero, so it has no contraction and its torsion is `0`).
* `uK_eq_zero_of_rep_zero`: a representation of the zero corrected coordinate is zero.
* `coordLinkInputs_example`: for lane ClearingComplex's consistency witness
  `identification2_example` (one genuine tame new place) and interface data with `ũ = 0`, the two
  inputs `CorrectedIsEta` and `RelIsKM` hold together (zero class and functional, `u_rel = 0`), and
  `coordLink_of_km` applies (`coordLink_example`).

The instance is degenerate (`ũ = 0`, zero class); it shows that the inputs are jointly satisfiable
with a genuine `Identification2`, not that they hold for the genuine coordinate.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CoordLink

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)

/-- **The coordinate of the zero class vanishes.** -/
theorem kmCoord_zero_class {R : Type*} [CommRing R] [Nontrivial R] {ι0 ι1 ι2 ι3 : Type*}
    [Fintype ι0] [Fintype ι1] [Fintype ι2] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1]
    [DecidableEq ι2] [DecidableEq ι3] (C : FourCx R ι0 ι1 ι2 ι3) (lam : ι2 → R)
    (hz : C.d1 *ᵥ (0 : ι1 → R) = 0) (hlam : lam ᵥ* C.d1 = 0)
    (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) : kmCoord C 0 lam hz hlam σ = 0 := by
  have hno : ¬ Nonempty (Contraction (C.aug 0 lam hz hlam).toBased) := by
    rintro ⟨h⟩
    have hex := BasedCx.isExact_of_contraction _ h
    set e : (ι0 ⊕ Unit) ⊕ ι2 → R := Pi.single (Sum.inl (Sum.inr ())) 1
    obtain ⟨y, hy⟩ := hex.1 e (by
      funext i
      rcases i with i | i <;>
        simp [e, FourCx.toBased_dOE, FourCx.aug, mulVec, dotProduct, Pi.single_apply])
    have := congrFun hy (Sum.inl (Sum.inr ()))
    simp [e, FourCx.toBased_dEO, mulVec, dotProduct, Fintype.sum_sum_type] at this
  unfold kmCoord torsion
  simp only [hno, dite_false, neg_zero]

/-- A representation of the zero corrected coordinate is zero. -/
theorem uK_eq_zero_of_rep_zero {ℓ : ℕ} (Dd : RCData ℓ) (F : Family)
    (h0 : ∀ x, Dd.uTilde F x = 0) (e : Addr F.b → ℕ) (g : Addr F.b → Lam)
    (hrep : UTildeRep Dd F e g) (x : Addr F.b) : uK (O := OO) (e x) (g x) = 0 := by
  have hg : g x = 0 := by
    ext j
    have := hrep x j
    rw [h0 x, map_zero] at this
    have h2 : (2 : ℚ_[2]) ^ e x ≠ 0 := pow_ne_zero _ two_ne_zero
    have h3 : ((PowerSeries.coeff j (g x) : ℤ_[2]) : ℚ_[2]) = 0 := by
      field_simp at this; simpa using this.symm
    simpa using h3
  simp [uK, hg]

/-- Interface data with `ũ = 0` (all other fields arbitrary). -/
def ddZero (ℓ : ℕ) : RCData ℓ where
  S := ∅
  prepared _ := False
  Lstar _ := 0
  jgen _ := 0
  jrc _ _ := 0
  hstar := 0
  stages := pure 0
  Mθ _ := 0
  aθ _ _ := 0
  admissible _ _ := False
  δo := 0
  kfin := 0
  uPrim _ _ := 0
  uTilde _ _ := 0

/-- The consistency witness of lane ClearingComplex. -/
abbrev Mex (b : ℕ) : Identification2 b 0 0 0 0 := identification2_example b

/-- The zero class. -/
abbrev zEx (b : ℕ) : Fin (Mex b).D.m0 ⊕ Unit ⊕ Fin (Mex b).D.m1 → MonoidAlgebra OO (SignGroup b) :=
  0

/-- The zero functional. -/
abbrev lamEx (b : ℕ) : (Fin (Mex b).C.m1 ⊕ Unit ⊕ Fin (Mex b).C.m2) ⊕ (Mex b).C.N →
    MonoidAlgebra OO (SignGroup b) := 0

theorem hz0 (b : ℕ) : (Mex b).D.d1 *ᵥ zEx b = 0 := mulVec_zero _

theorem hlam0 (b : ℕ) :
    lamEx b ᵥ* fromRows ((Mex b).C.map (φO b)).X ((Mex b).C.map (φO b)).Y = 0 :=
  zero_vecMul _

/-- **LESSON 2: the two inputs of E1a hold together** for lane ClearingComplex's consistency
witness `identification2_example` and interface data with `ũ = 0`. -/
theorem coordLinkInputs_example (ℓ : ℕ) (F : Family) :
    CorrectedIsEta (ddZero ℓ) F 1 0 ∧
      RelIsKM (Mex F.b) 0 (zEx F.b) (lamEx F.b) (hz0 F.b) (hlam0 F.b) := by
  refine ⟨fun e g hrep x => ?_, fun x _ => ?_⟩
  · rw [uK_eq_zero_of_rep_zero (ddZero ℓ) F (fun _ => rfl) e g hrep x]
    simp
  · have hz' : (evK (sgnChar x) ∘ zEx F.b) = 0 := by
      funext i; simp
    exact ((kmCoord_congr rfl hz' rfl _ _ (mulVec_zero _) (hlamev (hlam0 F.b) x) _).trans
      (kmCoord_zero_class _ _ _ _ _)).symm

/-- `coordLink_of_km` applied to the consistency instance. -/
theorem coordLink_example (ℓ : ℕ) (F : Family) :
    ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep (ddZero ℓ) F e g →
      CoordLink (Mex F.b).toIdentification.B
        (kappaOf (Mex F.b)) 1 0 e g
        (cOf (Mex F.b).D (zEx F.b)
          (transportFun ((Mex F.b).C.map (φO F.b)) (lamEx F.b)) (hz0 F.b)
          (hμ_cancel ((Mex F.b).C.map (φO F.b))
            (Mex F.b).isUnit_B (hlam0 F.b))) :=
  coordLink_of_km (ddZero ℓ) F (Mex F.b) (zEx F.b) (lamEx F.b) (hz0 F.b) (hlam0 F.b) 1 0
    (coordLinkInputs_example ℓ F).1 (coordLinkInputs_example ℓ F).2

end ZInQ.Contrib.CloudB3RC53.CoordLink
