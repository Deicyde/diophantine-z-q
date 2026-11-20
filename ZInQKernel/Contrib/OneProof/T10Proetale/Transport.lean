import ZInQKernel.Contrib.OneProof.T10Milne86.Printed
import ZInQKernel.HDecomp.Textbook.T10Etale

/-!
# Transport conventions for T10

The two squares needed to compose the comparison with the geometric identification
have different origins. Here we verify the convention for the classical pullback,
the semilinear calculation on points, and the composition when both squares are given.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry PkgI3
  MonoidalCategory CartesianMonoidalCategory MonObj
open scoped PadicInt

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

variable {K : Type} [Field K] (A : AbVar K)

/-- The pullback corresponding to the row's transport uses `1 × Spec(σ)`. -/
theorem galIso_inv_inv_eq_galAut (σ : Field.absoluteGaloisGroup K) :
    (T10Etale.galIso A σ⁻¹).inv = T10Etale.galAut A σ := by
  change AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K at σ
  change T10Etale.galAut A (σ⁻¹)⁻¹ = T10Etale.galAut A σ
  rw [inv_inv]

/-- View a geometric point as a section of `A_Kbar → Spec(Kbar)`. -/
def graphPoint (P : A.Pt (AlgebraicClosure K)) :
    Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ T10Etale.AKbar A :=
  pullback.lift P.left (𝟙 _) (by
    change P.left ≫ A.X.hom = 𝟙 _ ≫ T10Etale.specAlg K
    simpa only [Category.id_comp, T10Etale.specAlg, AbVar.ptObj, Over.mk_hom] using Over.w P)

set_option backward.isDefEq.respectTransparency false in
/-- Under `1 × Spec(σ)`, a graph is normalized to a section by precomposing with
`Spec(σ⁻¹)`. This acts on its point by `σ⁻¹`. -/
theorem graphPoint_galAut (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (P : A.Pt (AlgebraicClosure K)) :
    T10Etale.specAut σ⁻¹ ≫ graphPoint A P ≫ T10Etale.galAut A σ =
      graphPoint A (A.galAct σ⁻¹ P) := by
  let fst := pullback.fst A.X.hom (T10Etale.specAlg K)
  let snd := pullback.snd A.X.hom (T10Etale.specAlg K)
  have gf (Q : A.Pt (AlgebraicClosure K)) : graphPoint A Q ≫ fst = Q.left :=
    pullback.lift_fst _ _ _
  have gs (Q : A.Pt (AlgebraicClosure K)) : graphPoint A Q ≫ snd = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have af : T10Etale.galAut A σ ≫ fst = fst := by
    simp only [fst, T10Etale.galAut, pullback.map, pullback.lift_fst, Category.comp_id]
  have ass : T10Etale.galAut A σ ≫ snd = snd ≫ T10Etale.specAut σ := by
    simp only [snd, T10Etale.galAut, pullback.map, pullback.lift_snd]
  apply pullback.hom_ext
  · change (T10Etale.specAut σ⁻¹ ≫ graphPoint A P ≫ T10Etale.galAut A σ) ≫ fst =
      graphPoint A (A.galAct σ⁻¹ P) ≫ fst
    rw [Category.assoc, Category.assoc, af, gf, gf]
    rfl
  · change (T10Etale.specAut σ⁻¹ ≫ graphPoint A P ≫ T10Etale.galAut A σ) ≫ snd =
      graphPoint A (A.galAct σ⁻¹ P) ≫ snd
    rw [Category.assoc, Category.assoc, ass, ← Category.assoc (graphPoint A P), gs, gs,
      Category.id_comp, ← T10Etale.specAut_mul, inv_mul_cancel, T10Etale.specAut_one]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The classical étale pullback in the same convention as `galH`. -/
abbrev etaleGal (σ : Field.absoluteGaloisGroup K) :
    T10Milne86.EtaleH1 (T10Etale.AKbar A) ℓ →ₗ[ℤ_[ℓ]]
      T10Milne86.EtaleH1 (T10Etale.AKbar A) ℓ :=
  T10Milne86.etalePull (T10Etale.galAut A σ) ℓ

/-- The two transport squares compose to the row's equation at this abelian variety.
The second equation has to hold for the specific classical identification used. -/
theorem compose_transport_squares
    (C : (T10Etale.AKbar A).EllAdicCohomology ℓ 1 ≃ₗ[ℤ_[ℓ]]
      T10Milne86.EtaleH1 (T10Etale.AKbar A) ℓ)
    (φ : T10Milne86.EtaleH1 (T10Etale.AKbar A) ℓ ≃ₗ[ℤ_[ℓ]]
      Module.Dual ℤ_[ℓ] (A.T ℓ))
    (hC : ∀ σ x, C (T10Etale.galH A ℓ σ x) = etaleGal A ℓ σ (C x))
    (hφ : ∀ (σ : Field.absoluteGaloisGroup K) y,
      φ (etaleGal A ℓ σ y) = (A.galT (ℓ := ℓ) σ⁻¹).dualMap (φ y))
    (σ : Field.absoluteGaloisGroup K) (x : (T10Etale.AKbar A).EllAdicCohomology ℓ 1) :
    (C.trans φ) (T10Etale.galH A ℓ σ x) =
      (A.galT (ℓ := ℓ) σ⁻¹).dualMap ((C.trans φ) x) := by
  change φ (C (T10Etale.galH A ℓ σ x)) = (A.galT (ℓ := ℓ) σ⁻¹).dualMap (φ (C x))
  exact (congrArg (fun z => φ z) (hC σ x)).trans (hφ σ (C x))

end

end ZInQ.Manuscript.T10Proetale
