import ZInQKernel.Contrib.OneProof.T10Proetale.Transport

/-!
# Semilinear squares of the geometric schemes

Changing the geometric base commutes with any arrow defined over the original
field. In particular, this gives the scheme square for the multiplication
covers used in a geometric construction of Tate duality.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry PkgI3
  MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

variable {K : Type} [Field K] {A B : AbVar K}

/-- A map of the geometric base changes induced by a homomorphism over `K`. -/
def geometricHom (f : AbVar.Hom A B) : T10Etale.AKbar A ⟶ T10Etale.AKbar B :=
  ((Over.pullback (T10Etale.specAlg K)).map f.hom).left

/-- The scheme square for changing the geometric base of a map defined over `K`. -/
theorem galAut_geometricHom (f : AbVar.Hom A B)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    T10Etale.galAut A σ ≫ geometricHom f = geometricHom f ≫ T10Etale.galAut B σ := by
  apply pullback.hom_ext
  · have h (D : AbVar K) :
        T10Etale.galAut D σ ≫ pullback.fst D.X.hom (T10Etale.specAlg K) =
          pullback.fst D.X.hom (T10Etale.specAlg K) := by
      simp [T10Etale.galAut, pullback.map]
    simp only [Category.assoc, geometricHom, Over.pullback_map_left, pullback.lift_fst]
    rw [h B, pullback.lift_fst, ← Category.assoc, h A]
  · have h (D : AbVar K) :
        T10Etale.galAut D σ ≫ pullback.snd D.X.hom (T10Etale.specAlg K) =
          pullback.snd D.X.hom (T10Etale.specAlg K) ≫ T10Etale.specAut σ := by
      simp [T10Etale.galAut, pullback.map]
    simp only [Category.assoc, geometricHom, Over.pullback_map_left, pullback.lift_snd]
    rw [h A, h B, ← Category.assoc, pullback.lift_snd]

/-- Multiplication by an integer on `A_Kbar` using the endomorphism over `K`. -/
def geometricMultiplication (A : AbVar K) (m : ℤ) :
    T10Etale.AKbar A ⟶ T10Etale.AKbar A :=
  geometricHom (m : AbVar.End A)

/-- In particular, every `[ℓ^n]` has a semilinear square before taking étale
cohomology or identifying it with a dual. -/
theorem galAut_geometricMultiplication (A : AbVar K) (m : ℤ)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    T10Etale.galAut A σ ≫ geometricMultiplication A m =
      geometricMultiplication A m ≫ T10Etale.galAut A σ :=
  galAut_geometricHom (m : AbVar.End A) σ

end
end ZInQ.Manuscript.T10Proetale
