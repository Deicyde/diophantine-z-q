import ZInQKernel.Contrib.OneProof.PhiAmpleIsogenyWeil

/-! By-product (not used by the fold): pic-dict's leaf `MumfordSquareAC` (theorem of the square, Mumford §6 Cor. 4
over `k = k̄`) from L1 and L2: `φ_c = λ_c ≫ j` with `λ_c` a homomorphism (`exists_hom_comp_eq_phiL`), `j` a
homomorphism, and `kClass` an injective homomorphism (Kleiman 9.2.5 at `Spec k̄`). -/

open CategoryTheory AlgebraicGeometry Limits Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

namespace PhiSurj

open T09Pic PkgI3 PkgI3.AbVar PicDict

theorem kClass_mul {k : Type} [Field k] {X : AbVar k} {P : Over (Spec (CommRingCat.of k))}
    (rep : (picardFunctor X.X.hom).obj.RepresentableBy P) (c c' : X.X.left.Pic) :
    letI := picardFunctorCommGrpObj X.X.hom rep
    kClass rep (c * c') = kClass rep c * kClass rep c' := by
  letI := picardFunctorCommGrpObj X.X.hom rep
  unfold kClass
  rw [Scheme.Pic.map_mul]
  exact homEquiv_symm_toPicardFunctor_mul X.X.hom rep _ _

/-- **`φ_c` is a homomorphism on `k`-points** (from L1, L2). -/
theorem phi_mul (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) {k : Type} [Field k] [IsAlgClosed k]
    (X : AbVar k) (c : X.X.left.Pic) (x y : AC.Kpt X) :
    AC.phi c (x * y) = AC.phi c x * AC.phi c y := by
  obtain ⟨P, ⟨rep⟩⟩ := h1 k X
  obtain ⟨B, j, hj⟩ := h2 k X P rep
  obtain ⟨lam, hlam⟩ := exists_hom_comp_eq_phiL rep hj c
  letI := picardFunctorCommGrpObj X.X.hom rep
  have hmon : IsMonHom j := hj.2.2
  apply kClass_injective rep
  rw [kClass_mul, ← kpt_comp_phiL, ← kpt_comp_phiL, ← kpt_comp_phiL, ← hlam,
    ← Category.assoc, ← Category.assoc, ← Category.assoc, MonObj.mul_comp, MonObj.mul_comp]

/-- **pic-dict's `MumfordSquareAC` is a theorem** given L1 and L2. -/
theorem mumfordSquareAC_of_open (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar) : MumfordSquareAC := by
  intro k _ _ X c x y
  have h := phi_mul h1 h2 X c x y
  simp only [AC.phi] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  rw [h]
  simp only [mul_assoc, mul_comm, mul_left_comm, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel,
    mul_one]

end PhiSurj

#print axioms PhiSurj.mumfordSquareAC_of_open
