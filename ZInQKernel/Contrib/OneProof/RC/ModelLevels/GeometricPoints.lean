import ZInQKernel.Contrib.OneProof.RC.ModelLevels.AffinePointCoordinates
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.ExactOrder

/-! # The exact-order algebra over a geometric field -/

namespace WeierstrassCurve.ModelLevels

open Polynomial ModelTorsion WeierstrassCurve.Affine

variable {k : Type*} [Field k]
variable (W : WeierstrassCurve k) [W.IsElliptic] (N : ℕ)

private theorem no_common_branch {x : k} (hn : IsUnit (N : k)) (he : Even N)
    (hf : (W.preΨ' N).eval x = 0) (hg : W.Ψ₂Sq.eval x = 0) : False := by
  have hs := separable_xPolynomial W hn.ne_zero
  rw [xPolynomial, ite_eq_left he] at hs
  have h := Polynomial.aeval_ne_zero_of_isCoprime hs x
  simp only [aeval_def, Algebra.algebraMap_self, eval₂_id, eval_mul, derivative_mul,
    eval_add, hf, hg, mul_zero, zero_mul, zero_add, ne_self_iff_false, or_self] at h

private theorem branch_two_isUnit {N : ℕ} (hn : IsUnit (N : k)) (he : Even N) :
    IsUnit (2 : k) := by
  exact isUnit_of_dvd_unit (Nat.cast_dvd_cast he.two_dvd) hn

/-- The rational points of nonidentity torsion, read on the two affine charts.
For an even level, the branch abscissa has a unique ordinate. -/
noncomputable def affineTorsionCoordinateEquiv (hn : IsUnit (N : k)) :
    (AffineTorsionAlgebra W N →ₐ[k] k) ≃ affineCoordinates W N := by
  classical
  refine productFieldPoints.symm.trans <|
    (Equiv.sumCongr (quadraticChartPoints W N) (branchChartPoints W N)).trans ?_
  let f :
      ({xy : k × k // (W.preΨ' N).eval xy.1 = 0 ∧ W.toAffine.Equation xy.1 xy.2} ⊕
        {x : k // (branchPolynomial W N).eval x = 0}) → affineCoordinates W N :=
    Sum.elim
      (fun xy => ⟨xy.1, xy.2.2, by by_cases he : Even N <;> simp [xPolynomial, he, xy.2.1]⟩)
      (fun x => by
        have he : Even N := by
          by_contra he
          have hx := x.2
          simp [branchPolynomial, he] at hx
        have hx : W.Ψ₂Sq.eval x.1 = 0 := by simpa [branchPolynomial, he] using x.2
        have hroot := (branch_eq_zero_iff_existsUnique_ordinate W (branch_two_isUnit hn he)
          x.1).mp hx
        let y := hroot.choose
        have hy := hroot.choose_spec.1
        exact ⟨(x.1, y), hy.1, by simp [xPolynomial, he, hx]⟩)
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (Subtype.ext (congrArg (fun xy : affineCoordinates W N => xy.1) h))
    · have hab : a.1.1 = b.1 := congrArg (fun xy : affineCoordinates W N => xy.1.1) h
      have hb := b.2
      by_cases he : Even N
      · exact (no_common_branch W N hn he a.2.1
          (by simpa [branchPolynomial, he, hab] using hb)).elim
      · simp [branchPolynomial, he] at hb
    · have hab : b.1.1 = a.1 := congrArg (fun xy : affineCoordinates W N => xy.1.1) h.symm
      have ha := a.2
      by_cases he : Even N
      · exact (no_common_branch W N hn he b.2.1
          (by simpa [branchPolynomial, he, hab] using ha)).elim
      · simp [branchPolynomial, he] at ha
    · exact congrArg Sum.inr (Subtype.ext
        (congrArg (fun xy : affineCoordinates W N => xy.1.1) h))
  · intro xy
    by_cases hx : (W.preΨ' N).eval xy.1.1 = 0
    · exact ⟨Sum.inl ⟨xy.1, hx, xy.2.1⟩, Subtype.ext rfl⟩
    · have hN : Even N := by
        by_contra he
        exact hx (by simpa [xPolynomial, he] using xy.2.2)
      have hx' : W.Ψ₂Sq.eval xy.1.1 = 0 := by
        simpa [xPolynomial, hN, hx] using xy.2.2
      let a : {x : k // (branchPolynomial W N).eval x = 0} :=
        ⟨xy.1.1, by simpa [branchPolynomial, hN] using hx'⟩
      refine ⟨Sum.inr a, ?_⟩
      have hunique := (branch_eq_zero_iff_existsUnique_ordinate W
        (branch_two_isUnit hn hN) a.1).mp hx'
      have hy : 2 * xy.1.2 + (W.a₁ * xy.1.1 + W.a₃) = 0 := by
        have hy' := (eval_Ψ₂Sq_eq_zero_iff W xy.2.1).mp hx'
        rw [WeierstrassCurve.Affine.negY] at hy'
        linear_combination hy'
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact (hunique.choose_spec.2 xy.1.2 ⟨xy.2.1, hy⟩).symm

/-- The torsion equations read as nonidentity points killed by the level. -/
noncomputable def affineTorsionPoints [DecidableEq k] (hn : IsUnit (N : k)) :
    (AffineTorsionAlgebra W N →ₐ[k] k) ≃ {P : W.toAffine.Point // P ≠ 0 ∧ N • P = 0} :=
  (affineTorsionCoordinateEquiv W N hn).trans <| Equiv.ofBijective
    (fun xy =>
      let h := W.toAffine.equation_iff_nonsingular.mp xy.2.1
      ⟨Point.some xy.1.1 xy.1.2 h, Point.some_ne_zero h,
        (nsmul_some_eq_zero_iff W N h).2 xy.2.2⟩)
    (by
      constructor
      · intro xy xy' h
        rcases Point.some.inj (congrArg Subtype.val h) with ⟨hx, hy⟩
        exact Subtype.ext (Prod.ext hx hy)
      · rintro ⟨(_ | ⟨x, y, h⟩), hne, ht⟩
        · exact (hne rfl).elim
        · exact ⟨⟨(x, y), h.1, (nsmul_some_eq_zero_iff W N h).1 ht⟩, Subtype.ext rfl⟩)

#print axioms no_common_branch
#print axioms branch_two_isUnit
#print axioms affineTorsionCoordinateEquiv
#print axioms affineTorsionPoints

end WeierstrassCurve.ModelLevels
