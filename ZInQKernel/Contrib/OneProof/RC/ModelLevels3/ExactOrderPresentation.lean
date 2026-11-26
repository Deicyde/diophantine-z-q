import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.CoordinateEvaluation
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.ShortWeights

/-! # A weighted polynomial presentation of the short exact-order cover -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion
open scoped Polynomial

section Roots

variable {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
  [Algebra A S] [Algebra A T]

private theorem adjoinRoot_mem_subalgebra (p : S[X]) (f : AdjoinRoot p →ₐ[A] T)
    (B : Subalgebra A T)
    (hc : ∀ s, f (AdjoinRoot.of p s) ∈ B)
    (hr : f (AdjoinRoot.root p) ∈ B) (z : AdjoinRoot p) :
    f z ∈ B := by
  induction z using AdjoinRoot.induction_on with
  | ih q =>
    induction q using Polynomial.induction_on' with
    | add q r hq hr' => simpa only [map_add] using B.add_mem hq hr'
    | monomial i s =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_C]
      rw [map_mul, map_pow]
      exact B.mul_mem (hc s) (B.pow_mem hr i)

end Roots

section Exact

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A) [W.IsElliptic]
  {n : ℕ} (hn : IsUnit ((n + 2 : ℕ) : A))

/-- The affine abscissa on the exact-order factor, including level two. -/
noncomputable def exactOrderX : ExactOrderAlgebra W hn :=
  affineToExactOrder W hn (torsionChartX W (n + 2))

/-- The affine ordinate on the short exact-order factor. The two-torsion
branch has ordinate zero. -/
noncomputable def exactOrderY : ExactOrderAlgebra W hn :=
  affineToExactOrder W hn (torsionChartY W (n + 2))

set_option backward.isDefEq.respectTransparency false in
private theorem exactOrder_mem_subalgebra (B : Subalgebra A (ExactOrderAlgebra W hn))
    (hx : exactOrderX W hn ∈ B) (hy : exactOrderY W hn ∈ B)
    (z : ExactOrderAlgebra W hn) : z ∈ B := by
  obtain ⟨s, hs⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
    (S := ClopenFactor (exactOrderIdempotent W hn))
    _ (exactOrderIdempotent_idempotent W hn) z
  change affineToExactOrder W hn s = z at hs
  rw [← hs]
  obtain _ | n := n
  · have hi : (1 : AdjoinRoot (W.preΨ' 2)) = 0 := by
      rw [← map_one (AdjoinRoot.mk _), AdjoinRoot.mk_eq_zero, preΨ'_two]
    have hzero (r : AdjoinRoot (W.preΨ' 2)) : r = 0 := by
      conv_lhs => rw [← mul_one r, hi, mul_zero]
    have hzero' (r : AdjoinRoot (unramifiedOrdinate W 2)) : r = 0 := by
      have h := congrArg (AdjoinRoot.of (unramifiedOrdinate W 2)) hi
      rw [map_one, map_zero] at h
      conv_lhs => rw [← mul_one r, h, mul_zero]
    let f : AdjoinRoot (branchPolynomial W 2) →ₐ[A] ExactOrderAlgebra W hn :=
      { toFun := fun r => affineToExactOrder W hn (0, r)
        map_one' := by
          change affineToExactOrder W hn (0, 1) = 1
          rw [← show (1 : AffineTorsionAlgebra W 2) = (0, 1) from Prod.ext (hzero' 1) rfl]
          exact map_one _
        map_zero' := map_zero (affineToExactOrder W hn)
        map_add' := fun a b => by
          rw [← map_add]
          exact congrArg (affineToExactOrder W hn) (Prod.ext (zero_add _).symm rfl)
        map_mul' := fun a b => by
          rw [← map_mul]
          exact congrArg (affineToExactOrder W hn) (Prod.ext (zero_mul _).symm rfl)
        commutes' := fun a => by
          rw [← (affineToExactOrder W hn).commutes a]
          exact congrArg (affineToExactOrder W hn) (Prod.ext (hzero' _).symm rfl) }
    have hr : f (AdjoinRoot.root _) ∈ B := by
      change affineToExactOrder W hn (0, AdjoinRoot.root _) ∈ B
      simpa only [exactOrderX, torsionChartX, hzero' (AdjoinRoot.of _ (AdjoinRoot.root _))] using hx
    rw [show s = (0, s.2) from Prod.ext (hzero' s.1) rfl]
    exact adjoinRoot_mem_subalgebra _ f B (fun a => by
      change f (algebraMap A _ a) ∈ B
      rw [f.commutes]
      exact B.algebraMap_mem a) hr s.2
  · let f := quadraticToExactOrder W hn
    rw [← quadraticToExactOrder_apply]
    apply adjoinRoot_mem_subalgebra _ f B _ _
    · let g := f.comp (AdjoinRoot.ofAlgHom A (unramifiedOrdinate W (n + 3)))
      exact adjoinRoot_mem_subalgebra _ g B (fun a => by
        change g (algebraMap A _ a) ∈ B
        rw [g.commutes]
        exact B.algebraMap_mem a) (by
        change f (torsionChartX W (n + 3)).1 ∈ B
        rwa [quadraticToExactOrder_apply])
    · change f (torsionChartY W (n + 3)).1 ∈ B
      rwa [quadraticToExactOrder_apply]

end Exact

variable {R : Type*} [CommRing R] {n : ℕ} (hn : IsUnit ((n + 2 : ℕ) : ShortBase R))
  [Algebra R (ExactOrderAlgebra (shortFamily R) hn)]
  [IsScalarTower R (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn)]

/-- The coordinates of the universal affine exact generator over the
whole short locus, in order (a_4,a_6,x,y,\Delta^{-1}). -/
noncomputable def exactOrderShortCoordinates (i : Fin 5) :
    ExactOrderAlgebra (shortFamily R) hn :=
  match i.val with
  | 0 => algebraMap (ShortBase R) _ (shortFamily R).a₄
  | 1 => algebraMap (ShortBase R) _ (shortFamily R).a₆
  | 2 => exactOrderX (shortFamily R) hn
  | 3 => exactOrderY (shortFamily R) hn
  | _ => algebraMap (ShortBase R) _ (IsLocalization.Away.invSelf (shortEquation R).Δ)

/-- Evaluation of the polynomial presentation on the specified
coefficients, coordinates and inverse discriminant. -/
noncomputable def exactOrderShortPresentation :
    MvPolynomial (Fin 5) R →ₐ[R] ExactOrderAlgebra (shortFamily R) hn :=
  MvPolynomial.aeval (exactOrderShortCoordinates hn)

set_option backward.isDefEq.respectTransparency false in
/-- Every element of the universal exact-order algebra is a polynomial
in the five short coordinates. -/
theorem exactOrderShortPresentation_surjective :
    Function.Surjective (exactOrderShortPresentation hn) := by
  let F := exactOrderShortPresentation hn
  let A := ShortBase R
  let S := ExactOrderAlgebra (shortFamily R) hn
  have hc (a : A) : algebraMap A S a ∈ F.range := by
    have hpoly (p : MvPolynomial (Fin 2) R) :
        algebraMap A S (algebraMap (MvPolynomial (Fin 2) R) A p) ∈ F.range := by
      let g : MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 5) R :=
        MvPolynomial.aeval (fun i => MvPolynomial.X (if i = 0 then 0 else 1))
      have he : F.comp g =
          (IsScalarTower.toAlgHom R A S).comp (IsScalarTower.toAlgHom R _ A) := by
        ext i
        fin_cases i <;>
          simp [F, g, exactOrderShortPresentation, exactOrderShortCoordinates,
            shortFamily, shortEquation] <;> rfl
      exact F.mem_range.mpr ⟨g p, DFunLike.congr_fun he p⟩
    obtain ⟨⟨p, ⟨q, hq⟩⟩, hp⟩ := IsLocalization.surj
      (Submonoid.powers (shortEquation R).Δ) a
    obtain ⟨d, rfl⟩ := hq
    change a * algebraMap (MvPolynomial (Fin 2) R) A ((shortEquation R).Δ ^ d) =
      algebraMap (MvPolynomial (Fin 2) R) A p at hp
    have ha : a = algebraMap (MvPolynomial (Fin 2) R) A p *
        IsLocalization.Away.invSelf (shortEquation R).Δ ^ d := by
      calc
        a = a * 1 := (mul_one a).symm
        _ = a * (algebraMap (MvPolynomial (Fin 2) R) A (shortEquation R).Δ *
              IsLocalization.Away.invSelf (shortEquation R).Δ) ^ d := by
          rw [IsLocalization.Away.mul_invSelf, one_pow]
        _ = _ := by
          rw [mul_pow, ← mul_assoc, ← map_pow, hp]
    rw [ha, map_mul, map_pow]
    exact F.range.mul_mem (hpoly p) (F.range.pow_mem
      (F.mem_range.mpr ⟨MvPolynomial.X 4, MvPolynomial.aeval_X _ _⟩) d)
  let B : Subalgebra A S :=
    { F.range.toSubsemiring with algebraMap_mem' := hc }
  intro z
  apply F.mem_range.mp
  exact exactOrder_mem_subalgebra (shortFamily R) hn B
    (F.mem_range.mpr ⟨MvPolynomial.X 2, MvPolynomial.aeval_X _ _⟩)
    (F.mem_range.mpr ⟨MvPolynomial.X 3, MvPolynomial.aeval_X _ _⟩) z

#print axioms adjoinRoot_mem_subalgebra
#print axioms exactOrderX
#print axioms exactOrderY
#print axioms exactOrder_mem_subalgebra
#print axioms exactOrderShortCoordinates
#print axioms exactOrderShortPresentation
#print axioms exactOrderShortPresentation_surjective

end WeierstrassCurve.ModelLevels
