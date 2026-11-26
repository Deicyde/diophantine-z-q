import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.FibrePoints

/-! # Removing the two-torsion chart at levels greater than two -/

namespace WeierstrassCurve.ModelLevels

open Polynomial ModelTorsion

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A) [W.IsElliptic]

set_option backward.isDefEq.respectTransparency false in
private theorem exactOrderIdempotent_snd {n : ℕ} (hN : IsUnit ((n + 3 : ℕ) : A)) :
    (exactOrderIdempotent W hN).2 = 0 := by
  by_cases he : Even (n + 3)
  · let hd : 2 ∣ n + 3 := he.two_dvd
    let d : {d // d ∈ (n + 3).properDivisors} :=
      ⟨2, Nat.mem_properDivisors.mpr ⟨hd, by omega⟩⟩
    let z := divisorIdempotent W hN hd
    have hz : restrictAffineTorsion W hN hd z = 0 :=
      RingHom.mem_ker.mp ((divisorIdempotent_spec W hN hd).2.symm ▸
        Ideal.subset_span (Set.mem_singleton z))
    have hb : branchPolynomial W 2 = branchPolynomial W (n + 3) := by
      simp [branchPolynomial, he]
    have hres : (restrictAffineTorsion W hN hd z).2 =
        (AdjoinRoot.algEquivOfEq A _ _ hb.symm) z.2 := by
      unfold restrictAffineTorsion affineDivisorMap
      change AdjoinRoot.algHomOfDvd A _ _ (dvd_of_eq hb) z.2 = _
      rw [AdjoinRoot.coe_algEquivOfEq]
    have hzero : z.2 = 0 := (AdjoinRoot.algEquivOfEq A _ _ hb.symm).injective (by
      rw [← hres, hz, map_zero]
      rfl)
    classical
    change (AlgHom.snd A _ _) (exactOrderIdempotent W hN) = 0
    rw [exactOrderIdempotent, map_prod]
    apply Finset.prod_eq_zero (i := d) (Finset.mem_attach _ _)
    exact hzero
  · have h1 : (1 : AdjoinRoot (branchPolynomial W (n + 3))) = 0 := by
      have h := AdjoinRoot.eval₂_root (branchPolynomial W (n + 3))
      have hb : branchPolynomial W (n + 3) = 1 := by simp [branchPolynomial, he]
      rw [show ∀ x : AdjoinRoot (branchPolynomial W (n + 3)),
        (branchPolynomial W (n + 3)).eval₂ (AdjoinRoot.of _) x = 1 by
          intro x
          calc
            _ = (1 : A[X]).eval₂ (AdjoinRoot.of (branchPolynomial W (n + 3))) x :=
              congrArg (fun p : A[X] => p.eval₂ (AdjoinRoot.of (branchPolynomial W (n + 3))) x) hb
            _ = 1 := eval₂_one _ _] at h
      exact h
    rw [← mul_one (exactOrderIdempotent W hN).2, h1, mul_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem exactOrder_kills_branch {n : ℕ} (hN : IsUnit ((n + 3 : ℕ) : A))
    (x : AdjoinRoot (branchPolynomial W (n + 3))) :
    affineToExactOrder W hN (0, x) = 0 := by
  let g := affineToExactOrder W hN
  let e := exactOrderIdempotent W hN
  have he : e * (0, x) = 0 := by
    apply Prod.ext
    · change e.1 * 0 = 0
      rw [mul_zero]
    · change e.2 * x = 0
      rw [exactOrderIdempotent_snd W hN, zero_mul]
  have hu : IsUnit (g e) := IsLocalization.Away.algebraMap_isUnit (S := ClopenFactor e) e
  apply hu.mul_right_injective
  change g e * g (0, x) = g e * 0
  rw [← map_mul, he, map_zero, mul_zero]

private theorem exactOrder_ignores_branch {n : ℕ} (hN : IsUnit ((n + 3 : ℕ) : A))
    (x : AffineTorsionAlgebra W (n + 3)) :
    affineToExactOrder W hN (x.1, 0) = affineToExactOrder W hN x := by
  let g := affineToExactOrder W hN
  have he : x = (x.1, 0) + (0, x.2) := by
    apply Prod.ext <;> simp
  conv_rhs => rw [he]
  rw [map_add, exactOrder_kills_branch W hN, add_zero]

set_option backward.isDefEq.respectTransparency false in
/-- For levels at least three the exact-order factor is a quotient of the
quadratic chart. The branch of order two vanishes in that factor. -/
noncomputable def quadraticToExactOrder {n : ℕ} (hN : IsUnit ((n + 3 : ℕ) : A)) :
    AdjoinRoot (unramifiedOrdinate W (n + 3)) →ₐ[A] ExactOrderAlgebra W hN where
  toFun x := affineToExactOrder W hN (x, 0)
  map_one' := (exactOrder_ignores_branch W hN 1).trans (map_one _)
  map_zero' := map_zero _
  map_add' x y := by
    rw [← map_add]
    congr 1
    apply Prod.ext <;> simp
  map_mul' x y := by
    rw [← map_mul]
    congr 1
  commutes' a := (exactOrder_ignores_branch W hN (algebraMap A _ a)).trans
    ((affineToExactOrder W hN).commutes a)

theorem quadraticToExactOrder_apply {n : ℕ} (hN : IsUnit ((n + 3 : ℕ) : A))
    (x : AffineTorsionAlgebra W (n + 3)) :
    quadraticToExactOrder W hN x.1 = affineToExactOrder W hN x :=
  exactOrder_ignores_branch W hN x

#print axioms exactOrderIdempotent_snd
#print axioms exactOrder_kills_branch
#print axioms exactOrder_ignores_branch
#print axioms quadraticToExactOrder
#print axioms quadraticToExactOrder_apply

end WeierstrassCurve.ModelLevels
