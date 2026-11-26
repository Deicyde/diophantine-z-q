import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.CoordinateEvaluation
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.FieldTests

/-! # Lifting exact-order coordinates from field tests -/

namespace WeierstrassCurve.ModelLevels

open Polynomial ModelTorsion

universe u

variable {A : Type*} {T : Type u} [CommRing A] [CommRing T] [Algebra A T]
  (W : WeierstrassCurve A) [W.IsElliptic] {n : ℕ} (hN : IsUnit ((n + 3 : ℕ) : A))

/-- The exact-order coordinate ring is determined by the two root
generators when the level is greater than two. -/
theorem exactOrder_algHom_ext {f g : ExactOrderAlgebra W hN →ₐ[A] T}
    (hx : f (generatorX W hN) = g (generatorX W hN))
    (hy : f (generatorY W hN) = g (generatorY W hN)) : f = g := by
  let j := quadraticToExactOrder W hN
  have eq : f.comp j = g.comp j := by
    apply AdjoinRoot.algHom_ext'
    · apply AdjoinRoot.algHom_ext
      change f (j (torsionChartX W (n + 3)).1) = g (j (torsionChartX W (n + 3)).1)
      rw [quadraticToExactOrder_apply]
      exact hx
    · change f (j (torsionChartY W (n + 3)).1) = g (j (torsionChartY W (n + 3)).1)
      rw [quadraticToExactOrder_apply]
      exact hy
  ext s
  obtain ⟨z, rfl⟩ :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
      (S := ClopenFactor (exactOrderIdempotent W hN))
      _ (exactOrderIdempotent_idempotent W hN) s
  change f (affineToExactOrder W hN z) = g (affineToExactOrder W hN z)
  rw [← quadraticToExactOrder_apply]
  exact DFunLike.congr_fun eq z.1

private theorem hom_eval_adjoined_root {R U V : Type*} [CommRing R] [CommRing U]
    [CommRing V] [Algebra R U] [Algebra R V] {p : U[X]} (f : AdjoinRoot p →ₐ[R] V) :
    p.eval₂ ((f.comp (AdjoinRoot.ofAlgHom R p)).toRingHom) (f (AdjoinRoot.root p)) = 0 := by
  change p.eval₂ (f.toRingHom.comp (AdjoinRoot.of p)) (f.toRingHom (AdjoinRoot.root p)) = 0
  rw [← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- If a pair of coordinates over a reduced algebra belongs to the
exact-order locus after every field-valued test, it defines a unique
point of that locus over the algebra. -/
theorem exists_exactOrder_map_of_fields [IsReduced T] (x y : T)
    (h : ∀ (k : Type u) [Field k] [Algebra A k] (f : T →ₐ[A] k),
      ∃ g : ExactOrderAlgebra W hN →ₐ[A] k,
        g (generatorX W hN) = f x ∧ g (generatorY W hN) = f y) :
    ∃ g : ExactOrderAlgebra W hN →ₐ[A] T,
      g (generatorX W hN) = x ∧ g (generatorY W hN) = y := by
  let p := W.preΨ' (n + 3)
  let q := unramifiedOrdinate W (n + 3)
  let j := quadraticToExactOrder W hN
  have hx : p.eval₂ (algebraMap A T) x = 0 := by
    apply eq_of_eq_at_fields (A := A)
    intro k _ _ f
    obtain ⟨g, hx, _⟩ := h k f
    let gx := (g.comp j).comp (AdjoinRoot.ofAlgHom A q)
    have hroot : gx (AdjoinRoot.root p) = f x := by
      change g (j (torsionChartX W (n + 3)).1) = _
      rw [quadraticToExactOrder_apply]
      exact hx
    have hcoeff : f.toRingHom.comp (algebraMap A T) = gx.toRingHom.comp (AdjoinRoot.of p) :=
      f.comp_algebraMap.trans gx.comp_algebraMap.symm
    rw [map_zero]
    change f.toRingHom (p.eval₂ (algebraMap A T) x) = 0
    rw [Polynomial.hom_eval₂, hcoeff]
    change p.eval₂ _ (f x) = 0
    rw [← hroot]
    exact hom_eval_adjoined_root gx
  let fx := AdjoinRoot.liftAlgHom p (Algebra.ofId A T) x hx
  have hfx : fx (AdjoinRoot.root p) = x := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hy : q.eval₂ fx.toRingHom y = 0 := by
    apply eq_of_eq_at_fields (A := A)
    intro k _ _ f
    obtain ⟨g, hx, hy⟩ := h k f
    have hcoeff : f.comp fx = (g.comp j).comp (AdjoinRoot.ofAlgHom A q) := by
      apply AdjoinRoot.algHom_ext
      change f (fx (AdjoinRoot.root p)) = g (j (torsionChartX W (n + 3)).1)
      rw [hfx, quadraticToExactOrder_apply]
      exact hx.symm
    have hroot : (g.comp j) (AdjoinRoot.root q) = f y := by
      change g (j (torsionChartY W (n + 3)).1) = _
      rw [quadraticToExactOrder_apply]
      exact hy
    rw [map_zero]
    change f.toRingHom (q.eval₂ fx.toRingHom y) = 0
    rw [Polynomial.hom_eval₂, ← show (f.comp fx).toRingHom = f.toRingHom.comp fx.toRingHom from rfl, hcoeff]
    change q.eval₂ _ (f y) = 0
    rw [← hroot]
    exact hom_eval_adjoined_root (g.comp j)
  let fy := AdjoinRoot.liftAlgHom q fx y hy
  let fj := fy.comp (AlgHom.fst A (AdjoinRoot q) (AdjoinRoot (branchPolynomial W (n + 3))))
  have he : fj (exactOrderIdempotent W hN) = 1 := by
    apply eq_of_eq_at_fields (A := A)
    intro k _ _ f
    obtain ⟨g, hx, hy⟩ := h k f
    have heq : f.comp fy = g.comp j := by
      apply AdjoinRoot.algHom_ext'
      · apply AdjoinRoot.algHom_ext
        change f (fy (AdjoinRoot.of q (AdjoinRoot.root p))) = g (j (torsionChartX W (n + 3)).1)
        rw [AdjoinRoot.liftAlgHom_of, hfx, quadraticToExactOrder_apply]
        exact hx.symm
      · change f (fy (AdjoinRoot.root q)) = g (j (torsionChartY W (n + 3)).1)
        rw [AdjoinRoot.liftAlgHom_root, quadraticToExactOrder_apply]
        exact hy.symm
    rw [map_one]
    change (f.comp fy) (exactOrderIdempotent W hN).1 = 1
    rw [heq, AlgHom.comp_apply, quadraticToExactOrder_apply]
    have hu : IsUnit ((affineToExactOrder W hN) (exactOrderIdempotent W hN)) :=
      IsLocalization.Away.algebraMap_isUnit (S := ClopenFactor (exactOrderIdempotent W hN)) _
    have hi := ((exactOrderIdempotent_idempotent W hN).map (affineToExactOrder W hN)).map g
    exact (IsIdempotentElem.iff_eq_one_of_isUnit (hu.map g)).mp hi
  have hu : IsUnit (fj (exactOrderIdempotent W hN)) := he.symm ▸ isUnit_one
  let g : ClopenFactor (exactOrderIdempotent W hN) →ₐ[A] T :=
    IsLocalization.Away.liftAlgHom _ hu
  refine ⟨g, ?_, ?_⟩
  · change g (affineToExactOrder W hN _) = _
    rw [show g (affineToExactOrder W hN (torsionChartX W (n + 3))) = fj (torsionChartX W (n + 3))
      from IsLocalization.Away.lift_eq (S := ClopenFactor (exactOrderIdempotent W hN)) _ hu _]
    change fy (AdjoinRoot.of q (AdjoinRoot.root p)) = x
    rw [AdjoinRoot.liftAlgHom_of, hfx]
  · change g (affineToExactOrder W hN _) = _
    rw [show g (affineToExactOrder W hN (torsionChartY W (n + 3))) = fj (torsionChartY W (n + 3))
      from IsLocalization.Away.lift_eq (S := ClopenFactor (exactOrderIdempotent W hN)) _ hu _]
    exact AdjoinRoot.liftAlgHom_root q fx y hy

#print axioms exactOrder_algHom_ext
#print axioms hom_eval_adjoined_root
#print axioms exists_exactOrder_map_of_fields

end WeierstrassCurve.ModelLevels
