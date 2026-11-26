import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.QuadraticFactor

/-! # The coordinates of the universal generator -/

namespace WeierstrassCurve.ModelLevels

open Polynomial ModelTorsion WeierstrassCurve.Affine
open scoped TensorProduct

variable {A k : Type*} [CommRing A] [Field k] [Algebra A k] [DecidableEq k]

/-- The abscissa and ordinate on the affine exact-order cover. For levels
greater than two every field-valued point is on the quadratic chart. -/
noncomputable def generatorX (W : WeierstrassCurve A) [W.IsElliptic]
    {n : ℕ} (hN : IsUnit ((n + 3 : ℕ) : A)) : ExactOrderAlgebra W hN :=
  (affineToExactOrder W hN) (torsionChartX W (n + 3))

/-- The ordinate root on the exact-order cover at levels greater than two. -/
noncomputable def generatorY (W : WeierstrassCurve A) [W.IsElliptic]
    {n : ℕ} (hN : IsUnit ((n + 3 : ℕ) : A)) : ExactOrderAlgebra W hN :=
  (affineToExactOrder W hN) (torsionChartY W (n + 3))

set_option backward.isDefEq.respectTransparency false in
/-- The field reading of the relative cover uses the two evaluated root
coordinates. This identifies exactly which universal coordinates enter
the coprime multiplication formulas. -/
theorem exactOrderFibrePoints_coordinates (W : WeierstrassCurve A) [W.IsElliptic]
    {n : ℕ} (hN : IsUnit ((n + 3 : ℕ) : A)) (f : ExactOrderAlgebra W hN →ₐ[A] k) :
    let V := W.map (algebraMap A k)
    ∃ h : V.toAffine.Nonsingular (f (generatorX W hN)) (f (generatorY W hN)),
      (exactOrderFibrePoints W hN f).1 = Point.some _ _ h := by
  let V := W.map (algebraMap A k)
  let hNk : IsUnit ((n + 3 : ℕ) : k) := by simpa only [map_natCast] using hN.map (algebraMap A k)
  let e := exactOrderBaseChange (B := k) W hN
  let f' := (AlgHom.liftEquiv A k _ k f).comp e.symm.toAlgHom
  let g := f'.comp (affineToExactOrder V hNk)
  have hg (s : AffineTorsionAlgebra W (n + 3)) :
      g (affineTorsionAlgebraBaseChange W (n + 3) (1 ⊗ₜ[A] s)) =
        f (affineToExactOrder W hN s) := by
    change f' (affineToExactOrder V hNk _) = _
    rw [← exactOrderBaseChange_affine W hN (1 : k) s]
    change (AlgHom.liftEquiv A k _ k f) (e.symm (e _)) = _
    simp
  have hP : (exactOrderFibrePoints W hN f).1 = (affineTorsionPoints V _ hNk g).1 := rfl
  let q := f'.comp (quadraticToExactOrder V hNk)
  have hq : productFieldPoints (Sum.inl q) = g := by
    ext z
    change f' (quadraticToExactOrder V hNk z.1) = f' (affineToExactOrder V hNk z)
    rw [quadraticToExactOrder_apply]
  have hx := hg (torsionChartX W (n + 3))
  have hy := hg (torsionChartY W (n + 3))
  rw [affineTorsionBaseChange_x, ← hq] at hx
  rw [affineTorsionBaseChange_y, ← hq] at hy
  change q (AdjoinRoot.of _ (AdjoinRoot.root _)) = f (generatorX W hN) at hx
  change q (AdjoinRoot.root _) = f (generatorY W hN) at hy
  rw [hP, ← hq]
  simp only [affineTorsionPoints, affineTorsionCoordinateEquiv, Equiv.trans_apply,
    Equiv.symm_apply_apply, Equiv.sumCongr, Equiv.coe_fn_mk, Sum.map_inl,
    Equiv.ofBijective, Sum.elim_inl]
  let ns := V.toAffine.equation_iff_nonsingular.mp (quadraticChartPoints V (n + 3) q).2.2
  change ∃ h : V.toAffine.Nonsingular (f (generatorX W hN)) (f (generatorY W hN)),
    Point.some (q (AdjoinRoot.of _ (AdjoinRoot.root _))) (q (AdjoinRoot.root _)) ns =
      Point.some _ _ h
  have hns : V.toAffine.Nonsingular (f (generatorX W hN)) (f (generatorY W hN)) := hx ▸ hy ▸ ns
  refine ⟨hns, ?_⟩
  rw [Point.some.injEq]
  exact ⟨hx, hy⟩

#print axioms generatorX
#print axioms generatorY
#print axioms exactOrderFibrePoints_coordinates

end WeierstrassCurve.ModelLevels
