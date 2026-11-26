import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.AffineBaseChange

/-! # Field-valued points of the two affine torsion charts -/

namespace WeierstrassCurve.ModelLevels

open Polynomial ModelTorsion

variable {k : Type*} [Field k]

private theorem hom_eval₂_root {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] {p : B[X]} (f : AdjoinRoot p →ₐ[R] C) :
    p.eval₂ (f.toRingHom.comp (AdjoinRoot.of p)) (f (AdjoinRoot.root p)) = 0 := by
  change p.eval₂ (f.toRingHom.comp (AdjoinRoot.of p)) (f.toRingHom (AdjoinRoot.root p)) = 0
  rw [← hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the two successive root generators reads the abscissa and
ordinate on the quadratic chart. -/
noncomputable def quadraticChartPoints (W : WeierstrassCurve k) (n : ℕ) :
    (AdjoinRoot (unramifiedOrdinate W n) →ₐ[k] k) ≃
      {xy : k × k // (W.preΨ' n).eval xy.1 = 0 ∧ W.toAffine.Equation xy.1 xy.2} := by
  let p := W.preΨ' n
  let q := unramifiedOrdinate W n
  let i : AdjoinRoot p →ₐ[k] AdjoinRoot q := IsScalarTower.toAlgHom k _ _
  have ordinateMap (f : AdjoinRoot p →ₐ[k] k) :
      q.map f.toRingHom = ordinatePolynomial W (f (AdjoinRoot.root p)) := by
    change (ordinatePolynomial (W.map (algebraMap k (AdjoinRoot p))) _).map _ = _
    rw [map_ordinatePolynomial, WeierstrassCurve.map_map]
    have hcoeff : f.toRingHom.comp (algebraMap k (AdjoinRoot p)) = RingHom.id k := by
      ext a
      exact f.commutes a
    rw [hcoeff, WeierstrassCurve.map_id]
    rfl
  refine {
    toFun := fun f => ⟨(f (i (AdjoinRoot.root p)), f (AdjoinRoot.root q)), ?_⟩
    invFun := fun xy => ?_
    left_inv := ?_
    right_inv := ?_ }
  · constructor
    · change p.eval ((f.comp i) (AdjoinRoot.root p)) = 0
      exact AdjoinRoot.aeval_algHom_eq_zero p (f.comp i)
    · apply (eval_ordinatePolynomial_eq_zero_iff W _ _).mp
      change (ordinatePolynomial W ((f.comp i) (AdjoinRoot.root p))).eval
        (f (AdjoinRoot.root q)) = 0
      rw [← ordinateMap (f.comp i), eval_map]
      exact hom_eval₂_root f
  · have hx : p.eval₂ (RingHom.id k) xy.1.1 = 0 := xy.2.1
    let f := AdjoinRoot.liftAlgHom p (AlgHom.id k k) xy.1.1 hx
    have hroot : f (AdjoinRoot.root p) = xy.1.1 := AdjoinRoot.liftAlgHom_root _ _ _ _
    have hy : q.eval₂ f.toRingHom xy.1.2 = 0 := by
      rw [← eval_map, ordinateMap, hroot]
      exact (eval_ordinatePolynomial_eq_zero_iff W _ _).mpr xy.2.2
    exact AdjoinRoot.liftAlgHom q f xy.1.2 hy
  · intro f
    apply AdjoinRoot.algHom_ext'
    · apply AdjoinRoot.algHom_ext
      simp only [AlgHom.comp_apply]
      have hOf : AdjoinRoot.ofAlgHom k q (AdjoinRoot.root p) =
          AdjoinRoot.of q (AdjoinRoot.root p) := rfl
      rw [hOf, AdjoinRoot.liftAlgHom_of, AdjoinRoot.liftAlgHom_root]
      rfl
    · exact AdjoinRoot.liftAlgHom_root _ _ _ _
  · intro xy
    apply Subtype.ext
    apply Prod.ext
    · change (AdjoinRoot.liftAlgHom q _ _ _) (AdjoinRoot.of q (AdjoinRoot.root p)) = _
      rw [AdjoinRoot.liftAlgHom_of, AdjoinRoot.liftAlgHom_root]
    · exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- A point of the branch chart is the root of its single equation. -/
noncomputable def branchChartPoints (W : WeierstrassCurve k) (n : ℕ) :
    (AdjoinRoot (branchPolynomial W n) →ₐ[k] k) ≃ {x : k // (branchPolynomial W n).eval x = 0} where
  toFun f := ⟨f (AdjoinRoot.root _), by
    simpa only [aeval_def, Algebra.algebraMap_self, eval₂_id] using
      (AdjoinRoot.aeval_algHom_eq_zero (branchPolynomial W n) f)⟩
  invFun x := AdjoinRoot.liftAlgHom _ (AlgHom.id k k) x.1 x.2
  left_inv f := AdjoinRoot.algHom_ext (AdjoinRoot.liftAlgHom_root _ _ _ _)
  right_inv x := Subtype.ext (AdjoinRoot.liftAlgHom_root _ _ _ _)

/-- A field-valued point of a binary product comes from exactly one factor. -/
noncomputable def productFieldPoints {R B C : Type*} [CommRing R] [Algebra R k]
    [CommRing B] [CommRing C] [Algebra R B] [Algebra R C] :
    ((B →ₐ[R] k) ⊕ (C →ₐ[R] k)) ≃ (B × C →ₐ[R] k) := by
  let f : ((B →ₐ[R] k) ⊕ (C →ₐ[R] k)) → (B × C →ₐ[R] k) :=
    Sum.elim (fun x => x.comp (AlgHom.fst R B C)) (fun y => y.comp (AlgHom.snd R B C))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro (x | x) (y | y) h
    · congr 1
      ext b
      exact DFunLike.congr_fun h (b, 0)
    · have he : (1 : k) = 0 := by simpa [f] using DFunLike.congr_fun h (1, 0)
      exact (one_ne_zero he).elim
    · have he : (1 : k) = 0 := by simpa [f] using DFunLike.congr_fun h.symm (1, 0)
      exact (one_ne_zero he).elim
    · congr 1
      ext c
      exact DFunLike.congr_fun h (0, c)
  · intro x
    have hm : x (1, 0) * x (0, 1) = 0 := by
      rw [← map_mul, show (1, 0) * (0, 1) = (0 : B × C) by ext <;> simp, map_zero]
    rcases mul_eq_zero.mp hm with h₁ | h₂
    · let g := AlgHom.snd R B C
      have hs : Function.Surjective g := fun c => ⟨(0, c), rfl⟩
      have hk : RingHom.ker g ≤ RingHom.ker x := by
        rintro ⟨b, c⟩ h
        have hc : c = 0 := h
        subst c
        change x (b, 0) = 0
        calc
          x (b, 0) = x ((1, 0) * (b, 0)) := by simp
          _ = 0 := by rw [map_mul, h₁, zero_mul]
      exact ⟨Sum.inr (g.liftOfSurjective hs x hk), AlgHom.liftOfSurjective_comp g hs x hk⟩
    · let g := AlgHom.fst R B C
      have hs : Function.Surjective g := fun b => ⟨(b, 0), rfl⟩
      have hk : RingHom.ker g ≤ RingHom.ker x := by
        rintro ⟨b, c⟩ h
        have hb : b = 0 := h
        subst b
        change x (0, c) = 0
        calc
          x (0, c) = x ((0, 1) * (0, c)) := by simp
          _ = 0 := by rw [map_mul, h₂, zero_mul]
      exact ⟨Sum.inl (g.liftOfSurjective hs x hk), AlgHom.liftOfSurjective_comp g hs x hk⟩

#print axioms hom_eval₂_root
#print axioms quadraticChartPoints
#print axioms branchChartPoints
#print axioms productFieldPoints

end WeierstrassCurve.ModelLevels
