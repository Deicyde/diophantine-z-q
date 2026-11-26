import ZInQKernel.Contrib.OneProof.RC.ModelLevels.GeometricPoints

/-! # Exact order in the geometric point group -/

namespace WeierstrassCurve.ModelLevels

open Polynomial ModelTorsion WeierstrassCurve.Affine

variable {k : Type*} [Field k] (W : WeierstrassCurve k) [W.IsElliptic]

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_coordinates {d N : ℕ} (hN : IsUnit (N : k)) (hdN : d ∣ N)
    (f : AffineTorsionAlgebra W d →ₐ[k] k) :
    (affineTorsionCoordinateEquiv W N hN (f.comp (restrictAffineTorsion W hN hdN))).1 =
      (affineTorsionCoordinateEquiv W d (isUnit_of_dvd_unit (Nat.cast_dvd_cast hdN) hN) f).1 := by
  classical
  let fₙ := restrictAffineTorsion W hN hdN
  obtain ⟨f', rfl⟩ := productFieldPoints.surjective f
  rcases f' with f' | f'
  · let g₀ := AdjoinRoot.algHomOfDvd k (W.preΨ' N) (W.preΨ' d)
      (divisor_polynomials_dvd W hN hdN).2
    have h₀ : g₀.toRingHom (AdjoinRoot.root (W.preΨ' N)) = AdjoinRoot.root (W.preΨ' d) :=
      AdjoinRoot.algHomOfDvd_root (R := k) _ _ _
    have hd : unramifiedOrdinate W d ∣ (unramifiedOrdinate W N).map g₀.toRingHom := by
      unfold unramifiedOrdinate
      rw [map_ordinatePolynomial, WeierstrassCurve.map_map,
        show g₀.toRingHom.comp (algebraMap k _) = algebraMap k _ from g₀.comp_algebraMap, h₀]
    let g := AdjoinRoot.mapAlgHom g₀ _ _ hd
    have hg : (productFieldPoints (Sum.inl f')).comp fₙ =
        productFieldPoints (Sum.inl (f'.comp g)) := rfl
    change (affineTorsionCoordinateEquiv W N hN
      ((productFieldPoints (Sum.inl f')).comp fₙ)).1 = _
    rw [hg]
    simp only [affineTorsionCoordinateEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.sumCongr, Equiv.coe_fn_mk, Sum.map_inl, Equiv.ofBijective, Sum.elim_inl]
    apply Prod.ext
    · change f' (g (AdjoinRoot.of _ (AdjoinRoot.root _))) = f' (AdjoinRoot.of _ (AdjoinRoot.root _))
      change g₀ (AdjoinRoot.root (W.preΨ' N)) = AdjoinRoot.root (W.preΨ' d) at h₀
      simp [g, h₀]
    · change f' (g (AdjoinRoot.root _)) = f' (AdjoinRoot.root _)
      simp [g]
  · have hb : branchPolynomial W d ∣ branchPolynomial W N := by
      by_cases he : Even d
      · obtain ⟨m, rfl⟩ := hdN
        simp [branchPolynomial, he, he.mul_right m]
      · simp [branchPolynomial, he]
    let g := AdjoinRoot.algHomOfDvd k _ _ hb
    have hg : (productFieldPoints (Sum.inr f')).comp fₙ =
        productFieldPoints (Sum.inr (f'.comp g)) := rfl
    change (affineTorsionCoordinateEquiv W N hN
      ((productFieldPoints (Sum.inr f')).comp fₙ)).1 = _
    rw [hg]
    simp only [affineTorsionCoordinateEquiv, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.sumCongr, Equiv.coe_fn_mk, Sum.map_inr, Equiv.ofBijective, Sum.elim_inr]
    have habscissa : (f'.comp g) (AdjoinRoot.root (branchPolynomial W N)) =
        f' (AdjoinRoot.root (branchPolynomial W d)) := by simp [g]
    refine Prod.ext habscissa ?_
    have he_d : Even d := by
      by_contra hd
      have hroot := (branchChartPoints W d f').2
      simp [branchPolynomial, hd] at hroot
    have hu : IsUnit (2 : k) :=
      isUnit_of_dvd_unit (Nat.cast_dvd_cast he_d.two_dvd)
        (isUnit_of_dvd_unit (Nat.cast_dvd_cast hdN) hN)
    have he_N : Even N := by
      obtain ⟨m, rfl⟩ := hdN
      exact he_d.mul_right m
    have hpoly {n : ℕ} (hn : Even n) (x : {x : k // (branchPolynomial W n).eval x = 0}) :
        W.Ψ₂Sq.eval x.1 = 0 := by simpa [branchPolynomial, hn] using x.2
    have hroot₁ := hpoly he_N (branchChartPoints W N (f'.comp g))
    have hroot₂ := hpoly he_d (branchChartPoints W d f')
    let Y₁ := (branch_eq_zero_iff_existsUnique_ordinate W hu _).mp hroot₁
    let Y₂ := (branch_eq_zero_iff_existsUnique_ordinate W hu _).mp hroot₂
    change Y₁.choose = Y₂.choose
    have hy₁ := Y₁.choose_spec.1.2
    have hy₂ := Y₂.choose_spec.1.2
    change (branchChartPoints W N (f'.comp g)).1 = (branchChartPoints W d f').1 at habscissa
    have hmul := congrArg (fun x : k => W.a₁ * x) habscissa
    apply mul_left_cancel₀ hu.ne_zero
    linear_combination hy₁ - hy₂ - hmul

/-- Divisor-level restriction does not change an affine torsion point's
underlying Weierstrass point. -/
theorem restrictAffineTorsion_point [DecidableEq k] {d N : ℕ} (hN : IsUnit (N : k))
    (hdN : d ∣ N) (f : AffineTorsionAlgebra W d →ₐ[k] k) :
    (affineTorsionPoints W N hN (f.comp (restrictAffineTorsion W hN hdN))).1 =
      (affineTorsionPoints W d (isUnit_of_dvd_unit (Nat.cast_dvd_cast hdN) hN) f).1 := by
  have h := restrict_coordinates W hN hdN f
  change Point.some _ _ _ = Point.some _ _ _
  rw [Point.some.injEq]
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

private noncomputable def clopenPoints {S : Type*} [CommRing S] [Algebra k S]
    (e : S) (he : IsIdempotentElem e) :
    (ClopenFactor e →ₐ[k] k) ≃ {f : S →ₐ[k] k // f e ≠ 0} := by
  let i : S →ₐ[k] ClopenFactor e := IsScalarTower.toAlgHom k _ _
  let f : (ClopenFactor e →ₐ[k] k) → {f : S →ₐ[k] k // f e ≠ 0} :=
    fun g => ⟨g.comp i, ((IsLocalization.Away.algebraMap_isUnit e).map g).ne_zero⟩
  apply Equiv.ofBijective f
  refine ⟨?_, ?_⟩
  · intro g h hEq
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem (S := ClopenFactor e) e he x
    exact DFunLike.congr_fun (congrArg Subtype.val hEq) y
  · intro g
    let h : ClopenFactor e →ₐ[k] k :=
      IsLocalization.Away.liftAlgHom e (f := g.1) (isUnit_iff_ne_zero.mpr g.2)
    refine ⟨h, Subtype.ext (AlgHom.ext ?_)⟩
    intro s
    exact IsLocalization.Away.lift_eq e (isUnit_iff_ne_zero.mpr g.2) s

private theorem product_idempotent_order_iff [DecidableEq k] {N : ℕ} (hN : IsUnit (N : k))
    (x : AffineTorsionAlgebra W N →ₐ[k] k) :
    x (exactOrderIdempotent W hN) ≠ 0 ↔
      addOrderOf (affineTorsionPoints W N hN x).1 = N := by
  classical
  rw [exactOrderIdempotent_eval_ne_zero_iff]
  let P := affineTorsionPoints W N hN x
  have hdiv : addOrderOf P.1 ∣ N := addOrderOf_dvd_of_nsmul_eq_zero P.2.2
  have hpos : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hN)
  constructor
  · intro hx
    change addOrderOf P.1 = N
    apply le_antisymm (Nat.le_of_dvd hpos hdiv)
    by_contra! hlt
    let e := affineTorsionPoints W (addOrderOf P.1)
      (isUnit_of_dvd_unit (Nat.cast_dvd_cast hdiv) hN)
    let y := e.symm ⟨P.1, P.2.1, addOrderOf_nsmul_eq_zero P.1⟩
    apply hx _ hdiv hlt
    refine ⟨y, (affineTorsionPoints W N hN).injective (Subtype.ext ?_)⟩
    rw [restrictAffineTorsion_point W hN hdiv]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · intro h d hd hlt ⟨y, hy⟩
    have hp := restrictAffineTorsion_point W hN hd y
    rw [hy] at hp
    have h' := addOrderOf_dvd_of_nsmul_eq_zero
      (affineTorsionPoints W d (isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) hN) y).2.2
    rw [← hp, h] at h'
    exact (Nat.not_le_of_gt hlt) (Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hd hpos) h')

/-- When the elliptic base is a field, its exact-order algebra points are
exactly the affine Weierstrass points of additive order `N`, including the
identity at level one. In particular this holds over algebraically closed
fields of characteristic prime to the level. -/
noncomputable def exactOrderPoints [DecidableEq k] {N : ℕ} (hN : IsUnit (N : k)) :
    (ExactOrderAlgebra W hN →ₐ[k] k) ≃ {P : W.toAffine.Point // addOrderOf P = N} := by
  have hpos : N ≠ 0 := by rintro rfl; simp at hN
  obtain _ | _ | N := N
  · exact (hpos rfl).elim
  · change (k →ₐ[k] k) ≃ _
    exact Equiv.ofBijective (fun _ => ⟨0, addOrderOf_zero⟩)
      ⟨fun f g _ => Subsingleton.elim f g, by
        rintro ⟨P, hp⟩
        exact ⟨AlgHom.id k k, Subtype.ext (AddMonoid.addOrderOf_eq_one_iff.mp hp).symm⟩⟩
  · change (ClopenFactor (exactOrderIdempotent W hN) →ₐ[k] k) ≃ _
    refine (clopenPoints _ (exactOrderIdempotent_idempotent W hN)).trans <|
      ((affineTorsionPoints W _ hN).subtypeEquiv (q := fun p => addOrderOf p.1 = N + 2) (fun x =>
        (product_idempotent_order_iff W hN x))).trans ?_
    refine Equiv.ofBijective (fun p => ⟨p.1.1, p.2⟩) ⟨?_, ?_⟩
    · intro a b h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : {P : W.toAffine.Point //
        addOrderOf P = N + 2} => x.1) h))
    · rintro ⟨P, hP⟩
      have ht : (N + 2) • P = 0 := by rw [← hP, addOrderOf_nsmul_eq_zero]
      have hne : P ≠ 0 := by rintro rfl; simp at hP
      exact ⟨⟨⟨P, hne, ht⟩, hP⟩, rfl⟩

#print axioms restrict_coordinates
#print axioms restrictAffineTorsion_point
#print axioms clopenPoints
#print axioms product_idempotent_order_iff
#print axioms exactOrderPoints

end WeierstrassCurve.ModelLevels
