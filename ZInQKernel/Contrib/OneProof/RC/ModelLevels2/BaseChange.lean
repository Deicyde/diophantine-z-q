import ZInQKernel.Contrib.OneProof.RC.ModelLevels.ExactOrderBaseChange

/-! # Naturality of the divisor charts -/

namespace WeierstrassCurve.ModelLevels

open Polynomial ModelTorsion
open scoped TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The map on the first abscissa ring before adjoining the ordinate. -/
private noncomputable def specializeAbscissa (W : WeierstrassCurve A) (n : ℕ) :
    AdjoinRoot (W.preΨ' n) →ₐ[A] AdjoinRoot ((W.map (algebraMap A B)).preΨ' n) :=
  (((polynomialQuotientBaseChange (B := B) (W.preΨ' n)).trans
    (AdjoinRoot.algEquivOfEq B _ _ (W.map_preΨ' (algebraMap A B) n).symm)).restrictScalars A).toAlgHom.comp
    Algebra.TensorProduct.includeRight

private theorem specializeAbscissa_root (W : WeierstrassCurve A) (n : ℕ) :
    specializeAbscissa (B := B) W n (AdjoinRoot.root _) = AdjoinRoot.root _ := by
  simp only [specializeAbscissa, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.restrictScalars_apply, AlgEquiv.trans_apply,
    polynomialQuotientBaseChange_root, AdjoinRoot.algEquivOfEq_root]

private theorem specializeOrdinate_eq (W : WeierstrassCurve A) (n : ℕ) :
    (unramifiedOrdinate W n).map (specializeAbscissa (B := B) W n).toRingHom =
      unramifiedOrdinate (W.map (algebraMap A B)) n := by
  unfold unramifiedOrdinate
  rw [map_ordinatePolynomial, WeierstrassCurve.map_map, WeierstrassCurve.map_map,
    show (specializeAbscissa (B := B) W n).toRingHom.comp (algebraMap A _) =
      algebraMap A _ from (specializeAbscissa (B := B) W n).comp_algebraMap,
    ← IsScalarTower.algebraMap_eq]
  rw [show (specializeAbscissa (B := B) W n).toRingHom (AdjoinRoot.root _) =
    AdjoinRoot.root _ from specializeAbscissa_root W n]

private theorem specializeBranch_eq (W : WeierstrassCurve A) (n : ℕ) :
    (branchPolynomial W n).map (algebraMap A B) =
      branchPolynomial (W.map (algebraMap A B)) n := by
  by_cases h : Even n <;> simp [branchPolynomial, h, W.map_Ψ₂Sq]

set_option backward.isDefEq.respectTransparency false in
/-- The affine scalar extension sends the old chart roots to the corresponding new ones. -/
theorem affineTorsionBaseChange_includeRight (W : WeierstrassCurve A) (n : ℕ)
    (x : AffineTorsionAlgebra W n) :
    affineTorsionAlgebraBaseChange (B := B) W n (1 ⊗ₜ[A] x) =
      (AdjoinRoot.mapAlgHom (specializeAbscissa (B := B) W n) _ _
        (dvd_of_eq (specializeOrdinate_eq W n).symm) x.1,
        AdjoinRoot.mapAlgHom (Algebra.ofId A B) _ _ (dvd_of_eq (specializeBranch_eq W n).symm) x.2) := by
  simp only [affineTorsionAlgebraBaseChange, AlgEquiv.trans_apply,
    Algebra.TensorProduct.prodRight_tmul, AlgEquiv.prodCongr_apply]
  apply Prod.ext
  · let q := unramifiedOrdinate W n
    let q' := unramifiedOrdinate (W.map (algebraMap A B)) n
    let i : AdjoinRoot (W.preΨ' n) →ₐ[A] B ⊗[A] AdjoinRoot (W.preΨ' n) :=
      Algebra.TensorProduct.includeRight
    let e : B ⊗[A] AdjoinRoot (W.preΨ' n) ≃ₐ[B] AdjoinRoot ((W.map (algebraMap A B)).preΨ' n) :=
      (polynomialQuotientBaseChange _).trans
        (AdjoinRoot.algEquivOfEq B _ _ (W.map_preΨ' (algebraMap A B) n).symm)
    have h : Associated ((q.map i.toRingHom).map e.toRingHom) q' := by
      rw [Polynomial.map_map]
      change Associated ((unramifiedOrdinate W n).map (specializeAbscissa (B := B) W n).toRingHom) _
      rw [specializeOrdinate_eq]
    change AdjoinRoot.mapAlgEquiv e _ q' h
      (AdjoinRoot.tensorAlgEquiv q (q.map i.toRingHom) rfl (1 ⊗ₜ x.1)) = _
    let f : AdjoinRoot q →ₐ[A] AdjoinRoot q' :=
      (((AdjoinRoot.tensorAlgEquiv q (q.map i.toRingHom) rfl).trans
        (AdjoinRoot.mapAlgEquiv e _ q' h)).restrictScalars A).toAlgHom.comp
        Algebra.TensorProduct.includeRight
    change f x.1 = _
    suffices hf : f = AdjoinRoot.mapAlgHom (specializeAbscissa W n) _ _
        (dvd_of_eq (specializeOrdinate_eq W n).symm) by rw [hf]
    apply AdjoinRoot.algHom_ext'
    · apply AdjoinRoot.algHom_ext
      change AdjoinRoot.mapAlgEquiv e _ q' h
        (AdjoinRoot.tensorAlgEquiv q _ rfl (1 ⊗ₜ AdjoinRoot.of q (AdjoinRoot.root _))) =
        AdjoinRoot.map (specializeAbscissa (B := B) W n).toRingHom q q' (dvd_of_eq (specializeOrdinate_eq W n).symm)
          (AdjoinRoot.of q (AdjoinRoot.root _))
      rw [AdjoinRoot.tensorAlgEquiv_of, AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_of,
        AdjoinRoot.map_of]
      rfl
    · change AdjoinRoot.mapAlgEquiv e _ q' h
        (AdjoinRoot.tensorAlgEquiv q _ rfl (1 ⊗ₜ AdjoinRoot.root q)) =
        AdjoinRoot.map (specializeAbscissa (B := B) W n).toRingHom q q' (dvd_of_eq (specializeOrdinate_eq W n).symm) (AdjoinRoot.root q)
      rw [AdjoinRoot.tensorAlgEquiv_root, AdjoinRoot.coe_mapAlgEquiv,
        AdjoinRoot.map_root, AdjoinRoot.map_root]
  · let p := branchPolynomial W n
    let p' := branchPolynomial (W.map (algebraMap A B)) n
    let f : AdjoinRoot p →ₐ[A] AdjoinRoot p' :=
      (((polynomialQuotientBaseChange p).trans
        (AdjoinRoot.algEquivOfEq B _ _ (specializeBranch_eq W n))).restrictScalars A).toAlgHom.comp
        Algebra.TensorProduct.includeRight
    suffices hf : f = AdjoinRoot.mapAlgHom (Algebra.ofId A B) _ _ (dvd_of_eq (specializeBranch_eq W n).symm) by
      change f x.2 = _
      rw [hf]
    apply AdjoinRoot.algHom_ext
    change AdjoinRoot.algEquivOfEq B _ _ (specializeBranch_eq W n)
      (polynomialQuotientBaseChange p (1 ⊗ₜ AdjoinRoot.root p)) =
        AdjoinRoot.map (algebraMap A B) p p' (dvd_of_eq (specializeBranch_eq W n).symm)
          (AdjoinRoot.root p)
    rw [polynomialQuotientBaseChange_root, AdjoinRoot.algEquivOfEq_root, AdjoinRoot.map_root]

private theorem adjoinRoot_map_congr {U V : Type*} [CommRing U] [CommRing V]
    {p : U[X]} {q : V[X]} {f g : U →+* V}
    (h : f = g) (hf : q ∣ p.map f) (hg : q ∣ p.map g) (x : AdjoinRoot p) :
    AdjoinRoot.map f p q hf x = AdjoinRoot.map g p q hg x := by
  subst g
  rfl

private theorem adjoinRoot_map_square {R U V U' V' : Type*} [CommRing R]
    [CommRing U] [CommRing V] [CommRing U'] [CommRing V']
    [Algebra R U] [Algebra R V] [Algebra R U'] [Algebra R V']
    {p : U[X]} {q : V[X]} {p' : U'[X]} {q' : V'[X]}
    (f : U →ₐ[R] V) (g : U' →ₐ[R] V') (i : U →ₐ[R] U') (j : V →ₐ[R] V')
    (h : j.comp f = g.comp i) (hf : q ∣ p.map f) (hg : q' ∣ p'.map g)
    (hi : p' ∣ p.map i) (hj : q' ∣ q.map j) (x : AdjoinRoot p) :
    AdjoinRoot.mapAlgHom j q q' hj (AdjoinRoot.mapAlgHom f p q hf x) =
      AdjoinRoot.mapAlgHom g p' q' hg (AdjoinRoot.mapAlgHom i p p' hi x) := by
  change (AdjoinRoot.mapAlgHom j q q' hj |>.comp (AdjoinRoot.mapAlgHom f p q hf)) x =
    (AdjoinRoot.mapAlgHom g p' q' hg |>.comp (AdjoinRoot.mapAlgHom i p p' hi)) x
  rw [AdjoinRoot.mapAlgHom_comp_mapAlgHom, AdjoinRoot.mapAlgHom_comp_mapAlgHom]
  have hleft : q' ∣ p.map (j.comp f).toRingHom := by
    rw [show (j.comp f).toRingHom = j.toRingHom.comp f.toRingHom from rfl, ← Polynomial.map_map]
    exact hj.trans (Polynomial.map_dvd j.toRingHom hf)
  have hright : q' ∣ p.map (g.comp i).toRingHom := by
    rw [show (g.comp i).toRingHom = g.toRingHom.comp i.toRingHom from rfl, ← Polynomial.map_map]
    exact hg.trans (Polynomial.map_dvd g.toRingHom hi)
  exact adjoinRoot_map_congr (congrArg AlgHom.toRingHom h) hleft hright x

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Base change commutes with divisor-level restriction of affine torsion. -/
theorem restrictAffineTorsion_baseChange (W : WeierstrassCurve A) [W.IsElliptic]
    {N d : ℕ} (hN : IsUnit (N : A)) (hd : d ∣ N) :
    RestrictionBaseChange (B := B) W hN d hd := by
  let V := W.map (algebraMap A B)
  let hNB : IsUnit (N : B) := by simpa using hN.map (algebraMap A B)
  let f := ((affineTorsionAlgebraBaseChange (B := B) W d).restrictScalars A).toAlgHom.comp
    (Algebra.TensorProduct.map (S := A) (AlgHom.id A B) (restrictAffineTorsion W hN hd))
  let g := ((restrictAffineTorsion V hNB hd).restrictScalars A).comp
    ((affineTorsionAlgebraBaseChange (B := B) W N).restrictScalars A).toAlgHom
  suffices hf : f = g by
    intro x
    exact DFunLike.congr_fun hf x
  apply Algebra.TensorProduct.ext
  · ext b : 1
    simp only [f, g, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      AlgEquiv.coe_toAlgHom, AlgEquiv.restrictScalars_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    change affineTorsionAlgebraBaseChange W d (b ⊗ₜ 1) =
      restrictAffineTorsion V hNB hd (affineTorsionAlgebraBaseChange W N (b ⊗ₜ 1))
    change affineTorsionAlgebraBaseChange W d (algebraMap B _ b) =
      restrictAffineTorsion V hNB hd (affineTorsionAlgebraBaseChange W N (algebraMap B _ b))
    rw [(affineTorsionAlgebraBaseChange (B := B) W d).commutes,
      (affineTorsionAlgebraBaseChange (B := B) W N).commutes,
      (restrictAffineTorsion V hNB hd).commutes]
  · ext x : 1
    change affineTorsionAlgebraBaseChange W d (1 ⊗ₜ restrictAffineTorsion W hN hd x) =
      restrictAffineTorsion V hNB hd (affineTorsionAlgebraBaseChange W N (1 ⊗ₜ x))
    rw [affineTorsionBaseChange_includeRight, affineTorsionBaseChange_includeRight]
    unfold restrictAffineTorsion affineDivisorMap
    apply Prod.ext
    · simp only [AlgHom.prodMap, AlgHom.coe_mk, RingHom.coe_prodMap, Prod.map_fst]
      let fₓ := AdjoinRoot.algHomOfDvd A _ _ (divisor_polynomials_dvd W hN hd).2
      let gₓ := AdjoinRoot.algHomOfDvd B _ _ (divisor_polynomials_dvd V hNB hd).2
      have hₓ : (specializeAbscissa (B := B) W d).comp fₓ =
          (gₓ.restrictScalars A).comp (specializeAbscissa W N) := by
        apply AdjoinRoot.algHom_ext
        change specializeAbscissa W d (fₓ (AdjoinRoot.root _)) =
          gₓ (specializeAbscissa W N (AdjoinRoot.root _))
        rw [show fₓ (AdjoinRoot.root _) = AdjoinRoot.root _ from AdjoinRoot.algHomOfDvd_root (R := A) _ _ _,
          specializeAbscissa_root, specializeAbscissa_root,
          show gₓ (AdjoinRoot.root _) = AdjoinRoot.root _ from AdjoinRoot.algHomOfDvd_root (R := B) _ _ _]
      exact adjoinRoot_map_square fₓ (gₓ.restrictScalars A) _ _ hₓ _ _ _ _ x.1
    · simp only [AlgHom.prodMap, AlgHom.coe_mk, RingHom.coe_prodMap, Prod.map_snd]
      exact adjoinRoot_map_square (AlgHom.id A A) ((AlgHom.id B B).restrictScalars A)
        (Algebra.ofId A B) (Algebra.ofId A B) rfl _ _ _ _ x.2

/-- The exact-order algebra commutes with arbitrary scalar extension. -/
noncomputable def exactOrderBaseChange (W : WeierstrassCurve A) [W.IsElliptic]
    {N : ℕ} (hN : IsUnit (N : A)) :
    let hNB : IsUnit (N : B) := by simpa only [map_natCast] using hN.map (algebraMap A B)
    B ⊗[A] ExactOrderAlgebra W hN ≃ₐ[B] ExactOrderAlgebra (W.map (algebraMap A B)) hNB :=
  exactOrderBaseChangeOfRestriction W hN fun _ hd _ => restrictAffineTorsion_baseChange W hN hd

/-- The abscissa root on both torsion charts. -/
noncomputable def torsionChartX (W : WeierstrassCurve A) (n : ℕ) :
    AffineTorsionAlgebra W n :=
  (AdjoinRoot.of _ (AdjoinRoot.root (W.preΨ' n)), AdjoinRoot.root (branchPolynomial W n))

/-- The ordinate root on the quadratic chart, extended by zero on the
two-torsion branch. Only the quadratic component is used for exact orders
greater than two. -/
noncomputable def torsionChartY (W : WeierstrassCurve A) (n : ℕ) :
    AffineTorsionAlgebra W n := (AdjoinRoot.root (unramifiedOrdinate W n), 0)

theorem affineTorsionBaseChange_x (W : WeierstrassCurve A) (n : ℕ) :
    affineTorsionAlgebraBaseChange (B := B) W n (1 ⊗ₜ[A] torsionChartX W n) =
      torsionChartX (W.map (algebraMap A B)) n := by
  rw [affineTorsionBaseChange_includeRight]
  apply Prod.ext
  · change AdjoinRoot.map (specializeAbscissa (B := B) W n).toRingHom _ _
        (dvd_of_eq (specializeOrdinate_eq W n).symm) (AdjoinRoot.of _ (AdjoinRoot.root (W.preΨ' n))) =
      AdjoinRoot.of _ (AdjoinRoot.root ((W.map (algebraMap A B)).preΨ' n))
    rw [AdjoinRoot.map_of]
    exact congrArg (AdjoinRoot.of _) (specializeAbscissa_root W n)
  · change AdjoinRoot.map (algebraMap A B) _ _ (dvd_of_eq (specializeBranch_eq W n).symm)
        (AdjoinRoot.root (branchPolynomial W n)) = _
    exact AdjoinRoot.map_root _ _ _ _

theorem affineTorsionBaseChange_y (W : WeierstrassCurve A) (n : ℕ) :
    affineTorsionAlgebraBaseChange (B := B) W n (1 ⊗ₜ[A] torsionChartY W n) =
      torsionChartY (W.map (algebraMap A B)) n := by
  rw [affineTorsionBaseChange_includeRight]
  apply Prod.ext
  · change AdjoinRoot.map (specializeAbscissa (B := B) W n).toRingHom _ _
        (dvd_of_eq (specializeOrdinate_eq W n).symm) (AdjoinRoot.root (unramifiedOrdinate W n)) = _
    exact AdjoinRoot.map_root _ _ _ _
  · exact map_zero (AdjoinRoot.mapAlgHom (Algebra.ofId A B) _ _
      (dvd_of_eq (specializeBranch_eq W n).symm))

#print axioms torsionChartX
#print axioms torsionChartY
#print axioms affineTorsionBaseChange_x
#print axioms affineTorsionBaseChange_y
#print axioms specializeAbscissa_root
#print axioms specializeOrdinate_eq
#print axioms specializeBranch_eq
#print axioms affineTorsionBaseChange_includeRight
#print axioms adjoinRoot_map_congr
#print axioms adjoinRoot_map_square
#print axioms restrictAffineTorsion_baseChange
#print axioms exactOrderBaseChange

end WeierstrassCurve.ModelLevels
