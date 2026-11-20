import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Schwartz

/-! Conjugation transports to the local rule for the chosen completed chart. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler LocalWeights
open scoped Quaternion

variable {a b : ℚ} {R : Order a b}

/-- Interpret an ambient integral unit as a unit of the completed order. -/
def completedUnit (q : Prime) (u : localUnits R q) : (R.completion q.val)ˣ :=
  ⟨⟨u.val.val, u.prop.1⟩, ⟨u.val.inv, u.prop.2⟩,
    Subtype.ext u.val.val_inv, Subtype.ext u.val.inv_val⟩

private theorem re_conj (q : Prime) (u : (Bp q.val a b)ˣ) (x : Bp q.val a b) :
    ((↑u⁻¹ : Bp q.val a b) * x * (u : Bp q.val a b)).re = x.re := by
  have hc (s t : Bp q.val a b) : (s * t).re = (t * s).re := by
    simp only [QuaternionAlgebra.re_mul]
    ring
  rw [hc, ← mul_assoc, Units.mul_inv, one_mul]

variable {O : Type} [CommRing O] {ell N : ℕ} [Fact ell.Prime]
variable (h : ell % 4 = 3) (hN : 0 < N)
variable (C : LevelRoots O N) (m : ℕ)

/-- The conjugating unit in the split Eichler chart. -/
def splitUnit (q : Prime) (hq : q.val ≠ ell)
    (u : localUnits (levelOrder ell h N hN) q) :
    (eichler q.val (N.factorization q.val))ˣ :=
  Units.map (splitOrderEquiv ell h N hN q hq).toMonoidHom (completedUnit q u)

theorem splitUnit_ambient (q : Prime) (hq : q.val ≠ ell)
    (u : localUnits (levelOrder ell h N hN) q) :
    Units.map (integralMat q.val).toMonoidHom (eichlerUnit (splitUnit h hN q hq u)) =
      Units.map (splitChart ell h q hq).toMonoidHom u.val :=
  Units.ext (splitOrderEquiv_apply ell h N hN q hq
    (⟨u.val.val, u.prop.1⟩ : (levelOrder ell h N hN).completion q.val))

/-- Norm character for conjugation at a split prime. -/
def splitConjSign (q : Prime) (hq : q.val ≠ ell)
    (u : localUnits (levelOrder ell h N hN) q) : Oˣ :=
  if q.val ∣ N ∨ q.val = 2 then 1
  else if q.val ∣ m then legendreUnit q.val (Matrix.GeneralLinearGroup.det
    (eichlerUnit (splitUnit h hN q hq u)))
  else 1

private theorem dyadic_conj_of_zero {e : ℕ} (he : e = 0)
    (U : (eichler 2 e)ˣ) (y : TraceZero ℚ_[2]) :
    (dyadicSchwartz (matrixConj (Units.map (integralMat 2).toMonoidHom (eichlerUnit U)) y) : O) =
      ((1 : Oˣ)⁻¹ : Oˣ) * dyadicSchwartz y := by
  subst e
  exact (dyadicRule (O := O)).weight_conj U y

theorem splitFactor_conj (q : Prime) (hq : q.val ≠ ell)
    (u : localUnits (levelOrder ell h N hN) q) (x : Bp q.val (-1) (-(ell : ℚ))) :
    splitFactor h C m q hq ((↑u.val⁻¹ : Bp q.val (-1) (-(ell : ℚ))) * x * ↑u.val) =
      ((splitConjSign (O := O) h hN m q hq u)⁻¹ : Oˣ) * splitFactor h C m q hq x := by
  classical
  let y' := (↑u.val⁻¹ : Bp q.val (-1) (-(ell : ℚ))) * x * ↑u.val
  have hr : y'.re = x.re := re_conj q u.val x
  by_cases hx : x.re = 0
  · let E := splitChart ell h q hq
    let y : TraceZero ℚ_[q.val] := ⟨E x, by
      rw [(split_invariants _ _ E x).1, hx, mul_zero]⟩
    let U := splitUnit h hN q hq u
    have hh : (⟨E y', by rw [(split_invariants _ _ E y').1, hr, hx, mul_zero]⟩ :
        TraceZero ℚ_[q.val]) = matrixConj
        (Units.map (integralMat q.val).toMonoidHom (eichlerUnit U)) y := by
      apply Subtype.ext
      change E y' = _
      unfold U
      rw [splitUnit_ambient]
      simp only [y', matrixConj, map_mul, y]
      rfl
    change splitFactor h C m q hq y' = _
    simp only [splitFactor, dite_eq_left hx, dite_eq_left (hr.trans hx), splitConjSign]
    by_cases hqN : q.val ∣ N
    · simp only [dite_eq_left hqN, ite_eq_left (Or.inl hqN)]
      rw [hh]
      exact (levelRule (q.prop.factorization_pos_of_dvd hN.ne' hqN)
        (C.alpha q hqN)).weight_conj U y
    · simp only [hqN, false_or]
      by_cases hq₂ : q.val = 2
      · have he : q = ⟨2, Nat.prime_two⟩ := Subtype.ext hq₂
        subst q
        simp only [ite_true]
        rw [hh]
        have h0 : N.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd hqN
        exact dyadic_conj_of_zero h0 U y
      · simp only [dite_eq_right hq₂, ite_eq_right hq₂]
        by_cases hqm : q.val ∣ m
        · simp only [ite_eq_left hqm]
          rw [hh]
          exact (nilRule (O := O) (p := q.val)).weight_conj (eichlerUnit U) y
        · simp only [ite_eq_right hqm]
          rw [hh]
          exact (goodRule (O := O) (p := q.val)).weight_conj (eichlerUnit U) y
  · change splitFactor h C m q hq y' = _
    simp only [splitFactor, dite_eq_right hx, dite_eq_right (fun he => hx (hr.symm.trans he)), mul_zero]

/-- Units at the detecting prime act trivially on the actual division factor. -/
theorem divisionFactor_conj
    (u : localUnits (levelOrder ell h N hN) ⟨ell, Fact.out⟩)
    (x : Bp ell (-1) (-(ell : ℚ))) :
    divisionFactor h ((↑u.val⁻¹ : Bp ell (-1) (-(ell : ℚ))) * x * ↑u.val) =
      (divisionFactor h x : O) := by
  classical
  let : Fact (ell % 4 = 3) := ⟨h⟩
  let q : Prime := ⟨ell, Fact.out⟩
  let y' := (↑u.val⁻¹ : Bp ell (-1) (-(ell : ℚ))) * x * ↑u.val
  have hre : y'.re = x.re := re_conj q u.val x
  by_cases hx : x.re = 0
  · let D := LocalDivision.coordinates ell
    let E := DivisionJoin.ambientEquiv ell
    let y : D.RationalZero := ⟨E x, by
      change LocalDivision.tr (DivisionJoin.ambientEquiv ell x) = 0
      rw [DivisionJoin.ambient_trace, DivisionJoin.reducedTrace, hx, mul_zero]⟩
    have hU : (u.val : Bp ell (-1) (-(ell : ℚ))) ∈ DivisionJoin.completedOrder ell h :=
      divisionCompletion ell h N hN ▸ u.prop.1
    have hV : (↑u.val⁻¹ : Bp ell (-1) (-(ell : ℚ))) ∈ DivisionJoin.completedOrder ell h :=
      divisionCompletion ell h N hN ▸ u.prop.2
    let v : (DivisionJoin.completedOrder ell h)ˣ :=
      ⟨⟨u.val.val, hU⟩, ⟨u.val.inv, hV⟩, Subtype.ext u.val.val_inv, Subtype.ext u.val.inv_val⟩
    let U : D.orderˣ := Units.map (DivisionJoin.orderEquiv ell h).toMonoidHom v
    have hU' : Units.map D.order.val.toMonoidHom U = Units.map E.toMonoidHom u.val :=
      Units.ext (DivisionJoin.order_compatible ell h v.val).symm
    have he : (⟨E y', by
        change LocalDivision.tr (DivisionJoin.ambientEquiv ell y') = 0
        rw [DivisionJoin.ambient_trace, DivisionJoin.reducedTrace, hre, hx, mul_zero]⟩ :
        D.RationalZero) = D.conjZero (LocalDivision.localModel ell)
          (Units.map D.order.val.toMonoidHom U) y := by
      apply Subtype.ext
      change E y' = _
      rw [hU']
      simp only [y', y, map_mul, DivisionCoordinates.conjZero]
      rfl
    change divisionFactor h y' = _
    simp only [divisionFactor, dite_eq_left hx, dite_eq_left (hre.trans hx)]
    rw [he]
    simpa only [DivisionCoordinates.divisionRule, MonoidHom.one_apply, inv_one, Units.val_one,
      one_mul] using (D.divisionRule (O := O) (LocalDivision.localModel ell)).weight_conj U y
  · change divisionFactor h y' = _
    simp only [divisionFactor, dite_eq_right hx, dite_eq_right (fun he => hx (hre.symm.trans he))]

end ZInQ.Manuscript.RC.ThetaJoin
