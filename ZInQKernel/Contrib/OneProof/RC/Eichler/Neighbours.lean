import ZInQKernel.Contrib.OneProof.RC.Eichler.Fields

/-!
# Duality of the ideal correspondences

Tex 8481–8484 and 9067–9071. On-the-spot (c): an arrow from `i` to `j` is a multiplier
of the chosen representative of `j` onto a subideal of the representative of `i`.
Duality sends the multiplier `u` to `u⁻¹ p`; this exchanges the two index-`p²`
inclusions between `pI` and `I`.
-/

open Module

namespace ZInQ.Manuscript.RC.Eichler.RightIdeal

variable {a b : ℚ} {R : Order a b}

/-- A nonzero natural number as a scalar quaternion unit. -/
def scalarUnit (p : ℕ) (hp : p ≠ 0) : (B a b)ˣ :=
  Units.map (algebraMap ℚ (B a b)).toMonoidHom (Units.mk0 (p : ℚ) (by exact_mod_cast hp))

theorem scalar_mul (p : ℕ) (hp : p ≠ 0) (x : B a b) :
    (↑(scalarUnit (a := a) (b := b) p hp) : B a b) * x = p • x := by
  change algebraMap ℚ (B a b) (p : ℚ) * x = _
  rw [← Algebra.smul_def, Nat.cast_smul_eq_nsmul]

private theorem scalar_comm (p : ℕ) (hp : p ≠ 0) (u : (B a b)ˣ) :
    scalarUnit p hp * u = u * scalarUnit p hp :=
  Units.ext (Algebra.commutes (p : ℚ) (u : B a b))

private theorem lattice_scalar_le (I : RightIdeal R) (p : ℕ) (hp : p ≠ 0) :
    (I.translate (scalarUnit p hp)).lattice ≤ I.lattice := by
  rintro _ ⟨x, hx, rfl⟩
  change (↑(scalarUnit (a := a) (b := b) p hp) : B a b) * x ∈ I.lattice
  rw [scalar_mul]
  exact I.lattice.nsmul_mem hx _

set_option backward.isDefEq.respectTransparency false in
/-- The index of `pI` in a full lattice `I` is `p⁴`. -/
theorem relIndex_scalar (I : RightIdeal R) (p : ℕ) (hp : p ≠ 0) :
    (I.translate (scalarUnit p hp)).lattice.toAddSubgroup.relIndex I.lattice.toAddSubgroup = p^4 := by
  classical
  let c := I.full.basis (QuaternionAlgebra.basisOneIJK a 0 b)
  let f := ((scalarUnit p hp).mulLeftLinearEquiv ℚ (B a b)).restrictScalars ℤ
  let d := c.map (Submodule.equivMapOfInjective f.toLinearMap f.injective I.lattice)
  have h (i : Fin 4) :
      (⟨d i, lattice_scalar_le I p hp (d i).prop⟩ : I.lattice) = (p : ℤ) • c i := by
    apply Subtype.ext
    change ((f : B a b → B a b) (c i : B a b)) = _
    change (↑(scalarUnit (a := a) (b := b) p hp) : B a b) * (c i : B a b) = _
    rw [scalar_mul]
    simp
  have hidx := AddSubgroup.relIndex_eq_natAbs_det
    (I.translate (scalarUnit p hp)).lattice.toAddSubgroup I.lattice.toAddSubgroup
    (lattice_scalar_le I p hp) d c
  change _ = (c.det (fun i => (⟨d i, lattice_scalar_le I p hp (d i).prop⟩ : I.lattice))).natAbs at hidx
  rw [hidx]
  simp_rw [h]
  have hm : c.toMatrix (fun i => (p : ℤ) • c i) = (p : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    ext i j
    rw [Basis.toMatrix_apply, c.repr.map_smul, Finsupp.smul_apply, c.repr_self,
      Matrix.smul_apply, Matrix.one_apply, Finsupp.single_apply]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
    · simp only [ite_eq_right hij, ite_eq_right (Ne.symm hij)]
  rw [Basis.det_apply, hm, Matrix.det_smul, Matrix.det_one, mul_one]
  simp

private theorem translate_le_iff (I J : RightIdeal R) (u : (B a b)ˣ) :
    (I.translate u).lattice ≤ (J.translate u).lattice ↔ I.lattice ≤ J.lattice := by
  constructor
  · intro h x hx
    have h' : (u : B a b) * x ∈ (I.translate u).lattice := ⟨x, hx, rfl⟩
    have ht := (mem_translate u J _).mp (h h')
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using ht
  · intro h x hx
    rw [mem_translate] at hx ⊢
    exact h hx

private theorem relIndex_translate (I J : RightIdeal R) (u : (B a b)ˣ) :
    (I.translate u).lattice.toAddSubgroup.relIndex (J.translate u).lattice.toAddSubgroup =
      I.lattice.toAddSubgroup.relIndex J.lattice.toAddSubgroup := by
  let g := (u.mulLeftLinearEquiv ℚ (B a b)).restrictScalars ℤ
  change (I.lattice.map g.toLinearMap).toAddSubgroup.relIndex
    (J.lattice.map g.toLinearMap).toAddSubgroup = _
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (f := g.toLinearMap.toAddMonoidHom) g.injective

/-- Index-`p²` right subideals between `pI` and `I`. -/
def IsNeighbour (p : ℕ) (hp : p ≠ 0) (I J : RightIdeal R) : Prop :=
  (I.translate (scalarUnit p hp)).lattice ≤ J.lattice ∧ J.lattice ≤ I.lattice ∧
    J.lattice.toAddSubgroup.relIndex I.lattice.toAddSubgroup = p^2

/-- Duality of the two inclusions for an actual multiplier into a neighbour. -/
theorem neighbour_dual {p : ℕ} (hp : p ≠ 0) {I J : RightIdeal R} {u : (B a b)ˣ}
    (h : IsNeighbour p hp I (J.translate u)) :
    IsNeighbour p hp J (I.translate (u⁻¹ * scalarUnit p hp)) := by
  let s : (B a b)ˣ := scalarUnit p hp
  have hj : (J.translate s).translate u = (J.translate u).translate s := by
    rw [← translate_mul, ← translate_mul, scalar_comm]
  have hi : (I.translate (u⁻¹ * s)).translate u = I.translate s := by
    rw [← translate_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · apply (translate_le_iff _ _ u).mp
    rw [hi, hj]
    exact (translate_le_iff _ _ s).mpr h.2.1
  · apply (translate_le_iff _ _ u).mp
    rw [hi]
    exact h.1
  · have hidx := AddSubgroup.relIndex_mul_relIndex
        (H := (I.translate s).lattice.toAddSubgroup)
        (K := (J.translate u).lattice.toAddSubgroup)
        (L := I.lattice.toAddSubgroup) h.1 h.2.1
    rw [h.2.2, I.relIndex_scalar p hp, show p^4 = p^2 * p^2 by ring] at hidx
    have hidx' := Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero hp) _) hidx
    rw [← relIndex_translate _ _ u, hi]
    exact hidx'

/-- All multipliers realizing an arrow from `I` to the class of `J`. -/
abbrev Arrows (p : ℕ) (hp : p ≠ 0) (I J : RightIdeal R) :=
  {u : (B a b)ˣ // IsNeighbour p hp I (J.translate u)}

/-- Dualizing gives a bijection on actual multipliers. -/
def arrowsDual (p : ℕ) (hp : p ≠ 0) (I J : RightIdeal R) : Arrows p hp I J ≃ Arrows p hp J I where
  toFun u := ⟨u.val⁻¹ * scalarUnit p hp, neighbour_dual hp u.prop⟩
  invFun u := ⟨u.val⁻¹ * scalarUnit p hp, neighbour_dual hp u.prop⟩
  left_inv u := Subtype.ext (by
    change (u.val⁻¹ * scalarUnit p hp)⁻¹ * scalarUnit p hp = u.val
    rw [mul_inv_rev, inv_inv, mul_assoc, ← scalar_comm p hp u.val, ← mul_assoc, inv_mul_cancel, one_mul])
  right_inv u := Subtype.ext (by
    change (u.val⁻¹ * scalarUnit p hp)⁻¹ * scalarUnit p hp = u.val
    rw [mul_inv_rev, inv_inv, mul_assoc, ← scalar_comm p hp u.val, ← mul_assoc, inv_mul_cancel, one_mul])

end ZInQ.Manuscript.RC.Eichler.RightIdeal

namespace ZInQ.Manuscript.RC.Eichler

variable {a b : ℚ}

/-- Every definite right ideal class has an integral representative with uniformly bounded index. -/
theorem exists_bounded_integral_representative (R : Order a b) (ha : a < 0) (hb : b < 0) :
    ∃ M : ℕ, ∀ z : ClassSet R, ∃ J : LPIdeal R, Quotient.mk (idealRel R) J = z ∧
      J.val.lattice ≤ R.lattice ∧
      J.val.lattice.toAddSubgroup.relIndex R.lattice.toAddSubgroup ∈ Set.Icc 1 M := by
  obtain ⟨d, hd, hden⟩ := exists_normalized_denominator R
  refine ⟨d^4, fun z => ?_⟩
  let I := representative z
  obtain ⟨u, hR, hnorm⟩ := I.val.exists_normalized ha hb
  let s : (B a b)ˣ := RightIdeal.scalarUnit d hd.ne'
  let J : LPIdeal R :=
    ⟨I.val.translate (s * u), I.val.locallyPrincipal_translate I.prop (s * u)⟩
  have hz : Quotient.mk (idealRel R) J = z :=
    (Quotient.sound (s := idealRel R)
      (show (idealRel R).r I J from ⟨s * u, rfl⟩)).symm.trans (Quotient.out_eq z)
  have hJ : J.val.lattice ≤ R.lattice := by
    change (I.val.translate (s * u)).lattice ≤ R.lattice
    rw [RightIdeal.translate_mul]
    rintro _ ⟨x, hx, rfl⟩
    change (s : B a b) * x ∈ R.lattice
    rw [RightIdeal.scalar_mul]
    exact hden _ hR hnorm x hx
  have hlow : ((RightIdeal.self R).translate s).lattice ≤ J.val.lattice := by
    change ((RightIdeal.self R).translate s).lattice ≤ (I.val.translate (s * u)).lattice
    rw [RightIdeal.translate_mul]
    exact (RightIdeal.translate_le_iff _ _ s).mpr hR
  have hidx : J.val.lattice.toAddSubgroup.relIndex R.lattice.toAddSubgroup ∣ d^4 := by
    rw [← (RightIdeal.self R).relIndex_scalar d hd.ne']
    exact AddSubgroup.relIndex_dvd_of_le_left _ hlow
  have hpos : 0 < d^4 := pow_pos hd _
  refine ⟨J, hz, hJ, ?_, Nat.le_of_dvd hpos hidx⟩
  by_contra! hn
  have hz' : J.val.lattice.toAddSubgroup.relIndex R.lattice.toAddSubgroup = 0 := by omega
  rw [hz', zero_dvd_iff] at hidx
  exact hpos.ne' hidx

/-- There are finitely many integral right ideals of bounded positive index in the order. -/
theorem finite_integral_bounded (R : Order a b) (M : ℕ) :
    Finite {I : RightIdeal R // I.lattice ≤ R.lattice ∧
      I.lattice.toAddSubgroup.relIndex R.lattice.toAddSubgroup ∈ Set.Icc 1 M} := by
  let d := M.factorial
  have hd : 0 < d := Nat.factorial_pos _
  let s : (B a b)ˣ := RightIdeal.scalarUnit d hd.ne'
  let J := (RightIdeal.self R).translate s
  let := finite_overlattices J.lattice J.full d hd
  let f (I : {I : RightIdeal R // I.lattice ≤ R.lattice ∧
      I.lattice.toAddSubgroup.relIndex R.lattice.toAddSubgroup ∈ Set.Icc 1 M}) :
      {K : Submodule ℤ (B a b) // J.lattice ≤ K ∧ ∀ x ∈ K, d • x ∈ J.lattice} :=
    ⟨I.val.lattice, by
      have hdvd : I.val.lattice.toAddSubgroup.relIndex R.lattice.toAddSubgroup ∣ d :=
        Nat.dvd_factorial I.prop.2.1 I.prop.2.2
      rintro _ ⟨x, hx, rfl⟩
      change (s : B a b) * x ∈ I.val.lattice
      rw [RightIdeal.scalar_mul]
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, mul_nsmul]
      have hx' : x ∈ R.lattice.toAddSubgroup := hx
      exact I.val.lattice.nsmul_mem
        (AddSubgroup.nsmul_relIndex_mem I.val.lattice.toAddSubgroup (K := R.lattice.toAddSubgroup) hx') k,
      fun x hx => ⟨x, I.prop.1 hx, RightIdeal.scalar_mul d hd.ne' x⟩⟩
  exact Finite.of_injective f fun _ _ h =>
    Subtype.ext (RightIdeal.ext (congrArg
      (fun K : {K : Submodule ℤ (B a b) // J.lattice ≤ K ∧ ∀ x ∈ K, d • x ∈ J.lattice} =>
        K.val) h))

end ZInQ.Manuscript.RC.Eichler

/-! Axiom audit -/

#print axioms ZInQ.Manuscript.RC.Eichler.RightIdeal.scalar_mul
#print axioms ZInQ.Manuscript.RC.Eichler.RightIdeal.scalar_comm
#print axioms ZInQ.Manuscript.RC.Eichler.RightIdeal.lattice_scalar_le
#print axioms ZInQ.Manuscript.RC.Eichler.RightIdeal.relIndex_scalar
#print axioms ZInQ.Manuscript.RC.Eichler.RightIdeal.translate_le_iff
#print axioms ZInQ.Manuscript.RC.Eichler.RightIdeal.relIndex_translate
#print axioms ZInQ.Manuscript.RC.Eichler.RightIdeal.IsNeighbour
#print axioms ZInQ.Manuscript.RC.Eichler.RightIdeal.neighbour_dual
#print axioms ZInQ.Manuscript.RC.Eichler.RightIdeal.arrowsDual
#print axioms ZInQ.Manuscript.RC.Eichler.exists_bounded_integral_representative
#print axioms ZInQ.Manuscript.RC.Eichler.finite_integral_bounded
