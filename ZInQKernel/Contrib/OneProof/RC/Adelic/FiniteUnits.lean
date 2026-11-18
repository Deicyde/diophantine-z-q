import ZInQKernel.Contrib.OneProof.RC.Adelic.FullPatch
import ZInQKernel.Contrib.OneProof.RC.Eichler.ClassSet

/-!
# The finite adelic unit group and the double cosets
Tex 8465–8468. The restricted product uses the unit groups of the local orders.
The finite-support and diagonal inclusion proofs are on-the-spot (c).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Adelic

open Eichler Module QuaternionAlgebra

variable {a b : ℚ}

/-- The embedded unit group of a completed order. -/
def localUnits (R : Order a b) (p : Prime) : Subgroup (Bp p.val a b)ˣ where
  carrier := {u | (u : Bp p.val a b) ∈ R.completion p.val ∧
    (↑u⁻¹ : Bp p.val a b) ∈ R.completion p.val}
  one_mem' := by simp
  mul_mem' {u v} hu hv := by
    rw [Set.mem_ofPred_eq, mul_inv_rev]
    exact ⟨(R.completion p.val).mul_mem hu.1 hv.1, (R.completion p.val).mul_mem hv.2 hu.2⟩
  inv_mem' {u} hu := ⟨hu.2, by simpa only [inv_inv] using hu.1⟩

theorem localUnits_eq_range (R : Order a b) (p : Prime) :
    localUnits R p = (Units.map (R.completion p.val).val.toMonoidHom).range := by
  ext u
  constructor
  · intro h
    let v : (R.completion p.val)ˣ :=
      ⟨⟨u.val, h.1⟩, ⟨u.inv, h.2⟩, Subtype.ext u.val_inv, Subtype.ext u.inv_val⟩
    exact ⟨v, Units.ext rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v.val.prop, v.inv.prop⟩

abbrev LocalFamily (a b : ℚ) := (p : Prime) → (Bp p.val a b)ˣ

def restrictedUnits (R : Order a b) : Subgroup (LocalFamily a b) where
  carrier := {z | {p | z p ∉ localUnits R p}.Finite}
  one_mem' := by simp
  mul_mem' {z w} hz hw := by
    refine (hz.union hw).subset ?_
    intro p hp
    by_contra h
    change ¬ (z p ∉ localUnits R p ∨ w p ∉ localUnits R p) at h
    exact hp ((localUnits R p).mul_mem (not_not.mp (not_or.mp h).1)
      (not_not.mp (not_or.mp h).2))
  inv_mem' {z} hz := hz.subset fun p hp hz' => hp ((localUnits R p).inv_mem hz')

abbrev FiniteUnits (R : Order a b) := restrictedUnits R

/-- The subgroup consisting of everywhere integral units. -/
def integralUnits (R : Order a b) : Subgroup (FiniteUnits R) where
  carrier := {z | ∀ p, z.val p ∈ localUnits R p}
  one_mem' := fun p => (localUnits R p).one_mem
  mul_mem' h₁ h₂ p := (localUnits R p).mul_mem (h₁ p) (h₂ p)
  inv_mem' h p := (localUnits R p).inv_mem (h p)

private theorem exists_nat_multiple {L M : Submodule ℤ (B a b)} (hL : L.FG)
    (hM : FullLattice M) : ∃ m : ℕ, m ≠ 0 ∧ ∀ x ∈ L, m • x ∈ M := by
  let e := hM.ratBasis (basisOneIJK a 0 b)
  obtain ⟨d, hd, hdL⟩ := commonDenom e hL
  refine ⟨d.natAbs, Int.natAbs_ne_zero.mpr hd, fun x hx => ?_⟩
  have hz : d • x ∈ M := by
    rw [← hM.span_ratBasis (basisOneIJK a 0 b)]
    apply (e.mem_span_iff_repr_mem ℤ _).mpr
    intro i
    obtain ⟨z, hz⟩ := hdL x hx i
    refine ⟨z, ?_⟩
    change (z : ℚ) = e.repr (d • x) i
    simpa only [← Int.cast_smul_eq_zsmul ℚ, map_smul, Finsupp.smul_apply, smul_eq_mul] using hz
  have he : (d.natAbs : ℤ) = d ∨ (d.natAbs : ℤ) = -d := by
    rcases Int.natAbs_eq d with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by omega)
  rw [← Nat.cast_smul_eq_nsmul ℤ]
  rcases he with h | h
  · simpa only [h] using hz
  · simpa only [h, neg_smul] using M.neg_mem hz

private theorem local_le_of_multiple {L M : Submodule ℤ (B a b)} (p : Prime)
    {m : ℕ} (hm : ¬ p.val ∣ m) (h : ∀ x ∈ L, m • x ∈ M) :
    localLattice p.val L ≤ localLattice p.val M := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  have hx' : toLocal p.val (m • x) ∈ localLattice p.val M :=
    Submodule.subset_span (Set.mem_image_of_mem _ (h x hx))
  obtain ⟨u, hu⟩ := nat_isUnit p hm
  rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p.val], ← hu] at hx'
  change toLocal p.val x ∈ localLattice p.val M
  simpa only [smul_smul, Units.inv_mul, one_smul] using
    (localLattice p.val M).smul_mem (↑u⁻¹ : ℤ_[p.val]) hx'

/-- Two full rational lattices have equal completions outside a finite set. -/
theorem finite_localLattice_ne {L M : Submodule ℤ (B a b)}
    (hL : FullLattice L) (hM : FullLattice M) :
    {p : Prime | localLattice p.val L ≠ localLattice p.val M}.Finite := by
  obtain ⟨m, hm, hml⟩ := exists_nat_multiple hL.fg hM
  obtain ⟨n, hn, hnl⟩ := exists_nat_multiple hM.fg hL
  refine ((finite_prime_dvd hm).union (finite_prime_dvd hn)).subset ?_
  intro p hp
  by_contra h
  have h' : ¬ p.val ∣ m ∧ ¬ p.val ∣ n := by simpa using h
  exact hp (le_antisymm (local_le_of_multiple p h'.1 hml) (local_le_of_multiple p h'.2 hnl))

/-- Every rational quaternion is integral in the order at almost every prime. -/
theorem finite_not_mem_completion (R : Order a b) (x : B a b) :
    {p : Prime | toLocal p.val x ∉ R.completion p.val}.Finite := by
  let L := Submodule.span ℤ ({x} : Set (B a b))
  obtain ⟨m, hm, hmul⟩ := exists_nat_multiple (L := L)
    (Submodule.fg_span (Set.finite_singleton _)) R.full
  refine (finite_prime_dvd hm).subset ?_
  intro p hp
  by_contra h
  apply hp
  have hx : toLocal p.val x ∈ localLattice p.val L :=
    Submodule.subset_span (Set.mem_image_of_mem _ (Submodule.mem_span_singleton_self x))
  change toLocal p.val x ∈ (R.completion p.val).toSubmodule
  rw [R.completion_toSubmodule]
  exact local_le_of_multiple p h hmul hx

/-- Rational units embed diagonally in the restricted product. -/
def diagonal (R : Order a b) : (B a b)ˣ →* FiniteUnits R where
  toFun u := ⟨fun p => Units.map (toLocal p.val).toMonoidHom u, by
    refine ((finite_not_mem_completion R u.val).union
      (finite_not_mem_completion R u.inv)).subset ?_
    intro p hp
    by_contra h
    exact hp ⟨by simpa using (not_or.mp h).1, by simpa using (not_or.mp h).2⟩⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' u v := Subtype.ext (funext fun _ => map_mul _ u v)

theorem diagonal_injective (R : Order a b) : Function.Injective (diagonal R) := by
  intro u v h
  let p : Prime := ⟨2, Nat.prime_two⟩
  let _ : Fact p.val.Prime := ⟨p.prop⟩
  have he := congrArg (fun z : FiniteUnits R => (z.val p).val) h
  change toLocal p.val u.val = toLocal p.val v.val at he
  exact Units.ext (QuaternionAlgebra.ext
    (Rat.cast_injective (congrArg QuaternionAlgebra.re he))
    (Rat.cast_injective (congrArg QuaternionAlgebra.imI he))
    (Rat.cast_injective (congrArg QuaternionAlgebra.imJ he))
    (Rat.cast_injective (congrArg QuaternionAlgebra.imK he)))

/-- The relation defining (B^\times\backslash\widehat B^\times/\widehat R^\times). -/
def doubleCosetRel (R : Order a b) : Setoid (FiniteUnits R) where
  r z w := ∃ u : (B a b)ˣ, ∃ r : integralUnits R, w = diagonal R u * z * r.val
  iseqv := {
    refl z := ⟨1, 1, by simp⟩
    symm := by
      rintro z _ ⟨u, r, rfl⟩
      exact ⟨u⁻¹, r⁻¹, by simp [mul_assoc, ← mul_assoc (diagonal R u)⁻¹ (diagonal R u)]⟩
    trans := by
      rintro z _ _ ⟨u, r, rfl⟩ ⟨v, s, rfl⟩
      exact ⟨v * u, r * s, by simp [mul_assoc]⟩ }

abbrev DoubleCosets (R : Order a b) := Quotient (doubleCosetRel R)

#print axioms localUnits_eq_range
#print axioms exists_nat_multiple
#print axioms local_le_of_multiple
#print axioms finite_localLattice_ne
#print axioms finite_not_mem_completion
#print axioms diagonal_injective

end ZInQ.Manuscript.RC.Adelic
