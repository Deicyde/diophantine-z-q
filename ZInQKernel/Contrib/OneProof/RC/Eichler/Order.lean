import ZInQKernel.Contrib.OneProof.RC.Eichler.Lattice
import ZInQKernel.Contrib.OneProof.RC.Odd.Constants
import ZInQKernel.Contrib.OneProof.RC.AppF.Prints

/-!
# Integer orders and their unit groups

Tex 8464–8468, 8571–8576 and 8605–8611. The proofs about integer lattices and reduced norms
are on-the-spot (c); the norm and the divisibility constant are the existing tree definitions.
-/

open scoped Quaternion
open Module

namespace ZInQ.Manuscript.RC.Eichler

variable {a b : ℚ}

/-- An integer order in the quaternion algebra: a unital subring which is a full lattice. -/
structure Order (a b : ℚ) where
  ring : Subring (B a b)
  full : FullLattice ring.toAddSubgroup.toIntSubmodule

namespace Order

abbrev lattice (R : Order a b) : Submodule ℤ (B a b) := R.ring.toAddSubgroup.toIntSubmodule

/-- The rank four integer basis required by `Odd.card_dvd_c0_of_basis`. -/
noncomputable def basis (R : Order a b) : Basis (Fin 4) ℤ R.ring :=
  R.full.basis (QuaternionAlgebra.basisOneIJK a 0 b)

/-- The image of the units of the order in the ambient quaternion units. -/
def unitsHom (R : Order a b) : R.ringˣ →* (B a b)ˣ := Units.map R.ring.subtype

theorem unitsHom_injective (R : Order a b) : Function.Injective R.unitsHom :=
  fun _ _ h => Units.ext (Subtype.val_injective (congrArg Units.val h))

/-- The subgroup type of the `Visibility.ThetaStage.G` field. -/
def G (R : Order a b) : Subgroup (B a b)ˣ := R.unitsHom.range

/-- The order's units and their image in the ambient unit group have the same cardinality. -/
noncomputable def unitsEquiv (R : Order a b) : R.ringˣ ≃ R.G :=
  Equiv.ofBijective R.unitsHom.rangeRestrict
    ⟨fun _ _ h => R.unitsHom_injective (congrArg Subtype.val h),
      fun ⟨_, hx⟩ => by
        obtain ⟨u, hu⟩ := hx
        exact ⟨u, Subtype.ext hu⟩⟩

private def normHom : B a b →* ℚ where
  toFun := Visibility.nrd
  map_one' := Visibility.nrd_one
  map_mul' := Visibility.nrd_mul

/-- In a definite order every unit has reduced norm one (tex 8571–8576).
If its norm were below one, its distinct powers would all fit in a finite norm ball.
Apply the same argument to its inverse to exclude norm above one. -/
theorem nrd_unit (R : Order a b) (ha : a < 0) (hb : b < 0) (u : R.ringˣ) :
    Visibility.nrd (R.unitsHom u : B a b) = 1 := by
  have hpos (v : R.ringˣ) : 0 < Visibility.nrd (R.unitsHom v : B a b) := by
    apply nrd_pos ha hb
    exact (Units.isUnit (R.unitsHom v)).ne_zero
  have hge (v : R.ringˣ) : 1 ≤ Visibility.nrd (R.unitsHom v : B a b) := by
    by_contra! hlt
    let f : ℕ → {x : B a b | x ∈ R.lattice ∧ Visibility.nrd x ≤ 1} := fun n =>
      ⟨(R.unitsHom v : B a b) ^ n, by
        change (R.unitsHom v : B a b) ^ n ∈ R.ring
        exact R.ring.pow_mem (v.val.prop) n,
        show normHom ((R.unitsHom v : B a b) ^ n) ≤ 1 by
          rw [map_pow]
          exact pow_le_one₀ (hpos v).le hlt.le⟩
    have hfin := finite_norm_le ha hb R.lattice R.full.fg 1
    let := hfin.to_subtype
    have hinj : Function.Injective f := by
      intro m n he
      have hn := congrArg (fun x => normHom x.val) he
      change normHom ((R.unitsHom v : B a b) ^ m) =
        normHom ((R.unitsHom v : B a b) ^ n) at hn
      rw [map_pow, map_pow] at hn
      exact (pow_right_strictAnti₀ (hpos v) hlt).injective hn
    let := Finite.of_injective f hinj
    exact not_finite ℕ
  have hmul : Visibility.nrd (R.unitsHom u : B a b) *
      Visibility.nrd (R.unitsHom u⁻¹ : B a b) = 1 := by
    rw [← Visibility.nrd_mul, map_inv, Units.mul_inv, Visibility.nrd_one]
  have hu := hge u
  have hv := hge u⁻¹
  have hm := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)
  exact le_antisymm (by nlinarith) hu

/-- The unit group of a definite order is finite (tex 8467–8468). -/
theorem finite_units (R : Order a b) (ha : a < 0) (hb : b < 0) : Finite R.ringˣ := by
  let f (u : R.ringˣ) : {x : B a b | x ∈ R.lattice ∧ Visibility.nrd x ≤ 1} :=
    ⟨(R.unitsHom u : B a b), u.val.prop, (R.nrd_unit ha hb u).le⟩
  have hfin := finite_norm_le ha hb R.lattice R.full.fg 1
  let := hfin.to_subtype
  apply Finite.of_injective f
  intro u v h
  have hv : (R.unitsHom u : B a b) = (R.unitsHom v : B a b) :=
    congrArg (fun y : {x : B a b | x ∈ R.lattice ∧ Visibility.nrd x ≤ 1} => y.val) h
  exact R.unitsHom_injective (Units.ext hv)

theorem finite_G (R : Order a b) (ha : a < 0) (hb : b < 0) : Finite R.G := by
  let := R.finite_units ha hb
  exact Finite.of_equiv _ R.unitsEquiv

/-- The divisibility required by `Visibility.ThetaStage.card_G_dvd`. -/
theorem card_G_dvd (R : Order a b) (ha : a < 0) (hb : b < 0) : Nat.card R.G ∣ Odd.c0 := by
  let := R.finite_units ha hb
  have h := Odd.card_dvd_c0_of_basis R.basis (⊤ : Subgroup R.ringˣ)
  let e : (⊤ : Subgroup R.ringˣ) ≃ R.G := Subgroup.topEquiv.toEquiv.trans R.unitsEquiv
  rw [← Nat.card_congr e]
  exact h

end Order

/-- Anisotropy at infinity in the existing ramification predicate forces both parameters negative. -/
theorem neg_of_ramified {ell : ℕ} (h : AppF.RamifiedExactlyAtEll0Infty ell a b) :
    a < 0 ∧ b < 0 := by
  constructor
  · by_contra! ha
    have ha' : 0 ≤ (a : ℝ) := by exact_mod_cast ha
    have ht := h.2.2.1 (Real.sqrt a) 1 0 0 (by simpa using sub_eq_zero.mpr (Real.sq_sqrt ha'))
    exact one_ne_zero ht.2.1
  · by_contra! hb
    have hb' : 0 ≤ (b : ℝ) := by exact_mod_cast hb
    have ht := h.2.2.1 (Real.sqrt b) 0 1 0 (by simpa using sub_eq_zero.mpr (Real.sq_sqrt hb'))
    exact one_ne_zero ht.2.2.1

end ZInQ.Manuscript.RC.Eichler
