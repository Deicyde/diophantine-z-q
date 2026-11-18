import ZInQKernel.Contrib.OneProof.RC.Eichler.Order

/-!
# Full right ideals and their left orders

The ideal description of the class set in tex 8466–8468 uses full fractional right
ideals, with local principality imposed in the local model. The left order and transport
arguments here are on-the-spot (c).
-/

open Module

namespace ZInQ.Manuscript.RC.Eichler

namespace FullLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Given two full lattices, a nonzero integer multiple of the first is in the second. -/
theorem multiple_mem {L M : Submodule ℤ V} (hL : FullLattice L) (hM : FullLattice M)
    {ι : Type*} [Fintype ι] (b : Basis ι ℚ V) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, d • x ∈ M := by
  classical
  let c := hM.ratBasis b
  obtain ⟨d, hd, h⟩ := commonDenom c hL.fg
  refine ⟨d, hd, fun x hx => ?_⟩
  rw [← hM.span_ratBasis b]
  apply (c.mem_span_iff_repr_mem ℤ _).mpr
  intro i
  obtain ⟨z, hz⟩ := h x hx i
  refine ⟨z, ?_⟩
  change (z : ℚ) = c.repr (d • x) i
  simpa only [← Int.cast_smul_eq_zsmul ℚ, map_smul, Finsupp.smul_apply, smul_eq_mul] using hz

end FullLattice

variable {a b : ℚ} (R : Order a b)

/-- A full fractional right ideal, before imposing local principality. -/
structure RightIdeal where
  lattice : Submodule ℤ (B a b)
  full : FullLattice lattice
  mul_mem : ∀ ⦃x r : B a b⦄, x ∈ lattice → r ∈ R.ring → x * r ∈ lattice

namespace RightIdeal

variable {R}

@[ext]
theorem ext {I J : RightIdeal R} (h : I.lattice = J.lattice) : I = J := by
  cases I
  cases J
  cases h
  rfl

/-- The order itself as a right ideal. -/
def self (R : Order a b) : RightIdeal R where
  lattice := R.lattice
  full := R.full
  mul_mem := fun {_ _} hx hr => R.ring.mul_mem hx hr

/-- The left order of a right ideal, as a subring of the ambient quaternion algebra. -/
def leftRing (I : RightIdeal R) : Subring (B a b) where
  carrier := {u | ∀ x ∈ I.lattice, u * x ∈ I.lattice}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' hu hv x hx := by rw [add_mul]; exact I.lattice.add_mem (hu x hx) (hv x hx)
  neg_mem' hu x hx := by rw [neg_mul]; exact I.lattice.neg_mem (hu x hx)
  mul_mem' hu hv x hx := by rw [mul_assoc]; exact hu _ (hv x hx)

theorem exists_ne_zero (I : RightIdeal R) : ∃ x ∈ I.lattice, x ≠ 0 := by
  by_contra! h
  have he : I.lattice = ⊥ := le_bot_iff.mp fun x hx => by simpa using h x hx
  have ht := I.full.span_eq_top
  rw [he, Submodule.bot_coe, Submodule.span_zero_singleton] at ht
  exact bot_ne_top ht

/-- For definite `B`, the left ring is itself a full integer order. -/
def leftOrder (I : RightIdeal R) (ha : a < 0) (hb : b < 0) : Order a b where
  ring := I.leftRing
  full := by
    let b₀ := QuaternionAlgebra.basisOneIJK a 0 b
    obtain ⟨x, hx, hx0⟩ := I.exists_ne_zero
    let u := unitOfNeZero ha hb x hx0
    let L := I.leftRing.toAddSubgroup.toIntSubmodule
    let φ : L →ₗ[ℤ] I.lattice := {
      toFun := fun y => ⟨y.val * x, y.prop x hx⟩
      map_add' := fun _ _ => Subtype.ext (add_mul _ _ _)
      map_smul' := fun _ _ => Subtype.ext (smul_mul_assoc _ _ _) }
    have hφ : Function.Injective φ := by
      intro y z hz
      apply Subtype.ext
      have h : y.val * (u : B a b) = z.val * (u : B a b) := congrArg Subtype.val hz
      simpa only [mul_assoc, Units.mul_inv, mul_one] using
        congrArg (fun t : B a b => t * (↑u⁻¹ : B a b)) h
    let : Module.Finite ℤ I.lattice := Module.Finite.of_fg I.full.fg
    have : IsNoetherian ℤ L := isNoetherian_of_injective φ hφ
    refine ⟨(L.fg_top).mp (IsNoetherian.noetherian (⊤ : Submodule ℤ L)), ?_⟩
    obtain ⟨d, hd, hdI⟩ := I.full.multiple_mem R.full b₀
    obtain ⟨e, he, heR⟩ := R.full.multiple_mem I.full b₀
    have hmem (r : B a b) (hr : r ∈ R.lattice) :
        (e * d) • r ∈ L := by
      intro y hy
      rw [mul_smul, smul_mul_assoc, smul_mul_assoc, ← mul_smul_comm d r y]
      exact heR _ (R.ring.mul_mem hr (hdI y hy))
    refine top_unique ?_
    rw [← R.full.span_eq_top]
    apply Submodule.span_le.mpr
    intro r hr
    have ht := Submodule.subset_span (R := ℚ) (s := (L : Set (B a b))) (hmem r hr)
    have hd' : ((e * d : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (mul_ne_zero he hd)
    rw [← Int.cast_smul_eq_zsmul ℚ] at ht
    have hv := Submodule.smul_mem (Submodule.span ℚ (L : Set (B a b))) ((↑(e * d : ℤ) : ℚ)⁻¹) ht
    rw [smul_smul, inv_mul_cancel₀ hd', one_smul] at hv
    exact hv

end RightIdeal

end ZInQ.Manuscript.RC.Eichler
