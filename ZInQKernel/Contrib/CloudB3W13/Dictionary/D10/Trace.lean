/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.Interfaces

/-!
# D10: the `twist` clause over the FLT fine moduli scheme (W13)

For `α ∈ Aut(𝒪)` the FLT objects are twisted by `act ↦ act ∘ α` (same scheme, group law, level
subscheme and level point). Since `α` preserves the reduced trace (`trd_ringEquiv`, from the
quadratic relation and integrality on the order), the twisted datum is again a fake elliptic curve
with full level `3`. `ptF ∘ twist` is a second fine-moduli structure on the same `M`, so the FLT
uniqueness theorem `IsFineModuli.exists_iso_of_isFineModuli` produces the automorphism `g`; the
fibre comparison is as in D9.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj

namespace D10

/-! ### `α` preserves the reduced trace -/

theorem two_re_eq_of_mem (x : LeafQM.O) :
    ∃ T : ℤ, 2 * (x : ℍ[ℚ, 2, -3]).re = T :=
  (trd_nrd_int oLattice_isOrder ((order_bridge.2.2 _).mpr x.2)).1

theorem quad (y : ℍ[ℚ, 2, -3]) :
    y ^ 2 - ((2 * y.re : ℚ) : ℍ[ℚ, 2, -3]) * y + ((nrd y : ℚ) : ℍ[ℚ, 2, -3]) = 0 := by
  have h := aeval_charpoly y
  simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    QuaternionAlgebra.coe_algebraMap] at h
  rw [QuaternionAlgebra.coe_mul]; exact h

theorem re_eq_of_two_smul {X : ℍ[ℚ, 2, -3]} {c : ℚ} (h : (2 : ℚ) • X = (c : ℍ[ℚ, 2, -3])) :
    2 * X.re = c := by
  have := congrArg QuaternionAlgebra.re h
  simpa using this

theorem trd_ringEquiv (α : LeafQM.O ≃+* LeafQM.O) (x : LeafQM.O) :
    (α x : ℍ[ℚ, 2, -3]).re = (x : ℍ[ℚ, 2, -3]).re := by
  set X : ℍ[ℚ, 2, -3] := (↑x : ℍ[ℚ, 2, -3])
  set Y : ℍ[ℚ, 2, -3] := (↑(α x) : ℍ[ℚ, 2, -3])
  obtain ⟨T, hT⟩ := two_re_eq_of_mem x
  obtain ⟨N, hN⟩ := (trd_nrd_int oLattice_isOrder ((order_bridge.2.2 _).mpr x.2)).2
  have hx : x ^ 2 - (T : LeafQM.O) * x + (N : LeafQM.O) = 0 := by
    apply Subtype.ext
    have := quad X
    rw [hT, hN, QuaternionAlgebra.coe_intCast, QuaternionAlgebra.coe_intCast] at this
    push_cast
    exact this
  have hy : (α x) ^ 2 - (T : LeafQM.O) * α x + (N : LeafQM.O) = 0 := by
    have := congrArg α hx
    simpa using this
  have hyH : Y ^ 2 - ((T : ℚ) : ℍ[ℚ, 2, -3]) * Y + ((N : ℚ) : ℍ[ℚ, 2, -3]) = 0 := by
    have := congrArg Subtype.val hy
    push_cast at this
    rw [QuaternionAlgebra.coe_intCast, QuaternionAlgebra.coe_intCast]
    exact this
  have hqY := quad Y
  have h1 : ((T : ℚ) : ℍ[ℚ, 2, -3]) * Y = Y ^ 2 + ((N : ℚ) : ℍ[ℚ, 2, -3]) := by
    rw [sub_add_eq_add_sub, sub_eq_zero] at hyH; exact hyH.symm
  have h2 : ((2 * Y.re : ℚ) : ℍ[ℚ, 2, -3]) * Y = Y ^ 2 + ((nrd Y : ℚ) : ℍ[ℚ, 2, -3]) := by
    rw [sub_add_eq_add_sub, sub_eq_zero] at hqY; exact hqY.symm
  by_contra hne
  have hd : (2 * Y.re - T : ℚ) ≠ 0 := by
    intro h0
    apply hne
    linarith
  have hlin : (2 * Y.re - T : ℚ) • Y = ((nrd Y - N : ℚ) : ℍ[ℚ, 2, -3]) := by
    rw [sub_smul, ← QuaternionAlgebra.coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul_eq_smul, h1, h2,
      QuaternionAlgebra.coe_sub]
    abel
  set c : ℚ := (2 * Y.re - T)⁻¹ * (nrd Y - N)
  have hYc : Y = (c : ℍ[ℚ, 2, -3]) := by
    have := congrArg (fun z => (2 * Y.re - T : ℚ)⁻¹ • z) hlin
    simp only [smul_smul, inv_mul_cancel₀ hd, one_smul] at this
    rw [this, ← QuaternionAlgebra.coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul]
  obtain ⟨T', hT'⟩ := two_re_eq_of_mem (α x)
  have hYre : Y.re = c := by rw [hYc]; simp
  have hYY : α x + α x = (T' : LeafQM.O) := by
    apply Subtype.ext
    push_cast
    show Y + Y = _
    rw [hYc, ← QuaternionAlgebra.coe_add, ← QuaternionAlgebra.coe_intCast]
    congr 1
    have : 2 * Y.re = T' := hT'
    linarith
  have hXX : x + x = (T' : LeafQM.O) := by
    have := congrArg α.symm hYY
    simpa using this
  have hre : 2 * X.re = T' := by
    have := congrArg (fun z : LeafQM.O => (z : ℍ[ℚ, 2, -3]).re) hXX
    simp only [Subring.coe_add, QuaternionAlgebra.re_add] at this
    rw [two_mul, this]
    simp
  apply hne
  have : 2 * Y.re = T' := hT'
  linarith

end D10

end ZInQ.Contrib.CloudB2Shimura.Dictionary
