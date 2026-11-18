import ZInQKernel.Contrib.OneProof.RC.Eichler.Order

/-!
# An explicit order in the algebra `(-1,-ell)`

On-the-spot (c), for tex 8437 and 8462–8464. The integer basis is
`1, i, (1+j)/2, (i+k)/2` for `ell = 4m - 1`. This file verifies the order;
the local maximality and ramification of this choice are separate assertions.
-/

open scoped Quaternion
open Module

namespace ZInQ.Manuscript.RC.Eichler

abbrev ExplicitB (m : ℤ) := B (-1) (1 - 4 * (m : ℚ))

/-- Coordinates on `1, i, (1+j)/2, (i+k)/2`. -/
def explicitCoords (m : ℤ) : ExplicitB m ≃ₗ[ℚ] (Fin 4 → ℚ) where
  toFun x := ![x.re - x.imJ, x.imI - x.imK, 2 * x.imJ, 2 * x.imK]
  invFun z := ⟨z 0 + z 2 / 2, z 1 + z 3 / 2, z 2 / 2, z 3 / 2⟩
  left_inv x := by ext <;> simp
  right_inv z := by ext i; fin_cases i <;> simp <;> ring
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' t x := by ext i; fin_cases i <;> simp <;> ring

private def fromInts (m : ℤ) (v : Fin 4 → ℤ) : ExplicitB m :=
  (explicitCoords m).symm (fun i => (v i : ℚ))

private theorem fromInts_mul (m : ℤ) (x y : Fin 4 → ℤ) :
    fromInts m x * fromInts m y = fromInts m ![
      x 0 * y 0 - x 1 * y 1 - x 3 * y 1 - m * (x 2 * y 2 + x 3 * y 3),
      x 0 * y 1 + x 1 * y 0 + x 2 * y 1 - m * (x 3 * y 2 - x 2 * y 3),
      x 0 * y 2 - x 1 * y 3 + x 2 * y 0 + x 3 * y 1 + x 2 * y 2,
      x 0 * y 3 + x 1 * y 2 + x 3 * y 0 - x 2 * y 1 + x 3 * y 2] := by
  apply (explicitCoords m).injective
  ext i
  fin_cases i <;> simp [fromInts, explicitCoords] <;> ring

/-- Explicit integer order in `(-1,1-4m)`. -/
noncomputable def explicitOrder (m : ℤ) : Order (-1) (1 - 4 * (m : ℚ)) := by
  let e := Basis.ofEquivFun (explicitCoords m)
  let L := Submodule.span ℤ (Set.range e)
  have hL (x : ExplicitB m) : x ∈ L ↔ ∃ v, fromInts m v = x := by
    rw [e.mem_span_iff_repr_mem ℤ x]
    constructor
    · intro hx
      choose v hv using hx
      exact ⟨v, (explicitCoords m).injective (by
        rw [fromInts, LinearEquiv.apply_symm_apply]
        funext i
        exact hv i)⟩
    · rintro ⟨v, rfl⟩ i
      refine ⟨v i, ?_⟩
      change ((v i : ℤ) : ℚ) = (explicitCoords m (fromInts m v)) i
      simp [fromInts]
  refine ⟨{
    carrier := L
    zero_mem' := L.zero_mem
    add_mem' := L.add_mem
    neg_mem' := L.neg_mem
    one_mem' := (hL 1).mpr ⟨![1,0,0,0], by
      ext <;> norm_num [fromInts, explicitCoords]⟩
    mul_mem' := fun {x y} hx hy => by
      obtain ⟨v, rfl⟩ := (hL x).mp hx
      obtain ⟨w, rfl⟩ := (hL y).mp hy
      exact (hL _).mpr ⟨_, (fromInts_mul m v w).symm⟩ }, ?_⟩
  change FullLattice L
  exact ⟨Submodule.fg_span (Set.finite_range e), by
    rw [Submodule.span_span_of_tower, e.span_eq]⟩

/-- The explicit order at a prime (or positive integer) congruent to three modulo four. -/
noncomputable def explicitOrderAt (ell : ℕ) (h : ell % 4 = 3) : Order (-1) (-(ell : ℚ)) := by
  let m : ℤ := (ell / 4 : ℕ) + 1
  have he : (ell : ℤ) = 4 * m - 1 := by dsimp [m]; omega
  have he' : (ell : ℚ) = 4 * (m : ℚ) - 1 := by exact_mod_cast he
  have hb : 1 - 4 * (m : ℚ) = -(ell : ℚ) := by linarith
  rw [← hb]
  exact explicitOrder m

/-- The explicit algebra is ramified at the real place, in the existing norm-form sense. -/
theorem explicit_anisotropic_real {ell : ℕ} (hell : 0 < ell) :
    AppF.NormFormAnisotropic ℝ (-1) (-(ell : ℝ)) := by
  intro x y z t h
  have hp : (0 : ℝ) < ell := by exact_mod_cast hell
  have h₀ := sq_nonneg x
  have h₁ := sq_nonneg y
  have h₂ := mul_nonneg hp.le (sq_nonneg z)
  have h₃ := mul_nonneg hp.le (sq_nonneg t)
  have hz : (ell : ℝ) * z ^ 2 = 0 := by nlinarith
  have ht : (ell : ℝ) * t ^ 2 = 0 := by nlinarith
  exact ⟨sq_eq_zero_iff.mp (by nlinarith), sq_eq_zero_iff.mp (by nlinarith),
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left hp.ne'),
    sq_eq_zero_iff.mp ((mul_eq_zero.mp ht).resolve_left hp.ne')⟩

end ZInQ.Manuscript.RC.Eichler

/-! Axiom audit -/

#print axioms ZInQ.Manuscript.RC.Eichler.fromInts_mul
#print axioms ZInQ.Manuscript.RC.Eichler.explicitOrder
#print axioms ZInQ.Manuscript.RC.Eichler.explicitOrderAt
#print axioms ZInQ.Manuscript.RC.Eichler.explicit_anisotropic_real
