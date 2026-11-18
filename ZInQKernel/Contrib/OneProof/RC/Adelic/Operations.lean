import ZInQKernel.Contrib.OneProof.RC.Adelic.Level
import ZInQKernel.Contrib.OneProof.RC.Adelic.RightAction
import ZInQKernel.Contrib.OneProof.RC.Eichler.Neighbours
import ZInQKernel.Contrib.OneProof.RC.LocalDivision.Residue

/-!
# The Atkin–Lehner and division uniformizer permutations
Tex 8487–8490, 9331–9358. The split matrix and the proof of descent are
on-the-spot (c); the division order and uniformizer are imported.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Adelic

open Eichler Matrix

private def swapUnit {K : Type*} [Field K] (d : K) (hd : d ≠ 0) : (M2 K)ˣ where
  val := !![0, 1; d, 0]
  inv := !![0, d⁻¹; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hd]

/-- In the lower-left congruence convention the matrix is [0,1; p^e,0]. -/
def atkinMatrix (p : Prime) (e : ℕ) : (M2 ℚ_[p.val])ˣ :=
  swapUnit ((p.val : ℚ_[p.val]) ^ e) (pow_ne_zero _ (Nat.cast_ne_zero.mpr p.prop.ne_zero))

theorem atkinMatrix_square (p : Prime) (e : ℕ) :
    (atkinMatrix p e : M2 ℚ_[p.val]) * atkinMatrix p e =
      algebraMap ℚ_[p.val] (M2 ℚ_[p.val]) ((p.val : ℚ_[p.val]) ^ e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinMatrix, swapUnit, Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_matrix_apply]

private theorem atkinMatrix_conj_formula (p : Prime) (e : ℕ) (x : M2 ℚ_[p.val]) :
    (↑(atkinMatrix p e)⁻¹ : M2 ℚ_[p.val]) * x * (atkinMatrix p e : M2 ℚ_[p.val]) =
      !![x 1 1, ((p.val : ℚ_[p.val]) ^ e)⁻¹ * x 1 0;
        (p.val : ℚ_[p.val]) ^ e * x 0 1, x 0 0] := by
  have hp : (p.val : ℚ_[p.val]) ^ e ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [atkinMatrix, swapUnit, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      mul_comm, ← mul_assoc, hp]

theorem atkinMatrix_conj (p : Prime) (e : ℕ) (x : M2 ℚ_[p.val]) :
    (↑(atkinMatrix p e)⁻¹ : M2 ℚ_[p.val]) * x * (atkinMatrix p e : M2 ℚ_[p.val]) ∈
      standardOrder p e ↔ x ∈ standardOrder p e := by
  let w := atkinMatrix p e
  let f (x : M2 ℚ_[p.val]) := (↑w⁻¹ : M2 ℚ_[p.val]) * x * (w : M2 ℚ_[p.val])
  have hp : (p.val : ℚ_[p.val]) ^ e ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)
  have hf (x : M2 ℚ_[p.val]) : f (f x) = x := by
    change (↑w⁻¹ : M2 ℚ_[p.val]) * f x * (w : M2 ℚ_[p.val]) = x
    rw [atkinMatrix_conj_formula]
    unfold f
    rw [atkinMatrix_conj_formula]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp]
  have hm (x : M2 ℚ_[p.val]) (hx : x ∈ standardOrder p e) : f x ∈ standardOrder p e := by
    obtain ⟨A, hA, rfl⟩ := hx
    obtain ⟨c, hc⟩ : (p.val : ℤ_[p.val]) ^ e ∣ A 1 0 := hA
    let B : M2 ℤ_[p.val] := !![A 1 1, c; (p.val : ℤ_[p.val]) ^ e * A 0 1, A 0 0]
    refine ⟨B, dvd_mul_right _ _, ?_⟩
    change matrixCast p.val B = f (matrixCast p.val A)
    unfold f
    rw [atkinMatrix_conj_formula]
    have hc' : (A 1 0 : ℚ_[p.val]) = (p.val : ℚ_[p.val]) ^ e * (c : ℚ_[p.val]) := by
      simpa only [PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast] using
        congrArg (fun z : ℤ_[p.val] => (z : ℚ_[p.val])) hc
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrixCast, B, hc', hp]
  exact ⟨fun h => hf x ▸ hm (f x) h, hm x⟩

section Level

variable (ell : ℕ) [Fact ell.Prime] (h : ell % 4 = 3)
variable (N : ℕ) (hN : 0 < N)

abbrev LevelR := levelOrder ell h N hN

private def atkinLocal (p : Prime) (hp : p.val ≠ ell) :
    (Bp p.val (-1) (-(ell : ℚ)))ˣ :=
  Units.map (splitChart ell h p hp).symm.toMonoidHom (atkinMatrix p (N.factorization p.val))

private theorem atkinLocal_conj (p : Prime) (hp : p.val ≠ ell)
    (x : Bp p.val (-1) (-(ell : ℚ))) :
    (↑(atkinLocal ell h N p hp)⁻¹ : Bp p.val (-1) (-(ell : ℚ))) * x *
        (atkinLocal ell h N p hp : Bp p.val (-1) (-(ell : ℚ))) ∈
      (LevelR ell h N hN).completion p.val ↔ x ∈ (LevelR ell h N hN).completion p.val := by
  rw [levelOrder_completion, levelLocal_mem_split ell h N p hp,
    levelLocal_mem_split ell h N p hp]
  let f := splitChart ell h p hp
  change f (_ * x * _) ∈ _ ↔ f x ∈ _
  rw [map_mul, map_mul]
  have he : Units.map f.toMonoidHom (atkinLocal ell h N p hp) =
      atkinMatrix p (N.factorization p.val) := by
    apply Units.ext
    exact f.apply_symm_apply _
  have he' := congrArg Units.val (congrArg Inv.inv he)
  change f (↑(atkinLocal ell h N p hp)⁻¹) = _ at he'
  rw [he', show f ↑(atkinLocal ell h N p hp) = ↑(atkinMatrix p (N.factorization p.val)) from
    congrArg Units.val he]
  exact atkinMatrix_conj p _ _

private theorem split_of_factorization_pos (hcop : N.Coprime ell) (p : Prime)
    (he : 0 < N.factorization p.val) : p.val ≠ ell := by
  intro hh
  have hnd := ((Fact.out : ell.Prime).coprime_iff_not_dvd).mp hcop.symm
  apply Nat.ne_of_gt he
  exact Nat.factorization_eq_zero_of_not_dvd (hh.symm ▸ hnd)

private def atkinAdele (hcop : N.Coprime ell) (p : Prime) (he : 0 < N.factorization p.val) :
    FiniteUnits (LevelR ell h N hN) :=
  single _ p (atkinLocal ell h N p (split_of_factorization_pos ell N hcop p he))

/-- The algebraic Atkin–Lehner field of RC/PM. -/
def atkin (hcop : N.Coprime ell) (p : ℕ) (hp : p.Prime) (he : 0 < N.factorization p) :
    Equiv.Perm (ClassSet (LevelR ell h N hN)) :=
  let q : Prime := ⟨p, hp⟩
  let hq := split_of_factorization_pos ell N hcop q he
  rightClassPerm (atkinAdele ell h N hN hcop q he)
    (normalizes_single q _ (atkinLocal_conj ell h N hN q hq))

private theorem diagonal_scalar_val {a b : ℚ} (R : Order a b) (p : Prime)
    (m : ℕ) (hm : m ≠ 0) :
    ((diagonal R (RightIdeal.scalarUnit m hm)).val p : Bp p.val a b) =
      algebraMap ℚ_[p.val] (Bp p.val a b) (m : ℚ_[p.val]) := by
  change toLocal p.val (algebraMap ℚ (B a b) (m : ℚ)) = _
  ext <;> simp [toLocal]

theorem atkin_involutive (hcop : N.Coprime ell) (p : ℕ) (hp : p.Prime)
    (he : 0 < N.factorization p) :
    Function.Involutive (atkin ell h N hN hcop p hp he) := by
  let R := LevelR ell h N hN
  let q : Prime := ⟨p, hp⟩
  let _ : Fact q.val.Prime := ⟨hp⟩
  let e := N.factorization p
  let m := p ^ e
  have hm : m ≠ 0 := pow_ne_zero _ hp.ne_zero
  let u : (B (-1) (-(ell : ℚ)))ˣ := RightIdeal.scalarUnit m hm
  let k := atkinAdele ell h N hN hcop q he
  let r := (diagonal R u)⁻¹ * (k * k)
  have hunit : r ∈ integralUnits R := by
    intro t
    change ((diagonal R u).val t)⁻¹ * (k.val t * k.val t) ∈ localUnits R t
    by_cases ht : t = q
    · subst t
      have hsq : k.val q * k.val q = (diagonal R u).val q := by
        apply Units.ext
        change ((k.val q : Bp q.val (-1) (-(ell : ℚ))) *
          (k.val q : Bp q.val (-1) (-(ell : ℚ)))) = _
        unfold k atkinAdele
        rw [single_same, diagonal_scalar_val]
        let f := splitChart ell h q (split_of_factorization_pos ell N hcop q he)
        apply f.injective
        change f (f.symm _ * f.symm _) = _
        rw [map_mul, AlgEquiv.apply_symm_apply, atkinMatrix_square,
          f.commutes, Nat.cast_pow]
      rw [hsq, inv_mul_cancel]
      exact (localUnits R q).one_mem
    · unfold k atkinAdele
      rw [single_away ht, mul_one, mul_one]
      apply (localUnits R t).inv_mem
      have hd : ¬ t.val ∣ m := fun hd => ht (Subtype.ext
        ((Nat.prime_dvd_prime_iff_eq t.prop hp).mp (t.prop.dvd_of_dvd_pow hd)))
      obtain ⟨v, hv⟩ := nat_isUnit t hd
      let V := Units.map (algebraMap ℤ_[t.val] (R.completion t.val)).toMonoidHom v
      rw [localUnits_eq_range]
      refine ⟨V, Units.ext ?_⟩
      rw [diagonal_scalar_val]
      change algebraMap ℤ_[t.val] (Bp t.val (-1) (-(ell : ℚ))) (v : ℤ_[t.val]) = _
      rw [hv]
      rfl
  unfold atkin
  refine rightClassPerm_involutive _ _ u ?_ ⟨r, hunit⟩ ?_
  · intro z
    apply Subtype.ext
    funext t
    apply Units.ext
    change (z.val t : Bp t.val (-1) (-(ell : ℚ))) * ((diagonal R u).val t : Bp t.val (-1) (-(ell : ℚ))) =
      ((diagonal R u).val t : Bp t.val (-1) (-(ell : ℚ))) * (z.val t : Bp t.val (-1) (-(ell : ℚ)))
    rw [diagonal_scalar_val]
    exact (Algebra.commutes _ _).symm
  · exact (mul_inv_cancel_left (diagonal R u) (k * k)).symm

/-- The level order at the division prime is the same as the completed explicit order. -/
theorem level_completion_division :
    (LevelR ell h N hN).completion ell = DivisionJoin.completedOrder ell h := by
  let q : Prime := ⟨ell, Fact.out⟩
  rw [show (LevelR ell h N hN).completion ell = levelLocal ell h N q from
    levelOrder_completion ell h N hN q, levelLocal, dite_eq_right (not_not.mpr rfl)]

private def divisionUnit : (Bp ell (-1) (-(ell : ℚ)))ˣ :=
  letI : Fact (ell % 4 = 3) := ⟨h⟩
  Units.map (DivisionJoin.ambientEquiv ell).symm.toMonoidHom LocalDivision.uniformizer

theorem divisionUnit_normalizes (x : Bp ell (-1) (-(ell : ℚ))) :
    (↑(divisionUnit ell h)⁻¹ : Bp ell (-1) (-(ell : ℚ))) * x *
        (divisionUnit ell h : Bp ell (-1) (-(ell : ℚ))) ∈ (LevelR ell h N hN).completion ell ↔
      x ∈ (LevelR ell h N hN).completion ell := by
  let _ : Fact (ell % 4 = 3) := ⟨h⟩
  let f := DivisionJoin.ambientIntegralEquiv ell
  have hmem (y : Bp ell (-1) (-(ell : ℚ))) :
      y ∈ (LevelR ell h N hN).completion ell ↔ f y ∈ LocalDivision.order ell := by
    rw [level_completion_division, ← DivisionJoin.completion_map ell h]
    exact ⟨fun hy => ⟨y, hy, rfl⟩, fun ⟨z, hz, he⟩ => f.injective he ▸ hz⟩
  rw [hmem, hmem]
  rw [map_mul, map_mul]
  let j : (LocalDivision.D ell)ˣ := LocalDivision.uniformizer
  have hu : Units.map f.toMonoidHom (divisionUnit ell h) = j := by
    apply Units.ext
    exact f.apply_symm_apply _
  have hUinv := congrArg Units.val (congrArg Inv.inv hu)
  change f (↑(divisionUnit ell h)⁻¹) = _ at hUinv
  rw [hUinv, show f ↑(divisionUnit ell h) = (j : LocalDivision.D ell) from congrArg Units.val hu]
  simp only [LocalDivision.mem_order_iff_nrd, LocalDivision.nrd_conj]

/-- The right division-uniformizer permutation in the type of RC/PM's field. -/
def uniformizer : Equiv.Perm (ClassSet (LevelR ell h N hN)) :=
  let q : Prime := ⟨ell, Fact.out⟩
  rightClassPerm (single _ q (divisionUnit ell h))
    (normalizes_single q _ (divisionUnit_normalizes ell h N hN))

#print axioms atkinMatrix_square
#print axioms atkinMatrix_conj_formula
#print axioms atkinMatrix_conj
#print axioms atkinLocal_conj
#print axioms split_of_factorization_pos
#print axioms diagonal_scalar_val
#print axioms atkin
#print axioms atkin_involutive
#print axioms level_completion_division
#print axioms divisionUnit_normalizes
#print axioms uniformizer

end Level

end ZInQ.Manuscript.RC.Adelic
