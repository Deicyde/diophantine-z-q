import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.FieldTorsion
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Separability of the abscissa polynomial -/

namespace WeierstrassCurve.ModelTorsion

open Polynomial
open WeierstrassCurve.Affine

variable {K : Type*} [Field K]

private def Roots (f : K[X]) [DecidableEq K] := {x // x ∈ f.roots.toFinset}

private noncomputable instance {f : K[X]} [DecidableEq K] : Fintype (Roots f) :=
  Finset.Subtype.fintype f.roots.toFinset

private theorem card_roots_le [DecidableEq K] (f : K[X]) :
    Fintype.card (Roots f) ≤ f.natDegree := by
  simpa [Roots] using (Multiset.toFinset_card_le f.roots).trans f.card_roots'

private theorem separable_of_card_roots [DecidableEq K] [IsAlgClosed K] {f : K[X]}
    (hf : f ≠ 0) (hc : Fintype.card (Roots f) = f.natDegree) : f.Separable := by
  apply (nodup_roots_iff_of_splits hf (IsAlgClosed.splits f)).mp
  apply Multiset.toFinset_card_eq_card_iff_nodup.mp
  simpa [Roots, IsAlgClosed.card_roots_eq_natDegree] using hc

private noncomputable def chosenOrdinate (W : WeierstrassCurve K) (x : K) : K := by
  classical
  exact if h : ∃ y, W.toAffine.Equation x y then h.choose else 0

private theorem eq_of_ordinate_tag [DecidableEq K] (W : WeierstrassCurve K) {x y z : K}
    (hy : W.toAffine.Equation x y) (hz : W.toAffine.Equation x z)
    (he : decide (y = chosenOrdinate W x) = decide (z = chosenOrdinate W x)) : y = z := by
  let t := chosenOrdinate W x
  have ht : W.toAffine.Equation x t := by
    classical
    have h : ∃ y, W.toAffine.Equation x y := ⟨y, hy⟩
    simpa [t, chosenOrdinate, h] using h.choose_spec
  rcases W.toAffine.Y_eq_of_X_eq hy ht rfl with hy' | hy' <;>
    rcases W.toAffine.Y_eq_of_X_eq hz ht rfl with hz' | hz'
  · exact hy'.trans hz'.symm
  · change decide (y = t) = decide (z = t) at he
    simpa [hy', eq_comm] using he
  · change decide (y = t) = decide (z = t) at he
    simpa [hz'] using he
  · exact hy'.trans hz'.symm

private theorem separable_over_algClosed [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    (xPolynomial W n).Separable := by
  let f := W.preΨ' n
  let g := if Even n then W.Ψ₂Sq else 1
  have hfg : xPolynomial W n = f * g := by by_cases h : Even n <;> simp [xPolynomial, f, g, h]
  have hf : f ≠ 0 := W.preΨ'_ne_zero hn
  have hg : g ≠ 0 := by
    by_cases h : Even n
    · obtain ⟨m, rfl⟩ := h.two_dvd
      have h₂m : (2 : K) * (m : K) ≠ 0 := by simpa using hn
      have h₄ : (4 : K) ≠ 0 := by
        rw [show (4 : K) = 2 * 2 by ring]
        exact mul_ne_zero (left_ne_zero_of_mul h₂m) (left_ne_zero_of_mul h₂m)
      simpa [g, even_two_mul] using W.Ψ₂Sq_ne_zero h₄
    · simp [g, h]
  let encode : affineCoordinates W n → (Roots f × Bool) ⊕ Roots g := fun P =>
    if h : g.eval P.val.1 = 0 then
      .inr ⟨P.val.1, Multiset.mem_toFinset.mpr (mem_roots hg |>.mpr h)⟩
    else
      have hx : f.eval P.val.1 = 0 := by
        have he : f.eval P.val.1 = 0 ∨ g.eval P.val.1 = 0 := by
          simpa only [hfg, eval_mul, mul_eq_zero] using P.property.2
        exact he.resolve_right h
      .inl (⟨P.val.1, Multiset.mem_toFinset.mpr (mem_roots hf |>.mpr hx)⟩,
        decide (P.val.2 = chosenOrdinate W P.val.1))
  have hinj : Function.Injective encode := by
    rintro ⟨⟨x, y⟩, hy, hxy⟩ ⟨⟨x', y'⟩, hy', hxy'⟩ he
    by_cases hx : g.eval x = 0 <;> by_cases hx' : g.eval x' = 0
    · simp only [encode, dite_eq_left hx, dite_eq_left hx'] at he
      have hxx : x = x' := congrArg Subtype.val (Sum.inr.inj he)
      subst x'
      have hc : W.Ψ₂Sq.eval x = 0 := by
        by_cases hn : Even n
        · simpa [g, hn] using hx
        · simp [g, hn] at hx
      have hyneg := (eval_Ψ₂Sq_eq_zero_iff W hy).1 hc
      rcases W.toAffine.Y_eq_of_X_eq hy' hy rfl with h | h
      · exact Subtype.ext (Prod.ext rfl h.symm)
      · rw [← hyneg] at h
        exact Subtype.ext (Prod.ext rfl h.symm)
    · simp [encode, hx, hx'] at he
    · simp [encode, hx, hx'] at he
    · simp only [encode, dite_eq_right hx, dite_eq_right hx'] at he
      have hpair := Sum.inl.inj he
      have hxx : x = x' := congrArg (fun z : Roots f × Bool => z.1.val) hpair
      subst x'
      have hyy := eq_of_ordinate_tag W hy hy' (congrArg Prod.snd hpair)
      exact Subtype.ext (Prod.ext rfl hyy)
  have hdeg : 2 * f.natDegree + g.natDegree = n ^ 2 - 1 := by
    rw [show f.natDegree = _ from W.natDegree_preΨ' hn]
    rcases n.even_or_odd' with ⟨m, rfl | rfl⟩
    · have h₂m : (2 : K) * (m : K) ≠ 0 := by simpa using hn
      have h₄ : (4 : K) ≠ 0 := by
        rw [show (4 : K) = 2 * 2 by ring]
        exact mul_ne_zero (left_ne_zero_of_mul h₂m) (left_ne_zero_of_mul h₂m)
      have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at h₂m)
      simp only [g, ite_eq_left (even_two_mul m), W.natDegree_Ψ₂Sq h₄]
      have hsq : (2 * m) ^ 2 = 4 * m * m := by ring
      have hlarge : 0 < m * m := Nat.mul_pos hm hm
      rw [hsq, mul_assoc]
      omega
    · simp only [g, ite_eq_right m.not_even_two_mul_add_one, natDegree_one, add_zero]
      have hsq : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
      rw [hsq]
      omega
  have hsize : Nat.card (affineCoordinates W n) = n ^ 2 - 1 := card_affineCoordinates W hn
  let : Finite (affineCoordinates W n) := Finite.of_injective encode hinj
  let := Fintype.ofFinite (affineCoordinates W n)
  rw [Nat.card_eq_fintype_card] at hsize
  have hbound := Fintype.card_le_of_injective encode hinj
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool] at hbound
  have hfle := card_roots_le f
  have hgle := card_roots_le g
  have hfc : Fintype.card (Roots f) = f.natDegree := by omega
  have hgc : Fintype.card (Roots g) = g.natDegree := by omega
  have hcard : Fintype.card (affineCoordinates W n) = Fintype.card ((Roots f × Bool) ⊕ Roots g) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, hfc, hgc]
    omega
  have hsurj := ((Fintype.bijective_iff_injective_and_card encode).2 ⟨hinj, hcard⟩).2
  have hcop : IsCoprime f g := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) K]
    intro x
    simp only [aeval_def, Algebra.algebraMap_self, eval₂_id]
    by_cases hfx : f.eval x = 0
    · right
      intro hgx
      let rx : Roots f := ⟨x, Multiset.mem_toFinset.mpr (mem_roots hf |>.mpr hfx)⟩
      obtain ⟨P, hP⟩ := hsurj (.inl (rx, false))
      by_cases hx : g.eval P.val.1 = 0
      · simp [encode, hx] at hP
      · have hx' : P.val.1 = x := by
          have he := hP
          simp only [encode, dite_eq_right hx] at he
          exact congrArg (fun z : Roots f × Bool => z.1.val) (Sum.inl.inj he)
        exact hx (hx' ▸ hgx)
    · exact Or.inl hfx
  rw [hfg]
  exact (separable_of_card_roots hf hfc).mul (separable_of_card_roots hg hgc) hcop

/-- If the discriminant and level are nonzero, the abscissa polynomial is separable. -/
theorem separable_xPolynomial (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ}
    (hn : (n : K) ≠ 0) : (xPolynomial W n).Separable := by
  classical
  rw [← Polynomial.separable_map (f := algebraMap K (AlgebraicClosure K)), ← map_xPolynomial]
  have he : (W.map (algebraMap K (AlgebraicClosure K))).IsElliptic := inferInstance
  exact separable_over_algClosed _ (by simpa using (algebraMap K (AlgebraicClosure K)).injective.ne hn)

#print axioms card_roots_le
#print axioms separable_of_card_roots
#print axioms eq_of_ordinate_tag
#print axioms separable_over_algClosed
#print axioms separable_xPolynomial

end WeierstrassCurve.ModelTorsion
