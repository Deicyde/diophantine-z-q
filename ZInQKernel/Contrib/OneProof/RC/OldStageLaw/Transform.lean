import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Words

/-! The missing arithmetic is an eigenvector calculation in finite spaces.
The real factor and all analytic conditions have already been proved using
Poisson summation. -/

noncomputable section

namespace ZInQ.Manuscript.RC.OldStageLaw

open Complex Matrix.SpecialLinearGroup CongruenceSubgroup PrintsAnalytic
open UpperHalfPlane hiding I
open scoped BigOperators MatrixGroups

abbrev referenceForm : Fin 3 → ℕ := fun _ => 1

/-- `1_{ℤ³}` in the discriminant module of the sum of three squares. -/
def referenceWeight : Grid referenceForm → ℂ := by
  classical
  exact fun r => if r = 0 then 1 else 0

theorem gridTheta_reference (z : ℂ) : gridTheta referenceWeight z = jacobiTheta (2 * z) ^ 3 := by
  classical
  unfold gridTheta cosetSum referenceWeight
  simp [ite_mul, offset, line, jacobiTheta_eq_jacobiTheta₂, Fin.prod_univ_three, pow_succ, mul_assoc]

theorem gridTheta_scale {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]
    (c : ℂ) (w : Grid a → ℂ) (z : ℂ) :
    gridTheta (fun r => c * w r) z = c * gridTheta w z := by
  simp [gridTheta, cosetSum, Finset.mul_sum, mul_assoc]

/-- Missing theory: finite Weil action on the actual coset vector, relative
to `1_{ℤ³}` for the same word. This contains only finite sums, signs and
scalars, and never evaluates a theta function. The common scalar may depend
on the word. The ratio is evaluated at the lower-right entry because this
is the finite action of the inverse (tex 8893–8936, 8989–9015).
See Weil, *Sur certains groupes d'opérateurs unitaires*, I.13–I.14 and
II.25–II.30 (manuscript locators; independently UNVERIFIED). -/
def RelativeFiniteAction {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)] {m : ℕ}
    (ξ : (ZMod m)ˣ →* ℂˣ) (w : Grid a → ℂ) : Prop :=
  ∀ (l : List Step) (h : wordMatrix l ∈ Gamma0 m), ∃ c : ℂ,
    wordAction l referenceWeight = (fun r => c * referenceWeight r) ∧
    wordAction l w = (fun r => (ξ ((Gamma0Map m).toHomUnits ⟨wordMatrix l, h⟩) : ℂ) * c * w r)

private theorem theta_ne_zero (z : ℍ) : thetaFun z ≠ 0 := by
  unfold thetaFun
  apply HalfIntegral.jacobiTheta_ne_zero_of_im_pos
  rw [← ofReal_ofNat, im_ofReal_mul]
  exact mul_pos (by norm_num) z.im_pos

/-- Complete classical law for a coset weight from its relative finite action. -/
theorem halfIntegral_of_finiteAction {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]
    (ha : ∀ i, 0 < a i) {m : ℕ} {ξ : (ZMod m)ˣ →* ℂˣ} {w : Grid a → ℂ}
    (hfin : RelativeFiniteAction ξ w) :
    BlocksPerU.HalfIntegralThreeHalves m ξ (fun z => gridTheta w z) := by
  refine ⟨gridTheta_holo ha w, ?_, gridTheta_cusps ha w⟩
  intro γ z
  obtain ⟨l, hl⟩ := exists_word (γ : SL(2, ℤ))
  have hm : wordMatrix l ∈ Gamma0 m := hl ▸ γ.property
  obtain ⟨c, hc, hw⟩ := hfin l hm
  have hγ : (⟨wordMatrix l, hm⟩ : Gamma0 m) = γ := Subtype.ext hl
  rw [hγ] at hw
  have hθ := gridTheta_word (a := referenceForm) (fun _ => Nat.zero_lt_one) referenceWeight l z
  rw [hc, gridTheta_scale, gridTheta_reference, gridTheta_reference, hl] at hθ
  have hθ' : thetaMultiplier (γ : SL(2, ℤ)) z ^ 3 = wordFactor l z * c := by
    rw [thetaMultiplier, div_pow]
    apply (div_eq_iff (pow_ne_zero _ (theta_ne_zero z))).mpr
    change jacobiTheta (2 * ↑((γ : SL(2, ℤ)) • z)) ^ 3 = _ * jacobiTheta (2 * ↑z) ^ 3
    rw [hθ, mul_assoc]
  have h := gridTheta_word ha w l z
  rw [hw, gridTheta_scale, hl] at h
  rw [hθ', h]
  ring

#print axioms gridTheta_reference
#print axioms gridTheta_scale
#print axioms theta_ne_zero
#print axioms halfIntegral_of_finiteAction

end ZInQ.Manuscript.RC.OldStageLaw
