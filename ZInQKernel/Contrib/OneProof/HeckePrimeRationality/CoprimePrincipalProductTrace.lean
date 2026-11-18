import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceActions

/-!
# Coprime-prime trace closure for genuine principal degree-two products

The actual CRT split has rank zero, one, or two in the prime part. Verified
lower correlation forms supply the orbit sums. Constructed principal-group
motions and nonempty finite-orbit averaging then give the actual trace in the
Good degree-two product span at the original lower level.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups Matrix ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

open TorsionCorrelation TorsionCorrelationLower TorsionCorrelationLowerProducts
open TorsionQuadraticGenerators AllLevelProducts DivisionEisensteinLevelMaps

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The actual upper raw product in split coordinates, with zero classes retained. -/
def splitRawProduct (p N : ℕ) (hp : 0 < p) (hN : 0 < N)
    (A B : Point N) (T U : Point p) : _root_.ModularForm (ΓP (p * N)) 2 :=
  rawProductForm (p * N) (Nat.mul_pos hp hN) (splitPoint p N A T) (splitPoint p N B U)

lemma splitRawProduct_apply (p N : ℕ) (hp : 0 < p) (hN : 0 < N)
    (A B : Point N) (T U : Point p) (τ : ℍ) :
    splitRawProduct p N hp hN A B T U τ = (TorsionWeierstrassData.scale ^ 2)⁻¹ *
      (splitLambda p N τ A T * splitLambda p N τ B U) := by
  rw [splitRawProduct, rawProductForm_apply]
  unfold splitLambda lambdaPointValue
  field_simp [TorsionWeierstrassData.scale_ne_zero]

lemma splitRawProduct_comm (p N : ℕ) (hp : 0 < p) (hN : 0 < N)
    (A B : Point N) (T U : Point p) :
    splitRawProduct p N hp hN A B T U = splitRawProduct p N hp hN B A U T := by
  apply _root_.ModularForm.ext
  intro τ
  rw [splitRawProduct_apply, splitRawProduct_apply, mul_comm (splitLambda p N τ A T)]

lemma rank_one_sum_restriction (p N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (s : ZMod p) (A B : Point N) :
    (∑ T : {T : Point p // T ≠ 0}, splitRawProduct p N (Fact.out : p.Prime).pos hN A B T.val (scale s T.val)) =
      restriction N (p * N) (dvd_mul_left N p)
        ((TorsionWeierstrassData.scale ^ 2)⁻¹ • nonzeroCorrelationForm p N hN s A B) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [restriction_apply, smul_apply, smul_eq_mul, nonzeroCorrelationForm_apply]
  simp only [sum_apply, splitRawProduct_apply, nonzeroCorrelationValue, Finset.mul_sum]

lemma rank_two_sum_restriction (p N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (hcop : Nat.Coprime p N) (d : ZMod p) (A B : Point N) :
    (∑ D : DeterminantPairs p d, splitRawProduct p N (Fact.out : p.Prime).pos hN A B D.1.val D.2.val) =
      restriction N (p * N) (dvd_mul_left N p)
        ((TorsionWeierstrassData.scale ^ 2)⁻¹ • determinantOrbitForm p N hN d A B) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [restriction_apply, smul_apply, smul_eq_mul, determinantOrbitForm_apply p N hN hcop]
  simp only [sum_apply, splitRawProduct_apply, determinantOrbitValue, Finset.mul_sum]

lemma nonzero_components {K : Type*} [Zero K] (T : Pair K) (hT : T ≠ 0) : T.1 ≠ 0 ∨ T.2 ≠ 0 := by
  by_contra hz
  push_neg at hz
  exact hT (Prod.ext hz.1 hz.2)

/-- The actual rank-one trace belongs to the lower Good product span. -/
theorem rank_one_trace_mem (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N) (hcop : Nat.Coprime p N)
    (A B : Point N) (T0 : Point p) (hT0 : T0 ≠ 0) (s : ZMod p) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (splitRawProduct p N (Fact.out : p.Prime).pos (by omega) A B T0 (scale s T0)) ∈ productSpan N (by omega) := by
  classical
  have hN : 0 < N := by omega
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero p := ⟨hp.ne'⟩
  let F := (TorsionWeierstrassData.scale ^ 2)⁻¹ • nonzeroCorrelationForm p N hN s A B
  have hF : F ∈ productSpan N hN := Submodule.smul_mem _ _
    (nonzeroCorrelationForm_mem_productSpan p N hN h3 s A B)
  apply trace_of_finite_orbit_sum (⟨T0,hT0⟩ : {T : Point p // T ≠ 0}) N (p * N)
    hN (Nat.mul_pos hp hN) (dvd_mul_left N p)
    (fun T => splitRawProduct p N hp hN A B T.val (scale s T.val))
    (splitRawProduct p N hp hN A B T0 (scale s T0)) F hF
    (rank_one_sum_restriction p N hN s A B)
  intro T
  obtain ⟨G, hG⟩ := DivisionEisensteinLowerClosure.exists_SL2_nonzero_row_move
    T0.1 T0.2 T.val.1 T.val.2 (nonzero_components T0 hT0) (nonzero_components T.val T.property)
  have hs : ![(scale s T0).1,(scale s T0).2] ᵥ* G.1 = ![(scale s T.val).1,(scale s T.val).2] := by
    have hv (P : Point p) : ![(scale s P).1,(scale s P).2] = s • (![P.1,P.2] : Fin 2 → ZMod p) := by
      ext i; fin_cases i <;> rfl
    rw [hv, hv, Matrix.smul_vecMul, hG]
  obtain ⟨γ, hγ, hP, hQ⟩ := exists_Gamma_split_pair_move p N hcop A B
    T0 (scale s T0) T.val (scale s T.val) G hG hs
  unfold splitRawProduct
  rw [← hP, ← hQ]
  exact normalizedTrace_rawProduct_action N (p * N) (Nat.mul_pos hp hN)
    (splitPoint p N A T0) (splitPoint p N B (scale s T0)) γ hγ

/-- The actual rank-two trace belongs to the lower Good product span. -/
theorem rank_two_trace_mem (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N) (hcop : Nat.Coprime p N)
    (A B : Point N) (T0 U0 : Point p) (d : ZMod p) (hd : d ≠ 0) (hTU : det T0 U0 = d) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (splitRawProduct p N (Fact.out : p.Prime).pos (by omega) A B T0 U0) ∈ productSpan N (by omega) := by
  classical
  have hN : 0 < N := by omega
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero p := ⟨hp.ne'⟩
  have hT0 : T0 ≠ 0 := by
    intro hz
    rw [hz] at hTU
    have hz0 : det (0 : Point p) U0 = 0 := by simp [det]
    exact hd (hTU.symm.trans hz0)
  let F := (TorsionWeierstrassData.scale ^ 2)⁻¹ • determinantOrbitForm p N hN d A B
  have hF : F ∈ productSpan N hN := Submodule.smul_mem _ _
    (determinantOrbitForm_mem_productSpan p N hN h3 d A B)
  apply trace_of_finite_orbit_sum (⟨⟨T0,hT0⟩,⟨U0,hTU⟩⟩ : DeterminantPairs p d) N (p * N)
    hN (Nat.mul_pos hp hN) (dvd_mul_left N p)
    (fun D => splitRawProduct p N hp hN A B D.1.val D.2.val)
    (splitRawProduct p N hp hN A B T0 U0) F hF
    (rank_two_sum_restriction p N hN hcop d A B)
  intro D
  obtain ⟨G, hG0, hG1⟩ := exists_SL2_determinant_pair_move T0 U0 D.1.val D.2.val d hd hTU D.2.property
  obtain ⟨γ, hγ, hP, hQ⟩ := exists_Gamma_split_pair_move p N hcop A B
    T0 U0 D.1.val D.2.val G hG0 hG1
  unfold splitRawProduct
  rw [← hP, ← hQ]
  exact normalizedTrace_rawProduct_action N (p * N) (Nat.mul_pos hp hN)
    (splitPoint p N A T0) (splitPoint p N B U0) γ hγ

/-- Every actual split raw product has coprime-prime trace closure, including
all zero classes and every rank of its two prime-part rows. -/
theorem split_raw_product_trace_mem (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N) (hcop : Nat.Coprime p N)
    (A B : Point N) (T U : Point p) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (splitRawProduct p N (Fact.out : p.Prime).pos (by omega) A B T U) ∈ productSpan N (by omega) := by
  have hN : 0 < N := by omega
  have hp : 0 < p := (Fact.out : p.Prime).pos
  by_cases hT : T = 0
  · by_cases hU : U = 0
    · subst T; subst U
      have he : splitRawProduct p N hp hN A B 0 0 =
          restriction N (p * N) (dvd_mul_left N p) (rawProductForm N hN A B) := by
        apply _root_.ModularForm.ext
        intro τ
        rw [restriction_apply, splitRawProduct_apply, splitLambda_zero p N hp hN,
          splitLambda_zero p N hp hN, rawProductForm_apply]
        unfold lambdaPointValue
        field_simp [TorsionWeierstrassData.scale_ne_zero]
      rw [he, normalizedTrace_restriction (Nat.mul_pos hp hN) (dvd_mul_left N p)]
      exact rawProductForm_mem_productSpan N hN A B
    · have h := rank_one_trace_mem p N h3 hcop B A U hU 0
      have hz : scale (0 : ZMod p) U = 0 := by simp [scale]
      rw [hz, splitRawProduct_comm p N hp hN B A U 0] at h
      simpa only [hT] using h
  · by_cases hd : det T U = 0
    · have hu := (determinant_kernel T hT U).mp hd
      generalize hs : coordinate T U = s at hu
      rw [hu]
      exact rank_one_trace_mem p N h3 hcop A B T hT s
    · exact rank_two_trace_mem p N h3 hcop A B T U (det T U) hd rfl

/-- The all-label raw product trace closure at the actual upper principal level. -/
theorem raw_product_trace_coprime_mem (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N) (hcop : Nat.Coprime p N)
    (P Q : Point (p * N)) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (rawProductForm (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) P Q) ∈ productSpan N (by omega) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let : NeZero N := ⟨by omega⟩
  obtain ⟨⟨A,T⟩,hP⟩ := (splitPointEquiv p N hcop).surjective P
  obtain ⟨⟨B,U⟩,hQ⟩ := (splitPointEquiv p N hcop).surjective Q
  rw [← hP, ← hQ]
  exact split_raw_product_trace_mem p N h3 hcop A B T U

/-- Coprime-prime trace closure for every genuine Good degree-two principal product. -/
theorem principal_product_trace_coprime_mem (p N : ℕ) [Fact p.Prime] (h3 : 3 ≤ N)
    (hcop : Nat.Coprime p N) (a b c d : ℤ)
    (hP : AllLevelForms.Good (p * N) (a,b)) (hQ : AllLevelForms.Good (p * N) (c,d)) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))
      (productForm (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) 2
        ![(a,b),(c,d)] (by intro i; fin_cases i <;> assumption)) ∈ productSpan N (by omega) := by
  have hM : 0 < p * N := Nat.mul_pos (Fact.out : p.Prime).pos (by omega)
  have he : rawProductForm (p * N) hM (label (p * N) a b) (label (p * N) c d) =
      productForm (p * N) hM 2 ![(a,b),(c,d)]
        (show ∀ i : Fin 2, AllLevelForms.Good (p * N) (![(a,b),(c,d)] i) from by
          intro i; fin_cases i <;> assumption) := by
    apply _root_.ModularForm.ext
    intro τ
    rw [rawProductForm_apply, h_label hM, h_label hM, TorsionDistributionTwo.reg_of_good hP,
      TorsionDistributionTwo.reg_of_good hQ, productForm_apply]
    simp [Fin.prod_univ_two]
  rw [← he]
  exact raw_product_trace_coprime_mem p N h3 hcop (label (p * N) a b) (label (p * N) c d)

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
