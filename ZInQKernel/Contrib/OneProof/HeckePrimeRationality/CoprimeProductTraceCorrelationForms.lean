import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceActualReduction
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelationLowerClosure

/-!
# Genuine lower forms for the nonzero prime correlations

The verified signed lower correlation form, minus its zero-point term,
represents the nonzero-T actual λ-correlation. Every constituent belongs to
the actual admissible degree-two product span at the original lower level.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

open TorsionCorrelation TorsionCorrelationEnlarge TorsionCorrelationSigned
open TorsionCorrelationLower TorsionCorrelationLowerProducts TorsionCorrelationLowerClosure
open TorsionQuadraticGenerators

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The prime-torsion additive embedding, with the product level in pN order. -/
def primeEmbed (p N : ℕ) (hp : 0 < p) : Point p →+ Point (p * N) where
  toFun T :=
    let f := ZMod.castHom (show p * N ∣ N * p from by rw [Nat.mul_comm N p]) (ZMod (p * N))
    (f (levelMap N p hp T).1, f (levelMap N p hp T).2)
  map_zero' := by simp
  map_add' T U := by simp only [map_add, Prod.fst_add, Prod.snd_add]; rfl

lemma primeEmbed_label (p N : ℕ) (hp : 0 < p) (a b : ℤ) :
    primeEmbed p N hp (label p a b) = label (p * N) ((N : ℤ) * a) ((N : ℤ) * b) := by
  change ((ZMod.castHom _ (ZMod (p * N))) (levelMap N p hp (label p a b)).1,
    (ZMod.castHom _ (ZMod (p * N))) (levelMap N p hp (label p a b)).2) = _
  rw [levelMap_label hp N a b]
  apply Prod.ext <;> simp only [label, map_intCast]

lemma splitPoint_embedding (p N : ℕ) (hp : 0 < p) (hN : 0 < N) (A : Point N) (T : Point p) :
    splitPoint p N A T = levelMap p N hN A + primeEmbed p N hp T := by
  have hA := levelMap_label hN p (A.1.val : ℤ) (A.2.val : ℤ)
  have hT := primeEmbed_label p N hp (T.1.val : ℤ) (T.2.val : ℤ)
  rw [label_val hN A] at hA
  rw [label_val hp T] at hT
  rw [hA, hT, label_add]
  rfl

lemma primeEmbed_division (p N : ℕ) [NeZero p] (hp : 0 < p) (T : DivisionIndex p) :
    primeEmbed p N hp (ZMod.finEquiv p T.1,ZMod.finEquiv p T.2) = divisionPoint (p * N) p T := by
  let : NeZero p := ⟨hp.ne'⟩
  have hT : (ZMod.finEquiv p T.1,ZMod.finEquiv p T.2) =
      label p (T.1.val : ℤ) (T.2.val : ℤ) := by
    rw [← label_val hp (ZMod.finEquiv p T.1,ZMod.finEquiv p T.2)]
    simp only [finite_residue_val]
  rw [hT, primeEmbed_label]
  simp only [divisionPoint, Nat.mul_div_cancel_left N hp]

lemma scale_eq_zsmul (p : ℕ) [NeZero p] (s : ZMod p) (T : Point p) :
    scale s T = (s.val : ℤ) • T := by
  apply Prod.ext <;> simp [scale, Prod.smul_fst, Prod.smul_snd, zsmul_eq_mul]

/-- The actual λ-correlation over all prime points is the fixed lower signed
correlation value multiplied by the known nonzero normalization. -/
theorem all_correlation_value (p N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (τ : ℍ) (s : ZMod p) (A B : Point N) :
    (∑ T : Point p, splitLambda p N τ A T * splitLambda p N τ B (scale s T)) =
      TorsionWeierstrassData.scale ^ 2 *
        lowerCorrelationForm N p hN (Fact.out : p.Prime).pos (-(s.val : ℤ)) A B τ := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [← (Equiv.prodCongr (ZMod.finEquiv p).toEquiv (ZMod.finEquiv p).toEquiv).sum_comp]
  rw [lowerCorrelationForm_apply]
  unfold CInt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  change splitLambda p N τ A (ZMod.finEquiv p T.1,ZMod.finEquiv p T.2) *
    splitLambda p N τ B (scale s (ZMod.finEquiv p T.1,ZMod.finEquiv p T.2)) = _
  unfold splitLambda lambdaPointValue
  rw [splitPoint_embedding p N hp hN, splitPoint_embedding p N hp hN,
    scale_eq_zsmul, map_zsmul, primeEmbed_division p N hp]
  simp only [neg_zsmul, sub_neg_eq_add]
  ring

lemma splitLambda_zero (p N : ℕ) (hp : 0 < p) (hN : 0 < N) (τ : ℍ) (A : Point N) :
    splitLambda p N τ A 0 = lambdaPointValue N τ A := by
  rw [splitLambda, splitPoint_embedding p N hp hN, map_zero, add_zero]
  unfold lambdaPointValue
  rw [h_levelMap hp hN]

/-- The actual lower-level form representing the nonzero prime correlation. -/
def nonzeroCorrelationForm (p N : ℕ) [Fact p.Prime] (hN : 0 < N) (s : ZMod p)
    (A B : Point N) : _root_.ModularForm (ΓP N) 2 :=
  TorsionWeierstrassData.scale ^ 2 •
    (lowerCorrelationForm N p hN (Fact.out : p.Prime).pos (-(s.val : ℤ)) A B -
      rawProductForm N hN A B)

/-- The form evaluates to the exact nonzero-T λ-correlation. -/
theorem nonzeroCorrelationForm_apply (p N : ℕ) [Fact p.Prime] (hN : 0 < N)
    (s : ZMod p) (A B : Point N) (τ : ℍ) :
    nonzeroCorrelationForm p N hN s A B τ = nonzeroCorrelationValue p N τ s A B := by
  classical
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hsum := Fintype.sum_eq_add_sum_subtype_ne
    (fun T : Point p => splitLambda p N τ A T * splitLambda p N τ B (scale s T)) 0
  rw [all_correlation_value p N hN τ s A B] at hsum
  have hs0 : scale s (0 : Point p) = 0 := by simp [scale]
  rw [hs0, splitLambda_zero p N (Fact.out : p.Prime).pos hN,
    splitLambda_zero p N (Fact.out : p.Prime).pos hN] at hsum
  simp only [nonzeroCorrelationForm, smul_apply, smul_eq_mul, sub_apply, rawProductForm_apply,
    nonzeroCorrelationValue, lambdaPointValue]
  simp only [lambdaPointValue] at hsum
  linear_combination hsum

/-- The exact correlation form belongs to the genuine lower Good product span. -/
theorem nonzeroCorrelationForm_mem_productSpan (p N : ℕ) [Fact p.Prime]
    (hN : 0 < N) (h3 : 3 ≤ N) (s : ZMod p) (A B : Point N) :
    nonzeroCorrelationForm p N hN s A B ∈ productSpan N hN := by
  unfold nonzeroCorrelationForm
  apply Submodule.smul_mem
  exact Submodule.sub_mem _
    (lowerCorrelationForm_mem_productSpan N p hN h3 (Fact.out : p.Prime).pos (-(s.val : ℤ)) A B)
    (rawProductForm_mem_productSpan N hN A B)

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
