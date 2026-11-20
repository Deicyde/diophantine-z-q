import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Frame
import ZInQKernel.Contrib.OneProof.RC.Adelic.RightAction

/-! Transport the weights through the vector bijection at a good-prime
neighbour. The input to this comparison is an equality of lattices,
expressed as membership after division by the good prime. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler
open scoped Quaternion

variable {a b : ℚ} {R : Order a b} {O S : Type} [CommRing O] [CommRing S]

theorem atRep_single_away (z : FiniteUnits R) {p q : Prime} (hq : q ≠ p)
    (u : (Bp p.val a b)ˣ) (x : B a b) :
    atRep (z * single R p u) q x = atRep z q x := by
  have h : (z * single R p u).val q = z.val q := by
    change z.val q * (single R p u).val q = _
    rw [single_away hq, mul_one]
  unfold atRep
  rw [h]

/-- At a good prime, changing only that local ideal generator leaves the
factors away from the prime fixed. Thus multiplication by the good prime
takes the neighbour's weight to the original weight times `s`. -/
theorem weightAt_neighbour_scale (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (hw : ∀ q ∈ A.places, ∀ (v : ℤ_[q.val]ˣ) (y : Bp q.val a b),
      w q ((v : ℤ_[q.val]) • y) = (A.alpha q v : O) * w q y)
    (z : FiniteUnits R) (p : Prime) (hp : p.val ∉ A.support)
    (u : (Bp p.val a b)ˣ) (x : B a b)
    (hx : x ∈ (fromAdelic (z * single R p u)).val.leftRing)
    (hy : p.val • x ∈ (fromAdelic z).val.leftRing) :
    weightAt A w z (p.val • x) = (A.phase p.val : O) * weightAt A w (z * single R p u) x := by
  classical
  have he : weightAt A w z (p.val • x) =
      weightAt A w (z * single R p u) (p.val • x) := by
    have hp' : p.val • x ∈ (fromAdelic (z * single R p u)).val.leftRing :=
      (fromAdelic (z * single R p u)).val.leftRing.toAddSubgroup.nsmul_mem hx _
    unfold weightAt
    rw [ite_eq_left hy, ite_eq_left hp']
    exact Finset.prod_congr rfl fun q hq => by
      have hqp : q ≠ p := fun h => hp ((A.mem_support p).mpr (h ▸ hq))
      rw [atRep_single_away z hqp]
  rw [he, A.phase_good p hp]
  exact weightAt_scale A w hw _ _ (A.away_of_not_mem p hp) x hx

namespace FrameCoordinates

variable {p : Prime} {z : FiniteUnits R} (D : FrameCoordinates p z)

/-- The local line predicate recognizes precisely the scaled vectors of the
rational neighbour. This obligation is independent of coefficient values. -/
def NeighbourLattice (u : (Bp p.val a b)ˣ) (i : Option (ZMod p.val)) : Prop :=
  ∀ x : B a b, x.re = 0 →
    (x ∈ (fromAdelic (z * single R p u)).val.leftRing ↔
      ∃ y : Ternary z, y.val = p.val • x ∧
        AppF.MemNbr p.val 1 (D.coord y).1 (D.coord y).2.1 (D.coord y).2.2 i)

/-- Summing the scale law over the line yields the unweighted-by-norm-character
neighbour comparison at the actual adelic lift. -/
theorem frame_neighbour (reduction : O →+* S)
    (ha : a < 0) (hb : b < 0) (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (hw : ∀ q ∈ A.places, ∀ (v : ℤ_[q.val]ˣ) (y : Bp q.val a b),
      w q ((v : ℤ_[q.val]) • y) = (A.alpha q v : O) * w q y)
    (hp : p.val ∉ A.support) (u : (Bp p.val a b)ˣ)
    (i : Option (ZMod p.val)) (hL : D.NeighbourLattice u i) (n : ℕ) :
    reduction (coefficientAt A w (z * single R p u) n) =
      reduction ((A.phase p.val)⁻¹ : Oˣ) * (D.frame reduction ha hb A w).nbrSum i n := by
  classical
  let z' := z * single R p u
  let P := D.frame reduction ha hb A w
  let test (y : Ternary z) : Prop :=
    AppF.MemNbr p.val 1 (D.coord y).1 (D.coord y).2.1 (D.coord y).2.2 i
  have H : ∀ x : Ternary z', ∃ y : Ternary z,
      y.val = p.val • x.val ∧ test y :=
    fun x => (hL x.val x.prop.2).mp x.prop.1
  let f (x : Ternary z') : Ternary z := (H x).choose
  have hf (x : Ternary z') : (f x).val = p.val • x.val ∧ test (f x) := (H x).choose_spec
  have hn (x : Ternary z') :
      Visibility.nrd (f x).val = (p.val : ℚ) ^ 2 * Visibility.nrd x.val := by
    rw [(hf x).1, nrd_nsmul]
  have hne : (p.val : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
  change reduction (coefficientAt A w z' n) = _ * P.nbrSum i n
  rw [coefficientAt_eq_vectors reduction ha hb A w z']
  change (∑ x ∈ vectors ha hb z' n, reduction (weightAt A w z' x.val)) =
    reduction ((A.phase p.val)⁻¹ : Oˣ) *
      ∑ y ∈ (vectors ha hb z (p.val ^ 2 * n)).filter test, reduction (weightAt A w z y.val)
  rw [Finset.mul_sum]
  refine Finset.sum_bij (fun x _ => f x) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter, mem_vectors, hn, (mem_vectors _ _ _ _ _).mp hx]
    exact ⟨by push_cast; rfl, (hf x).2⟩
  · intro x _ y _ he
    apply Subtype.ext
    have he' := congrArg Subtype.val he
    rw [(hf x).1, (hf y).1, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at he'
    exact smul_right_injective _ hne he'
  · intro y hy
    change y ∈ (vectors ha hb z (p.val ^ 2 * n)).filter test at hy
    rw [Finset.mem_filter, mem_vectors] at hy
    let x : B a b := (p.val : ℚ)⁻¹ • y.val
    have hscale : p.val • x = y.val := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, show x = (p.val : ℚ)⁻¹ • y.val from rfl, smul_smul,
        mul_inv_cancel₀ hne, one_smul]
    have hr : x.re = 0 := by
      rw [show x = (p.val : ℚ)⁻¹ • y.val from rfl, QuaternionAlgebra.re_smul, y.prop.2, smul_zero]
    let X : Ternary z' := ⟨x, (hL x hr).mpr ⟨y, hscale.symm, hy.2⟩, hr⟩
    have he : f X = y := Subtype.ext ((hf X).1.trans hscale)
    refine ⟨X, (mem_vectors _ _ _ _ _).mpr ?_, he⟩
    have h := hn X
    rw [he, hy.1, Nat.cast_mul, Nat.cast_pow] at h
    exact (mul_left_cancel₀ (pow_ne_zero 2 hne) h).symm
  · intro x _
    have hh := weightAt_neighbour_scale A w hw z p hp u x.val x.prop.1
      (show p.val • x.val ∈ (fromAdelic z).val.leftRing from (hf x).1 ▸ (f x).prop.1)
    change reduction (weightAt A w z' x.val) =
      reduction ((A.phase p.val)⁻¹ : Oˣ) * reduction (weightAt A w z (f x).val)
    rw [(hf x).1, hh, map_mul, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

end FrameCoordinates
end ZInQ.Manuscript.RC.ThetaJoin
