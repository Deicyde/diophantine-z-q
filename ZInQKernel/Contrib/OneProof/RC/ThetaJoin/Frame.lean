import ZInQKernel.Contrib.OneProof.RC.ThetaJoin.Global
import ZInQKernel.Contrib.OneProof.RC.AppF.Brandt

/-! The rational ternary lattice and its finite norm spheres, in the
residue coordinates consumed by the Brandt recurrence. -/

noncomputable section

namespace ZInQ.Manuscript.RC.ThetaJoin

open Adelic Eichler LocalWeights
open scoped Quaternion

variable {a b : ℚ} {R : Order a b}

/-- The trace-zero lattice in the adelic left order. -/
abbrev Ternary (z : FiniteUnits R) :=
  {x : B a b // x ∈ (fromAdelic z).val.leftRing ∧ x.re = 0}

/-- Rational multiplication entering the good-prime frame. -/
def scaleVector (z : FiniteUnits R) (n : ℕ) (x : Ternary z) : Ternary z :=
  ⟨n • x.val, (fromAdelic z).val.leftRing.toAddSubgroup.nsmul_mem x.prop.1 n, by
    rw [← Nat.cast_smul_eq_nsmul ℚ, QuaternionAlgebra.re_smul, x.prop.2, smul_zero]⟩

theorem nrd_nsmul (n : ℕ) (x : B a b) :
    Visibility.nrd (n • x) = (n : ℚ) ^ 2 * Visibility.nrd x := by
  simp only [← Nat.cast_smul_eq_nsmul ℚ n x, Visibility.nrd_apply,
    QuaternionAlgebra.re_smul, QuaternionAlgebra.imI_smul, QuaternionAlgebra.imJ_smul,
    QuaternionAlgebra.imK_smul, smul_eq_mul]
  ring

/-- The kth sphere of the ternary lattice, including vectors with weight zero. -/
def vectors (ha : a < 0) (hb : b < 0) (z : FiniteUnits R) (k : ℕ) : Finset (Ternary z) :=
  have hs : {x : Ternary z | Visibility.nrd x.val = (k : ℚ)}.Finite := by
    refine ((latticeSphere_finite ha hb z k).preimage
      Subtype.val_injective.injOn).subset ?_
    intro x hx
    exact ⟨x.prop.1, x.prop.2, hx⟩
  hs.toFinset

@[simp] theorem mem_vectors (ha : a < 0) (hb : b < 0) (z : FiniteUnits R)
    (k : ℕ) (x : Ternary z) :
    x ∈ vectors ha hb z k ↔ Visibility.nrd x.val = (k : ℚ) := by
  simp [vectors]

/-- The integral entries in the aligned split chart. The divisibility field
is the assertion of saturation at this prime for the rational lattice. -/
structure FrameCoordinates (p : Prime) (z : FiniteUnits R) where
  matrix : Ternary z → M2 ℤ_[p.val]
  trace : ∀ x, (matrix x).trace = 0
  det : ∀ x, ((matrix x).det : ℚ_[p.val]) = (Visibility.nrd x.val : ℚ_[p.val])
  scale : ∀ x, matrix (scaleVector z p.val x) = (p.val : ℤ_[p.val]) • matrix x
  divisible : ∀ y, (∀ i j, (p.val : ℤ_[p.val]) ∣ matrix y i j) →
    ∃ x, scaleVector z p.val x = y
  integralNorm : ∀ x : Ternary z, ∃ k : ℕ, Visibility.nrd x.val = (k : ℚ)

variable {p : Prime} {z : FiniteUnits R}

namespace FrameCoordinates

variable (D : FrameCoordinates p z)

private def residueRep (p : Prime) (v : ℤ_[p.val]) : ℤ :=
  ((PadicInt.toZModPow 2 v).val : ℤ)

private theorem residueRep_cast (p : Prime) (v : ℤ_[p.val]) :
    ((residueRep p v : ℤ) : ZMod (p.val ^ 2)) = PadicInt.toZModPow 2 v := by
  have : NeZero (p.val ^ 2) := ⟨pow_ne_zero _ p.prop.ne_zero⟩
  simp [residueRep]

/-- Integer representatives of the three entries modulo the square of the prime. -/
def coord (x : Ternary z) : ℤ × ℤ × ℤ :=
  (residueRep p (D.matrix x 0 0), residueRep p (D.matrix x 0 1),
    residueRep p (D.matrix x 1 0))

private theorem det_equation (x : Ternary z) :
    (D.matrix x).det = -(D.matrix x 0 0) ^ 2 - D.matrix x 0 1 * D.matrix x 1 0 := by
  have h := D.trace x
  rw [Matrix.trace_fin_two] at h
  rw [Matrix.det_fin_two, eq_neg_of_add_eq_zero_left h]
  ring

theorem coord_det (x : Ternary z) (k : ℕ) (hk : Visibility.nrd x.val = (k : ℚ)) :
    (p.val : ℤ) ^ 2 ∣ (-(D.coord x).1 ^ 2 - (D.coord x).2.1 * (D.coord x).2.2) - k := by
  have : NeZero (p.val ^ 2) := ⟨pow_ne_zero _ p.prop.ne_zero⟩
  have hdet : (D.matrix x).det = (k : ℤ_[p.val]) := by
    apply Subtype.val_injective
    rw [D.det, hk]
    simp
  have h := congrArg (PadicInt.toZModPow 2) hdet
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
  simp only [coord, Int.cast_sub, Int.cast_neg, Int.cast_pow, Int.cast_mul, Int.cast_natCast,
    residueRep_cast]
  simpa only [D.det_equation, map_sub, map_neg, map_pow, map_mul, map_natCast] using h.symm

theorem coord_scale (x : Ternary z) :
    (p.val : ℤ) ^ 2 ∣ (D.coord (scaleVector z p.val x)).1 - p.val * (D.coord x).1 ∧
    (p.val : ℤ) ^ 2 ∣ (D.coord (scaleVector z p.val x)).2.1 - p.val * (D.coord x).2.1 ∧
    (p.val : ℤ) ^ 2 ∣ (D.coord (scaleVector z p.val x)).2.2 - p.val * (D.coord x).2.2 := by
  have : NeZero (p.val ^ 2) := ⟨pow_ne_zero _ p.prop.ne_zero⟩
  have h (i j : Fin 2) :
      (p.val : ℤ) ^ 2 ∣ residueRep p (D.matrix (scaleVector z p.val x) i j) -
        p.val * residueRep p (D.matrix x i j) := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
    simp only [Int.cast_mul, Int.cast_natCast, residueRep_cast, D.scale, Matrix.smul_apply,
      smul_eq_mul, map_mul, map_natCast]
  exact ⟨h 0 0, h 0 1, h 1 0⟩

private theorem dvd_entry (v : ℤ_[p.val]) (hv : (p.val : ℤ) ∣ residueRep p v) :
    (p.val : ℤ_[p.val]) ∣ v := by
  have hc : (residueRep p v : ℤ_[p.val]) - v ∈
      RingHom.ker (PadicInt.toZModPow 2 : ℤ_[p.val] →+* _) := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, map_intCast, residueRep_cast]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hc
  obtain ⟨d, hd⟩ := hv
  have hz : (p.val : ℤ_[p.val]) ∣ (residueRep p v : ℤ_[p.val]) :=
    ⟨d, by rw [hd]; push_cast; rfl⟩
  simpa only [sub_sub_cancel] using dvd_sub hz (dvd_trans (dvd_pow_self _ two_ne_zero) hc)

theorem div_vector (y : Ternary z) (hy : AppF.PDiv p.val
    (D.coord y).1 (D.coord y).2.1 (D.coord y).2.2) :
    ∃ x, scaleVector z p.val x = y := by
  obtain ⟨ha, hb, hc⟩ := hy
  have H := D.trace y
  rw [Matrix.trace_fin_two] at H
  apply D.divisible
  intro i j
  fin_cases i <;> fin_cases j
  · exact dvd_entry _ ha
  · exact dvd_entry _ hb
  · exact dvd_entry _ hc
  · change (p.val : ℤ_[p.val]) ∣ D.matrix y 1 1
    rw [eq_neg_of_add_eq_zero_right H]
    exact dvd_neg.mpr (dvd_entry _ ha)

/-- Construct an App F frame from the aligned chart and the saturation and
integral norm facts about its rational lattice. -/
def frame {O S : Type} [CommRing O] [CommRing S] (reduction : O →+* S)
    (ha : a < 0) (hb : b < 0) (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O) :
    AppF.PFrame p.val S where
  V := Ternary z
  deq := Classical.decEq _
  vecs := vectors ha hb z
  coord := D.coord
  F x := reduction (weightAt A w z x.val)
  scale := scaleVector z p.val
  coord_det k x hx := D.coord_det x k ((mem_vectors ha hb z k x).mp hx)
  scale_mem k x hx := by
    rw [mem_vectors, show (scaleVector z p.val x).val = p.val • x.val from rfl,
      nrd_nsmul, (mem_vectors ha hb z k x).mp hx]
    push_cast
    rfl
  div_mem k y hy hdiv := by
    obtain ⟨x, rfl⟩ := D.div_vector y hdiv
    rw [mem_vectors] at hy
    change Visibility.nrd (p.val • x.val) = (k : ℚ) at hy
    obtain ⟨n, hn⟩ := D.integralNorm x
    rw [nrd_nsmul, hn] at hy
    have hk : p.val ^ 2 * n = k := by exact_mod_cast hy
    refine ⟨⟨n, hk.symm⟩, x, ?_, rfl⟩
    rw [mem_vectors, hn, ← hk, Nat.mul_div_cancel_left _ (pow_pos p.prop.pos _)]
  scale_inj := fun x y h => by
    apply Subtype.ext
    have he : p.val • x.val = p.val • y.val := congrArg Subtype.val h
    rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at he
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr p.prop.ne_zero : (p.val : ℚ) ≠ 0) he
  coord_scale := D.coord_scale

/-- Express the rational sum as a sum on the finite left-order lattice. -/
theorem coefficientAt_eq_vectors {O S : Type} [CommRing O] [CommRing S] (reduction : O →+* S)
    (ha : a < 0) (hb : b < 0) (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (z : FiniteUnits R) (k : ℕ) :
    reduction (coefficientAt A w z k) =
      ∑ x ∈ vectors ha hb z k, reduction (weightAt A w z x.val) := by
  classical
  let L := {x : B a b | x ∈ (fromAdelic z).val.leftRing ∧ x.re = 0 ∧ Visibility.nrd x = (k : ℚ)}
  have hL : L.Finite := latticeSphere_finite ha hb z k
  have he : coefficientAt A w z k = ∑ᶠ x ∈ L, weightAt A w z x := by
    apply finsum_mem_inter_support_eq'
    intro x hx
    have hint : x ∈ (fromAdelic z).val.leftRing := by
      by_contra h
      exact hx (ite_eq_right h)
    exact ⟨fun h => ⟨hint, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩
  rw [he, finsum_mem_eq_finite_toFinset_sum _ hL, map_sum]
  symm
  refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    exact hL.mem_toFinset.mpr ⟨x.prop.1, x.prop.2, (mem_vectors ha hb z k x).mp hx⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro y hy
    obtain ⟨hy₁, hy₂, hy₃⟩ := hL.mem_toFinset.mp hy
    exact ⟨⟨y, hy₁, hy₂⟩, (mem_vectors ha hb z k _).mpr hy₃, rfl⟩

/-- The frameTheta identity at the representative used by this frame. -/
theorem frame_theta {O S : Type} [CommRing O] [CommRing S] (reduction : O →+* S)
    (ha : a < 0) (hb : b < 0) (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (k : ℕ) :
    reduction (coefficientAt A w z k) = (D.frame reduction ha hb A w).theta k :=
  coefficientAt_eq_vectors reduction ha hb A w z k

/-- The frameScale identity of the same integral product, after applying any ring map. -/
theorem frame_scale {O S : Type} [CommRing O] [CommRing S] (reduction : O →+* S)
    (ha : a < 0) (hb : b < 0) (A : PhaseData O) (w : (q : Prime) → Bp q.val a b → O)
    (hw : ∀ q ∈ A.places, ∀ (v : ℤ_[q.val]ˣ) (y : Bp q.val a b),
      w q ((v : ℤ_[q.val]) • y) = (A.alpha q v : O) * w q y)
    (hp : p.val ∉ A.support) (x : (D.frame reduction ha hb A w).V) :
    (D.frame reduction ha hb A w).F ((D.frame reduction ha hb A w).scale x) =
      reduction (A.phase p.val : O) * (D.frame reduction ha hb A w).F x := by
  change reduction (weightAt A w z (p.val • x.val)) =
    reduction (A.phase p.val : O) * reduction (weightAt A w z x.val)
  rw [A.phase_good p hp, weightAt_scale A w hw z p.val (A.away_of_not_mem p hp) x.val x.prop.1,
    map_mul]

end FrameCoordinates
end ZInQ.Manuscript.RC.ThetaJoin
