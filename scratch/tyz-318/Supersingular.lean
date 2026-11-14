import Mathlib
import ZInQKernel.Model.Field.ShortWeierstrass

/-!
# tyz-318: the supersingular exponent of `y² = x³ + 4x`, elementary (weak form)

For `p ≡ 3 (mod 4)` and a field `k ⊆ F_{p²}` of characteristic `p` containing `√−1`, every point of
`y² = x³ + 4x` over `k` is killed by `2(p + 1)`.

Proof: `#E(F_p) = p + 1` (pairing `x ↔ −x`, `−1` a non-square); the `p`-power Frobenius `π` and
`[i] : (x, y) ↦ (−x, iy)` satisfy `π² = 1`, `π[i] = −[i]π`; `P + πP` and `[i](P − πP)` are fixed by
`π`, hence `F_p`-points, hence killed by `p + 1`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.T318SS

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1. Counting `E(F_p)` -/

section Count

variable {F : Type*} [Field F] [DecidableEq F]

/-- Points of an affine Weierstrass curve: `O` or an affine nonsingular solution. -/
def ptEquiv (W : WeierstrassCurve.Affine F) :
    W.Point ≃ Option {xy : F × F // W.Nonsingular xy.1 xy.2} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), h⟩
  invFun
    | none => .zero
    | some xy => .some xy.1.1 xy.1.2 xy.2
  left_inv P := by cases P <;> rfl
  right_inv o := by rcases o with _ | ⟨⟨x, y⟩, h⟩ <;> rfl

variable (p : ℕ) [hp : Fact p.Prime]

/-- `y² = x³ + 4x` over `F_p`. -/
abbrev W1 : WeierstrassCurve.Affine (ZMod p) := (ZInQ.shortCurve (4 : ZMod p)).baseChange (ZMod p)

theorem W1_nonsingular_iff (hp2 : p ≠ 2) (x y : ZMod p) :
    (W1 p).Nonsingular x y ↔ y ^ 2 = x ^ 3 + 4 * x := by
  have hΔ : (W1 p).Δ ≠ 0 := by
    have h1 : (W1 p).Δ = -4096 := by
      rw [W1, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, ZInQ.shortCurve_Δ]
      simp; norm_num
    rw [h1, neg_ne_zero]
    have h2 : (4096 : ZMod p) = (2 : ZMod p) ^ 12 := by norm_num
    rw [h2]
    apply pow_ne_zero
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  rw [← equation_iff_nonsingular_of_Δ_ne_zero hΔ, equation_iff]
  simp [W1, WeierstrassCurve.baseChange, WeierstrassCurve.map]

theorem ringChar_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2

theorem sum_quadraticChar_f (hp4 : p % 4 = 3) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 4 * x) = 0 := by
  have hp2 : p ≠ 2 := by omega
  have hneg : quadraticChar (ZMod p) (-1) = -1 := by
    rw [quadraticChar_neg_one (ringChar_ne_two p hp2), ZMod.card, ZMod.χ₄_nat_three_mod_four hp4]
  have hS : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 4 * x) =
      ∑ x : ZMod p, quadraticChar (ZMod p) ((-x) ^ 3 + 4 * (-x)) :=
    (Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun x => rfl)).symm
  have hS' : ∑ x : ZMod p, quadraticChar (ZMod p) ((-x) ^ 3 + 4 * (-x)) =
      -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 4 * x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [show (-x) ^ 3 + 4 * (-x) = (-1) * (x ^ 3 + 4 * x) by ring, map_mul, hneg, neg_one_mul]
  rw [hS'] at hS
  linarith

theorem card_W1 (hp4 : p % 4 = 3) : Nat.card (W1 p).Point = p + 1 := by
  classical
  have hp2 : p ≠ 2 := by omega
  rw [Nat.card_congr (ptEquiv (W1 p)), Finite.card_option]
  congr 1
  have e1 : Nat.card {xy : ZMod p × ZMod p // (W1 p).Nonsingular xy.1 xy.2} =
      Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + 4 * xy.1} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun xy => W1_nonsingular_iff p hp2 xy.1 xy.2))
  rw [e1, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_prod_type]
  have h1 : ∀ x : ZMod p, (∑ y : ZMod p, if y ^ 2 = x ^ 3 + 4 * x then 1 else 0 : ℕ) =
      (Set.toFinset {y : ZMod p | y ^ 2 = x ^ 3 + 4 * x}).card := by
    intro x
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp
  simp_rw [h1]
  have h2 : ((∑ x : ZMod p, (Set.toFinset {y : ZMod p | y ^ 2 = x ^ 3 + 4 * x}).card : ℕ) : ℤ) =
      (p : ℤ) := by
    push_cast
    simp_rw [quadraticChar_card_sqrts (ringChar_ne_two p hp2)]
    rw [Finset.sum_add_distrib, sum_quadraticChar_f p hp4]
    simp
  exact_mod_cast h2

end Count

/-! ## §2. `[i]` on a curve `y² = x³ + a₄x` over a field with `ι² = −1` -/

section IMap

variable {k : Type*} [Field k] [DecidableEq k] (C : WeierstrassCurve k)
  (ha₁ : C.a₁ = 0) (ha₂ : C.a₂ = 0) (ha₃ : C.a₃ = 0) (ha₆ : C.a₆ = 0)
  {ι : k} (hι : ι ^ 2 = -1)

include ha₁ ha₂ ha₃ ha₆ hι

theorem ι_ne_zero : ι ≠ 0 := by
  intro h; rw [h] at hι; have : (0 : k) = -1 := by simpa using hι
  exact one_ne_zero (neg_eq_zero.mp this.symm)

theorem nonsingular_iK {x y : k} (h : C.toAffine.Nonsingular x y) :
    C.toAffine.Nonsingular (-x) (ι * y) := by
  have hι0 := ι_ne_zero C ha₁ ha₂ ha₃ ha₆ hι
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff'] at h ⊢
  simp only [ha₁, ha₂, ha₃, ha₆] at h ⊢
  obtain ⟨he, hn⟩ := h
  refine ⟨by linear_combination y ^ 2 * hι - he, ?_⟩
  rcases hn with h | h
  · left
    intro h'
    apply h
    linear_combination h'
  · right
    intro h'
    apply h
    have : ι * (2 * y) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hι0
    · linear_combination h0

/-- `[i]` : `O ↦ O`, `(x, y) ↦ (−x, ιy)`. -/
def iK : C.toAffine.Point → C.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (-x) (ι * y) (nonsingular_iK C ha₁ ha₂ ha₃ ha₆ hι h)

theorem iK_some {x y : k} (h : C.toAffine.Nonsingular x y) :
    iK C ha₁ ha₂ ha₃ ha₆ hι (.some x y h) = .some (-x) (ι * y) (nonsingular_iK C ha₁ ha₂ ha₃ ha₆ hι h) :=
  rfl

theorem div_iota_mul (A B : k) : A / (ι * B) = -ι * (A / B) := by
  have hι0 := ι_ne_zero C ha₁ ha₂ ha₃ ha₆ hι
  have hinv : ι⁻¹ = -ι := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination -hι
  rw [mul_comm ι B, ← div_div, div_eq_mul_inv _ ι, hinv]
  ring

theorem slope_iK (x₁ x₂ y₁ y₂ : k) :
    C.toAffine.slope (-x₁) (-x₂) (ι * y₁) (ι * y₂) = -ι * C.toAffine.slope x₁ x₂ y₁ y₂ := by
  have hι0 := ι_ne_zero C ha₁ ha₂ ha₃ ha₆ hι
  by_cases hx : x₁ = x₂
  · have hx' : -x₁ = -x₂ := by rw [hx]
    by_cases hy : y₁ = C.toAffine.negY x₂ y₂
    · have hy' : ι * y₁ = C.toAffine.negY (-x₂) (ι * y₂) := by
        simp only [negY, ha₁, ha₃] at hy ⊢
        rw [hy]; ring
      rw [slope_of_Y_eq hx hy, slope_of_Y_eq hx' hy', mul_zero]
    · have hy' : ι * y₁ ≠ C.toAffine.negY (-x₂) (ι * y₂) := by
        simp only [negY, ha₁, ha₃] at hy ⊢
        intro h
        apply hy
        have : ι * (y₁ - (-y₂ - 0 * x₂ - 0)) = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hι0
        · linear_combination h0
      rw [slope_of_Y_ne hx hy, slope_of_Y_ne hx' hy']
      simp only [negY, ha₁, ha₂, ha₃]
      rw [show ι * y₁ - (-(ι * y₁) - 0 * -x₁ - 0) = ι * (y₁ - (-y₁ - 0 * x₁ - 0)) by ring,
        div_iota_mul C ha₁ ha₂ ha₃ ha₆ hι]
      congr 2
      ring
  · have hx' : -x₁ ≠ -x₂ := fun h => hx (neg_injective h)
    rw [slope_of_X_ne hx, slope_of_X_ne hx']
    rw [show -x₁ - -x₂ = -(x₁ - x₂) by ring, div_neg,
      show ι * y₁ - ι * y₂ = ι * (y₁ - y₂) by ring]
    ring

theorem iK_add (P Q : C.toAffine.Point) :
    iK C ha₁ ha₂ ha₃ ha₆ hι (P + Q) = iK C ha₁ ha₂ ha₃ ha₆ hι P + iK C ha₁ ha₂ ha₃ ha₆ hι Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · have hι0 := ι_ne_zero C ha₁ ha₂ ha₃ ha₆ hι
    by_cases hxy : x₁ = x₂ ∧ y₁ = C.toAffine.negY x₂ y₂
    · have hxy' : -x₁ = -x₂ ∧ ι * y₁ = C.toAffine.negY (-x₂) (ι * y₂) := by
        refine ⟨by rw [hxy.1], ?_⟩
        have := hxy.2
        simp only [negY, ha₁, ha₃] at this ⊢
        rw [this]; ring
      rw [Point.add_of_Y_eq hxy.1 hxy.2, iK_some, iK_some, Point.add_of_Y_eq hxy'.1 hxy'.2]
      rfl
    · have hxy' : ¬(-x₁ = -x₂ ∧ ι * y₁ = C.toAffine.negY (-x₂) (ι * y₂)) := by
        rintro ⟨h1, h2⟩
        apply hxy
        refine ⟨neg_injective h1, ?_⟩
        simp only [negY, ha₁, ha₃] at h2 ⊢
        have : ι * (y₁ - (-y₂ - 0 * x₂ - 0)) = 0 := by linear_combination h2
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hι0
        · linear_combination h0
      rw [Point.add_some hxy, iK_some, iK_some, iK_some, Point.add_some hxy', Point.some.injEq]
      have hs := slope_iK C ha₁ ha₂ ha₃ ha₆ hι x₁ x₂ y₁ y₂
      constructor
      · simp only [addX, ha₁, ha₂]
        rw [hs]
        linear_combination (-(C.toAffine.slope x₁ x₂ y₁ y₂) ^ 2) * hι
      · simp only [addY, negAddY, addX, negY, ha₁, ha₂, ha₃]
        rw [hs]
        linear_combination (-ι * C.toAffine.slope x₁ x₂ y₁ y₂ ^ 3) * hι

theorem iK_iK (P : C.toAffine.Point) :
    iK C ha₁ ha₂ ha₃ ha₆ hι (iK C ha₁ ha₂ ha₃ ha₆ hι P) = -P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [iK_some, iK_some, Point.neg_some, Point.some.injEq]
    refine ⟨neg_neg x, ?_⟩
    simp only [negY, ha₁, ha₃]
    linear_combination y * hι

/-- `[i]` as an additive map. -/
def iKHom : C.toAffine.Point →+ C.toAffine.Point :=
  AddMonoidHom.mk' (iK C ha₁ ha₂ ha₃ ha₆ hι) (iK_add C ha₁ ha₂ ha₃ ha₆ hι)

end IMap

/-! ## §3. Frobenius and the exponent `2(p + 1)` -/

section Frob

variable (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [DecidableEq k] [CharP k p]

/-- The roots of `X^p − X` in `k` are the elements of the prime field. -/
theorem exists_zmod_of_pow_eq (r : k) (hr : r ^ p = r) :
    ∃ a : ZMod p, (ZMod.castHom (dvd_refl p) k) a = r := by
  classical
  by_contra hne
  push_neg at hne
  set f : Polynomial k := Polynomial.X ^ p - Polynomial.X
  have hp1 : 1 < p := hp.out.one_lt
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hp1
  have hdeg : f.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq k hp1
  set S : Finset k := insert r (Finset.univ.image (ZMod.castHom (dvd_refl p) k))
  have hSsub : S ⊆ f.roots.toFinset := by
    intro z hz
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0, Polynomial.IsRoot.def]
    simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · rw [hr, sub_self]
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
      rw [← map_pow, ZMod.pow_card, sub_self]
  have hcardS : S.card = p + 1 := by
    rw [Finset.card_insert_of_notMem, Finset.card_image_of_injective _ (RingHom.injective _),
      Finset.card_univ, ZMod.card]
    intro hmem
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hmem
    exact hne a ha
  have h1 := Finset.card_le_card hSsub
  have h2 := Multiset.toFinset_card_le f.roots
  have h3 := Polynomial.card_roots' f
  omega

end Frob

section Main

variable (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [DecidableEq k] [Algebra (ZMod p) k]

theorem exists_zmod_of_pow_eq' (r : k) (hr : r ^ p = r) :
    ∃ a : ZMod p, algebraMap (ZMod p) k a = r := by
  haveI : CharP k p := charP_of_injective_algebraMap' (ZMod p) p
  obtain ⟨a, ha⟩ := exists_zmod_of_pow_eq p k r hr
  refine ⟨a, ?_⟩
  rw [← ha]
  exact congrFun (congrArg DFunLike.coe (RingHom.ext_zmod (algebraMap (ZMod p) k)
    (ZMod.castHom (dvd_refl p) k))) a

/-- `E = (y² = x³ + 4x)⁄k`. -/
abbrev Ek : WeierstrassCurve k := (ZInQ.shortCurve (4 : ZMod p)).baseChange k

@[simp] theorem Ek_a₁ : (Ek p k).a₁ = 0 := by simp [Ek, WeierstrassCurve.baseChange]
@[simp] theorem Ek_a₂ : (Ek p k).a₂ = 0 := by simp [Ek, WeierstrassCurve.baseChange]
@[simp] theorem Ek_a₃ : (Ek p k).a₃ = 0 := by simp [Ek, WeierstrassCurve.baseChange]
@[simp] theorem Ek_a₆ : (Ek p k).a₆ = 0 := by simp [Ek, WeierstrassCurve.baseChange]

/-- **The weak supersingular exponent**: for `p ≡ 3 (mod 4)`, `k ⊆ F_{p²}` with `ι² = −1`, every point
of `(y² = x³ + 4x)⁄k` is killed by `2(p + 1)`. -/
theorem two_mul_succ_nsmul_Ek (hp4 : p % 4 = 3) (hk : ∀ r : k, r ^ (p ^ 2) = r) {ι : k}
    (hι : ι ^ 2 = -1) (P : (Ek p k).toAffine.Point) : (2 * (p + 1)) • P = 0 := by
  set W0 := ZInQ.shortCurve (4 : ZMod p)
  have hcardp : Fintype.card (ZMod p) = p := ZMod.card p
  set frob : k →ₐ[ZMod p] k := FiniteField.frobeniusAlgHom (ZMod p) k
  have hfrob : ∀ r : k, frob r = r ^ p := by
    intro r; simp [frob, FiniteField.frobeniusAlgHom_apply, hcardp]
  let π : (Ek p k).toAffine.Point →+ (Ek p k).toAffine.Point := Point.map (W' := W0) frob
  let ψ : (W0.baseChange (ZMod p)).toAffine.Point →+ (Ek p k).toAffine.Point :=
    Point.map (W' := W0) (Algebra.ofId (ZMod p) k)
  -- `π² = 1`
  have hππ : ∀ Q, π (π Q) = Q := by
    intro Q
    rcases Q with _ | ⟨x, y, h⟩
    · rfl
    · simp only [π, Point.map_some, Point.some.injEq, hfrob]
      rw [← pow_mul, ← pow_mul, ← sq, hk, hk]
      exact ⟨rfl, rfl⟩
  -- fixed points are `F_p`-points, killed by `p + 1`
  have hcard := card_W1 p hp4
  have hfix : ∀ Q, π Q = Q → (p + 1) • Q = 0 := by
    intro Q hQ
    rcases Q with _ | ⟨x, y, h⟩
    · exact nsmul_zero _
    · simp only [π, Point.map_some, Point.some.injEq, hfrob] at hQ
      obtain ⟨a, rfl⟩ := exists_zmod_of_pow_eq' p k x hQ.1
      obtain ⟨b, rfl⟩ := exists_zmod_of_pow_eq' p k y hQ.2
      have h' : (W0.baseChange (ZMod p)).toAffine.Nonsingular a b :=
        (WeierstrassCurve.Affine.baseChange_nonsingular (W := W0) (f := Algebra.ofId (ZMod p) k)
          (algebraMap (ZMod p) k).injective a b).mp h
      have hψ : ψ (.some a b h') = .some _ _ h := rfl
      rw [← hψ, ← map_nsmul]
      have : (p + 1) • (Point.some a b h' : (W0.baseChange (ZMod p)).toAffine.Point) = 0 := by
        rw [← hcard]; exact card_nsmul_eq_zero'
      rw [this, map_zero]
  -- `[i]`
  let iH := iKHom (Ek p k) (Ek_a₁ p k) (Ek_a₂ p k) (Ek_a₃ p k) (Ek_a₆ p k) hι
  have hiH : ∀ Q, iH (iH Q) = -Q := iK_iK (Ek p k) (Ek_a₁ p k) (Ek_a₂ p k) (Ek_a₃ p k) (Ek_a₆ p k) hι
  have hιp : ι ^ p = -ι := by
    obtain ⟨m, hm⟩ : ∃ m, p = 4 * m + 3 := ⟨p / 4, by omega⟩
    rw [hm, show 4 * m + 3 = 2 * (2 * m + 1) + 1 by ring, pow_succ, pow_mul, hι,
      Odd.neg_one_pow ⟨m, rfl⟩, neg_one_mul]
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hπi : ∀ Q, π (iH Q) = -(iH (π Q)) := by
    intro Q
    rcases Q with _ | ⟨x, y, h⟩
    · rfl
    · show π (iK (Ek p k) (Ek_a₁ p k) (Ek_a₂ p k) (Ek_a₃ p k) (Ek_a₆ p k) hι (.some x y h)) =
        -(iK (Ek p k) (Ek_a₁ p k) (Ek_a₂ p k) (Ek_a₃ p k) (Ek_a₆ p k) hι (π (.some x y h)))
      simp only [π, iK_some, Point.map_some, Point.neg_some, Point.some.injEq, hfrob]
      refine ⟨hpodd.neg_pow x, ?_⟩
      simp only [negY, Ek_a₁, Ek_a₃]
      rw [mul_pow, hιp]; ring
  -- assemble
  have h1 : (p + 1) • (P + π P) = 0 := by
    apply hfix
    rw [map_add, hππ, add_comm]
  have h2 : (p + 1) • (P - π P) = 0 := by
    have hQ2 : (p + 1) • iH (P - π P) = 0 := by
      apply hfix
      rw [hπi, map_sub, hππ, ← neg_sub, map_neg, neg_neg]
    have := congrArg iH hQ2
    rw [map_nsmul, map_zero, hiH, smul_neg, neg_eq_zero] at this
    exact this
  calc (2 * (p + 1)) • P = (p + 1) • (P + π P) + (p + 1) • (P - π P) := by
        rw [mul_comm, mul_nsmul', ← nsmul_add]; congr 1; abel
    _ = 0 := by rw [h1, h2, add_zero]

end Main

/-- **The weak supersingular exponent of `y² = x³ + 4x`, PROVED** (statement over the plain curve
`ZInQ.shortCurve (4 : k)`): for `p ≡ 3 (mod 4)` and a field `k` of characteristic `p` with
`r^{p²} = r` for all `r` and containing `√−1`, every point is killed by `2(p + 1)`. -/
theorem supersingularExponentWeak : ∀ p : ℕ, p.Prime → p % 4 = 3 →
    ∀ (k : Type) [Field k] [CharP k p] [DecidableEq k], (∀ r : k, r ^ (p ^ 2) = r) →
      (∃ ι : k, ι ^ 2 = -1) →
      ∀ P : (ZInQ.shortCurve (4 : k)).toAffine.Point, (2 * (p + 1)) • P = 0 := by
  intro p hp hp4 k _ _ _ hk hι
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  obtain ⟨ι, hι⟩ := hι
  have hE : Ek p k = ZInQ.shortCurve 4 := by
    ext <;> simp [Ek, WeierstrassCurve.baseChange]
    exact map_ofNat _ 4
  have key : ∀ C : WeierstrassCurve k, Ek p k = C →
      ∀ P : C.toAffine.Point, (2 * (p + 1)) • P = 0 := by
    rintro C rfl P
    exact two_mul_succ_nsmul_Ek p k hp4 hk hι P
  exact key _ hE

end ZInQ.Contrib.TYZGenus.T318SS

#print axioms ZInQ.Contrib.TYZGenus.T318SS.supersingularExponentWeak
