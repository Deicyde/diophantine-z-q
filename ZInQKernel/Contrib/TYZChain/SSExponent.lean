import Mathlib
import ZInQKernel.Model.Field.ShortWeierstrass

/-!
# TYZ chain: ss-exponent (`SupersingularExponentA` proved; not needed by the main theorem)

Task tyz-chain (2026-11-14). This module is `scratch/ss-exponent/SSExponent.lean` unchanged except that its `#print axioms`
lines were moved to `scratch/tyz-chain/Check.lean`. The original header follows.
-/


/-!
# ss-exponent: the supersingular exponent of `y² = x³ + 4x` (the leaf `SupersingularExponentA`), PROVED

Task ss-exponent (2026-11-14). Report: `docs/research/ss-exponent.md`; log: `scratch/ss-exponent/log.md`.

`SupersingularExponentA` (verbatim copy of the textbook leaf of `scratch/tyz-318/Lemma318.lean` §1): for a
prime `p ≡ 3 (mod 4)` and a field `k` of characteristic `p` with `r^{p²} = r` for all `r`, every point of
`y² = x³ + 4x` over `k` is killed by `p + 1`. Main theorem: `supersingularExponentA : SupersingularExponentA`.

Elementary proof (no characteristic polynomial of Frobenius, no isogenies):
* §1–§3 (copied from `scratch/tyz-318/Supersingular.lean`): `#E(F_p) = p + 1` (character sum, `x ↔ −x`);
  `[i] : (x, y) ↦ (−x, ιy)` is additive with `[i]² = −1`; the `p`-power Frobenius `π` on `E(k)`.
* §4 (new, abstract): a finite abelian group with an involution `π`, an automorphism `i`, `i² = −1`,
  `π i = −i π`, whose `π`-fixed subgroups have order dividing `N = 2^v m` (`m` odd), is killed by `N`.
  Weak exponent `2N` (tyz-318's argument); `#G[2^{v+1}] ≤ #(π-fixed part)·#(π-antifixed part) ≤ 2^{2v}`;
  the chain `ker (1+i)^n` strictly increases until it is stable, and `(1+i)² = 2i`, so
  `(1+i)^{2v} = 2^v i^v` already kills `G[2^{v+1}]`.
* §5: `π`-fixed points of `E(k)` are `F_p`-points (so `π`-fixed subgroups have order dividing `p + 1`);
  if `k` has no `√−1` then `k = F_p` (if `s = r − r^p ≠ 0` then `(s^{(p−1)/2})² = −1`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.SSExponent

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

end Main

/-! ## §4. The abstract exponent lemma -/

section Abstract

variable {G : Type*} [AddCommGroup G]

theorem iterate_nsmul (f : G →+ G) (k c : ℕ) (x : G) : f^[k] (c • x) = c • f^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, map_nsmul, ih]

theorem iterate_zero (f : G →+ G) (k : ℕ) : f^[k] 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, map_zero, ih]

/-- `ker f^[n]` as an additive subgroup. -/
def kerIt (f : G →+ G) (n : ℕ) : AddSubgroup G where
  carrier := {x | f^[n] x = 0}
  zero_mem' := iterate_zero f n
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [show f^[n] (a + b) = f^[n] a + f^[n] b from iterate_map_add f n a b, ha, hb, add_zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rw [show f^[n] (-a) = -f^[n] a from iterate_map_neg f n a, ha, neg_zero]

theorem mem_kerIt (f : G →+ G) (n : ℕ) (x : G) : x ∈ kerIt f n ↔ f^[n] x = 0 := Iff.rfl

theorem kerIt_mono (f : G →+ G) (n : ℕ) : kerIt f n ≤ kerIt f (n + 1) := by
  intro x hx
  rw [mem_kerIt] at *
  rw [Function.iterate_succ_apply', hx, map_zero]

theorem kerIt_stab (f : G →+ G) {n : ℕ} (h : kerIt f n = kerIt f (n + 1)) (r : ℕ) :
    kerIt f (n + r) = kerIt f (n + r + 1) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    apply le_antisymm (kerIt_mono f _)
    intro x hx
    rw [mem_kerIt, show n + (r + 1) + 1 = (n + r + 1) + 1 by omega, Function.iterate_succ_apply]
      at hx
    have : f x ∈ kerIt f (n + r) := by rw [ih]; exact hx
    rw [mem_kerIt, show n + (r + 1) = (n + r) + 1 by omega, Function.iterate_succ_apply]
    exact this

/-- **Abstract supersingular exponent.** A finite abelian group `G` with an involution `π` and an
automorphism `i` with `i² = −1`, `π i = −i π`, all of whose `π`-fixed subgroups have order dividing
`N = 2^v m` (`m` odd), is killed by `N`. -/
theorem nsmul_eq_zero_of_frob [Finite G] (π i : G →+ G) (v m : ℕ) (hm : Odd m)
    (hππ : ∀ Q, π (π Q) = Q) (hii : ∀ Q, i (i Q) = -Q) (hπi : ∀ Q, π (i Q) = -(i (π Q)))
    (hA : ∀ S : AddSubgroup G, (∀ Q ∈ S, π Q = Q) → Nat.card S ∣ 2 ^ v * m) :
    ∀ P : G, (2 ^ v * m) • P = 0 := by
  set N := 2 ^ v * m with hN
  have hinj : Function.Injective i := by
    intro a b hab
    have := congrArg i hab
    rw [hii, hii] at this
    exact neg_injective this
  -- fixed points are killed by `N`
  have hfix : ∀ Q, π Q = Q → N • Q = 0 := by
    intro Q hQ
    have h1 := hA (AddSubgroup.zmultiples Q) (by
      intro R hR
      obtain ⟨z, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hR
      simp [map_zsmul, hQ])
    rw [Nat.card_zmultiples] at h1
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp h1
  -- the weak exponent `2N`
  have hweak : ∀ P : G, (2 * N) • P = 0 := by
    intro P
    have h1 : N • (P + π P) = 0 := by
      apply hfix
      rw [map_add, hππ, add_comm]
    have h2 : N • (P - π P) = 0 := by
      have hQ2 : N • i (P - π P) = 0 := by
        apply hfix
        rw [hπi, map_sub, hππ, ← neg_sub, map_neg, neg_neg]
      rw [← map_nsmul] at hQ2
      exact hinj (hQ2.trans (map_zero i).symm)
    calc (2 * N) • P = N • (P + π P) + N • (P - π P) := by
          rw [mul_comm, mul_nsmul', ← nsmul_add]; congr 1; abel
      _ = 0 := by rw [h1, h2, add_zero]
  -- `j = 1 + i`, `j² = 2 i`
  set j : G →+ G := AddMonoidHom.id G + i with hj
  have hjj : ∀ Q : G, j (j Q) = 2 • i Q := by
    intro Q
    simp only [hj, AddMonoidHom.add_apply, AddMonoidHom.id_apply, map_add, hii]
    rw [two_nsmul]; abel
  have hj2 : ∀ (n : ℕ) (Q : G), j^[2 * n] Q = 2 ^ n • i^[n] Q := by
    intro n
    induction n with
    | zero => intro Q; simp
    | succ n ih =>
      intro Q
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, Function.iterate_add_apply,
        show j^[2] Q = j (j Q) from rfl, hjj, iterate_nsmul, ih, Function.iterate_succ_apply,
        smul_smul, pow_succ']
  have hinjv : ∀ n, Function.Injective i^[n] := fun n => hinj.iterate n
  have hK : ∀ (n : ℕ) (x : G), x ∈ kerIt j (2 * n) ↔ 2 ^ n • x = 0 := by
    intro n x
    rw [mem_kerIt, hj2, ← iterate_nsmul]
    constructor
    · intro h; exact hinjv n (by rw [h, iterate_zero])
    · intro h; rw [h, iterate_zero]
  -- the `2^{v+1}`-torsion has order `≤ 2^{2v}`
  set M := kerIt j (2 * (v + 1)) with hMdef
  let MA : AddSubgroup G :=
    { carrier := {x | 2 ^ (v + 1) • x = 0 ∧ π x = x}
      zero_mem' := by simp
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨by rw [nsmul_add, ha1, hb1, add_zero], by rw [map_add, ha2, hb2]⟩
      neg_mem' := by
        rintro a ⟨ha1, ha2⟩
        exact ⟨by rw [smul_neg, ha1, neg_zero], by rw [map_neg, ha2]⟩ }
  let MB : AddSubgroup G :=
    { carrier := {x | 2 ^ (v + 1) • x = 0 ∧ π x = -x}
      zero_mem' := by simp
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        exact ⟨by rw [nsmul_add, ha1, hb1, add_zero], by rw [map_add, ha2, hb2, neg_add]⟩
      neg_mem' := by
        rintro a ⟨ha1, ha2⟩
        exact ⟨by rw [smul_neg, ha1, neg_zero], by rw [map_neg, ha2]⟩ }
  have hMA : Nat.card MA ∣ 2 ^ v := by
    have h1 : Nat.card MA ∣ 2 ^ v * m := hA MA (fun Q hQ => hQ.2)
    have hcop : Nat.Coprime (Nat.card MA) m := by
      apply Nat.coprime_of_dvd
      intro q hq hqA hqm
      have : Fact q.Prime := ⟨hq⟩
      obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hqA
      have h2 : 2 ^ (v + 1) • x = 0 := Subtype.ext x.2.1
      have h3 : q ∣ 2 ^ (v + 1) := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero h2
      have h4 : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h3)
      subst h4
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hqm)
    exact hcop.dvd_of_dvd_mul_right h1
  have hMB : Nat.card MB ≤ Nat.card MA := by
    refine Nat.card_le_card_of_injective (fun x => ⟨i x.1, ?_, ?_⟩) ?_
    · rw [← map_nsmul, x.2.1, map_zero]
    · rw [hπi, x.2.2, map_neg, neg_neg]
    · intro a b hab
      exact Subtype.ext (hinj (congrArg Subtype.val hab))
  have hM : Nat.card M ≤ 2 ^ (2 * v) := by
    let f : M →+ G := (AddMonoidHom.id G - π).comp M.subtype
    have hrange : f.range ≤ MB := by
      rintro _ ⟨x, rfl⟩
      have hx : 2 ^ (v + 1) • (x : G) = 0 := (hK (v + 1) x).mp x.2
      refine ⟨?_, ?_⟩
      · simp only [f, AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
          AddSubgroup.coe_subtype]
        rw [nsmul_sub, hx, ← map_nsmul, hx, map_zero, sub_zero]
      · simp only [f, AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
          AddSubgroup.coe_subtype]
        rw [map_sub, hππ, neg_sub]
    have hker : Nat.card f.ker ≤ Nat.card MA := by
      refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, ?_, ?_⟩) ?_
      · exact (hK (v + 1) x.1.1).mp x.1.2
      · have := x.2
        rw [AddMonoidHom.mem_ker] at this
        simp only [f, AddMonoidHom.comp_apply, AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
          AddSubgroup.coe_subtype] at this
        exact (sub_eq_zero.mp this).symm
      · intro a b hab
        have h := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h)
    have h1 := AddSubgroup.card_ker_mul_card_range f
    have h2 : Nat.card f.range ≤ Nat.card MB := AddSubgroup.card_le_of_le hrange
    have hMA' : Nat.card MA ≤ 2 ^ v := Nat.le_of_dvd (by positivity) hMA
    calc Nat.card M = Nat.card f.ker * Nat.card f.range := h1.symm
      _ ≤ 2 ^ v * 2 ^ v := Nat.mul_le_mul (hker.trans hMA') (h2.trans (hMB.trans hMA'))
      _ = 2 ^ (2 * v) := by rw [← pow_add, two_mul]
  -- the chain `ker j^n` stabilizes by `n = 2v`
  have key : kerIt j (2 * v) = M := by
    by_contra hne
    have hlt : ∀ n, n ≤ 2 * v → kerIt j n < kerIt j (n + 1) := by
      intro n hn
      refine lt_of_le_of_ne (kerIt_mono j n) (fun h => hne ?_)
      have e1 := kerIt_stab j h (2 * v - n)
      have e2 := kerIt_stab j h (2 * v - n + 1)
      rw [show n + (2 * v - n) = 2 * v by omega] at e1
      rw [show n + (2 * v - n + 1) = 2 * v + 1 by omega] at e2
      rw [hMdef, show 2 * (v + 1) = 2 * v + 1 + 1 by ring, ← e2, e1]
    have hcard : ∀ n, n ≤ 2 * v + 1 → 2 ^ n ≤ Nat.card (kerIt j n) := by
      intro n
      induction n with
      | zero => intro _; rw [pow_zero]; exact Nat.card_pos
      | succ n ih =>
        intro hn
        have h1 := hlt n (by omega)
        have h2 := AddSubgroup.card_dvd_of_le h1.le
        have h3 := AddSubgroup.card_lt_of_lt h1
        obtain ⟨c, hc⟩ := h2
        have hc2 : 2 ≤ c := by
          have h4 : Nat.card (kerIt j n) * 1 < Nat.card (kerIt j n) * c := by
            rw [mul_one, ← hc]; exact h3
          exact Nat.lt_of_mul_lt_mul_left h4
        rw [pow_succ, hc]
        exact Nat.mul_le_mul (ih (by omega)) hc2
    have h1 := hcard (2 * v + 1) le_rfl
    have h2 : Nat.card (kerIt j (2 * v + 1)) ≤ Nat.card M := by
      apply AddSubgroup.card_le_of_le
      rw [hMdef, show 2 * (v + 1) = 2 * v + 1 + 1 by ring]
      exact kerIt_mono j _
    have h3 : 2 ^ (2 * v) < 2 ^ (2 * v + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  intro P
  have h1 : 2 ^ (v + 1) • (m • P) = 0 := by
    rw [smul_smul, pow_succ, mul_comm (2 ^ v) 2, mul_assoc, ← hN]; exact hweak P
  have h2 : m • P ∈ kerIt j (2 * v) := by rw [key, hMdef, hK]; exact h1
  rw [hK] at h2
  rw [hN, ← smul_smul]
  exact h2

end Abstract

/-! ## §5. The strong exponent `p + 1` -/

section Strong

variable (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [DecidableEq k] [Algebra (ZMod p) k]

/-- **The supersingular exponent**: for `p ≡ 3 (mod 4)` and `k ⊆ F_{p²}`, every point of
`(y² = x³ + 4x)⁄k` is killed by `p + 1`. -/
theorem succ_nsmul_Ek (hp4 : p % 4 = 3) (hk : ∀ r : k, r ^ (p ^ 2) = r)
    (P : (Ek p k).toAffine.Point) : (p + 1) • P = 0 := by
  haveI : CharP k p := charP_of_injective_algebraMap' (ZMod p) p
  set W0 := ZInQ.shortCurve (4 : ZMod p)
  have hcardp : Fintype.card (ZMod p) = p := ZMod.card p
  set frob : k →ₐ[ZMod p] k := FiniteField.frobeniusAlgHom (ZMod p) k
  have hfrob : ∀ r : k, frob r = r ^ p := by
    intro r; simp [frob, FiniteField.frobeniusAlgHom_apply, hcardp]
  let π : (Ek p k).toAffine.Point →+ (Ek p k).toAffine.Point := Point.map (W' := W0) frob
  let ψ : (W0.baseChange (ZMod p)).toAffine.Point →+ (Ek p k).toAffine.Point :=
    Point.map (W' := W0) (Algebra.ofId (ZMod p) k)
  have hππ : ∀ Q, π (π Q) = Q := by
    intro Q
    rcases Q with _ | ⟨x, y, h⟩
    · rfl
    · simp only [π, Point.map_some, Point.some.injEq, hfrob]
      rw [← pow_mul, ← pow_mul, ← sq, hk, hk]
      exact ⟨rfl, rfl⟩
  have hcard := card_W1 p hp4
  -- `π`-fixed points are `F_p`-points
  have hrange : ∀ Q, π Q = Q → ∃ Q', ψ Q' = Q := by
    intro Q hQ
    rcases Q with _ | ⟨x, y, h⟩
    · exact ⟨0, rfl⟩
    · simp only [π, Point.map_some, Point.some.injEq, hfrob] at hQ
      obtain ⟨a, rfl⟩ := exists_zmod_of_pow_eq' p k x hQ.1
      obtain ⟨b, rfl⟩ := exists_zmod_of_pow_eq' p k y hQ.2
      have h' : (W0.baseChange (ZMod p)).toAffine.Nonsingular a b :=
        (WeierstrassCurve.Affine.baseChange_nonsingular (W := W0) (f := Algebra.ofId (ZMod p) k)
          (algebraMap (ZMod p) k).injective a b).mp h
      exact ⟨.some a b h', rfl⟩
  have hψinj : Function.Injective ψ :=
    Point.map_injective (W' := W0) (f := Algebra.ofId (ZMod p) k)
  have hfix : ∀ Q, π Q = Q → (p + 1) • Q = 0 := by
    intro Q hQ
    obtain ⟨Q', rfl⟩ := hrange Q hQ
    rw [← map_nsmul, ← hcard, card_nsmul_eq_zero', map_zero]
  by_cases hι : ∃ ι : k, ι ^ 2 = -1
  · obtain ⟨ι, hι⟩ := hι
    have hA : ∀ S : AddSubgroup (Ek p k).toAffine.Point, (∀ Q ∈ S, π Q = Q) →
        Nat.card S ∣ p + 1 := by
      intro S hS
      have hmap : (S.comap ψ).map ψ = S := by
        apply le_antisymm (AddSubgroup.map_comap_le _ _)
        intro Q hQ
        obtain ⟨Q', rfl⟩ := hrange Q (hS Q hQ)
        exact AddSubgroup.mem_map_of_mem _ hQ
      rw [← hmap, AddSubgroup.card_map_of_injective hψinj, ← hcard]
      exact AddSubgroup.card_addSubgroup_dvd_card _
    let iH := iKHom (Ek p k) (Ek_a₁ p k) (Ek_a₂ p k) (Ek_a₃ p k) (Ek_a₆ p k) hι
    have hiH : ∀ Q, iH (iH Q) = -Q :=
      iK_iK (Ek p k) (Ek_a₁ p k) (Ek_a₂ p k) (Ek_a₃ p k) (Ek_a₆ p k) hι
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
    -- finiteness
    have hp1 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
    haveI : Finite k := by
      have hf0 := FiniteField.X_pow_card_sub_X_ne_zero k hp1
      refine Set.finite_univ_iff.mp
        ((Polynomial.roots (Polynomial.X ^ (p ^ 2) - Polynomial.X : Polynomial k)).toFinset.finite_toSet.subset ?_)
      intro r _
      simp [Polynomial.mem_roots hf0, hk r]
    haveI : Finite (Ek p k).toAffine.Point := Finite.of_equiv _ (ptEquiv (Ek p k).toAffine).symm
    obtain ⟨v, m, hm, hpm⟩ := Nat.exists_eq_two_pow_mul_odd (n := p + 1) (by omega)
    rw [hpm] at hA ⊢
    exact nsmul_eq_zero_of_frob π iH v m hm hππ hiH hπi hA P
  · -- no `√−1` in `k`: then `k = F_p` and every point is `π`-fixed
    push_neg at hι
    have hall : ∀ r : k, r ^ p = r := by
      intro r
      by_contra hr
      set s := r - r ^ p with hs
      have hs0 : s ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
      have hsp : s ^ p = -s := by
        rw [hs, sub_pow_char, ← pow_mul, ← sq, hk, neg_sub]
      obtain ⟨t, ht⟩ : ∃ t, p = 2 * t + 1 := ⟨p / 2, by omega⟩
      apply hι (s ^ t)
      have h1 : s ^ (2 * t) * s = -1 * s := by rw [← pow_succ, ← ht, hsp, neg_one_mul]
      rw [← pow_mul, mul_comm]
      exact mul_right_cancel₀ hs0 h1
    apply hfix
    rcases P with _ | ⟨x, y, h⟩
    · rfl
    · simp only [π, Point.map_some, hfrob, hall]

end Strong

/-! ## §6. The leaf, verbatim, and its proof -/

/-- **LEAF SS (supersingular reduction of `A` at `p ≡ 3 (mod 4)`)**: for a prime `p ≡ 3 (mod 4)` and
a field `k` of characteristic `p` all of whose elements satisfy `r^{p²} = r` (i.e. `k ≅ F_p` or
`F_{p²}`), every point of `y² = x³ + 4x` over `k` is killed by `p + 1`.

Verbatim copy of `ZInQ.Contrib.TYZGenus.T318.SupersingularExponentA` (`scratch/tyz-318/Lemma318.lean`
§1); PROVED below (`supersingularExponentA`). -/
def SupersingularExponentA : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 3 → ∀ (k : Type) [Field k] [CharP k p] [DecidableEq k],
    (∀ r : k, r ^ (p ^ 2) = r) → ∀ P : (ZInQ.shortCurve (4 : k)).toAffine.Point, (p + 1) • P = 0

/-- **`SupersingularExponentA` is a theorem** (Mathlib only, elementary). -/
theorem supersingularExponentA : SupersingularExponentA := by
  intro p hp hp4 k _ _ _ hk
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  have hE : Ek p k = ZInQ.shortCurve 4 := by
    ext <;> simp [Ek, WeierstrassCurve.baseChange]
    exact map_ofNat _ 4
  have key : ∀ C : WeierstrassCurve k, Ek p k = C → ∀ P : C.toAffine.Point, (p + 1) • P = 0 := by
    rintro C rfl P
    exact succ_nsmul_Ek p k hp4 hk P
  exact key _ hE

section Examples

open Classical

local instance fact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
local instance fact7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Instance check (the leaf is not vacuous): over `F_{3²} = GaloisField 3 2` every point of
`y² = x³ + 4x` is killed by `4`. -/
example : ∀ P : (ZInQ.shortCurve (4 : GaloisField 3 2)).toAffine.Point, (3 + 1) • P = 0 := by
  haveI : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 3 2) = 3 ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 3 2 two_ne_zero
  exact supersingularExponentA 3 Nat.prime_three (by norm_num) (GaloisField 3 2)
    (fun r => hc ▸ FiniteField.pow_card r)

/-- Instance check over `F_7`: every point of `y² = x³ + 4x` is killed by `8`. -/
example : ∀ P : (ZInQ.shortCurve (4 : ZMod 7)).toAffine.Point, (7 + 1) • P = 0 := by
  exact supersingularExponentA 7 (by norm_num) (by norm_num) (ZMod 7)
    (fun r => by rw [pow_succ, pow_one, pow_mul, ZMod.pow_card, ZMod.pow_card])

end Examples

end ZInQ.Contrib.SSExponent

