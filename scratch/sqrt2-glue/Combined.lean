import ZInQKernel.Contrib.TYZGenus.RingClassBridge
import ZInQKernel.Contrib.TYZGenus.RingClassTwo
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.Algebra.ZMod

/-!
# sqrt2-glue: combined file — TYZ Lemma `torsion2` (`Lemma318Literal HHprime`) unconditionally

Task sqrt2-glue (2026-11-14). This file is the verbatim concatenation of
`scratch/tyz-318/Lemma318.lean` (task tyz-318: `SqrtTwoNotInHHprime → Lemma318Literal HHprime`) and
`scratch/sqrt2-glue/Sqrt2Glue.lean` (this task: `SqrtTwoNotInHHprime` proved), followed by the
combination (§C). Scratch files cannot import each other, hence the copy.
-/


/-!
# tyz-318: TYZ Lemma `torsion2` (`Lemma318Literal HHprime`) from one textbook leaf and one glue Prop

Task tyz-318 (2026-11-13/14). Report: `docs/research/tyz-318.md`; log: `scratch/tyz-318/log.md`.

`Lemma318Literal HHprime` (verbatim copy of `Package.Lemma318Literal`, checked by `rfl`) says: for
squarefree `n ≡ 5 (mod 8)`, every torsion point `P` of `A(ℍ'_n)` (`A : y² = x³ + 4x`) satisfies
`2(P + [i]P) = 0`. Main theorem (`lemma318Literal_HHprime_of_ss_sqrtTwo`, §9):

    SupersingularExponentA → SqrtTwoNotInHHprime → Lemma318Literal HHprime

* `SupersingularExponentA` (LEAF, textbook): for `p ≡ 3 (mod 4)`, every point of `y² = x³ + 4x` over a
  field `k` of characteristic `p` inside `F_{p²}` is killed by `p + 1`.
* `SqrtTwoNotInHHprime` (GLUE, TYZ's Step 3 of the proof of Lemma `torsion2`): `√2 ∉ ℍ'_n`. Proved
  here when `n` is its only divisor `≡ 5 (mod 8)` (`sqrtTwo_not_mem_HHprime_of_single`), so
  `lemma318_at_single` gives Lemma `torsion2` at such `n` from the leaf alone.
* `HHprimeFrobSq` (residue fields of `ℍ'_n` above primes inert in every `K_{d₀}` lie in `F_{p²}`) and
  `HprimeFrobOrderTwo` (the same for one `H'_d`, in Frobenius form) were glue in the first reduction
  (`lemma318Literal_HHprime_of`, `lemma318Literal_HHprime_of'`) and are now PROVED (`hhprimeFrobSq`,
  `hprimeFrobOrderTwo`, §8–§9) from ring-class's splitting law and Mathlib's fundamental identity.

The rest is proved here: the odd part by reduction modulo a prime `p ≡ 3 (mod 8)`, `p ≡ 1 (mod nℓ)`
(Dirichlet, Mathlib), with Tau Ceti's `eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero`
(Silverman VII.3.1(b), vendored and proved); the 2-primary part by the explicit computation
`4S = 0, 2(1+i)S ≠ 0 ⟹ (i(x(S) − x(2S))/2)² = 2`. §10 plugs the result into
`RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD`.

No `sorry`, no `axiom`.
-/

noncomputable section

/-! ## §S. The weak supersingular exponent (from `scratch/tyz-318/Supersingular.lean`, proved) -/

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

namespace ZInQ.Contrib.TYZGenus.T318

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  NumberField WeierstrassCurve.Affine ZInQ.RouteK.Rank5b

/-! ## §0. The target, verbatim -/

/-- Verbatim copy of `Package.Lemma318Literal` (= cm-bridge's `CMBridge.Copy.Lemma318Literal`). -/
def Lemma318Literal (Hn : ℕ → IntermediateField ℚ Qbar) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∀ P ∈ ptsOver (Hn n), IsOfFinAddOrder P → 2 • (P + iPt P) = 0

theorem lemma318Literal_eq : Lemma318Literal = Package.Lemma318Literal := rfl

/-! ## §1. The leaf and the two glue Props -/

/-- **LEAF SS (supersingular reduction of `A` at `p ≡ 3 (mod 4)`)**: for a prime `p ≡ 3 (mod 4)` and
a field `k` of characteristic `p` all of whose elements satisfy `r^{p²} = r` (i.e. `k ≅ F_p` or
`F_{p²}`), every point of `y² = x³ + 4x` over `k` is killed by `p + 1`.

Source: `y² = x³ + 4x` is isomorphic over `F_p` to `y² = x³ + x` (`x ↦ u²x`, `u⁴ = 4`, `u² = ±2`, one of
which is a square), which is supersingular for `p ≡ 3 (mod 4)` (Silverman, *AEC*, Example V.4.5,
UNVERIFIED number); then `a_p = 0`, `#Ã(F_p) = p + 1`, the `p`-power Frobenius satisfies `φ² = [−p]`,
and `Ã(F_{p²}) = ker(1 − φ²) = Ã[p + 1] ≅ (ℤ/(p+1))²` (e.g. Washington, *Elliptic curves*, 2nd ed.,
Prop. 4.37 / Thm. 4.3 + Exercise, UNVERIFIED numbers). Checked numerically for
`p ∈ {3, 7, 11, 19, 23, 31, 43, 47}` (`scratch/tyz-318/ss_check.py`). Textbook, refereed. -/
def SupersingularExponentA : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 3 → ∀ (k : Type) [Field k] [CharP k p] [DecidableEq k],
    (∀ r : k, r ^ (p ^ 2) = r) → ∀ P : (ZInQ.shortCurve (4 : k)).toAffine.Point, (p + 1) • P = 0

/-- **G-Frob (residue degree `≤ 2` of `ℍ'_n` at primes inert in every `K_{d₀}`); glue in the first
reduction, PROVED below (`hhprimeFrobSq`, §8–§9)**: for squarefree
`n ≡ 5 (mod 8)` and an odd prime `p ∤ n` with `(−d₀/p) = −1` for every `d₀ ∣ n`, `d₀ ≡ 5 (mod 8)`,
every prime `𝔓` of `𝓞_{ℍ'_n}` above `p` has residue field inside `F_{p²}`: `a^{p²} ≡ a (mod 𝔓)`.

Proof sketch (formalized in §8–§9 via Frobenius elements): `p` is inert in `K_{d₀}` and `p𝓞_{K_{d₀}}` is
generated by `p ∈ ℤ ⊂ ℤ + 4𝓞_{K_{d₀}}`, prime to the conductor, so its class in `Pic(𝒪_{d₀,4})` is
trivial and it splits completely in `H_{d₀,4}/K_{d₀}` (Tau Ceti's Artin reciprocity for ring class
fields): Frobenius at `p` has order `2` on `H_{d₀,4} ⊇ H'_{d₀}`. On the multiquadratic `L_n(i)` it has
order `≤ 2`. `p` is unramified in `ℍ'_n = L_n(i) · Π H'_{d₀}` (`p ∤ 2n`), `ℍ'_n/ℚ` is normal
(`RingClassBridge.normalFields_HHprime'`) and `Gal(ℍ'_n/ℚ)` embeds into the product of the Galois
groups of the factors, so Frobenius has order `≤ 2` and residue degrees are `≤ 2`. TYZ use the same
primes (`p ≡ 3 (mod 8)` inert in the `K_{d₀}`) in their proof of Lemma `torsion2` (cm-bridge.md §4,
reading of L2230–2300; source not on this host). -/
def HHprimeFrobSq : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ n →
    (∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → jacobiSym (-(d₀ : ℤ)) p = -1) →
    ∀ 𝔓 : Ideal (𝓞 (HHprime n)), 𝔓.IsPrime → (p : 𝓞 (HHprime n)) ∈ 𝔓 →
      ∀ a : 𝓞 (HHprime n), a ^ (p ^ 2) - a ∈ 𝔓

/-- **GLUE G-√2 (`√2 ∉ ℍ'_n`)**: for squarefree `n ≡ 5 (mod 8)`, `2` is not a square in `ℍ'_n`.
TYZ prove this as Step 3 of their proof of Lemma `torsion2` (L2230–2300 as read by `rv-nt-tyz.md`
B4 and `cm-bridge.md` §4; source not on this host: HUMAN CHECK of the step's statement). For one
factor it is ring-class's `RingClass.not_adjSqrt_two_le_Hprime` (`√2 ∉ H'_d`, proved); for the
compositum, proof sketch in `docs/research/tyz-318.md` §3 (local class field theory at `2`: all
`K_{d₀} ⊗ ℚ₂` are the same field `ℚ₂(√3) ⊂ L_n(i) ⊗ ℚ₂ = ℚ₂(ζ₁₂)`, and the classes of
`3 + 2√−d₀` agree, so one local unit of `L_n(i)` has Artin symbol `σ_{1+2ϖ}` on every `H_{d₀,4}`). -/
def SqrtTwoNotInHHprime : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∀ s ∈ HHprime n, s ^ 2 ≠ 2

/-! ## §2. The 2-primary part -/

theorem iPt_nsmul (m : ℕ) (P : PtA) : iPt (m • P) = m • iPt P :=
  map_nsmul iHom m P

theorem iPt_zero : iPt (0 : PtA) = 0 := rfl

/-- `y = negY x y` on `y² = x³ + 4x` forces `y = 0`. -/
theorem y_eq_zero_of_eq_negY {x y : Qbar} (h : y = curveAbar.toAffine.negY x y) : y = 0 := by
  simp only [negY, curveAbar_a₁, curveAbar_a₃, zero_mul, sub_zero] at h
  have : (2 : Qbar) * y = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h2 | h2
  · norm_num at h2
  · exact h2

/-- **The `A[4]` computation**: if `S ∈ A(K)`, `i ∈ K`, `4S = 0` and `2(S + [i]S) ≠ 0`, then `2` is a
square in `K`: `2S = (e, 0)` with `e² = −4`, `x = x(S)` satisfies `x² − 2ex + 4 = 0`, and
`(i(x − e)/2)² = 2`. -/
theorem sqrt_two_of_four_torsion {K : IntermediateField ℚ Qbar} (hi : iQ ∈ K) {S : PtA}
    (hS : S ∈ ptsOver K) (h4 : 4 • S = 0) (h : 2 • (S + iPt S) ≠ 0) : ∃ s ∈ K, s ^ 2 = 2 := by
  have hsplit : 2 • (S + iPt S) = 2 • S + iPt (2 • S) := by rw [nsmul_add, iPt_nsmul]
  have hT4 : 2 • (2 • S) = 0 := by rw [← mul_nsmul]; exact h4
  have hTmem : 2 • S ∈ ptsOver K := (ptsOver K).nsmul_mem hS 2
  -- `S = (x, y)`
  rcases hSdef : S with _ | ⟨x, y, hxy⟩
  · exfalso; apply h
    rw [hSdef]
    show 2 • ((0 : PtA) + iPt 0) = 0
    rw [iPt_zero, add_zero, nsmul_zero]
  have hxK : x ∈ K ∧ y ∈ K := by
    have := (mem_ptsOver_iff K S).mp hS; rw [hSdef] at this; exact this
  -- `y ≠ negY x y`, else `2S = 0`
  by_cases hy : y = curveAbar.toAffine.negY x y
  · exfalso; apply h
    rw [hsplit, hSdef, two_nsmul, Point.add_self_of_Y_eq hy, iPt_zero, add_zero]
  have h2S : 2 • S = Point.some _ _ (nonsingular_add hxy hxy fun hxy' => hy hxy'.right) := by
    rw [hSdef, two_nsmul, Point.add_self_of_Y_ne hy]
  rcases hTdef : 2 • S with _ | ⟨e, f, hef⟩
  · rw [hTdef] at h2S; exact absurd h2S.symm (Point.some_ne_zero _)
  rw [hTdef] at h2S hTmem hT4 hsplit
  obtain ⟨heq, -⟩ := Point.some.inj h2S
  have heK : e ∈ K := ((mem_ptsOver_iff K _).mp hTmem).1
  -- `2(2S) = 0` forces `f = 0`
  have hf0 : f = 0 := by
    apply y_eq_zero_of_eq_negY (x := e)
    by_contra hne
    rw [two_nsmul, Point.add_self_of_Y_ne hne] at hT4
    exact Point.some_ne_zero _ hT4
  subst hf0
  -- the curve equations
  have hTeq : e ^ 3 + 4 * e = 0 := by
    have := (equation_iff _ _).mp hef.1
    simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆] at this
    linear_combination -this
  have hSeq : y ^ 2 = x ^ 3 + 4 * x := by
    have := (equation_iff _ _).mp hxy.1
    simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆] at this
    linear_combination this
  -- `e ≠ 0`, else `2S = (0, 0) = [i](0, 0)` and `2(S + [i]S) = 2·(0,0) = 0`
  have he0 : e ≠ 0 := by
    rintro rfl
    apply h
    rw [hsplit, iPt_some]
    have hpt : (Point.some (-0) (iQ * 0) (nonsingular_iPt hef) : PtA) = Point.some 0 0 hef := by
      rw [Point.some.injEq]; exact ⟨neg_zero, mul_zero _⟩
    rw [hpt, ← two_nsmul, hT4]
  have he2 : e ^ 2 = -4 := by
    have : e * (e ^ 2 + 4) = 0 := by linear_combination hTeq
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 he0
    · linear_combination h0
  -- the doubling formula
  have hden : y - curveAbar.toAffine.negY x y ≠ 0 := sub_ne_zero.mpr hy
  have hneg : curveAbar.toAffine.negY x y = -y := by
    simp only [negY, curveAbar_a₁, curveAbar_a₃, zero_mul, sub_zero]
  have hslope : curveAbar.toAffine.slope x x y y * (y - curveAbar.toAffine.negY x y) =
      3 * x ^ 2 + 4 := by
    rw [slope_of_Y_ne rfl hy, div_mul_cancel₀ _ hden]
    simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₄]
    ring
  rw [hneg] at hslope
  have heq' : e = curveAbar.toAffine.slope x x y y ^ 2 - 2 * x := by
    rw [heq]; simp only [addX, curveAbar_a₁, curveAbar_a₂]; ring
  set L := curveAbar.toAffine.slope x x y y
  have hq : (x ^ 2 - 2 * e * x + 4) ^ 2 = 0 := by
    linear_combination (-(L * (y - -y) + 3 * x ^ 2 + 4)) * hslope - 4 * y ^ 2 * heq'
      + 4 * (e + 2 * x) * hSeq + 4 * x ^ 2 * he2
  have hq' : x ^ 2 - 2 * e * x + 4 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hq
  refine ⟨iQ * (x - e) / 2, ?_, ?_⟩
  · exact K.div_mem (K.mul_mem hi (K.sub_mem hxK.1 heK)) (ofNat_mem K 2)
  · linear_combination ((x - e) ^ 2 / 4) * iQ_sq - (1 / 4 : Qbar) * hq' - (1 / 4 : Qbar) * he2

/-- **The 2-primary part**: if `A(K)[4] ⊆ A[(1+i)³]` (and `i ∈ K`), every 2-power torsion point
of `A(K)` lies in `A[(1+i)³]`. Induction on the exponent: `Q = [1+i]²P = 2iP` has smaller
exponent, so `2[1+i]³P = 0`, i.e. `4[1+i]P = 0`; the hypothesis applied to `[1+i]P` gives `4P = 0`,
and then to `P`. -/
theorem two_power_part {K : IntermediateField ℚ Qbar} (hi : iQ ∈ K)
    (h4 : ∀ S ∈ ptsOver K, 4 • S = 0 → 2 • (S + iPt S) = 0) :
    ∀ a : ℕ, ∀ P ∈ ptsOver K, 2 ^ a • P = 0 → 2 • (P + iPt P) = 0 := by
  intro a
  induction a with
  | zero =>
    intro P hP hP0
    rw [pow_zero, one_nsmul] at hP0
    subst hP0; simp [iPt_zero]
  | succ a ih =>
    intro P hP hPa
    -- `Q = P + [i]P`, `Q + [i]Q = 2[i]P`
    have hQ : P + iPt P ∈ ptsOver K := (ptsOver K).add_mem hP (iPt_mem hi hP)
    have hQQ : (P + iPt P) + iPt (P + iPt P) = 2 • iPt P := by
      rw [iPt_add, iPt_iPt, two_nsmul]; abel
    have hiP : iPt P ∈ ptsOver K := iPt_mem hi hP
    have hR : 2 • iPt P ∈ ptsOver K := (ptsOver K).nsmul_mem hiP 2
    have hRa : 2 ^ a • (2 • iPt P) = 0 := by
      rw [← iPt_nsmul, ← iPt_nsmul, ← mul_nsmul', ← pow_succ, hPa, iPt_zero]
    have h1 := ih _ hR hRa
    -- `2(R + [i]R) = 4[i](P + [i]P)` ... rewrite into `4 • (P + iPt P) = 0`
    have h4Q : 4 • (P + iPt P) = 0 := by
      have e1 : 2 • (2 • iPt P + iPt (2 • iPt P)) = iPt (4 • (P + iPt P)) := by
        rw [iPt_nsmul, iPt_nsmul, iPt_add, iPt_iPt]; abel
      rw [e1] at h1
      have := congrArg iPt h1
      rw [iPt_iPt, iPt_zero, neg_eq_zero] at this
      exact this
    have h2Q := h4 _ hQ h4Q
    rw [hQQ] at h2Q
    -- `2 • (2 • iPt P) = 0` gives `4 • P = 0`
    have h4P : 4 • P = 0 := by
      have := congrArg iPt h2Q
      rw [iPt_nsmul, iPt_nsmul, iPt_iPt, iPt_zero] at this
      calc (4 : ℕ) • P = -((2 : ℕ) • (2 : ℕ) • -P) := by abel
        _ = 0 := by rw [this, neg_zero]
    exact h4 P hP h4P

/-! ## §3. `ℍ'_n` is a number field -/

theorem finiteDimensional_restrictScalars_Hprime (d : ℕ) [NeZero d] :
    FiniteDimensional ℚ ((Hprime d).restrictScalars ℚ) := by
  have : FiniteDimensional ℚ (Hprime d) := Module.Finite.trans (QNeg d) (Hprime d)
  exact inferInstanceAs (FiniteDimensional ℚ (Hprime d))

theorem finiteDimensional_map_Hprime (d : ℕ) [NeZero d] :
    FiniteDimensional ℚ (((Hprime d).restrictScalars ℚ).map (embed d)) :=
  haveI := finiteDimensional_restrictScalars_Hprime d
  LinearEquiv.finiteDimensional
    (IntermediateField.equivMap ((Hprime d).restrictScalars ℚ) (embed d)).toLinearEquiv

theorem Hprimebar_eq (d : ℕ) [NeZero d] :
    Hprimebar d = ((Hprime d).restrictScalars ℚ).map (embed d) := by
  rw [Hprimebar, dite_eq_right (NeZero.ne d)]

instance finiteDimensional_Hprimebar (d : ℕ) : FiniteDimensional ℚ (Hprimebar d) := by
  by_cases h : d = 0
  · subst h; rw [Hprimebar, dite_eq_left rfl]; infer_instance
  · haveI : NeZero d := ⟨h⟩
    rw [Hprimebar_eq]; exact finiteDimensional_map_Hprime d

theorem finiteDimensional_HHprime {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) :
    FiniteDimensional ℚ (HHprime n) := by
  haveI : NeZero n := ⟨by omega⟩
  rw [HHprime_eq_iSup hn hsq]; infer_instance

/-! ## §4. Residue fields inside `F_q` -/

/-- If `a^q ≡ a (mod u)` for all `a ∈ R`, every element `r` of the residue field of the valuation
ring of `u` satisfies `r^q = r`. -/
theorem residue_pow_eq_self {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (u : IsDedekindDomain.HeightOneSpectrum R) {q : ℕ} (hq : 0 < q)
    (h : ∀ a : R, a ^ q - a ∈ u.asIdeal)
    (r : IsLocalRing.ResidueField (u.valuation K).valuationSubring) : r ^ q = r := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  rw [← map_pow, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  obtain ⟨a, d, hd⟩ := u.exists_primeCompl_mul_eq_of_integer (K := K) (x : K) x.2
  have hdv : u.valuation K (algebraMap R K d) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem u).mpr d.2
  -- `d^{q-1} ≡ 1`
  have hd1 : (d : R) ^ m - 1 ∈ u.asIdeal := by
    have h1 : (d : R) * ((d : R) ^ m - 1) ∈ u.asIdeal := by
      have : (d : R) * ((d : R) ^ m - 1) = (d : R) ^ (m + 1) - d := by ring
      rw [this]; exact h d
    exact (u.isPrime.mem_or_mem h1).resolve_left d.2
  have hnum : a ^ (m + 1) - a * (d : R) ^ m ∈ u.asIdeal := by
    have : a ^ (m + 1) - a * (d : R) ^ m = (a ^ (m + 1) - a) - a * ((d : R) ^ m - 1) := by ring
    rw [this]
    exact u.asIdeal.sub_mem (h a) (u.asIdeal.mul_mem_left a hd1)
  have hkey : ((x : K) ^ (m + 1) - (x : K)) * algebraMap R K d ^ (m + 1) =
      algebraMap R K (a ^ (m + 1) - a * (d : R) ^ m) := by
    rw [map_sub, map_mul, map_pow, map_pow, ← hd]
    ring
  have hv := congrArg (u.valuation K) hkey
  rw [map_mul, map_pow, hdv, one_pow, mul_one] at hv
  rw [show ((x ^ (m + 1) - x : (u.valuation K).valuationSubring) : K) =
    (x : K) ^ (m + 1) - (x : K) by push_cast; rfl, hv]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) u _).mpr hnum

/-! ## §5. The auxiliary prime `p` (Dirichlet) -/

/-- A prime `p ≡ 3 (mod 8)` with `p ≡ 1 (mod m)`, for odd `m` (Dirichlet's theorem, Mathlib). -/
theorem exists_prime_three_mod_eight_one_mod {m : ℕ} (hm : Odd m) :
    ∃ p : ℕ, p.Prime ∧ p % 8 = 3 ∧ p % m = 1 % m := by
  have hco : Nat.Coprime 8 m := by
    have h2 : Nat.Coprime 2 m := Nat.coprime_two_left.mpr hm
    simpa using Nat.Coprime.pow_left 3 h2
  haveI : NeZero (8 * m) := ⟨by have := hm.pos; omega⟩
  obtain ⟨k, hk8, hkm⟩ := Nat.chineseRemainder hco 3 1
  have hku : IsUnit (k : ZMod (8 * m)) := by
    rw [ZMod.isUnit_iff_coprime]
    refine Nat.Coprime.mul_right ?_ ?_
    · have : Nat.gcd k 8 = Nat.gcd 3 8 := Nat.ModEq.gcd_eq hk8
      rw [Nat.Coprime, this]; rfl
    · have : Nat.gcd k m = Nat.gcd 1 m := Nat.ModEq.gcd_eq hkm
      rw [Nat.Coprime, this, Nat.gcd_one_left]
  obtain ⟨p, -, hp, hpk⟩ := Nat.forall_exists_prime_gt_and_eq_mod hku 0
  rw [ZMod.natCast_eq_natCast_iff] at hpk
  refine ⟨p, hp, ?_, ?_⟩
  · have := (Nat.ModEq.of_mul_right m hpk).trans hk8
    exact this
  · exact (Nat.ModEq.of_mul_left 8 hpk).trans hkm

/-- For `p ≡ 3 (mod 4)` with `p ≡ 1 (mod d₀)`, `d₀ ≡ 1 (mod 4)`: `(−d₀/p) = −1`. -/
theorem jacobiSym_neg_eq {p d₀ : ℕ} (hp4 : p % 4 = 3) (hd4 : d₀ % 4 = 1) (hpd : p % d₀ = 1) :
    jacobiSym (-(d₀ : ℤ)) p = -1 := by
  have hpodd : Odd p := Nat.odd_iff.mpr (by omega)
  have hdodd : Odd d₀ := Nat.odd_iff.mpr (by omega)
  rw [neg_eq_neg_one_mul, jacobiSym.mul_left, jacobiSym.at_neg_one hpodd,
    ZMod.χ₄_nat_three_mod_four hp4]
  have hd1 : 1 < d₀ := by
    rcases Nat.lt_or_ge 1 d₀ with h | h
    · exact h
    · interval_cases d₀
      · rw [Nat.mod_zero] at hpd; omega
      · rw [Nat.mod_one] at hpd; omega
  have hmod : ((p : ℤ) % (d₀ : ℤ)) = ((1 : ℕ) : ℤ) % (d₀ : ℤ) := by
    rw [← Int.natCast_mod, ← Int.natCast_mod, hpd, Nat.mod_eq_of_lt hd1]
  rw [jacobiSym.quadratic_reciprocity_one_mod_four hd4 hpodd, jacobiSym.mod_left' hmod,
    Nat.cast_one, jacobiSym.one_left]
  norm_num

/-! ## §6. The odd part: reduction at `p` -/

section OddPart

open IsDedekindDomain IsLocalRing WeierstrassCurve

variable {K : Type} [Field K] [NumberField K]

/-- The `u`-adic integral model of `A⁄K` (coefficients `0, 0, 0, 4, 0`). -/
theorem isIntegral_curveA (u : HeightOneSpectrum (𝓞 K)) :
    WeierstrassCurve.IsIntegral (u.valuation K).valuationSubring (curveA.baseChange K) := by
  have h4 : (u.valuation K) (algebraMap (𝓞 K) K 4) ≤ 1 := u.valuation_le_one _
  refine ⟨⟨⟨0, 0, 0, ⟨algebraMap (𝓞 K) K 4, h4⟩, 0⟩, ?_⟩⟩
  ext <;> simp [curveA, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  exact (map_ofNat (algebraMap (𝓞 K) K) 4).symm

/-- At a prime `u` not above `2`, the integral model of `A⁄K` has unit discriminant. -/
theorem isElliptic_integralModel (u : HeightOneSpectrum (𝓞 K)) (h2 : (2 : 𝓞 K) ∉ u.asIdeal) :
    letI := isIntegral_curveA u
    (integralModel (u.valuation K).valuationSubring (curveA.baseChange K)).IsElliptic := by
  letI := isIntegral_curveA u
  set v := u.valuation K
  have hΔ : algebraMap v.valuationSubring K
      (integralModel v.valuationSubring (curveA.baseChange K)).Δ =
      algebraMap ℚ K curveA.Δ := by
    have h := congrArg WeierstrassCurve.Δ
      (baseChange_integralModel_eq v.valuationSubring (curveA.baseChange K))
    simpa only [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ] using h
  have hcΔ : curveA.Δ = -4096 := by
    rw [curveA, ZInQ.shortCurve_Δ]; norm_num
  have hΔ1 : v (algebraMap ℚ K curveA.Δ) = 1 := by
    rw [hcΔ]
    have : algebraMap ℚ K (-4096) = algebraMap (𝓞 K) K (-(2 ^ 12)) := by
      simp only [map_neg, map_ofNat, map_pow]; norm_num
    rw [this, map_neg, Valuation.map_neg]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
    intro hmem
    exact h2 (u.isPrime.mem_of_pow_mem 12 hmem)
  refine ⟨?_⟩
  by_contra h
  have h1 := (Valuation.mem_maximalIdeal_iff (v := v)).mp ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have h2' : v ((integralModel v.valuationSubring (curveA.baseChange K)).Δ : K) = 1 := by
    rw [← hΔ1, ← hΔ]; rfl
  rw [h2'] at h1
  exact lt_irrefl _ h1

/-- The reduced curve is `y² = x³ + 4x` over the residue field. -/
theorem reduced_eq_shortCurve (u : HeightOneSpectrum (𝓞 K)) :
    letI := isIntegral_curveA u
    (integralModel (u.valuation K).valuationSubring (curveA.baseChange K)).map
      (residue (u.valuation K).valuationSubring) = ZInQ.shortCurve 4 := by
  letI := isIntegral_curveA u
  have e₁ := coe_integralModel_a₁ (W := (curveA.baseChange K).toAffine) (u.valuation K)
  have e₂ := coe_integralModel_a₂ (W := (curveA.baseChange K).toAffine) (u.valuation K)
  have e₃ := coe_integralModel_a₃ (W := (curveA.baseChange K).toAffine) (u.valuation K)
  have e₄ := coe_integralModel_a₄ (W := (curveA.baseChange K).toAffine) (u.valuation K)
  have e₆ := coe_integralModel_a₆ (W := (curveA.baseChange K).toAffine) (u.valuation K)
  have z₁ : (integralModel (u.valuation K).valuationSubring (curveA.baseChange K)).a₁ = 0 :=
    Subtype.ext (by rw [e₁]; simp [curveA, WeierstrassCurve.baseChange, WeierstrassCurve.map])
  have z₂ : (integralModel (u.valuation K).valuationSubring (curveA.baseChange K)).a₂ = 0 :=
    Subtype.ext (by rw [e₂]; simp [curveA, WeierstrassCurve.baseChange, WeierstrassCurve.map])
  have z₃ : (integralModel (u.valuation K).valuationSubring (curveA.baseChange K)).a₃ = 0 :=
    Subtype.ext (by rw [e₃]; simp [curveA, WeierstrassCurve.baseChange, WeierstrassCurve.map])
  have z₄ : (integralModel (u.valuation K).valuationSubring (curveA.baseChange K)).a₄ = 4 :=
    Subtype.ext (by
      rw [e₄]; simp [curveA, WeierstrassCurve.baseChange, WeierstrassCurve.map]
      exact (map_ofNat (algebraMap (u.valuation K).valuationSubring K) 4).symm)
  have z₆ : (integralModel (u.valuation K).valuationSubring (curveA.baseChange K)).a₆ = 0 :=
    Subtype.ext (by rw [e₆]; simp [curveA, WeierstrassCurve.baseChange, WeierstrassCurve.map])
  ext <;> simp [WeierstrassCurve.map, z₁, z₂, z₃, z₄, z₆]
  exact map_ofNat _ 4

end OddPart

open IsDedekindDomain IsLocalRing WeierstrassCurve in
/-- **The odd part**: for an odd prime `ℓ`, `A(ℍ'_n)[ℓ] = 0`. Reduce modulo a prime `𝔓` of `ℍ'_n` over
a prime `p ≡ 3 (mod 8)`, `p ≡ 1 (mod nℓ)`: the residue field lies in `F_{p²}` (G-Frob), its points
are killed by `p + 1` (leaf SS), `ℓ ∤ p + 1`, and reduction is injective on `ℓ`-torsion (Tau Ceti). -/
theorem odd_part (hSS : SupersingularExponentA) (hG : HHprimeFrobSq) {n : ℕ} (hn : n % 8 = 5)
    (hsq : Squarefree n) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {P : PtA}
    (hP : P ∈ ptsOver (HHprime n)) (hℓP : ℓ • P = 0) : P = 0 := by
  haveI : FiniteDimensional ℚ (HHprime n) := finiteDimensional_HHprime hn hsq
  haveI : NumberField (HHprime n) := ⟨⟩
  -- the auxiliary prime `p`
  have hn1 : 1 < n := by omega
  have hℓ3 : 2 < ℓ := lt_of_le_of_ne hℓ.two_le (Ne.symm hℓ2)
  have hmodd : Odd (n * ℓ) := Nat.odd_mul.mpr ⟨Nat.odd_iff.mpr (by omega), hℓ.odd_of_ne_two hℓ2⟩
  obtain ⟨p, hp, hp8, hpm⟩ := exists_prime_three_mod_eight_one_mod hmodd
  have hpn : p % n = 1 := by
    rw [← Nat.mod_mod_of_dvd p (dvd_mul_right n ℓ), hpm, Nat.mod_mod_of_dvd _ (dvd_mul_right n ℓ),
      Nat.mod_eq_of_lt hn1]
  have hpℓ : p % ℓ = 1 := by
    rw [← Nat.mod_mod_of_dvd p (dvd_mul_left ℓ n), hpm, Nat.mod_mod_of_dvd _ (dvd_mul_left ℓ n),
      Nat.mod_eq_of_lt hℓ.one_lt]
  have hp2 : p ≠ 2 := by omega
  have hpdvd : ¬ p ∣ n := by
    intro h
    have : p ∣ p % n := (Nat.dvd_mod_iff h).mpr dvd_rfl
    rw [hpn] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hpl : p ≠ ℓ := by rintro rfl; rw [Nat.mod_self] at hpℓ; exact zero_ne_one hpℓ
  have hjac : ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → jacobiSym (-(d₀ : ℤ)) p = -1 := by
    intro d₀ hd hd8
    have hdn : d₀ ∣ n := Nat.dvd_of_mem_divisors hd
    have hd1 : 1 < d₀ := by omega
    apply jacobiSym_neg_eq (by omega) (by omega)
    rw [← Nat.mod_mod_of_dvd p hdn, hpn, Nat.mod_eq_of_lt hd1]
  -- a prime `𝔓` of `𝓞_{ℍ'_n}` over `p`
  haveI hPp : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  have hker : RingHom.ker (algebraMap ℤ (𝓞 (HHprime n))) ≤ Ideal.span {(p : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 (HHprime n))).injective_int]
    exact bot_le
  obtain ⟨Q, hQ, hQu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain _ hker
  have hmemQ : ∀ m : ℕ, ((m : 𝓞 (HHprime n)) ∈ Q ↔ p ∣ m) := by
    intro m
    have : ((m : 𝓞 (HHprime n)) ∈ Q ↔ (m : ℤ) ∈ Q.under ℤ) := by
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    rw [this, hQu, Ideal.mem_span_singleton]
    exact_mod_cast Iff.rfl
  have hpQ : (p : 𝓞 (HHprime n)) ∈ Q := (hmemQ p).mpr dvd_rfl
  have hℓQ : (ℓ : 𝓞 (HHprime n)) ∉ Q := by
    rw [hmemQ]; intro h
    exact hpl ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h)
  have h2Q : (2 : 𝓞 (HHprime n)) ∉ Q := by
    have := hmemQ 2
    rw [Nat.cast_ofNat] at this
    rw [this]; intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hQne : Q ≠ ⊥ := by
    intro h; rw [h] at hpQ
    exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.mp hpQ))
  let u : HeightOneSpectrum (𝓞 (HHprime n)) := ⟨Q, hQ, hQne⟩
  -- the residue field
  set k := ResidueField (u.valuation (HHprime n)).valuationSubring
  have hk : ∀ r : k, r ^ (p ^ 2) = r :=
    residue_pow_eq_self (K := HHprime n) u (pow_pos hp.pos 2)
      (fun a => hG n hn hsq p hp hp2 hpdvd hjac Q hQ hpQ a)
  haveI : CharP k p := by
    rw [CharP.charP_iff_prime_eq_zero hp]
    have hv : (u.valuation (HHprime n)) (algebraMap (𝓞 (HHprime n)) (HHprime n) p) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := HHprime n) u _).mpr hpQ
    have : ((p : (u.valuation (HHprime n)).valuationSubring)) ∈
        maximalIdeal (u.valuation (HHprime n)).valuationSubring := by
      rw [Valuation.mem_maximalIdeal_iff]; push_cast; simpa using hv
    rw [← map_natCast (residue _), residue_eq_zero_iff]
    exact this
  haveI : DecidableEq k := Classical.decEq _
  letI := isIntegral_curveA u
  haveI := isElliptic_integralModel u h2Q
  -- the point over `ℍ'_n`
  obtain ⟨PK, rfl⟩ := hP
  have hℓPK : ℓ • PK = 0 := by
    apply Affine.Point.map_injective (W' := curveA) (f := (HHprime n).val)
    rw [map_nsmul, hℓP, map_zero]
  -- its reduction
  set R := Affine.Point.reductionHom (u.valuation (HHprime n)) PK
  have hℓR : ℓ • R = 0 := by rw [← map_nsmul, hℓPK, map_zero]
  have key : ∀ C : WeierstrassCurve k, C = ZInQ.shortCurve 4 →
      ∀ Q : C.toAffine.Point, (p + 1) • Q = 0 := by
    rintro C rfl
    exact hSS p hp (by omega) k hk
  have hpR : (p + 1) • R = 0 := key _ (reduced_eq_shortCurve u) R
  have hcop : Nat.Coprime ℓ (p + 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hℓ, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hpℓ,
      Nat.mod_eq_of_lt hℓ.one_lt, Nat.mod_eq_of_lt hℓ3]
    omega
  have hR0 : R = 0 := by
    rw [← AddMonoid.addOrderOf_eq_one_iff]
    have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hℓR) (addOrderOf_dvd_of_nsmul_eq_zero hpR)
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  have hPK0 : PK = 0 :=
    Affine.Point.eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero u
      (show ((ℓ : ℕ) : 𝓞 (HHprime n)) ∉ u.asIdeal from hℓQ) hR0 hℓPK
  rw [hPK0, map_zero]

/-- The weak supersingular exponent (statement of `T318SS.supersingularExponentWeak`, PROVED). -/
def SupersingularExponentWeak : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 3 →
    ∀ (k : Type) [Field k] [CharP k p] [DecidableEq k], (∀ r : k, r ^ (p ^ 2) = r) →
      (∃ ι : k, ι ^ 2 = -1) →
      ∀ P : (ZInQ.shortCurve (4 : k)).toAffine.Point, (2 * (p + 1)) • P = 0

theorem supersingularExponentWeak : SupersingularExponentWeak :=
  T318SS.supersingularExponentWeak

open IsDedekindDomain IsLocalRing WeierstrassCurve in
/-- **The odd part, with the proved weak exponent `2(p + 1)`**: for an odd prime `ℓ`, `A(ℍ'_n)[ℓ] = 0`. Reduce modulo a prime `𝔓` of `ℍ'_n` over
a prime `p ≡ 3 (mod 8)`, `p ≡ 1 (mod nℓ)`: the residue field lies in `F_{p²}` (G-Frob), its points
are killed by `p + 1` (leaf SS), `ℓ ∤ p + 1`, and reduction is injective on `ℓ`-torsion (Tau Ceti). -/
theorem odd_part_w (hSS : SupersingularExponentWeak) (hG : HHprimeFrobSq) {n : ℕ} (hn : n % 8 = 5)
    (hsq : Squarefree n) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) {P : PtA}
    (hP : P ∈ ptsOver (HHprime n)) (hℓP : ℓ • P = 0) : P = 0 := by
  haveI : FiniteDimensional ℚ (HHprime n) := finiteDimensional_HHprime hn hsq
  haveI : NumberField (HHprime n) := ⟨⟩
  -- the auxiliary prime `p`
  have hn1 : 1 < n := by omega
  have hℓ3 : 2 < ℓ := lt_of_le_of_ne hℓ.two_le (Ne.symm hℓ2)
  have hmodd : Odd (n * ℓ) := Nat.odd_mul.mpr ⟨Nat.odd_iff.mpr (by omega), hℓ.odd_of_ne_two hℓ2⟩
  obtain ⟨p, hp, hp8, hpm⟩ := exists_prime_three_mod_eight_one_mod hmodd
  have hpn : p % n = 1 := by
    rw [← Nat.mod_mod_of_dvd p (dvd_mul_right n ℓ), hpm, Nat.mod_mod_of_dvd _ (dvd_mul_right n ℓ),
      Nat.mod_eq_of_lt hn1]
  have hpℓ : p % ℓ = 1 := by
    rw [← Nat.mod_mod_of_dvd p (dvd_mul_left ℓ n), hpm, Nat.mod_mod_of_dvd _ (dvd_mul_left ℓ n),
      Nat.mod_eq_of_lt hℓ.one_lt]
  have hp2 : p ≠ 2 := by omega
  have hpdvd : ¬ p ∣ n := by
    intro h
    have : p ∣ p % n := (Nat.dvd_mod_iff h).mpr dvd_rfl
    rw [hpn] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hpl : p ≠ ℓ := by rintro rfl; rw [Nat.mod_self] at hpℓ; exact zero_ne_one hpℓ
  have hjac : ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → jacobiSym (-(d₀ : ℤ)) p = -1 := by
    intro d₀ hd hd8
    have hdn : d₀ ∣ n := Nat.dvd_of_mem_divisors hd
    have hd1 : 1 < d₀ := by omega
    apply jacobiSym_neg_eq (by omega) (by omega)
    rw [← Nat.mod_mod_of_dvd p hdn, hpn, Nat.mod_eq_of_lt hd1]
  -- a prime `𝔓` of `𝓞_{ℍ'_n}` over `p`
  haveI hPp : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  have hker : RingHom.ker (algebraMap ℤ (𝓞 (HHprime n))) ≤ Ideal.span {(p : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 (HHprime n))).injective_int]
    exact bot_le
  obtain ⟨Q, hQ, hQu⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain _ hker
  have hmemQ : ∀ m : ℕ, ((m : 𝓞 (HHprime n)) ∈ Q ↔ p ∣ m) := by
    intro m
    have : ((m : 𝓞 (HHprime n)) ∈ Q ↔ (m : ℤ) ∈ Q.under ℤ) := by
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    rw [this, hQu, Ideal.mem_span_singleton]
    exact_mod_cast Iff.rfl
  have hpQ : (p : 𝓞 (HHprime n)) ∈ Q := (hmemQ p).mpr dvd_rfl
  have hℓQ : (ℓ : 𝓞 (HHprime n)) ∉ Q := by
    rw [hmemQ]; intro h
    exact hpl ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp h)
  have h2Q : (2 : 𝓞 (HHprime n)) ∉ Q := by
    have := hmemQ 2
    rw [Nat.cast_ofNat] at this
    rw [this]; intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hQne : Q ≠ ⊥ := by
    intro h; rw [h] at hpQ
    exact hp.ne_zero (by exact_mod_cast (Ideal.mem_bot.mp hpQ))
  let u : HeightOneSpectrum (𝓞 (HHprime n)) := ⟨Q, hQ, hQne⟩
  -- the residue field
  set k := ResidueField (u.valuation (HHprime n)).valuationSubring
  have hk : ∀ r : k, r ^ (p ^ 2) = r :=
    residue_pow_eq_self (K := HHprime n) u (pow_pos hp.pos 2)
      (fun a => hG n hn hsq p hp hp2 hpdvd hjac Q hQ hpQ a)
  haveI : CharP k p := by
    rw [CharP.charP_iff_prime_eq_zero hp]
    have hv : (u.valuation (HHprime n)) (algebraMap (𝓞 (HHprime n)) (HHprime n) p) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := HHprime n) u _).mpr hpQ
    have : ((p : (u.valuation (HHprime n)).valuationSubring)) ∈
        maximalIdeal (u.valuation (HHprime n)).valuationSubring := by
      rw [Valuation.mem_maximalIdeal_iff]; push_cast; simpa using hv
    rw [← map_natCast (residue _), residue_eq_zero_iff]
    exact this
  haveI : DecidableEq k := Classical.decEq _
  letI := isIntegral_curveA u
  haveI := isElliptic_integralModel u h2Q
  -- the point over `ℍ'_n`
  obtain ⟨PK, rfl⟩ := hP
  have hℓPK : ℓ • PK = 0 := by
    apply Affine.Point.map_injective (W' := curveA) (f := (HHprime n).val)
    rw [map_nsmul, hℓP, map_zero]
  -- its reduction
  set R := Affine.Point.reductionHom (u.valuation (HHprime n)) PK
  have hℓR : ℓ • R = 0 := by rw [← map_nsmul, hℓPK, map_zero]
  -- `√−1` in the residue field: the residue of `iQ ∈ ℍ'_n`
  have hiK : iQ ∈ HHprime n := Package.iContained_HHprime n hn hsq
  set i0 : HHprime n := ⟨iQ, hiK⟩
  have hi0 : i0 ^ 2 = -1 := Subtype.ext (by simp [i0, iQ_sq])
  have hint : IsIntegral ℤ i0 :=
    ⟨Polynomial.X ^ 2 + Polynomial.C 1, Polynomial.monic_X_pow_add_C 1 two_ne_zero, by
      simp [hi0]⟩
  have hiv : (u.valuation (HHprime n)) i0 ≤ 1 :=
    u.valuation_le_one (K := HHprime n) (⟨i0, hint⟩ : 𝓞 (HHprime n))
  set ι : k := residue (u.valuation (HHprime n)).valuationSubring ⟨i0, hiv⟩
  have hι : ι ^ 2 = -1 := by
    show residue (u.valuation (HHprime n)).valuationSubring ⟨i0, hiv⟩ ^ 2 = -1
    rw [← map_pow, ← map_one (residue (u.valuation (HHprime n)).valuationSubring), ← map_neg]
    congr 1
    exact Subtype.ext (by simp [hi0])
  have key : ∀ C : WeierstrassCurve k, C = ZInQ.shortCurve 4 →
      ∀ Q : C.toAffine.Point, (2 * (p + 1)) • Q = 0 := by
    rintro C rfl
    exact hSS p hp (by omega) k hk ⟨ι, hι⟩
  have hpR : (2 * (p + 1)) • R = 0 := key _ (reduced_eq_shortCurve u) R
  have hcop1 : Nat.Coprime ℓ (p + 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hℓ, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, hpℓ,
      Nat.mod_eq_of_lt hℓ.one_lt, Nat.mod_eq_of_lt hℓ3]
    omega
  have hcop : Nat.Coprime ℓ (2 * (p + 1)) :=
    Nat.Coprime.mul_right ((Nat.coprime_primes hℓ Nat.prime_two).mpr hℓ2) hcop1
  have hR0 : R = 0 := by
    rw [← AddMonoid.addOrderOf_eq_one_iff]
    have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hℓR) (addOrderOf_dvd_of_nsmul_eq_zero hpR)
    rw [hcop.gcd_eq_one] at this
    exact Nat.dvd_one.mp this
  have hPK0 : PK = 0 :=
    Affine.Point.eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero u
      (show ((ℓ : ℕ) : 𝓞 (HHprime n)) ∉ u.asIdeal from hℓQ) hR0 hℓPK
  rw [hPK0, map_zero]

/-! ## §7. Assembly -/

/-- If no element of `G` has odd prime order, no element of `G` has odd order. -/
theorem eq_zero_of_odd_nsmul {G : AddSubgroup PtA}
    (hodd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∀ P ∈ G, ℓ • P = 0 → P = 0) :
    ∀ b : ℕ, Odd b → ∀ P ∈ G, b • P = 0 → P = 0 := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hb P hP hbP
    by_cases h1 : b = 1
    · subst h1; simpa using hbP
    obtain ⟨ℓ, hℓ, c, rfl⟩ := Nat.exists_prime_and_dvd h1
    have hc : Odd c := (Nat.odd_mul.mp hb).2
    have hℓ2 : ℓ ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr (Nat.odd_mul.mp hb).1) even_two
    have hcP : c • P ∈ G := G.nsmul_mem hP c
    have h1' : ℓ • (c • P) = 0 := by rw [← mul_nsmul', hbP]
    have hcP0 := hodd ℓ hℓ hℓ2 _ hcP h1'
    have hc0 : 0 < c := hc.pos
    exact ih c (lt_mul_left hc0 hℓ.one_lt) hc P hP hcP0

/-- **Main theorem**: TYZ Lemma `torsion2` (`Lemma318Literal HHprime`, verbatim) from the textbook
leaf `SupersingularExponentA` and the glue `HHprimeFrobSq`, `SqrtTwoNotInHHprime`. -/
theorem lemma318_at (hSS : SupersingularExponentA) (hG : HHprimeFrobSq) {n : ℕ} (hn : n % 8 = 5)
    (hsq : Squarefree n) (h2n : ∀ s ∈ HHprime n, s ^ 2 ≠ 2) :
    ∀ P ∈ ptsOver (HHprime n), IsOfFinAddOrder P → 2 • (P + iPt P) = 0 := by
  intro P hP hPt
  have hi : iQ ∈ HHprime n := Package.iContained_HHprime n hn hsq
  obtain ⟨m, hm, hmP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hPt
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  -- the odd part vanishes: `2^a • P = 0`
  have hQ : 2 ^ a • P = 0 := by
    refine eq_zero_of_odd_nsmul (G := ptsOver (HHprime n))
      (fun ℓ hℓ hℓ2 R hR hℓR => odd_part hSS hG hn hsq hℓ hℓ2 hR hℓR) b hb _
      ((ptsOver _).nsmul_mem hP _) ?_
    rw [← mul_nsmul', mul_comm]; exact hmP
  -- the 2-primary part
  refine two_power_part hi (fun S hS h4 => ?_) a P hP hQ
  by_contra hne
  obtain ⟨s, hs, hs2⟩ := sqrt_two_of_four_torsion hi hS h4 hne
  exact h2n s hs hs2

theorem lemma318Literal_HHprime_of (hSS : SupersingularExponentA) (hG : HHprimeFrobSq)
    (h2 : SqrtTwoNotInHHprime) : Lemma318Literal HHprime :=
  fun n hn hsq => lemma318_at hSS hG hn hsq (h2 n hn hsq)

/-- `lemma318_at` with the proved weak exponent `2(p + 1)` in place of the leaf. -/
theorem lemma318_at_w (hG : HHprimeFrobSq) {n : ℕ} (hn : n % 8 = 5)
    (hsq : Squarefree n) (h2n : ∀ s ∈ HHprime n, s ^ 2 ≠ 2) :
    ∀ P ∈ ptsOver (HHprime n), IsOfFinAddOrder P → 2 • (P + iPt P) = 0 := by
  intro P hP hPt
  have hi : iQ ∈ HHprime n := Package.iContained_HHprime n hn hsq
  obtain ⟨m, hm, hmP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hPt
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm.ne'
  have hQ : 2 ^ a • P = 0 := by
    refine eq_zero_of_odd_nsmul (G := ptsOver (HHprime n))
      (fun ℓ hℓ hℓ2 R hR hℓR => odd_part_w supersingularExponentWeak hG hn hsq hℓ hℓ2 hR hℓR)
      b hb _ ((ptsOver _).nsmul_mem hP _) ?_
    rw [← mul_nsmul', mul_comm]; exact hmP
  refine two_power_part hi (fun S hS h4 => ?_) a P hP hQ
  by_contra hne
  obtain ⟨s, hs, hs2⟩ := sqrt_two_of_four_torsion hi hS h4 hne
  exact h2n s hs hs2

/-- The same, for the kernel's `Package.Lemma318Literal` (the hypothesis `h318` of
`RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD` and of cm-bridge's final theorems). -/
theorem package_lemma318Literal_HHprime_of (hSS : SupersingularExponentA) (hG : HHprimeFrobSq)
    (h2 : SqrtTwoNotInHHprime) : Package.Lemma318Literal HHprime :=
  lemma318Literal_HHprime_of hSS hG h2

/-! ## §8. `HHprimeFrobSq` from one factor at a time

`HHprimeFrobSq` (residue fields of the compositum `ℍ'_n`) is reduced to `HprimeFrobOrderTwo`, a
statement about one ring class field `H'_d`: a Frobenius at `p` acts on `H'_d` with order `≤ 2`. The
compositum step is proved: take a Frobenius `σ ∈ Gal(ℍ'_n/ℚ)` at `𝔓` (Mathlib's
`IsArithFrobAt.exists_of_isInvariant`), lift it to `h ∈ Gal(ℚ̄/ℚ)`; `h²` fixes `L_n(i)` (every generator
`s` has `s² ∈ ℚ`, so `h(s) = ±s`) and every `H'_{d₀}` (`HprimeFrobOrderTwo`), hence `ℍ'_n`; so `σ² = 1`
and `a^{p²} ≡ σ²(a) = a (mod 𝔓)`. -/

/-- **G-Frob₁ (Frobenius at an inert prime has order `≤ 2` on `H'_d`); PROVED in §9
(`hprimeFrobOrderTwo`)**: for squarefree
`d ≡ 5 (mod 8)` and an odd prime `p ∤ d` inert in `K_d = ℚ(√−d)` (`(−d/p) = −1`), every
`h ∈ Gal(ℚ̄/ℚ)` that is an (arithmetic) Frobenius on `H'_d` at a prime `Q ∋ p` of `𝓞_{H'_d}`
(`h(a) ≡ a^p (mod Q)` for `a ∈ 𝓞_{H'_d}`) satisfies `h² = 1` on `H'_d`.

Proof sketch (formalized in §9): `p` is unramified in `H'_d` (`p ∤ 2d`), so `h|_{H'_d}`
is the Frobenius of `Q`, whose order is the residue degree `f(Q|p)`. `p𝓞_{K_d}` is prime (inert) and
generated by `p ∈ ℤ + 4𝓞_{K_d}`, prime to the conductor `4`, so its class in `Pic(ℤ + 4𝓞_{K_d})` is
trivial and it splits completely in `H_{d,4} ⊇ H'_d` (Tau Ceti `ringClassArtinEquiv`; ring-class's
splitting law `RingClass.mem_splitSet_iff`); hence `f(Q|p) = 2`. -/
def HprimeFrobOrderTwo : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ d →
    jacobiSym (-(d : ℤ)) p = -1 →
    ∀ (h : Qbar ≃ₐ[ℚ] Qbar) (Q : Ideal (𝓞 (Hprimebar d))), Q.IsPrime →
      (p : 𝓞 (Hprimebar d)) ∈ Q →
      (∀ a b : 𝓞 (Hprimebar d), ((b : Hprimebar d) : Qbar) =
        h ((a : Hprimebar d) : Qbar) - ((a : Hprimebar d) : Qbar) ^ p → b ∈ Q) →
      ∀ x ∈ Hprimebar d, h (h x) = x

theorem card_quot_span (p : ℕ) [Fact p.Prime] : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

/-- `h²` fixes every `s` with `s² ∈ ℚ`. -/
theorem sq_fix_of_sq_eq (h : Qbar ≃ₐ[ℚ] Qbar) {s : Qbar} (c : ℚ) (hs : s ^ 2 = algebraMap ℚ Qbar c) :
    h (h s) = s := by
  have h1 : (h s) ^ 2 = s ^ 2 := by rw [← map_pow, hs, AlgEquiv.commutes]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with e | e
  · rw [e, e]
  · rw [e, map_neg, e, neg_neg]

/-- **`HHprimeFrobSq` from `HprimeFrobOrderTwo`** (the compositum step, proved). -/
theorem hhprimeFrobSq_of (hF : HprimeFrobOrderTwo) : HHprimeFrobSq := by
  intro n hn hsq p hp hp2 hpn hjac 𝔓 h𝔓 hp𝔓 a
  haveI : FiniteDimensional ℚ (HHprime n) := finiteDimensional_HHprime hn hsq
  haveI : NumberField (HHprime n) := ⟨⟩
  haveI : Normal ℚ (HHprime n) := RingClassBridge.normalFields_HHprime' n hn hsq
  haveI : IsGalois ℚ (HHprime n) := ⟨⟩
  haveI : Fact p.Prime := ⟨hp⟩
  -- `𝔓` lies over `p`
  have hle : Ideal.span {(p : ℤ)} ≤ 𝔓.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap,
      map_natCast]
    exact hp𝔓
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp) |>.isMaximal (by simp [hp.ne_zero])
  have h𝔓p : 𝔓.under ℤ = Ideal.span {(p : ℤ)} :=
    (hmax.eq_of_le (Ideal.IsPrime.ne_top (Ideal.comap_isPrime _ _)) hle).symm
  have h𝔓ne : 𝔓 ≠ ⊥ := by
    intro h0; rw [h0, Ideal.mem_bot] at hp𝔓
    exact hp.ne_zero (by exact_mod_cast hp𝔓)
  haveI : 𝔓.IsMaximal := h𝔓.isMaximal h𝔓ne
  -- a Frobenius `σ` at `𝔓`, lifted to `h ∈ Gal(ℚ̄/ℚ)`
  let _ := IsIntegralClosure.MulSemiringAction ℤ ℚ (HHprime n) (𝓞 (HHprime n))
  have := Algebra.isInvariant_of_isGalois ℤ ℚ (HHprime n) (𝓞 (HHprime n))
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ ((HHprime n) ≃ₐ[ℚ] (HHprime n)) 𝔓
  obtain ⟨h, hres⟩ : ∃ h : Qbar ≃ₐ[ℚ] Qbar, AlgEquiv.restrictNormal h (HHprime n) = σ :=
    ⟨σ.liftNormal Qbar, σ.restrict_liftNormal Qbar⟩
  have hfrob : ∀ x : 𝓞 (HHprime n), σ • x - x ^ p ∈ 𝔓 := by
    intro x; have := hσ x; rwa [h𝔓p, card_quot_span] at this
  have hσx : ∀ x : 𝓞 (HHprime n),
      (((σ • x : 𝓞 (HHprime n)) : HHprime n) : Qbar) = h ((x : HHprime n) : Qbar) := by
    intro x
    change ((algebraMap (𝓞 (HHprime n)) (HHprime n)
      (galRestrict ℤ ℚ (HHprime n) (𝓞 (HHprime n)) σ x) : HHprime n) : Qbar) = _
    rw [algebraMap_galRestrict_apply, ← hres]
    exact (AlgEquiv.restrictNormal_commutes h (HHprime n) (algebraMap (𝓞 (HHprime n)) _ x))
  -- `h²` fixes `ℍ'_n`
  have hmemF : ∀ y, h (h y) = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers (h * h)) := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have hst : Subgroup.zpowers (h * h) ≤ MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) y := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, AlgEquiv.mul_apply]
      exact hy
    exact hst hg
  have hF' : HHprime n ≤ IntermediateField.fixedField (Subgroup.zpowers (h * h)) := by
    apply sup_le
    · rw [Lni, IntermediateField.adjoin_le_iff]
      rintro s (hs | ⟨q, -, hs⟩)
      · apply hmemF
        exact sq_fix_of_sq_eq h (-1) (by rw [hs]; simp)
      · apply hmemF
        exact sq_fix_of_sq_eq h q (by rw [hs]; simp)
    · apply iSup₂_le
      intro d₀ hd₀
      rw [Finset.mem_filter] at hd₀
      have hdn : d₀ ∣ n := Nat.dvd_of_mem_divisors hd₀.1
      have hle₀ : Hprimebar d₀ ≤ HHprime n :=
        le_sup_of_le_right (le_iSup₂_of_le (f := fun d _ => Hprimebar d) d₀
          (Finset.mem_filter.mpr hd₀) le_rfl)
      let ι : 𝓞 (Hprimebar d₀) →+* 𝓞 (HHprime n) :=
        RingOfIntegers.mapRingHom (IntermediateField.inclusion hle₀).toRingHom
      have hι : ∀ x : 𝓞 (Hprimebar d₀), (((ι x : 𝓞 (HHprime n)) : HHprime n) : Qbar) =
          ((x : Hprimebar d₀) : Qbar) := fun x => rfl
      intro y hy
      apply hmemF
      refine hF d₀ hd₀.2 (hsq.squarefree_of_dvd hdn) p hp hp2 (fun h' => hpn (h'.trans hdn))
        (hjac d₀ hd₀.1 hd₀.2) h (𝔓.comap ι) (Ideal.comap_isPrime _ _)
        (by rw [Ideal.mem_comap, map_natCast]; exact hp𝔓) ?_ y hy
      intro x b hb
      rw [Ideal.mem_comap]
      have key : ((ι b : HHprime n) : Qbar) =
          (((σ • ι x - ι x ^ p : 𝓞 (HHprime n)) : HHprime n) : Qbar) := by
        calc ((ι b : HHprime n) : Qbar) = ((b : Hprimebar d₀) : Qbar) := hι b
          _ = h ((x : Hprimebar d₀) : Qbar) - ((x : Hprimebar d₀) : Qbar) ^ p := hb
          _ = (((σ • ι x : 𝓞 (HHprime n)) : HHprime n) : Qbar) -
              (((ι x : 𝓞 (HHprime n)) : HHprime n) : Qbar) ^ p := by rw [hσx, hι]
          _ = (((σ • ι x - ι x ^ p : 𝓞 (HHprime n)) : HHprime n) : Qbar) := by push_cast; rfl
      have e : ι b = σ • ι x - ι x ^ p := RingOfIntegers.ext (Subtype.ext key)
      rw [e]
      exact hfrob (ι x)
  -- conclude: `σ² = 1` on `𝓞`, and `a^{p²} ≡ σ²(a) = a`
  have hσσ : σ • (σ • a) = a := by
    have hfa := hF' ((a : HHprime n)).2
    rw [IntermediateField.mem_fixedField_iff] at hfa
    have hfa' := hfa (h * h) (Subgroup.mem_zpowers _)
    rw [AlgEquiv.mul_apply] at hfa'
    have key : (((σ • (σ • a) : 𝓞 (HHprime n)) : HHprime n) : Qbar) = ((a : HHprime n) : Qbar) := by
      rw [hσx, hσx]; exact hfa'
    exact RingOfIntegers.ext (Subtype.ext key)
  have h1 := hfrob (σ • a)
  rw [hσσ] at h1
  have h2 : (σ • a) ^ p - (a ^ p) ^ p ∈ 𝔓 :=
    Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ p) (hfrob a)
  have h3 := 𝔓.add_mem h1 h2
  have : a ^ (p ^ 2) - a = -((a - (σ • a) ^ p) + ((σ • a) ^ p - (a ^ p) ^ p)) := by ring
  rw [this]
  exact 𝔓.neg_mem h3

/-- **Main theorem, finer form**: `Lemma318Literal HHprime` from the textbook leaf
`SupersingularExponentA` and the glue `HprimeFrobOrderTwo` (one ring class field at a time) and
`SqrtTwoNotInHHprime`. -/
theorem lemma318Literal_HHprime_of' (hSS : SupersingularExponentA) (hF : HprimeFrobOrderTwo)
    (h2 : SqrtTwoNotInHHprime) : Lemma318Literal HHprime :=
  lemma318Literal_HHprime_of hSS (hhprimeFrobSq_of hF) h2

/-! ## §9. `HprimeFrobOrderTwo`, proved (ring class field theory of one `H'_d`)

Step C (`hprime_inert_split`): above a prime `p` inert in `K_d`, `p ∤ 2d`, every prime `Q` of
`𝓞_{H'_d}` has residue field inside `F_{p²}` and trivial inertia group in `Gal(H'_d/K_d)`: `p𝓞_{K_d}`
(`prime_eq_span_of_inert`) has trivial class in `Pic(ℤ + 4𝓞_{K_d})` (generated by `p`), hence lies in
ring-class's `splitSet` of `H'_d` (`RingClass.mem_splitSet_iff`), and Mathlib's fundamental identity
`#primes · #inertia · f = |Gal|` forces `#inertia = f = 1`. Transport (`hprimeFrobOrderTwo_aux`): a
Frobenius `h` on `H̄'_d ⊂ ℚ̄` becomes, through `embed d`, a `ℚ`-automorphism `τ` of `H'_d` with
`τ(√−d) = ±√−d`; `τ²` lies in `Gal(H'_d/K_d)`, acts as `a ↦ a^{p²} ≡ a` modulo `Q`, so is in the
inertia group, hence `τ² = 1`. -/

section StepC
open TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory
  IsDedekindDomain
variable {d : ℕ} [NeZero d]

instance instFDHprime : FiniteDimensional (QNeg d) (Hprime d) := by
  rw [Hprime_eq_ringSubfield]; infer_instance
instance instGalHprime : IsGalois (QNeg d) (Hprime d) := by
  rw [Hprime_eq_ringSubfield]; infer_instance
instance instFDQHprime : FiniteDimensional ℚ (Hprime d) := Module.Finite.trans (QNeg d) (Hprime d)
instance instNFHprime : NumberField (Hprime d) := ⟨⟩

theorem absNorm_span_natCast (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 (QNeg d))}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have e : (p : 𝓞 (QNeg d)) = algebraMap ℤ (𝓞 (QNeg d)) (p : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap, RingOfIntegers.rank, QuadraticAlgebra.finrank_eq_two]
  simp

/-- A prime `𝔭` of `𝓞_{K_d}` containing an odd prime `p` with `(−d/p) = −1` is `p𝓞_{K_d}`. -/
theorem prime_eq_span_of_inert {p : ℕ} (hp : p.Prime) (hpd : ¬ p ∣ d)
    (hj : jacobiSym (-(d : ℤ)) p = -1) (𝔭 : Ideal (𝓞 (QNeg d))) [h𝔭 : 𝔭.IsPrime]
    (hp𝔭 : (p : 𝓞 (QNeg d)) ∈ 𝔭) : 𝔭 = Ideal.span {(p : 𝓞 (QNeg d))} := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : Ideal.span {(p : 𝓞 (QNeg d))} ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).2 hp𝔭
  have hnormp : Ideal.absNorm (Ideal.span {(p : 𝓞 (QNeg d))}) = p ^ 2 := absNorm_span_natCast p
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hmul : Ideal.absNorm 𝔭 * Ideal.absNorm J = p ^ 2 := by
    rw [← map_mul, ← hJ, hnormp]
  have hdvd : Ideal.absNorm 𝔭 ∣ p ^ 2 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime_pow hp).1 hdvd with ⟨k, hk, hk'⟩
  interval_cases k
  · exact absurd (Ideal.absNorm_eq_one_iff.1 (by simpa using hk')) h𝔭.ne_top
  · exfalso
    rw [pow_one] at hk'
    have h𝔭ne : 𝔭 ≠ ⊥ := by
      intro h0; rw [h0, Ideal.mem_bot] at hp𝔭
      exact hp.ne_zero (by exact_mod_cast hp𝔭)
    haveI : 𝔭.IsMaximal := h𝔭.isMaximal h𝔭ne
    letI := Ideal.Quotient.field 𝔭
    have hcard : Nat.card (𝓞 (QNeg d) ⧸ 𝔭) = p := by
      rw [← hk', ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    haveI : Finite (𝓞 (QNeg d) ⧸ 𝔭) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
    haveI : CharP (𝓞 (QNeg d) ⧸ 𝔭) p := by
      rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (Ideal.Quotient.mk 𝔭),
        Ideal.Quotient.eq_zero_iff_mem]
      exact hp𝔭
    let f : ZMod p →+* 𝓞 (QNeg d) ⧸ 𝔭 := ZMod.castHom (dvd_refl p) _
    have hinj : Function.Injective f := f.injective
    have hbij : Function.Bijective f := by
      refine (Function.Injective.bijective_of_nat_card_le hinj ?_)
      rw [hcard, Nat.card_zmod]
    obtain ⟨z, hz⟩ := hbij.2 (Ideal.Quotient.mk 𝔭 (sqrtNeg d))
    have hsq : z * z = ((-(d : ℤ) : ℤ) : ZMod p) := by
      apply hinj
      rw [map_mul, hz, ← map_mul, sqrtNeg_mul_self, map_intCast, map_neg, map_natCast]
      push_cast; rfl
    have ha0 : ((-(d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_neg]
      exact_mod_cast hpd
    have h1 : legendreSym p (-(d : ℤ)) = 1 := (legendreSym.eq_one_iff p ha0).2 ⟨z, hsq.symm⟩
    rw [jacobiSym.legendreSym.to_jacobiSym, hj] at h1
    norm_num at h1
  · have hJ1 : Ideal.absNorm J = 1 := by
      rw [hk'] at hmul
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith [hmul]
    rw [Ideal.absNorm_eq_one_iff] at hJ1
    rw [hJ, hJ1, Ideal.mul_top]

/-- **Step C (ring class field theory, proved)**: let `p` be an odd prime, `p ∤ d`, inert in `K_d`, and
`Q` a prime of `𝓞_{H'_d}` containing `p`. Then `𝓞/Q ⊆ F_{p²}` and the inertia group of `Q` in
`Gal(H'_d/K_d)` is trivial: `p𝓞_{K_d}` has trivial class in `Pic(ℤ + 4𝓞_{K_d})`, so it splits completely
in `H'_d` (ring-class's `mem_splitSet_iff`), and the fundamental identity
`#primes · #inertia · f = [H'_d : K_d]` forces `#inertia = f = 1`. -/
theorem hprime_inert_split (_hd : d % 8 = 5) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d)
    (hj : jacobiSym (-(d : ℤ)) p = -1) (Q : Ideal (𝓞 (Hprime d))) [hQ : Q.IsPrime]
    (hpQ : (p : 𝓞 (Hprime d)) ∈ Q) :
    (∀ a : 𝓞 (Hprime d), a ^ (p ^ 2) - a ∈ Q) ∧
    (∀ τ : Gal(Hprime d / QNeg d), (∀ a : 𝓞 (Hprime d), τ • a - a ∈ Q) → τ = 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set 𝔭 : Ideal (𝓞 (QNeg d)) := Q.under (𝓞 (QNeg d)) with h𝔭def
  have hp𝔭 : (p : 𝓞 (QNeg d)) ∈ 𝔭 := by
    rw [h𝔭def, Ideal.under_def, Ideal.mem_comap, map_natCast]; exact hpQ
  have h𝔭eq : 𝔭 = Ideal.span {(p : 𝓞 (QNeg d))} := prime_eq_span_of_inert hp hpd hj 𝔭 hp𝔭
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    intro h0; rw [h0, Ideal.mem_bot] at hp𝔭
    exact hp.ne_zero (by exact_mod_cast hp𝔭)
  haveI h𝔭max : 𝔭.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔭ne
  -- `2 ∉ 𝔭`
  have h2 : (2 : 𝓞 (QNeg d)) ∉ 𝔭 := by
    intro h2
    have hco : IsCoprime (2 : ℤ) (p : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
      exact_mod_cast this
    obtain ⟨u, v, huv⟩ := hco
    have h1 : ((u * 2 + v * p : ℤ) : 𝓞 (QNeg d)) ∈ 𝔭 := by
      push_cast
      exact 𝔭.add_mem (𝔭.mul_mem_left _ h2) (𝔭.mul_mem_left _ hp𝔭)
    rw [huv, Int.cast_one] at h1
    exact h𝔭max.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  -- `𝔭` is prime to the conductor of `ℤ + 4𝓞_K`
  let 𝔭' : HeightOneSpectrum (𝓞 (QNeg d)) := ⟨𝔭, inferInstance, h𝔭ne⟩
  have hT : ¬ (O4 d).conductor ≤ 𝔭'.asIdeal := by
    intro hle
    have h4 : ((4 : ℕ) : 𝓞 (QNeg d)) * 1 ∈ 𝔭 := hle (natCast_mul_mem_conductor (QNeg d) 4 1)
    rw [mul_one, show ((4 : ℕ) : 𝓞 (QNeg d)) = 2 * 2 by norm_num] at h4
    exact h2 ((Ideal.IsPrime.mem_or_mem inferInstance h4).elim id id)
  have hJ := mem_primeTo_of_not_le 𝔭' hT
  haveI : ((⟨𝔭'.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := h𝔭max
  have hc : (O4 d).picClass ⟨𝔭'.asIdeal, hJ⟩ = 1 := by
    rw [picClass_eq_one_iff]
    exact ⟨(p : 𝓞 (QNeg d)), natCast_mem _ p, h𝔭eq⟩
  have hsplit : 𝔭' ∈ splitSet (QNeg d) (Hprime d) := by
    rw [Hprime_eq_ringSubfield]
    exact (mem_splitSet_iff (O4 d) _ ⟨_, hJ⟩ 𝔭' rfl).2 (hc ▸ Subgroup.one_mem _)
  have hsplit' : (𝔭.primesOver (𝓞 (Hprime d))).ncard = Module.finrank (QNeg d) (Hprime d) :=
    hsplit
  -- the fundamental identity
  have hfund := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank
    (G := Gal(Hprime d / QNeg d)) 𝔭 Q
  rw [hsplit', IsGalois.card_aut_eq_finrank, mul_assoc] at hfund
  have hpos : 0 < Module.finrank (QNeg d) (Hprime d) := Module.finrank_pos
  have h1 : Nat.card (Q.inertia Gal(Hprime d / QNeg d)) * Q.inertiaDeg (𝓞 (QNeg d)) = 1 := by
    have := hfund
    nth_rewrite 2 [← mul_one (Module.finrank (QNeg d) (Hprime d))] at this
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hI : Nat.card (Q.inertia Gal(Hprime d / QNeg d)) = 1 := Nat.eq_one_of_mul_eq_one_right h1
  have hf : Q.inertiaDeg (𝓞 (QNeg d)) = 1 := Nat.eq_one_of_mul_eq_one_left h1
  refine ⟨?_, ?_⟩
  · have hQne : Q ≠ ⊥ := by
      intro h0; rw [h0, Ideal.mem_bot] at hpQ
      exact hp.ne_zero (by exact_mod_cast hpQ)
    haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQne
    have hcardQ : Nat.card (𝓞 (Hprime d) ⧸ Q) = p ^ 2 := by
      have h := Ideal.absNorm_pow_inertiaDeg 𝔭 Q
      rw [hf, pow_one, h𝔭eq, absNorm_span_natCast] at h
      rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← h]
    letI := Ideal.Quotient.field Q
    haveI : Finite (𝓞 (Hprime d) ⧸ Q) :=
      Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact pow_ne_zero 2 hp.ne_zero)
    letI := Fintype.ofFinite (𝓞 (Hprime d) ⧸ Q)
    intro a
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero, ← hcardQ,
      Nat.card_eq_fintype_card, FiniteField.pow_card]
  · intro τ hτ
    have hmem : τ ∈ Q.inertia Gal(Hprime d / QNeg d) := hτ
    have hbot := Subgroup.eq_bot_of_card_eq _ hI
    rw [hbot] at hmem
    exact hmem

/-! ### Transport to `ℚ̄`: `HprimeFrobOrderTwo` -/

/-- `H'_d ≅ H̄'_d ⊂ ℚ̄` (as `ℚ`-algebras), through `embed d`. -/
noncomputable def psi0 (d : ℕ) [NeZero d] : ((Hprime d).restrictScalars ℚ) ≃ₐ[ℚ] Hprimebar d :=
  (IntermediateField.equivMap ((Hprime d).restrictScalars ℚ) (embed d)).trans
    (IntermediateField.equivOfEq (Hprimebar_eq d).symm)

theorem psi0_apply (y : (Hprime d).restrictScalars ℚ) :
    ((psi0 d y : Hprimebar d) : Qbar) = embed d (y : SeparableClosure (QNeg d)) := rfl

instance instNormalHprimebar : Normal ℚ (Hprimebar d) := normal_Hprimebar d

/-- `h ∈ Gal(ℚ̄/ℚ)` transported to a `ℚ`-automorphism of `H'_d`. -/
noncomputable def tauQ (h : Qbar ≃ₐ[ℚ] Qbar) :
    ((Hprime d).restrictScalars ℚ) ≃ₐ[ℚ] ((Hprime d).restrictScalars ℚ) :=
  ((psi0 d).trans (h.restrictNormal (Hprimebar d))).trans (psi0 d).symm

theorem psi0_tauQ (h : Qbar ≃ₐ[ℚ] Qbar) (y : (Hprime d).restrictScalars ℚ) :
    ((psi0 d (tauQ (d := d) h y) : Hprimebar d) : Qbar) = h ((psi0 d y : Hprimebar d) : Qbar) := by
  simp only [tauQ, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  exact AlgEquiv.restrictNormal_commutes h (Hprimebar d) (psi0 d y)

/-- The image of `c ∈ K_d` in `H'_d`, as an element of `H'_d` viewed over `ℚ`. -/
noncomputable def kpt (c : QNeg d) : (Hprime d).restrictScalars ℚ :=
  ⟨algebraMap (QNeg d) (SeparableClosure (QNeg d)) c, (Hprime d).algebraMap_mem c⟩

theorem kpt_eq (c : QNeg d) :
    kpt c = algebraMap ℚ ((Hprime d).restrictScalars ℚ) c.re +
      algebraMap ℚ ((Hprime d).restrictScalars ℚ) c.im * kpt (QuadraticAlgebra.omega : QNeg d) := by
  have hc : c = algebraMap ℚ (QNeg d) c.re + algebraMap ℚ (QNeg d) c.im * QuadraticAlgebra.omega := by
    ext <;> simp
  apply Subtype.ext
  show algebraMap (QNeg d) (SeparableClosure (QNeg d)) c = _
  conv_lhs => rw [hc]
  rw [map_add, map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rfl

/-- The square of `tauQ h` fixes `K_d`. -/
theorem tauQ_sq_kpt (h : Qbar ≃ₐ[ℚ] Qbar) (c : QNeg d) :
    tauQ (d := d) h (tauQ (d := d) h (kpt c)) = kpt c := by
  set τ := tauQ (d := d) h
  set w := kpt (QuadraticAlgebra.omega : QNeg d)
  have hw2 : w * w = algebraMap ℚ ((Hprime d).restrictScalars ℚ) (-(d : ℚ)) := by
    apply Subtype.ext
    show algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega *
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega = _
    rw [← map_mul, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_add, map_mul,
      ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    simp only [map_zero, zero_mul, add_zero]
    rfl
  have hτw : τ w * τ w = w * w := by rw [← map_mul, hw2, AlgEquiv.commutes]
  have hττw : τ (τ w) = w := by
    rcases mul_self_eq_mul_self_iff.mp hτw with e | e
    · rw [e, e]
    · rw [e, map_neg, e, neg_neg]
  rw [kpt_eq, map_add, map_add, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes,
    AlgEquiv.commutes, AlgEquiv.commutes, hττw]

/-- `(tauQ h)²` as an element of `Gal(H'_d/K_d)`. -/
noncomputable def tau2 (h : Qbar ≃ₐ[ℚ] Qbar) : Gal(Hprime d / QNeg d) :=
  AlgEquiv.ofRingEquiv (f := (tauQ (d := d) h * tauQ (d := d) h).toRingEquiv) (fun c => by
    show tauQ (d := d) h (tauQ (d := d) h (kpt c)) = kpt c
    exact tauQ_sq_kpt h c)

theorem coe_tau2 (h : Qbar ≃ₐ[ℚ] Qbar) (y : Hprime d) :
    ((tau2 h y : Hprime d) : SeparableClosure (QNeg d)) =
      ((tauQ (d := d) h (tauQ (d := d) h y) : (Hprime d).restrictScalars ℚ) :
        SeparableClosure (QNeg d)) := rfl

/-- **`HprimeFrobOrderTwo` for one `d`** (proved from Step C by transport through `embed d`). -/
theorem hprimeFrobOrderTwo_aux (hd : d % 8 = 5) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ d) (hj : jacobiSym (-(d : ℤ)) p = -1) (h : Qbar ≃ₐ[ℚ] Qbar)
    (Q : Ideal (𝓞 (Hprimebar d))) [Q.IsPrime] (hpQ : (p : 𝓞 (Hprimebar d)) ∈ Q)
    (hfrob : ∀ a b : 𝓞 (Hprimebar d), ((b : Hprimebar d) : Qbar) =
      h ((a : Hprimebar d) : Qbar) - ((a : Hprimebar d) : Qbar) ^ p → b ∈ Q) :
    ∀ x ∈ Hprimebar d, h (h x) = x := by
  let ι0 : (Hprime d) →+* (Hprimebar d) := (psi0 d).toRingHom
  let ψ : 𝓞 (Hprime d) →+* 𝓞 (Hprimebar d) := RingOfIntegers.mapRingHom ι0
  let τ0 : (Hprime d) →+* (Hprime d) := (tauQ (d := d) h).toRingHom
  let τO : 𝓞 (Hprime d) →+* 𝓞 (Hprime d) := RingOfIntegers.mapRingHom τ0
  have hψτ : ∀ b : 𝓞 (Hprime d), ((ψ (τO b) : Hprimebar d) : Qbar) =
      h ((ψ b : Hprimebar d) : Qbar) := fun b => psi0_tauQ h (b : Hprime d)
  set Q' := Q.comap ψ with hQ'
  haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hpQ' : (p : 𝓞 (Hprime d)) ∈ Q' := by rw [hQ', Ideal.mem_comap, map_natCast]; exact hpQ
  have hfr : ∀ a : 𝓞 (Hprime d), τO a - a ^ p ∈ Q' := by
    intro a
    rw [hQ', Ideal.mem_comap]
    apply hfrob (ψ a) (ψ (τO a - a ^ p))
    rw [map_sub, map_pow]
    push_cast
    rw [hψτ]
  obtain ⟨hres, hin⟩ := hprime_inert_split hd hp hp2 hpd hj Q' hpQ'
  have hsmul : ∀ a : 𝓞 (Hprime d), (tau2 (d := d) h) • a = τO (τO a) := fun a => rfl
  have htau2 : tau2 (d := d) h = 1 := by
    apply hin
    intro a
    rw [hsmul]
    have h1 := hfr (τO a)
    have h2 : (τO a) ^ p - (a ^ p) ^ p ∈ Q' := Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ p) (hfr a)
    have h3 := hres a
    have e : τO (τO a) - a = (τO (τO a) - τO a ^ p) + ((τO a) ^ p - (a ^ p) ^ p) +
        (a ^ (p ^ 2) - a) := by ring
    rw [e]
    exact Q'.add_mem (Q'.add_mem h1 h2) h3
  intro x hx
  set y := (psi0 d).symm ⟨x, hx⟩ with hy
  have hxy : x = ((psi0 d y : Hprimebar d) : Qbar) := by rw [hy, AlgEquiv.apply_symm_apply]
  rw [hxy, ← psi0_tauQ, ← psi0_tauQ]
  have hyy : tauQ (d := d) h (tauQ (d := d) h y) = y := by
    apply Subtype.ext
    have := coe_tau2 h y
    rw [htau2] at this
    exact this.symm
  rw [hyy]

end StepC

/-- **`√2 ∉ ℍ'_n` when `n` is the only divisor `d₀ ≡ 5 (mod 8)` of `n`** (e.g. `n` prime, or `n = 21`):
then `ℍ'_n = H'_n` (`Lni_le_Hprimebar`) and ring-class's `not_adjSqrt_two_le_Hprime` applies after
transport through `embed n`. The general case (several `H'_{d₀}`) is the open glue
`SqrtTwoNotInHHprime`. -/
theorem sqrtTwo_not_mem_HHprime_of_single {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n)
    (h1 : ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → d₀ = n) : ∀ s ∈ HHprime n, s ^ 2 ≠ 2 := by
  haveI : NeZero n := ⟨by omega⟩
  have hle : HHprime n ≤ Hprimebar n := by
    apply sup_le (Lni_le_Hprimebar (by omega) hsq)
    apply iSup₂_le
    intro d₀ hd₀
    rw [Finset.mem_filter] at hd₀
    rw [h1 d₀ hd₀.1 hd₀.2]
  intro s hs hs2
  set y := (psi0 n).symm ⟨s, hle hs⟩ with hy
  have hsy : s = embed n (y : SeparableClosure (QNeg n)) := by
    rw [← psi0_apply, hy, AlgEquiv.apply_symm_apply]
  have hy2 : (y : SeparableClosure (QNeg n)) ^ 2 = 2 := by
    have e1 : embed n ((y : SeparableClosure (QNeg n)) ^ 2) = s ^ 2 := by rw [map_pow, ← hsy]
    have e2 : embed n ((y : SeparableClosure (QNeg n)) ^ 2) = embed n 2 := by
      rw [e1, hs2, map_ofNat]
    exact (embed n).injective e2
  have hymem : (y : SeparableClosure (QNeg n)) ∈ Hprime n := y.2
  have hsq2 : sqrtK (QNeg n) 2 ^ 2 = (y : SeparableClosure (QNeg n)) ^ 2 := by
    rw [sqrtK_sq, hy2]; norm_num
  have hmem : sqrtK (QNeg n) 2 ∈ Hprime n := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq2 with e | e
    · rw [e]; exact hymem
    · rw [e]; exact (Hprime n).neg_mem hymem
  exact not_adjSqrt_two_le_Hprime hn (IntermediateField.adjoin_simple_le_iff.mpr hmem)

/-- **A common lift of the `σ_{1+2ϖ}`** (the class-field-theoretic content of `√2 ∉ ℍ'_n`, Route A/B of
`docs/research/tyz-318.md` §3.2): some `h ∈ Gal(ℚ̄/ℚ)` fixes `L_n(i)` pointwise and acts on every
`H̄_{d₀,4} = embed d₀ (H_{d₀,4})`, `d₀ ∣ n`, `d₀ ≡ 5 (mod 8)`, as the Artin symbol `σ_{1+2ϖ}` of
`Pic(ℤ + 4𝓞_{K_{d₀}})`. Not proved here. This is STRONGER than `SqrtTwoNotInHHprime`
(`sqrtTwoNotInHHprime_of_sigmaLift`); it is the form in which class field theory supplies it (Route A:
`h` is a Frobenius at a prime of `L_n(i)` in the class of `α = 1 + 2i∏(1+√q*)/2`). -/
def SigmaLift : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ h : Qbar ≃ₐ[ℚ] Qbar, (∀ x ∈ Lni n, h x = x) ∧
    ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → ∀ _ : NeZero d₀, ∀ y : H4 d₀,
      h (embed d₀ (y : SeparableClosure (QNeg d₀))) =
        embed d₀ ((artin4 d₀ (sigmaClass d₀) y : H4 d₀) : SeparableClosure (QNeg d₀))

/-- `σ_{1+2ϖ}` moves `√2` (`√2 ∈ H_{d,4}`, `√2 ∉ H'_d = H_{d,4}^{σ}`). -/
theorem sigma_moves_sqrtTwo {d : ℕ} [NeZero d] (hd : d % 8 = 5) :
    ((artin4 d (sigmaClass d) ⟨sqrtK (QNeg d) 2,
        adjSqrt_two_le_H4 (by omega) (IntermediateField.mem_adjoin_simple_self _ _)⟩ : H4 d) :
      SeparableClosure (QNeg d)) = -sqrtK (QNeg d) 2 := by
  set σ := artin4 d (sigmaClass d)
  set w : H4 d := ⟨sqrtK (QNeg d) 2,
    adjSqrt_two_le_H4 (by omega) (IntermediateField.mem_adjoin_simple_self _ _)⟩
  have hw2 : w * w = 2 := by
    apply Subtype.ext
    show sqrtK (QNeg d) 2 * sqrtK (QNeg d) 2 = 2
    rw [← sq, sqrtK_sq]; norm_num
  have hσw : σ w * σ w = w * w := by rw [← map_mul, hw2, map_ofNat]
  rcases mul_self_eq_mul_self_iff.mp hσw with e | e
  · exfalso
    apply not_adjSqrt_two_le_Hprime hd
    rw [IntermediateField.adjoin_simple_le_iff]
    show ((w : H4 d) : SeparableClosure (QNeg d)) ∈ Hprime d
    rw [Hprime, IntermediateField.mem_lift, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer _ w := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact e
    exact hst hg
  · rw [e]; rfl

/-- **`SqrtTwoNotInHHprime` from `SigmaLift`** (Route A, steps 5–7, proved). -/
theorem sqrtTwoNotInHHprime_of_sigmaLift (hL : SigmaLift) : SqrtTwoNotInHHprime := by
  intro n hn hsq s hs hs2
  obtain ⟨h, hLni, hH⟩ := hL n hn hsq
  haveI : NeZero n := ⟨by omega⟩
  have hnD : n ∈ n.divisors := Nat.mem_divisors_self n (by omega)
  -- `h` fixes every `H̄'_{d₀}`
  have hfixH : ∀ d₀ ∈ n.divisors.filter (fun d => d % 8 = 5), ∀ x ∈ Hprimebar d₀, h x = x := by
    intro d₀ hd₀ x hx
    rw [Finset.mem_filter] at hd₀
    haveI : NeZero d₀ := ⟨by omega⟩
    rw [Hprimebar_eq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : y ∈ Hprime d₀ := hy
    have hyH4 : y ∈ H4 d₀ := Hprime_le_H4 d₀ hy'
    have hz := (IntermediateField.mem_lift (⟨y, hyH4⟩ : H4 d₀)).mp hy'
    rw [IntermediateField.mem_fixedField_iff] at hz
    have hσz := hz (artin4 d₀ (sigmaClass d₀)) (Subgroup.mem_zpowers _)
    have e : ((artin4 d₀ (sigmaClass d₀) ⟨y, hyH4⟩ : H4 d₀) : SeparableClosure (QNeg d₀)) = y :=
      congrArg Subtype.val hσz
    have key := hH d₀ hd₀.1 hd₀.2 ‹NeZero d₀› ⟨y, hyH4⟩
    have k2 := key.trans (congrArg (embed d₀) e)
    exact k2
  -- `h` fixes `ℍ'_n`
  have hmemF : ∀ y, h y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers h) := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have hst : Subgroup.zpowers h ≤ MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) y := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hy
    exact hst hg
  have hF : HHprime n ≤ IntermediateField.fixedField (Subgroup.zpowers h) := by
    apply sup_le
    · intro x hx; exact hmemF x (hLni x hx)
    · apply iSup₂_le
      intro d₀ hd₀ x hx
      exact hmemF x (hfixH d₀ hd₀ x hx)
  have hhs : h s = s := by
    have := hF hs
    rw [IntermediateField.mem_fixedField_iff] at this
    exact this h (Subgroup.mem_zpowers _)
  -- `h` moves `√2`
  set w : H4 n := ⟨sqrtK (QNeg n) 2,
    adjSqrt_two_le_H4 (by omega) (IntermediateField.mem_adjoin_simple_self _ _)⟩ with hw
  have hmove : h (embed n (w : SeparableClosure (QNeg n))) = -embed n (w : SeparableClosure (QNeg n)) := by
    rw [hH n (Nat.mem_divisors_self n (by omega)) hn inferInstance w, hw, sigma_moves_sqrtTwo hn,
      map_neg]
  have hw2 : (embed n (w : SeparableClosure (QNeg n))) ^ 2 = 2 := by
    rw [← map_pow, hw]
    show embed n (sqrtK (QNeg n) 2 ^ 2) = 2
    rw [sqrtK_sq]; simp only [Int.cast_ofNat]; exact map_ofNat (embed n) 2
  have hsw : s ^ 2 = (embed n (w : SeparableClosure (QNeg n))) ^ 2 := by rw [hs2, hw2]
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsw with e | e
  · rw [e, hmove] at hhs
    exact hs0 (by rw [e]; linear_combination hhs.symm / 2)
  · rw [e, map_neg, hmove, neg_neg] at hhs
    exact hs0 (by rw [e]; linear_combination -hhs / 2)

/-- **`HprimeFrobOrderTwo` holds** (no hypotheses). -/
theorem hprimeFrobOrderTwo : HprimeFrobOrderTwo := by
  intro d hd _hsq p hp hp2 hpd hj h Q hQ hpQ hfrob
  haveI : NeZero d := ⟨by omega⟩
  exact hprimeFrobOrderTwo_aux hd hp hp2 hpd hj h Q hpQ hfrob

/-- **`HHprimeFrobSq` holds** (no hypotheses). -/
theorem hhprimeFrobSq : HHprimeFrobSq := hhprimeFrobSq_of hprimeFrobOrderTwo

/-- **Main theorem, final form**: TYZ Lemma `torsion2` (`Lemma318Literal HHprime`, verbatim) from the
textbook leaf `SupersingularExponentA` (supersingular reduction of `y² = x³ + 4x`) and the glue
`SqrtTwoNotInHHprime` (`√2 ∉ ℍ'_n`, TYZ's Step 3). -/
theorem lemma318Literal_HHprime_of_ss_sqrtTwo (hSS : SupersingularExponentA)
    (h2 : SqrtTwoNotInHHprime) : Lemma318Literal HHprime :=
  lemma318Literal_HHprime_of hSS hhprimeFrobSq h2

/-- **TYZ Lemma `torsion2` unconditionally on the glue when `n` is the only divisor `d₀ ≡ 5 (mod 8)`
of `n`** (e.g. `n` prime): only the textbook leaf `SupersingularExponentA` is used. -/
theorem lemma318_at_single (hSS : SupersingularExponentA) {n : ℕ} (hn : n % 8 = 5)
    (hsq : Squarefree n) (h1 : ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → d₀ = n) :
    ∀ P ∈ ptsOver (HHprime n), IsOfFinAddOrder P → 2 • (P + iPt P) = 0 :=
  lemma318_at hSS hhprimeFrobSq hn hsq (sqrtTwo_not_mem_HHprime_of_single hn hsq h1)

/-- The same for the kernel's `Package.Lemma318Literal`. -/
theorem package_lemma318Literal_HHprime_of_ss_sqrtTwo (hSS : SupersingularExponentA)
    (h2 : SqrtTwoNotInHHprime) : Package.Lemma318Literal HHprime :=
  lemma318Literal_HHprime_of_ss_sqrtTwo hSS h2

/-! ## §10. Plugging into the kernel's ring-class main theorem -/

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.Package in
/-- **`RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD` with `h318` replaced** by the
textbook leaf `SupersingularExponentA` and the glue `SqrtTwoNotInHHprime`. -/
theorem tyzThm35ReadingA_of_cmLeaves_ringClassD_ss_sqrtTwo (h11 : TYZThm11Integral)
    (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition ringClassFieldD)
    (hs : TYZSigmaFixesZn) (hSS : SupersingularExponentA) (h2 : SqrtTwoNotInHHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD h11 h1 h29 hcm hs
    (package_lemma318Literal_HHprime_of_ss_sqrtTwo hSS h2) hG

/-! ## §11. Final form: only `√2 ∉ ℍ'_n` remains -/

/-- **Main theorem (final)**: TYZ Lemma `torsion2`, `Lemma318Literal HHprime` verbatim, from the single
glue Prop `SqrtTwoNotInHHprime` (`√2 ∉ ℍ'_n`, TYZ's Step 3). The textbook leaf
`SupersingularExponentA` is no longer needed: the proved weak exponent `2(p + 1)`
(`supersingularExponentWeak`) suffices for the odd torsion. -/
theorem lemma318Literal_HHprime_of_sqrtTwoNotIn (h2 : SqrtTwoNotInHHprime) :
    Lemma318Literal HHprime :=
  fun n hn hsq => lemma318_at_w hhprimeFrobSq hn hsq (h2 n hn hsq)

/-- The same for the kernel's `Package.Lemma318Literal`. -/
theorem package_lemma318Literal_HHprime_of_sqrtTwoNotIn (h2 : SqrtTwoNotInHHprime) :
    Package.Lemma318Literal HHprime :=
  lemma318Literal_HHprime_of_sqrtTwoNotIn h2

/-- **TYZ Lemma `torsion2` unconditionally at every `n` whose only divisor `≡ 5 (mod 8)` is `n`**
(e.g. `n` prime ≡ 5 mod 8, or `n = 21`): no hypotheses at all. -/
theorem lemma318_at_single_unconditional {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n)
    (h1 : ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → d₀ = n) :
    ∀ P ∈ ptsOver (HHprime n), IsOfFinAddOrder P → 2 • (P + iPt P) = 0 :=
  lemma318_at_w hhprimeFrobSq hn hsq (sqrtTwo_not_mem_HHprime_of_single hn hsq h1)

/-- `Lemma318Literal HHprime` from the class-field-theoretic `SigmaLift` (stronger than the glue). -/
theorem lemma318Literal_HHprime_of_sigmaLift (hL : SigmaLift) : Lemma318Literal HHprime :=
  lemma318Literal_HHprime_of_sqrtTwoNotIn (sqrtTwoNotInHHprime_of_sigmaLift hL)

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.Package in
/-- **`RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD` with `h318` replaced by
`SqrtTwoNotInHHprime` alone.** -/
theorem tyzThm35ReadingA_of_cmLeaves_ringClassD_sqrtTwo (h11 : TYZThm11Integral)
    (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition ringClassFieldD)
    (hs : TYZSigmaFixesZn) (h2 : SqrtTwoNotInHHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD h11 h1 h29 hcm hs
    (package_lemma318Literal_HHprime_of_sqrtTwoNotIn h2) hG

end ZInQ.Contrib.TYZGenus.T318


/-! ## Part 2: scratch/sqrt2-glue/Sqrt2Glue.lean (verbatim body) -/

noncomputable section

open NumberField

namespace ZInQ.Contrib.TYZGenus.Sqrt2Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.RingClass ZInQ.RouteK.Rank5b
  TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder TauCeti.ClassFieldTheory

/-! ## §0. The target and tyz-318's reduction (verbatim copies) -/

/-- **GLUE G-√2 (`√2 ∉ ℍ'_n`)**, verbatim from `scratch/tyz-318/Lemma318.lean`: for squarefree
`n ≡ 5 (mod 8)`, `2` is not a square in `ℍ'_n`. TYZ prove this as Step 3 of their proof of Lemma
`torsion2`. -/
def SqrtTwoNotInHHprime : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∀ s ∈ HHprime n, s ^ 2 ≠ 2

/-- **A common lift of the `σ_{1+2ϖ}`**, verbatim from `scratch/tyz-318/Lemma318.lean`: some
`h ∈ Gal(ℚ̄/ℚ)` fixes `L_n(i)` pointwise and acts on every `H̄_{d₀,4}` as `σ_{1+2ϖ}`. -/
def SigmaLift : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ h : Qbar ≃ₐ[ℚ] Qbar, (∀ x ∈ Lni n, h x = x) ∧
    ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → ∀ _ : NeZero d₀, ∀ y : H4 d₀,
      h (embed d₀ (y : SeparableClosure (QNeg d₀))) =
        embed d₀ ((artin4 d₀ (sigmaClass d₀) y : H4 d₀) : SeparableClosure (QNeg d₀))

theorem Hprimebar_eq (d : ℕ) [NeZero d] :
    Hprimebar d = ((Hprime d).restrictScalars ℚ).map (embed d) := by
  rw [Hprimebar, dite_eq_right (NeZero.ne d)]

/-- `σ_{1+2ϖ}` moves `√2` (tyz-318, verbatim). -/
theorem sigma_moves_sqrtTwo {d : ℕ} [NeZero d] (hd : d % 8 = 5) :
    ((artin4 d (sigmaClass d) ⟨sqrtK (QNeg d) 2,
        adjSqrt_two_le_H4 (by omega) (IntermediateField.mem_adjoin_simple_self _ _)⟩ : H4 d) :
      SeparableClosure (QNeg d)) = -sqrtK (QNeg d) 2 := by
  set σ := artin4 d (sigmaClass d)
  set w : H4 d := ⟨sqrtK (QNeg d) 2,
    adjSqrt_two_le_H4 (by omega) (IntermediateField.mem_adjoin_simple_self _ _)⟩
  have hw2 : w * w = 2 := by
    apply Subtype.ext
    show sqrtK (QNeg d) 2 * sqrtK (QNeg d) 2 = 2
    rw [← sq, sqrtK_sq]; norm_num
  have hσw : σ w * σ w = w * w := by rw [← map_mul, hw2, map_ofNat]
  rcases mul_self_eq_mul_self_iff.mp hσw with e | e
  · exfalso
    apply not_adjSqrt_two_le_Hprime hd
    rw [IntermediateField.adjoin_simple_le_iff]
    show ((w : H4 d) : SeparableClosure (QNeg d)) ∈ Hprime d
    rw [Hprime, IntermediateField.mem_lift, IntermediateField.mem_fixedField_iff]
    intro g hg
    have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer _ w := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact e
    exact hst hg
  · rw [e]; rfl

/-- **`SqrtTwoNotInHHprime` from `SigmaLift`** (tyz-318, verbatim: Route A, steps 5–7). -/
theorem sqrtTwoNotInHHprime_of_sigmaLift (hL : SigmaLift) : SqrtTwoNotInHHprime := by
  intro n hn hsq s hs hs2
  obtain ⟨h, hLni, hH⟩ := hL n hn hsq
  haveI : NeZero n := ⟨by omega⟩
  have hnD : n ∈ n.divisors := Nat.mem_divisors_self n (by omega)
  -- `h` fixes every `H̄'_{d₀}`
  have hfixH : ∀ d₀ ∈ n.divisors.filter (fun d => d % 8 = 5), ∀ x ∈ Hprimebar d₀, h x = x := by
    intro d₀ hd₀ x hx
    rw [Finset.mem_filter] at hd₀
    haveI : NeZero d₀ := ⟨by omega⟩
    rw [Hprimebar_eq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : y ∈ Hprime d₀ := hy
    have hyH4 : y ∈ H4 d₀ := Hprime_le_H4 d₀ hy'
    have hz := (IntermediateField.mem_lift (⟨y, hyH4⟩ : H4 d₀)).mp hy'
    rw [IntermediateField.mem_fixedField_iff] at hz
    have hσz := hz (artin4 d₀ (sigmaClass d₀)) (Subgroup.mem_zpowers _)
    have e : ((artin4 d₀ (sigmaClass d₀) ⟨y, hyH4⟩ : H4 d₀) : SeparableClosure (QNeg d₀)) = y :=
      congrArg Subtype.val hσz
    have key := hH d₀ hd₀.1 hd₀.2 ‹NeZero d₀› ⟨y, hyH4⟩
    have k2 := key.trans (congrArg (embed d₀) e)
    exact k2
  -- `h` fixes `ℍ'_n`
  have hmemF : ∀ y, h y = y → y ∈ IntermediateField.fixedField (Subgroup.zpowers h) := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro g hg
    have hst : Subgroup.zpowers h ≤ MulAction.stabilizer (Qbar ≃ₐ[ℚ] Qbar) y := by
      rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]; exact hy
    exact hst hg
  have hF : HHprime n ≤ IntermediateField.fixedField (Subgroup.zpowers h) := by
    apply sup_le
    · intro x hx; exact hmemF x (hLni x hx)
    · apply iSup₂_le
      intro d₀ hd₀ x hx
      exact hmemF x (hfixH d₀ hd₀ x hx)
  have hhs : h s = s := by
    have := hF hs
    rw [IntermediateField.mem_fixedField_iff] at this
    exact this h (Subgroup.mem_zpowers _)
  -- `h` moves `√2`
  set w : H4 n := ⟨sqrtK (QNeg n) 2,
    adjSqrt_two_le_H4 (by omega) (IntermediateField.mem_adjoin_simple_self _ _)⟩ with hw
  have hmove : h (embed n (w : SeparableClosure (QNeg n))) = -embed n (w : SeparableClosure (QNeg n)) := by
    rw [hH n (Nat.mem_divisors_self n (by omega)) hn inferInstance w, hw, sigma_moves_sqrtTwo hn,
      map_neg]
  have hw2 : (embed n (w : SeparableClosure (QNeg n))) ^ 2 = 2 := by
    rw [← map_pow, hw]
    show embed n (sqrtK (QNeg n) 2 ^ 2) = 2
    rw [sqrtK_sq]; simp only [Int.cast_ofNat]; exact map_ofNat (embed n) 2
  have hsw : s ^ 2 = (embed n (w : SeparableClosure (QNeg n))) ^ 2 := by rw [hs2, hw2]
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs2
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsw with e | e
  · rw [e, hmove] at hhs
    exact hs0 (by rw [e]; linear_combination hhs.symm / 2)
  · rw [e, map_neg, hmove, neg_neg] at hhs
    exact hs0 (by rw [e]; linear_combination -hhs / 2)

/-! ## §1. Definitions: `K_d → F`, relative norms, Picard classes -/

/-- `K_d = ℚ(√−d) → ℚ̄` through `K_dˢ` and `embed d` (the embedding used for `H̄_{d,4}`). -/
def kEmb (d : ℕ) [NeZero d] : QNeg d →ₐ[ℚ] Qbar :=
  (embed d).comp (IsScalarTower.toAlgHom ℚ (QNeg d) (SeparableClosure (QNeg d)))

/-- `K_d → F` when `kEmb d` lands in `F`. -/
def iotaK (F : IntermediateField ℚ Qbar) (d : ℕ) [NeZero d] (h : ∀ k, kEmb d k ∈ F) :
    QNeg d →ₐ[ℚ] F :=
  (kEmb d).codRestrict F.toSubalgebra h

/-- **The relative norm `N_{F/K_d}` of an ideal of `𝓞_F`**, for `F ⊂ ℚ̄` a number field containing
`kEmb d (K_d)`, with `K_d → F` given by `iotaK` (Mathlib's `Ideal.relNorm`); `⊥` otherwise. -/
def relNormK (F : IntermediateField ℚ Qbar) (d : ℕ) [NeZero d] (P : Ideal (𝓞 F)) :
    Ideal (𝓞 (QNeg d)) := by
  classical
  exact if h : (∀ k, kEmb d k ∈ F) ∧ FiniteDimensional ℚ F then
    letI : Algebra (QNeg d) F := (iotaK F d h.1).toRingHom.toAlgebra
    haveI : FiniteDimensional ℚ F := h.2
    haveI : NumberField F := ⟨⟩
    Ideal.relNorm (𝓞 (QNeg d)) P
  else ⊥

open Classical in
/-- The class in `Pic(ℤ + 4𝓞_{K_d})` of an ideal of `𝓞_{K_d}` prime to the conductor (`1` for other
ideals). `sigmaClass d = classOf (span {3 + 2√−d})` by definition. -/
def classOf {d : ℕ} [NeZero d] (J : Ideal (𝓞 (QNeg d))) : Pic (O4 d) :=
  if h : J ∈ integralIdealsPrimeTo (O4 d).conductorModulus then (O4 d).picClass ⟨J, h⟩ else 1

theorem sigmaClass_eq_classOf (d : ℕ) [NeZero d] :
    sigmaClass d = classOf (Ideal.span {alpha d}) := rfl

/-! ## §2. The two Props -/

/-- **GLUE `FrobNormLaw` (norm compatibility of ring-class reciprocity, at primes)**: let `F ⊂ ℚ̄` be a
number field, normal over `ℚ`, `D` a finite set of indices and `P` a nonzero prime of `𝓞_F` with
`2 ∉ P`. Then some `h ∈ Gal(ℚ̄/F)` (a Frobenius at a prime above `P`) acts on `H̄_{d,4}`, for every
`d ∈ D` with `K_d ⊂ F`, as the Artin symbol of the relative norm `N_{F/K_d}(P) = 𝔭^f` in
`Pic(ℤ + 4𝓞_{K_d})`.

Proof (below, `frobNormLaw`): Mathlib's Frobenius over `𝓞_F` in a finite Galois `M ⊇ F, H̄_{d,4}`;
on `H_{d,4}` it is an arithmetic Frobenius over `𝓞_{K_d}` with exponent `N P = (N 𝔭)^f`, as is
`Art([𝔭])^f` (Tau Ceti `isArithFrobAt_ringClassArtinEquiv_picClass`); both agree since `𝔭 ∤ 4` is
unramified in `H_{d,4}` (Tau Ceti `isUnramifiedAt_ringClassField`). Standard (norm functoriality of
the Artin map, e.g. Neukirch, *Algebraic Number Theory*, VI.5, UNVERIFIED number). -/
def FrobNormLaw : Prop :=
  ∀ F : IntermediateField ℚ Qbar, FiniteDimensional ℚ F → Normal ℚ F →
    ∀ D : Finset ℕ, ∀ P : Ideal (𝓞 F), P.IsPrime → P ≠ ⊥ → (2 : 𝓞 F) ∉ P →
      ∃ h : Qbar ≃ₐ[ℚ] Qbar, (∀ x ∈ F, h x = x) ∧
        ∀ d ∈ D, ∀ _ : NeZero d, (∀ k, kEmb d k ∈ F) → ∀ y : H4 d,
          h (embed d (y : SeparableClosure (QNeg d))) =
            embed d ((artin4 d (classOf (relNormK F d P)) y : H4 d) : SeparableClosure (QNeg d))

/-- **GLUE `NormSigma` (an element of `L_n(i)` whose norms have class `σ_{1+2ϖ}`)**: for squarefree
`n ≡ 5 (mod 8)` some `α ∈ 𝓞_{L_n(i)}`, `α ≠ 0`, coprime to `2`, has
`[N_{L_n(i)/K_{d₀}}(α𝓞)] = σ_{1+2ϖ}` in `Pic(ℤ + 4𝓞_{K_{d₀}})` for every `d₀ ∣ n`,
`d₀ ≡ 5 (mod 8)`. Route A, step 1: `α = 1 + 2i∏_{q∣n}(1 + √q*)/2`
(`docs/research/tyz-318.md` §3.2; checked numerically by `scratch/tyz-318/trace_check.py`). -/
def NormSigma : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ α : 𝓞 (Lni n), α ≠ 0 ∧ IsCoprime α 2 ∧
    ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → ∀ _ : NeZero d₀,
      classOf (relNormK (Lni n) d₀ (Ideal.span {α})) = sigmaClass d₀

/-! ## §3. Ideal-theoretic lemmas -/

section Generic

variable {L : Type*} [Field L] [NumberField L]

/-- An ideal of odd absolute norm is coprime to `2`. -/
theorem isCoprime_two_of_odd_absNorm {J : Ideal (𝓞 L)} (h : Odd (Ideal.absNorm J)) :
    IsCoprime J (Ideal.span {(2 : 𝓞 L)}) := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  obtain ⟨k, hk⟩ := h
  have h1 : ((Ideal.absNorm J : ℕ) : 𝓞 L) ∈ J := Ideal.absNorm_mem J
  have e : (1 : 𝓞 L) = ((Ideal.absNorm J : ℕ) : 𝓞 L) - 2 * (k : 𝓞 L) := by
    rw [hk]; push_cast; ring
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left h1)
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

/-- A nonzero ideal coprime to `2` has odd absolute norm (Cauchy's theorem in `𝓞_L / J`). -/
theorem odd_absNorm_of_isCoprime_two {J : Ideal (𝓞 L)} (hJ0 : J ≠ ⊥)
    (h : IsCoprime J (Ideal.span {(2 : 𝓞 L)})) : Odd (Ideal.absNorm J) := by
  rw [Nat.odd_iff]
  by_contra hev
  have h2 : 2 ∣ Nat.card (𝓞 L ⧸ J) := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]; omega
  haveI : Finite (𝓞 L ⧸ J) := Ring.HasFiniteQuotients.finiteQuotient hJ0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' 2 h2
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Submodule.mem_sup] at h
  obtain ⟨a, ha, b, hb, hab⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  have h2x : (2 : 𝓞 L ⧸ J) * x = 0 := by
    have := addOrderOf_nsmul_eq_zero x
    rw [hx, nsmul_eq_mul] at this
    exact_mod_cast this
  have hc : Ideal.Quotient.mk J c * 2 = 1 := by
    have : Ideal.Quotient.mk J (a + c * 2) = 1 := by rw [hab, map_one]
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, map_mul, map_ofNat] at this
    exact this
  have hx0 : x = 0 := by
    calc x = (Ideal.Quotient.mk J c * 2) * x := by rw [hc, one_mul]
      _ = Ideal.Quotient.mk J c * (2 * x) := by ring
      _ = 0 := by rw [h2x, mul_zero]
  rw [hx0, addOrderOf_zero] at hx
  omega

variable {K : Type*} [Field K] [NumberField K] [Algebra K L]

/-- The relative norm of a nonzero ideal coprime to `2` is coprime to `2`. -/
theorem relNorm_isCoprime_two {J : Ideal (𝓞 L)} (hJ0 : J ≠ ⊥)
    (h : IsCoprime J (Ideal.span {(2 : 𝓞 L)})) :
    IsCoprime (Ideal.relNorm (𝓞 K) J) (Ideal.span {(2 : 𝓞 K)}) := by
  apply isCoprime_two_of_odd_absNorm
  rw [Ideal.absNorm_relNorm]
  exact odd_absNorm_of_isCoprime_two hJ0 h

end Generic

section PicClass

variable {d : ℕ} [NeZero d]

theorem absNorm_span_natCast' (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 (QNeg d))}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have e : (p : 𝓞 (QNeg d)) = algebraMap ℤ (𝓞 (QNeg d)) (p : ℤ) := by simp
  rw [e, Algebra.norm_algebraMap, RingOfIntegers.rank, QuadraticAlgebra.finrank_eq_two]
  simp

/-- An ideal of `𝓞_{K_d}` coprime to `2` is prime to the conductor of `ℤ + 4𝓞_{K_d}`. -/
theorem mem_primeTo_of_isCoprime_two {J : Ideal (𝓞 (QNeg d))}
    (h : IsCoprime J (Ideal.span {(2 : 𝓞 (QNeg d))})) :
    J ∈ integralIdealsPrimeTo (O4 d).conductorModulus := by
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
  refine ⟨?_, ?_⟩
  · rintro rfl
    rw [Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at h
    have := absNorm_span_natCast' (d := d) 2
    rw [show ((2 : ℕ) : 𝓞 (QNeg d)) = 2 by norm_num, h, Ideal.absNorm_top] at this
    norm_num at this
  · have h4 : IsCoprime J (Ideal.span {(2 : 𝓞 (QNeg d))} ^ 2) := h.pow_right
    rw [Ideal.span_singleton_pow, Ideal.isCoprime_iff_sup_eq] at h4
    rw [eq_top_iff, ← h4]
    apply sup_le_sup_left
    rw [Ideal.span_singleton_le_iff_mem]
    have := natCast_mul_mem_conductor (QNeg d) 4 1
    rw [mul_one] at this
    convert this using 1
    norm_num

theorem classOf_of_mem {J : Ideal (𝓞 (QNeg d))} (h : J ∈ integralIdealsPrimeTo (O4 d).conductorModulus) :
    classOf J = (O4 d).picClass ⟨J, h⟩ := by
  rw [classOf, dif_pos h]

theorem classOf_mul {I J : Ideal (𝓞 (QNeg d))} (hI : I ∈ integralIdealsPrimeTo (O4 d).conductorModulus)
    (hJ : J ∈ integralIdealsPrimeTo (O4 d).conductorModulus) :
    classOf (I * J) = classOf I * classOf J := by
  rw [classOf_of_mem hI, classOf_of_mem hJ, classOf_of_mem (Submonoid.mul_mem _ hI hJ), ← map_mul]
  rfl

theorem classOf_top : classOf (⊤ : Ideal (𝓞 (QNeg d))) = 1 := by
  have h1 : (⊤ : Ideal (𝓞 (QNeg d))) ∈ integralIdealsPrimeTo (O4 d).conductorModulus := by
    rw [← Ideal.one_eq_top]; exact (integralIdealsPrimeTo (O4 d).conductorModulus).one_mem
  rw [classOf_of_mem h1]
  have e : (⟨⊤, h1⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) = 1 :=
    Subtype.ext Ideal.one_eq_top.symm
  rw [e, map_one]

end PicClass

section RelNormK

variable (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] (d : ℕ) [NeZero d]
  (hK : ∀ k, kEmb d k ∈ F)
include hK

theorem relNormK_mul (I J : Ideal (𝓞 F)) :
    relNormK F d (I * J) = relNormK F d I * relNormK F d J := by
  simp only [relNormK, dif_pos (And.intro hK ‹FiniteDimensional ℚ F›)]
  letI : Algebra (QNeg d) F := (iotaK F d hK).toRingHom.toAlgebra
  haveI : NumberField F := ⟨⟩
  exact map_mul _ _ _

theorem relNormK_top : relNormK F d ⊤ = ⊤ := by
  simp only [relNormK, dif_pos (And.intro hK ‹FiniteDimensional ℚ F›)]
  letI : Algebra (QNeg d) F := (iotaK F d hK).toRingHom.toAlgebra
  haveI : NumberField F := ⟨⟩
  exact Ideal.relNorm_top _

theorem relNormK_ne_bot {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) : relNormK F d I ≠ ⊥ := by
  simp only [relNormK, dif_pos (And.intro hK ‹FiniteDimensional ℚ F›)]
  letI : Algebra (QNeg d) F := (iotaK F d hK).toRingHom.toAlgebra
  haveI : NumberField F := ⟨⟩
  exact Ideal.relNorm_eq_bot_iff.not.mpr hI

theorem relNormK_isCoprime {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (h : IsCoprime I (Ideal.span {(2 : 𝓞 F)})) :
    IsCoprime (relNormK F d I) (Ideal.span {(2 : 𝓞 (QNeg d))}) := by
  simp only [relNormK, dif_pos (And.intro hK ‹FiniteDimensional ℚ F›)]
  letI : Algebra (QNeg d) F := (iotaK F d hK).toRingHom.toAlgebra
  haveI : NumberField F := ⟨⟩
  exact relNorm_isCoprime_two hI h

end RelNormK

/-! ## §4. Assembly: `SigmaLift` from `FrobNormLaw` and `NormSigma` -/

/-- Square roots of `−d₀` lie in `L_n(i)` for `d₀ ∣ n` squarefree. -/
theorem mem_Lni_of_sq_eq_neg {n d₀ : ℕ} (hsq : Squarefree n) (hd : d₀ ∣ n) {x : Qbar}
    (hx : x ^ 2 = -(d₀ : Qbar)) : x ∈ Lni n := by
  have hn0 : n ≠ 0 := hsq.ne_zero
  have hsqd : Squarefree d₀ := hsq.squarefree_of_dvd hd
  have hroot : ∀ p ∈ d₀.primeFactors, ∃ s ∈ Lni n, s ^ 2 = (p : Qbar) := by
    intro p hp
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (p : Qbar) (by norm_num : 0 < 2)
    refine ⟨s, IntermediateField.subset_adjoin _ _ (Or.inr ⟨p, ?_, hs⟩), hs⟩
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,
      (Nat.dvd_of_mem_primeFactors hp).trans hd, hn0⟩
  choose! s hsL hs2 using hroot
  set r : Qbar := iQ * ∏ p ∈ d₀.primeFactors, s p with hr
  have hrL : r ∈ Lni n :=
    (Lni n).mul_mem (ZInQ.Contrib.TYZGenus.Package.iQ_mem_Lni n)
      ((Lni n).prod_mem fun p hp => hsL p hp)
  have hr2 : r ^ 2 = -(d₀ : Qbar) := by
    rw [hr, mul_pow, ← Finset.prod_pow, Finset.prod_congr rfl hs2, iQ_sq]
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsqd]
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans hr2.symm) with e | e
  · rw [e]; exact hrL
  · rw [e]; exact (Lni n).neg_mem hrL

theorem kEmb_mem_Lni {n d₀ : ℕ} [NeZero d₀] (hsq : Squarefree n) (hd : d₀ ∣ n) :
    ∀ k, kEmb d₀ k ∈ Lni n := by
  intro k
  have hk : k = algebraMap ℚ (QNeg d₀) k.re + algebraMap ℚ (QNeg d₀) k.im * QuadraticAlgebra.omega := by
    ext <;> simp
  have hω : kEmb d₀ QuadraticAlgebra.omega ∈ Lni n := by
    apply mem_Lni_of_sq_eq_neg hsq hd
    rw [← map_pow, sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    simp
  rw [hk, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]
  exact (Lni n).add_mem ((Lni n).algebraMap_mem _)
    ((Lni n).mul_mem ((Lni n).algebraMap_mem _) hω)

theorem finiteDimensional_Lni {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) :
    FiniteDimensional ℚ (Lni n) := by
  haveI : NeZero n := ⟨by omega⟩
  have hle := Lni_le_Hprimebar (by omega) hsq
  have : FiniteDimensional ℚ (Hprimebar n) := by
    rw [Hprimebar_eq]
    have : FiniteDimensional ℚ (Hprime n) := Module.Finite.trans (QNeg n) (Hprime n)
    have : FiniteDimensional ℚ ((Hprime n).restrictScalars ℚ) :=
      inferInstanceAs (FiniteDimensional ℚ (Hprime n))
    exact LinearEquiv.finiteDimensional
      (IntermediateField.equivMap ((Hprime n).restrictScalars ℚ) (embed n)).toLinearEquiv
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

/-- A product of nonzero ideals coprime to `I` is nonzero and coprime to `I`. -/
theorem prod_ne_bot_isCoprime {R : Type*} [CommRing R] [IsDomain R] {I : Ideal R}
    (t : Multiset (Ideal R)) (ht : ∀ Q ∈ t, Q ≠ ⊥ ∧ IsCoprime Q I) :
    t.prod ≠ ⊥ ∧ IsCoprime t.prod I := by
  induction t using Multiset.induction_on with
  | empty =>
    rw [Multiset.prod_zero, Ideal.one_eq_top]
    exact ⟨top_ne_bot, Ideal.isCoprime_iff_sup_eq.mpr (top_sup_eq I)⟩
  | cons Q u ihu =>
    obtain ⟨h1, h2⟩ := ihu (fun R hR => ht R (Multiset.mem_cons_of_mem hR))
    obtain ⟨h3, h4⟩ := ht Q (Multiset.mem_cons_self _ _)
    rw [Multiset.prod_cons]
    refine ⟨fun h0 => ?_, h4.mul_left h2⟩
    rcases Ideal.mul_eq_bot.mp h0 with e | e
    · exact h3 e
    · exact h1 e

/-- **`SigmaLift` from `FrobNormLaw` and `NormSigma`** (product of Frobenius elements over the prime
factors of `α𝓞_F`). -/
theorem sigmaLift_of (hF : FrobNormLaw) (hN : NormSigma) : SigmaLift := by
  intro n hn hsq
  obtain ⟨α, hα0, hα2, hασ⟩ := hN n hn hsq
  haveI hFD : FiniteDimensional ℚ (Lni n) := finiteDimensional_Lni hn hsq
  haveI : NumberField (Lni n) := ⟨⟩
  haveI : Normal ℚ (Lni n) := ZInQ.Contrib.TYZGenus.Package.normal_Lni n
  set D := n.divisors.filter (fun d => d % 8 = 5)
  -- the claim, by induction on a multiset of primes
  have claim : ∀ s : Multiset (Ideal (𝓞 (Lni n))),
      (∀ P ∈ s, P.IsPrime ∧ P ≠ ⊥ ∧ IsCoprime P (Ideal.span {(2 : 𝓞 (Lni n))})) →
      ∃ h : Qbar ≃ₐ[ℚ] Qbar, (∀ x ∈ Lni n, h x = x) ∧
        ∀ d ∈ D, ∀ _ : NeZero d, (∀ k, kEmb d k ∈ Lni n) → ∀ y : H4 d,
          h (embed d (y : SeparableClosure (QNeg d))) =
            embed d ((artin4 d (classOf (relNormK (Lni n) d s.prod)) y : H4 d) :
              SeparableClosure (QNeg d)) := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      intro _
      refine ⟨AlgEquiv.refl, fun x _ => rfl, ?_⟩
      intro d _ _ hK y
      rw [Multiset.prod_zero, Ideal.one_eq_top, relNormK_top (Lni n) d hK, classOf_top, map_one]
      rfl
    | cons P t ih =>
      intro hs
      obtain ⟨hP, hP0, hP2⟩ := hs P (Multiset.mem_cons_self _ _)
      obtain ⟨ht, htF, htH⟩ := ih (fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ))
      have hP2' : (2 : 𝓞 (Lni n)) ∉ P := by
        intro h2
        rw [Ideal.isCoprime_iff_sup_eq] at hP2
        apply hP.ne_top
        rw [eq_top_iff, ← hP2]
        exact sup_le le_rfl ((Ideal.span_singleton_le_iff_mem _).mpr h2)
      obtain ⟨hp, hpF, hpH⟩ := hF (Lni n) hFD inferInstance D P hP hP0 hP2'
      refine ⟨hp * ht, fun x hx => by rw [AlgEquiv.mul_apply, htF x hx, hpF x hx], ?_⟩
      intro d hd hd0 hK y
      -- the product `t.prod` is nonzero and coprime to `2`
      have htprod := prod_ne_bot_isCoprime t (fun Q hQ =>
          ⟨(hs Q (Multiset.mem_cons_of_mem hQ)).2.1, (hs Q (Multiset.mem_cons_of_mem hQ)).2.2⟩)
      have hcP := mem_primeTo_of_isCoprime_two (relNormK_isCoprime (Lni n) d hK hP0 hP2)
      have hct := mem_primeTo_of_isCoprime_two (relNormK_isCoprime (Lni n) d hK htprod.1 htprod.2)
      rw [AlgEquiv.mul_apply, htH d hd hd0 hK y, hpH d hd hd0 hK, Multiset.prod_cons,
        relNormK_mul (Lni n) d hK, classOf_mul hcP hct, map_mul]
      rfl
  -- apply the claim to the prime factors of `α𝓞_F`
  have hspan0 : Ideal.span {α} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨h, hfix, hact⟩ := claim (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {α}))
    (by
      intro P hP
      have hPprime := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
      have hPne : P ≠ ⊥ := hPprime.ne_zero
      refine ⟨Ideal.isPrime_of_prime hPprime, hPne, ?_⟩
      have hαP : α ∈ P := by
        have hdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
        rw [Ideal.dvd_iff_le] at hdvd
        exact hdvd (Ideal.mem_span_singleton_self α)
      obtain ⟨a, b, hab⟩ := hα2
      rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mem_sup_left (P.mul_mem_left a hαP))
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ b (Ideal.mem_span_singleton_self _))))
  refine ⟨h, hfix, ?_⟩
  intro d₀ hd₀ hd₀5 hd₀0 y
  have hK := kEmb_mem_Lni (d₀ := d₀) hsq (Nat.dvd_of_mem_divisors hd₀)
  rw [hact d₀ (Finset.mem_filter.mpr ⟨hd₀, hd₀5⟩) hd₀0 hK y,
    Ideal.prod_normalizedFactors_eq_self hspan0, hασ d₀ hd₀ hd₀5 hd₀0]

/-- **`SqrtTwoNotInHHprime` from `FrobNormLaw` and `NormSigma`.** -/
theorem sqrtTwoNotInHHprime_of (hF : FrobNormLaw) (hN : NormSigma) : SqrtTwoNotInHHprime :=
  sqrtTwoNotInHHprime_of_sigmaLift (sigmaLift_of hF hN)

/-! ## §5. Frobenius comparison: an exponent-`(N𝔭)^f` Frobenius is `Art(𝔭)^f` -/

section FrobPow

/-- Iterating a Frobenius-type congruence. -/
theorem iterate_congr {S : Type*} [CommRing S] (Q : Ideal S) (φ : S → S) (m : ℕ)
    (hφ : ∀ x, φ x - x ^ m ∈ Q) (hQ : ∀ x y, x - y ∈ Q → φ x - φ y ∈ Q) :
    ∀ k x, φ^[k] x - x ^ (m ^ k) ∈ Q := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [Function.iterate_succ_apply']
    have h1 := hφ (φ^[k] x)
    have h2 : (φ^[k] x) ^ m - (x ^ (m ^ k)) ^ m ∈ Q :=
      Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow _ _ m) (ih x)
    have e : φ (φ^[k] x) - x ^ (m ^ (k + 1)) =
        (φ (φ^[k] x) - (φ^[k] x) ^ m) + ((φ^[k] x) ^ m - (x ^ (m ^ k)) ^ m) := by
      rw [← pow_mul, ← pow_succ]; ring
    rw [e]; exact Q.add_mem h1 h2

variable {K L : Type*} [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-- **An automorphism acting as `x ↦ x^{(N𝔭)^f}` modulo an unramified `Q` is `φ^f`**, `φ` an arithmetic
Frobenius at `Q` (reduction to Tau Ceti's uniqueness `isArithFrobAt_eq_of_isUnramifiedAt`). -/
theorem eq_pow_of_congr {Q : Ideal (𝓞 L)} [hQ : Q.IsPrime] [Algebra.IsUnramifiedAt (𝓞 K) Q]
    {φ τ : L ≃ₐ[K] L} (hφ : IsArithFrobAt (𝓞 K) φ Q) (f : ℕ)
    (hτ : ∀ x : 𝓞 L, τ • x - x ^ (Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ f) ∈ Q) : τ = φ ^ f := by
  set N := Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) with hN
  have hNpos : 0 < N := hφ.card_pos
  have hφ' : ∀ x : 𝓞 L, φ • x - x ^ N ∈ Q := fun x => hφ x
  have hφQ : ∀ x y : 𝓞 L, x - y ∈ Q → φ • x - φ • y ∈ Q := by
    intro x y hxy
    have := hφ.le_comap hxy
    rw [Ideal.mem_comap, map_sub] at this
    exact this
  -- `φ^f` has exponent `N^f`
  have hφf : ∀ x : 𝓞 L, φ ^ f • x - x ^ (N ^ f) ∈ Q := by
    intro x
    have := iterate_congr Q (fun x => φ • x) N hφ' hφQ f x
    rwa [smul_iterate_apply] at this
  -- `τ` preserves `Q`
  have hτQ1 : ∀ j : ℕ, ∀ x ∈ Q, τ ^ j • x ∈ Q := by
    intro j
    induction j with
    | zero => intro x hx; rwa [pow_zero, one_smul]
    | succ j ih =>
      intro x hx
      rw [pow_succ', mul_smul]
      have h1 := ih x hx
      have h2 := hτ (τ ^ j • x)
      have h3 : (τ ^ j • x) ^ (N ^ f) ∈ Q := Q.pow_mem_of_mem h1 _ (pow_pos hNpos f)
      have := Q.add_mem h2 h3
      rwa [sub_add_cancel] at this
  have hfin : IsOfFinOrder τ := isOfFinOrder_of_finite τ
  have hτinv : ∀ x ∈ Q, τ⁻¹ • x ∈ Q := by
    intro x hx
    have e : τ⁻¹ = τ ^ (orderOf τ - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hfin.orderOf_pos,
        pow_orderOf_eq_one]
    rw [e]; exact hτQ1 _ x hx
  -- `ρ = τ⁻¹ φ^f` acts trivially modulo `Q`
  set ρ := τ⁻¹ * φ ^ f with hρ
  have hρ1 : ∀ x : 𝓞 L, ρ • x - x ∈ Q := by
    intro x
    have hd : φ ^ f • x - τ • x ∈ Q := by
      have := Q.sub_mem (hφf x) (hτ x)
      rwa [sub_sub_sub_cancel_right] at this
    have := hτinv _ hd
    rw [smul_sub, inv_smul_smul, ← mul_smul] at this
    exact this
  -- `φρ` is an arithmetic Frobenius at `Q`, hence `φρ = φ`
  have hφρ : IsArithFrobAt (𝓞 K) (φ * ρ) Q := by
    intro x
    show (φ * ρ) • x - x ^ N ∈ Q
    have h1 := hφQ _ _ (hρ1 x)
    have h2 := hφ' x
    have e : (φ * ρ) • x - x ^ N = (φ • ρ • x - φ • x) + (φ • x - x ^ N) := by
      rw [mul_smul]; ring
    rw [e]; exact Q.add_mem h1 h2
  have := isArithFrobAt_eq_of_isUnramifiedAt hφρ hφ
  have hρ1' : ρ = 1 := by
    have := congrArg (φ⁻¹ * ·) this
    simpa using this
  rw [hρ, inv_mul_eq_one] at hρ1'
  exact hρ1'

end FrobPow

/-! ## §6. Transport `H_{d,4} ≅ H̄_{d,4}` and the Frobenius over `F` on `H_{d,4}` -/

section Transport

variable {d : ℕ} [NeZero d]

/-- `H_{d,4} ≅ H̄_{d,4} ⊂ ℚ̄` through `embed d`. -/
def psi4 (d : ℕ) [NeZero d] : ((H4 d).restrictScalars ℚ) ≃ₐ[ℚ] H4bar d :=
  (IntermediateField.equivMap ((H4 d).restrictScalars ℚ) (embed d)).trans
    (IntermediateField.equivOfEq (H4bar_eq_map (d := d)).symm)

theorem psi4_apply (y : (H4 d).restrictScalars ℚ) :
    ((psi4 d y : H4bar d) : Qbar) = embed d (y : SeparableClosure (QNeg d)) := rfl

instance instNormalH4bar : Normal ℚ (H4bar d) := normal_H4bar d

/-- `h ∈ Gal(ℚ̄/ℚ)` transported to a `ℚ`-automorphism of `H_{d,4}`. -/
def tauQ4 (h : Qbar ≃ₐ[ℚ] Qbar) : ((H4 d).restrictScalars ℚ) ≃ₐ[ℚ] ((H4 d).restrictScalars ℚ) :=
  ((psi4 d).trans (h.restrictNormal (H4bar d))).trans (psi4 d).symm

theorem psi4_tauQ4 (h : Qbar ≃ₐ[ℚ] Qbar) (y : (H4 d).restrictScalars ℚ) :
    ((psi4 d (tauQ4 (d := d) h y) : H4bar d) : Qbar) = h ((psi4 d y : H4bar d) : Qbar) := by
  simp only [tauQ4, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  exact AlgEquiv.restrictNormal_commutes h (H4bar d) (psi4 d y)

/-- If `h` fixes `kEmb d (K_d)`, its transport is a `K_d`-automorphism of `H_{d,4}`. -/
def tau4 (h : Qbar ≃ₐ[ℚ] Qbar) (hK : ∀ k, h (kEmb d k) = kEmb d k) : Gal(H4 d / QNeg d) :=
  AlgEquiv.ofRingEquiv (f := (tauQ4 (d := d) h).toRingEquiv) (fun c => by
    apply Subtype.ext
    apply (embed d).injective
    have e := psi4_tauQ4 (d := d) h
      (⟨algebraMap (QNeg d) (SeparableClosure (QNeg d)) c, (H4 d).algebraMap_mem c⟩ :
        (H4 d).restrictScalars ℚ)
    rw [psi4_apply, psi4_apply] at e
    exact e.trans (hK c))

theorem coe_tau4 (h : Qbar ≃ₐ[ℚ] Qbar) (hK : ∀ k, h (kEmb d k) = kEmb d k) (y : H4 d) :
    ((tau4 h hK y : H4 d) : SeparableClosure (QNeg d)) =
      ((tauQ4 (d := d) h y : (H4 d).restrictScalars ℚ) : SeparableClosure (QNeg d)) := rfl

theorem classOf_pow {J : Ideal (𝓞 (QNeg d))} (hJ : J ∈ integralIdealsPrimeTo (O4 d).conductorModulus)
    (k : ℕ) : classOf (J ^ k) = classOf J ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, Ideal.one_eq_top, classOf_top]
  | succ k ih =>
    have hk : J ^ k ∈ integralIdealsPrimeTo (O4 d).conductorModulus := Submonoid.pow_mem _ hJ k
    rw [pow_succ, classOf_mul hk hJ, ih, pow_succ]

end Transport

/-- **The Frobenius over `F` on `H_{d,4}`**: let `F ⊂ M ⊂ ℚ̄` be number fields with `K_d ⊂ F` and
`H̄_{d,4} ⊂ M`, `𝔔` a prime of `𝓞_M` over a nonzero prime `P ∌ 2` of `𝓞_F`, and `h ∈ Gal(ℚ̄/F)`
acting as `x ↦ x^{N P}` modulo `𝔔` on `𝓞_M`. Then `h` acts on `H̄_{d,4}` as the Artin symbol of
`N_{F/K_d}(P) = 𝔭^f`. -/
theorem frob_on_H4 (F M : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] [FiniteDimensional ℚ M]
    (hFM : F ≤ M) (d : ℕ) [NeZero d] (hK : ∀ k, kEmb d k ∈ F) (hHM : H4bar d ≤ M)
    (h : Qbar ≃ₐ[ℚ] Qbar) (hfix : ∀ x ∈ F, h x = x) (𝔔 : Ideal (𝓞 M)) [𝔔.IsPrime]
    (P : Ideal (𝓞 F)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (hP2 : (2 : 𝓞 F) ∉ P)
    (hPQ : ∀ a : 𝓞 F, a ∈ P ↔
      RingOfIntegers.mapRingHom (IntermediateField.inclusion hFM).toRingHom a ∈ 𝔔)
    (hfrob : ∀ x b : 𝓞 M, ((b : M) : Qbar) =
      h ((x : M) : Qbar) - ((x : M) : Qbar) ^ Nat.card (𝓞 F ⧸ P) → b ∈ 𝔔) :
    ∀ y : H4 d, h (embed d (y : SeparableClosure (QNeg d))) =
      embed d ((artin4 d (classOf (relNormK F d P)) y : H4 d) : SeparableClosure (QNeg d)) := by
  haveI : NumberField F := ⟨⟩
  haveI : NumberField M := ⟨⟩
  letI : Algebra (QNeg d) F := (iotaK F d hK).toRingHom.toAlgebra
  have hKfix : ∀ k, h (kEmb d k) = kEmb d k := fun k => hfix _ (hK k)
  obtain ⟨τ, hτval⟩ : ∃ τ : Gal(H4 d / QNeg d), ∀ y : H4 d,
      embed d ((τ y : H4 d) : SeparableClosure (QNeg d)) =
        h (embed d ((y : H4 d) : SeparableClosure (QNeg d))) :=
    ⟨tau4 h hKfix, fun y => psi4_tauQ4 (d := d) h (y : H4 d)⟩
  let ψ : 𝓞 (H4 d) →+* 𝓞 M := RingOfIntegers.mapRingHom
    ((IntermediateField.inclusion hHM).toRingHom.comp (psi4 d).toRingHom)
  have hψ : ∀ y : 𝓞 (H4 d), (((ψ y : 𝓞 M) : M) : Qbar) =
      embed d ((y : H4 d) : SeparableClosure (QNeg d)) := fun y => rfl
  set Q' := 𝔔.comap ψ with hQ'
  haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
  set q := Nat.card (𝓞 F ⧸ P) with hqdef
  -- the congruence for `τ`
  have hτ : ∀ y : 𝓞 (H4 d), τ • y - y ^ q ∈ Q' := by
    intro y
    rw [hQ', Ideal.mem_comap]
    apply hfrob (ψ y) (ψ (τ • y - y ^ q))
    have e1 : (((ψ (τ • y) : 𝓞 M) : M) : Qbar) = h (((ψ y : 𝓞 M) : M) : Qbar) := by
      rw [hψ, hψ]
      exact hτval (y : H4 d)
    rw [map_sub, map_pow]
    push_cast
    rw [e1]
  -- the prime `𝔭` of `𝓞_{K_d}` below
  set 𝔭 := Q'.under (𝓞 (QNeg d)) with h𝔭def
  have hιeq : ∀ k : 𝓞 (QNeg d),
      RingOfIntegers.mapRingHom (IntermediateField.inclusion hFM).toRingHom
        (algebraMap (𝓞 (QNeg d)) (𝓞 F) k) = ψ (algebraMap (𝓞 (QNeg d)) (𝓞 (H4 d)) k) := by
    intro k
    apply RingOfIntegers.ext
    apply Subtype.ext
    rfl
  have hP𝔭 : P.under (𝓞 (QNeg d)) = 𝔭 := by
    ext k
    rw [Ideal.under_def, Ideal.mem_comap, hPQ, hιeq, h𝔭def, Ideal.under_def, Ideal.mem_comap,
      hQ', Ideal.mem_comap]
  haveI : P.LiesOver 𝔭 := ⟨hP𝔭.symm⟩
  have h2𝔭 : (2 : 𝓞 (QNeg d)) ∉ 𝔭 := by
    rw [← hP𝔭, Ideal.under_def, Ideal.mem_comap, map_ofNat]; exact hP2
  have h𝔭0 : 𝔭 ≠ ⊥ := by rw [← hP𝔭]; exact Ideal.under_ne_bot _ hP0
  haveI h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  haveI h𝔭max : 𝔭.IsMaximal := h𝔭prime.isMaximal h𝔭0
  haveI : P.IsMaximal := hP.isMaximal hP0
  -- the relative norm and the exponent
  have hrel : relNormK F d P = 𝔭 ^ P.inertiaDeg (𝓞 (QNeg d)) := by
    simp only [relNormK, dif_pos (And.intro hK ‹FiniteDimensional ℚ F›)]
    exact Ideal.relNorm_eq_pow_of_isMaximal P 𝔭
  have hq : q = Nat.card (𝓞 (QNeg d) ⧸ 𝔭) ^ P.inertiaDeg (𝓞 (QNeg d)) := by
    have := Ideal.cardQuot_pow_inertiaDeg 𝔭 P
    rw [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at this
    exact this.symm
  -- the class of `𝔭`
  have hco : IsCoprime 𝔭 (Ideal.span {(2 : 𝓞 (QNeg d))}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    have := h𝔭max.eq_of_le hne le_sup_left
    exact h2𝔭 (this ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have h𝔭mem := mem_primeTo_of_isCoprime_two hco
  set f := P.inertiaDeg (𝓞 (QNeg d))
  have hclass : classOf (relNormK F d P) = (O4 d).picClass ⟨𝔭, h𝔭mem⟩ ^ f := by
    rw [hrel, classOf_pow h𝔭mem, classOf_of_mem h𝔭mem]
  -- Frobenius at `Q'` and unramifiedness
  haveI : ((⟨𝔭, h𝔭mem⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := h𝔭max
  haveI : Q'.LiesOver ((⟨𝔭, h𝔭mem⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))) := ⟨rfl⟩
  have hφ := isArithFrobAt_ringClassArtinEquiv_picClass (O4 d) ⟨𝔭, h𝔭mem⟩ Q'
  have hndvd : ¬ (⟨𝔭, h𝔭prime, h𝔭0⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 (QNeg d))).asIdeal ∣
      (O4 d).conductor := by
    intro hdvd
    rw [Ideal.dvd_iff_le] at hdvd
    have h1 := ((mem_integralIdealsPrimeTo_conductorModulus_iff (O := O4 d)).mp h𝔭mem).2
    rw [sup_eq_left.mpr hdvd] at h1
    exact h𝔭max.ne_top h1
  haveI : Q'.LiesOver (⟨𝔭, h𝔭prime, h𝔭0⟩ :
    IsDedekindDomain.HeightOneSpectrum (𝓞 (QNeg d))).asIdeal := ⟨rfl⟩
  haveI : Algebra.IsUnramifiedAt (𝓞 (QNeg d)) Q' :=
    isUnramifiedAt_ringClassField (O4 d) hndvd Q'
  have hτ' : ∀ x : 𝓞 (H4 d), τ • x - x ^ (Nat.card (𝓞 (QNeg d) ⧸ Q'.under (𝓞 (QNeg d))) ^ f) ∈ Q' := by
    intro x
    have e : Nat.card (𝓞 (QNeg d) ⧸ Q'.under (𝓞 (QNeg d))) ^ f = q := hq.symm
    rw [e]
    exact hτ x
  have hτφ : τ = ringClassArtinEquiv (O4 d) ((O4 d).picClass ⟨𝔭, h𝔭mem⟩) ^ f :=
    eq_pow_of_congr (K := QNeg d) (L := H4 d) (Q := Q') hφ f hτ'
  intro y
  rw [show artin4 d = ringClassArtinEquiv (O4 d) from rfl, hclass, map_pow, ← hτφ]
  exact (hτval y).symm

/-! ## §7. `FrobNormLaw` holds -/

instance finiteDimensional_H4bar (d : ℕ) : FiniteDimensional ℚ (H4bar d) := by
  by_cases h : d = 0
  · subst h; rw [H4bar, dite_eq_left rfl]; infer_instance
  · haveI : NeZero d := ⟨h⟩
    rw [H4bar_eq_map]
    have : FiniteDimensional ℚ (H4 d) := Module.Finite.trans (QNeg d) (H4 d)
    have : FiniteDimensional ℚ ((H4 d).restrictScalars ℚ) :=
      inferInstanceAs (FiniteDimensional ℚ (H4 d))
    exact LinearEquiv.finiteDimensional
      (IntermediateField.equivMap ((H4 d).restrictScalars ℚ) (embed d)).toLinearEquiv

/-- **`FrobNormLaw` holds** (no hypotheses). -/
theorem frobNormLaw : FrobNormLaw := by
  intro F hFD hFN D P hP hP0 hP2
  haveI := hFD
  haveI := hFN
  haveI : NumberField F := ⟨⟩
  set M : IntermediateField ℚ Qbar := F ⊔ ⨆ d : D, H4bar (d : ℕ) with hM
  haveI : FiniteDimensional ℚ M := by rw [hM]; infer_instance
  haveI : Normal ℚ M := by rw [hM]; infer_instance
  haveI : NumberField M := ⟨⟩
  have hFM : F ≤ M := le_sup_left
  have hHM : ∀ d ∈ D, H4bar d ≤ M := fun d hd =>
    le_sup_of_le_right (le_iSup (fun d : D => H4bar (d : ℕ)) ⟨d, hd⟩)
  letI : Algebra F M := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F M := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : IsGalois ℚ M := ⟨⟩
  haveI : IsGalois F M := IsGalois.tower_top_of_isGalois ℚ F M
  haveI : FiniteDimensional F M := Module.Finite.of_restrictScalars_finite ℚ F M
  let _ := IsIntegralClosure.MulSemiringAction (𝓞 F) F M (𝓞 M)
  have := Algebra.isInvariant_of_isGalois (𝓞 F) F M (𝓞 M)
  haveI : SMulCommClass (M ≃ₐ[F] M) (𝓞 F) (𝓞 M) := ⟨fun g r x => by
    change galRestrict (𝓞 F) F M (𝓞 M) g (r • x) = r • galRestrict (𝓞 F) F M (𝓞 M) g x
    exact map_smul _ r x⟩
  -- a prime `𝔔` of `𝓞_M` over `P`
  obtain ⟨𝔔, -, h𝔔, h𝔔P⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal (𝓞 M))
    (by
      intro a ha
      rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_bot] at ha
      have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 M)) :=
        FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 M)
      rw [hinj (ha.trans (map_zero _).symm)]
      exact P.zero_mem)
  haveI := h𝔔
  have h𝔔0 : 𝔔 ≠ ⊥ := by
    rintro rfl
    apply hP0
    rw [← h𝔔P]
    ext a
    simp only [Ideal.under_def, Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro ha
      exact FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 M) (ha.trans (map_zero _).symm)
    · rintro rfl; exact map_zero _
  haveI : Finite (𝓞 M ⧸ 𝔔) := Ring.HasFiniteQuotients.finiteQuotient h𝔔0
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 F) (M ≃ₐ[F] M) 𝔔
  -- lift `σ` to `h ∈ Gal(ℚ̄/ℚ)`
  obtain ⟨h, hres⟩ : ∃ h : Qbar ≃ₐ[ℚ] Qbar, AlgEquiv.restrictNormal h M = σ.restrictScalars ℚ :=
    ⟨(σ.restrictScalars ℚ).liftNormal Qbar, (σ.restrictScalars ℚ).restrict_liftNormal Qbar⟩
  have hσM : ∀ x : M, ((σ x : M) : Qbar) = h (x : Qbar) := by
    intro x
    have := AlgEquiv.restrictNormal_commutes h M x
    rw [hres] at this
    exact this
  have hσx : ∀ x : 𝓞 M, (((σ • x : 𝓞 M) : M) : Qbar) = h ((x : M) : Qbar) := by
    intro x
    rw [← hσM]
    change ((algebraMap (𝓞 M) M (galRestrict (𝓞 F) F M (𝓞 M) σ x) : M) : Qbar) = _
    rw [algebraMap_galRestrict_apply]
  have hfixF : ∀ x ∈ F, h x = x := by
    intro x hx
    have e1 := hσM (algebraMap F M ⟨x, hx⟩)
    rw [AlgEquiv.commutes] at e1
    exact e1.symm
  refine ⟨h, hfixF, ?_⟩
  intro d hd hd0 hK y
  apply frob_on_H4 F M hFM d hK (hHM d hd) h hfixF 𝔔 P hP0 hP2
  · intro a
    rw [← h𝔔P, Ideal.under_def, Ideal.mem_comap]
    rfl
  · intro x b hb
    have hσ' := hσ x
    have hu : 𝔔.under (𝓞 F) = P := h𝔔P
    have e2 : (((σ • x - x ^ Nat.card (𝓞 F ⧸ P) : 𝓞 M) : M) : Qbar) =
        h ((x : M) : Qbar) - ((x : M) : Qbar) ^ Nat.card (𝓞 F ⧸ P) := by
      rw [← hσx]
      push_cast
      rfl
    have e : b = σ • x - x ^ Nat.card (𝓞 F ⧸ P) :=
      RingOfIntegers.ext (Subtype.ext (hb.trans e2.symm))
    rw [e]
    have : (MulSemiringAction.toAlgHom (𝓞 F) (𝓞 M) σ) x = σ • x := rfl
    rw [← this, ← hu]
    exact hσ'

/-- **`SqrtTwoNotInHHprime` from `NormSigma` alone.** -/
theorem sqrtTwoNotInHHprime_of_normSigma (hN : NormSigma) : SqrtTwoNotInHHprime :=
  sqrtTwoNotInHHprime_of frobNormLaw hN

/-! ## §8. From the norm congruence `N(α) ≡ 1 ± 2√−d₀ (mod 4)` to `NormSigma` -/

section NormClass

variable {d : ℕ} [NeZero d]

theorem intCast_add_four_mul_mem (a : ℤ) (y : 𝓞 (QNeg d)) :
    ((a : 𝓞 (QNeg d)) + 4 * y) ∈ (O4 d).toRingOfIntegers := by
  rw [mem_toRingOfIntegers]
  refine ⟨a, y, ?_⟩
  push_cast
  rfl

theorem isCoprime_span_two_of_eq {x y : 𝓞 (QNeg d)} (h : x = 1 + 2 * y) :
    IsCoprime (Ideal.span {x}) (Ideal.span {(2 : 𝓞 (QNeg d))}) := by
  rw [Ideal.isCoprime_span_singleton_iff]
  exact ⟨1, -y, by rw [h]; ring⟩

theorem classOf_span_mul_eq_one {x y : 𝓞 (QNeg d)}
    (hx : IsCoprime (Ideal.span {x}) (Ideal.span {(2 : 𝓞 (QNeg d))}))
    (hy : IsCoprime (Ideal.span {y}) (Ideal.span {(2 : 𝓞 (QNeg d))}))
    (hxy : x * y ∈ (O4 d).toRingOfIntegers) :
    classOf (Ideal.span {x}) * classOf (Ideal.span {y}) = 1 := by
  have hmx := mem_primeTo_of_isCoprime_two hx
  have hmy := mem_primeTo_of_isCoprime_two hy
  rw [← classOf_mul hmx hmy, Ideal.span_singleton_mul_span_singleton,
    classOf_of_mem (by rw [← Ideal.span_singleton_mul_span_singleton]; exact Submonoid.mul_mem _ hmx hmy),
    picClass_eq_one_iff]
  exact ⟨x * y, hxy, rfl⟩

/-- **The class of `1 + 2ε√−d + 4γ` is `σ_{1+2ϖ}`** (`ε = ±1`, `d ≡ 5 (mod 8)`): its product with
`3 − 2ε√−d` lies in `ℤ + 4𝓞_K`, and `3 ∓ 2√−d` both have class `σ^{±1} = σ`. -/
theorem classOf_span_congr (hd : d % 8 = 5) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (γ : 𝓞 (QNeg d)) :
    classOf (Ideal.span {1 + 2 * (ε : 𝓞 (QNeg d)) * sqrtNeg d + 4 * γ}) = sigmaClass d := by
  have hε2 : (ε : 𝓞 (QNeg d)) * ε = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  set u := 1 + 2 * (ε : 𝓞 (QNeg d)) * sqrtNeg d + 4 * γ with hu
  set v := 3 - 2 * (ε : 𝓞 (QNeg d)) * sqrtNeg d with hv
  have hcu := isCoprime_span_two_of_eq (x := u) (y := ε * sqrtNeg d + 2 * γ) (by rw [hu]; ring)
  have hcv := isCoprime_span_two_of_eq (x := v) (y := 1 - ε * sqrtNeg d) (by rw [hv]; ring)
  have huv : u * v ∈ (O4 d).toRingOfIntegers := by
    have e : u * v = ((3 + 4 * (d : ℤ) : ℤ) : 𝓞 (QNeg d)) +
        4 * (ε * sqrtNeg d + γ * (3 - 2 * ε * sqrtNeg d)) := by
      rw [hu, hv]
      push_cast
      linear_combination (-4 : 𝓞 (QNeg d)) * (ε : 𝓞 (QNeg d)) * ε * sqrtNeg_mul_self (d := d) +
        (4 * (d : 𝓞 (QNeg d))) * hε2
    rw [e]; exact intCast_add_four_mul_mem _ _
  have h1 := classOf_span_mul_eq_one hcu hcv huv
  have hσ2 : sigmaClass d * sigmaClass d = 1 := by rw [← sq]; exact sigmaClass_sq
  have hσ : sigmaClass d = classOf (Ideal.span {alpha d}) := rfl
  have hca : IsCoprime (Ideal.span {alpha d}) (Ideal.span {(2 : 𝓞 (QNeg d))}) :=
    isCoprime_span_two_of_eq (y := 1 + sqrtNeg d) (by unfold alpha; ring)
  rcases hε with rfl | rfl
  · -- `v = 3 − 2√−d`, `v · α = 9 + 4d`
    have hva : v * alpha d ∈ (O4 d).toRingOfIntegers := by
      have e : v * alpha d = ((9 + 4 * (d : ℤ) : ℤ) : 𝓞 (QNeg d)) + 4 * 0 := by
        rw [hv]; unfold alpha; push_cast
        linear_combination (-4 : 𝓞 (QNeg d)) * sqrtNeg_mul_self (d := d)
      rw [e]; exact intCast_add_four_mul_mem _ _
    have h2 := classOf_span_mul_eq_one hcv hca hva
    rw [← hσ] at h2
    -- `cu * cv = 1` and `cv * σ = 1`, so `cu = σ`
    calc classOf (Ideal.span {u}) = classOf (Ideal.span {u}) * (classOf (Ideal.span {v}) * sigmaClass d) := by
          rw [h2, mul_one]
      _ = (classOf (Ideal.span {u}) * classOf (Ideal.span {v})) * sigmaClass d := by rw [mul_assoc]
      _ = sigmaClass d := by rw [h1, one_mul]
  · -- `v = 3 + 2√−d = α`
    have hva : v = alpha d := by rw [hv]; unfold alpha; push_cast; ring
    rw [hva, ← hσ] at h1
    calc classOf (Ideal.span {u}) = classOf (Ideal.span {u}) * (sigmaClass d * sigmaClass d) := by
          rw [hσ2, mul_one]
      _ = (classOf (Ideal.span {u}) * sigmaClass d) * sigmaClass d := by rw [mul_assoc]
      _ = sigmaClass d := by rw [h1, one_mul]

end NormClass

/-- **GLUE `NormCongr` (the norm congruence of Route A, step 1)**: for squarefree `n ≡ 5 (mod 8)` some
`α ∈ 𝓞_{L_n(i)}`, `α ≠ 0`, coprime to `2`, has `N_{L_n(i)/K_{d₀}}(α𝓞) = (1 + 2ε√−d₀ + 4γ)𝓞_{K_{d₀}}`
with `ε = ±1`, `γ ∈ 𝓞_{K_{d₀}}`, for every `d₀ ∣ n`, `d₀ ≡ 5 (mod 8)`. For
`α = 1 + 2i∏_{q∣n}(1 + √q*)/2`: `N(1 + 2β) ≡ 1 + 2 Tr(β) (mod 4)` and `Tr_{L_n(i)/K_{d₀}}(β) = ±√−d₀`
(`docs/research/tyz-318.md` §3.2). -/
def NormCongr : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ α : 𝓞 (Lni n), α ≠ 0 ∧ IsCoprime α 2 ∧
    ∀ d₀ ∈ n.divisors, d₀ % 8 = 5 → ∀ _ : NeZero d₀, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∃ γ : 𝓞 (QNeg d₀), relNormK (Lni n) d₀ (Ideal.span {α}) =
        Ideal.span {1 + 2 * (ε : 𝓞 (QNeg d₀)) * sqrtNeg d₀ + 4 * γ}

theorem normSigma_of (h : NormCongr) : NormSigma := by
  intro n hn hsq
  obtain ⟨α, hα0, hα2, hα⟩ := h n hn hsq
  refine ⟨α, hα0, hα2, ?_⟩
  intro d₀ hd₀ hd₀5 hd₀0
  obtain ⟨ε, hε, γ, hrel⟩ := hα d₀ hd₀ hd₀5 hd₀0
  rw [hrel]
  exact classOf_span_congr hd₀5 hε γ

/-- **`SqrtTwoNotInHHprime` from `NormCongr` alone.** -/
theorem sqrtTwoNotInHHprime_of_normCongr (h : NormCongr) : SqrtTwoNotInHHprime :=
  sqrtTwoNotInHHprime_of_normSigma (normSigma_of h)

/-! ## §9. Rational arithmetic for the multiquadratic field `L_n(i)` -/

section Arith

/-- `p* = ±p ≡ 1 (mod 4)` for an odd prime `p`. -/
def pstar (p : ℕ) : ℤ := if p % 4 = 1 then (p : ℤ) else -(p : ℤ)

theorem pstar_mod_four {p : ℕ} (hp : p % 2 = 1) : pstar p % 4 = 1 := by
  unfold pstar
  split_ifs with h
  · omega
  · omega

theorem pstar_eq_or (p : ℕ) : pstar p = p ∨ pstar p = -p := by
  unfold pstar; split_ifs <;> simp

/-- `p ∤ ∏_{q ∈ V} q*` for a prime `p ∉ V`, `V` a set of primes. -/
theorem not_dvd_prod_pstar (V : Finset ℕ) (hV : ∀ q ∈ V, q.Prime) {p : ℕ} (hp : p.Prime)
    (hpV : p ∉ V) : ¬ (p : ℤ) ∣ ∏ q ∈ V, pstar q := by
  intro h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨q, hq, hdvd⟩ := (Prime.dvd_finset_prod_iff hpZ _).mp h
  have hpq : (p : ℤ) ∣ (q : ℤ) := by
    rcases pstar_eq_or q with e | e <;> rw [e] at hdvd
    · exact hdvd
    · exact (dvd_neg).mp hdvd
  have : p = q := (Nat.prime_dvd_prime_iff_eq hp (hV q hq)).mp (Int.natCast_dvd_natCast.mp hpq)
  exact hpV (this ▸ hq)

/-- `p · r` with `p ∤ r` is not a rational square. -/
theorem not_sq_of_mul {p : ℕ} (hp : p.Prime) {r : ℤ} (hr : ¬ (p : ℤ) ∣ r) (q : ℚ) :
    (((p : ℤ) * r : ℤ) : ℚ) ≠ q ^ 2 := by
  intro h
  have hsq : IsSquare ((p : ℤ) * r) := Rat.isSquare_intCast_iff.mp ⟨q, by rw [h, sq]⟩
  obtain ⟨k, hk⟩ := hsq
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpk : (p : ℤ) ∣ k := by
    have : (p : ℤ) ∣ k * k := ⟨r, hk.symm⟩
    rcases hpZ.dvd_or_dvd this with h | h <;> exact h
  obtain ⟨j, rfl⟩ := hpk
  apply hr
  refine ⟨j * j, ?_⟩
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  apply mul_left_cancel₀ hp0
  rw [hk]; ring

/-- `∏_{p ∣ d} p* = d` for squarefree `d ≡ 1 (mod 4)`. -/
theorem prod_pstar_primeFactors {d : ℕ} (hsq : Squarefree d) (hd : d % 4 = 1) :
    ∏ p ∈ d.primeFactors, pstar p = d := by
  have hsgn : ∀ p, pstar p = (if p % 4 = 1 then 1 else -1) * (p : ℤ) := by
    intro p; unfold pstar; split_ifs <;> simp
  have hprod : ∏ p ∈ d.primeFactors, pstar p =
      (∏ p ∈ d.primeFactors, (if p % 4 = 1 then (1 : ℤ) else -1)) * d := by
    rw [Finset.prod_congr rfl (fun p _ => hsgn p), Finset.prod_mul_distrib]
    congr 1
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  have hS : (∏ p ∈ d.primeFactors, (if p % 4 = 1 then (1 : ℤ) else -1)) = 1 ∨
      (∏ p ∈ d.primeFactors, (if p % 4 = 1 then (1 : ℤ) else -1)) = -1 := by
    apply Finset.prod_induction _ (fun x => x = 1 ∨ x = -1)
    · rintro a b (rfl | rfl) (rfl | rfl) <;> simp
    · simp
    · intro p _; split_ifs <;> simp
  have hmod : (∏ p ∈ d.primeFactors, pstar p) % 4 = 1 := by
    apply Finset.prod_induction _ (fun x : ℤ => x % 4 = 1)
    · intro a b ha hb; rw [Int.mul_emod, ha, hb]; rfl
    · rfl
    · intro p hp
      apply pstar_mod_four
      have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
      rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd with h2 | h2
      · subst h2; obtain ⟨k, rfl⟩ := hpd; omega
      · exact h2
  rcases hS with h | h
  · rw [hprod, h, one_mul]
  · rw [hprod, h] at hmod ⊢
    exfalso
    have : ((d : ℤ)) % 4 = 1 := by exact_mod_cast hd
    omega

end Arith

/-! ## §10. Traces of square roots and degrees of multiquadratic fields -/

section TraceSq

open Polynomial

/-- `Tr_{L/K}(x) = 0` if `x² ∈ K` and `x ∉ K`. -/
theorem trace_eq_zero_of_sq {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    {x : L} {c : K} (hx : x ^ 2 = algebraMap K L c) (hxK : x ∉ (algebraMap K L).range) :
    Algebra.trace K L x = 0 := by
  have hint : IsIntegral K x := .of_finite K x
  have hmin : minpoly K x = X ^ 2 - C c := by
    have hdvd : minpoly K x ∣ X ^ 2 - C c := minpoly.dvd K x (by simp [hx])
    have hmon : (X ^ 2 - C c : K[X]).Monic := monic_X_pow_sub_C c two_ne_zero
    have hdeg : (X ^ 2 - C c : K[X]).natDegree = 2 := natDegree_X_pow_sub_C
    have h2 := (minpoly.two_le_natDegree_iff hint).mpr hxK
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmon hdvd
      (by rw [hdeg]; exact h2)).symm
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin, Polynomial.nextCoeff, natDegree_X_pow_sub_C]
  simp

/-- `[ℚ(T) : ℚ] ≤ 2^{#T}` for a finite set `T` of elements with rational squares. -/
theorem finrank_adjoin_sq_le {E : Type*} [Field E] [Algebra ℚ E] (T : Finset E)
    (hT : ∀ t ∈ T, ∃ c : ℚ, t ^ 2 = algebraMap ℚ E c) :
    FiniteDimensional ℚ (IntermediateField.adjoin ℚ (T : Set E)) ∧
      Module.finrank ℚ (IntermediateField.adjoin ℚ (T : Set E)) ≤ 2 ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.coe_empty, IntermediateField.adjoin_empty, Finset.card_empty, pow_zero]
    refine ⟨inferInstance, ?_⟩
    rw [IntermediateField.finrank_bot]
  | insert a T haT ih =>
    obtain ⟨hfd, hle⟩ := ih (fun t ht => hT t (Finset.mem_insert_of_mem ht))
    obtain ⟨c, hc⟩ := hT a (Finset.mem_insert_self a T)
    have hint : IsIntegral ℚ a := by
      refine ⟨X ^ 2 - C c, monic_X_pow_sub_C c two_ne_zero, ?_⟩
      simp [hc]
    have hdeg : Module.finrank ℚ (IntermediateField.adjoin ℚ ({a} : Set E)) ≤ 2 := by
      rw [IntermediateField.adjoin.finrank hint]
      have hdvd : minpoly ℚ a ∣ X ^ 2 - C c := minpoly.dvd ℚ a (by simp [hc])
      have := Polynomial.natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero two_pos c)
      rwa [natDegree_X_pow_sub_C] at this
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ ({a} : Set E)) :=
      IntermediateField.adjoin.finiteDimensional hint
    haveI := hfd
    have heq : IntermediateField.adjoin ℚ ((insert a T : Finset E) : Set E) =
        IntermediateField.adjoin ℚ ({a} : Set E) ⊔ IntermediateField.adjoin ℚ (T : Set E) := by
      rw [Finset.coe_insert, Set.insert_eq, IntermediateField.adjoin_union]
    rw [heq, Finset.card_insert_of_notMem haT]
    refine ⟨inferInstance, ?_⟩
    calc Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({a} : Set E) ⊔ IntermediateField.adjoin ℚ (T : Set E))
        ≤ Module.finrank ℚ (IntermediateField.adjoin ℚ ({a} : Set E)) *
          Module.finrank ℚ (IntermediateField.adjoin ℚ (T : Set E)) :=
          IntermediateField.finrank_sup_le _ _
      _ ≤ 2 * 2 ^ T.card := Nat.mul_le_mul hdeg hle
      _ = 2 ^ (T.card + 1) := by ring

end TraceSq

/-! ## §11. `N(1 + 2β) ≡ 1 + 2 Tr(β) (mod 4)` and traces of sums of square roots -/

section NormTrace

/-- `∏ (1 + 2 f_i) = 1 + 2 Σ f_i + 4 Z` with `Z` integral over `ℤ`. -/
theorem prod_one_add_two {E ι : Type*} [CommRing E] (s : Finset ι) (f : ι → E)
    (hf : ∀ i ∈ s, IsIntegral ℤ (f i)) :
    ∃ Z : E, IsIntegral ℤ Z ∧ ∏ i ∈ s, (1 + 2 * f i) = 1 + 2 * ∑ i ∈ s, f i + 4 * Z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, isIntegral_zero, by simp⟩
  | insert a s has ih =>
    obtain ⟨Z, hZ, hprod⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have ha := hf a (Finset.mem_insert_self a s)
    have hS : IsIntegral ℤ (∑ i ∈ s, f i) :=
      IsIntegral.sum _ (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨Z + f a * ∑ i ∈ s, f i + (f a * Z + f a * Z), ?_, ?_⟩
    · exact (hZ.add (ha.mul hS)).add ((ha.mul hZ).add (ha.mul hZ))
    · rw [Finset.prod_insert has, Finset.sum_insert has, hprod]
      ring

/-- **`N_{F/K}(1 + 2β) = 1 + 2 Tr_{F/K}(β) + 4γ`** with `γ ∈ K` integral over `ℤ`, for `β` integral. -/
theorem norm_one_add_two_mul {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F] (β : F) (hβ : IsIntegral ℤ β) :
    ∃ γ : K, IsIntegral ℤ γ ∧ Algebra.norm K (1 + 2 * β) = 1 + 2 * Algebra.trace K F β + 4 * γ := by
  let E := AlgebraicClosure K
  have hN := Algebra.norm_eq_prod_embeddings K E (1 + 2 * β)
  have hT := trace_eq_sum_embeddings E (K := K) (L := F) (x := β)
  obtain ⟨Z, hZ, hprod⟩ := prod_one_add_two (Finset.univ : Finset (F →ₐ[K] E))
    (fun σ => σ β) (fun σ _ => hβ.map σ)
  have h4K : (4 : K) ≠ 0 := by norm_num
  set γ : K := (Algebra.norm K (1 + 2 * β) - 1 - 2 * Algebra.trace K F β) / 4 with hγ
  refine ⟨γ, ?_, by rw [hγ, mul_div_cancel₀ _ h4K]; ring⟩
  have hγE : algebraMap K E γ * 4 = Z * 4 := by
    have e1 : ∏ σ : F →ₐ[K] E, σ (1 + 2 * β) = ∏ σ : F →ₐ[K] E, (1 + 2 * σ β) := by
      apply Finset.prod_congr rfl; intro σ _; rw [map_add, map_mul, map_one, map_ofNat]
    have e2 : γ * 4 = Algebra.norm K (1 + 2 * β) - 1 - 2 * Algebra.trace K F β := by
      rw [hγ, div_mul_cancel₀ _ h4K]
    have e3 := congrArg (algebraMap K E) e2
    rw [map_mul, map_ofNat, map_sub, map_sub, map_mul, map_one, map_ofNat, hN, hT, e1, hprod] at e3
    rw [e3]; ring
  have h4E : (4 : E) ≠ 0 := by
    rw [show (4 : E) = algebraMap K E 4 by rw [map_ofNat]]
    exact (map_ne_zero _).mpr h4K
  have hγZ : algebraMap K E γ = Z := mul_right_cancel₀ h4E hγE
  have : IsIntegral ℤ (algebraMap K E γ) := hγZ ▸ hZ
  exact isIntegral_algebraMap_iff.mp this

/-- **Trace of a sum of square roots**: if `x_{i₀} ∈ K` and every other `x_i` has `x_i² ∈ K`,
`x_i ∉ K`, then `Tr(c Σ x_i) = c [F:K] x_{i₀}`. -/
theorem trace_sum_sq {K F ι : Type*} [Field K] [Field F] [Algebra K F] [FiniteDimensional K F]
    (I : Finset ι) (x : ι → F) (i₀ : ι) (hi₀ : i₀ ∈ I) (k₀ : K) (hx₀ : x i₀ = algebraMap K F k₀)
    (hx : ∀ i ∈ I, i ≠ i₀ → (∃ c : K, x i ^ 2 = algebraMap K F c) ∧ x i ∉ (algebraMap K F).range)
    (c : K) :
    Algebra.trace K F (algebraMap K F c * ∑ i ∈ I, x i) = c * (Module.finrank K F • k₀) := by
  rw [← Algebra.smul_def, map_smul, map_sum, Finset.sum_eq_single i₀]
  · rw [hx₀, Algebra.trace_algebraMap, smul_eq_mul]
  · intro i hi hne
    obtain ⟨⟨c', hc'⟩, hnot⟩ := hx i hi hne
    exact trace_eq_zero_of_sq hc' hnot
  · intro h; exact absurd hi₀ h

end NormTrace

/-! ## §12. The element `α = 1 + 2i∏_{q∣n}(1 + √q*)/2` of `L_n(i)` -/

section Multiquad

open Polynomial

/-- A chosen square root of `p` in `ℚ̄`. -/
def sqrtQ (p : ℕ) : Qbar := (IsAlgClosed.exists_pow_nat_eq (p : Qbar) two_pos).choose

theorem sqrtQ_sq (p : ℕ) : sqrtQ p ^ 2 = (p : Qbar) :=
  (IsAlgClosed.exists_pow_nat_eq (p : Qbar) two_pos).choose_spec

/-- `√(p*)`, `p* = ±p ≡ 1 (mod 4)`. -/
def sQ (p : ℕ) : Qbar := if p % 4 = 1 then sqrtQ p else iQ * sqrtQ p

theorem sQ_sq (p : ℕ) : sQ p ^ 2 = ((pstar p : ℤ) : Qbar) := by
  unfold sQ pstar
  split_ifs with h
  · rw [sqrtQ_sq]; push_cast; rfl
  · rw [mul_pow, iQ_sq, sqrtQ_sq]; push_cast; ring

theorem sqrtQ_mem {n p : ℕ} (hp : p ∈ n.primeFactors) : sqrtQ p ∈ Lni n :=
  IntermediateField.subset_adjoin _ _ (Or.inr ⟨p, hp, sqrtQ_sq p⟩)

theorem sQ_mem {n p : ℕ} (hp : p ∈ n.primeFactors) : sQ p ∈ Lni n := by
  unfold sQ
  split_ifs
  · exact sqrtQ_mem hp
  · exact (Lni n).mul_mem (ZInQ.Contrib.TYZGenus.Package.iQ_mem_Lni n) (sqrtQ_mem hp)

/-- `x_S = i ∏_{p ∈ S} √(p*)`. -/
def xS (S : Finset ℕ) : Qbar := iQ * ∏ p ∈ S, sQ p

theorem xS_sq (S : Finset ℕ) : xS S ^ 2 = -((∏ p ∈ S, pstar p : ℤ) : Qbar) := by
  unfold xS
  rw [mul_pow, iQ_sq, ← Finset.prod_pow, Finset.prod_congr rfl (fun p _ => sQ_sq p)]
  push_cast; ring

theorem xS_mem {n : ℕ} {S : Finset ℕ} (hS : S ⊆ n.primeFactors) : xS S ∈ Lni n :=
  (Lni n).mul_mem (ZInQ.Contrib.TYZGenus.Package.iQ_mem_Lni n)
    ((Lni n).prod_mem fun p hp => sQ_mem (hS hp))

/-- `β = i ∏_{p ∣ n} (1 + √(p*))/2`. -/
def betaQ (n : ℕ) : Qbar := iQ * ∏ p ∈ n.primeFactors, (1 + sQ p) / 2

theorem betaQ_mem (n : ℕ) : betaQ n ∈ Lni n := by
  unfold betaQ
  refine (Lni n).mul_mem (ZInQ.Contrib.TYZGenus.Package.iQ_mem_Lni n) ((Lni n).prod_mem fun p hp => ?_)
  exact (Lni n).div_mem ((Lni n).add_mem (Lni n).one_mem (sQ_mem hp)) (by
    have := (Lni n).algebraMap_mem (2 : ℚ); simpa using this)

theorem betaQ_eq (n : ℕ) : betaQ n =
    (1 / 2 : Qbar) ^ n.primeFactors.card * ∑ S ∈ n.primeFactors.powerset, xS S := by
  unfold betaQ xS
  have h1 : ∏ p ∈ n.primeFactors, (1 + sQ p) / 2 =
      (1 / 2 : Qbar) ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (sQ p + 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro p _; ring
  rw [h1, Finset.prod_add (fun p => sQ p) (fun _ => (1 : Qbar))]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro S _; ring

theorem isIntegral_half_one_add_sQ {p : ℕ} (hp : p % 2 = 1) : IsIntegral ℤ ((1 + sQ p) / 2) := by
  obtain ⟨c, hc⟩ : ∃ c : ℤ, pstar p = 4 * c + 1 := ⟨pstar p / 4, by have := pstar_mod_four hp; omega⟩
  refine ⟨X ^ 2 - (X + C c), monic_X_pow_sub (by
    calc degree (X + C c : ℤ[X]) = 1 := degree_X_add_C c
      _ < 2 := by norm_num), ?_⟩
  have hs := sQ_sq p
  rw [hc] at hs
  simp only [eval₂_sub, eval₂_X_pow, eval₂_add, eval₂_X]
  have hcc : eval₂ (algebraMap ℤ Qbar) ((1 + sQ p) / 2) (C c) = (c : Qbar) := by
    rw [eval₂_C]; simp
  push_cast at hs ⊢
  rw [hcc]
  linear_combination hs / 4

theorem isIntegral_iQ : IsIntegral ℤ iQ := by
  refine ⟨X ^ 2 + 1, by monicity!, ?_⟩
  simp [iQ_sq]

theorem isIntegral_betaQ {n : ℕ} (hn : n % 2 = 1) : IsIntegral ℤ (betaQ n) := by
  unfold betaQ
  refine isIntegral_iQ.mul (IsIntegral.prod _ fun p hp => isIntegral_half_one_add_sQ ?_)
  have hpn := Nat.dvd_of_mem_primeFactors hp
  rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd with h2 | h2
  · subst h2; obtain ⟨k, rfl⟩ := hpn; omega
  · exact h2

/-- One prime appearing once makes `±∏_U p* · ∏_V p*` a non-square. -/
theorem prod_pstar_not_sq {U V : Finset ℕ} (hU : ∀ q ∈ U, q.Prime) (hV : ∀ q ∈ V, q.Prime) {p : ℕ}
    (hpU : p ∈ U) (hpV : p ∉ V) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (q : ℚ) :
    ((σ * ((∏ x ∈ U, pstar x) * ∏ x ∈ V, pstar x) : ℤ) : ℚ) ≠ q ^ 2 := by
  have hp := hU p hpU
  obtain ⟨τ, hτ, hpτ⟩ : ∃ τ : ℤ, (τ = 1 ∨ τ = -1) ∧ pstar p = τ * p := by
    rcases pstar_eq_or p with e | e
    · exact ⟨1, Or.inl rfl, by rw [e]; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [e]; ring⟩
  have e : σ * ((∏ x ∈ U, pstar x) * ∏ x ∈ V, pstar x) =
      (p : ℤ) * (σ * τ * ((∏ x ∈ U.erase p, pstar x) * ∏ x ∈ V, pstar x)) := by
    rw [← Finset.mul_prod_erase U _ hpU, hpτ]; ring
  rw [e]
  apply not_sq_of_mul hp
  intro hdvd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hστ : IsUnit (σ * τ) := by
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> simp
  rw [hστ.dvd_mul_left] at hdvd
  rcases hpZ.dvd_or_dvd hdvd with h | h
  · exact not_dvd_prod_pstar (U.erase p) (fun q hq => hU q (Finset.mem_of_mem_erase hq)) hp
      (Finset.notMem_erase p U) h
  · exact not_dvd_prod_pstar V hV hp hpV h

/-- `kEmb d₀ (k) ≠ x_S` unless `S` is the set of primes of `d₀`. -/
theorem kEmb_ne_xS {n d₀ : ℕ} [NeZero d₀] (hsq : Squarefree n) (hd : d₀ ∣ n) (hd4 : d₀ % 4 = 1)
    {S : Finset ℕ} (hS : S ⊆ n.primeFactors) (hSD : S ≠ d₀.primeFactors) (k : QNeg d₀) :
    kEmb d₀ k ≠ xS S := by
  intro hk
  have hsqd : Squarefree d₀ := hsq.squarefree_of_dvd hd
  have hSp : ∀ q ∈ S, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (hS hq)
  have hDp : ∀ q ∈ d₀.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  set w := kEmb d₀ QuadraticAlgebra.omega with hw
  have hw2 : w ^ 2 = -(d₀ : Qbar) := by
    rw [hw, ← map_pow, sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]; simp
  have hkk : k = algebraMap ℚ (QNeg d₀) k.re + algebraMap ℚ (QNeg d₀) k.im * QuadraticAlgebra.omega := by
    ext <;> simp
  set a := k.re; set b := k.im
  have hk' : algebraMap ℚ Qbar a + algebraMap ℚ Qbar b * w = xS S := by
    rw [← hk, hkk, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]
  set c : ℤ := ∏ p ∈ S, pstar p with hc
  have hsq2 : (algebraMap ℚ Qbar a + algebraMap ℚ Qbar b * w) ^ 2 = -((c : ℤ) : Qbar) := by
    rw [hk', xS_sq]
  -- `(a² − d₀ b² + c) + 2ab w = 0`
  have hlin : algebraMap ℚ Qbar (a ^ 2 - d₀ * b ^ 2 + c) + algebraMap ℚ Qbar (2 * a * b) * w = 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_intCast, map_ofNat]
    linear_combination hsq2 - (algebraMap ℚ Qbar b) ^ 2 * hw2
  -- `w ∉ ℚ`
  have hab : 2 * a * b = 0 := by
    by_contra hne
    have h2ab : algebraMap ℚ Qbar (2 * a * b) ≠ 0 := (_root_.map_ne_zero _).mpr hne
    have hwq : w = algebraMap ℚ Qbar (-(a ^ 2 - d₀ * b ^ 2 + c) / (2 * a * b)) := by
      rw [map_div₀, map_neg, eq_div_iff h2ab]
      linear_combination hlin
    have h2 : algebraMap ℚ Qbar ((-(a ^ 2 - d₀ * b ^ 2 + c) / (2 * a * b)) ^ 2) =
        algebraMap ℚ Qbar (-(d₀ : ℚ)) := by
      rw [map_pow, ← hwq, hw2, map_neg, map_natCast]
    have h3 := (algebraMap ℚ Qbar).injective h2
    have h4 : (0 : ℚ) ≤ (-(a ^ 2 - d₀ * b ^ 2 + c) / (2 * a * b)) ^ 2 := sq_nonneg _
    rw [h3] at h4
    have : (0 : ℚ) < d₀ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d₀)
    linarith
  have hrat : a ^ 2 - d₀ * b ^ 2 + c = 0 := by
    rw [hab, map_zero, zero_mul, add_zero] at hlin
    exact (algebraMap ℚ Qbar).injective (hlin.trans (map_zero _).symm)
  rcases mul_eq_zero.mp hab with h | hb
  · rcases mul_eq_zero.mp h with h | ha
    · norm_num at h
    · -- `a = 0`: `∏_S p* = d₀ b²`, so `∏_S p* ∏_{D₀} p* = (d₀ b)²`
      rw [ha] at hrat
      have hd0' : (∏ p ∈ d₀.primeFactors, ((pstar p : ℤ) : ℚ)) = d₀ := by
        have := prod_pstar_primeFactors hsqd hd4
        exact_mod_cast this
      have hc' : (∏ p ∈ S, ((pstar p : ℤ) : ℚ)) = d₀ * b ^ 2 := by
        have : ((c : ℤ) : ℚ) = d₀ * b ^ 2 := by linarith
        rw [hc] at this; exact_mod_cast this
      have key : (((1 : ℤ) * ((∏ x ∈ S, pstar x) * ∏ x ∈ d₀.primeFactors, pstar x) : ℤ) : ℚ) =
          ((d₀ : ℚ) * b) ^ 2 := by
        push_cast
        rw [hd0', hc']; ring
      by_cases h1 : ∃ p ∈ S, p ∉ d₀.primeFactors
      · obtain ⟨p, hpS, hpD⟩ := h1
        exact prod_pstar_not_sq hSp hDp hpS hpD (Or.inl rfl) _ key
      · push_neg at h1
        have h2 : ∃ p ∈ d₀.primeFactors, p ∉ S := by
          by_contra h2; push_neg at h2
          exact hSD (Finset.Subset.antisymm h1 h2)
        obtain ⟨p, hpD, hpS⟩ := h2
        rw [mul_comm (∏ x ∈ S, pstar x)] at key
        exact prod_pstar_not_sq hDp hSp hpD hpS (Or.inl rfl) _ key
  · -- `b = 0`: `a² = −∏_S p*`
    rw [hb] at hrat
    by_cases hS0 : S = ∅
    · rw [hc, hS0, Finset.prod_empty] at hrat
      norm_num at hrat
      nlinarith [sq_nonneg a]
    · obtain ⟨p, hpS⟩ := Finset.nonempty_iff_ne_empty.mpr hS0
      have hc' : (∏ p ∈ S, ((pstar p : ℤ) : ℚ)) = -a ^ 2 := by
        have : ((c : ℤ) : ℚ) = -a ^ 2 := by linarith
        rw [hc] at this; exact_mod_cast this
      have key : (((-1 : ℤ) * ((∏ x ∈ S, pstar x) * ∏ x ∈ (∅ : Finset ℕ), pstar x) : ℤ) : ℚ) =
          a ^ 2 := by
        rw [Finset.prod_empty, mul_one]; push_cast
        rw [hc']; ring
      exact prod_pstar_not_sq hSp (by simp) hpS (Finset.notMem_empty p) (Or.inr rfl) _ key


theorem finrank_Lni_le {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) :
    Module.finrank ℚ (Lni n) ≤ 2 ^ (n.primeFactors.card + 1) := by
  classical
  set T : Finset Qbar := insert iQ (n.primeFactors.image sqrtQ) with hT
  have hTsq : ∀ t ∈ T, ∃ c : ℚ, t ^ 2 = algebraMap ℚ Qbar c := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact ⟨-1, by rw [iQ_sq]; simp⟩
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp ht
      exact ⟨p, by rw [sqrtQ_sq]; simp⟩
  obtain ⟨hfd, hle⟩ := finrank_adjoin_sq_le T hTsq
  have hsub : Lni n ≤ IntermediateField.adjoin ℚ (T : Set Qbar) := by
    rw [Lni, IntermediateField.adjoin_le_iff]
    rintro x (hx | ⟨p, hp, hx⟩)
    · have hx' : x ^ 2 = iQ ^ 2 := by rw [iQ_sq]; exact hx
      have hi : iQ ∈ IntermediateField.adjoin ℚ (T : Set Qbar) :=
        IntermediateField.subset_adjoin _ _ (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx' with e | e
      · rw [e]; exact hi
      · rw [e]; exact (IntermediateField.adjoin ℚ (T : Set Qbar)).neg_mem hi
    · have hx' : x ^ 2 = sqrtQ p ^ 2 := by rw [sqrtQ_sq]; exact hx
      have hi : sqrtQ p ∈ IntermediateField.adjoin ℚ (T : Set Qbar) :=
        IntermediateField.subset_adjoin _ _
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)))
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx' with e | e
      · rw [e]; exact hi
      · rw [e]; exact (IntermediateField.adjoin ℚ (T : Set Qbar)).neg_mem hi
  haveI := hfd
  calc Module.finrank ℚ (Lni n) ≤ Module.finrank ℚ (IntermediateField.adjoin ℚ (T : Set Qbar)) :=
        IntermediateField.finrank_le_of_le_right hsub
    _ ≤ 2 ^ T.card := hle
    _ ≤ 2 ^ (n.primeFactors.card + 1) :=
        Nat.pow_le_pow_right two_pos ((Finset.card_insert_le _ _).trans
          (Nat.succ_le_succ Finset.card_image_le))

/-- **The norm congruence at one `d₀`**: `N_{L_n(i)/K_{d₀}}(α𝓞) = (1 + 2ε√−d₀ + 4γ)𝓞_{K_{d₀}}`. -/
theorem normCongr_at {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n) {d₀ : ℕ} [NeZero d₀]
    (hd : d₀ ∈ n.divisors) (hd5 : d₀ % 8 = 5) (αO : 𝓞 (Lni n))
    (hα : ((αO : Lni n) : Qbar) = 1 + 2 * betaQ n) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∃ γ : 𝓞 (QNeg d₀), relNormK (Lni n) d₀ (Ideal.span {αO}) =
      Ideal.span {1 + 2 * (ε : 𝓞 (QNeg d₀)) * sqrtNeg d₀ + 4 * γ} := by
  haveI hFD : FiniteDimensional ℚ (Lni n) := finiteDimensional_Lni hn hsq
  haveI : NumberField (Lni n) := ⟨⟩
  have hdn : d₀ ∣ n := Nat.dvd_of_mem_divisors hd
  have hK := kEmb_mem_Lni (d₀ := d₀) hsq hdn
  letI : Algebra (QNeg d₀) (Lni n) := (iotaK (Lni n) d₀ hK).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (QNeg d₀) (Lni n) :=
    IsScalarTower.of_algebraMap_eq (fun q => ((iotaK (Lni n) d₀ hK).commutes q).symm)
  haveI : FiniteDimensional (QNeg d₀) (Lni n) :=
    Module.Finite.of_restrictScalars_finite ℚ (QNeg d₀) (Lni n)
  have hval : ∀ k : QNeg d₀, ((algebraMap (QNeg d₀) (Lni n) k : Lni n) : Qbar) = kEmb d₀ k :=
    fun k => rfl
  set P := n.primeFactors with hP
  set r := P.card with hr
  have hD₀P : d₀.primeFactors ⊆ P := Nat.primeFactors_mono hdn (by omega)
  have hd4 : d₀ % 4 = 1 := by omega
  -- the elements `x_S` and `β` of `F`
  let xF : Finset ℕ → Lni n := fun S => if h : S ⊆ P then ⟨xS S, xS_mem h⟩ else 0
  have hxF : ∀ S ∈ P.powerset, ((xF S : Lni n) : Qbar) = xS S := fun S hS => by
    simp only [xF, dif_pos (Finset.mem_powerset.mp hS)]
  set βF : Lni n := ⟨betaQ n, betaQ_mem n⟩ with hβFdef
  have hβF : βF = algebraMap (QNeg d₀) (Lni n) (algebraMap ℚ (QNeg d₀) ((1 / 2) ^ r)) *
      ∑ S ∈ P.powerset, xF S := by
    apply Subtype.ext
    show betaQ n = (((algebraMap (QNeg d₀) (Lni n) (algebraMap ℚ (QNeg d₀) ((1 / 2) ^ r)) *
      ∑ S ∈ P.powerset, xF S : Lni n)) : Qbar)
    rw [IntermediateField.coe_mul, hval, AlgHom.commutes]
    have hsum : ((∑ S ∈ P.powerset, xF S : Lni n) : Qbar) = ∑ S ∈ P.powerset, ((xF S : Lni n) : Qbar) :=
      map_sum (Lni n).val xF P.powerset
    rw [hsum, Finset.sum_congr rfl hxF, betaQ_eq]
    simp only [one_div, inv_pow, map_pow, map_inv₀, map_ofNat]
    rfl
  -- `x_{D₀} = ε √−d₀`
  have hw2 : (kEmb d₀ QuadraticAlgebra.omega) ^ 2 = -(d₀ : Qbar) := by
    rw [← map_pow, sq, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]; simp
  have hxD : xS d₀.primeFactors ^ 2 = (kEmb d₀ QuadraticAlgebra.omega) ^ 2 := by
    rw [xS_sq, hw2, prod_pstar_primeFactors (hsq.squarefree_of_dvd hdn) hd4]; push_cast; ring
  obtain ⟨ε, hε, hxDε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      xS d₀.primeFactors = kEmb d₀ ((ε : QNeg d₀) * QuadraticAlgebra.omega) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxD with e | e
    · exact ⟨1, Or.inl rfl, by rw [e]; simp⟩
    · exact ⟨-1, Or.inr rfl, by rw [e]; simp⟩
  -- the trace of `β`
  set N := Module.finrank (QNeg d₀) (Lni n) with hN
  have htr : Algebra.trace (QNeg d₀) (Lni n) βF = algebraMap ℚ (QNeg d₀) ((1 / 2) ^ r) *
      (N • ((ε : QNeg d₀) * QuadraticAlgebra.omega)) := by
    rw [hβF]
    apply trace_sum_sq P.powerset xF d₀.primeFactors (Finset.mem_powerset.mpr hD₀P)
    · apply Subtype.ext
      rw [hxF _ (Finset.mem_powerset.mpr hD₀P), hval, hxDε]
    · intro S hS hSD
      refine ⟨⟨algebraMap ℚ (QNeg d₀) (-((∏ p ∈ S, pstar p : ℤ) : ℚ)), ?_⟩, ?_⟩
      · apply Subtype.ext
        rw [IntermediateField.coe_pow, hxF S hS, xS_sq, hval, AlgHom.commutes, map_neg, map_intCast]
      · rintro ⟨k, hk⟩
        have h1 : ((algebraMap (QNeg d₀) (Lni n) k : Lni n) : Qbar) = ((xF S : Lni n) : Qbar) :=
          congrArg Subtype.val hk
        rw [hval, hxF S hS] at h1
        exact kEmb_ne_xS hsq hdn hd4 (Finset.mem_powerset.mp hS) hSD k h1
  -- integrality
  have hβint : IsIntegral ℤ βF := by
    have h1 : IsIntegral ℤ (algebraMap (Lni n) Qbar βF) := isIntegral_betaQ (by omega)
    exact isIntegral_algebraMap_iff.mp h1
  have htrint : IsIntegral ℤ (Algebra.trace (QNeg d₀) (Lni n) βF) := Algebra.isIntegral_trace hβint
  -- `[F : K_{d₀}] = 2^r`
  have hNle : N ≤ 2 ^ r := by
    have h1 := finrank_Lni_le hn hsq
    rw [← hP, ← hr] at h1
    have h2 := Module.finrank_mul_finrank ℚ (QNeg d₀) (Lni n)
    rw [QuadraticAlgebra.finrank_eq_two] at h2
    rw [← h2, pow_succ] at h1
    omega
  have hε2 : (ε : ℚ) ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hNdvd : 2 ^ r ∣ N := by
    set c : ℚ := (1 / 2) ^ r * N * ε with hc
    have hy : Algebra.trace (QNeg d₀) (Lni n) βF = algebraMap ℚ (QNeg d₀) c * QuadraticAlgebra.omega := by
      rw [htr, nsmul_eq_mul, hc, map_mul, map_mul, map_natCast, map_intCast]; ring
    have hy2 : (Algebra.trace (QNeg d₀) (Lni n) βF) ^ 2 =
        algebraMap ℚ (QNeg d₀) (-(d₀ : ℚ) * c ^ 2) := by
      rw [hy, mul_pow, sq QuadraticAlgebra.omega, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
      simp only [map_mul, map_neg, map_pow, map_natCast, map_zero, zero_mul, mul_zero, add_zero,
        zero_smul]
      ring
    have hint2 : IsIntegral ℤ (algebraMap ℚ (QNeg d₀) (-(d₀ : ℚ) * c ^ 2)) := hy2 ▸ htrint.pow 2
    have hint3 : IsIntegral ℤ (-(d₀ : ℚ) * c ^ 2) := isIntegral_algebraMap_iff.mp hint2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint3
    have hm' : (m : ℚ) = -(d₀ : ℚ) * c ^ 2 := by rw [← hm]; simp
    have h2r : ((1 : ℚ) / 2) ^ r * 2 ^ r = 1 := by rw [← mul_pow]; norm_num
    have hq : (m : ℚ) * 4 ^ r = -((d₀ : ℚ) * (N : ℚ) ^ 2) := by
      have h4 : (4 : ℚ) ^ r = (2 ^ r) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [hm', h4, hc]
      calc -(d₀ : ℚ) * ((1 / 2) ^ r * N * ε) ^ 2 * (2 ^ r) ^ 2 =
          -(d₀ : ℚ) * N ^ 2 * ε ^ 2 * ((1 / 2) ^ r * 2 ^ r) ^ 2 := by ring
        _ = -((d₀ : ℚ) * (N : ℚ) ^ 2) := by rw [hε2, h2r]; ring
    have hz : m * 4 ^ r = -((d₀ : ℤ) * (N : ℤ) ^ 2) := by exact_mod_cast hq
    have hdvdZ : ((4 ^ r : ℕ) : ℤ) ∣ ((d₀ * N ^ 2 : ℕ) : ℤ) := ⟨-m, by push_cast; linarith⟩
    have hdvdN : 4 ^ r ∣ d₀ * N ^ 2 := Int.natCast_dvd_natCast.mp hdvdZ
    have hcop : Nat.Coprime (4 ^ r) d₀ := by
      apply Nat.Coprime.pow_left
      have : Nat.Coprime 2 d₀ := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))
      have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h4]; exact Nat.Coprime.pow_left 2 this
    have h1 : 4 ^ r ∣ N ^ 2 := hcop.dvd_of_dvd_mul_left hdvdN
    have h2 : (2 ^ r) ^ 2 ∣ N ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num; exact h1
    exact (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).mp h2
  have hNeq : N = 2 ^ r := le_antisymm hNle (Nat.le_of_dvd Module.finrank_pos hNdvd)
  have htr' : Algebra.trace (QNeg d₀) (Lni n) βF = (ε : QNeg d₀) * QuadraticAlgebra.omega := by
    rw [htr, hNeq, nsmul_eq_mul, ← mul_assoc]
    have : algebraMap ℚ (QNeg d₀) ((1 / 2) ^ r) * ((2 ^ r : ℕ) : QNeg d₀) = 1 := by
      rw [← map_natCast (algebraMap ℚ (QNeg d₀)), ← map_mul]
      push_cast
      rw [← mul_pow]; norm_num
    rw [this, one_mul]
  -- the norm
  obtain ⟨γK, hγint, hnorm⟩ := norm_one_add_two_mul (K := QNeg d₀) βF hβint
  obtain ⟨γ, hγ⟩ : ∃ γ : 𝓞 (QNeg d₀), algebraMap (𝓞 (QNeg d₀)) (QNeg d₀) γ = γK :=
    ⟨⟨γK, hγint⟩, rfl⟩
  refine ⟨ε, hε, γ, ?_⟩
  simp only [relNormK, dif_pos (And.intro hK hFD)]
  rw [Ideal.relNorm_singleton]
  have hαF : algebraMap (𝓞 (Lni n)) (Lni n) αO = 1 + 2 * βF := by
    apply Subtype.ext
    show ((αO : Lni n) : Qbar) = _
    rw [hα]; push_cast; rfl
  have key : Algebra.intNorm (𝓞 (QNeg d₀)) (𝓞 (Lni n)) αO =
      1 + 2 * (ε : 𝓞 (QNeg d₀)) * sqrtNeg d₀ + 4 * γ := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (QNeg d₀)) (QNeg d₀)
    rw [Algebra.algebraMap_intNorm (K := QNeg d₀) (L := Lni n), hαF, hnorm, htr']
    have e1 : algebraMap (𝓞 (QNeg d₀)) (QNeg d₀) (sqrtNeg d₀) = QuadraticAlgebra.omega := rfl
    rw [map_add, map_add, map_mul, map_mul, map_mul, map_one, map_ofNat, map_ofNat, map_intCast,
      e1, hγ]
    ring
  rw [key]

end Multiquad

/-! ## §13. `NormCongr`, `NormSigma`, `SigmaLift` and `SqrtTwoNotInHHprime` hold -/

/-- `β ∈ 𝓞_{L_n(i)}` for odd `n`. -/
def betaO (n : ℕ) (hn : n % 2 = 1) : 𝓞 (Lni n) :=
  ⟨⟨betaQ n, betaQ_mem n⟩, (isIntegral_algebraMap_iff (B := Qbar)).mp (isIntegral_betaQ hn)⟩

theorem coe_betaO (n : ℕ) (hn : n % 2 = 1) : (((betaO n hn : 𝓞 (Lni n)) : Lni n) : Qbar) = betaQ n :=
  rfl

/-- **`NormCongr` holds**, with `α = 1 + 2β`, `β = i∏_{q∣n}(1 + √q*)/2`. -/
theorem normCongr : NormCongr := by
  intro n hn hsq
  have hn2 : n % 2 = 1 := by omega
  set βO := betaO n hn2 with hβO
  have h22 : (((2 : 𝓞 (Lni n)) : Lni n) : Qbar) = 2 := by
    have : ((2 : 𝓞 (Lni n)) : Lni n) = 2 := map_ofNat (algebraMap (𝓞 (Lni n)) (Lni n)) 2
    rw [this]; exact map_ofNat (Lni n).val 2
  refine ⟨1 + 2 * βO, ?_, ⟨1, -βO, by ring⟩, ?_⟩
  · intro h0
    have h1 : (((1 + 2 * βO : 𝓞 (Lni n)) : Lni n) : Qbar) = 0 := by rw [h0]; rfl
    push_cast at h1
    rw [h22, hβO, coe_betaO] at h1
    have h2 : betaQ n = algebraMap ℚ Qbar (-1 / 2) := by
      rw [map_div₀, map_neg, map_one, map_ofNat]; linear_combination h1 / 2
    have h3 : IsIntegral ℤ (algebraMap ℚ Qbar (-1 / 2)) := h2 ▸ isIntegral_betaQ hn2
    have h4 : IsIntegral ℤ ((-1 / 2 : ℚ)) := isIntegral_algebraMap_iff.mp h3
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp h4
    have hm' : (m : ℚ) * 2 = -1 := by
      have : (m : ℚ) = -1 / 2 := by rw [← hm]; simp
      rw [this]; norm_num
    have : m * 2 = -1 := by exact_mod_cast hm'
    omega
  · intro d₀ hd₀ hd₀5 hd₀0
    apply normCongr_at hn hsq hd₀ hd₀5
    push_cast
    rw [h22, hβO, coe_betaO]

theorem normSigma : NormSigma := normSigma_of normCongr

theorem sigmaLift : SigmaLift := sigmaLift_of frobNormLaw normSigma

/-- **`√2 ∉ ℍ'_n` (`SqrtTwoNotInHHprime`), proved** (no hypotheses). -/
theorem sqrtTwoNotInHHprime : SqrtTwoNotInHHprime := sqrtTwoNotInHHprime_of_sigmaLift sigmaLift

end ZInQ.Contrib.TYZGenus.Sqrt2Glue


/-! ## §C. The combination -/

namespace ZInQ.Contrib.TYZGenus.Sqrt2Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.RingClass ZInQ.RouteK.Rank5b

/-- The two copies of the glue Prop agree. -/
theorem sqrtTwoNotInHHprime_eq : T318.SqrtTwoNotInHHprime = SqrtTwoNotInHHprime := rfl

/-- **TYZ Lemma `torsion2` (Lemma 3.18), `Lemma318Literal HHprime` verbatim, unconditionally.** -/
theorem lemma318Literal_HHprime : T318.Lemma318Literal HHprime :=
  T318.lemma318Literal_HHprime_of_sqrtTwoNotIn sqrtTwoNotInHHprime

/-- The same for the kernel's `Package.Lemma318Literal` (the hypothesis `h318` of cm-bridge). -/
theorem package_lemma318Literal_HHprime : Package.Lemma318Literal HHprime :=
  T318.package_lemma318Literal_HHprime_of_sqrtTwoNotIn sqrtTwoNotInHHprime

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.Package in
/-- **`RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD` with `h318` discharged.** -/
theorem tyzThm35ReadingA_of_cmLeaves_ringClassD_no318 (h11 : TYZThm11Integral)
    (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hcm : ZInQ.Contrib.TYZGenus.CM.CMFieldOfDefinition ringClassFieldD)
    (hs : TYZSigmaFixesZn)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  RingClassBridge.tyzThm35ReadingA_of_cmLeaves_ringClassD h11 h1 h29 hcm hs
    package_lemma318Literal_HHprime hG

end ZInQ.Contrib.TYZGenus.Sqrt2Glue

#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.sqrtTwoNotInHHprime
#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.lemma318Literal_HHprime
#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.package_lemma318Literal_HHprime
#print axioms ZInQ.Contrib.TYZGenus.Sqrt2Glue.tyzThm35ReadingA_of_cmLeaves_ringClassD_no318
