import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.BuzzardLeaves
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.OrderMod
import ZInQKernel.Contrib.OneProof.Y3FullThreeRepZ30.FrameRep3
import ZInQKernel.Contrib.OneProof.BuzzardFrameRepTorsor5.Defs
import Mathlib

/-!
# Injectivity of the quaternionic action on a false elliptic curve

The structure `FEC S` does not ask the action `ι : O → End(A)` to be injective, while
K. Buzzard, Duke Math. J. 87 (1997), §1, asks for an injective ring homomorphism
`O ↪ End_S(A)`. This file shows that injectivity is automatic.

* `iota_injective`: over a nonempty `Z[1/30]`-scheme, `ι` is injective, given Milne's count of
  torsion points at geometric points (`MilneRem84`).
* `iota_eq_of_isEmpty`: over the empty scheme, `A` is empty, so all maps `ι(a)` agree.

Outline of the proof of `iota_injective`.
1. By `iota_add`, `a ↦ ι(a)` turns sums into products in the group of endomorphisms of `A`
   over `S`, so `ι(a) = ι(b)` gives `ι(a - b) = 1`.
2. If `ι(x) = 1` with `x ≠ 0`, let `x̄` be the conjugate of `x`; it lies in `O`. By `iota_mul`,
   `ι(x x̄) = ι(x̄) ≫ ι(x) = 1`, and `x x̄ = nrd(x)` is a nonzero integer `N`, because the norm
   form `a² - 2b² + 3c² - 6d²` of `B = (2, -3)_ℚ` is anisotropic (descent modulo 3).
3. `ι(N)` is the `N`-th power map, so every point `P` of `A` satisfies `P ^ |N| = 1`.
4. At a geometric point of characteristic `p`, choose a prime `ℓ` with `ℓ > |N|` and `ℓ > p`.
   An `ℓ`-torsion point is also `|N|`-torsion, hence trivial, so there is exactly one
   `ℓ`-torsion point, while Milne's count gives `ℓ ^ 4 > 1` of them.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV

namespace Y3Buzzard

attribute [local instance] FEC.grp

/-! ## The norm form of `B` is anisotropic -/

/-- Modulo 3, `x² - 2y² = x² + y²` vanishes only at `x = y = 0`. -/
theorem iotaInj_zmod3 : ∀ x y : ZMod 3, x ^ 2 - 2 * y ^ 2 = 0 → x = 0 ∧ y = 0 := by
  decide

/-- If `a² - 2b²` is divisible by 3, then so are `a` and `b`. -/
theorem iotaInj_dvd3 {a b c : ℤ} (h : a ^ 2 - 2 * b ^ 2 = 3 * c) : 3 ∣ a ∧ 3 ∣ b := by
  have h' : ((a : ZMod 3)) ^ 2 - 2 * ((b : ZMod 3)) ^ 2 = 0 := by
    have h3 := congrArg (Int.cast : ℤ → ZMod 3) h
    push_cast at h3
    rw [h3]
    have e : (3 : ZMod 3) = 0 := rfl
    rw [e, zero_mul]
  obtain ⟨ha, hb⟩ := iotaInj_zmod3 _ _ h'
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).1 ha, (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).1 hb⟩

/-- Descent modulo 3, by strong induction on `|a| + |b| + |c| + |d|`: a solution of
`a² - 2b² + 3c² - 6d² = 0` has `3 ∣ a, b`, then `3 ∣ c, d`, and dividing by 3 gives a smaller
solution. -/
theorem iotaInj_form_aux : ∀ (s : ℕ) (a b c d : ℤ),
    a.natAbs + b.natAbs + c.natAbs + d.natAbs = s →
    a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro a b c d hs h
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ :=
      iotaInj_dvd3 (a := a) (b := b) (c := 2 * d ^ 2 - c ^ 2) (by linear_combination h)
    have h1 : c ^ 2 - 2 * d ^ 2 = 3 * (2 * b' ^ 2 - a' ^ 2) := by linarith
    obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ := iotaInj_dvd3 h1
    have h2 : a' ^ 2 - 2 * b' ^ 2 + 3 * c' ^ 2 - 6 * d' ^ 2 = 0 := by linarith
    simp only [Int.natAbs_mul] at hs
    norm_num at hs
    by_cases hs0 : s = 0
    · have ha : a'.natAbs = 0 := by omega
      have hb : b'.natAbs = 0 := by omega
      have hc : c'.natAbs = 0 := by omega
      have hd : d'.natAbs = 0 := by omega
      simp only [Int.natAbs_eq_zero] at ha hb hc hd
      subst ha hb hc hd
      simp
    · obtain ⟨ha, hb, hc, hd⟩ := ih (a'.natAbs + b'.natAbs + c'.natAbs + d'.natAbs) (by omega)
        a' b' c' d' rfl h2
      subst ha hb hc hd
      simp

/-- A nonzero `x = n₀ + n₁ i + n₂ (1+j)/2 + n₃ (i+k)/2` of `O` times its conjugate
`x̄ = (n₀ + n₂) - n₁ i - n₂ (1+j)/2 - n₃ (i+k)/2`, which lies in `O`, is the nonzero integer
`nrd(x) = n₀² + n₀n₂ + n₂² - 2(n₁² + n₁n₃ + n₃²)`. Four times it is the norm form at
`(2n₀ + n₂, 2n₁ + n₃, n₂, n₃)`. -/
theorem iotaInj_conj (x : O) (hx : x ≠ 0) : ∃ (y : O) (N : ℤ), N ≠ 0 ∧ x * y = (N : O) := by
  obtain ⟨n, hn⟩ := Y3OrderMod.exists_ofInt x
  refine ⟨⟨ofInt ![n 0 + n 2, -n 1, -n 2, -n 3], Y3OrderMod.ofInt_mem _⟩,
    n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2), ?_, ?_⟩
  · intro hN
    apply hx
    obtain ⟨h0, h1, h2, h3⟩ := iotaInj_form_aux _ (2 * n 0 + n 2) (2 * n 1 + n 3) (n 2) (n 3) rfl
      (by linear_combination 4 * hN)
    have e0 : n 0 = 0 := by omega
    have e1 : n 1 = 0 := by omega
    apply Subtype.ext
    rw [hn]
    ext <;> simp [ofInt, e0, e1, h2, h3]
  · apply Subtype.ext
    change (x : B) * ofInt ![n 0 + n 2, -n 1, -n 2, -n 3] = _
    rw [hn, SubringClass.coe_intCast]
    ext <;> simp only [QuaternionAlgebra.re_intCast, QuaternionAlgebra.imI_intCast,
      QuaternionAlgebra.imJ_intCast, QuaternionAlgebra.imK_intCast] <;> simp [ofInt] <;> ring

/-! ## The action in the group of endomorphisms -/

section Helpers

variable {S : Scheme.{0}} (A : FEC S)

/-- Step 1: `ι(a) = ι(b)` gives `ι(a - b) = 1`, since `ι(a) = ι(a - b) · ι(b)` by `iota_add`. -/
theorem iotaInj_homMk_sub {a b : O} (h : A.iota a = A.iota b) :
    (Over.homMk (A.iota (a - b)) (A.iota_over _) : A.F ⟶ A.F) = 1 := by
  have h1 := A.iota_add (a - b) b
  have h2 : (Over.homMk (A.iota (a - b + b)) (A.iota_over _) : A.F ⟶ A.F) =
      Over.homMk (A.iota b) (A.iota_over b) :=
    Over.OverMorphism.ext (by simp [h])
  rw [h2] at h1
  exact mul_eq_right.1 h1.symm

/-- Step 2: if `ι(x) = 1`, then `ι(x y) = ι(y) ≫ ι(x) = 1` by `iota_mul`. -/
theorem iotaInj_homMk_mul (x y : O)
    (hx : (Over.homMk (A.iota x) (A.iota_over x) : A.F ⟶ A.F) = 1) :
    (Over.homMk (A.iota (x * y)) (A.iota_over _) : A.F ⟶ A.F) = 1 := by
  have e : (Over.homMk (A.iota (x * y)) (A.iota_over _) : A.F ⟶ A.F) =
      (Over.homMk (A.iota y) (A.iota_over y) : A.F ⟶ A.F) ≫
        Over.homMk (A.iota x) (A.iota_over x) :=
    Over.OverMorphism.ext (by simp [A.iota_mul])
  rw [e, hx, MonObj.comp_one]

/-- Step 3: if `ι(N) = 1` for an integer `N`, then every point `P` satisfies `P ^ |N| = 1`,
since `ι(n)` is the `n`-th power map for `n : ℕ` and `ι(N) ι(|N|) = ι(0) = 1` when `N < 0`. -/
theorem iotaInj_pow_natAbs {U : Over S} (P : U ⟶ A.F) (N : ℤ)
    (hN : (Over.homMk (A.iota (N : O)) (A.iota_over _) : A.F ⟶ A.F) = 1) :
    P ^ N.natAbs = 1 := by
  have hP : P ≫ (Over.homMk (A.iota (N : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 := by
    rw [hN, MonObj.comp_one]
  rcases Int.natAbs_eq N with h | h
  · have e : ((N.natAbs : ℕ) : O) = (N : O) := by rw [← Int.cast_natCast, ← h]
    rw [← comp_iotaHom_natCast A P N.natAbs, e]
    exact hP
  · have h0 : (N : O) + ((N.natAbs : ℕ) : O) = ((0 : ℕ) : O) := by
      have e : N + (N.natAbs : ℤ) = 0 := by omega
      rw [Nat.cast_zero, ← Int.cast_natCast, ← Int.cast_add, e, Int.cast_zero]
    have key := comp_iota_add A P (N : O) ((N.natAbs : ℕ) : O)
    rw [h0, comp_iotaHom_natCast, comp_iotaHom_natCast, hP, _root_.one_mul,
      _root_.pow_zero] at key
    exact key.symm

end Helpers

/-! ## Injectivity -/

/-- Step 4: over a nonempty base, `ι(x) = 1` forces `x = 0`. -/
theorem iotaInj_eq_zero (hR : MilneRem84) (S : Over Z30Base) (A : FEC S.left) [Nonempty S.left]
    {x : O} (hx : (Over.homMk (A.iota x) (A.iota_over x) : A.F ⟶ A.F) = 1) : x = 0 := by
  by_contra hx0
  obtain ⟨y, N, hN0, hxy⟩ := iotaInj_conj x hx0
  have hN : (Over.homMk (A.iota (N : O)) (A.iota_over _) : A.F ⟶ A.F) = 1 := by
    have h := iotaInj_homMk_mul A x y hx
    rw [hxy] at h
    exact h
  obtain ⟨t⟩ := ‹Nonempty S.left›
  have hm : 0 < N.natAbs := Int.natAbs_pos.2 hN0
  obtain ⟨ℓ, hℓ, hℓp⟩ := Nat.exists_infinite_primes (N.natAbs + ringChar (geomK t) + 1)
  have hℓk : (ℓ : geomK t) ≠ 0 := by
    intro h0
    rcases hℓp.eq_one_or_self_of_dvd _ ((ringChar.spec (geomK t) ℓ).1 h0) with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · omega
  have hcop : Nat.Coprime N.natAbs ℓ :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓp).2
      (Nat.not_dvd_of_pos_of_lt hm (by omega)))
  have hcard := hR S A (geomK t) (geomPt t) ℓ hℓk
  have key : ∀ P : {P : Over.mk (geomPt t) ⟶ A.F // P ^ ℓ = 1}, P.1 = 1 := by
    rintro ⟨P, hP⟩
    have h1 : P ^ (N.natAbs.gcd ℓ) = 1 := pow_gcd_eq_one.2 ⟨iotaInj_pow_natAbs A P N hN, hP⟩
    rw [hcop.gcd_eq_one, _root_.pow_one] at h1
    exact h1
  have hsub : Subsingleton {P : Over.mk (geomPt t) ⟶ A.F // P ^ ℓ = 1} :=
    ⟨fun P Q => Subtype.ext ((key P).trans (key Q).symm)⟩
  have h1 : Nat.card {P : Over.mk (geomPt t) ⟶ A.F // P ^ ℓ = 1} = 1 :=
    Nat.card_of_subsingleton ⟨1, _root_.one_pow ℓ⟩
  have h2 : 1 = ℓ ^ 4 := h1.symm.trans hcard
  have h16 : 2 ^ 4 ≤ ℓ ^ 4 := Nat.pow_le_pow_left hℓp.two_le 4
  rw [← h2] at h16
  norm_num at h16

/-- Over a nonempty `Z[1/30]`-scheme the action `ι : O → End(A)` of a false elliptic curve is
injective, given Milne's count of torsion points at geometric points. So `FEC` agrees with
Buzzard's definition, which asks for an injective `ι`. -/
theorem iota_injective (hR : MilneRem84) (S : Over Z30Base) (A : FEC S.left) [Nonempty S.left] :
    Function.Injective A.iota := by
  intro a b hab
  exact sub_eq_zero.1 (iotaInj_eq_zero hR S A (iotaInj_homMk_sub A hab))

/-- Over the empty scheme, `A` has no points, so it is an initial object and any two of its
endomorphisms agree: here `ι` is not injective, which is why `iota_injective` asks for a
nonempty base. -/
theorem iota_eq_of_isEmpty {X : Scheme.{0}} (A : FEC X) [IsEmpty X] (a b : O) :
    A.iota a = A.iota b := by
  have : IsEmpty A.F.left := ⟨fun p => IsEmpty.false (A.F.hom p)⟩
  exact isInitialOfIsEmpty.hom_ext _ _

end Y3Buzzard
