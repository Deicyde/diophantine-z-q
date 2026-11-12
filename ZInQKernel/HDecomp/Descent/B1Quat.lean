import Mathlib

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-descent/B1Quat.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-descent: the quaternion algebra of B1 (N5 L637-644)

N5's `B = (2, -3)` is Mathlib's `ℍ[ℚ, 2, -3] = QuaternionAlgebra ℚ 2 0 (-3)` (`i² = 2`,
`j² = -3`, `ij = -ji = k`).

* `B6_commute_i_j`: an element commuting with `i` and `j` is a rational scalar. This is the step
  "`c(σ,τ)` commutes with `B`, hence belongs to `ℚ^×`" (N5 L640-644), given `End⁰(A_ℚ̄) = B`.
* `B6_isCentral`: `Algebra.IsCentral ℚ B6`.
* `LeafSkolemNoether`: the Skolem–Noether theorem (automorphism case) over Mathlib's central
  simple algebras, the literature input of B1 (Reiner, *Maximal orders*, Thm 7.21; formalized in
  Tau Ceti, not in Mathlib v4.35).
-/

namespace GlueDescent

open Quaternion

/-- N5's quaternion algebra `B = (2, -3)` of discriminant 6. -/
abbrev B6 := ℍ[ℚ, 2, -3]

/-- `i ∈ B`. -/
def qi : B6 := ⟨0, 1, 0, 0⟩
/-- `j ∈ B`. -/
def qj : B6 := ⟨0, 0, 1, 0⟩

/-- **B1, the discrepancy is a scalar.** An element of `B` commuting with `i` and `j` lies in `ℚ`.
  -/
theorem B6_commute_i_j (x : B6) (hi : x * qi = qi * x) (hj : x * qj = qj * x) :
    x = algebraMap ℚ B6 x.re := by
  have e1 := congrArg QuaternionAlgebra.imI hi
  have e2 := congrArg QuaternionAlgebra.imJ hi
  have e3 := congrArg QuaternionAlgebra.imK hi
  have f1 := congrArg QuaternionAlgebra.imI hj
  have f2 := congrArg QuaternionAlgebra.imJ hj
  have f3 := congrArg QuaternionAlgebra.imK hj
  simp [qi, qj, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul] at e1 e2 e3 f1 f2 f3
  ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> linarith

/-- `B` is central over `ℚ`. -/
instance B6_isCentral : Algebra.IsCentral ℚ B6 where
  out x hx := by
    rw [Subalgebra.mem_center_iff] at hx
    exact ⟨x.re, (B6_commute_i_j x (hx qi).symm (hx qj).symm).symm⟩

/-- **Leaf L-B1 (Skolem–Noether, automorphism case).** Every `K`-algebra automorphism of a
finite-dimensional central simple `K`-algebra is inner. -/
def LeafSkolemNoether : Prop :=
  ∀ (K : Type) [Field K] (A : Type) [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] [FiniteDimensional K A] (φ : A ≃ₐ[K] A),
    ∃ u : Aˣ, ∀ a : A, φ a = u * a * (u⁻¹ : Aˣ)

/-! ### `B` is a division algebra, hence simple (so `LeafSkolemNoether` applies to it) -/

theorem zmod3_aniso : ∀ x y : ZMod 3, x ^ 2 - 2 * y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide

theorem three_dvd_of_form {a b e : ℤ} (h : a ^ 2 - 2 * b ^ 2 + 3 * e = 0) : 3 ∣ a ∧ 3 ∣ b := by
  have h3 : ((a : ZMod 3)) ^ 2 - 2 * (b : ZMod 3) ^ 2 = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod 3)) h
    push_cast at this
    have h30 : (3 : ZMod 3) = 0 := by decide
    rw [h30, zero_mul, add_zero] at this
    exact this
  obtain ⟨ha, hb⟩ := zmod3_aniso _ _ h3
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp
      hb⟩

/-- The norm form `a² - 2b² + 3c² - 6d²` of `B` is anisotropic over `ℤ` (descent mod 3). -/
theorem aniso_int : ∀ (n : ℕ) (a b c d : ℤ), a.natAbs + b.natAbs + c.natAbs + d.natAbs ≤ n →
    a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b c d hn h
  obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ :=
    three_dvd_of_form (a := a) (b := b) (e := c ^ 2 - 2 * d ^ 2) (by linear_combination h)
  have h' : c ^ 2 - 2 * d ^ 2 + 3 * (a' ^ 2 - 2 * b' ^ 2) = 0 := by
    have : (3 : ℤ) * (c ^ 2 - 2 * d ^ 2 + 3 * (a' ^ 2 - 2 * b' ^ 2)) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ := three_dvd_of_form (a := c) (b := d) h'
  have h'' : a' ^ 2 - 2 * b' ^ 2 + 3 * c' ^ 2 - 6 * d' ^ 2 = 0 := by
    have : (9 : ℤ) * (a' ^ 2 - 2 * b' ^ 2 + 3 * c' ^ 2 - 6 * d' ^ 2) = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  by_cases hz : a' = 0 ∧ b' = 0 ∧ c' = 0 ∧ d' = 0
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hz; simp
  · exfalso
    apply hz
    have hsum : a'.natAbs + b'.natAbs + c'.natAbs + d'.natAbs < n := by
      simp only [Int.natAbs_mul, show (3 : ℤ).natAbs = 3 from rfl] at hn
      have : 0 < a'.natAbs + b'.natAbs + c'.natAbs + d'.natAbs := by
        by_contra h0
        apply hz
        omega
      omega
    exact ih _ hsum a' b' c' d' le_rfl h''

/-- Anisotropy over `ℚ`. -/
theorem aniso_rat (a b c d : ℚ) (h : a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  set D : ℚ := (a.den : ℚ) * b.den * c.den * d.den with hD
  have hD0 : D ≠ 0 := by positivity
  have hnum : ∀ q : ℚ, (q.num : ℚ) = q * q.den := fun q =>
    (div_eq_iff (by positivity)).mp (Rat.num_div_den q)
  have ha : a * D = ((a.num * (b.den * c.den * d.den) : ℤ) : ℚ) := by
    push_cast; rw [hD, hnum a]; ring
  have hb : b * D = ((b.num * (a.den * c.den * d.den) : ℤ) : ℚ) := by
    push_cast; rw [hD, hnum b]; ring
  have hc : c * D = ((c.num * (a.den * b.den * d.den) : ℤ) : ℚ) := by
    push_cast; rw [hD, hnum c]; ring
  have hd : d * D = ((d.num * (a.den * b.den * c.den) : ℤ) : ℚ) := by
    push_cast; rw [hD, hnum d]; ring
  set A := a.num * (b.den * c.den * d.den)
  set B := b.num * (a.den * c.den * d.den)
  set C := c.num * (a.den * b.den * d.den)
  set E := d.num * (a.den * b.den * c.den)
  have hint : A ^ 2 - 2 * B ^ 2 + 3 * C ^ 2 - 6 * E ^ 2 = 0 := by
    have : ((A ^ 2 - 2 * B ^ 2 + 3 * C ^ 2 - 6 * E ^ 2 : ℤ) : ℚ) = 0 := by
      push_cast
      rw [← ha, ← hb, ← hc, ← hd]
      linear_combination D ^ 2 * h
    exact_mod_cast this
  obtain ⟨h1, h2, h3, h4⟩ := aniso_int _ A B C E le_rfl hint
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := ha; rw [h1] at this; push_cast at this; exact (mul_eq_zero.mp this).resolve_right hD0
  · have := hb; rw [h2] at this; push_cast at this; exact (mul_eq_zero.mp this).resolve_right hD0
  · have := hc; rw [h3] at this; push_cast at this; exact (mul_eq_zero.mp this).resolve_right hD0
  · have := hd; rw [h4] at this; push_cast at this; exact (mul_eq_zero.mp this).resolve_right hD0

/-- `star x * x` is the scalar `x.re² - 2 x.imI² + 3 x.imJ² - 6 x.imK²`. -/
theorem B6_star_mul (x : B6) :
    star x * x = algebraMap ℚ B6 (x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2) := by
  rw [QuaternionAlgebra.star_mul_eq_coe]
  congr 1
  simp [QuaternionAlgebra.re_mul]
  ring

/-- **`B` is simple** (it is a division algebra: the norm form is anisotropic). -/
instance B6_isSimpleRing : IsSimpleRing B6 := by
  rw [isSimpleRing_iff_isTwoSided_imp]
  refine ⟨inferInstance, fun I _ => ?_⟩
  by_cases hI : I = ⊥
  · exact Or.inl hI
  · right
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hmem : star x * x ∈ I := I.mul_mem_left _ hxI
    rw [B6_star_mul] at hmem
    set n := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2
    have hn : n ≠ 0 := by
      intro h0
      obtain ⟨h1, h2, h3, h4⟩ := aniso_rat _ _ _ _ h0
      exact hx0 (QuaternionAlgebra.ext h1 h2 h3 h4)
    exact Ideal.eq_top_of_isUnit_mem I hmem
      ((IsUnit.mk0 n hn).map (algebraMap ℚ B6))

/-- **B1, Skolem–Noether at `B`**: from the leaf, every `ℚ`-automorphism of `B` is inner. -/
theorem B6_inner (hSN : LeafSkolemNoether) (φ : B6 ≃ₐ[ℚ] B6) :
    ∃ u : B6ˣ, ∀ a : B6, φ a = u * a * (u⁻¹ : B6ˣ) :=
  hSN ℚ B6 φ

end GlueDescent

