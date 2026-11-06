import ZInQKernel.Compiler.Precision.JacobianGenerator
import ZInQKernel.Compiler.Precision.ZCoordinate

/-!
# Scalar multiplication by halving

Blueprint: `compiler/natural/precision/jacobian-scalar-multiplication.md`.

`jmulLoop A Π Θ e` is the loop with state `(Π, Θ, e)`: while `e > 0`, if `e` is odd replace `Π`
by `Π ⊕ Θ`; replace `Θ` by `dbl*(Θ)` and `e` by `⌊e/2⌋`; return `Π`. It terminates because `e`
halves. `jmul k` runs it from `(O, P₀ᴶ, k)` for `k ≥ 0` and negates `jmul (-k)` for `k < 0`; its
value is a Jacobian representative of `[k]P₀` satisfying `𝓔 = 0`.
-/

namespace ZInQ.Compiler.Precision

open JTriple WeierstrassCurve WeierstrassCurve.Affine

section Loop

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- The halving loop of scalar multiplication. -/
def jmulLoop (A : R) (acc base : JTriple R) (e : ℕ) : JTriple R :=
  if h : e = 0 then acc
  else jmulLoop A (if e % 2 = 1 then jaddB A acc base else acc) (jdblB A base) (e / 2)
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by norm_num)

theorem jmulLoop_zero (A : R) (acc base : JTriple R) : jmulLoop A acc base 0 = acc := by
  rw [jmulLoop, dite_eq_left rfl]

theorem jmulLoop_of_ne_zero (A : R) (acc base : JTriple R) {e : ℕ} (he : e ≠ 0) :
    jmulLoop A acc base e =
      jmulLoop A (if e % 2 = 1 then jaddB A acc base else acc) (jdblB A base) (e / 2) := by
  rw [jmulLoop, dite_eq_right he]

theorem curveE_jmulLoop {A : R} (e : ℕ) {acc base : JTriple R} (h1 : curveE A acc = 0)
    (h2 : curveE A base = 0) : curveE A (jmulLoop A acc base e) = 0 := by
  induction e using Nat.strong_induction_on generalizing acc base with
  | _ e ih =>
    rcases eq_or_ne e 0 with rfl | he
    · rwa [jmulLoop_zero]
    · rw [jmulLoop_of_ne_zero A acc base he]
      refine ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by norm_num)) ?_ (curveE_jdblB h2)
      split_ifs
      · exact curveE_jaddB h1 h2
      · exact h1

theorem map_jmulLoop {S : Type*} [CommRing S] [DecidableEq S] {f : R →+* S}
    (hf : Function.Injective f) (A : R) (e : ℕ) (acc base : JTriple R) :
    (jmulLoop A acc base e).map f = jmulLoop (f A) (acc.map f) (base.map f) e := by
  induction e using Nat.strong_induction_on generalizing acc base with
  | _ e ih =>
    rcases eq_or_ne e 0 with rfl | he
    · rw [jmulLoop_zero, jmulLoop_zero]
    · rw [jmulLoop_of_ne_zero _ _ _ he, jmulLoop_of_ne_zero _ _ _ he,
        ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero he) (by norm_num)), map_jdblB hf]
      congr 1
      split_ifs
      · exact map_jaddB hf A acc base
      · rfl

end Loop

/-- The loop invariant: if `Π, Θ` represent `π, θ`, the loop returns a representative of
`π + [e]θ`. -/
theorem rep_jmulLoop {F : Type*} [Field F] [DecidableEq F] [NeZero (2 : F)] {A : F} (e : ℕ)
    {acc base : JTriple F} {π θ : (shortCurve A).toAffine.Point} (h1 : Rep A acc π)
    (h2 : Rep A base θ) : Rep A (jmulLoop A acc base e) (π + e • θ) := by
  induction e using Nat.strong_induction_on generalizing acc base π θ with
  | _ e ih =>
    rcases eq_or_ne e 0 with rfl | he
    · rwa [jmulLoop_zero, zero_nsmul, add_zero]
    · rw [jmulLoop_of_ne_zero A acc base he]
      have hlt := Nat.div_lt_self (Nat.pos_of_ne_zero he) (by norm_num : 1 < 2)
      have hdbl := rep_jdblB h2
      have hsplit : e • θ = (e % 2) • θ + (e / 2) • (θ + θ) := by
        rw [← two_nsmul, ← mul_nsmul', ← add_nsmul, Nat.mod_add_div' e 2]
      rw [hsplit, ← add_assoc]
      split_ifs with hodd
      · rw [hodd, one_nsmul]
        exact ih _ hlt (rep_jaddB h1 h2) hdbl
      · rw [show e % 2 = 0 by omega, zero_nsmul, add_zero]
        exact ih _ hlt h1 hdbl

/-! ### Scalar multiples of the fixed point -/

/-- `mul(k)` for `k ∈ ℕ`: the loop from `(O, P₀ᴶ, k)`. -/
def jmulNat (k : ℕ) : JTriple Zs := jmulLoop Acoef jO P0J k

/-- `mul(k)` for `k ∈ ℤ`; negative `k` negates `mul(-k)`. -/
def jmul (k : ℤ) : JTriple Zs := if 0 ≤ k then jmulNat k.toNat else jneg (jmulNat (-k).toNat)

theorem curveE_jmulNat (k : ℕ) : curveE Acoef (jmulNat k) = 0 :=
  curveE_jmulLoop k (curveE_jO Acoef) curveE_P0J

/-- `mul(k)` satisfies `𝓔 = 0`. -/
theorem curveE_jmul (k : ℤ) : curveE Acoef (jmul k) = 0 := by
  unfold jmul; split_ifs
  · exact curveE_jmulNat _
  · rw [curveE_jneg]; exact curveE_jmulNat _

theorem rep_jmulNat (k : ℕ) : Rep (-genD ^ 2) ((jmulNat k).map Zs.toK0) (k • genP0) := by
  rw [jmulNat, map_jmulLoop Zs.toK0_injective, toK0_Acoef, map_jO]
  have := rep_jmulLoop k (rep_jO (-genD ^ 2)) rep_P0J
  exact this.congr_point (zero_add _)

/-- **Scalar multiplication by halving**: `mul(k)` is a Jacobian representative of `[k]P₀`. -/
theorem rep_jmul (k : ℤ) : Rep (-genD ^ 2) ((jmul k).map Zs.toK0) (k • genP0) := by
  unfold jmul; split_ifs with hk
  · have := rep_jmulNat k.toNat
    rwa [← natCast_zsmul, Int.toNat_of_nonneg hk] at this
  · have := rep_jneg (rep_jmulNat (-k).toNat)
    rw [← map_jneg] at this
    refine this.congr_point ?_
    exact (by rw [← natCast_zsmul, Int.toNat_of_nonneg (by omega), neg_zsmul, neg_neg] :
      -(((-k).toNat : ℕ) • genP0) = k • genP0)

/-- `[k]P₀ = O` exactly when the third coordinate of `mul(k)` vanishes. -/
theorem jmul_Z_eq_zero_iff (k : ℤ) : (jmul k).Z = 0 ↔ k • genP0 = 0 := by
  exact (map_eq_zero_iff _ Zs.toK0_injective).symm.trans (rep_jmul k).eq_zero_iff.symm

/-- For `Z ≠ 0`, `[k]P₀` is the affine point `(X/Z², Y/Z³)` of the image of `mul(k)` in `K₀`. -/
theorem jmul_eq_some {k : ℤ} (hZ : (jmul k).Z ≠ 0) :
    ∃ h : genCurve.toAffine.Nonsingular (Zs.toK0 (jmul k).X / Zs.toK0 (jmul k).Z ^ 2)
      (Zs.toK0 (jmul k).Y / Zs.toK0 (jmul k).Z ^ 3), k • genP0 = .some _ _ h := by
  rcases rep_jmul k with ⟨h, -⟩ | ⟨-, h, e⟩
  · exact absurd ((map_eq_zero_iff _ Zs.toK0_injective).mp h) hZ
  · exact ⟨h, e⟩

/-- For `[k]P₀ = (x, y)` affine, `y = 0` exactly when the second coordinate of `mul(k)` vanishes. -/
theorem jmul_Y_eq_zero_iff {k : ℤ} {x y : K0} {h : genCurve.toAffine.Nonsingular x y}
    (hk : k • genP0 = .some x y h) : (jmul k).Y = 0 ↔ y = 0 := by
  have hZ : (jmul k).Z ≠ 0 := fun hZ => Point.some_ne_zero h (hk ▸ (jmul_Z_eq_zero_iff k).mp hZ)
  obtain ⟨h', e⟩ := jmul_eq_some hZ
  rw [hk, Point.some.injEq] at e
  rw [e.2, div_eq_zero_iff, map_eq_zero_iff _ Zs.toK0_injective]
  have : Zs.toK0 (jmul k).Z ^ 3 ≠ 0 :=
    pow_ne_zero 3 ((map_ne_zero_iff _ Zs.toK0_injective).mpr hZ)
  simp [this]

/-- `k` is admissible exactly when `mul(k)` has nonzero second and third coordinates. -/
theorem admissible_iff_jmul (k : ℤ) : Admissible k ↔ (jmul k).Z ≠ 0 ∧ (jmul k).Y ≠ 0 := by
  constructor
  · rintro ⟨x, y, h, hk, hy⟩
    refine ⟨fun hZ => Point.some_ne_zero h (hk ▸ (jmul_Z_eq_zero_iff k).mp hZ), ?_⟩
    rw [Ne, jmul_Y_eq_zero_iff hk]; exact hy
  · rintro ⟨hZ, hY⟩
    obtain ⟨h, e⟩ := jmul_eq_some hZ
    exact ⟨_, _, h, e, by rw [Ne, ← jmul_Y_eq_zero_iff e]; exact hY⟩

end ZInQ.Compiler.Precision
