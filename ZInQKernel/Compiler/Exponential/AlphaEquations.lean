import ZInQKernel.Compiler.Exponential.AlphaGrowth
import ZInQKernel.Compiler.Exponential.AlphaPell
import ZInQKernel.Compiler.Exponential.AlphaParameterCongruence
import ZInQ.AlphaUnordered
import ZInQ.AlphaIndexCompanion
import ZInQ.AlphaSquareBridgeDraft
import ZInQ.AlphaFoldedResidue
import ZInQ.AlphaSignedResidue
import ZInQ.AlphaCompanionBound
import ZInQ.AlphaLargeOddPair
import ZInQ.AlphaWitnessTransport
import ZInQ.AlphaCRTWitness

/-!
# The alpha formula (C.2)

Blueprint: `compiler/natural/exponential/alpha-equations.md`,
`alpha-equations-sound.md`, `alpha-equations-complete.md`.

`AlphaEqns X b N` is the fifteen-condition system (C.2) with eight natural witnesses
`r, s, t, u, v, w, x, y`; congruences are equalities of natural remainders (so modulus `0` means
equality). It holds exactly when `b > 3` and `X = α_b(N)`.
-/

namespace ZInQ.AlphaPower

/-- The alpha formula (C.2): the fifteen conditions with witnesses `r, s, t, u, v, w, x, y`. -/
def AlphaEqns (X b N : ℕ) : Prop :=
  ∃ r s t u v w x y : ℕ, 3 < b ∧ u ^ 2 + t ^ 2 = 1 + b * u * t ∧
    s ^ 2 + r ^ 2 = 1 + b * s * r ∧ r < s ∧ u ^ 2 ∣ s ∧ v + 2 * r = b * s ∧
    w % v = b % v ∧ w % u = 2 % u ∧ 2 < w ∧ x ^ 2 + y ^ 2 = 1 + w * x * y ∧
    2 * X < u ∧ 2 * X < v ∧ x % v = X % v ∧ 2 * N < u ∧ x % u = N % u

private theorem sq_form {B x y : ℕ} (h : x ^ 2 + y ^ 2 = 1 + B * x * y) :
    x * x + y * y = 1 + B * x * y := by
  rw [← h]; ring

/-- Soundness of the alpha formula: `AlphaEqns X b N` implies `b > 3` and `X = α_b(N)`. -/
theorem alphaEqns_sound {X b N : ℕ} (h : AlphaEqns X b N) :
    3 < b ∧ (X : ℤ) = alphaZ b N := by
  obtain ⟨r, s, t, u, v, w, x, y, hb, hut, hsr, hrs, hus, hv, hwv, hwu, hw, hxy, hXu, hXv,
    hxv, hNu, hxu⟩ := h
  refine ⟨hb, ?_⟩
  have hb2 : 2 < b := by omega
  -- Shapes.
  obtain ⟨k, hk⟩ := exists_eq_alphaZ_of_quadratic b u t hb2 (sq_form hut)
  obtain ⟨m, hm, hr, hs⟩ := orderedPair_positive_index b r s hrs hsr
  obtain ⟨n, hn⟩ := exists_eq_alphaZ_of_quadratic w x y hw (sq_form hxy)
  -- `u ∣ m`.
  have hum : u ∣ m := square_divisibility_to_index b u s k m hb2 hm hk hs hus
  -- The companion.
  have hvc : (v : ℤ) = alphaZ b (m + 1) - alphaZ b (m - 1) :=
    companion_of_additive_witness b r s v m hm hr hs hv
  -- Residues.
  have hXmod : (X : ℤ) % (v : ℤ) = alphaZ b n % (v : ℤ) := by
    have h1 : ((X % v : ℕ) : ℤ) = ((x % v : ℕ) : ℤ) := by rw [hxv]
    push_cast at h1
    rw [h1, hn]
    exact alphaZ_emod_eq_of_mod_eq v w b n hwv
  have hNmod : N % u = n % u := by
    have h2 : ((x : ℤ)) % (u : ℤ) = (n : ℤ) % (u : ℤ) := by
      rw [hn, alphaZ_emod_eq_of_mod_eq u w 2 n hwu, alphaZ_two_left]
    have h1 : ((N % u : ℕ) : ℤ) = ((x % u : ℕ) : ℤ) := by rw [hxu]
    push_cast at h1
    have h3 : ((N % u : ℕ) : ℤ) = ((n % u : ℕ) : ℤ) := by push_cast; rw [h1, h2]
    exact_mod_cast h3
  -- Fold `n` and recover `X`.
  obtain ⟨l, j, hjm, hf⟩ := exists_folded_index m n hm
  have hdiv := folded_alpha_signed_residue b X v n m l j hb2 hvc hXmod hf
  have hjv := two_mul_alphaZ_lt_companion b j m hb hm hjm
  rw [← hvc] at hjv
  have hXj : (X : ℤ) = alphaZ b j :=
    eq_of_small_signed_residue X (alphaZ b j) v (by positivity)
      (alphaZ_nonneg b hb2.le j) (by exact_mod_cast hXv) hjv hdiv
  -- Recover `N`.
  have hju : 2 * j < u := by
    have := alphaZ_ge_index b j hb2.le
    have : (2 * j : ℤ) < u := by omega
    exact_mod_cast this
  have hNj : N = j := folded_index_recovery u m n N l j hum hNu hju hNmod hf
  rw [hXj, hNj]

/-- Completeness of the alpha formula: for `b > 3`, `AlphaEqns (α_b(N)) b N` (the value being
natural). -/
theorem alphaEqns_complete (b N : ℕ) (hb : 3 < b) :
    AlphaEqns (alphaZ b N).toNat b N := by
  have hb2 : 2 < b := by omega
  set X := (alphaZ b N).toNat with hXdef
  have hX : (X : ℤ) = alphaZ b N := Int.toNat_of_nonneg (alphaZ_nonneg b hb2.le N)
  -- 1. A large odd `u = α_b(k)`.
  obtain ⟨k, hk, hodd, hXk, hlt, hq⟩ := alphaZ_large_odd_pair b X hb
  have hk0 := alphaZ_nonneg b hb2.le k
  have hk1 := alphaZ_nonneg b hb2.le (k + 1)
  set u := (alphaZ b k).toNat with hudef
  set t := (alphaZ b (k + 1)).toNat with htdef
  have hu : (u : ℤ) = alphaZ b k := Int.toNat_of_nonneg hk0
  have ht : (t : ℤ) = alphaZ b (k + 1) := Int.toNat_of_nonneg hk1
  have hut : u ^ 2 + t ^ 2 = 1 + b * u * t := by
    have : ((u ^ 2 + t ^ 2 : ℕ) : ℤ) = ((1 + b * u * t : ℕ) : ℤ) := by
      push_cast; rw [hu, ht]; linear_combination hq
    exact_mod_cast this
  have huodd : Odd u := by
    rw [← Int.odd_coe_nat, hu]; exact hodd
  have hXu : 2 * X < u := by
    have : ((2 * X : ℕ) : ℤ) < (u : ℤ) := by push_cast; rw [hu]; exact hXk
    exact_mod_cast this
  have hupos : 0 < u := by omega
  -- 2. The pair `(r, s)` at `m = u k`.
  obtain ⟨r, s, hm, hr, hs, hrs, hsr, hus⟩ := square_multiple_pair b k u hb2 hk hu
  -- 3. The companion `v`.
  obtain ⟨v, hv, hsv⟩ := exists_large_additive_companion b r s hb hrs
  -- 4. Bounds.
  have hus' : u ≤ s := by
    have hkm : k ≤ u * k := Nat.le_mul_of_pos_left k hupos
    have := alphaZ_le_of_le b hb2.le hkm
    have : (u : ℤ) ≤ (s : ℤ) := by rw [hu, hs]; exact this
    exact_mod_cast this
  have hXv : 2 * X < v := by omega
  have hNX : N ≤ X := by
    have := alphaZ_ge_index b N hb2.le
    have : (N : ℤ) ≤ (X : ℤ) := by rw [hX]; exact this
    exact_mod_cast this
  have hNu : 2 * N < u := by omega
  -- 5. Coprimality and 6. CRT.
  have hcop : Nat.Coprime u v := coprime_of_square_witness b u r s v huodd hus hsr hv
  obtain ⟨w, hw, hwu, hwv⟩ := exists_gt_two_modEq_pair b u v hupos (by omega) hcop
  -- 7. The pair `(x, y)`.
  obtain ⟨x, y, -, -, hxy, hXx, hNx⟩ :=
    exists_parameter_pair_residues b X N u v w hw hX hwu hwv
  exact ⟨r, s, t, u, v, w, x, y, hb, hut, hsr, hrs, hus, hv, hwv, hwu, hw, hxy, hXu, hXv,
    hXx.symm, hNu, hNx.symm⟩

/-- The alpha formula holds exactly when `b > 3` and `X = α_b(N)`. -/
theorem alphaEqns_iff (X b N : ℕ) : AlphaEqns X b N ↔ 3 < b ∧ (X : ℤ) = alphaZ b N := by
  refine ⟨alphaEqns_sound, fun ⟨hb, hX⟩ => ?_⟩
  have : X = (alphaZ b N).toNat := by rw [← hX]; rfl
  rw [this]
  exact alphaEqns_complete b N hb

end ZInQ.AlphaPower
