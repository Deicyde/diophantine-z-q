import Mathlib
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.IndexAlgebra

/-!
# Lane RC23: the native-index bound of (O.8), its algebraic core (App F, tex 9422–9428)

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-visibility` (tex 9421–9428):

"For a known simple-zero `D`, write `P_D = m_D G + T` in its native rank-one free lattice. The same
`L` kills `T`. An integral finite-field Kummer map cannot decrease `v₂(m_D)`, so (O.7) gives the
lower bound by the native index."

The index valuation is batch 3's `twoDivIndex M x` (the supremum of the `e` with `x − 2^e G` torsion
for some `G ∈ M`; `j = v₂(m_D)` when `x = m_D G + T` in a rank-one `M`). This file proves the step
for an arbitrary subgroup `M` (the native lattice), an arbitrary multiple `L` killing its torsion
and an arbitrary additive map to `ℤ/2^M` (the finite-field Kummer evaluation
`λ_M ∘ reduction`, tex 8378–8398, 8476, 9283–9286):

* `kummer_native_bound` (PROVED): `k ≤ j(x)` implies `2^k ∣ κ(L x)` in `ℤ/2^M`;
* `two_pow_dvd_val` (PROVED): for `k ≤ M` the divisibility passes to the canonical integer lift;
* `native_bound_toNat` (PROVED): the form used by (O.8), with `j` read as an integer
  (`ENat.toNat`, so the value `⊤` of a torsion point reads `0`);
* `kummer_native_bound_sharp` (PROVED, non-vacuity): the bound is attained.

Kinds: everything here is PROVED; the facts about the genuine objects (rank one, `L` killing the
torsion of the native lattice, the stage maps) enter in `Visibility/Genus.lean`.
-/

namespace ZInQ.Manuscript.RC.Visibility

open ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- **PROVED (tex 9422–9425): "an integral finite-field Kummer map cannot decrease `v₂(m_D)`".**
`Mlat` is the native lattice, `x ∈ Mlat` the genus point, `L` an integer killing the torsion of
`Mlat` ("the same `L` kills `T`", tex 9423), `κ` any additive map to `ℤ/2^M` (the finite-field
Kummer evaluation). If the index valuation of `x` in `Mlat` is at least `k`, i.e.
`x = 2^k G + T` with `G ∈ Mlat` and `T` torsion, then `κ(L x) = 2^k κ(L G)`. -/
theorem kummer_native_bound {A : Type*} [AddCommGroup A] {Mlat : AddSubgroup A} {x : A}
    (hx : x ∈ Mlat) {L : ℕ} (hL : ∀ t ∈ Mlat, IsOfFinAddOrder t → L • t = 0) {M : ℕ}
    (κ : A →+ ZMod (2 ^ M)) {k : ℕ} (hk : (k : ℕ∞) ≤ twoDivIndex Mlat x) :
    (2 : ZMod (2 ^ M)) ^ k ∣ κ (L • x) := by
  obtain ⟨G, hG, hT⟩ := (le_twoDivIndex_iff hx k).mp hk
  have hTmem : x - (2 ^ k : ℕ) • G ∈ Mlat := Mlat.sub_mem hx (Mlat.nsmul_mem hG _)
  have hLT : L • (x - (2 ^ k : ℕ) • G) = 0 := hL _ hTmem hT
  have hLx : L • x = (2 ^ k : ℕ) • (L • G) := by
    have hsplit : x = (2 ^ k : ℕ) • G + (x - (2 ^ k : ℕ) • G) := by abel
    rw [hsplit, smul_add, hLT, add_zero, smul_comm]
  refine ⟨κ (L • G), ?_⟩
  rw [hLx, map_nsmul, nsmul_eq_mul]
  push_cast
  ring

/-- **PROVED.** For `k ≤ M`, a residue in `ℤ/2^M` divisible by `2^k` has its canonical integer lift
divisible by `2^k` (so the 2-adic valuation of the lift is at least `k`). -/
theorem two_pow_dvd_val {M k : ℕ} (hk : k ≤ M) {y : ZMod (2 ^ M)}
    (h : (2 : ZMod (2 ^ M)) ^ k ∣ y) : (2 : ℤ) ^ k ∣ (y.val : ℤ) := by
  have : NeZero (2 ^ M) := ⟨by positivity⟩
  obtain ⟨z, rfl⟩ := h
  have hcast : (((((2 : ZMod (2 ^ M)) ^ k * z).val : ℕ) : ℤ) : ZMod (2 ^ M)) =
      (((2 : ℤ) ^ k * (z.val : ℤ) : ℤ) : ZMod (2 ^ M)) := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id', id, ZMod.natCast_val, ZMod.cast_id', id]
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hcast
  have h1 : (2 : ℤ) ^ k ∣ ((2 ^ M : ℕ) : ℤ) := by
    push_cast
    exact pow_dvd_pow 2 hk
  have h2 : (2 : ℤ) ^ k ∣ (2 : ℤ) ^ k * (z.val : ℤ) - ((((2 : ZMod (2 ^ M)) ^ k * z).val : ℕ) : ℤ) :=
    dvd_trans h1 hdvd
  have h3 : (2 : ℤ) ^ k ∣ (2 : ℤ) ^ k * (z.val : ℤ) := dvd_mul_right _ _
  have := dvd_sub h3 h2
  rwa [sub_sub_cancel] at this

/-- **PROVED (tex 9422–9428, the form used by (O.8)).** With the index valuation read as an integer
(`ENat.toNat`; a torsion point has index `⊤`, read `0`), every `k ≤ min(M, j)` gives
`2^k ∣ val(κ(L x))`. -/
theorem native_bound_toNat {A : Type*} [AddCommGroup A] {Mlat : AddSubgroup A} {x : A}
    (hx : x ∈ Mlat) {L : ℕ} (hL : ∀ t ∈ Mlat, IsOfFinAddOrder t → L • t = 0) {M : ℕ}
    (κ : A →+ ZMod (2 ^ M)) {k : ℕ} (hkM : k ≤ M)
    (hkj : (k : ℤ) ≤ ((twoDivIndex Mlat x).toNat : ℤ)) :
    (2 : ℤ) ^ k ∣ ((κ (L • x)).val : ℤ) := by
  by_cases htop : twoDivIndex Mlat x = ⊤
  · rw [htop, ENat.toNat_top, Nat.cast_zero] at hkj
    have hk0 : k = 0 := by omega
    subst hk0
    simp
  · apply two_pow_dvd_val hkM
    apply kummer_native_bound hx hL κ
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hj, ENat.toNat_natCast] at hkj
    rw [← hj]
    exact_mod_cast (show k ≤ j by omega)

/-- **PROVED (non-vacuity of `kummer_native_bound`).** The bound is attained: in `A = ℤ` with
`Mlat = ⊤`, `L = 1` and the reduction map `κ : ℤ → ℤ/2^M`, the point `x = 2^j` (`j < M`) has index
valuation at least `j`, and `κ(x)` is divisible by `2^j` but not by `2^{j+1}`. -/
theorem kummer_native_bound_sharp {M j : ℕ} (hj : j < M) :
    ((j : ℕ∞) ≤ twoDivIndex (⊤ : AddSubgroup ℤ) ((2 : ℤ) ^ j)) ∧
      (2 : ZMod (2 ^ M)) ^ j ∣ (Int.castAddHom (ZMod (2 ^ M))) (1 • (2 : ℤ) ^ j) ∧
      ¬ (2 : ZMod (2 ^ M)) ^ (j + 1) ∣ (Int.castAddHom (ZMod (2 ^ M))) (1 • (2 : ℤ) ^ j) := by
  have hle : (j : ℕ∞) ≤ twoDivIndex (⊤ : AddSubgroup ℤ) ((2 : ℤ) ^ j) := by
    refine (le_twoDivIndex_iff (AddSubgroup.mem_top _) j).mpr ⟨1, AddSubgroup.mem_top _, ?_⟩
    have : (2 : ℤ) ^ j - (2 ^ j : ℕ) • (1 : ℤ) = 0 := by ring
    rw [this]
    exact IsOfFinAddOrder.zero
  refine ⟨hle, kummer_native_bound (AddSubgroup.mem_top _) (fun t _ ht => ?_) _ hle, ?_⟩
  · -- `ℤ` is torsion-free
    obtain ⟨n, hn, hnt⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero).mp ht
    rw [nsmul_eq_mul] at hnt
    rcases mul_eq_zero.mp hnt with h | h
    · exact absurd (by exact_mod_cast h) hn.ne'
    · rw [h, smul_zero]
  · rintro ⟨z, hz⟩
    simp only [one_smul, Int.coe_castAddHom, Int.cast_pow, Int.cast_ofNat] at hz
    -- `2^j = 2^(j+1) z` in `ℤ/2^M`; lift to `ℤ`
    have hz' : (((2 : ℤ) ^ j : ℤ) : ZMod (2 ^ M)) = (((2 : ℤ) ^ (j + 1) * (z.val : ℤ) : ℤ) :
        ZMod (2 ^ M)) := by
      have : NeZero (2 ^ M) := ⟨by positivity⟩
      push_cast
      rw [ZMod.natCast_val, ZMod.cast_id', id]
      exact hz
    have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hz'
    have h1 : (2 : ℤ) ^ (j + 1) ∣ ((2 ^ M : ℕ) : ℤ) := by
      push_cast
      exact pow_dvd_pow 2 hj
    have h2 := dvd_trans h1 hdvd
    have h3 : (2 : ℤ) ^ (j + 1) ∣ (2 : ℤ) ^ (j + 1) * (z.val : ℤ) := dvd_mul_right _ _
    have h4 : (2 : ℤ) ^ (j + 1) ∣ (2 : ℤ) ^ j := by
      have := dvd_sub h3 h2
      rwa [sub_sub_cancel] at this
    have h5 : (2 : ℤ) ^ (j + 1) ≤ 2 ^ j := Int.le_of_dvd (by positivity) h4
    have h6 : (2 : ℤ) ^ j < 2 ^ (j + 1) := pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self j)
    omega

end ZInQ.Manuscript.RC.Visibility
