/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 4d91513e4d30, module
-- TauCeti.NumberTheory.ModularForms.Degeneracy), Apache-2.0: declarations added to that module
-- after commit 5a01f5fe, whose version is vendored as
-- `ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Degeneracy`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Degeneracy
public import ZInQKernel.Contrib.TauCeti.Backport.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The conjugate of `Γ₁(N)` by `diag(q, 1)` (backport)

* `TauCeti.gamma1Conj q N`: the intersection of `SL(2, ℤ)` with the conjugate
  `diag(q, 1) Γ₁(N) diag(q, 1)⁻¹`.
-/

public noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Function

open scoped Manifold MatrixGroups ModularForm Pointwise

namespace TauCeti

section Gamma1Conj

variable {q N M : ℕ}

/-- The intersection of `SL(2, ℤ)` with `diag(q, 1) Γ₁(N) diag(q, 1)⁻¹` (Mathlib's `conjGL` at
`diag(q, 1)⁻¹`), which is the whole conjugate when `q ∣ N` (`map_gamma1Conj`). It consists of the
matrices `(a, q b; c, d)` with `(a, b; q c, d) ∈ Γ₁(N)` (`mem_gamma1Conj_iff`). It has finite index
in `SL(2, ℤ)` when `N ≠ 0`. -/
def gamma1Conj (q N : ℕ) [NeZero q] : Subgroup SL(2, ℤ) :=
  conjGL (Gamma1 N) (scaleGL q)⁻¹

/-- The `diag(q, 1)`-conjugate `conjScale q δ c hc` of a matrix `δ ∈ Γ₁(N)` lies in
`gamma1Conj q N`. -/
lemma conjScale_mem_gamma1Conj [NeZero q] {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma1 N) {c : ℤ}
    (hc : δ 1 0 = q * c) : conjScale q δ c hc ∈ gamma1Conj q N := by
  rw [gamma1Conj, conjGL, inv_inv, Subgroup.mem_comap, ← mapGL_conjScale,
    ← ConjAct.toConjAct_smul]
  exact Subgroup.smul_mem_pointwise_smul _ _ _ ⟨δ, hδ, rfl⟩

/-- The members of `gamma1Conj q N` are exactly the `diag(q, 1)`-conjugates
`conjScale q δ c hc` of the matrices `δ ∈ Γ₁(N)`. -/
lemma mem_gamma1Conj_iff [NeZero q] {γ : SL(2, ℤ)} :
    γ ∈ gamma1Conj q N ↔
      ∃ δ ∈ Gamma1 N, ∃ (c : ℤ) (hc : δ 1 0 = q * c), conjScale q δ c hc = γ := by
  refine ⟨fun hγ ↦ ?_, fun ⟨δ, hδ, c, hc, h⟩ ↦ h ▸ conjScale_mem_gamma1Conj hδ hc⟩
  rw [gamma1Conj, conjGL, inv_inv, Subgroup.mem_comap,
    Subgroup.mem_smul_pointwise_iff_exists] at hγ
  obtain ⟨_, ⟨δ, hδ, rfl⟩, hγ⟩ := hγ
  have hmul : scaleGL q * mapGL ℝ δ = mapGL ℝ γ * scaleGL q := by
    rw [ConjAct.toConjAct_smul] at hγ
    rw [← hγ]; group
  have h10 := congrArg (fun g : GL (Fin 2) ℝ ↦ (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) hmul
  simp only [Fin.isValue, Units.val_mul, coe_scaleGL, mapGL_coe_matrix, algebraMap_int_eq,
    map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.mul_apply, of_apply,
    cons_val', cons_val_fin_one, cons_val_one, map_apply, Fin.sum_univ_two, cons_val_zero,
    zero_mul, one_mul, zero_add, mul_zero, add_zero] at h10
  have hc : δ 1 0 = q * γ 1 0 := by exact_mod_cast h10.trans (mul_comm _ _)
  refine ⟨δ, hδ, γ 1 0, hc, (mapGL_inj (S := ℝ) _ _).mp ?_⟩
  rw [← mapGL_conjScale, ← hγ, ConjAct.toConjAct_smul]

/-- For `q ∣ N`, the image of `gamma1Conj q N` in `GL(2, ℝ)` is the whole conjugate
`diag(q, 1) Γ₁(N) diag(q, 1)⁻¹`. -/
lemma map_gamma1Conj [NeZero q] (hqN : q ∣ N) :
    (gamma1Conj q N).map (mapGL ℝ) =
      ConjAct.toConjAct (scaleGL q) • (Gamma1 N).map (mapGL ℝ) := by
  rw [gamma1Conj, conjGL, inv_inv]
  refine Subgroup.map_comap_eq_self fun x hx ↦ ?_
  obtain ⟨_, ⟨δ, hδ, rfl⟩, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hx
  obtain ⟨c, hc⟩ : (q : ℤ) ∣ δ 1 0 :=
    (Int.natCast_dvd_natCast.mpr hqN).trans (mem_Gamma1_iff_dvd_lowerRow.mp hδ).1
  exact ⟨conjScale q δ c hc, by rw [ConjAct.toConjAct_smul, mapGL_conjScale]⟩

/-- For `q ∣ N`, conjugating `gamma1Conj q N` back by `diag(q, 1)⁻¹` recovers `Γ₁(N)`. -/
lemma inv_conjAct_map_gamma1Conj [NeZero q] (hqN : q ∣ N) :
    ConjAct.toConjAct (scaleGL q)⁻¹ • (gamma1Conj q N).map (mapGL ℝ) =
      (Gamma1 N).map (mapGL ℝ) := by
  rw [map_gamma1Conj hqN, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

/-- The image of `gamma1Conj q N` lies in the conjugate of `Γ₁(N)` by `(diag(q, 1)⁻¹)⁻¹`, the
form taken by the hypothesis of restricting a translate by `diag(q, 1)⁻¹`. -/
lemma map_gamma1Conj_le [NeZero q] :
    (gamma1Conj q N).map (mapGL ℝ) ≤
      ConjAct.toConjAct (scaleGL q)⁻¹⁻¹ • (Gamma1 N).map (mapGL ℝ) :=
  Subgroup.map_comap_le _ _

/-- A matrix of `Γ₁(N)` whose upper-right entry is divisible by `q` lies in `gamma1Conj q N`. -/
lemma mem_gamma1Conj_of_mem_Gamma1 [NeZero q] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N)
    (hq : (q : ℤ) ∣ γ 0 1) : γ ∈ gamma1Conj q N := by
  obtain ⟨b, hb⟩ := hq
  obtain ⟨h10, h11⟩ := mem_Gamma1_iff_dvd_lowerRow.mp hγ
  have hdet := Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  obtain ⟨δ, hδ⟩ : ∃ δ : SL(2, ℤ),
      (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![γ 0 0, b; q * γ 1 0, γ 1 1] :=
    ⟨⟨!![γ 0 0, b; q * γ 1 0, γ 1 1], by
      rw [Matrix.det_fin_two_of]; rw [hb] at hdet; linear_combination hdet⟩, rfl⟩
  have hc : δ 1 0 = q * γ 1 0 := by rw [hδ]; simp
  have hδN : δ ∈ Gamma1 N := mem_Gamma1_of_dvd_lowerRow (by rw [hc]; exact h10.mul_left _)
    (by rw [hδ]; simpa using h11)
  have hγδ : conjScale q δ (γ 1 0) hc = γ :=
    Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ by
      rw [coe_conjScale, hδ]
      fin_cases i <;> fin_cases j <;> simp [hb]
  exact hγδ ▸ conjScale_mem_gamma1Conj hδN hc

/-- For `q * M ∣ N`, the conjugate `gamma1Conj q N` lies in `Γ₁(M)`. -/
lemma gamma1Conj_le_Gamma1 [NeZero q] (hqM : q * M ∣ N) : gamma1Conj q N ≤ Gamma1 M := by
  intro γ hγ
  obtain ⟨δ, hδ, c, hc, rfl⟩ := mem_gamma1Conj_iff.mp hγ
  obtain ⟨h10, h11⟩ := mem_Gamma1_iff_dvd_lowerRow.mp hδ
  refine mem_Gamma1_of_dvd_lowerRow ?_
    (by simpa using (Int.natCast_dvd_natCast.mpr (dvd_of_mul_left_dvd hqM)).trans h11)
  have : ((q * M : ℕ) : ℤ) ∣ q * c := (Int.natCast_dvd_natCast.mpr hqM).trans (hc ▸ h10)
  push_cast at this
  simpa using Int.dvd_of_mul_dvd_mul_left (Int.natCast_ne_zero.mpr (NeZero.ne q)) this

/-- The principal congruence subgroup `Γ(q N)` lies in `gamma1Conj q N`. -/
lemma Gamma_le_gamma1Conj [NeZero q] : Gamma (q * N) ≤ gamma1Conj q N := fun _ hγ ↦
  mem_gamma1Conj_of_mem_Gamma1 (Gamma_le_Gamma1 N (Gamma_le_Gamma_of_dvd (Dvd.intro_left q rfl) hγ))
    ((Int.natCast_dvd_natCast.mpr (Dvd.intro N rfl)).trans
      ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma_mem.mp hγ).2.1))

/-- `gamma1Conj q N` has finite index in `SL(2, ℤ)`, as it contains `Γ(q N)`. -/
instance [NeZero q] [NeZero N] : (gamma1Conj q N).FiniteIndex :=
  Subgroup.finiteIndex_of_le Gamma_le_gamma1Conj

/-- For `K' = q m` and `lcm m K = K'`, the conjugate `diag(q, 1) Γ₁(K) diag(q, 1)⁻¹`
meets `Γ₁(m)` in the conjugate of `Γ₁(K')`. -/
lemma gamma1Conj_eq_inf [NeZero q] {m K K' : ℕ} (hm : q * m = K')
    (hlcm : Nat.lcm m K = K') : gamma1Conj q K' = Gamma1 m ⊓ gamma1Conj q K := by
  have hKK' : K ∣ K' := hlcm ▸ Nat.dvd_lcm_right m K
  refine le_antisymm (le_inf (gamma1Conj_le_Gamma1 (dvd_of_eq hm)) fun γ hγ ↦ ?_) fun γ hγ ↦ ?_
  · obtain ⟨δ, hδ, c, hc, rfl⟩ := mem_gamma1Conj_iff.mp hγ
    exact conjScale_mem_gamma1Conj (Gamma1_le_Gamma1_of_dvd hKK' hδ) hc
  · obtain ⟨hγm, hγK⟩ := Subgroup.mem_inf.mp hγ
    obtain ⟨δ, hδ, c, hc, rfl⟩ := mem_gamma1Conj_iff.mp hγK
    obtain ⟨h10, h11⟩ := mem_Gamma1_iff_dvd_lowerRow.mp hγm
    have hδm : δ ∈ Gamma1 m := mem_Gamma1_of_dvd_lowerRow
      (by rw [hc]; exact Dvd.dvd.mul_left (by simpa using h10) _) (by simpa using h11)
    refine conjScale_mem_gamma1Conj ?_ hc
    rw [← hlcm, Gamma1_lcm_eq_inf]
    exact ⟨hδm, hδ⟩

/-- **`Γ₁(n) ⊆ Γ₁(m) · diag(q, 1) Γ₁(K) diag(q, 1)⁻¹`**, for `q ∣ K` and `gcd m K = n`: every
element of `Γ₁(n)` factors as a product of an element of `Γ₁(m)` and one of `gamma1Conj q K`. -/
lemma exists_mul_gamma1Conj_eq_of_mem_Gamma1 [NeZero q] {n m K : ℕ} (hqK : q ∣ K)
    (hgcd : Nat.gcd m K = n) {x : SL(2, ℤ)} (hx : x ∈ Gamma1 n) :
    ∃ a ∈ Gamma1 m, ∃ b ∈ gamma1Conj q K, a * b = x := by
  -- factor through `Γ₁(n) = Γ₁(m) · Γ₁(K)` and move a power of `T` across to make the
  -- upper-right entry of the `Γ₁(K)` factor divisible by `q`
  obtain ⟨α, hα, β, hβ, rfl⟩ := exists_mul_eq_of_mem_Gamma1_gcd (hgcd ▸ hx)
  have h11 : (K : ℤ) ∣ β 1 1 - 1 := (mem_Gamma1_iff_dvd_lowerRow.mp hβ).2
  refine ⟨α * ModularGroup.T ^ (β 0 1), mul_mem hα (T_zpow_mem_Gamma1 m _),
    ModularGroup.T ^ (-(β 0 1)) * β,
    mem_gamma1Conj_of_mem_Gamma1 (mul_mem (T_zpow_mem_Gamma1 K _) hβ) ?_, by group⟩
  have h01 : (ModularGroup.T ^ (-(β 0 1)) * β) 0 1 = -(β 0 1 * (β 1 1 - 1)) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T_zpow]
    ring
  rw [h01]
  exact (((Int.natCast_dvd_natCast.mpr hqK).trans h11).mul_left _).neg_right

end Gamma1Conj

end TauCeti
