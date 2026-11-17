import ZInQKernel.Contrib.OneProof.RC.Determinant.Pole
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Determinant clearing: Proposition `ex:limits-fixed-field-clearing`, display (5.9) (Lane RC7)

Manuscript `diophantine_zq.tex` (11/5; identical in Version 19), tex 5486–5645.

After the simultaneous new-local cancellation of Lemma `ex:limits-fixed-field-budget`, the remaining
complex `D` over `S = 𝒪[G]` has augmentation the old complex over `Λ`; centrally (`t = 0`, after
constant `ℤ₂` basis changes) its only nonzero differentials are the Smith disks `E_i → B_{i+1}`.
Let `A_i` be the actual differential submatrix from `E_i` to `B_{i+1}`, `δ_i = det A_i`,
`Δ = ∏ δ_i` (tex 5530–5536).  The proof cancels each grouped block once (tex 5544–5560, formalized in
`Schur.lean`); the final projection and inclusion give the scalars `α = (pz)¹`, `β = (μι)²`,
with `α = z_H - C A_0⁻¹ z_B` (incoming cancellation at degree one) and `β = μ_H - μ_E A_2⁻¹ B_H`
(outgoing cancellation at degree two) (tex 5562–5584).  This file proves, over an arbitrary
commutative ring `S` with a family of evaluations `ev x : S →+* O` (the sign evaluations) and a field
`K ⊇ O` (the fraction field):

* `Z := Δα ∈ S`, `W := Δβ ∈ S`, `P := ΔT = ε ∏_{i even} δ_i² ∈ S`, `Q := κZWP ∈ S`
  (tex 5583, 5593–5601), as explicit elements of `S` built with adjugates — no inverse, no
  interpolation, no division by `|G|`;
* from Elliot's determinant-coordinate identity `ũ_x = η_x κ_x α_x (2^{-a} β_x) T_x` (an `ELLIOT`
  input, tex 5605–5617): `ũ_x = 2^{-a} η_x Q_x / Δ_x³` wherever `Δ_x ≠ 0`, and with `f = 2^a Δ⁴`,
  `d = η Δ Q`: `f_x ũ_x = d_x` at every character, including `Δ_x = 0` (tex 5619–5624);
* `f_0 ∈ Λ` and `v₂ f_0(0) = a + 4 h₁ ≤ a + 4 (h_K + 2 c_E + 2 t_K) = c_det` from the central Smith
  entries (tex 5536–5541, 5625–5627);
* the pole bound `L_T(M) = 16 (d_K + 5) M` for every `f_x` modulo `2^M`, uniformly in `x`, from the
  pole bound `4M` on the sign-evaluated entries of `D` (tex 5627–5634).

The arithmetic inputs (the budget (5.7): `m ≤ d_K + 5`, `h₁ ≤ h_K + 2c_E + 2t_K`; the entry pole
bound (5.8); Elliot's coordinate identity and the generic patterns) are hypotheses, each named after
the manuscript display it encodes.
-/

namespace ZInQ.Manuscript.RC.Determinant

open Matrix Finset

/-- The ring `Λ = ℤ₂[[t]]` (tex 2747). -/
abbrev Lam : Type := PowerSeries ℤ_[2]

/-- Central Smith data of the remaining old complex (tex 5522–5536).  The disks are indexed by the
degree `i < n` of their source: `A i` is the actual differential submatrix from `E_i` to `B_{i+1}`
(square of size `m i`), with augmentation `A0 i` over `Λ`.  Centrally (constant coefficient `t ↦ 0`)
`A0 i` is the diagonal matrix of the nonzero Smith entries `s i j` (after the constant `ℤ₂` basis
change, which is built into the chosen bases). -/
structure SmithBlocks (S O : Type*) [CommRing S] [CommRing O] [Algebra Lam O] where
  /-- number of degrees carrying Smith disks (`E_i → B_{i+1}` for `i < n`) -/
  n : ℕ
  /-- `m i = rank E_i = rank B_{i+1}` -/
  m : ℕ → ℕ
  /-- the actual differential submatrix `A_i : E_i → B_{i+1}` over `S` -/
  A : (i : ℕ) → Matrix (Fin (m i)) (Fin (m i)) S
  /-- its augmentation, a matrix over `Λ` (tex 5537–5538: `Δ_0 ∈ Λ`) -/
  A0 : (i : ℕ) → Matrix (Fin (m i)) (Fin (m i)) Lam
  /-- the central Smith entries `2^{e} u` of the disks of `D_c = D_0 ⊗_Λ ℤ₂` -/
  s : (i : ℕ) → Fin (m i) → ℤ_[2]
  s_ne : ∀ i j, s i j ≠ 0
  central : ∀ i, (A0 i).map PowerSeries.constantCoeff = Matrix.diagonal (s i)

namespace SmithBlocks

variable {S O : Type*} [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O)

/-- `δ_i = det A_i` (tex 5533). -/
noncomputable def δ (i : ℕ) : S := (B.A i).det

/-- `Δ = ∏_i δ_i`; an empty determinant is one (tex 5533–5535). -/
noncomputable def Δ : S := ∏ i ∈ range B.n, B.δ i

/-- `m = ∑_i m_i`, the number of all central Smith disks (tex 5530–5531). -/
def mTot : ℕ := ∑ i ∈ range B.n, B.m i

/-- `h₁`-contribution: the sum of the valuations of all central Smith entries (tex 5382–5383,
5539–5541). -/
noncomputable def hSmith : ℕ := ∑ i ∈ range B.n, ∑ j, (B.s i j).valuation

/-- The augmentation of `Δ`, an element `Δ_0 ∈ Λ` (tex 5537–5538). -/
noncomputable def Δ0 : Lam := ∏ i ∈ range B.n, (B.A0 i).det

/-- **Tex 5537–5541 (PROVED).**  `Δ_0(0) = ∏` of the central Smith entries, so
`v₂ Δ_0(0) = ∑_{central Smith disks} v₂(disk)`, and `Δ_0(0) ≠ 0`. -/
theorem constantCoeff_Δ0 : PowerSeries.constantCoeff B.Δ0 = ∏ i ∈ range B.n, ∏ j, B.s i j := by
  rw [Δ0, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [RingHom.map_det, RingHom.mapMatrix_apply, B.central i, det_diagonal]

theorem constantCoeff_Δ0_ne_zero : PowerSeries.constantCoeff B.Δ0 ≠ 0 := by
  rw [constantCoeff_Δ0]
  exact Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => B.s_ne i j

theorem valuation_constantCoeff_Δ0 :
    (PowerSeries.constantCoeff B.Δ0).valuation = B.hSmith := by
  rw [constantCoeff_Δ0, hSmith]
  have hprod : ∀ (t : Finset ℕ), (∏ i ∈ t, ∏ j, B.s i j).valuation =
      ∑ i ∈ t, ∑ j, (B.s i j).valuation := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih =>
      have hne1 : (∏ j, B.s i j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => B.s_ne i j
      have hne2 : (∏ i ∈ t, ∏ j, B.s i j) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => B.s_ne i j
      rw [Finset.prod_insert hi, Finset.sum_insert hi, PadicInt.valuation_mul hne1 hne2, ih]
      congr 1
      have hinner : ∀ (u : Finset (Fin (B.m i))), (∏ j ∈ u, B.s i j).valuation =
          ∑ j ∈ u, (B.s i j).valuation := by
        intro u
        induction u using Finset.induction_on with
        | empty => simp
        | insert j u hj ih' =>
          have h1 : B.s i j ≠ 0 := B.s_ne i j
          have h2 : (∏ j ∈ u, B.s i j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => B.s_ne i j
          rw [Finset.prod_insert hj, Finset.sum_insert hj, PadicInt.valuation_mul h1 h2, ih']
      exact hinner Finset.univ
  exact hprod _

end SmithBlocks

/-! ### The cleared scalars and the identity `f ũ = d` -/

section Clearing

variable {S O K : Type*} [CommRing S] [CommRing O] [Field K] [Algebra Lam O]
  (B : SmithBlocks S O)

/-- The data of the transported cycle and functional needed for the two scalars (tex 5577–5584):
`α = z_H - C A_0⁻¹ z_B` and `β = μ_H - μ_E A_2⁻¹ B_H`, where `C` is the `(H_1, E_0)` row of the
degree-zero differential, `z_H, z_B` the `H_1` and `B_1` coordinates of the transported cycle `z`,
`μ_H, μ_E` the `H_2` and `E_2` coordinates of the transported closed functional `μ = 2^a λ_z`, and
`B_H` the `(B_3, H_2)` column of the degree-two differential.  All are integral over `S`. -/
structure ScalarData (B : SmithBlocks S O) where
  zH : S
  zB : Fin (B.m 0) → S
  C : Fin (B.m 0) → S
  μH : S
  μE : Fin (B.m 2) → S
  BH : Fin (B.m 2) → S

variable {B}

/-- `Z := Δ α ∈ S`, written without inverses: `Z = (∏_{i ≠ 0} δ_i)(δ_0 z_H - C adj(A_0) z_B)`
(tex 5583). -/
noncomputable def ScalarData.Z (sd : ScalarData B) : S :=
  (∏ i ∈ (range B.n).erase 0, B.δ i) * (B.δ 0 * sd.zH - sd.C ⬝ᵥ ((B.A 0).adjugate *ᵥ sd.zB))

/-- `W := Δ β ∈ S`, written without inverses: `W = (∏_{i ≠ 2} δ_i)(δ_2 μ_H - μ_E adj(A_2) B_H)`
(tex 5583). -/
noncomputable def ScalarData.W (sd : ScalarData B) : S :=
  (∏ i ∈ (range B.n).erase 2, B.δ i) * (B.δ 2 * sd.μH - sd.μE ⬝ᵥ ((B.A 2).adjugate *ᵥ sd.BH))

/-- `P := Δ T = ε ∏_{i even} δ_i² ∈ S` (tex 5593–5594). -/
noncomputable def cleanP (B : SmithBlocks S O) (ε : S) : S :=
  ε * ∏ i ∈ (range B.n).filter Even, B.δ i ^ 2

/-- `Q := κ Z W P ∈ S` (tex 5600–5601). -/
noncomputable def ScalarData.Q (sd : ScalarData B) (κ ε : S) : S := κ * sd.Z * sd.W * cleanP B ε

/-- `f := 2^a Δ⁴` (tex 5495, 5619). -/
noncomputable def clearF (B : SmithBlocks S O) (a : ℕ) : S := 2 ^ a * B.Δ ^ 4

/-- `d := η Δ Q` (tex 5495, 5619). -/
noncomputable def ScalarData.dd (sd : ScalarData B) (κ ε η : S) : S := η * B.Δ * sd.Q κ ε

variable (φ : S →+* K)

/-- The scalar `α` at a character, computed in the fraction field (tex 5580). -/
noncomputable def ScalarData.αK (sd : ScalarData B) : K :=
  φ sd.zH - (fun j => φ (sd.C j)) ⬝ᵥ (((B.A 0).map φ)⁻¹ *ᵥ fun k => φ (sd.zB k))

/-- The scalar `β` at a character, computed in the fraction field (tex 5581). -/
noncomputable def ScalarData.βK (sd : ScalarData B) : K :=
  φ sd.μH - (fun j => φ (sd.μE j)) ⬝ᵥ (((B.A 2).map φ)⁻¹ *ᵥ fun k => φ (sd.BH k))

/-- The remaining determinant comparison factor `T = ε ∏_i δ_i^{(-1)^i}` at a character
(tex 5591–5593). -/
noncomputable def cleanT (B : SmithBlocks S O) (ε : S) : K :=
  φ ε * ∏ i ∈ range B.n, (φ (B.δ i)) ^ ((-1 : ℤ) ^ i)

theorem map_δ (i : ℕ) : φ (B.δ i) = ((B.A i).map φ).det := by
  rw [SmithBlocks.δ, RingHom.map_det, RingHom.mapMatrix_apply]

theorem map_Δ_eq (i : ℕ) (hi : i < B.n) :
    φ B.Δ = φ (B.δ i) * ∏ j ∈ (range B.n).erase i, φ (B.δ j) := by
  rw [SmithBlocks.Δ, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hi)]

theorem map_δ_ne_zero {i : ℕ} (hi : i < B.n) (hΔ : φ B.Δ ≠ 0) : φ (B.δ i) ≠ 0 := by
  intro h; apply hΔ; rw [map_Δ_eq φ i hi, h, zero_mul]

/-- In a field, `det(A) · A⁻¹ = adj(A)` when `det A ≠ 0`. -/
theorem det_smul_inv_eq_adjugate {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K)
    (hA : A.det ≠ 0) : A.det • A⁻¹ = A.adjugate := by
  rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hA, one_smul]

/-- **Tex 5562–5583 (PROVED).**  `Z = Δ α`: at a character with `Δ_x ≠ 0`, the explicit element
`Z ∈ S` evaluates to `Δ_x α_x`; products of denominators divide `∏ δ_i`, not a power depending on the
number of individual Smith disks. -/
theorem Z_eval (sd : ScalarData B) (h0 : 0 < B.n) (hΔ : φ B.Δ ≠ 0) :
    φ sd.Z = φ B.Δ * sd.αK φ := by
  have hδ0 := map_δ_ne_zero φ h0 hΔ
  have hadj : φ.mapMatrix (B.A 0).adjugate = ((B.A 0).map φ).adjugate := RingHom.map_adjugate _ _
  rw [RingHom.mapMatrix_apply] at hadj
  rw [map_Δ_eq φ 0 h0, ScalarData.Z, ScalarData.αK, map_mul, map_prod, map_sub, map_mul]
  have hdot : φ (sd.C ⬝ᵥ ((B.A 0).adjugate *ᵥ sd.zB)) =
      (fun j => φ (sd.C j)) ⬝ᵥ (((B.A 0).map φ).adjugate *ᵥ fun k => φ (sd.zB k)) := by
    rw [← hadj, RingHom.map_dotProduct]
    congr 1
    funext i
    exact RingHom.map_mulVec φ _ _ i
  rw [hdot, ← det_smul_inv_eq_adjugate _ (by rwa [← map_δ])]
  rw [← map_δ, smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/-- **Tex 5562–5583 (PROVED).**  `W = Δ β` at a character with `Δ_x ≠ 0`. -/
theorem W_eval (sd : ScalarData B) (h2 : 2 < B.n) (hΔ : φ B.Δ ≠ 0) :
    φ sd.W = φ B.Δ * sd.βK φ := by
  have hadj : φ.mapMatrix (B.A 2).adjugate = ((B.A 2).map φ).adjugate := RingHom.map_adjugate _ _
  rw [RingHom.mapMatrix_apply] at hadj
  rw [map_Δ_eq φ 2 h2, ScalarData.W, ScalarData.βK, map_mul, map_prod, map_sub, map_mul]
  have hdot : φ (sd.μE ⬝ᵥ ((B.A 2).adjugate *ᵥ sd.BH)) =
      (fun j => φ (sd.μE j)) ⬝ᵥ (((B.A 2).map φ).adjugate *ᵥ fun k => φ (sd.BH k)) := by
    rw [← hadj, RingHom.map_dotProduct]
    congr 1
    funext i
    exact RingHom.map_mulVec φ _ _ i
  rw [hdot, ← det_smul_inv_eq_adjugate _ (by rw [← map_δ]; exact map_δ_ne_zero φ h2 hΔ)]
  rw [← map_δ, smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

/-- **Tex 5591–5594 (PROVED).**  `P = Δ T = ε ∏_{i even} δ_i²` at a character with `Δ_x ≠ 0`. -/
theorem P_eval (ε : S) (hΔ : φ B.Δ ≠ 0) : φ (cleanP B ε) = φ B.Δ * cleanT φ B ε := by
  rw [cleanP, cleanT, SmithBlocks.Δ, map_mul, map_prod, map_prod]
  have hne : ∀ i ∈ range B.n, φ (B.δ i) ≠ 0 := fun i hi =>
    map_δ_ne_zero φ (Finset.mem_range.1 hi) hΔ
  rw [mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun i hi => ?_
  split_ifs with h
  · rw [h.neg_one_pow, zpow_one, map_pow, sq]
  · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow, zpow_neg_one, mul_inv_cancel₀ (hne i hi)]

/-- **Tex 5605–5609 (PROVED from the ELLIOT coordinate identity).**  If at a character with
`Δ_x ≠ 0` the coordinate is `ũ_x = η_x κ_x α_x (2^{-a} β_x) T_x`, then
`ũ_x = 2^{-a} η_x Q_x / Δ_x³`. -/
theorem coordinate_formula (sd : ScalarData B) (κ ε η : S) (a : ℕ) (u : K) (h2K : (2 : K) ≠ 0)
    (hn : 2 < B.n) (hΔ : φ B.Δ ≠ 0)
    (hu : u = φ η * φ κ * sd.αK φ * (((2 : K) ^ a)⁻¹ * sd.βK φ) * cleanT φ B ε) :
    u = ((2 : K) ^ a)⁻¹ * φ η * φ (sd.Q κ ε) / φ B.Δ ^ 3 := by
  have h0 : 0 < B.n := by omega
  rw [ScalarData.Q, map_mul, map_mul, map_mul, Z_eval φ sd h0 hΔ, W_eval φ sd hn hΔ,
    P_eval φ ε hΔ, hu]
  field_simp

/-- **Tex 5619–5624 (PROVED).**  With `f = 2^a Δ⁴` and `d = η Δ Q`: `f_x ũ_x = d_x` at every
character.  Where `Δ_x ≠ 0` this is the coordinate formula; where `Δ_x = 0` both `f_x` and `d_x`
vanish and the already defined (finite) coordinate satisfies the identity directly — no rational
expression with a zero denominator is specialized. -/
theorem f_mul_u_eq_d (sd : ScalarData B) (κ ε η : S) (a : ℕ) (u : K) (h2K : (2 : K) ≠ 0)
    (hn : 2 < B.n)
    (hu : φ B.Δ ≠ 0 → u = φ η * φ κ * sd.αK φ * (((2 : K) ^ a)⁻¹ * sd.βK φ) * cleanT φ B ε) :
    φ (clearF B a) * u = φ (sd.dd κ ε η) := by
  by_cases hΔ : φ B.Δ = 0
  · simp [clearF, ScalarData.dd, hΔ]
  · rw [coordinate_formula φ sd κ ε η a u h2K hn hΔ (hu hΔ), clearF, ScalarData.dd]
    simp only [map_mul, map_pow, map_ofNat]
    have h2a : ((2 : K) ^ a) ≠ 0 := pow_ne_zero _ h2K
    field_simp

end Clearing

/-! ### The valuation bound and the pole bound of (5.9) -/

section Bounds

variable {S O : Type*} [CommRing S] [CommRing O] [Algebra Lam O] (B : SmithBlocks S O)

/-- **Tex 5625–5627 (PROVED).**  `f_0 = 2^a Δ_0⁴ ∈ Λ`, and `v₂ f_0(0) = a + 4 h₁` where `h₁` is the
sum of the valuations of the central Smith entries; with the budget `h₁ ≤ h_K + 2c_E + 2t_K` of
(5.7) this gives `c = v₂ f_0(0) ≤ c_det = a + 4(h_K + 2c_E + 2t_K)`. -/
theorem valuation_f0 (a hK cE tK : ℕ) (hbudget : B.hSmith ≤ hK + 2 * cE + 2 * tK) :
    PowerSeries.constantCoeff ((2 : Lam) ^ a * B.Δ0 ^ 4) ≠ 0 ∧
      (PowerSeries.constantCoeff ((2 : Lam) ^ a * B.Δ0 ^ 4)).valuation = a + 4 * B.hSmith ∧
      (PowerSeries.constantCoeff ((2 : Lam) ^ a * B.Δ0 ^ 4)).valuation ≤
        a + 4 * (hK + 2 * cE + 2 * tK) := by
  have hne := B.constantCoeff_Δ0_ne_zero
  have h2 : (2 : ℤ_[2]) ≠ 0 := two_ne_zero
  have hval : (PowerSeries.constantCoeff ((2 : Lam) ^ a * B.Δ0 ^ 4)).valuation = a + 4 * B.hSmith := by
    rw [map_mul, map_pow, map_pow, map_ofNat, PadicInt.valuation_mul (pow_ne_zero _ h2)
      (pow_ne_zero _ hne), PadicInt.valuation_pow, PadicInt.valuation_pow,
      B.valuation_constantCoeff_Δ0]
    have : (2 : ℤ_[2]).valuation = 1 := by
      have := PadicInt.valuation_p (p := 2); simpa using this
    rw [this]; ring
  refine ⟨?_, hval, ?_⟩
  · rw [map_mul, map_pow, map_pow, map_ofNat]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ hne)
  · rw [hval]; omega

/-- **Tex 5537–5538, 5625 (PROVED).**  If the augmentation `ev_0` maps each `A_i` to (the image of)
`A0 i`, then `f_0 = ev_0(2^a Δ⁴)` is the image of `2^a Δ_0⁴ ∈ Λ`: `f_0 ∈ Λ`. -/
theorem f0_mem_Lam (aug : S →+* O) (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam O))
    (a : ℕ) : aug (clearF B a) = algebraMap Lam O ((2 : Lam) ^ a * B.Δ0 ^ 4) := by
  rw [clearF, SmithBlocks.Δ, SmithBlocks.Δ0, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow,
    map_ofNat, map_ofNat, map_prod, map_prod]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [SmithBlocks.δ, RingHom.map_det, RingHom.mapMatrix_apply, haug, RingHom.map_det,
    RingHom.mapMatrix_apply]

/-- **Tex 5627–5634: the pole bound `L_T(M) = 16(d_K+5)M` of (5.9) (PROVED).**  `f` is a polynomial
of degree `4m` with constant integral coefficients in the differential entries of `D`.  If every
sign-evaluated entry of every `A_i` has pole at most `4M` modulo `2^M` (the bound (5.8)), then
`f_x = 2^a Δ_x⁴` has pole at most `16 m M` modulo `2^M`; with the budget `m ≤ d_K + 5` this is
`L_T(M) = 16(d_K + 5)M`, uniformly in the character `x`. -/
theorem f_pole (D : PoleData Lam O) (evx : S →+* O) (a dK M : ℕ)
    (hpole : ∀ i, ∀ j k, ((B.A i).map evx) j k ∈ D.poleModLE M (4 * M))
    (hm : B.mTot ≤ dK + 5) :
    evx (clearF B a) ∈ D.poleModLE M (16 * (dK + 5) * M) := by
  have hdet : ∀ i, evx (B.δ i) ∈ D.poleModLE M (B.m i * (4 * M)) := by
    intro i
    rw [SmithBlocks.δ, RingHom.map_det, RingHom.mapMatrix_apply]
    simpa [Fintype.card_fin] using D.det_mem_poleModLE ((B.A i).map evx) (hpole i)
  have hΔ : evx B.Δ ∈ D.poleModLE M (B.mTot * (4 * M)) := by
    rw [SmithBlocks.Δ, map_prod, SmithBlocks.mTot, Finset.sum_mul]
    exact D.prod_mem_poleModLE _ _ _ fun i _ => hdet i
  have h4 := D.pow_mem_poleModLE hΔ 4
  have h2a : evx ((2 : S) ^ a) ∈ D.poleModLE M 0 := by
    rw [map_pow, map_ofNat]
    have : ((2 : O) ^ a) = algebraMap Lam O ((2 : Lam) ^ a) := by rw [map_pow, map_ofNat]
    rw [this]; exact D.poleLE_le_poleModLE M 0 (D.algebraMap_mem_poleLE _)
  have hf := D.mul_mem_poleModLE h2a h4
  have hfx : evx (clearF B a) = evx ((2 : S) ^ a) * evx B.Δ ^ 4 := by
    rw [clearF, map_mul, map_pow evx B.Δ]
  rw [hfx]
  refine D.poleModLE_mono ?_ hf
  have : B.mTot * (4 * M) * 4 ≤ (dK + 5) * (4 * M) * 4 := by
    have := Nat.mul_le_mul_right (4 * M) hm
    exact Nat.mul_le_mul_right 4 this
  nlinarith

end Bounds

end ZInQ.Manuscript.RC.Determinant
