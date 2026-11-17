import ZInQKernel.Contrib.OneProof.RC.Determinant.Clearing
import ZInQKernel.Contrib.OneProof.RC.Determinant.GroupRingUnits
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.NumberTheory.Padics.ProperSpace

/-!
# Proposition `ex:limits-fixed-field-clearing` (5.9) in coefficient form (Lane RC7)

Manuscript `diophantine_zq.tex` (11/5; identical in Version 19), tex 5486–5507 (statement) and
5508–5645 (proof); restated in Appendix G, tex 10901–10914.

This file assembles `Clearing.lean` into the form consumed by the missing-address argument
(Proposition `ex:limits-coefficient-transfer`, lane RC1-boolean): `S = 𝒪[G]` is the genuine group
ring `MonoidAlgebra O G` of a finite elementary abelian `2`-group `G`; sign characters are
`χ : G →* ℤˣ` with evaluations `signEval χ : O[G] → O`; elements of `O` are read through their
Laurent coefficients `[tⁱ] : O → ℤ₂` (`LaurentCoeffData`, realized for the genuine
`𝒪 = lim (ℤ/2ⁿ)((t))` in `OCoeff.lean`); the corrected coordinate `ũ_x ∈ Λ[1/2]` is
`g_x / 2^{e_x}` with `g_x ∈ Λ`.

Main result `fixed_field_clearing` (PROVED from the named inputs): with `f = 2^a Δ⁴` and
`d = η Δ Q` in `O[G]`,
* `f_x ũ_x = d_x` at every sign character, as the convergent coefficient identity
  `[tⁿ] d_x = Σ_{k ≥ 0} [t^{n-k}] f_x · [tᵏ] ũ_x` (tex 5495–5496, 5619–5624);
* `f_0 ∈ Λ`: no negative coefficients at the trivial character (tex 5497, 5625);
* `c = v₂ f_0(0)` is finite and `c ≤ c_det = a + 4(h_K + 2c_E + 2t_K)` (tex 5499, 5627);
* for every `M`, every sign character `x` and every `i < -L_T(M)`, `L_T(M) = 16(d_K+5)M`,
  `2^M ∣ [tⁱ] f_x` (tex 5500–5503, 5628–5639).

Inputs (hypotheses, with their manuscript provenance):
* the central Smith data of the remaining old complex and its augmentation (`SmithBlocks`,
  tex 5522–5538; ELLIOT, from the budget lemma's model, tex 5394–5427);
* the budget (5.7): `m ≤ d_K + 5`, `h₁ ≤ h_K + 2c_E + 2t_K` (tex 5384–5386; proved from the
  arithmetic exact sequences in `Budget.lean`);
* the entry pole bound (5.8) at every sign character (tex 5517–5519; proved in `NewLocalBlock.lean`
  for the Schur entries and trivially for the unchanged entries; preserved by basis change,
  `PoleData.basisChange_entry_mem_poleModLE`);
* Elliot's determinant-coordinate identity in the rank-one pattern, the vanishing in the acyclic
  pattern, and the exhaustiveness of the two patterns (tex 5605–5617; ELLIOT).
-/

namespace ZInQ.Manuscript.RC.Determinant

open Matrix Finset

/-- **The Laurent-coefficient realization of `O`** (interface): additive coefficient maps
`[tⁱ] : O → ℤ₂` such that elements of `Λ` have their power-series coefficients, membership in
`t^{-L} Λ + 2^M O` makes every coefficient below `-L` divisible by `2^M`, and multiplication by an
element of `Λ` is the convergent Cauchy product of coefficients.  For the genuine
`𝒪 = (Λ_{(2)})^ = lim_n (ℤ/2ⁿ)((t))` all of this is PROVED in `OCoeff.lean`. -/
structure LaurentCoeffData {O : Type*} [CommRing O] [Algebra Lam O] (D : PoleData Lam O) where
  /-- the Laurent coefficient `[tⁱ] y ∈ ℤ₂` -/
  coeffZ : O → ℤ → ℤ_[2]
  coeffZ_add : ∀ y z i, coeffZ (y + z) i = coeffZ y i + coeffZ z i
  coeffZ_intCast_mul : ∀ (r : ℤ) y i, coeffZ ((r : O) * y) i = (r : ℤ_[2]) * coeffZ y i
  coeffZ_algebraMap : ∀ (g : Lam) (i : ℤ),
    coeffZ (algebraMap Lam O g) i = if 0 ≤ i then PowerSeries.coeff i.toNat g else 0
  dvd_of_mem_poleModLE : ∀ (M L : ℕ) (y : O), y ∈ D.poleModLE M L →
    ∀ i : ℤ, i < -(L : ℤ) → (2 : ℤ_[2]) ^ M ∣ coeffZ y i
  conv : ∀ (y : O) (g : Lam) (n : ℤ),
    HasSum (fun k : ℕ => coeffZ y (n - k) * PowerSeries.coeff k g) (coeffZ (y * algebraMap Lam O g) n)
  /-- the coefficients tend to `0` at `-∞` (elements of `𝒪`, tex 2747–2748) -/
  decay : ∀ (y : O) (M : ℕ), ∃ L : ℕ, ∀ i : ℤ, i < -(L : ℤ) → (2 : ℤ_[2]) ^ M ∣ coeffZ y i

namespace LaurentCoeffData

variable {O : Type*} [CommRing O] [Algebra Lam O] {D : PoleData Lam O} (LC : LaurentCoeffData D)

theorem coeffZ_zero (i : ℤ) : LC.coeffZ 0 i = 0 := by
  have := LC.coeffZ_add 0 0 i
  simp only [add_zero] at this
  exact left_eq_add.mp this

theorem coeffZ_sum {ι : Type*} (s : Finset ι) (y : ι → O) (i : ℤ) :
    LC.coeffZ (∑ j ∈ s, y j) i = ∑ j ∈ s, LC.coeffZ (y j) i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LC.coeffZ_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, LC.coeffZ_add, ih]

theorem coeffZ_two_pow_mul (e : ℕ) (y : O) (i : ℤ) :
    LC.coeffZ ((2 : O) ^ e * y) i = (2 : ℤ_[2]) ^ e * LC.coeffZ y i := by
  have := LC.coeffZ_intCast_mul ((2 : ℤ) ^ e) y i
  simpa using this

end LaurentCoeffData

/-- **Tex 5517–5519, 5526–5532, 5630–5632 (PROVED).**  The entry pole bound consumed by the
clearing: if the sign-evaluated block `A_i` is a submatrix of `U d_x V`, where `U, V` are the
constant basis changes of the Smith decomposition (over `Λ`) and every entry of the sign-evaluated
differential `d_x` of `D` has pole at most `L` modulo `2^M` (for the entries next to the cancelled
new block this is `PoleData.newLocal_schur_pole`; the other entries are power series), then every
entry of `A_i` has pole at most `L` modulo `2^M`. -/
theorem entry_pole_of_differential {O : Type*} [CommRing O] [Algebra Lam O] (D : PoleData Lam O)
    {p q r s e e' : Type*} [Fintype q] [Fintype r] {M L : ℕ}
    (U : Matrix p q Lam) (d : Matrix q r O) (V : Matrix r s Lam)
    (hd : ∀ i j, d i j ∈ D.poleModLE M L) (fe : e → p) (fe' : e' → s) (Ax : Matrix e e' O)
    (hA : Ax = (U.map (algebraMap Lam O) * d * V.map (algebraMap Lam O)).submatrix fe fe') :
    ∀ j k, Ax j k ∈ D.poleModLE M L := by
  intro j k
  rw [hA, Matrix.submatrix_apply]
  exact D.basisChange_entry_mem_poleModLE U d V hd _ _

section Assembly

variable {O : Type*} [CommRing O] [IsDomain O] [Algebra Lam O] (D : PoleData Lam O)
  (LC : LaurentCoeffData D) {G : Type*} [CommMonoid G]

/-- The evaluation at a sign character, followed by the inclusion of `O` in its fraction field. -/
noncomputable def evK (χ : G →* ℤˣ) : MonoidAlgebra O G →+* FractionRing O :=
  (algebraMap O (FractionRing O)).comp (signEval χ).toRingHom

omit [IsDomain O] [Algebra Lam O] in
theorem evK_apply (χ : G →* ℤˣ) (s : MonoidAlgebra O G) :
    evK χ s = algebraMap O (FractionRing O) (signEval χ s) := rfl

/-- The corrected coordinate `ũ_x = g_x / 2^e ∈ Λ[1/2]`, viewed in the fraction field of `O`. -/
noncomputable def uK (e : ℕ) (g : Lam) : FractionRing O :=
  algebraMap O (FractionRing O) (algebraMap Lam O g) / 2 ^ e

omit [IsDomain O] in
/-- **Tex 5605–5617 (PROVED).**  The two generic patterns give one formula: in the rank-one pattern
Elliot's identity `ũ_x = η_x κ_x α_x (2^{-a} β_x) T_x` holds (ELLIOT input); in the acyclic pattern
`α_x = 0` and `ũ_x = 0`, so the same formula holds; these are the only generic patterns. -/
theorem coordinate_of_patterns {S K : Type*} [CommRing S] [Field K] {B : SmithBlocks S O}
    (φ : S →+* K) (sd : ScalarData B) (κ ε η : S) (a : ℕ) (u : K) (RankOne Acyclic : Prop)
    (hpat : RankOne ∨ Acyclic)
    (hrank : RankOne → u = φ η * φ κ * sd.αK φ * (((2 : K) ^ a)⁻¹ * sd.βK φ) * cleanT φ B ε)
    (hacyc : Acyclic → sd.αK φ = 0 ∧ u = 0) :
    u = φ η * φ κ * sd.αK φ * (((2 : K) ^ a)⁻¹ * sd.βK φ) * cleanT φ B ε := by
  rcases hpat with h | h
  · exact hrank h
  · obtain ⟨hα, hu⟩ := hacyc h
    rw [hu, hα]; ring

/-- **Proposition `ex:limits-fixed-field-clearing`, (5.9) (PROVED from the named inputs).**
See the module docstring for the list of inputs.  `X` indexes the sign characters `χ x` of the
family; `ũ_x = g_x / 2^{e_x}`. -/
theorem fixed_field_clearing [Fintype G] {X : Type*} (χ : X → G →* ℤˣ)
    (B : SmithBlocks (MonoidAlgebra O G) O) (hn : 2 < B.n)
    -- the augmentation of `D` is the old complex over `Λ` (tex 5517, 5537–5538)
    (haug : ∀ i, (B.A i).map aug = (B.A0 i).map (algebraMap Lam O))
    (sd : ScalarData B) (κ ε η : MonoidAlgebra O G) (a : ℕ)
    (e : X → ℕ) (g : X → Lam) (h2O : (2 : O) ≠ 0)
    -- the generic patterns and Elliot's coordinate identity (tex 5605–5617; ELLIOT)
    (RankOne Acyclic : X → Prop) (hpat : ∀ x, RankOne x ∨ Acyclic x)
    (hrank : ∀ x, evK (χ x) B.Δ ≠ 0 → RankOne x →
      uK (e x) (g x) = evK (χ x) η * evK (χ x) κ * sd.αK (evK (χ x)) *
        (((2 : FractionRing O) ^ a)⁻¹ * sd.βK (evK (χ x))) * cleanT (evK (χ x)) B ε)
    (hacyc : ∀ x, evK (χ x) B.Δ ≠ 0 → Acyclic x →
      sd.αK (evK (χ x)) = 0 ∧ uK (e x) (g x) = (0 : FractionRing O))
    -- the entry pole bound (5.8) at every sign character (tex 5517–5519)
    (hpole : ∀ x M i, ∀ j k, ((B.A i).map (signEval (χ x))) j k ∈ D.poleModLE M (4 * M))
    -- the budget (5.7) (tex 5384–5386)
    (dK hK cE tK : ℕ) (hm : B.mTot ≤ dK + 5) (hh : B.hSmith ≤ hK + 2 * cE + 2 * tK) :
    (∀ x (n : ℤ), HasSum (fun k : ℕ =>
        ((LC.coeffZ (signEval (χ x) (clearF B a)) (n - k) : ℤ_[2]) : ℚ_[2]) *
        (((PowerSeries.coeff k (g x) : ℤ_[2]) : ℚ_[2]) / 2 ^ e x))
        (LC.coeffZ (signEval (χ x) (sd.dd κ ε η)) n : ℚ_[2])) ∧
    (∀ i : ℤ, i < 0 → LC.coeffZ (aug (clearF B a)) i = 0) ∧
    LC.coeffZ (aug (clearF B a)) 0 ≠ 0 ∧
    (LC.coeffZ (aug (clearF B a)) 0).valuation = a + 4 * B.hSmith ∧
    a + 4 * B.hSmith ≤ a + 4 * (hK + 2 * cE + 2 * tK) ∧
    (∀ (M : ℕ) x (i : ℤ), i < -((16 * (dK + 5) * M : ℕ) : ℤ) →
      (2 : ℤ_[2]) ^ M ∣ LC.coeffZ (signEval (χ x) (clearF B a)) i) := by
  have h2K : (2 : FractionRing O) ≠ 0 := by
    have hinj := IsFractionRing.injective O (FractionRing O)
    intro h; apply h2O; apply hinj; rw [map_ofNat, h, map_zero]
  -- the integral identity `f_x g_x = 2^e d_x` in `O`
  have hint : ∀ x, signEval (χ x) (clearF B a) * algebraMap Lam O (g x) =
      2 ^ e x * signEval (χ x) (sd.dd κ ε η) := by
    intro x
    have hcoord : evK (χ x) B.Δ ≠ 0 → uK (e x) (g x) = evK (χ x) η * evK (χ x) κ *
        sd.αK (evK (χ x)) * (((2 : FractionRing O) ^ a)⁻¹ * sd.βK (evK (χ x))) *
          cleanT (evK (χ x)) B ε := fun hΔ =>
      coordinate_of_patterns (S := MonoidAlgebra O G) (K := FractionRing O) (evK (χ x)) sd κ ε η a
        (uK (e x) (g x)) (RankOne x) (Acyclic x) (hpat x) (hrank x hΔ) (hacyc x hΔ)
    have hid : evK (χ x) (clearF B a) * uK (e x) (g x) = evK (χ x) (sd.dd κ ε η) :=
      f_mul_u_eq_d (S := MonoidAlgebra O G) (K := FractionRing O) (evK (χ x)) sd κ ε η a
        (uK (e x) (g x)) h2K hn hcoord
    rw [evK_apply, evK_apply, uK] at hid
    apply IsFractionRing.injective O (FractionRing O)
    have h2e : (2 : FractionRing O) ^ e x ≠ 0 := pow_ne_zero _ h2K
    set A := algebraMap O (FractionRing O) (signEval (χ x) (clearF B a))
    set Bd := algebraMap O (FractionRing O) (signEval (χ x) (sd.dd κ ε η))
    set Gx := algebraMap O (FractionRing O) (algebraMap Lam O (g x))
    calc algebraMap O (FractionRing O) (signEval (χ x) (clearF B a) * algebraMap Lam O (g x))
        = A * Gx := map_mul _ _ _
      _ = (A * (Gx / 2 ^ e x)) * 2 ^ e x := by field_simp
      _ = Bd * 2 ^ e x := by rw [hid]
      _ = algebraMap O (FractionRing O) (2 ^ e x * signEval (χ x) (sd.dd κ ε η)) := by
          rw [map_mul, map_pow, map_ofNat, mul_comm]
  have hval := valuation_f0 B a hK cE tK hh
  have haug' : ∀ i, (B.A i).map (aug : MonoidAlgebra O G →ₐ[O] O).toRingHom =
      (B.A0 i).map (algebraMap Lam O) := haug
  have hf0 : aug (clearF B a) = algebraMap Lam O ((2 : Lam) ^ a * B.Δ0 ^ 4) :=
    f0_mem_Lam B (aug : MonoidAlgebra O G →ₐ[O] O).toRingHom haug' a
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n
    have hc := LC.conv (signEval (χ x) (clearF B a)) (g x) n
    rw [hint x, LC.coeffZ_two_pow_mul] at hc
    have hq := hc.map PadicInt.Coe.ringHom continuous_subtype_val
    have hq2 := hq.div_const ((2 : ℚ_[2]) ^ e x)
    have h2e : (2 : ℚ_[2]) ^ e x ≠ 0 := pow_ne_zero _ two_ne_zero
    convert hq2 using 1
    · funext k
      simp only [Function.comp_apply, map_mul, PadicInt.Coe.ringHom_apply]
      ring
    · simp only [map_mul, map_pow, map_ofNat, PadicInt.Coe.ringHom_apply]
      field_simp
  · intro i hi
    rw [hf0, LC.coeffZ_algebraMap]
    simp [show ¬ (0 ≤ i) by omega]
  · rw [hf0, LC.coeffZ_algebraMap]
    simpa using hval.1
  · rw [hf0, LC.coeffZ_algebraMap]
    simpa using hval.2.1
  · omega
  · intro M x i hi
    exact LC.dvd_of_mem_poleModLE M _ _ (f_pole B D (signEval (χ x)).toRingHom a dK M
      (fun i j k => hpole x M i j k) hm) i hi

end Assembly

end ZInQ.Manuscript.RC.Determinant
