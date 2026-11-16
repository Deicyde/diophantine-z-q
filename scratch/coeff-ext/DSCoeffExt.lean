import ZInQKernel.Contrib.OneProof.DSThm965Weak
import ZInQKernel.Contrib.T25.Bridge
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Eigenform
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.BadPrime.Eigenvector

/-! # coeff-ext: Diamond–Shurman 9.6.5 over `K_{f,λ}` and the eigenform dictionary

Task coeff-ext (2026-11-16), report `docs/research/coeff-ext.md`, scratch `scratch/coeff-ext/`.

Two coefficient-field dictionary steps are removed from the leaves `dsThm965Weak` and `dsThm966`.

* **Diamond–Shurman 9.6.5 over `K_{f,λ}`.** The field `DS965Weak.DSThm965Weak` states Deligne's theorem
  over `GL₂(ℚ̄_ℓ)` for every pair of embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_ℓ`. The print gives
  `ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})` for each prime `λ ∣ ℓ` of the number field `K_f`. `DSThm965Printed` states
  the print over Mathlib's `λ.adicCompletion K_f`; `dsThm965Weak_of_printed` proves the field from it and
  from `EigenformCoeffFieldFinite` (`K_f` is a number field, the print's presupposition). The glue
  (all proved here): `τ = ιL ∘ ιC⁻¹ : K_f → ℚ̄_ℓ` (algebraic numbers of `ℂ` lie in `ιC(ℚ̄)`), the place
  `λ_τ = {a ∈ 𝓞_{K_f} : ‖τ a‖ < 1}`, continuity of `τ` for the `λ_τ`-adic topology
  (`v_λ(x) ≤ v_λ(y) ⇒ ‖τ x‖ ≤ ‖τ y‖`), its extension `τ̂ : K_{f,λ_τ} → ℚ̄_ℓ` through the complete finite
  extension `ℚ_ℓ(τ(K_f))`, and `charpoly_map`.
* **"Normalized eigenform".** `IsNormalizedEigenformDS` is Diamond–Shurman's Def. 5.8.1 over Tau Ceti's
  `HeckeRing.GL2.Eigenform` (eigenvector of every `T_n`, the `U_p`, `p ∣ N`, included, in the `χ`-space of the
  diamond operators) with `a₁ = 1`. `isNormalizedEigenform_iff_DS` proves it equivalent to the kernel's
  coefficient form `ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform`; the `U_p` half is
  `heckeTCuspNat_eq_coeff_smul_all` (every prime `p`, from Tau Ceti's
  `heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom`). Both new 9.6.5/9.6.6 leaves use
  this definition, so they are direct instances of their prints.
* **Deligne–Serre.** `DSThm966Printed` is `ZInQ.Contrib.HodgeSplit.DSThm966` with the definition above,
  located at Deligne–Serre 1974 Thm 4.1 (4.1.1); `dsThm966_of_printed` and `dsThm966Printed_of_dsThm966`
  show the two equivalent.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace DSCoeffExt

open UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 NumberField IsDedekindDomain
open Polynomial (X C aeval)
open ZInQ.Contrib.G9.PkgI4 (Qbar GQ GaloisRep CF coeff HasNebentypus IsNormalizedEigenform LiesOver
  IsArithFrob)

/-! ## 0. Normalized eigenforms: Diamond–Shurman's definition and the kernel's coefficient form -/

section Dict

variable {N : ℕ} {k : ℤ}

/-- Diamond–Shurman Def. 5.8.1: a normalized eigenform in `S_k(N, χ)`. -/
def IsNormalizedEigenformDS [NeZero N] (f : CF N k) (χ : DirichletCharacter ℂ N) : Prop :=
  ∃ F : HeckeRing.GL2.Eigenform N k, F.toCuspForm = f ∧ F.χ = MulChar.toUnitHom χ ∧ coeff f 1 = 1

theorem ofUnitHom_toUnitHom (χ : DirichletCharacter ℂ N) :
    (MulChar.ofUnitHom (MulChar.toUnitHom χ) : DirichletCharacter ℂ N) = χ := by
  rw [MulChar.ofUnitHom_eq]
  exact MulChar.equivToUnitHom.symm_apply_apply χ

theorem ne_zero_of_coeff_one {f : CF N k} (h : coeff f 1 = 1) : f ≠ 0 := by
  rintro rfl
  simp only [coeff, FunLike.coe_zero, qExpansion_zero, map_zero] at h
  exact zero_ne_one h

/-- The `T_p`-eigenrelation at every prime `p`, the primes `p ∣ N` (`U_p`) included, from the kernel's
coefficient form. -/
theorem heckeTCuspNat_eq_coeff_smul_all [NeZero N] {g : CF N k} {χ : DirichletCharacter ℂ N}
    (hg : IsNormalizedEigenform g χ) {p : ℕ} (hp : p.Prime) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) g = coeff g p • g := by
  rw [heckeTCuspNat_eq_smul_iff_forall_qExpansion_coeff_prime_mul_ofUnitHom hp
    (T25.mem_cuspFormCharSpace_of_hasNebentypus hg.1), ofUnitHom_toUnitHom]
  intro m
  change coeff g (p * m) = coeff g p * coeff g m - _
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : coeff g 0 = 0 := T25.coeff_zero g
    simp only [mul_zero, Nat.zero_div, dvd_zero, ↓reduceIte]
    change coeff g 0 = coeff g p * coeff g 0 - _ * coeff g 0
    rw [h0]; ring
  have key := hg.2.2 p m hp.pos hm
  by_cases hpm : p ∣ m
  · obtain ⟨m', rfl⟩ := hpm
    have e1 : p * (p * m') / 1 ^ 2 = p * (p * m') := by simp
    have e2 : p * (p * m') / p ^ 2 = m' := by
      rw [← mul_assoc, ← pow_two, Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)]
    have e3 : p * m' / p = m' := Nat.mul_div_cancel_left _ hp.pos
    rw [Nat.gcd_eq_left (dvd_mul_right p m'), hp.divisors, Finset.sum_pair hp.one_lt.ne, e1,
      e2] at key
    simp only [dvd_mul_right, ↓reduceIte, e3]
    simp only [Nat.cast_one, map_one, one_zpow, one_mul] at key
    change _ = _ - _ * _ * coeff g m'
    linear_combination -key
  · have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hpm
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.divisors_one, Finset.sum_singleton] at key
    simp only [Nat.cast_one, map_one, one_zpow, one_mul, one_pow, Nat.div_one] at key
    simp only [hpm, ↓reduceIte, sub_zero]
    linear_combination -key

/-- **Coefficient form ⇒ Diamond–Shurman's definition.** -/
theorem isNormalizedEigenformDS_of [NeZero N] {g : CF N k} {χ : DirichletCharacter ℂ N}
    (hg : IsNormalizedEigenform g χ) : IsNormalizedEigenformDS g χ := by
  have hχ := T25.mem_cuspFormCharSpace_of_hasNebentypus hg.1
  refine ⟨Eigenform.ofForallPrime hχ (ne_zero_of_coeff_one hg.2.1)
    (fun p hp => ⟨coeff g p, ?_⟩), rfl, rfl, hg.2.1⟩
  apply Subtype.ext
  rw [coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k _ hp]
  exact heckeTCuspNat_eq_coeff_smul_all hg hp

/-- **Diamond–Shurman's definition ⇒ coefficient form.** -/
theorem isNormalizedEigenform_of_DS [NeZero N] {g : CF N k} {χ : DirichletCharacter ℂ N}
    (hg : IsNormalizedEigenformDS g χ) : IsNormalizedEigenform g χ := by
  obtain ⟨F, rfl, hχ, h1⟩ := hg
  have hneb := T25.hasNebentypus_of_mem_cuspFormCharSpace F.mem_charSpace
  rw [hχ, ofUnitHom_toUnitHom] at hneb
  refine ⟨hneb, h1, fun m n _ hn => ?_⟩
  lift n to ℕ+ using hn
  have h := qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 (N := N) (k := k)
    (χ := F.χ) (n := n) n.ne_zero ⟨F.toCuspForm, F.mem_charSpace⟩ m
  rw [F.isEigen n, Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map _),
    PowerSeries.coeff_smul, smul_eq_mul, ← F.qExpansion_coeff_eq_eigenvalue h1 n] at h
  have hχ' : χ = MulChar.ofUnitHom F.χ := by rw [hχ, ofUnitHom_toUnitHom]
  rw [hχ', mul_comm]
  exact h

theorem isNormalizedEigenform_iff_DS [NeZero N] {g : CF N k} {χ : DirichletCharacter ℂ N} :
    IsNormalizedEigenform g χ ↔ IsNormalizedEigenformDS g χ :=
  ⟨isNormalizedEigenformDS_of, isNormalizedEigenform_of_DS⟩

end Dict


/-! ## 1. Algebraic elements of `ℂ` come from `ℚ̄` -/

section Roots

open Polynomial

theorem mem_fieldRange_of_isIntegral (ιC : Qbar →ₐ[ℚ] ℂ) {x : ℂ} (hx : IsIntegral ℚ x) :
    x ∈ ιC.fieldRange := by
  set P := minpoly ℚ x
  have hP0 : P.map (algebraMap ℚ ℂ) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hx)
  have hroot : x ∈ (P.map (algebraMap ℚ ℂ)).roots := by
    rw [mem_roots hP0, IsRoot, eval_map_algebraMap]
    exact minpoly.aeval ℚ x
  have hmap : P.map (algebraMap ℚ ℂ) = (P.map (algebraMap ℚ Qbar)).map ιC.toRingHom := by
    rw [Polynomial.map_map]
    congr 1
    exact (ιC.comp_algebraMap).symm
  rw [hmap, ← roots_map_of_injective_of_card_eq_natDegree ιC.toRingHom.injective
    IsAlgClosed.card_roots_eq_natDegree] at hroot
  obtain ⟨r, -, hr⟩ := Multiset.mem_map.1 hroot
  exact ⟨r, hr⟩

end Roots

/-! ## 2. Norms on `ℚ̄_ℓ` -/

section Norm

open Polynomial

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Copy of `SwanBridge.isIntegral_iff_norm_le_one` (forward direction). -/
theorem norm_le_one_of_isIntegral (y : PadicAlgCl ℓ) (hy : IsIntegral ℤ_[ℓ] y) : ‖y‖ ≤ 1 := by
  have hyQ : IsIntegral ℚ_[ℓ] y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hyQ)]
  intro n
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[ℓ] hy, coeff_map]
  exact PadicInt.norm_le_one _

theorem norm_le_one_of_isIntegral_int (y : PadicAlgCl ℓ) (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 :=
  norm_le_one_of_isIntegral y (hy.tower_top)

theorem norm_natCast_prime : ‖(ℓ : PadicAlgCl ℓ)‖ < 1 := by
  have : (ℓ : PadicAlgCl ℓ) = algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) (ℓ : ℚ_[ℓ]) := by simp
  rw [this, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

end Norm

/-! ## 3. The place of a number field cut out by an embedding into `ℚ̄_ℓ` -/

section Place

variable {ℓ : ℕ} [Fact ℓ.Prime] {K : Type*} [Field K] [NumberField K] (τ : K →+* PadicAlgCl ℓ)

theorem norm_le_one_int (a : 𝓞 K) : ‖τ (a : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral_int _ ((a.isIntegral_coe).map τ.toIntAlgHom)

/-- The prime ideal `{a ∈ 𝓞_K : ‖τ a‖ < 1}`. -/
def placeIdeal : Ideal (𝓞 K) where
  carrier := {a | ‖τ (a : K)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, norm_mul] at *
    calc ‖τ (c : K)‖ * ‖τ (a : K)‖ ≤ 1 * ‖τ (a : K)‖ :=
          mul_le_mul_of_nonneg_right (norm_le_one_int τ c) (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact ha

theorem mem_placeIdeal {a : 𝓞 K} : a ∈ placeIdeal τ ↔ ‖τ (a : K)‖ < 1 := Iff.rfl

theorem natCast_mem_placeIdeal : (ℓ : 𝓞 K) ∈ placeIdeal τ := by
  rw [mem_placeIdeal]
  simpa using (norm_natCast_prime (ℓ := ℓ))

/-- The place `λ_τ` of `K` above `ℓ` cut out by `τ : K → ℚ̄_ℓ`. -/
def place : HeightOneSpectrum (𝓞 K) where
  asIdeal := placeIdeal τ
  isPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, mem_placeIdeal]
      simp
    · intro a b hab
      rw [mem_placeIdeal] at hab
      simp only [map_mul, norm_mul] at hab
      by_contra h
      push Not at h
      rw [mem_placeIdeal, mem_placeIdeal, not_lt, not_lt] at h
      have ha : ‖τ (a : K)‖ = 1 := le_antisymm (norm_le_one_int τ a) h.1
      have hb : ‖τ (b : K)‖ = 1 := le_antisymm (norm_le_one_int τ b) h.2
      rw [ha, hb, one_mul] at hab
      exact lt_irrefl _ hab
  ne_bot := by
    intro h
    have h1 := natCast_mem_placeIdeal (K := K) τ
    rw [h, Ideal.mem_bot] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero) h1

theorem norm_eq_one_of_not_mem {d : 𝓞 K} (hd : d ∉ (place τ).asIdeal) : ‖τ (d : K)‖ = 1 :=
  le_antisymm (norm_le_one_int τ d) (not_lt.1 hd)

/-- Valuation comparison: `v_λ(x) ≤ v_λ(y)` gives `‖τ x‖ ≤ ‖τ y‖`. -/
theorem norm_le_of_valuation_le {x y : K} (hy : y ≠ 0)
    (h : (place τ).valuation K x ≤ (place τ).valuation K y) : ‖τ x‖ ≤ ‖τ y‖ := by
  have hv : (place τ).valuation K (x / y) ≤ 1 := by
    rw [map_div₀]
    have : (place τ).valuation K y ≠ 0 := by simpa using hy
    exact (div_le_one₀ (zero_lt_iff.2 this)).2 h
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (place τ) _ hv
  have hd : ‖τ (d : 𝓞 K)‖ = 1 := norm_eq_one_of_not_mem τ d.2
  have hn := norm_le_one_int τ n
  have e := congrArg (fun z => ‖τ z‖) hnd
  simp only [map_mul, norm_mul, map_div₀, norm_div] at e
  have hd' : ‖τ (algebraMap (𝓞 K) K (d : 𝓞 K))‖ = 1 := hd
  rw [hd', mul_one] at e
  have hyn : 0 < ‖τ y‖ := norm_pos_iff.2 ((map_ne_zero τ).2 hy)
  have : ‖τ x‖ / ‖τ y‖ ≤ 1 := e ▸ hn
  exact (div_le_one₀ hyn).1 this

end Place

/-! ## 4. Extension to the completion `K_λ` -/

section Completion

variable {ℓ : ℕ} [Fact ℓ.Prime] {K : Type*} [Field K] [NumberField K] (τ : K →+* PadicAlgCl ℓ)

/-- `τ` as a ring hom on `WithVal v_λ`. -/
def τW : WithVal ((place τ).valuation K) →+* PadicAlgCl ℓ :=
  τ.comp (WithVal.equiv ((place τ).valuation K)).toRingHom

theorem continuous_τW : Continuous (τW τ) := by
  refine continuous_of_continuousAt_zero (τW τ).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hs
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_prime (ℓ := ℓ))
  set y : K := (ℓ : K) ^ m
  have hy : y ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)
  set yW : WithVal ((place τ).valuation K) := WithVal.toVal _ y
  have hyv : (Valued.v : Valuation (WithVal ((place τ).valuation K)) _) yW ≠ 0 := by
    rw [← WithVal.apply_ofVal]
    simpa [yW] using hy
  have hres : (Valued.v : Valuation (WithVal ((place τ).valuation K)) _).restrict yW ≠ 0 := by
    rwa [Ne, Valuation.restrict_eq_zero_iff]
  rw [Filter.mem_map, Valued.mem_nhds_zero]
  refine ⟨Units.mk0 _ hres, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hx
  show (τW τ) x ∈ s
  apply hball
  rw [Metric.mem_ball, dist_zero_right]
  have hle : (place τ).valuation K (WithVal.ofVal x) ≤ (place τ).valuation K y := by
    rw [WithVal.apply_ofVal, WithVal.apply_ofVal]
    exact hx.le
  calc ‖τW τ x‖ = ‖τ (WithVal.ofVal x)‖ := rfl
    _ ≤ ‖τ y‖ := norm_le_of_valuation_le τ hy hle
    _ = ‖(ℓ : PadicAlgCl ℓ)‖ ^ m := by simp [y]
    _ < ε := hm

/-- A finite extension of `ℚ_ℓ` inside `ℚ̄_ℓ` containing `τ(K)`. -/
def tgt : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) :=
  IntermediateField.adjoin ℚ_[ℓ] (Set.range (fun i => τ (Module.finBasis ℚ K i)))

instance : FiniteDimensional ℚ_[ℓ] (tgt τ) :=
  IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsIntegral.isIntegral x))

theorem mem_tgt (x : K) : τ x ∈ tgt τ := by
  rw [← (Module.finBasis ℚ K).sum_repr x, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, map_mul, eq_ratCast, map_ratCast]
  exact mul_mem (SubfieldClass.ratCast_mem _ _)
    (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)

instance : CompleteSpace (tgt τ) := by
  have : FiniteDimensional ℚ_[ℓ] ((tgt τ).toSubalgebra.toSubmodule) :=
    (inferInstance : FiniteDimensional ℚ_[ℓ] (tgt τ))
  exact (Submodule.complete_of_finiteDimensional ((tgt τ).toSubalgebra.toSubmodule)).completeSpace_coe

/-- `τ` into the complete field `tgt τ`. -/
def τE : WithVal ((place τ).valuation K) →+* tgt τ :=
  (τW τ).codRestrict (tgt τ) (fun _ => mem_tgt τ _)

theorem continuous_τE : Continuous (τE τ) :=
  Continuous.subtype_mk (continuous_τW τ) _

/-- The continuous extension `K_λ → ℚ̄_ℓ` of `τ`. -/
def τhat : (place τ).adicCompletion K →+* PadicAlgCl ℓ :=
  ((tgt τ).val.toRingHom.comp (UniformSpace.Completion.extensionHom (τE τ) (continuous_τE τ))).comp
    (HeightOneSpectrum.adicCompletion.equiv K (place τ)).toRingHom

theorem continuous_τhat : Continuous (τhat τ) :=
  continuous_subtype_val.comp ((UniformSpace.Completion.continuous_extension).comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion K (place τ)))

theorem τhat_algebraMap (x : K) : τhat τ (algebraMap K ((place τ).adicCompletion K) x) = τ x := by
  simp only [τhat, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]
  have : (HeightOneSpectrum.adicCompletion.equiv K (place τ))
      (algebraMap K ((place τ).adicCompletion K) x) =
      ((WithVal.toVal ((place τ).valuation K) x : WithVal _) :
        ((place τ).valuation K).Completion) := rfl
  rw [this, UniformSpace.Completion.extensionHom_coe]
  rfl

end Completion

/-! ## 5. The coefficient field `K_f` and the embedding `ιL ∘ ιC⁻¹ : K_f → ℚ̄_ℓ` -/

section CoeffField

variable {N : ℕ} {k : ℤ}

/-- **The coefficient field** `K_f = ℚ(a_n(f) : n ≥ 0) ⊆ ℂ` (Diamond–Shurman §6.5, §9.6; the same definition
as `coeffField` of `ZInQKernel/HDecomp/ModCurves/Defs.lean`, over `ZInQ.Contrib.G9.PkgI4.coeff`). -/
def coeffField (f : CF N k) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range (coeff f))

theorem coeff_mem_coeffField (f : CF N k) (n : ℕ) : coeff f n ∈ coeffField f :=
  IntermediateField.subset_adjoin ℚ _ ⟨n, rfl⟩

variable (ιC : Qbar →ₐ[ℚ] ℂ) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]

theorem exists_pre (x : K) : ∃ y : Qbar, ιC y = x :=
  (AlgHom.mem_fieldRange (f := ιC)).1
    (mem_fieldRange_of_isIntegral ιC ((Algebra.IsIntegral.isIntegral x).map K.val))

/-- `ιC⁻¹` on `K`. -/
def pre (x : K) : Qbar := (exists_pre ιC K x).choose

theorem ιC_pre (x : K) : ιC (pre ιC K x) = x := (exists_pre ιC K x).choose_spec

theorem pre_eq {x : K} {y : Qbar} (h : ιC y = x) : pre ιC K x = y :=
  ιC.toRingHom.injective ((ιC_pre ιC K x).trans h.symm)

/-- `ιC⁻¹ : K → ℚ̄` as a ring hom. -/
def preHom : K →+* Qbar where
  toFun := pre ιC K
  map_one' := pre_eq ιC K (by simp)
  map_mul' x y := pre_eq ιC K (by rw [map_mul, ιC_pre, ιC_pre]; rfl)
  map_zero' := pre_eq ιC K (by simp)
  map_add' x y := pre_eq ιC K (by rw [map_add, ιC_pre, ιC_pre]; rfl)

/-- `ιL ∘ ιC⁻¹ : K → ℚ̄_ℓ`. -/
def emb {ℓ : ℕ} [Fact ℓ.Prime] (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) : K →+* PadicAlgCl ℓ :=
  ιL.toRingHom.comp (preHom ιC K)

theorem emb_apply {ℓ : ℕ} [Fact ℓ.Prime] (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ) (x : K) :
    emb ιC K ιL x = ιL (pre ιC K x) := rfl

end CoeffField

/-! ## 6. Extension of scalars of a `2`-dimensional representation -/

section MapRep

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type*} [CommRing A] [TopologicalSpace A]

/-- `ρ` with coefficients extended along a continuous `φ : A → ℚ̄_ℓ`. -/
def mapRep (φ : A →+* PadicAlgCl ℓ) (hφ : Continuous φ) (ρ : GQ →* GL (Fin 2) A)
    (hρ : Continuous ρ) : GaloisRep ℓ 2 where
  toHom := (Units.map (φ.mapMatrix : Matrix (Fin 2) (Fin 2) A →+*
    Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).toMonoidHom).comp ρ
  continuous_toHom := (Units.continuous_map (continuous_id.matrix_map hφ)).comp hρ

theorem mapRep_mat (φ : A →+* PadicAlgCl ℓ) (hφ : Continuous φ) (ρ : GQ →* GL (Fin 2) A)
    (hρ : Continuous ρ) (σ : GQ) :
    (mapRep φ hφ ρ hρ).mat σ = (ρ σ : Matrix (Fin 2) (Fin 2) A).map φ := rfl

theorem aeval_map_matrix {B : Type*} [CommRing B] (φ : A →+* B) (M : Matrix (Fin 2) (Fin 2) A)
    (P : Polynomial A) : aeval (M.map φ) (P.map φ) = (aeval M P).map φ := by
  have h : (algebraMap B (Matrix (Fin 2) (Fin 2) B)).comp φ =
      (φ.mapMatrix : Matrix (Fin 2) (Fin 2) A →+* Matrix (Fin 2) (Fin 2) B).comp
        (algebraMap A (Matrix (Fin 2) (Fin 2) A)) := by
    ext a i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
    split_ifs <;> simp
  exact (Polynomial.map_aeval_eq_aeval_map h P M).symm

end MapRep

/-! ## 7. The leaves -/

/-- **LEAF (Diamond–Shurman Thm 9.6.5, printed form over `K_{f,λ}`).** Diamond–Shurman, *A First Course in
Modular Forms*, GTM 228 (2005), Thm 9.6.5 (`k ≥ 2`; Deligne, Sém. Bourbaki 355, 1969/1971; Shimura 1971
Thm 7.14 for `k = 2`; numbering UNVERIFIED, no network): let `f ∈ S_k(N, χ)` be a normalized eigenform with
number field `K_f`, `ℓ` a prime and `λ` a maximal ideal of `𝓞_{K_f}` over `ℓ`. There is a continuous
`ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})`, unramified at every `p ∤ ℓN`, such that for every maximal ideal `𝔭` of `ℤ̄`
over such a `p`, `ρ_{f,λ}(Frob_𝔭)` has characteristic polynomial (or, in the weakest reading, satisfies)
`x² − a_p(f) x + χ(p) p^{k−1}`.

Lean form: "normalized eigenform" is Diamond–Shurman's Def. 5.8.1 (`IsNormalizedEigenformDS`, over Tau Ceti's
Hecke operators `T_n` for every `n`, nebentypus by the diamond operators, `a₁ = 1`); `K_f = coeffField f`,
supposed a number field (the print's presupposition, the leaf `EigenformCoeffFieldFinite`); `λ` a
`HeightOneSpectrum (𝓞 K_f)` containing `ℓ`; `K_{f,λ}` Mathlib's `λ.adicCompletion K_f` with its valuation
topology; the polynomial has coefficients `a_p(f) ∈ K_f` and every `b ∈ K_f` equal to `χ(p) p^{k−1}`, mapped
into `K_{f,λ}`. Places of `ℚ̄` (`AlgebraicClosure ℚ`) are valuation subrings, `Frob_𝔭` is pkg-I4's
`IsArithFrob`, unramified means trivial on every inertia group above `p`. The per-Frobenius conclusion is the
disjunction "characteristic polynomial ∨ satisfies", so either printed wording gives it by or-introduction. -/
def DSThm965Printed : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    2 ≤ k → IsNormalizedEigenformDS f χ → ∀ [NumberField (coeffField f)]
    (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (coeffField f))),
    (ℓ : 𝓞 (coeffField f)) ∈ lam.asIdeal →
    ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (coeffField f)), Continuous ρ ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ b : coeffField f, (b : ℂ) = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) →
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2) (lam.adicCompletion (coeffField f))).charpoly =
              X ^ 2 - C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
                ⟨coeff f p, coeff_mem_coeffField f p⟩) * X +
                C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f)) b) ∨
            aeval (ρ σ : Matrix (Fin 2) (Fin 2) (lam.adicCompletion (coeffField f)))
              (X ^ 2 - C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
                ⟨coeff f p, coeff_mem_coeffField f p⟩) * X +
                C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f)) b)) = 0

/-- **LEAF (`K_f` is a number field).** For a normalized eigenform `f ∈ S_k(N, χ)` (Diamond–Shurman Def. 5.8.1),
`k ≥ 2`, the field `K_f = ℚ(a_n(f) : n)` is finite over `ℚ`. Diamond–Shurman Thm 6.5.1 for `k = 2`
(UNVERIFIED); for every `k`, Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971),
Thm 3.52 (`S_k(Γ₁(N))` has a basis with rational Fourier coefficients) with the Hecke-stability of that
rational structure (§3.5) (numbers UNVERIFIED). Diamond–Shurman 9.6.5 presupposes it ("with number field
`K_f`"). -/
def EigenformCoeffFieldFinite : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    2 ≤ k → IsNormalizedEigenformDS f χ → FiniteDimensional ℚ (coeffField f)

/-- **LEAF (Deligne–Serre, printed form).** Deligne–Serre, *Formes modulaires de poids 1*, Ann. Sci. ÉNS (4) 7
(1974), Thm 4.1 with display (4.1.1), p. 514 (locator from the task brief, not read here: UNVERIFIED);
Diamond–Shurman Thm 9.6.6 states the same. For a normalized eigenform `f ∈ S_1(N, χ)` (Diamond–Shurman
Def. 5.8.1; Deligne–Serre's hypothesis, a nonzero form of type `(1, χ)` that is an eigenvector of the `T_p`,
`p ∤ N`, with eigenvalues `a_p`, holds for it since `a₁ = 1`) there is a continuous
`ρ_f : G_ℚ → GL₂(ℂ)` with finite image, unramified at every `p ∤ N`, with `tr ρ_f(Frob_𝔭) = a_p(f)` and
`det ρ_f(Frob_𝔭) = χ(p)`. `ZInQ.Contrib.HodgeSplit.DSThm966` word for word except that "normalized eigenform"
is Diamond–Shurman's definition (`IsNormalizedEigenformDS`) instead of the kernel's coefficient form. -/
def DSThm966Printed : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (g : CF N 1),
    IsNormalizedEigenformDS g χ →
    ∃ ρ : GQ →* GL (Fin 2) ℂ, Continuous ρ ∧ (Set.range ρ).Finite ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        (∀ v : ValuationSubring Qbar, LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).trace = coeff g p ∧
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).det = χ (p : ZMod N)

/-! ## 8. The fields from the printed leaves -/

/-- `dsThm966` from Deligne–Serre's printed form: the coefficient form gives Diamond–Shurman's definition. -/
theorem dsThm966_of_printed (h : DSThm966Printed) : ZInQ.Contrib.HodgeSplit.DSThm966 := by
  intro N χ g hN hg
  have : NeZero N := ⟨hN.ne'⟩
  exact h N χ g (isNormalizedEigenformDS_of hg)

/-- Conversely the printed form follows from `dsThm966` (the two definitions agree): the new leaf is
equivalent to the field it replaces. -/
theorem dsThm966Printed_of_dsThm966 (h : ZInQ.Contrib.HodgeSplit.DSThm966) : DSThm966Printed := by
  intro N _ χ g hg
  exact h N χ g (Nat.pos_of_ne_zero (NeZero.ne N)) (isNormalizedEigenform_of_DS hg)

theorem coeff_sq_relation {N : ℕ} {k : ℤ} {g : CF N k} {χ : DirichletCharacter ℂ N}
    (hg : IsNormalizedEigenform g χ) {p : ℕ} (hp : p.Prime) :
    coeff g p ^ 2 - coeff g (p * p) = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) := by
  have key := hg.2.2 p p hp.pos hp.pos
  have e2 : p * p / p ^ 2 = 1 := by rw [← pow_two, Nat.div_self (pow_pos hp.pos 2)]
  rw [Nat.gcd_self, hp.divisors, Finset.sum_pair hp.one_lt.ne, one_pow, Nat.div_one, e2,
    hg.2.1] at key
  simp only [Nat.cast_one, map_one, one_zpow, one_mul, mul_one] at key
  linear_combination key

/-- **`dsThm965Weak` from Diamond–Shurman 9.6.5 over `K_{f,λ}` and the finiteness of `K_f`.** For given
`ιC`, `ιL`, take `τ = ιL ∘ ιC⁻¹ : K_f → ℚ̄_ℓ`, the place `λ_τ` it cuts out, the representation `ρ_{f,λ_τ}` of
the printed leaf, and extend scalars along the continuous extension `K_{f,λ_τ} → ℚ̄_ℓ` of `τ`. -/
theorem dsThm965Weak_of_printed (h1 : DSThm965Printed) (h2 : EigenformCoeffFieldFinite) :
    DS965Weak.DSThm965Weak := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  have : NeZero N := ⟨hN.ne'⟩
  have hDS := isNormalizedEigenformDS_of hg
  have : FiniteDimensional ℚ (coeffField g) := h2 N k χ g hk hDS
  have : NumberField (coeffField g) := ⟨⟩
  obtain ⟨ρ, hρc, hρ⟩ := h1 N k χ g hk hDS ℓ (place (emb ιC (coeffField g) ιL))
    (natCast_mem_placeIdeal _)
  refine ⟨mapRep (τhat (emb ιC (coeffField g) ιL)) (continuous_τhat _) ρ hρc, fun p hp hpN => ?_⟩
  obtain ⟨hun, hfr⟩ := hρ p hp hpN
  set a : coeffField g := ⟨coeff g p, coeff_mem_coeffField g p⟩ with ha
  set b : coeffField g := a ^ 2 - ⟨coeff g (p * p), coeff_mem_coeffField g _⟩ with hbdef
  have hb : (b : ℂ) = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) := by
    rw [← coeff_sq_relation hg hp]
    rfl
  refine ⟨?_, pre ιC (coeffField g) a, pre ιC (coeffField g) b, ιC_pre _ _ a,
    (ιC_pre _ _ b).trans hb, fun v σ hv hσ => ?_⟩
  · intro v hv σ hσ
    show Units.map _ (ρ _) = 1
    rw [hun v hv σ hσ, map_one]
  · have hP : (X ^ 2 - C (algebraMap (coeffField g) ((place (emb ιC (coeffField g) ιL)).adicCompletion
          (coeffField g)) a) * X + C (algebraMap (coeffField g) _ b)).map
          (τhat (emb ιC (coeffField g) ιL)) =
        X ^ 2 - C (ιL (pre ιC (coeffField g) a)) * X + C (ιL (pre ιC (coeffField g) b)) := by
      simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C, τhat_algebraMap, emb_apply]
    rcases hfr b hb v σ hv hσ with h | h
    · left
      rw [mapRep_mat, Matrix.charpoly_map, h, hP]
    · right
      rw [mapRep_mat, ← hP, aeval_map_matrix, h, Matrix.map_zero _ (map_zero _)]

/-! ## 9. The new leaves are consequences of the prints under every reading -/

/-- Cayley–Hamilton direction: the "characteristic polynomial" wording gives the disjunction (trivially, by
or-introduction); recorded so the reading is explicit. -/
theorem dsThm965Printed_of_charpoly
    (h : ∀ (N : ℕ) [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
      2 ≤ k → IsNormalizedEigenformDS f χ → ∀ [NumberField (coeffField f)]
      (ℓ : ℕ) [Fact ℓ.Prime] (lam : HeightOneSpectrum (𝓞 (coeffField f))),
      (ℓ : 𝓞 (coeffField f)) ∈ lam.asIdeal →
      ∃ ρ : GQ →* GL (Fin 2) (lam.adicCompletion (coeffField f)), Continuous ρ ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
          (∀ v : ValuationSubring Qbar, LiesOver v p →
            ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : GQ) = 1) ∧
          ∀ b : coeffField f, (b : ℂ) = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) →
          ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
            (ρ σ : Matrix (Fin 2) (Fin 2) (lam.adicCompletion (coeffField f))).charpoly =
                X ^ 2 - C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f))
                  ⟨coeff f p, coeff_mem_coeffField f p⟩) * X +
                  C (algebraMap (coeffField f) (lam.adicCompletion (coeffField f)) b)) :
    DSThm965Printed := by
  intro N _ k χ f hk hf _ ℓ _ lam hlam
  obtain ⟨ρ, hc, hρ⟩ := h N k χ f hk hf ℓ lam hlam
  exact ⟨ρ, hc, fun p hp hpN => ⟨(hρ p hp hpN).1, fun b hb v σ hv hσ =>
    Or.inl ((hρ p hp hpN).2 b hb v σ hv hσ)⟩⟩

end DSCoeffExt
