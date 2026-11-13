import ZInQKernel.HDecomp.Faltings.HodgeData

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt3 from
`scratch/def-faltings/Faltings.lean`, §7-§14.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

namespace ZInQ.DefFaltings

open NumberField MeasureTheory

/-! ## 7. Hermitian lines given by fractional ideals: the closed formula (part of node AR3)

Every invertible `𝓞_K`-module with a trivialization of its generic fibre is a fractional ideal
`I ⊆ K`. For such lines `#(I / 𝓞_K x) · N(I) = |N_{K/ℚ}(x)|` (`secIndex_mul_absNorm`), so
`deg(I, ρ·|σ(·)|) = −log N(I) − ∑_σ log ρ_σ` (`arakelovDegree_ofFractionalIdeal`). This is the form
in which AT1a meets a Néron lattice `𝔞 · dx/(2y + a₁x + a₃)` that is not free (class number > 1). -/

section FractionalIdeal

open Pointwise
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- **Index formula.** For a fractional ideal `I` and `0 ≠ x ∈ I`:
`#(I / 𝓞_K x) · N(I) = |N_{K/ℚ}(x)|`. -/
theorem secIndex_mul_absNorm (I : FractionalIdeal (𝓞 K)⁰ K) {x : K} (hx : x ∈ I) (hx0 : x ≠ 0) :
    (secIndex (I : Submodule (𝓞 K) K) x : ℚ) * FractionalIdeal.absNorm I =
      |Algebra.norm ℚ x| := by
  classical
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  have hd0' : d ≠ 0 := nonZeroDivisors.ne_zero I.den.2
  have hd0 : (d : K) ≠ 0 := by exact_mod_cast hd0'
  let f : K →ₗ[𝓞 K] K := DistribSMul.toLinearMap (𝓞 K) K I.den
  have hf_apply : ∀ z, f z = (d : K) * z := by
    intro z
    show I.den • z = (d : K) * z
    rw [Submonoid.smul_def, ← algebraMap_smul K, smul_eq_mul]
  have hf : Function.Injective f := fun a b h => by
    rw [hf_apply, hf_apply] at h
    exact mul_left_cancel₀ hd0 h
  have hfI : Submodule.map f (I : Submodule (𝓞 K) K) =
      Submodule.map (Algebra.linearMap (𝓞 K) K) I.num :=
    FractionalIdeal.den_mul_self_eq_num I
  -- `d x = y` with `y ∈ I.num`
  have hdx : f x ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num :=
    hfI ▸ Submodule.mem_map_of_mem hx
  obtain ⟨y, hy, hyx⟩ := hdx
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hyx
    exact hx0 (hf (by rw [← hyx, map_zero]))
  let ι : 𝓞 K →ₗ[𝓞 K] K := Algebra.linearMap (𝓞 K) K
  have hι : Function.Injective ι := IsFractionRing.injective (𝓞 K) K
  have hspan : Submodule.map f (Submodule.span (𝓞 K) {x}) =
      Submodule.map ι (Ideal.span {y}) := by
    rw [Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton]
    simp only [ι] at hyx ⊢
    rw [hyx]
  -- transport the index
  have h1 : secIndex (I : Submodule (𝓞 K) K) x =
      (Ideal.span {y}).toAddSubgroup.relIndex I.num.toAddSubgroup := by
    unfold secIndex
    have e1 := AddSubgroup.relIndex_map_map_of_injective
      (Submodule.span (𝓞 K) {x}).toAddSubgroup (I : Submodule (𝓞 K) K).toAddSubgroup
      (f := (f : K →+ K)) hf
    rw [← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hspan, hfI,
      Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
      AddSubgroup.relIndex_map_map_of_injective _ _ hι] at e1
    exact e1.symm
  have hle : Ideal.span {y} ≤ I.num := (Ideal.span_singleton_le_iff_mem _).mpr hy
  have h2 : (Ideal.span {y}).toAddSubgroup.relIndex I.num.toAddSubgroup *
      Ideal.absNorm I.num = (Algebra.norm ℤ y).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact AddSubgroup.relIndex_mul_index (Submodule.toAddSubgroup_mono hle)
  have hnum0 : Ideal.absNorm I.num ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    have : Algebra.norm ℤ y ≠ 0 := (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hy0
    omega
  -- norms
  have hNy : (Algebra.norm ℚ (y : K)) = Algebra.norm ℚ (d : K) * Algebra.norm ℚ x := by
    have : (y : K) = (d : K) * x := by rw [← hf_apply]; exact hyx
    rw [this, map_mul]
  rw [FractionalIdeal.absNorm_eq, h1]
  have hNyz : ((Algebra.norm ℤ y).natAbs : ℚ) = |Algebra.norm ℚ (y : K)| := by
    rw [← Algebra.coe_norm_int]; simp [Nat.cast_natAbs]
  have hNdz : ((Algebra.norm ℤ d : ℤ) : ℚ) = Algebra.norm ℚ (d : K) := Algebra.coe_norm_int d
  have hNd0 : Algebra.norm ℚ (d : K) ≠ 0 := by
    rw [← hNdz]; exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hd0'
  have key : ((Ideal.span {y}).toAddSubgroup.relIndex I.num.toAddSubgroup : ℚ) *
      (Ideal.absNorm I.num : ℚ) = |Algebra.norm ℚ (d : K)| * |Algebra.norm ℚ x| := by
    rw [← abs_mul, ← hNy, ← hNyz]; exact_mod_cast h2
  have hden : ((|Algebra.norm ℤ (I.den : 𝓞 K)| : ℤ) : ℚ) = |Algebra.norm ℚ (d : K)| := by
    rw [Int.cast_abs]; exact congr_arg _ hNdz
  rw [hden, ← mul_div_assoc, key]
  field_simp

/-- The Hermitian line `(I, ρ_σ · |σ(·)|)` on `Spec 𝓞_K`. -/
noncomputable def HermitianLattice.ofFractionalIdeal (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (ρ : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) : HermitianLattice K K where
  lattice := I
  finrank_eq_one := Module.finrank_self K
  isLattice := by
    obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
    refine ⟨x, hxI, hx0, fun h0 => ?_⟩
    have := secIndex_mul_absNorm I hxI hx0
    rw [h0, Nat.cast_zero, zero_mul] at this
    exact (Algebra.norm_ne_zero_iff.mpr hx0) (abs_eq_zero.mp this.symm)
  norm σ x := ρ σ * ‖σ x‖
  norm_smul σ a x := by rw [smul_eq_mul, map_mul, norm_mul]; ring
  norm_pos σ x hx := mul_pos (hρ σ) (by simpa using hx)

/-- **Closed formula:** `deg(I, ρ·|σ(·)|) = −log N(I) − ∑_σ log ρ_σ`. -/
theorem HermitianLattice.arakelovDegree_ofFractionalIdeal (I : FractionalIdeal (𝓞 K)⁰ K)
    (hI : I ≠ 0) (ρ : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) :
    (HermitianLattice.ofFractionalIdeal I hI ρ hρ).arakelovDegree =
      -Real.log (FractionalIdeal.absNorm I : ℝ) - ∑ σ : K →+* ℂ, Real.log (ρ σ) := by
  set L := HermitianLattice.ofFractionalIdeal I hI ρ hρ
  obtain ⟨hxI, hx0, hi⟩ := L.isLattice.choose_spec
  set x := L.isLattice.choose
  have hidx := secIndex_mul_absNorm I hxI hx0
  have hN0 : FractionalIdeal.absNorm I ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hidx
    exact (Algebra.norm_ne_zero_iff.mpr hx0) (abs_eq_zero.mp hidx.symm)
  unfold HermitianLattice.arakelovDegree HermitianLattice.degreeAt
  have hsum : ∑ σ : K →+* ℂ, Real.log (L.norm σ x) =
      ∑ σ : K →+* ℂ, Real.log (ρ σ) + Real.log |(Algebra.norm ℚ x : ℝ)| := by
    rw [← sum_log_norm_embeddings x hx0, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact Real.log_mul (hρ σ).ne' (by simpa using hx0)
  rw [hsum]
  have hidxR : (secIndex L.lattice x : ℝ) * (FractionalIdeal.absNorm I : ℝ) =
      |(Algebra.norm ℚ x : ℝ)| := by exact_mod_cast hidx
  have hlog : Real.log (secIndex L.lattice x : ℝ) + Real.log (FractionalIdeal.absNorm I : ℝ) =
      Real.log |(Algebra.norm ℚ x : ℝ)| := by
    rw [← Real.log_mul (by exact_mod_cast hi) (by exact_mod_cast hN0), hidxR]
  linarith

end FractionalIdeal

/-! ## 8. Acceptance test AT1 for a non-free Hodge lattice

For an elliptic curve with semistable reduction everywhere, the Néron lattice of invariant
differentials is `𝔞 · ω` with `ω = dx/(2y + a₁x + a₃)` and `𝔞` the fractional ideal with
`ord_𝔭 𝔞 = (ord_𝔭 Δ − ord_𝔭 Δ_min)/12` (`Δ_min` the minimal discriminant at `𝔭`). With
`ord_𝔭 Δ_min = max(0, −ord_𝔭 j)` (semistable) and the product formula,
`−12 log N(𝔞) = ∑_{v∤∞} log⁺|j|_v − ∑_σ log|σΔ|`. That identity is node AT1a (literature: Néron
models of elliptic curves); here it is the hypothesis `hNeron`. -/

section AcceptanceIdeal

open Polynomial
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- `σ : K → ℂ` as a `σ`-semilinear map. -/
def embCoeff (σ : K →+* ℂ) : K →ₛₗ[σ] ℂ where
  toFun := σ
  map_add' := map_add σ
  map_smul' a v := by simp

/-- The Hodge data `(𝔞 ⊆ K, Λ_σ)` of dimension 1: `V = K` (`ω ↦ 1`), lattice `𝔞`, period lattices
`(L σ).lattice1`, `ω ↦ dz`. -/
noncomputable def HodgeData.ofIdeal (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) : HodgeData K 1 K where
  lattice := 𝔞
  finrank_eq_one := Module.finrank_self K
  isLattice := (HermitianLattice.ofFractionalIdeal 𝔞 h𝔞 (fun _ => 1) (fun _ => one_pos)).isLattice
  periods σ := (L σ).lattice1
  periods_discrete _ := inferInstance
  periods_isZLattice _ := inferInstance
  coeff σ := embCoeff σ
  coeff_ne_zero σ h := by
    have := congr_arg (fun f => f 1) h
    simp [embCoeff] at this

theorem HodgeData.modelHeight_ofIdeal (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) :
    (HodgeData.ofIdeal 𝔞 h𝔞 L).modelHeight =
      (-Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) -
        (1 / 2) * ∑ σ : K →+* ℂ, Real.log (ZLattice.covolume (L σ).lattice)) /
          Module.finrank ℚ K := by
  set ρ : (K →+* ℂ) → ℝ := fun σ => Real.sqrt (ZLattice.covolume (L σ).lattice)
  have hρ : ∀ σ, 0 < ρ σ := fun σ => Real.sqrt_pos.mpr (ZLattice.covolume_pos _ volume)
  have hdeg := HermitianLattice.arakelovDegree_ofFractionalIdeal 𝔞 h𝔞 ρ hρ
  have heq : (HodgeData.ofIdeal 𝔞 h𝔞 L).hodgeBundle.arakelovDegree =
      (HermitianLattice.ofFractionalIdeal 𝔞 h𝔞 ρ hρ).arakelovDegree := by
    unfold HermitianLattice.arakelovDegree HermitianLattice.degreeAt
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    simp only [HodgeData.hodgeBundle, HodgeData.norm, HermitianLattice.ofFractionalIdeal,
      HodgeData.ofIdeal, embCoeff, LinearMap.coe_mk, AddHom.coe_mk, ρ,
      PeriodPair.covolume_lattice1]
    ring
  rw [HodgeData.modelHeight, heq, hdeg]
  congr 1
  have hs : ∀ σ : K →+* ℂ, Real.log (ρ σ) = (1 / 2) * Real.log (ZLattice.covolume (L σ).lattice) :=
      by
    intro σ
    simp only [ρ]
    rw [Real.log_sqrt (ZLattice.covolume_pos _ volume).le]
    ring
  rw [Finset.sum_congr rfl fun σ _ => hs σ, ← Finset.mul_sum]

/-- **Acceptance test AT1 (semistable elliptic curves, any class number), conditional form.**
Given the area formula AT1c (`PeriodAreaFormula`), period pairs `L σ` with Weierstrass polynomial
`4x³ − g₂(L σ)x − g₃(L σ)` equal to that of `W^σ` (AT1b), and a Hodge lattice `𝔞 · ω` satisfying the
Néron identity AT1a (`hNeron`), the model height equals pkg-I5's `faltingsHeightEC W`. Proved. -/
theorem modelHeight_ofIdeal_eq_faltingsHeightEC (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      4 * X ^ 3 - C (L σ).g₂ * X - C (L σ).g₃)
    (hNeron : -12 * Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) =
      finiteHeightPart W.j - ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) :
    (HodgeData.ofIdeal 𝔞 h𝔞 L).modelHeight = faltingsHeightEC W := by
  rw [HodgeData.modelHeight_ofIdeal, faltingsHeightEC, ← hNeron]
  have hterm : ∀ σ : K →+* ℂ, ZLattice.covolume (L σ).lattice =
      hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
    intro σ; rw [hP, hA]
  simp only [hterm]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp

end AcceptanceIdeal

/-! ## 9. Base change: the archimedean count (part of nodes AR3, H4)

Each complex embedding `σ` of `K` has exactly `[L:K]` extensions to `L`, so sums over the
embeddings of `L` of functions of the restriction are `[L:K]` times the sums over `K`. -/

section BaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open Classical in
theorem card_embeddings_over (σ : K →+* ℂ) :
    (Finset.univ.filter (fun τ : L →+* ℂ => τ.comp (algebraMap K L) = σ)).card =
      Module.finrank K L := by
  let _ : Algebra K ℂ := σ.toAlgebra
  have hc : ∀ τ : {τ : L →+* ℂ // τ.comp (algebraMap K L) = σ}, ∀ k : K,
      τ.1 (algebraMap K L k) = algebraMap K ℂ k := fun τ k => by
    have := congr_arg (fun f : K →+* ℂ => f k) τ.2
    simpa [RingHom.algebraMap_toAlgebra] using this
  have hc' : ∀ φ : L →ₐ[K] ℂ, (φ : L →+* ℂ).comp (algebraMap K L) = σ := fun φ => by
    ext k
    simp [RingHom.algebraMap_toAlgebra]
  rw [← AlgHom.card K L ℂ, ← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun τ => ⟨τ.1, hc τ⟩
      invFun := fun φ => ⟨(φ : L →+* ℂ), hc' φ⟩
      left_inv := fun τ => by ext; rfl
      right_inv := fun φ => by ext; rfl }

open Classical in
/-- `∑_{τ : L → ℂ} f(τ|_K) = [L:K] · ∑_{σ : K → ℂ} f(σ)`. -/
theorem sum_embeddings_comp (f : (K →+* ℂ) → ℝ) :
    ∑ τ : L →+* ℂ, f (τ.comp (algebraMap K L)) =
      Module.finrank K L * ∑ σ : K →+* ℂ, f σ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : L →+* ℂ => τ.comp (algebraMap K L))
    (fun τ => f (τ.comp (algebraMap K L))), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_congr rfl (fun τ hτ => by rw [(Finset.mem_filter.mp hτ).2]),
    Finset.sum_const, card_embeddings_over, nsmul_eq_mul]

end BaseChange

/-! ## 10. AT1 for every Weierstrass model: translation invariance

`ω ↦ dz` forces `g₂ = c₄/12`, `g₃ = c₆/216` but `P_W = 4x³ + b₂x² + 2b₄x + b₆` equals
`4x³ − g₂x − g₃` only after the translation `x ↦ x − b₂/12`. The archimedean term is translation
invariant (Lebesgue measure on `ℂ`), so AT1 holds with a translation at each `σ`. -/

section Translate

open Polynomial
open scoped nonZeroDivisors

theorem hypGram_comp_add (P : ℂ[X]) (c : ℂ) :
    hypGram (P.comp (X + C c)) 0 0 = hypGram P 0 0 := by
  simp only [hypGram, pow_zero, one_mul, eval_comp, eval_add, eval_X, eval_C]
  congr 1
  exact integral_add_right_eq_self (fun x => 1 / ((‖P.eval x‖ : ℝ) : ℂ)) c

theorem hypVol_one_comp_add (P : ℂ[X]) (c : ℂ) : hypVol 1 (P.comp (X + C c)) = hypVol 1 P := by
  simp only [hypVol, Matrix.det_fin_one, Matrix.of_apply, Fin.val_zero, hypGram_comp_add]

variable {K : Type*} [Field K] [NumberField K]

/-- **Acceptance test AT1, conditional form, any Weierstrass model with semistable reduction.**
As `modelHeight_ofIdeal_eq_faltingsHeightEC`, with the Weierstrass polynomial of `W^σ` equal to
`4x³ − g₂(L σ)x − g₃(L σ)` after a translation `x ↦ x + c σ`. -/
theorem modelHeight_ofIdeal_eq_faltingsHeightEC' (hA : PeriodAreaFormula)
    (W : WeierstrassCurve K) [W.IsElliptic] (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (L : (K →+* ℂ) → PeriodPair) (c : (K →+* ℂ) → ℂ)
    (hP : ∀ σ, (4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ =
      (4 * X ^ 3 - C (L σ).g₂ * X - C (L σ).g₃).comp (X + C (c σ)))
    (hNeron : -12 * Real.log (FractionalIdeal.absNorm 𝔞 : ℝ) =
      finiteHeightPart W.j - ∑ σ : K →+* ℂ, Real.log ‖σ W.Δ‖) :
    (HodgeData.ofIdeal 𝔞 h𝔞 L).modelHeight = faltingsHeightEC W := by
  rw [HodgeData.modelHeight_ofIdeal, faltingsHeightEC, ← hNeron]
  have hterm : ∀ σ : K →+* ℂ, ZLattice.covolume (L σ).lattice =
      hypVol 1 ((4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆ : K[X]).map σ) := by
    intro σ; rw [hP, hypVol_one_comp_add, hA]
  simp only [hterm]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  field_simp

end Translate

/-! ## 11. Base change of fractional-ideal Hermitian lines (node AR3, finite half)

`N_L(I𝓞_L) = N_K(I)^{[L:K]}` for fractional ideals (from Mathlib's `Ideal.absNorm_algebraMap` for
integral ideals), hence `deg_L((I, ρ)_{𝓞_L}) = [L:K] · deg_K(I, ρ)`: the Arakelov degree divided
by the absolute degree, i.e. the height, is invariant under base change. -/

section BaseChangeNorm

open scoped nonZeroDivisors

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem finrank_ringOfIntegers : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L :=
  (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm

theorem absNorm_map_ringOfIntegers (I : Ideal (𝓞 K)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 K) (𝓞 L))) = Ideal.absNorm I ^ Module.finrank K L := by
  rw [Ideal.absNorm_algebraMap, finrank_ringOfIntegers]

theorem norm_algebraMap_tower (x : K) :
    Algebra.norm ℚ (algebraMap K L x) = Algebra.norm ℚ x ^ Module.finrank K L := by
  rw [← Algebra.norm_norm (S := K), Algebra.norm_algebraMap, map_pow]

/-- **Norm of an extended fractional ideal.** -/
theorem absNorm_extendedHom (I : FractionalIdeal (𝓞 K)⁰ K) :
    FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L) I) =
      FractionalIdeal.absNorm I ^ Module.finrank K L := by
  have hnum := FractionalIdeal.den_mul_self_eq_num' (𝓞 K)⁰ K I
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.2
  have hK := congr_arg FractionalIdeal.absNorm hnum
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm] at hK
  have hL := congr_arg (fun J => FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L) J))
    hnum
  simp only [map_mul, FractionalIdeal.extendedHom_spanSingleton,
    FractionalIdeal.extendedHom_coeIdeal_eq_map, FractionalIdeal.absNorm_span_singleton,
    FractionalIdeal.coeIdeal_absNorm, absNorm_map_ringOfIntegers] at hL
  have hmap : IsFractionRing.map (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))
      (algebraMap (𝓞 K) K d) = algebraMap K L (algebraMap (𝓞 K) K d) := by
    simp only [IsFractionRing.map]
    rw [IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
      ← IsScalarTower.algebraMap_apply (𝓞 K) K L]
  rw [hmap, norm_algebraMap_tower, Nat.cast_pow, ← hK, abs_pow, mul_pow] at hL
  have hN0 : |Algebra.norm ℚ (algebraMap (𝓞 K) K d)| ^ Module.finrank K L ≠ 0 :=
    pow_ne_zero _ (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hd0))
  exact mul_left_cancel₀ hN0 hL

/-- **Base change of the Arakelov degree** for Hermitian lines given by fractional ideals:
`deg_L(I𝓞_L, ρ∘res) = [L:K] · deg_K(I, ρ)`. -/
theorem arakelovDegree_ofFractionalIdeal_baseChange (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (ρ : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) :
    (HermitianLattice.ofFractionalIdeal (FractionalIdeal.extendedHom L (𝓞 L) I)
      ((FractionalIdeal.extendedHom_eq_zero_iff L (𝓞 L)).not.mpr hI)
      (fun τ => ρ (τ.comp (algebraMap K L))) (fun _ => hρ _)).arakelovDegree =
      Module.finrank K L * (HermitianLattice.ofFractionalIdeal I hI ρ hρ).arakelovDegree := by
  rw [HermitianLattice.arakelovDegree_ofFractionalIdeal,
    HermitianLattice.arakelovDegree_ofFractionalIdeal, absNorm_extendedHom,
    sum_embeddings_comp (fun σ => Real.log (ρ σ))]
  push_cast
  rw [Real.log_pow]
  ring

end BaseChangeNorm

/-! ## 12. Base-change invariance of the model height (node H4, dimension-1 Hodge data) -/

section BaseChangeHeight

open scoped nonZeroDivisors

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The model height does not change under base change** (Hodge data of the form
`HodgeData.ofIdeal`): extending the lattice to `𝓞_L` and restricting the period lattices,
`h_L = h_K`. This is the Arakelov-theoretic content of "the Faltings height of a model with good
(or semistable) base change is invariant", node H4. -/
theorem HodgeData.modelHeight_ofIdeal_baseChange (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h𝔞 : 𝔞 ≠ 0)
    (P : (K →+* ℂ) → PeriodPair) :
    (HodgeData.ofIdeal (FractionalIdeal.extendedHom L (𝓞 L) 𝔞)
      ((FractionalIdeal.extendedHom_eq_zero_iff L (𝓞 L)).not.mpr h𝔞)
      (fun τ => P (τ.comp (algebraMap K L)))).modelHeight =
      (HodgeData.ofIdeal 𝔞 h𝔞 P).modelHeight := by
  rw [HodgeData.modelHeight_ofIdeal, HodgeData.modelHeight_ofIdeal, absNorm_extendedHom,
    sum_embeddings_comp (L := L) (fun σ => Real.log (ZLattice.covolume (P σ).lattice volume)),
    ← Module.finrank_mul_finrank ℚ K L]
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hL : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  push_cast
  rw [Real.log_pow]
  field_simp

end BaseChangeHeight

/-! ## 13. A numerical normalization check: `covol(ℤ + ℤi) = 1`, so `exampleHodge` has height 0 -/

section Gaussian

theorem covolume_gaussianPair : ZLattice.covolume gaussianPair.lattice = 1 := by
  have hspan : gaussianPair.lattice = Submodule.span ℤ (Set.range Complex.basisOneI) := by
    rw [Complex.coe_basisOneI, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.singleton_union]
    rfl
  have hF : IsAddFundamentalDomain gaussianPair.lattice
      (ZSpan.fundamentalDomain Complex.basisOneI) volume := by
    rw [hspan]; exact ZSpan.isAddFundamentalDomain _ volume
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume hF]
  have himg : Complex.measurableEquivPi ⁻¹'
      ZSpan.fundamentalDomain (Complex.basisOneI.map Complex.basisOneI.equivFun) =
      ZSpan.fundamentalDomain Complex.basisOneI := by
    rw [← ZSpan.map_fundamentalDomain]
    ext z
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨w, hw, hwz⟩
      have : w = z := Complex.basisOneI.equivFun.injective (by
        rw [hwz]; rfl)
      exact this ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  rw [Measure.real, ← himg, Complex.volume_preserving_equiv_pi.measure_preimage
    (ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet, ZSpan.volume_fundamentalDomain]
  have : Matrix.of (Complex.basisOneI.map Complex.basisOneI.equivFun) = 1 := by
    ext i j
    simp [Matrix.one_apply]
    fin_cases i <;> fin_cases j <;> simp
  rw [this, Matrix.det_one, abs_one, ENNReal.ofReal_one, ENNReal.toReal_one]

theorem exampleHodge_modelHeight_eq_zero : exampleHodge.modelHeight = 0 := by
  rw [exampleHodge_modelHeight, covolume_gaussianPair, Real.log_one, mul_zero]

end Gaussian

/-! ## 14. Tensor products of fractional-ideal Hermitian lines (node AR3)

For invertible `𝓞_K`-modules inside `K`, `I ⊗ J ≅ IJ`, and the tensor-product metric is the
product metric; the degree is additive. -/

section Tensor

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

theorem arakelovDegree_ofFractionalIdeal_mul (I J : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (hJ : J ≠ 0) (ρ ρ' : (K →+* ℂ) → ℝ) (hρ : ∀ σ, 0 < ρ σ) (hρ' : ∀ σ, 0 < ρ' σ) :
    (HermitianLattice.ofFractionalIdeal (I * J) (mul_ne_zero hI hJ) (fun σ => ρ σ * ρ' σ)
      (fun σ => mul_pos (hρ σ) (hρ' σ))).arakelovDegree =
      (HermitianLattice.ofFractionalIdeal I hI ρ hρ).arakelovDegree +
        (HermitianLattice.ofFractionalIdeal J hJ ρ' hρ').arakelovDegree := by
  simp only [HermitianLattice.arakelovDegree_ofFractionalIdeal, map_mul, Rat.cast_mul]
  have hI0 : (FractionalIdeal.absNorm I : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hI)
  have hJ0 : (FractionalIdeal.absNorm J : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hJ)
  rw [Real.log_mul hI0 hJ0, Finset.sum_congr rfl fun σ _ =>
    Real.log_mul (hρ σ).ne' (hρ' σ).ne', Finset.sum_add_distrib]
  ring

end Tensor


end ZInQ.DefFaltings
