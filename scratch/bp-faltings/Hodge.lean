import Mathlib

/-!
# bp-faltings: the first concrete layer of the stable Faltings height

Draft for `docs/research/bp-faltings.md`. Mathlib-only (no project imports).

The layer that does not depend on Néron models:

* `HermitianLattice K V`: a Hermitian line bundle on `Spec 𝓞_K` in generic-fibre form, i.e. a
  rank-one `𝓞_K`-lattice `M` in a one-dimensional `K`-vector space `V`, with a norm on
  `V ⊗_{K,σ} ℂ` for every complex embedding `σ`.
* `HermitianLattice.degreeAt`: the Arakelov degree computed with a nonzero section,
  `log #(M / 𝓞_K s) − ∑_σ log ‖s‖_σ`, and `arakelovDegree`; theorem `degreeAt_eq_arakelovDegree`:
  it does not depend on the section (product formula).
* `torusMetricSq Λ c`: the archimedean Faltings metric on the top form `c · dz₁ ∧ ⋯ ∧ dz_g` of the
  complex torus `ℂ^g / Λ`, `(i/2)^g ∫_{ℂ^g/Λ} η ∧ η̄` (sign convention: the positive value),
  computed as an integral over any fundamental domain (`torusMetricSq_eq_setIntegral`), and its
  independence of the linear coordinates (`torusMetricSq_comap`).
* `HodgeData K g V`: an abelian variety over `K` "given with a model": the determinant of the
  invariant differentials of a model as a lattice in `det H⁰(A, Ω¹)`, and for every `σ` the period
  lattice of `A_σ(ℂ)` in linear coordinates. `HodgeData.modelHeight` is Faltings' model height;
  proved: section independence, coordinate independence, monotonicity in the lattice (which is
  why the infimum over models is the Néron-model value).
-/

namespace ZInQ.BPFaltings

open NumberField MeasureTheory

/-! ## 1. Norms and complex embeddings -/

section Embeddings

variable {K : Type*} [Field K] [NumberField K]

/-- `∑_{σ : K → ℂ} log |σ x| = log |N_{K/ℚ}(x)|` (the archimedean half of the product formula). -/
theorem sum_log_norm_embeddings (x : K) (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  rw [← Real.log_prod (fun σ _ => by simpa using hx)]
  congr 1
  have h := congr_arg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)
  simp only [norm_prod] at h
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖) (fun φ => ‖φ x‖)
    (fun _ => by simp [RingHom.equivRatAlgHom_apply]), ← h]
  simp

/-- The same for an algebraic integer, with the integer norm. -/
theorem sum_log_norm_embeddings_int (a : 𝓞 K) (ha : a ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ (a : K)‖ = Real.log ((Algebra.norm ℤ a).natAbs : ℝ) := by
  rw [sum_log_norm_embeddings _ (by simpa using ha), ← Algebra.coe_norm_int]
  simp [Nat.cast_natAbs]

end Embeddings

/-! ## 2. Hermitian line bundles on `Spec 𝓞_K` and the Arakelov degree -/

section Arakelov

variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/-- The index `#(M / 𝓞_K s)` (as a natural number; `0` if infinite). -/
noncomputable def secIndex (M : Submodule (𝓞 K) V) (s : V) : ℕ :=
  (Submodule.span (𝓞 K) {s}).toAddSubgroup.relIndex M.toAddSubgroup

/-- **Change of section.** For `a ∈ 𝓞_K` and `0 ≠ s ∈ M`:
`#(M / 𝓞_K·as) = |N(a)| · #(M / 𝓞_K·s)`. -/
theorem secIndex_smul (M : Submodule (𝓞 K) V) {s : V} (hsM : s ∈ M) (hs : s ≠ 0) (a : 𝓞 K) :
    secIndex M (a • s) = (Algebra.norm ℤ a).natAbs * secIndex M s := by
  classical
  let φ : 𝓞 K →ₗ[𝓞 K] V := LinearMap.toSpanSingleton (𝓞 K) V s
  have hφ : Function.Injective φ := by
    intro x y hxy
    simp only [φ, LinearMap.toSpanSingleton_apply] at hxy
    have h1 : algebraMap (𝓞 K) K (x - y) • s = 0 := by
      rw [algebraMap_smul, sub_smul, hxy, sub_self]
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp (IsFractionRing.injective (𝓞 K) K (by simpa using h))
    · exact absurd h hs
  have h1 : Submodule.span (𝓞 K) {a • s} = Submodule.map φ (Ideal.span {a}) := by
    rw [Submodule.map_span, Set.image_singleton]
    simp [φ]
  have h2 : Submodule.span (𝓞 K) {s} = Submodule.map φ (⊤ : Ideal (𝓞 K)) := by
    rw [Submodule.map_top, LinearMap.span_singleton_eq_range]
  have hle1 : Submodule.span (𝓞 K) {a • s} ≤ Submodule.span (𝓞 K) {s} :=
    Submodule.span_le.mpr (by
      simpa using Submodule.smul_mem _ a (Submodule.mem_span_singleton_self s))
  have hle2 : Submodule.span (𝓞 K) {s} ≤ M := Submodule.span_le.mpr (by simpa using hsM)
  unfold secIndex
  rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hle1)
    (Submodule.toAddSubgroup_mono hle2)]
  congr 1
  rw [h1, h2, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ hφ, Submodule.top_toAddSubgroup,
    AddSubgroup.relIndex_top_right, ← Ideal.absNorm_span_singleton, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl

/-- **A Hermitian line bundle on `Spec 𝓞_K`**, in generic-fibre form. `V` is a one-dimensional
`K`-vector space (the generic fibre), `lattice` is the `𝓞_K`-module of global sections (an
invertible `𝓞_K`-module, i.e. a rank-one lattice in `V`), and `norm σ` is a norm on the complex
line `V ⊗_{K,σ} ℂ`, recorded through its values on `V`. Conjugation symmetry
(`‖v‖_σ̄ = ‖v‖_σ`) is not needed for the degree and is not imposed. -/
structure HermitianLattice (K : Type*) [Field K] [NumberField K] (V : Type*) [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] where
  /-- The `𝓞_K`-module of sections. -/
  lattice : Submodule (𝓞 K) V
  /-- `V` is a line. -/
  finrank_eq_one : Module.finrank K V = 1
  /-- `lattice` is a full lattice: some nonzero section generates a subgroup of finite index
  (then every nonzero section does, `secIndex_ne_zero`). -/
  isLattice : ∃ s ∈ lattice, s ≠ 0 ∧ secIndex lattice s ≠ 0
  /-- The norm on `V ⊗_{K,σ} ℂ`. -/
  norm : (K →+* ℂ) → V → ℝ
  norm_smul : ∀ σ (a : K) (v : V), norm σ (a • v) = ‖σ a‖ * norm σ v
  norm_pos : ∀ σ (v : V), v ≠ 0 → 0 < norm σ v

namespace HermitianLattice

variable (L : HermitianLattice K V)

/-- The Arakelov degree computed with the section `s`:
`log #(M / 𝓞_K s) − ∑_{σ : K → ℂ} log ‖s‖_σ`. -/
noncomputable def degreeAt (s : V) : ℝ :=
  Real.log (secIndex L.lattice s) - ∑ σ : K →+* ℂ, Real.log (L.norm σ s)

theorem degreeAt_smul {s : V} (hsM : s ∈ L.lattice) (hs : s ≠ 0)
    (hi : secIndex L.lattice s ≠ 0) {a : 𝓞 K} (ha : a ≠ 0) :
    L.degreeAt (a • s) = L.degreeAt s := by
  have hN : (Algebra.norm ℤ a).natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using (Algebra.norm_ne_zero_iff (R := ℤ)).mpr ha
  have has : a • s = (a : K) • s := (algebraMap_smul K a s).symm
  have hσ : ∀ σ : K →+* ℂ, Real.log (L.norm σ ((a : K) • s)) =
      Real.log ‖σ (a : K)‖ + Real.log (L.norm σ s) := by
    intro σ
    rw [L.norm_smul, Real.log_mul]
    · simpa using ha
    · exact (L.norm_pos σ s hs).ne'
  unfold degreeAt
  rw [secIndex_smul _ hsM hs, has, Finset.sum_congr rfl (fun σ _ => hσ σ), Finset.sum_add_distrib,
    sum_log_norm_embeddings_int a ha]
  push_cast
  rw [Real.log_mul (by exact_mod_cast hN) (by exact_mod_cast hi)]
  ring

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem _root_.ZInQ.BPFaltings.exists_smul_eq (hV : Module.finrank K V = 1)
    {s t : V} (hs : s ≠ 0) :
    ∃ b d : 𝓞 K, d ≠ 0 ∧ (d : K) • t = (b : K) • s := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' s hs).mp hV t
  obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
  refine ⟨b, d, nonZeroDivisors.ne_zero hd, ?_⟩
  have hd' : (algebraMap (𝓞 K) K d) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  rw [← hc, smul_smul, mul_div_cancel₀ _ hd']

/-- Every nonzero section has finite index. -/
theorem secIndex_ne_zero {t : V} (htM : t ∈ L.lattice) (ht : t ≠ 0) :
    secIndex L.lattice t ≠ 0 := by
  obtain ⟨s, hsM, hs, hi⟩ := L.isLattice
  obtain ⟨b, d, hd, h⟩ := exists_smul_eq L.finrank_eq_one (t := t) hs
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_smul, smul_eq_zero] at h
    rcases h with h | h
    · exact hd (by exact_mod_cast h)
    · exact ht h
  have e1 := secIndex_smul L.lattice htM ht d
  have e2 := secIndex_smul L.lattice hsM hs b
  have h' : d • t = b • s := by
    rw [← algebraMap_smul K d t, ← algebraMap_smul K b s]; exact h
  have : (Algebra.norm ℤ d).natAbs * secIndex L.lattice t =
      (Algebra.norm ℤ b).natAbs * secIndex L.lattice s := by
    rw [← e1, ← e2, h']
  intro h0
  rw [h0, mul_zero] at this
  have hN : (Algebra.norm ℤ b).natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using (Algebra.norm_ne_zero_iff (R := ℤ)).mpr hb
  exact hi (by simpa [hN] using this.symm)

/-- **Independence of the section.** -/
theorem degreeAt_eq {s t : V} (hsM : s ∈ L.lattice) (hs : s ≠ 0) (htM : t ∈ L.lattice)
    (ht : t ≠ 0) : L.degreeAt s = L.degreeAt t := by
  obtain ⟨b, d, hd, h⟩ := exists_smul_eq L.finrank_eq_one (t := t) hs
  have hb : b ≠ 0 := by
    rintro rfl
    simp only [map_zero, zero_smul, smul_eq_zero] at h
    rcases h with h | h
    · exact hd (by exact_mod_cast h)
    · exact ht h
  have e1 := L.degreeAt_smul htM ht (L.secIndex_ne_zero htM ht) hd
  have e2 := L.degreeAt_smul hsM hs (L.secIndex_ne_zero hsM hs) hb
  have h' : d • t = b • s := by
    rw [← algebraMap_smul K d t, ← algebraMap_smul K b s]; exact h
  rw [← e1, ← e2, h']

/-- **The Arakelov degree** `deg(M̄) = log #(M / 𝓞_K s) − ∑_σ log ‖s‖_σ` for any `0 ≠ s ∈ M`. -/
noncomputable def arakelovDegree : ℝ := L.degreeAt L.isLattice.choose

theorem degreeAt_eq_arakelovDegree {s : V} (hsM : s ∈ L.lattice) (hs : s ≠ 0) :
    L.degreeAt s = L.arakelovDegree :=
  L.degreeAt_eq hsM hs L.isLattice.choose_spec.1 L.isLattice.choose_spec.2.1

end HermitianLattice

end Arakelov

end ZInQ.BPFaltings
