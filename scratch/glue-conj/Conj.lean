import Mathlib

/-!
# glue-conj: proof of `LeafConj` (places of `ℚ̄` over `p` are `G_ℚ`-conjugate)

Self-contained (scratch files cannot import each other). `GQ`, `Qbar`, `LiesOver`, `inertiaGQ`
and `LeafConj` are copied verbatim from `scratch/glue-b3-unram/Unram.lean`.

Proof. `B` = algebraic integers in `ℚ̄`. To a place `w` over `p` attach its center
`𝔓_w = {b ∈ B | v_w(b) < 1}`, a prime of `B` over `pℤ`. Mathlib's profinite transitivity
(`Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`, G_ℚ acting on the discrete `B`)
gives `g` with `𝔓_{w'} = g • 𝔓_w = 𝔓_{g•w}`. The center lemma `le_of_center` (via the
DVR `𝓞_K` localized at a prime, `HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq`, in
`K = ℚ(x)`) gives `w' = g • w`, and `inertia_conj` gives `g⁻¹ I_{w'} g ≤ I_w`.
-/

open NumberField
open scoped Pointwise

namespace GlueConj

/-- `G_ℚ`. -/
abbrev GQ := Field.absoluteGaloisGroup ℚ

/-- `ℚ̄`. -/
abbrev Qbar := AlgebraicClosure ℚ

/-- `G_ℚ` as the type of `ℚ`-automorphisms of `ℚ̄` (definitionally `GQ`). -/
abbrev Gal := Qbar ≃ₐ[ℚ] Qbar

instance : IsGalois ℚ (AlgebraicClosure ℚ) := {}

/-- The valuation subring `w` of `ℚ̄` lies over the prime `p`: `v_w(p) < 1`. -/
def LiesOver (w : ValuationSubring Qbar) (p : ℕ) : Prop := w.valuation (p : Qbar) < 1

/-- The inertia subgroup `I_w ≤ G_ℚ`: the image of Mathlib's `ValuationSubring.inertiaSubgroup`
(elements of the decomposition group of `w` acting trivially on its residue field). -/
noncomputable def inertiaGQ (w : ValuationSubring Qbar) : Subgroup GQ :=
  (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype

/-- **Leaf (conjugacy of places)**, verbatim from glue-b3-unram. -/
def LeafConj : Prop :=
  ∀ p : ℕ, p.Prime → ∀ w w' : ValuationSubring Qbar, LiesOver w p → LiesOver w' p →
    ∃ σ : GQ, ∀ s ∈ inertiaGQ w', σ⁻¹ * s * σ ∈ inertiaGQ w

/-! ## 1. The center lemma -/

/-- Integral elements over `ℤ` lie in every valuation subring. -/
theorem mem_of_isIntegral (w : ValuationSubring Qbar) {y : Qbar} (hy : IsIntegral ℤ y) : y ∈ w := by
  have h1 : IsIntegral w y := IsIntegral.tower_top (A := w) hy
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  rw [← ha]; exact a.2

theorem val_le_one_of_isIntegral (w : ValuationSubring Qbar) {y : Qbar} (hy : IsIntegral ℤ y) :
    w.valuation y ≤ 1 := (w.valuation_le_one_iff y).mpr (mem_of_isIntegral w hy)

/-- **Center lemma.** Two valuation subrings of `ℚ̄` over a prime `p` with the same center on the
algebraic integers are comparable (hence equal, by symmetry). -/
theorem le_of_center (w₁ w₂ : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime)
    (hw₁ : w₁.valuation (p : Qbar) < 1)
    (hc : ∀ y : Qbar, IsIntegral ℤ y → (w₁.valuation y < 1 ↔ w₂.valuation y < 1)) :
    w₁ ≤ w₂ := by
  intro x hx
  let K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {x}
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ) x)
  have : NumberField K := ⟨⟩
  let ι : 𝓞 K →+* Qbar := (algebraMap K Qbar).comp (algebraMap (𝓞 K) K)
  have hint : ∀ r : 𝓞 K, IsIntegral ℤ (ι r) := fun r =>
    (RingOfIntegers.isIntegral_coe r).map (IsScalarTower.toAlgHom ℤ K Qbar)
  let f : 𝓞 K →+* w₁ :=
    { toFun := fun r => ⟨ι r, mem_of_isIntegral w₁ (hint r)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  let I : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal w₁).comap f
  have hI : ∀ r, r ∈ I ↔ w₁.valuation (ι r) < 1 := fun r =>
    (w₁.valuation_lt_one_iff (f r))
  have hpI : (p : 𝓞 K) ∈ I := by rw [hI]; simpa [ι] using hw₁
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨I, Ideal.comap_isPrime _ _, fun h => hp0 (by rw [h] at hpI; simpa using hpI)⟩
  let x' : K := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := K) x'
  have hd : ¬ w₁.valuation (ι d) < 1 := fun h' => d.2 ((hI d).mpr h')
  have hd2 : w₂.valuation (ι d) = 1 :=
    le_antisymm (val_le_one_of_isIntegral w₂ (hint d))
      (not_lt.mp fun h' => hd ((hc _ (hint d)).mpr h'))
  have hn2 := val_le_one_of_isIntegral w₂ (hint n)
  rw [← w₂.valuation_le_one_iff]
  rcases h with h | h
  · have h' : x * ι d = ι n := by
      have := congrArg (algebraMap K Qbar) h
      simpa [ι] using this
    have := congrArg w₂.valuation h'
    rw [map_mul, hd2, mul_one] at this
    rw [this]; exact hn2
  · have h' : x * ι n = ι d := by
      have := congrArg (algebraMap K Qbar) h
      simpa [ι] using this
    by_contra hx2
    push Not at hx2
    have e2 := congrArg w₂.valuation h'
    rw [map_mul, hd2] at e2
    have hn2' : w₂.valuation (ι n) < 1 := by
      rcases lt_or_eq_of_le hn2 with h3 | h3
      · exact h3
      · rw [h3, mul_one] at e2; exact absurd e2 (ne_of_gt hx2)
    have hn1 := (hc _ (hint n)).mpr hn2'
    have e1 := congrArg w₁.valuation h'
    rw [map_mul] at e1
    have hx1 : w₁.valuation x ≤ 1 := (w₁.valuation_le_one_iff x).mpr hx
    have : w₁.valuation x * w₁.valuation (ι n) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hx1) hn1
    rw [e1] at this
    exact hd (by simpa using this)

/-! ## 2. Profinite transitivity on primes of the algebraic integers -/

/-- The algebraic integers `B ⊆ ℚ̄`. -/
noncomputable abbrev B := integralClosure ℤ Qbar

theorem isIntegral_smul (σ : Gal) (b : B) : IsIntegral ℤ (σ (b : Qbar)) :=
  (mem_integralClosure_iff ℤ Qbar).mp b.2 |>.map ((σ : Qbar →+* Qbar).toIntAlgHom)

noncomputable instance : MulSemiringAction Gal B where
  smul σ b := ⟨σ b, isIntegral_smul σ b⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl
  smul_zero σ := Subtype.ext (map_zero σ)
  smul_add σ _ _ := Subtype.ext (map_add σ _ _)
  smul_one σ := Subtype.ext (map_one σ)
  smul_mul σ _ _ := Subtype.ext (map_mul σ _ _)

@[simp] theorem coe_smul (σ : Gal) (b : B) : ((σ • b : B) : Qbar) = σ (b : Qbar) := rfl

instance : SMulCommClass Gal ℤ B := inferInstance

instance : Algebra.IsInvariant ℤ B Gal := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ σ : Gal, σ (b : Qbar) = b := fun σ => congrArg Subtype.val (hb σ)
  have hbot : (b : Qbar) ∈ (⊥ : IntermediateField ℚ Qbar) :=
    (InfiniteGalois.mem_bot_iff_fixed (b : Qbar)).mpr hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
  have hint : IsIntegral ℤ (algebraMap ℚ Qbar q) := by
    rw [hq]; exact (mem_integralClosure_iff ℤ Qbar).mp b.2
  rw [isIntegral_algebraMap_iff] at hint
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨n, Subtype.ext ?_⟩
  rw [← hq]; simp

noncomputable instance : TopologicalSpace B := ⊥
instance : DiscreteTopology B := ⟨rfl⟩

instance : ContinuousSMul Gal B := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro b
  convert stabilizer_isOpen_of_isIntegral (K := ℚ) (L := Qbar) (b : Qbar) using 2
  ext σ
  simp only [MulAction.mem_stabilizer_iff]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

/-- Transitivity on primes of `B` over the same prime of `ℤ` (Mathlib, profinite case). -/
theorem exists_smul_eq (P Q : Ideal B) [P.IsPrime] [Q.IsPrime] (h : P.under ℤ = Q.under ℤ) :
    ∃ g : Gal, Q = g • P :=
  Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := ℤ) (G := Gal) P Q h

/-! ## 3. Transport and inertia conjugation -/

theorem val_lt_one_iff (w : ValuationSubring Qbar) (t : Qbar) :
    w.valuation t < 1 ↔ t ∈ w ∧ (t = 0 ∨ t⁻¹ ∉ w) := by
  rw [← w.valuation_le_one_iff, ← w.valuation_le_one_iff]
  by_cases ht : t = 0
  · subst ht; simp
  have hprod : w.valuation t * w.valuation t⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ht, map_one]
  constructor
  · intro h
    refine ⟨h.le, Or.inr fun h' => ?_⟩
    have : w.valuation t * w.valuation t⁻¹ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h') h
    rw [hprod] at this; exact lt_irrefl _ this
  · rintro ⟨h1, h2 | h2⟩
    · exact absurd h2 ht
    · refine lt_of_le_of_ne h1 fun he => h2 ?_
      rw [he, one_mul] at hprod; exact hprod.le

/-- Transport of the maximal ideal under the pointwise action. -/
theorem val_smul_lt_one_iff (w : ValuationSubring Qbar) (g : Gal) (y : Qbar) :
    (g • w).valuation y < 1 ↔ w.valuation (g⁻¹ y) < 1 := by
  rw [val_lt_one_iff, val_lt_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [AlgEquiv.smul_def, map_inv₀, map_eq_zero_iff _ (g⁻¹).injective]

/-- **Glue: conjugate places have conjugate inertia.** If `w' = g • w` then
`g⁻¹ I_{w'} g ≤ I_w` (inertia as in glue-b3-unram, the image of Mathlib's `inertiaSubgroup`). -/
theorem inertia_conj (w w' : ValuationSubring Qbar) (g : Gal) (hw : w' = g • w) (s : Gal)
    (hs : s ∈ (w'.inertiaSubgroup ℚ).map (w'.decompositionSubgroup ℚ).subtype) :
    g⁻¹ * s * g ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hs
  have hdec : g⁻¹ * (t : Gal) * g ∈ w.decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← hw,
      MulAction.mem_stabilizer_iff.mp t.2, hw, inv_smul_smul]
  refine Subgroup.mem_map.mpr ⟨⟨_, hdec⟩, ?_, rfl⟩
  have ht' : ∀ z : w', w'.valuation ((t : Gal) (z : Qbar) - z) < 1 := by
    intro z
    have h1 : MulSemiringAction.toRingAut _ (IsLocalRing.ResidueField w') t = 1 := ht
    have h2 := congrArg (fun f => f (IsLocalRing.residue w' z)) h1
    change t • IsLocalRing.residue w' z = IsLocalRing.residue w' z at h2
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h2
    exact h2
  change _ = (1 : _)
  ext r
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨_, hdec⟩ : w.decompositionSubgroup ℚ) • IsLocalRing.residue w y = IsLocalRing.residue w y
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  have hgy : g (y : Qbar) ∈ w' := by
    rw [hw]; exact ValuationSubring.smul_mem_pointwise_smul_iff.mpr y.2
  let e : w.decompositionSubgroup ℚ := ⟨_, hdec⟩
  show w.valuation ((e • y - y : w) : Qbar) < 1
  have he : ((e • y - y : w) : Qbar) = g⁻¹ ((t : Gal) (g y) - g y) := by
    rw [map_sub]
    show (g⁻¹ * ↑t * g) (y : Qbar) - y = _
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    congr 1
    exact ((g⁻¹ : Gal).apply_symm_apply _).symm.trans (by rfl) |>.symm ▸ rfl
  rw [he]
  generalize hu : (t : Gal) = u at ht' ⊢
  have h3 := ht' ⟨_, hgy⟩
  clear ht'
  subst hw
  rw [val_smul_lt_one_iff] at h3
  exact h3

/-! ## 4. Assembly -/

/-- `B → w`: algebraic integers lie in every valuation subring. -/
noncomputable def toW (w : ValuationSubring Qbar) : B →+* w where
  toFun b := ⟨b, mem_of_isIntegral w ((mem_integralClosure_iff ℤ Qbar).mp b.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The center `𝔓_w = {b ∈ B | v_w(b) < 1}` of `w` on the algebraic integers. -/
noncomputable def centerIdeal (w : ValuationSubring Qbar) : Ideal B :=
  (IsLocalRing.maximalIdeal w).comap (toW w)

instance (w : ValuationSubring Qbar) : (centerIdeal w).IsPrime := Ideal.comap_isPrime _ _

theorem mem_centerIdeal (w : ValuationSubring Qbar) (b : B) :
    b ∈ centerIdeal w ↔ w.valuation (b : Qbar) < 1 :=
  w.valuation_lt_one_iff (toW w b)

theorem centerIdeal_under (w : ValuationSubring Qbar) (p : ℕ) (hp : p.Prime) (hw : LiesOver w p) :
    (centerIdeal w).under ℤ = Ideal.span {(p : ℤ)} := by
  have : Fact p.Prime := ⟨hp⟩
  have hmem : (p : ℤ) ∈ (centerIdeal w).under ℤ := by
    rw [Ideal.under, Ideal.mem_comap, mem_centerIdeal]
    simpa [LiesOver] using hw
  have hle : Ideal.span {(p : ℤ)} ≤ (centerIdeal w).under ℤ :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  exact ((Int.ideal_span_isMaximal_of_prime p).eq_of_le
    (Ideal.comap_isPrime (algebraMap ℤ B) (centerIdeal w)).ne_top hle).symm

theorem centerIdeal_smul (w : ValuationSubring Qbar) (g : Gal) :
    centerIdeal (g • w) = g • centerIdeal w := by
  ext b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_centerIdeal, mem_centerIdeal,
    val_smul_lt_one_iff]
  rfl

/-- **`LeafConj` is glue**: proved from Mathlib. -/
theorem leafConj : LeafConj := by
  intro p hp w w' hw hw'
  obtain ⟨g, hg⟩ := exists_smul_eq (centerIdeal w) (centerIdeal w')
    (by rw [centerIdeal_under w p hp hw, centerIdeal_under w' p hp hw'])
  rw [← centerIdeal_smul] at hg
  have hc : ∀ y : Qbar, IsIntegral ℤ y → (w'.valuation y < 1 ↔ (g • w).valuation y < 1) := by
    intro y hy
    have h := congrArg (fun I : Ideal B => (⟨y, (mem_integralClosure_iff ℤ Qbar).mpr hy⟩ : B) ∈ I) hg
    simp only [mem_centerIdeal] at h
    exact h.to_iff
  have hpint : IsIntegral ℤ (p : Qbar) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := (p : ℤ))
  have h1 := le_of_center w' (g • w) p hp hw' hc
  have h2 := le_of_center (g • w) w' p hp ((hc _ hpint).mp hw') (fun y hy => (hc y hy).symm)
  have heq : w' = g • w := le_antisymm h1 h2
  exact ⟨g, fun s hs => inertia_conj w w' g heq s hs⟩

end GlueConj

#print axioms GlueConj.leafConj
