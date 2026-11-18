import ZInQKernel.Contrib.CloudB3RC53.RankCounts.Kummer.Statements

/-!
# `kummer`: Kummer theory for `n = 2` and the characters of `G_{K,S}`

Manuscript `diophantine_zq.tex`, tex 4482–4492 ("Kummer theory gives the exact sequence …").
Over a field `K` of characteristic zero, with `K̄ = AlgebraicClosure K`:

* `kchar`, `kummerHom`: the Kummer character `σ ↦ σ(√a)/√a ∈ {±1} ≅ 𝔽₂` of `a ∈ K^×`, a continuous
  homomorphism `Gal(K̄/K) → 𝔽₂`;
* `kummerHom_eq_one_iff`, `kummerHom_surjective`, `kummerQuot`: Kummer theory,
  `K^×/K^{×2} ≃ Hom_cont(Gal(K̄/K), 𝔽₂)` (surjectivity in the elementary form of Hilbert 90 for
  `n = 2`);
* `kummerChar_trivial_iff`: the Kummer character of `a` is trivial on `Gal(K̄/E)` iff `√a ∈ E`;
* `pullS_bijective`: characters of `G_{K,S} = Gal(K_S/K)` are the characters of `Gal(K̄/K)` trivial
  on `Gal(K̄/K_S)`;
* `card_hom_eq_card_selmer`: hence `|Hom_cont(G_{K,S}, 𝔽₂)| = |K(S,2)|`, from `SqrtMemOfSelmer` and
  `SelmerOfSqrtMem`.

Kinds: PROVED.
-/

noncomputable section
open NumberField IsDedekindDomain
namespace ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS
variable {K : Type} [Field K] [CharZero K]


omit [CharZero K] in
theorem smul_sq_root {x : (AlgebraicClosure K)} (hx : ∃ a : K, x ^ 2 = algebraMap K (AlgebraicClosure K) a) (σ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :
    σ x = x ∨ σ x = -x := by
  obtain ⟨a, ha⟩ := hx
  have h : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, ha, AlgEquiv.commutes]
  have : (σ x - x) * (σ x + x) = 0 := by ring_nf; rw [h]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · left; exact sub_eq_zero.mp h1
  · right; exact eq_neg_of_add_eq_zero_left h1

theorem neg_ne_self {x : (AlgebraicClosure K)} (hx : x ≠ 0) : -x ≠ x := by
  intro h
  have : (2 : (AlgebraicClosure K)) * x = 0 := by rw [two_mul]; nth_rewrite 1 [← h]; ring
  rcases mul_eq_zero.mp this with h2 | h2
  · exact two_ne_zero h2
  · exact hx h2

open Classical in
/-- The Kummer character `σ ↦ σ(x)/x ∈ {±1}`, with values in `𝔽₂` written multiplicatively. -/
def kcharFun (x : (AlgebraicClosure K)) (σ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) : Multiplicative (ZMod 2) :=
  if σ x = x then 1 else Multiplicative.ofAdd 1

theorem kcharFun_mul {x : (AlgebraicClosure K)} (hx0 : x ≠ 0) (hx : ∃ a : K, x ^ 2 = algebraMap K (AlgebraicClosure K) a) (σ τ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :
    kcharFun x (σ * τ) = kcharFun x σ * kcharFun x τ := by
  have hneg := neg_ne_self hx0
  rcases smul_sq_root hx τ with hτ | hτ <;> rcases smul_sq_root hx σ with hσ | hσ <;>
    simp only [kcharFun, AlgEquiv.mul_apply, hτ, hσ, map_neg, neg_neg, hneg,
      mul_one, one_mul, ↓reduceIte]
  all_goals decide

/-- The Kummer character as a continuous homomorphism. -/
def kchar (x : (AlgebraicClosure K)) (hx0 : x ≠ 0) (hx : ∃ a : K, x ^ 2 = algebraMap K (AlgebraicClosure K) a) :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* Multiplicative (ZMod 2) where
  toFun := kcharFun x
  map_one' := by simp [kcharFun]
  map_mul' := kcharFun_mul hx0 hx
  continuous_toFun := by
    let f : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* Multiplicative (ZMod 2) := ⟨⟨kcharFun x, by simp [kcharFun]⟩, kcharFun_mul hx0 hx⟩
    change Continuous f
    apply continuous_of_continuousAt_one
    have hfd : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    have hU : IsOpen (((IntermediateField.adjoin K {x})).fixingSubgroup : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) := IntermediateField.fixingSubgroup_isOpen _
    rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod 2)), Filter.tendsto_pure]
    filter_upwards [hU.mem_nhds (Subgroup.one_mem _)] with σ hσ
    have : σ x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ x
      (IntermediateField.mem_adjoin_simple_self K x)
    simp [f, kcharFun, this]

theorem kchar_apply (x : (AlgebraicClosure K)) (hx0 : x ≠ 0) (hx : ∃ a : K, x ^ 2 = algebraMap K (AlgebraicClosure K) a) (σ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) :
    kchar x hx0 hx σ = kcharFun x σ := rfl

/-- The Kummer character only depends on the square. -/
theorem kchar_eq_of_sq_eq {x y : (AlgebraicClosure K)} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : ∃ a : K, x ^ 2 = algebraMap K (AlgebraicClosure K) a) (hy : ∃ a : K, y ^ 2 = algebraMap K (AlgebraicClosure K) a)
    (h : y ^ 2 = x ^ 2) : kchar y hy0 hy = kchar x hx0 hx := by
  have : (y - x) * (y + x) = 0 := by ring_nf; rw [h]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · have : y = x := sub_eq_zero.mp h1
    subst this; rfl
  · have hyx : y = -x := eq_neg_of_add_eq_zero_left h1
    ext σ
    simp only [kchar_apply, kcharFun, hyx]
    rw [show σ (-x) = -σ x from map_neg σ x, neg_inj]


theorem kchar_mul_root {x y : (AlgebraicClosure K)} (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (hx : ∃ a : K, x ^ 2 = algebraMap K (AlgebraicClosure K) a) (hy : ∃ a : K, y ^ 2 = algebraMap K (AlgebraicClosure K) a)
    (hxy0 : x * y ≠ 0) (hxy : ∃ a : K, (x * y) ^ 2 = algebraMap K (AlgebraicClosure K) a) :
    kchar (x * y) hxy0 hxy = kchar x hx0 hx * kchar y hy0 hy := by
  ext σ
  have hneg := neg_ne_self hxy0
  have hσ : σ (x * y) = σ x * σ y := map_mul σ x y
  simp only [ContinuousMonoidHom.mul_apply, kchar_apply, kcharFun]
  rw [hσ]
  rcases smul_sq_root hx σ with h1 | h1 <;> rcases smul_sq_root hy σ with h2 | h2 <;>
    rw [h1, h2] <;>
    simp only [neg_mul, mul_neg, neg_neg, hneg, neg_ne_self hx0, neg_ne_self hy0,
      ↓reduceIte, mul_one, one_mul]
  all_goals decide

omit [CharZero K] in
theorem exists_root (a : Kˣ) : ∃ x : (AlgebraicClosure K), x ^ 2 = algebraMap K (AlgebraicClosure K) a :=
  IsAlgClosed.exists_pow_nat_eq _ two_pos

/-- A chosen square root of `a` in `K̄`. -/
def root (a : Kˣ) : (AlgebraicClosure K) := (exists_root a).choose

omit [CharZero K] in
theorem root_sq (a : Kˣ) : root a ^ 2 = algebraMap K (AlgebraicClosure K) a := (exists_root a).choose_spec

omit [CharZero K] in
theorem root_ne_zero (a : Kˣ) : root a ≠ 0 := by
  intro h
  have := root_sq a
  rw [h, zero_pow two_ne_zero] at this
  exact a.ne_zero ((algebraMap K (AlgebraicClosure K)).injective (by rw [← this, map_zero]))

/-- The Kummer character of `a ∈ K^×`. -/
def kummerChar (a : Kˣ) : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* Multiplicative (ZMod 2) :=
  kchar (root a) (root_ne_zero a) ⟨a, root_sq a⟩

theorem kummerChar_eq (a : Kˣ) {x : (AlgebraicClosure K)} (hx0 : x ≠ 0) (hx : x ^ 2 = algebraMap K (AlgebraicClosure K) a) :
    kummerChar a = kchar x hx0 ⟨a, hx⟩ :=
  kchar_eq_of_sq_eq hx0 (root_ne_zero a) _ _ (by rw [root_sq, hx])

/-- **The Kummer homomorphism** `K^× → Hom_cont(Gal(K̄/K), 𝔽₂)`. -/
def kummerHom : Kˣ →* ((AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* Multiplicative (ZMod 2)) where
  toFun := kummerChar
  map_one' := by
    have h1 : (1 : (AlgebraicClosure K)) ^ 2 = algebraMap K (AlgebraicClosure K) (1 : Kˣ) := by simp
    rw [kummerChar_eq 1 one_ne_zero h1]
    ext σ; simp [kchar_apply, kcharFun]
  map_mul' a b := by
    have hab : (root a * root b) ^ 2 = algebraMap K (AlgebraicClosure K) ((a * b : Kˣ) : K) := by
      rw [mul_pow, root_sq, root_sq, Units.val_mul, map_mul]
    rw [kummerChar_eq (a * b) (mul_ne_zero (root_ne_zero a) (root_ne_zero b)) hab]
    exact kchar_mul_root _ _ _ _ _ _


instance : IsGalois K (AlgebraicClosure K) := inferInstance

/-- An element of `K̄` fixed by every automorphism lies in `K`. -/
theorem mem_range_of_forall_fixed {z : (AlgebraicClosure K)} (h : ∀ σ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K), σ z = z) :
    ∃ c : K, algebraMap K (AlgebraicClosure K) c = z := by
  have hmem : z ∈ IntermediateField.fixedField (⊥ : IntermediateField K (AlgebraicClosure K)).fixingSubgroup := by
    rintro ⟨σ, -⟩; exact h σ
  rw [InfiniteGalois.fixedField_fixingSubgroup, IntermediateField.mem_bot] at hmem
  exact hmem

/-- **The kernel of the Kummer homomorphism is the squares.** -/
theorem kummerHom_eq_one_iff (a : Kˣ) :
    kummerHom a = 1 ↔ a ∈ (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  constructor
  · intro h
    have hfix : ∀ σ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K), σ (root a) = root a := by
      intro σ
      have := congrArg (fun χ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* Multiplicative (ZMod 2) => χ σ) h
      change kcharFun (root a) σ = (1 : Multiplicative (ZMod 2)) at this
      by_contra hne
      simp only [kcharFun, hne, ↓reduceIte] at this
      exact absurd this (by decide)
    obtain ⟨c, hc⟩ := mem_range_of_forall_fixed hfix
    have hc0 : c ≠ 0 := by
      rintro rfl; rw [map_zero] at hc; exact root_ne_zero a hc.symm
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    apply (algebraMap K (AlgebraicClosure K)).injective
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hc, root_sq]
  · rintro ⟨c, rfl⟩
    have hx : (algebraMap K (AlgebraicClosure K) c) ^ 2 = algebraMap K (AlgebraicClosure K) ((powMonoidHom 2 c : Kˣ) : K) := by
      simp [map_pow]
    have h0 : algebraMap K (AlgebraicClosure K) c ≠ 0 := by simp
    change kummerChar _ = 1
    rw [kummerChar_eq _ h0 hx]
    ext σ; simp [kchar_apply, kcharFun]


theorem mz2_cases (m : Multiplicative (ZMod 2)) : m = 1 ∨ m = Multiplicative.ofAdd 1 := by
  revert m; decide

/-- **Every continuous character of `Gal(K̄/K)` with values in `𝔽₂` is a Kummer character**
(Hilbert 90 for `n = 2`, here in the elementary form: the kernel `H` is open, its fixed field is a
proper extension, and for `z` in it outside `K` and `σ₀ ∉ H` the element `y = z − σ₀ z` satisfies
`σ y = ±y` according as `σ ∈ H`). -/
theorem kummerHom_surjective : Function.Surjective (kummerHom (K := K)) := by
  intro χ
  by_cases hχ : χ = 1
  · exact ⟨1, by rw [hχ, map_one]⟩
  obtain ⟨σ0, hσ0⟩ : ∃ σ0, χ σ0 ≠ 1 := by
    by_contra h
    push Not at h
    exact hχ (by ext σ; rw [h σ]; rfl)
  have hσ0' : χ σ0 = Multiplicative.ofAdd 1 := (mz2_cases _).resolve_left hσ0
  let H : Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) := χ.toMonoidHom.ker
  have hHc : IsClosed (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) := by
    have : (H : Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) = χ ⁻¹' {1} := by ext σ; simp [H, MonoidHom.mem_ker]
    rw [this]; exact IsClosed.preimage χ.continuous isClosed_singleton
  let L := IntermediateField.fixedField H
  have hfixL : (L.fixingSubgroup) = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHc⟩
  have hfix : ∀ σ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K), χ σ = 1 → ∀ z ∈ L, σ z = z := fun σ hσ z hz =>
    (IntermediateField.mem_fixedField_iff H z).mp hz σ (by simpa [H, MonoidHom.mem_ker] using hσ)
  have hL : L ≠ ⊥ := by
    intro hL
    apply hσ0
    have : σ0 ∈ L.fixingSubgroup := by rw [hL, IntermediateField.fixingSubgroup_bot]; trivial
    rw [hfixL] at this
    simpa [H, MonoidHom.mem_ker] using this
  obtain ⟨z, hzL, hzK⟩ := IsConcreteLE.exists_of_lt (bot_lt_iff_ne_bot.mpr hL)
  have hmove : ∀ σ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K), χ σ ≠ 1 → σ z = σ0 z := by
    intro σ hσ
    have hσ' := (mz2_cases (χ σ)).resolve_left hσ
    have h1 : χ (σ0⁻¹ * σ) = 1 := by rw [map_mul, map_inv, hσ', hσ0']; decide
    have := hfix _ h1 z hzL
    rw [AlgEquiv.mul_apply] at this
    have := congrArg σ0 this
    simpa using this
  set y := z - σ0 z with hydef
  have hy : ∀ σ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K), σ y = if χ σ = 1 then y else -y := by
    intro σ
    have hσσ0 : σ (σ0 z) = (σ * σ0) z := rfl
    by_cases hσ : χ σ = 1
    · rw [if_pos hσ, hydef, map_sub, hfix σ hσ z hzL, hσσ0,
        hmove (σ * σ0) (by rw [map_mul, hσ, one_mul]; exact hσ0)]
    · rw [if_neg hσ, hydef, map_sub, hmove σ hσ, hσσ0,
        hfix (σ * σ0) (by rw [map_mul, (mz2_cases (χ σ)).resolve_left hσ, hσ0']; decide) z hzL]
      ring
  have hy0 : y ≠ 0 := by
    intro h0
    apply hzK
    have hz0 : σ0 z = z := (sub_eq_zero.mp h0).symm
    obtain ⟨c, hc⟩ := mem_range_of_forall_fixed (fun σ => by
      by_cases hσ : χ σ = 1
      · exact hfix σ hσ z hzL
      · rw [hmove σ hσ, hz0])
    exact ⟨c, hc⟩
  have hysq : ∀ σ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K), σ (y ^ 2) = y ^ 2 := by
    intro σ; rw [map_pow, hy σ]; split_ifs <;> ring
  obtain ⟨c, hc⟩ := mem_range_of_forall_fixed hysq
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [map_zero] at hc; exact hy0 (pow_eq_zero_iff two_ne_zero |>.mp hc.symm)
  refine ⟨Units.mk0 c hc0, ?_⟩
  change kummerChar _ = χ
  rw [kummerChar_eq _ hy0 (by rw [Units.val_mk0, hc])]
  ext σ
  simp only [kchar_apply, kcharFun]
  rw [hy σ]
  by_cases hσ : χ σ = 1
  · simp [hσ]
  · simp only [hσ, ↓reduceIte, neg_ne_self hy0]
    rw [(mz2_cases (χ σ)).resolve_left hσ]


theorem ker_kummerHom : (kummerHom (K := K)).ker = (powMonoidHom 2 : Kˣ →* Kˣ).range := by
  ext a; rw [MonoidHom.mem_ker, kummerHom_eq_one_iff]

/-- **Kummer theory for `n = 2`**: `K^×/K^{×2} ≃ Hom_cont(Gal(K̄/K), 𝔽₂)`. -/
noncomputable def kummerQuot :
    (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) ≃* ((AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* Multiplicative (ZMod 2)) :=
  (QuotientGroup.quotientMulEquivOfEq ker_kummerHom.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ kummerHom_surjective)

theorem kummerQuot_mk (a : Kˣ) : kummerQuot (QuotientGroup.mk a) = kummerChar a := rfl

/-- The Kummer character of `a` is trivial on `Gal(K̄/E)` iff `√a ∈ E` (infinite Galois theory). -/
theorem kummerChar_trivial_iff (a : Kˣ) (E : IntermediateField K (AlgebraicClosure K)) :
    (∀ σ ∈ E.fixingSubgroup, kummerChar a σ = 1) ↔ root a ∈ E := by
  constructor
  · intro h
    rw [← InfiniteGalois.fixedField_fixingSubgroup E]
    rintro ⟨σ, hσ⟩
    have := h σ hσ
    change kcharFun (root a) σ = 1 at this
    show σ (root a) = root a
    by_contra hne
    simp only [kcharFun, hne, ↓reduceIte] at this
    exact absurd this (by decide)
  · intro hx σ hσ
    have : σ (root a) = root a := (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ _ hx
    change kcharFun (root a) σ = 1
    simp [kcharFun, this]


section GS
variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))


omit [NumberField K] in
theorem mem_fixingSubgroup_iff_resAbs (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    σ ∈ (unramifiedOutside K S).fixingSubgroup ↔ resAbs K S σ = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h; ext x; rw [resAbs_apply_coe]; exact h x x.2
  · intro h x hx
    have := congrArg (fun τ : GaloisGroupS K S => ((τ ⟨x, hx⟩ : unramifiedOutside K S) :
      AlgebraicClosure K)) h
    simpa [resAbs_apply_coe] using this

/-- Pulling back characters of `G_{K,S}` to `Gal(K̄/K)`. -/
def pullS (χ : GaloisGroupS K S →ₜ* (Multiplicative (ZMod 2))) :
    {χ' : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →ₜ* (Multiplicative (ZMod 2)) //
      ∀ σ ∈ (unramifiedOutside K S).fixingSubgroup, χ' σ = 1} :=
  ⟨χ.comp ⟨resAbs K S, InfiniteGalois.restrictNormalHom_continuous _⟩, fun σ hσ => by
    change χ (resAbs K S σ) = 1
    rw [(mem_fixingSubgroup_iff_resAbs S σ).mp hσ, map_one]⟩

theorem pullS_bijective : Function.Bijective (pullS S) := by
  constructor
  · intro χ₁ χ₂ h
    ext τ
    obtain ⟨σ, rfl⟩ := resAbs_surjective K S τ
    have := congrArg (fun χ => (χ.1 σ)) h
    exact this
  · rintro ⟨χ, hχ⟩
    have hconst : ∀ σ₁ σ₂, resAbs K S σ₁ = resAbs K S σ₂ → χ σ₁ = χ σ₂ := by
      intro σ₁ σ₂ h
      have h' : σ₁⁻¹ * σ₂ ∈ (unramifiedOutside K S).fixingSubgroup := by
        rw [mem_fixingSubgroup_iff_resAbs, map_mul, map_inv, h, inv_mul_cancel]
      have := hχ _ h'
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this
    let f : GaloisGroupS K S →* (Multiplicative (ZMod 2)) :=
      { toFun := fun τ => χ (resAbs_surjective K S τ).choose
        map_one' := by
          rw [hconst _ 1 (by rw [(resAbs_surjective K S 1).choose_spec, map_one]), map_one]
        map_mul' := fun τ₁ τ₂ => by
          rw [← map_mul, hconst _ ((resAbs_surjective K S τ₁).choose *
            (resAbs_surjective K S τ₂).choose)]
          rw [map_mul, (resAbs_surjective K S _).choose_spec,
            (resAbs_surjective K S _).choose_spec, (resAbs_surjective K S _).choose_spec] }
    have hcomp : ∀ σ, f (resAbs K S σ) = χ σ := fun σ =>
      hconst _ _ ((resAbs_surjective K S _).choose_spec)
    have hq : Topology.IsQuotientMap (resAbs K S) :=
      Topology.IsQuotientMap.of_surjective_continuous (resAbs_surjective K S)
        (InfiniteGalois.restrictNormalHom_continuous _)
    have hf : Continuous f := by
      rw [hq.continuous_iff]
      have : (f ∘ resAbs K S) = χ := funext hcomp
      rw [this]; exact χ.continuous
    refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
    ext σ
    exact hcomp σ

/-- **Characters of `G_{K,S}` are the Selmer classes** (Kummer theory; tex 4482–4492): given the
two stage statements, `|Hom_cont(G_{K,S}, 𝔽₂)| = |K(S,2)|` when `S` contains the primes above `2`.
PROVED. -/
theorem card_hom_eq_card_selmer (hSqrt : SqrtMemOfSelmer) (hSel : SelmerOfSqrtMem)
    (hS2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Nat.card (GaloisGroupS K S →ₜ* (Multiplicative (ZMod 2))) =
      Nat.card (IsDedekindDomain.selmerGroup (R := 𝓞 K) (K := K) (S := S) (n := 2)) := by
  rw [Nat.card_congr (Equiv.ofBijective _ (pullS_bijective S))]
  let e := (kummerQuot (K := K)).toEquiv
  refine Nat.card_congr (Equiv.subtypeEquiv e.symm fun χ => ?_)
  obtain ⟨c, hc⟩ : ∃ c, e c = χ := e.surjective χ
  subst hc
  rw [Equiv.symm_apply_apply]
  induction c using QuotientGroup.induction_on with
  | H a =>
    change (∀ σ ∈ _, kummerChar a σ = 1) ↔ _
    rw [kummerChar_trivial_iff]
    exact ⟨fun h => hSel K S a (root a) (root_sq a) h,
      fun h => hSqrt K S hS2 a (root a) (root_sq a) h⟩

end GS
end ZInQ.Contrib.CloudB3RC53.RankCounts.KummerS
