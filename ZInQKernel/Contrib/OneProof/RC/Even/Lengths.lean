import Mathlib

/-!
# Theorem 5.3, Lane RC11-even: the Kummer-duality length bookkeeping (E.6)–(E.7)

The 11/5 manuscript (`diophantine_zq.tex`), Appendix E, proof of Proposition
`ex:app-central-calibration` (tex 7631–7787). At a corank-zero constituent `E^h` the proof computes
`v₂ u_h^{ev}(0)` from exact sequences of finite-length `ℤ₂`-modules. This file proves the length
bookkeeping in that computation, over an arbitrary ring and arbitrary modules:

* `length_exact_four`, `length_exact_five`: lengths are additive along exact sequences
  `0 → A → B → C → D → 0` and `0 → X₁ → ⋯ → X₅ → 0` (values in `ℕ∞`, no finiteness assumed);
* `E6_length` — **(E.6)** (tex 7642, 7698–7730): `ℓ H²_glob = s(h) − i + Σ_v g_v + r₂ − g`, from the
  orthogonal-Kummer Poitou–Tate sequence and the lengths of its other terms;
* `length_quot_eq_torsion_add_free` and `length_coker_eq` — the free-index identity
  `ℓ coker(H¹_glob → H¹_ℝ) = r₁ − g + k − m` (tex 7649–7651, 7744–7747), with `g` the torsion length
  of `H¹_glob`, `k` the torsion length of `K = ker(H¹_glob → H¹_ℝ)` and `m` the free index of `K`;
* `length_torsion_quotient` — `k = p₀ + a_s` (tex 7650, 7746): `0 → T⁺ → P → K → 0` with `T⁺`
  torsion-free, `p₀` the torsion length of `P = H¹(C_h⁺)` and `a_s` the saturation index of the real
  line;
* `surjective_real_of_exact` — `H²_glob → H²(ℝ, T)` is onto (tex 7732–7735): a real component can be
  cancelled by a component at two, because the dyadic component of the last map is onto;
* `E7_of_lengths` — **(E.7)** (tex 7653–7660, 7748–7754): substitution of these equalities cancels
  `m` and `a_s` exactly and gives
  `v₂ u_h^{ev}(0) = v₂ exp* z − s(h) − Σ_v g_v + 2g + 1 − r₁ − e₂`.

Everything here is PROVED. The exact sequences themselves (Poitou–Tate, the positive-cone
sequences, local Tate duality) and the two determinant contributions of the wedge (E.4) are the
inputs; see `EvenSource.lean`.
-/

namespace ZInQ.Manuscript.RC.Even

open Module Submodule

section Exact

variable {R : Type*} [Ring R]

/-- **Length is additive along a four-term exact sequence** `0 → A → B → C → D → 0`
(PROVED): `ℓA + ℓC = ℓB + ℓD` in `ℕ∞`. -/
theorem length_exact_four {A B C D : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (k : C →ₗ[R] D) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hgk : Function.Exact g k) (hk : Function.Surjective k) :
    length R A + length R C = length R B + length R D := by
  have hB : length R B = length R A + length R (LinearMap.range g) :=
    Module.length_eq_add_of_exact f g.rangeRestrict hf g.surjective_rangeRestrict
      (LinearMap.exact_iff.mpr <| by
        rw [LinearMap.ker_rangeRestrict]; exact LinearMap.exact_iff.mp hfg)
  have hC : length R C = length R (LinearMap.range g) + length R D :=
    Module.length_eq_add_of_exact (LinearMap.range g).subtype k
      (LinearMap.range g).injective_subtype hk (LinearMap.exact_iff.mpr <| by
        rw [Submodule.range_subtype]; exact LinearMap.exact_iff.mp hgk)
  rw [hB, hC, add_assoc]

/-- **Length is additive along a five-term exact sequence** `0 → X₁ → X₂ → X₃ → X₄ → X₅ → 0`
(PROVED): `ℓX₁ + ℓX₃ + ℓX₅ = ℓX₂ + ℓX₄` in `ℕ∞`. -/
theorem length_exact_five {X₁ X₂ X₃ X₄ X₅ : Type*} [AddCommGroup X₁] [Module R X₁]
    [AddCommGroup X₂] [Module R X₂] [AddCommGroup X₃] [Module R X₃] [AddCommGroup X₄]
    [Module R X₄] [AddCommGroup X₅] [Module R X₅]
    (f₁ : X₁ →ₗ[R] X₂) (f₂ : X₂ →ₗ[R] X₃) (f₃ : X₃ →ₗ[R] X₄) (f₄ : X₄ →ₗ[R] X₅)
    (h₁ : Function.Injective f₁) (h₁₂ : Function.Exact f₁ f₂) (h₂₃ : Function.Exact f₂ f₃)
    (h₃₄ : Function.Exact f₃ f₄) (h₄ : Function.Surjective f₄) :
    length R X₁ + length R X₃ + length R X₅ = length R X₂ + length R X₄ := by
  have hX₂ : length R X₂ = length R X₁ + length R (LinearMap.range f₂) :=
    Module.length_eq_add_of_exact f₁ f₂.rangeRestrict h₁ f₂.surjective_rangeRestrict
      (LinearMap.exact_iff.mpr <| by
        rw [LinearMap.ker_rangeRestrict]; exact LinearMap.exact_iff.mp h₁₂)
  have h4 := length_exact_four (LinearMap.range f₂).subtype f₃ f₄
    (LinearMap.range f₂).injective_subtype
    (LinearMap.exact_iff.mpr (by rw [Submodule.range_subtype]; exact LinearMap.exact_iff.mp h₂₃))
    h₃₄ h₄
  rw [hX₂, add_assoc, add_assoc, h4]

/-- **(E.6)** (tex 7642, 7698–7730; PROVED from the exact sequence): in the orthogonal-Kummer
Poitou–Tate sequence
`0 → L₂/J₂ → Sel_{2^∞}(E^h/ℚ)^∨ → H²_glob → ⊕_{v ∈ S_f} H²(ℚ_v, T) ⊕ H²(ℝ, T) → H⁰(ℚ, D)^∨ → 0`
with `ℓ(L₂/J₂) = i`, `ℓ Sel^∨ = s(h)`, `ℓ ⊕_v H²(ℚ_v, T) = Σ_v g_v` (`= G`), `ℓ H²(ℝ, T) = r₂` and
`ℓ H⁰(ℚ, D)^∨ = g`, the global term has finite length and `ℓ H²_glob = s(h) − i + Σ_v g_v + r₂ − g`. -/
theorem E6_length {X₁ X₂ X₃ Xloc XR X₅ : Type*} [AddCommGroup X₁] [Module R X₁]
    [AddCommGroup X₂] [Module R X₂] [AddCommGroup X₃] [Module R X₃] [AddCommGroup Xloc]
    [Module R Xloc] [AddCommGroup XR] [Module R XR] [AddCommGroup X₅] [Module R X₅]
    (f₁ : X₁ →ₗ[R] X₂) (f₂ : X₂ →ₗ[R] X₃) (f₃ : X₃ →ₗ[R] Xloc × XR) (f₄ : Xloc × XR →ₗ[R] X₅)
    (h₁ : Function.Injective f₁) (h₁₂ : Function.Exact f₁ f₂) (h₂₃ : Function.Exact f₂ f₃)
    (h₃₄ : Function.Exact f₃ f₄) (h₄ : Function.Surjective f₄)
    (i s G r₂ g : ℕ) (hi : length R X₁ = i) (hs : length R X₂ = s) (hG : length R Xloc = G)
    (hr : length R XR = r₂) (hg : length R X₅ = g) :
    ∃ n : ℕ, length R X₃ = n ∧ (n : ℤ) = s - i + G + r₂ - g := by
  have key := length_exact_five f₁ f₂ f₃ f₄ h₁ h₁₂ h₂₃ h₃₄ h₄
  rw [Module.length_prod, hi, hs, hG, hr, hg] at key
  have hfin : (i : ℕ∞) + length R X₃ + g ≠ ⊤ := by
    rw [key]; exact_mod_cast ENat.natCast_ne_top (s + (G + r₂))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (WithTop.add_ne_top.mp (WithTop.add_ne_top.mp hfin).1).2
  refine ⟨n, hn.symm, ?_⟩
  rw [← hn] at key
  norm_cast at key
  omega

/-- **`H²_glob → H²(ℝ, T)` is onto** (tex 7732–7735; PROVED): in an exact sequence
`A → B₂ × B_ℝ × B' → C` whose last map is the sum of its three components, if the dyadic component
`β₂ : B₂ → C` is onto (it is dual to the injective restriction `H⁰(ℚ, D) → H⁰(ℚ₂, D)`), then the
real component `A → B_ℝ` is onto: any real component's image can be cancelled at two. -/
theorem surjective_real_of_exact {A B₂ BR B' C : Type*} [AddCommGroup A] [Module R A]
    [AddCommGroup B₂] [Module R B₂] [AddCommGroup BR] [Module R BR] [AddCommGroup B']
    [Module R B'] [AddCommGroup C] [Module R C]
    (α : A →ₗ[R] B₂ × BR × B') (β₂ : B₂ →ₗ[R] C) (βR : BR →ₗ[R] C) (β' : B' →ₗ[R] C)
    (hex : Function.Exact α (β₂.coprod (βR.coprod β'))) (hβ₂ : Function.Surjective β₂) :
    Function.Surjective ((LinearMap.fst R BR B').comp ((LinearMap.snd R B₂ (BR × B')).comp α)) := by
  intro bR
  obtain ⟨b₂, hb₂⟩ := hβ₂ (-(βR bR))
  obtain ⟨x, hx⟩ := (hex (b₂, (bR, 0))).mp (by simp [hb₂])
  exact ⟨x, by simp [hx]⟩

end Exact

section Torsion

variable {R : Type*} [CommRing R]

/-- **The free-index decomposition** (tex 7644–7651; PROVED): for a submodule `K ≤ M`,
`ℓ(M/K) + ℓ(K ∩ M_tors) = ℓ(M_tors) + ℓ(M/(K + M_tors))` in `ℕ∞`. With
`g = ℓ(M_tors)`, `k = ℓ(K ∩ M_tors)` (the torsion length of `K`, see `torsion_submodule_eq`) and
the free index `m = ℓ(M/(K + M_tors))`, this is `ℓ(M/K) = (g − k) + m`. -/
theorem length_quot_eq_torsion_add_free {M : Type*} [AddCommGroup M] [Module R M]
    (K : Submodule R M) :
    length R (M ⧸ K) + length R ↥(K ⊓ torsion R M) =
      length R ↥(torsion R M) + length R (M ⧸ (K ⊔ torsion R M)) := by
  rw [add_comm]
  refine length_exact_four (Submodule.inclusion (inf_le_right : K ⊓ torsion R M ≤ torsion R M))
    (K.mkQ ∘ₗ (torsion R M).subtype) (Submodule.factor (le_sup_left : K ≤ K ⊔ torsion R M))
    (Submodule.inclusion_injective _) ?_ ?_ (Submodule.factor_surjective _)
  · rintro ⟨t, ht⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Set.mem_range]
    constructor
    · intro hk
      exact ⟨⟨t, hk, ht⟩, rfl⟩
    · rintro ⟨⟨x, hxK, hxT⟩, hx⟩
      have hxt : x = t := congrArg Subtype.val hx
      exact hxt ▸ hxK
  · intro y
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective K y
    change Submodule.Quotient.mk m = (0 : M ⧸ (K ⊔ torsion R M)) ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_sup]
    constructor
    · rintro ⟨k, hk, t, ht, rfl⟩
      refine ⟨⟨t, ht⟩, ?_⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      have hkt : t - (k + t) = -k := by abel
      rw [hkt]
      exact K.neg_mem hk
    · rintro ⟨⟨t, ht⟩, h⟩
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        Submodule.mkQ_apply] at h
      rw [Submodule.Quotient.eq] at h
      refine ⟨m - t, ?_, t, ht, sub_add_cancel m t⟩
      have hmt : m - t = -(t - m) := by abel
      rw [hmt]
      exact K.neg_mem h

/-- The torsion of a submodule `K ≤ M` is `K ∩ M_tors` (PROVED): the two have the same length. -/
theorem length_torsion_submodule {M : Type*} [AddCommGroup M] [Module R M] (K : Submodule R M) :
    length R ↥(torsion R ↥K) = length R ↥(K ⊓ torsion R M) := by
  have h : (torsion R ↥K).map K.subtype = K ⊓ torsion R M := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.mem_torsion_iff,
      Submodule.coe_subtype]
    constructor
    · rintro ⟨y, ⟨a, ha⟩, rfl⟩
      exact ⟨y.2, a, by simpa using congrArg Subtype.val ha⟩
    · rintro ⟨hxK, a, ha⟩
      exact ⟨⟨x, hxK⟩, ⟨a, Subtype.ext ha⟩, rfl⟩
  exact ((Submodule.equivMapOfInjective K.subtype K.injective_subtype _).trans
    (LinearEquiv.ofEq _ _ h)).length_eq

/-- **`ℓ coker(H¹_glob → H¹_ℝ) = r₁ − g + k − m`** (tex 7649–7651, 7744–7747; PROVED), in the
subtraction-free form `ℓ coker ρ + g + m = r₁ + k`, for `ρ : M → H` with `K = ker ρ`,
`r₁ = ℓH`, `g = ℓ(M_tors)`, `k = ℓ(K ∩ M_tors)`, `m = ℓ(M/(K + M_tors))`, all finite. -/
theorem length_coker_eq {M H : Type*} [AddCommGroup M] [Module R M] [AddCommGroup H]
    [Module R H] (ρ : M →ₗ[R] H) (r₁ g k m : ℕ) (hH : length R H = r₁)
    (hg : length R ↥(torsion R M) = g) (hk : length R ↥(LinearMap.ker ρ ⊓ torsion R M) = k)
    (hm : length R (M ⧸ (LinearMap.ker ρ ⊔ torsion R M)) = m) :
    ∃ c : ℕ, length R (H ⧸ LinearMap.range ρ) = c ∧ c + g + m = r₁ + k := by
  have h1 : length R H = length R (M ⧸ LinearMap.ker ρ) + length R (H ⧸ LinearMap.range ρ) :=
    Module.length_eq_add_of_exact ((LinearMap.ker ρ).liftQ ρ le_rfl) (LinearMap.range ρ).mkQ
      (by rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
      (Submodule.mkQ_surjective _)
      (by rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_liftQ])
  have h2 := length_quot_eq_torsion_add_free (LinearMap.ker ρ)
  rw [hH] at h1
  rw [hk, hg, hm] at h2
  have hq : length R (M ⧸ LinearMap.ker ρ) + k ≠ ⊤ := by
    rw [h2]; exact_mod_cast ENat.natCast_ne_top (g + m)
  have hc : length R (M ⧸ LinearMap.ker ρ) + length R (H ⧸ LinearMap.range ρ) ≠ ⊤ := by
    rw [← h1]; exact ENat.natCast_ne_top r₁
  obtain ⟨q, hq'⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp hq).1
  obtain ⟨c, hc'⟩ := ENat.ne_top_iff_exists.mp (WithTop.add_ne_top.mp hc).2
  refine ⟨c, hc'.symm, ?_⟩
  rw [← hq', ← hc'] at h1
  rw [← hq'] at h2
  norm_cast at h1 h2
  omega

/-- **`k = p₀ + a_s`** (tex 7650, 7737–7747; PROVED): let `0 → T⁺ → P → K → 0` be exact with `T⁺`
torsion-free (the real invariants `H⁰(ℝ, T) = T⁺`, a free `ℤ₂`-module). Write
`Sat = π⁻¹(K_tors)` for the saturation of the real line `a(T⁺)` in `P`. Then
`ℓ(K_tors) = ℓ(P_tors) + ℓ(Sat/(a(T⁺) + P_tors))`; the last term is the saturation index `a_s` of
the real image in `P/P_tors`. -/
theorem length_torsion_quotient {T P K : Type*} [AddCommGroup T] [Module R T] [AddCommGroup P]
    [Module R P] [AddCommGroup K] [Module R K] (a : T →ₗ[R] P) (π : P →ₗ[R] K)
    (ha : Function.Injective a) (hex : Function.Exact a π) (hπ : Function.Surjective π)
    (hT : torsion R T = ⊥) :
    length R ↥(torsion R K) =
      length R ↥(torsion R P) +
        length R (↥((torsion R K).comap π) ⧸
          (LinearMap.range a ⊔ torsion R P).comap ((torsion R K).comap π).subtype) := by
  set S := (torsion R K).comap π with hS
  set B := (LinearMap.range a ⊔ torsion R P).comap S.subtype with hB
  -- the restriction of `π` to the saturation, onto the torsion of `K`
  let φ : S →ₗ[R] torsion R K := π.restrict (fun x hx => hx)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker : ∀ x : S, x ∈ LinearMap.ker φ ↔ (x : P) ∈ LinearMap.range a := by
    intro x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    have : φ x = 0 ↔ π x = 0 := by
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h
    rw [this, hex (x : P)]
    rfl
  have hTS : torsion R P ≤ S := by
    intro p hp
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff p).mp hp
    show π p ∈ torsion R K
    exact (Submodule.mem_torsion_iff _).mpr
      ⟨r, by rw [Submonoid.smul_def, ← map_smul, ← Submonoid.smul_def, hr, map_zero]⟩
  have hle : LinearMap.ker φ ≤ B := by
    intro x hx
    rw [hB, Submodule.mem_comap]
    exact Submodule.mem_sup_left ((hker x).mp hx)
  -- the inclusion of the torsion of `P` into `S ⧸ ker φ`
  let ι : torsion R P →ₗ[R] S ⧸ LinearMap.ker φ :=
    (LinearMap.ker φ).mkQ ∘ₗ Submodule.inclusion hTS
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨p, hp⟩ h
    simp only [ι, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at h
    rw [hker] at h
    obtain ⟨t, ht⟩ := h
    have ht' : a t = p := ht
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff p).mp hp
    have hrt : r • t = 0 := by
      apply ha
      rw [Submonoid.smul_def, map_smul, ← Submonoid.smul_def, ht', hr, map_zero]
    have ht0 : t ∈ torsion R T := (Submodule.mem_torsion_iff t).mpr ⟨r, hrt⟩
    rw [hT, Submodule.mem_bot] at ht0
    subst ht0
    ext
    simp [← ht']
  have hexι : Function.Exact ι (Submodule.factor hle) := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk x = (0 : S ⧸ B) ↔ _
    rw [Submodule.Quotient.mk_eq_zero, hB, Submodule.mem_comap, Submodule.mem_sup]
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, z, hz, hsum⟩
      refine ⟨⟨z, hz⟩, ?_⟩
      simp only [ι, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq, hker]
      refine ⟨-t, ?_⟩
      simp only [Submodule.coe_subtype] at hsum
      simp only [map_neg, Submodule.coe_sub, Submodule.coe_inclusion, ← hsum]
      abel
    · rintro ⟨⟨z, hz⟩, h⟩
      simp only [ι, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply] at h
      rw [Submodule.Quotient.eq, hker] at h
      obtain ⟨t, ht⟩ := h
      refine ⟨_, ⟨-t, rfl⟩, z, hz, ?_⟩
      simp only [Submodule.coe_sub, Submodule.coe_inclusion] at ht
      simp only [map_neg, ht, Submodule.coe_subtype]
      abel
  have h1 := Module.length_eq_add_of_exact ι (Submodule.factor hle) hι
    (Submodule.factor_surjective hle) hexι
  rw [← (φ.quotKerEquivOfSurjective hφ).length_eq, h1]

end Torsion

/-- **(E.7)** (tex 7653–7660, 7748–7754; PROVED): the substitution. With
* (E.6) `ℓH²_glob = s − i + G + r₂ − g` (`G = Σ_v g_v`),
* `ℓ coker(H¹_glob → H¹_ℝ) = r₁ − g + k − m` and `k = p₀ + a_s`,
* the positive cone `0 → coker → H²(C_h⁺) → H²_glob → H²(ℝ, T) → 0`, i.e.
  `ℓ coker + ℓH²_glob = ℓH²(C_h⁺) + r₂`,
* the wedge (E.4) contributing `a_s + 1 + v_free(z) − m` and the inverse-determinant conversion
  contributing `p₀ − ℓH²(C_h⁺)`, and
* `v₂ exp* z = v_free(z) + i + e₂`,

the terms `m` and `a_s` cancel exactly and
`v₂ u_h^{ev}(0) = v₂ exp* z − s − Σ_v g_v + 2g + 1 − r₁ − e₂`. -/
theorem E7_of_lengths (v2u v2exp s G g r₁ r₂ e₂ i k m p₀ aₛ vfree H2glob H2plus coker : ℤ)
    (hE6 : H2glob = s - i + G + r₂ - g) (hcoker : coker = r₁ - g + k - m) (hk : k = p₀ + aₛ)
    (hplus : coker + H2glob = H2plus + r₂)
    (hwedge : v2u = (aₛ + 1 + vfree - m) + (p₀ - H2plus)) (hexp : v2exp = vfree + i + e₂) :
    v2u = v2exp - s - G + 2 * g + 1 - r₁ - e₂ := by
  linarith

end ZInQ.Manuscript.RC.Even
