import Mathlib
import ZInQKernel.Contrib.Dim.IntegralHom
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Theorems.Thm_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime

/-!
# p1-quot3, part A: normality descends to invariant rings

`C` a ring with an action of a finite group `G`, `D → C` injective with image the invariants
(`Algebra.IsInvariant`). If every localization of `C` at a prime is an integrally closed domain, so is every
localization of `D` at a prime. (Elementwise, by prime avoidance and norms; no decomposition of `C` into
domains.)
-/

open scoped Pointwise

namespace P1Quot3

section LemmaA

variable {C D : Type*} [CommRing C] [CommRing D] [Algebra D C]
  {G : Type*} [Group G] [Fintype G] [MulSemiringAction G C]

/-- **Norm trick.** A `G`-stable ideal `I` not contained in a prime `𝔫` contains an invariant element outside
`𝔫` (prime avoidance over the `g • 𝔫`, then the norm `∏ g • w`). -/
theorem exists_algebraMap_mem_notMem [Algebra.IsInvariant D C G]
    (I : Ideal C) (hI : ∀ g : G, ∀ c ∈ I, g • c ∈ I) (𝔫 : Ideal C) [h𝔫 : 𝔫.IsPrime]
    (hn : ¬ I ≤ 𝔫) : ∃ d : D, algebraMap D C d ∈ I ∧ algebraMap D C d ∉ 𝔫 := by
  classical
  have hnot : ¬ ((I : Set C) ⊆ ⋃ g ∈ ((Finset.univ : Finset G) : Set G), ((g • 𝔫 : Ideal C) : Set C)) := by
    rw [Ideal.subset_union_prime 1 1 (fun g _ _ _ => Ideal.IsPrime.smul g)]
    rintro ⟨g, -, hg⟩
    apply hn
    intro c hc
    have h1 : g • c ∈ g • 𝔫 := hg (hI g c hc)
    exact (Ideal.smul_mem_pointwise_smul_iff).1 h1
  obtain ⟨w, hwI, hw⟩ := Set.not_subset.1 hnot
  simp only [Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion, not_exists] at hw
  have hgw : ∀ g : G, g • w ∉ 𝔫 := by
    intro g hg
    apply hw g⁻¹
    rw [SetLike.mem_coe, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    exact hg
  obtain ⟨d, hd⟩ := Algebra.IsInvariant.isInvariant (A := D) (∏ g : G, g • w)
    (fun g => Finset.smul_prod_perm w g)
  refine ⟨d, ?_, ?_⟩
  · rw [hd]
    apply Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem (fun g : G => g • w) (Finset.mem_univ 1))
    rw [one_smul]
    exact hwI
  · rw [hd, h𝔫.prod_mem_iff]
    rintro ⟨g, -, hg⟩
    exact hgw g hg

end LemmaA

section Descent

variable {C D : Type*} [CommRing C] [CommRing D] [Algebra D C]
  {G : Type*} [Group G] [Fintype G] [MulSemiringAction G C] [SMulCommClass G D C]
  [Algebra.IsInvariant D C G]

/-- Variant of the norm trick: the invariant element lies outside `𝔫`, i.e. outside `𝔮 = 𝔫 ∩ D`. -/
theorem exists_notMem_comap (I : Ideal C) (hI : ∀ g : G, ∀ c ∈ I, g • c ∈ I) (𝔫 : Ideal C) [𝔫.IsPrime]
    (hn : ¬ I ≤ 𝔫) : ∃ d : D, d ∉ 𝔫.comap (algebraMap D C) ∧ algebraMap D C d ∈ I := by
  obtain ⟨d, h1, h2⟩ := exists_algebraMap_mem_notMem (D := D) (G := G) I hI 𝔫 hn
  exact ⟨d, h2, h1⟩

/-- The annihilator of an invariant element is `G`-stable. -/
theorem annihilator_stable (a : D) : ∀ g : G, ∀ c ∈ (Submodule.span C {algebraMap D C a}).annihilator,
    g • c ∈ (Submodule.span C {algebraMap D C a}).annihilator := by
  intro g c hc
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hc ⊢
  rw [← smul_algebraMap g a, ← MulSemiringAction.smul_mul, hc, smul_zero]

variable (hinj : Function.Injective (algebraMap D C))
include G hinj

/-- **Zero test.** If an element of `D` vanishes in `C_𝔫`, it vanishes in `D_𝔮`, `𝔮 = 𝔫 ∩ D`. -/
theorem eq_zero_of_eq_zero_atPrime (𝔫 : Ideal C) [𝔫.IsPrime] (a : D)
    (ha : algebraMap C (Localization.AtPrime 𝔫) (algebraMap D C a) = 0) :
    ∃ d : D, d ∉ 𝔫.comap (algebraMap D C) ∧ d * a = 0 := by
  obtain ⟨⟨w, hw⟩, hwa⟩ := (IsLocalization.map_eq_zero_iff 𝔫.primeCompl _ _).1 ha
  have hn : ¬ (Submodule.span C {algebraMap D C a}).annihilator ≤ 𝔫 := by
    intro hle
    apply hw
    apply hle
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
    exact hwa
  obtain ⟨d, hd, hdI⟩ := exists_notMem_comap (D := D) (G := G) _ (annihilator_stable (G := G) a) 𝔫 hn
  refine ⟨d, hd, hinj ?_⟩
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul] at hdI
  rw [map_mul, hdI, map_zero]

/-- The local map `D_𝔮 → C_𝔫` is injective. -/
theorem localRingHom_injective (𝔫 : Ideal C) [𝔫.IsPrime] (𝔮 : Ideal D) [𝔮.IsPrime]
    (h : 𝔮 = 𝔫.comap (algebraMap D C)) :
    Function.Injective (Localization.localRingHom 𝔮 𝔫 (algebraMap D C) h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔮.primeCompl x
  rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨⟨w, hw⟩, hwa⟩ := hx
  have ha : algebraMap C (Localization.AtPrime 𝔫) (algebraMap D C a) = 0 := by
    rw [IsLocalization.map_eq_zero_iff 𝔫.primeCompl]
    exact ⟨⟨w, hw⟩, hwa⟩
  obtain ⟨d, hd, hda⟩ := eq_zero_of_eq_zero_atPrime (G := G) hinj 𝔫 a ha
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨d, h ▸ hd⟩, hda⟩

/-- **Division test.** For `a b : D` with `b ≠ 0` in `C_𝔫`, if `b ∣ a` in `C_𝔫` (𝔫 a prime with `C_𝔫` a domain)
then `b ∣ a` in `D_𝔮`. -/
theorem dvd_of_dvd_atPrime (𝔫 : Ideal C) [𝔫.IsPrime] [IsDomain (Localization.AtPrime 𝔫)] (a b : D)
    (hb : algebraMap C (Localization.AtPrime 𝔫) (algebraMap D C b) ≠ 0)
    (hab : ∃ c : Localization.AtPrime 𝔫,
      algebraMap C (Localization.AtPrime 𝔫) (algebraMap D C a) =
        algebraMap C (Localization.AtPrime 𝔫) (algebraMap D C b) * c) :
    ∃ (e f : D), e ∉ 𝔫.comap (algebraMap D C) ∧ e * a = b * f := by
  classical
  set a' := algebraMap D C a
  set b' := algebraMap D C b
  obtain ⟨c, hc⟩ := hab
  obtain ⟨⟨z, ⟨w, hw⟩⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔫.primeCompl c
  -- the colon ideal `{x | x a' ∈ (b')}` is `G`-stable and not inside `𝔫`
  let J : Ideal C :=
    { carrier := {x | ∃ y, x * a' = b' * y}
      add_mem' := by
        rintro x x' ⟨y, hy⟩ ⟨y', hy'⟩
        exact ⟨y + y', by rw [add_mul, hy, hy', mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r x ⟨y, hy⟩
        exact ⟨r * y, by rw [smul_eq_mul, mul_assoc, hy]; ring⟩ }
  have hJmem : ∀ x : C, x ∈ J ↔ ∃ y, x * a' = b' * y := fun x => Iff.rfl
  have hJst : ∀ g : G, ∀ x ∈ J, g • x ∈ J := by
    intro g x hx
    obtain ⟨y, hy⟩ := (hJmem x).1 hx
    refine (hJmem _).2 ⟨g • y, ?_⟩
    have ha' : g • a' = a' := smul_algebraMap g a
    have hb' : g • b' = b' := smul_algebraMap g b
    rw [← ha', ← MulSemiringAction.smul_mul, hy, MulSemiringAction.smul_mul, hb']
  have hJn : ¬ J ≤ 𝔫 := by
    have hc' : algebraMap C (Localization.AtPrime 𝔫) (a' * w) =
        algebraMap C (Localization.AtPrime 𝔫) (b' * z) := by
      have hspec : IsLocalization.mk' (Localization.AtPrime 𝔫) z (⟨w, hw⟩ : 𝔫.primeCompl) *
          algebraMap C (Localization.AtPrime 𝔫) w = algebraMap C _ z :=
        IsLocalization.mk'_spec _ z ⟨w, hw⟩
      rw [map_mul, map_mul, hc, mul_assoc, hspec]
    obtain ⟨⟨v, hv⟩, hv'⟩ := (IsLocalization.eq_iff_exists 𝔫.primeCompl _).1 hc'
    intro hle
    have hmem : v * w ∈ J := (hJmem _).2 ⟨v * z, by
      calc v * w * a' = v * (a' * w) := by ring
        _ = v * (b' * z) := hv'
        _ = b' * (v * z) := by ring⟩
    exact (Ideal.IsPrime.mem_or_mem ‹_› (hle hmem)).elim hv hw
  obtain ⟨d, hd, hdJ⟩ := exists_notMem_comap (D := D) (G := G) J hJst 𝔫 hJn
  obtain ⟨c₀, hc₀⟩ := (hJmem _).1 hdJ
  -- `c₀` is invariant up to an element outside `𝔫`
  let K : Ideal C := ⨅ g : G, (Submodule.span C {g • c₀ - c₀}).annihilator
  have hKmem : ∀ x : C, x ∈ K ↔ ∀ g : G, x * (g • c₀ - c₀) = 0 := by
    intro x
    simp only [K, Submodule.mem_iInf, Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  have hKst : ∀ g : G, ∀ x ∈ K, g • x ∈ K := by
    intro g x hx
    rw [hKmem] at hx ⊢
    intro h
    have e1 := hx (g⁻¹ * h)
    have e2 := hx g⁻¹
    have : x * (g⁻¹ • (h • c₀ - c₀)) = 0 := by
      rw [smul_sub, ← mul_smul]
      calc x * ((g⁻¹ * h) • c₀ - g⁻¹ • c₀)
          = x * ((g⁻¹ * h) • c₀ - c₀) - x * (g⁻¹ • c₀ - c₀) := by ring
        _ = 0 := by rw [e1, e2, sub_zero]
    have h2 := congrArg (fun y => g • y) this
    simp only [MulSemiringAction.smul_mul, smul_inv_smul, smul_zero] at h2
    exact h2
  have hinv0 : ∀ g : G, b' * (g • c₀ - c₀) = 0 := by
    intro g
    have h1 : g • (algebraMap D C d * a') = algebraMap D C d * a' := by
      rw [MulSemiringAction.smul_mul, smul_algebraMap, smul_algebraMap]
    rw [hc₀, MulSemiringAction.smul_mul, smul_algebraMap] at h1
    rw [mul_sub, h1, sub_self]
  have hKn : ¬ K ≤ 𝔫 := by
    have hloc : ∀ g : G, ∃ u : C, u ∉ 𝔫 ∧ u * (g • c₀ - c₀) = 0 := by
      intro g
      have h0 : algebraMap C (Localization.AtPrime 𝔫) b' *
          algebraMap C (Localization.AtPrime 𝔫) (g • c₀ - c₀) = 0 := by
        rw [← map_mul, hinv0, map_zero]
      have h1 := (mul_eq_zero.1 h0).resolve_left hb
      obtain ⟨⟨u, hu⟩, hu'⟩ := (IsLocalization.map_eq_zero_iff 𝔫.primeCompl _ _).1 h1
      exact ⟨u, hu, hu'⟩
    choose u hu hu' using hloc
    intro hle
    have hmem : (∏ g : G, u g) ∈ K := by
      rw [hKmem]
      intro g
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), mul_assoc, hu', mul_zero]
    have := hle hmem
    rw [Ideal.IsPrime.prod_mem_iff] at this
    obtain ⟨g, -, hg⟩ := this
    exact hu g hg
  obtain ⟨e, he, heK⟩ := exists_notMem_comap (D := D) (G := G) K hKst 𝔫 hKn
  rw [hKmem] at heK
  obtain ⟨f, hf⟩ := Algebra.IsInvariant.isInvariant (A := D) (G := G) (algebraMap D C e * c₀) (by
    intro g
    rw [MulSemiringAction.smul_mul, smul_algebraMap]
    have := heK g
    rw [mul_sub, sub_eq_zero] at this
    exact this)
  refine ⟨e * d, f, ?_, hinj ?_⟩
  · intro hmem
    exact (Ideal.IsPrime.mem_or_mem inferInstance hmem).elim he hd
  · rw [map_mul, map_mul, map_mul, hf, mul_assoc, hc₀]
    ring

/-- **Normality descends to the invariants.** If every localization of `C` at a prime is an integrally closed
domain, so is every localization of `D` at a prime. -/
theorem isDomain_isIntegrallyClosed_atPrime
    (hN : ∀ (𝔫 : Ideal C) [𝔫.IsPrime],
      IsDomain (Localization.AtPrime 𝔫) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔫))
    (𝔮 : Ideal D) [𝔮.IsPrime] :
    IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮) := by
  classical
  have : Algebra.IsIntegral D C := Algebra.IsInvariant.isIntegral D C G
  obtain ⟨𝔫, -, h𝔫, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔮 (⊥ : Ideal C)
    (Ideal.comap_bot_le_of_injective (algebraMap D C) hinj)
  have := h𝔫
  obtain ⟨hdom, hic⟩ := hN 𝔫
  have := hdom
  have := hic
  set Dq := Localization.AtPrime 𝔮
  set Cn := Localization.AtPrime 𝔫
  let ψ : Dq →+* Cn := Localization.localRingHom 𝔮 𝔫 (algebraMap D C) hcomap.symm
  have hψ : Function.Injective ψ := localRingHom_injective (G := G) hinj 𝔫 𝔮 hcomap.symm
  have hψa : ∀ z : D, ψ (algebraMap D Dq z) = algebraMap C Cn (algebraMap D C z) := fun z =>
    Localization.localRingHom_to_map _ _ _ _ z
  have hD : IsDomain Dq := hψ.isDomain ψ
  refine ⟨hD, ?_⟩
  let K := FractionRing Dq
  let L := FractionRing Cn
  rw [isIntegrallyClosed_iff K]
  intro x hx
  let g : Dq →+* L := (algebraMap Cn L).comp ψ
  have hg : Function.Injective g := (IsFractionRing.injective Cn L).comp hψ
  let f : K →+* L := IsFractionRing.lift hg
  have hf : ∀ z, f (algebraMap Dq K z) = algebraMap Cn L (ψ z) := fun z =>
    IsFractionRing.lift_algebraMap hg z
  have hfx : IsIntegral Cn (f x) := by
    obtain ⟨P, hPm, hP⟩ := hx
    refine ⟨P.map ψ, hPm.map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap Cn L).comp ψ = f.comp (algebraMap Dq K) := by
      ext z; exact (hf z).symm
    rw [this, ← Polynomial.hom_eval₂, hP, map_zero]
  obtain ⟨c, hc⟩ := (IsIntegrallyClosed.isIntegral_iff (R := Cn) (K := L)).1 hfx
  obtain ⟨α, β, hβ, rfl⟩ := IsFractionRing.div_surjective (A := Dq) x
  have hβ0 : β ≠ 0 := nonZeroDivisors.ne_zero hβ
  have hβK : algebraMap Dq K β ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap Dq K)]
    exact fun h => hβ0 (IsFractionRing.injective Dq K h)
  have hψβ : ψ β ≠ 0 := by
    rw [Ne, ← map_zero ψ]; exact fun h => hβ0 (hψ h)
  -- `ψ α = ψ β * c` in `C_𝔫`
  have hαβ : ψ α = ψ β * c := by
    apply IsFractionRing.injective Cn L
    have h1 : f (algebraMap Dq K α / algebraMap Dq K β) =
        algebraMap Cn L (ψ α) / algebraMap Cn L (ψ β) := by
      rw [map_div₀, hf, hf]
    have hne : algebraMap Cn L (ψ β) ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap Cn L)]
      exact fun h => hψβ (IsFractionRing.injective Cn L h)
    rw [map_mul, hc, h1, mul_div_cancel₀ _ hne]
  obtain ⟨⟨a, s⟩, hα⟩ := IsLocalization.surj 𝔮.primeCompl α
  obtain ⟨⟨b, t⟩, hβ'⟩ := IsLocalization.surj 𝔮.primeCompl β
  simp only at hα hβ'
  have hut : IsUnit (algebraMap D Dq t) := IsLocalization.map_units Dq t
  have hus : IsUnit (algebraMap D Dq s) := IsLocalization.map_units Dq s
  have hb : algebraMap C Cn (algebraMap D C b) ≠ 0 := by
    rw [← hψa, ← hβ']
    intro h
    rw [map_mul] at h
    rcases mul_eq_zero.1 h with h | h
    · exact hψβ h
    · exact (hut.map ψ).ne_zero h
  have hab : ∃ c' : Cn, algebraMap C Cn (algebraMap D C (a * t)) =
      algebraMap C Cn (algebraMap D C b) * c' := by
    refine ⟨c * ψ (algebraMap D Dq s), ?_⟩
    rw [← hψa, ← hψa]
    simp only [map_mul]
    rw [← hα, ← hβ']
    simp only [map_mul]
    rw [hαβ]
    ring
  obtain ⟨e, f', he, hef⟩ := dvd_of_dvd_atPrime (G := G) hinj 𝔫 (a * t) b hb hab
  have he' : e ∉ 𝔮 := by rw [← hcomap]; exact he
  have hes : (e * s : D) ∈ 𝔮.primeCompl := fun hmem =>
    (Ideal.IsPrime.mem_or_mem ‹_› hmem).elim he' s.2
  obtain ⟨u, hu⟩ := IsLocalization.map_units Dq (⟨e * s, hes⟩ : 𝔮.primeCompl)
  have key : α * algebraMap D Dq (e * s) = β * algebraMap D Dq f' := by
    apply hut.mul_right_cancel
    calc α * algebraMap D Dq (e * s) * algebraMap D Dq t
        = algebraMap D Dq e * (α * algebraMap D Dq s) * algebraMap D Dq t := by rw [map_mul]; ring
      _ = algebraMap D Dq (e * (a * t)) := by rw [hα, map_mul, map_mul]; ring
      _ = algebraMap D Dq (b * f') := by rw [hef]
      _ = β * algebraMap D Dq f' * algebraMap D Dq t := by rw [map_mul, ← hβ']; ring
  refine ⟨algebraMap D Dq f' * ↑u⁻¹, ?_⟩
  rw [eq_div_iff hβK, ← map_mul]
  congr 1
  calc algebraMap D Dq f' * ↑u⁻¹ * β = β * algebraMap D Dq f' * ↑u⁻¹ := by ring
    _ = α * algebraMap D Dq (e * s) * ↑u⁻¹ := by rw [key]
    _ = α := by
      have hu' : (↑u : Dq) = algebraMap D Dq (e * s) := hu
      rw [← hu', mul_assoc, Units.mul_inv, mul_one]

end Descent

/-! ## Field level -/

/-- Verbatim copy of `CurveSplit.RegularSmoothPerfect` (TailR; Stacks 00TV, `⇐`). -/
def RegularSmoothPerfect : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (S : Type) [CommRing S] [Algebra k S]
    [Algebra.FiniteType k S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime q) →
      ∃ g : S, g ∉ q ∧ Algebra.Smooth k (Localization.Away g)

/-- **Invariants of a smooth algebra of dimension `≤ 1` over a perfect field are smooth.** -/
theorem smooth_of_invariants_field (hRS : RegularSmoothPerfect) (k : Type) [Field k] [PerfectField k]
    (C : Type) [CommRing C] [Algebra k C] [Algebra.Smooth k C]
    (D : Type) [CommRing D] [Algebra k D] [Algebra.FiniteType k D]
    (φ : D →ₐ[k] C) (hφ : Function.Injective φ)
    (G : Type) [Group G] [Fintype G] [MulSemiringAction G C]
    (hfix : ∀ (g : G) (d : D), g • φ d = φ d)
    (hinv : ∀ c : C, (∀ g : G, g • c = c) → ∃ d, φ d = c)
    (hdim : ringKrullDim C ≤ 1) : Algebra.Smooth k D := by
  letI : Algebra D C := φ.toRingHom.toAlgebra
  have hφ' : Function.Injective (algebraMap D C) := hφ
  have : SMulCommClass G D C := ⟨fun g d c => by
    change g • (φ d * c) = φ d * (g • c)
    rw [MulSemiringAction.smul_mul, hfix]⟩
  have : Algebra.IsInvariant D C G := ⟨hinv⟩
  have : Algebra.IsIntegral D C := Algebra.IsInvariant.isIntegral D C G
  have hN : ∀ (𝔫 : Ideal C) [𝔫.IsPrime],
      IsDomain (Localization.AtPrime 𝔫) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔫) := fun 𝔫 _ =>
    ZInQ.Contrib.CloudW03NeronSurj.FLT.Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
      k C 𝔫 (Localization.AtPrime 𝔫)
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing k D
  have : Algebra.FinitePresentation k D := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hdimD : ringKrullDim D ≤ 1 := by
    rw [← ZInQ.Contrib.Dim.ringKrullDim_eq_of_isIntegral_of_injective (A := D) (B := C) hφ']
    exact hdim
  have hreg : ∀ (𝔮 : Ideal D) [𝔮.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔮) := by
    intro 𝔮 _
    obtain ⟨h1, h2⟩ := isDomain_isIntegrallyClosed_atPrime (G := G) hφ' hN 𝔮
    have hle : ringKrullDim (Localization.AtPrime 𝔮) ≤ 1 := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (Localization.AtPrime 𝔮)]
      exact (Ideal.height_le_ringKrullDim_of_isPrime).trans hdimD
    have : Ring.KrullDimLE 1 (Localization.AtPrime 𝔮) := by
      rw [Ring.krullDimLE_iff]; exact_mod_cast hle
    have : Ring.DimensionLEOne (Localization.AtPrime 𝔮) :=
      ⟨fun hp hpp => hpp.isMaximal_of_ne_bot hp⟩
    have : IsDedekindDomain (Localization.AtPrime 𝔮) := { }
    exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  have hloc : Algebra.smoothLocus k D = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨g, hg, hsm⟩ := hRS k D x.asIdeal (hreg x.asIdeal)
    exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth (f := g)).mpr hsm hg
  exact ⟨Algebra.smoothLocus_eq_univ_iff.mp hloc, inferInstance⟩

/-! ## Base change of invariants (Reynolds operator) -/

section BaseChange

open TensorProduct

variable (R : Type) [CommRing R] (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (ι : A →ₐ[R] B) (hι : Function.Injective ι)
  (G : Type) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G R B]
  (hfix : ∀ (g : G) (a : A), g • ι a = ι a)
  (hinv : ∀ b : B, (∀ g : G, g • b = b) → ∃ a, ι a = b)
  (hG : IsUnit (Fintype.card G : R))

/-- The Reynolds operator `b ↦ |G|⁻¹ Σ g • b`. -/
noncomputable def reynolds : B →ₗ[R] B :=
  (↑(hG.unit⁻¹) : R) • ∑ g : G, (MulSemiringAction.toAlgHom R B g).toLinearMap

theorem reynolds_apply (b : B) :
    reynolds R B G hG b = (↑(hG.unit⁻¹) : R) • ∑ g : G, g • b := by
  simp [reynolds, LinearMap.sum_apply]

theorem reynolds_invariant (b : B) (h : G) : h • reynolds R B G hG b = reynolds R B G hG b := by
  rw [reynolds_apply, smul_comm, Finset.smul_sum]
  congr 1
  simp_rw [← mul_smul]
  exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)

theorem reynolds_of_invariant (b : B) (hb : ∀ g : G, g • b = b) : reynolds R B G hG b = b := by
  rw [reynolds_apply]
  simp_rw [hb, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, hG.val_inv_mul, one_smul]

include hι hinv hfix in
/-- The retraction `r : B → A` with `ι ∘ r = reynolds`. -/
theorem exists_retraction : ∃ r : B →ₗ[R] A, (∀ b, ι (r b) = reynolds R B G hG b) ∧
    r.comp ι.toLinearMap = LinearMap.id := by
  let ιₗ := ι.toLinearMap
  let e := LinearEquiv.ofInjective ιₗ hι
  let ρ' : B →ₗ[R] LinearMap.range ιₗ := (reynolds R B G hG).codRestrict (LinearMap.range ιₗ)
    (fun b => by
      obtain ⟨a, ha⟩ := hinv _ (reynolds_invariant R B G hG b)
      exact ⟨a, ha⟩)
  refine ⟨e.symm.toLinearMap.comp ρ', fun b => ?_, ?_⟩
  · have h := LinearEquiv.ofInjective_apply (f := ιₗ) (h := hι) (e.symm (ρ' b))
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · ext a
    apply hι
    have h := LinearEquiv.ofInjective_apply (f := ιₗ) (h := hι) (e.symm (ρ' (ι a)))
    rw [LinearEquiv.apply_symm_apply] at h
    have h2 : (ρ' (ι a) : B) = ι a := by
      obtain ⟨a', ha'⟩ : ∃ a', ι a' = ι a := ⟨a, rfl⟩
      simp only [ρ', LinearMap.codRestrict_apply]
      exact reynolds_of_invariant R B G hG _ (fun g => hfix g a)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
    rw [← h2]
    exact h.symm

variable (k : Type) [CommRing k] [Algebra R k]

/-- `G` acting on `k ⊗[R] B` through the second factor. -/
noncomputable def tensorAut : G →* (k ⊗[R] B ≃ₐ[k] k ⊗[R] B) where
  toFun g := Algebra.TensorProduct.congr AlgEquiv.refl (MulSemiringAction.toAlgEquiv R B g)
  map_one' := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c b => simp
    | add x y hx hy => simp_all
  map_mul' g h := by
    ext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c b => simp [mul_smul]
    | add x y hx hy => simp_all

include hι hfix hinv hG in
/-- **Base change of invariants** (Reynolds operator): `k ⊗ A → k ⊗ B` is injective, lands in the invariants
of `G` (acting on the second factor) and its image is all the invariants. -/
theorem fibre_invariants :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k k) ι) ∧
    (∀ (g : G) (x : k ⊗[R] A), tensorAut R B G k g (Algebra.TensorProduct.map (AlgHom.id k k) ι x) =
      Algebra.TensorProduct.map (AlgHom.id k k) ι x) ∧
    (∀ x : k ⊗[R] B, (∀ g : G, tensorAut R B G k g x = x) →
      ∃ y, Algebra.TensorProduct.map (AlgHom.id k k) ι y = x) := by
  obtain ⟨r, hr, hri⟩ := exists_retraction R A B ι hι G hfix hinv hG
  set φ : k ⊗[R] A →ₐ[k] k ⊗[R] B := Algebra.TensorProduct.map (AlgHom.id k k) ι
  letI : MulSemiringAction G (k ⊗[R] B) := MulSemiringAction.compHom _ (tensorAut R B G k)
  have hsmul : ∀ (g : G) (c : k) (b : B), g • (c ⊗ₜ[R] b) = c ⊗ₜ[R] (g • b) := fun _ _ _ => rfl
  let rk : k ⊗[R] B →ₗ[k] k ⊗[R] A := LinearMap.baseChange k r
  have hφinj : Function.Injective φ := by
    refine Function.LeftInverse.injective (g := rk) (fun x => ?_)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c a =>
      simp only [φ, rk, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, LinearMap.baseChange_tmul]
      congr 1
      exact LinearMap.congr_fun hri a
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hfix' : ∀ (g : G) (x : k ⊗[R] A), g • φ x = φ x := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]
    | tmul c a =>
      simp only [φ, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
      rw [hsmul, hfix]
    | add x y hx hy => rw [map_add, smul_add, hx, hy]
  have hinv' : ∀ x : k ⊗[R] B, (∀ g : G, g • x = x) → ∃ y, φ y = x := by
    intro x hx
    let ρk : k ⊗[R] B → k ⊗[R] B := fun x => (↑(hG.unit⁻¹) : R) • ∑ g : G, g • x
    have h1 : ρk x = x := by
      simp only [ρk]
      simp_rw [hx, Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul R, smul_smul, hG.val_inv_mul, one_smul]
    have h2 : ∀ y, ρk y = φ (rk y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp [ρk]
      | tmul c b =>
        simp only [ρk, φ, rk, LinearMap.baseChange_tmul, Algebra.TensorProduct.map_tmul, AlgHom.coe_id,
          id_eq, hsmul]
        rw [← TensorProduct.tmul_sum, ← TensorProduct.tmul_smul, hr, reynolds_apply]
      | add y z hy hz =>
        simp only [ρk] at hy hz ⊢
        rw [map_add, map_add, ← hy, ← hz]
        simp only [smul_add, Finset.sum_add_distrib]
    exact ⟨rk x, (h2 x).symm.trans h1⟩
  exact ⟨hφinj, hfix', hinv'⟩

include hι hfix hinv hG in
/-- The fibres of `A` and of `B` have the same dimension. -/
theorem ringKrullDim_fibre_eq :
    ringKrullDim (k ⊗[R] A) = ringKrullDim (k ⊗[R] B) := by
  obtain ⟨hφinj, hfix', hinv'⟩ := fibre_invariants R A B ι hι G hfix hinv hG k
  letI : MulSemiringAction G (k ⊗[R] B) := MulSemiringAction.compHom _ (tensorAut R B G k)
  letI : Algebra (k ⊗[R] A) (k ⊗[R] B) := (Algebra.TensorProduct.map (AlgHom.id k k) ι).toRingHom.toAlgebra
  have : Algebra.IsInvariant (k ⊗[R] A) (k ⊗[R] B) G := ⟨hinv'⟩
  have : Algebra.IsIntegral (k ⊗[R] A) (k ⊗[R] B) := Algebra.IsInvariant.isIntegral _ _ G
  exact (ZInQ.Contrib.Dim.ringKrullDim_eq_of_isIntegral_of_injective (A := k ⊗[R] A) (B := k ⊗[R] B)
    hφinj).symm

include hι hfix hinv hG in
/-- **Invariants of a smooth algebra with fibres of dimension `≤ 1`, by a group of invertible order, are
smooth**, if the residue fields of the (noetherian) base are perfect. -/
theorem smooth_of_invariants (hRS : RegularSmoothPerfect) [IsNoetherianRing R] [Algebra.Smooth R B]
    [Algebra.FiniteType R A]
    (hperf : ∀ (I : Ideal R) [I.IsPrime], PerfectField I.ResidueField)
    (hdim : ∀ (I : Ideal R) [I.IsPrime], ringKrullDim (I.Fiber B) ≤ 1) : Algebra.Smooth R A := by
  obtain ⟨r, hr, hri⟩ := exists_retraction R A B ι hι G hfix hinv hG
  have : Module.Flat R A := Module.Flat.of_retract ι.toLinearMap r hri
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  refine Algebra.Smooth.of_formallySmooth_fiber (fun I _ => ?_)
  have := hperf I
  set k := I.ResidueField
  obtain ⟨hφinj, hfix', hinv'⟩ := fibre_invariants R A B ι hι G hfix hinv hG k
  letI : MulSemiringAction G (k ⊗[R] B) := MulSemiringAction.compHom _ (tensorAut R B G k)
  have := smooth_of_invariants_field hRS k (k ⊗[R] B) (k ⊗[R] A) _ hφinj G hfix' hinv' (hdim I)
  infer_instance

end BaseChange

end P1Quot3
