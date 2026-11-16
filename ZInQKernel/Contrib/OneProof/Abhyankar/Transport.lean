import ZInQKernel.Contrib.OneProof.Abhyankar.Defs

/-!
# abhyankar: `TameBranchNormal` from `TBNLocal` (localization at `m`)

`A = R_m`; the integral closure `S_A` of `A` in `L` is the localization of `S = R^L` at `R ∖ m`
(`TsKummer.intCl_isLocalization`); primes of `S` inside `𝔓` correspond to primes of `S_A` inside `𝔓S_A`, with
the same contraction to `R`, the same height (`IsLocalization.height_under`) and the same ramification index
(`SGRDirect.NVLocal.ramificationIdx_map_localization`); `S_A/QS_A` is a localization of `S/Q`, so a fraction
field of `S/Q` is one of `S_A/QS_A`.
-/

open IsLocalRing HDec Polynomial

set_option linter.all false

noncomputable section

namespace Abhyankar

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
/-- **`TameBranchNormal` from `TBNLocal`** (compiled). -/
theorem tameBranchNormal_of_local (h : TBNLocal) : SGRDirect.NVLocal.TameBranchNormal := by
  intro R K L _ _ _ _ _ _ _ _ _ _ _ _ m _ hreg hdim f g hm hfp p hp hpm hdeg hunr 𝔓 h𝔓 h𝔓m Q hQ hQu
    hQ𝔓
  classical
  haveI := h𝔓.isPrime
  haveI := hQ
  have hRK : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hunitK : ∀ y : m.primeCompl, IsUnit (algebraMap R K y) := fun y =>
    isUnit_iff_ne_zero.mpr (fun h0 => y.2 (by
      have : (y : R) = 0 := hRK (by rw [h0, map_zero])
      rw [this]; exact m.zero_mem))
  letI : Algebra (Localization.AtPrime m) K :=
    (IsLocalization.lift (M := m.primeCompl) (S := Localization.AtPrime m) hunitK).toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime m) K :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunitK x).symm)
  haveI : IsFractionRing (Localization.AtPrime m) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl _ K
  letI : Algebra (Localization.AtPrime m) L :=
    ((algebraMap K L).comp (algebraMap (Localization.AtPrime m) K)).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime m) K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R (Localization.AtPrime m) L := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap R L x = algebraMap K L (algebraMap (Localization.AtPrime m) K
      (algebraMap R (Localization.AtPrime m) x))
    rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime m) K,
      ← IsScalarTower.algebraMap_apply R K L])
  have hP0 : ∀ x ∈ m.primeCompl, algebraMap R L x ≠ 0 := by
    intro x hx h0
    apply hx
    have : x = 0 := by
      rw [IsScalarTower.algebraMap_apply R K L] at h0
      exact hRK (by rw [(map_eq_zero_iff (algebraMap K L) (algebraMap K L).injective).mp h0, map_zero])
    rw [this]; exact m.zero_mem
  letI : Algebra (integralClosure R L) (integralClosure (Localization.AtPrime m) L) :=
    (TsKummer.intClIncl R (Localization.AtPrime m) L).toAlgebra
  have hh := TsKummer.intCl_isLocalization R (Localization.AtPrime m) L m.primeCompl hP0
  obtain ⟨hst1, hst2, hloc⟩ := hh
  -- notation-free abbreviations
  have hmA : maximalIdeal (Localization.AtPrime m) = m.map (algebraMap R (Localization.AtPrime m)) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hdisjR : ∀ J : Ideal R, J ≤ m → Disjoint (m.primeCompl : Set R) J := by
    intro J hJ
    rw [Set.disjoint_left]
    intro x hx hxJ
    exact hx (hJ hxJ)
  have hdisjS : ∀ J : Ideal (integralClosure R L), J.under R ≤ m →
      Disjoint ((Algebra.algebraMapSubmonoid (integralClosure R L) m.primeCompl :
        Submonoid (integralClosure R L)) : Set (integralClosure R L)) J := by
    intro J hJ
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrJ
    exact hr (hJ hrJ)
  have hprimeS : ∀ J : Ideal (integralClosure R L), J.IsPrime → J.under R ≤ m →
      (J.map (algebraMap (integralClosure R L) (integralClosure (Localization.AtPrime m) L))).IsPrime ∧
      (J.map (algebraMap (integralClosure R L) (integralClosure (Localization.AtPrime m) L))).comap
        (algebraMap (integralClosure R L) (integralClosure (Localization.AtPrime m) L)) = J := by
    intro J hJ hle
    exact ⟨IsLocalization.isPrime_of_isPrime_disjoint _ _ J hJ (hdisjS J hle),
      IsLocalization.comap_map_of_isPrime_disjoint _ _ hJ (hdisjS J hle)⟩
  have hunderA : ∀ J : Ideal (integralClosure R L), J.IsPrime → J.under R ≤ m →
      (J.map (algebraMap (integralClosure R L) (integralClosure (Localization.AtPrime m) L))).under
        (Localization.AtPrime m) = (J.under R).map (algebraMap R (Localization.AtPrime m)) := by
    intro J hJ hle
    rw [← IsLocalization.map_under m.primeCompl (Localization.AtPrime m)
      ((J.map (algebraMap (integralClosure R L) (integralClosure (Localization.AtPrime m) L))).under
        (Localization.AtPrime m))]
    congr 1
    rw [Ideal.under_under, ← Ideal.under_under (B := integralClosure R L)]
    congr 1
    exact (hprimeS J hJ hle).2
  have hfm : f ∈ m := by rw [hm]; exact Ideal.subset_span (by simp)
  have hspanf_le : Ideal.span {f} ≤ m := by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hfm
  have hQle : Q.under R ≤ m := by rw [hQu]; exact hspanf_le
  have h𝔓le : 𝔓.under R ≤ m := h𝔓m.le
  -- the local data
  set fA := algebraMap R (Localization.AtPrime m) f with hfA
  set gA := algebraMap R (Localization.AtPrime m) g with hgA
  have hmA' : maximalIdeal (Localization.AtPrime m) = Ideal.span {fA, gA} := by
    rw [hmA, congrArg (Ideal.map (algebraMap R (Localization.AtPrime m))) hm, Ideal.map_span,
      Set.image_pair]
  have hspanfA : Ideal.span {fA} = (Ideal.span {f}).map (algebraMap R (Localization.AtPrime m)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hfpA : (Ideal.span {fA}).IsPrime := by
    rw [hspanfA]
    exact IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl _ _ hfp (hdisjR _ hspanf_le)
  have hpA : ((p : ℕ) : Localization.AtPrime m) ∈ maximalIdeal (Localization.AtPrime m) := by
    rw [hmA, ← map_natCast (algebraMap R (Localization.AtPrime m))]
    exact Ideal.mem_map_of_mem _ hpm
  have hunrA : ∀ P : Ideal (Localization.AtPrime m), P.IsPrime → P.height = 1 → fA ∉ P → gA ∉ P →
      ∀ P' : Ideal (integralClosure (Localization.AtPrime m) L), P'.IsPrime →
        P'.under (Localization.AtPrime m) = P → P'.ramificationIdx (Localization.AtPrime m) = 1 := by
    intro P hP hP1 hfP hgP P' hP' hP'u
    haveI := hP'
    set P'₀ := P'.comap (algebraMap (integralClosure R L) (integralClosure (Localization.AtPrime m) L))
    haveI : P'₀.IsPrime := Ideal.comap_isPrime _ _
    have hP'₀u : P'₀.under R = P.under R := by
      rw [← hP'u, Ideal.under_under, Ideal.under_under]
    have hPle : P.under R ≤ m := by
      intro x hx
      by_contra hxm
      have hu : IsUnit (algebraMap R (Localization.AtPrime m) x) :=
        IsLocalization.map_units (Localization.AtPrime m) (⟨x, hxm⟩ : m.primeCompl)
      exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
    have h1 := hunr (P.under R) (Ideal.IsPrime.under R P) (by
        rw [IsLocalization.height_under m.primeCompl]; exact hP1) hPle
      (fun h => hfP h) (fun h => hgP h) P'₀ inferInstance hP'₀u
    have hmap : P'₀.map (algebraMap (integralClosure R L) (integralClosure (Localization.AtPrime m) L))
        = P' := IsLocalization.map_comap
          (Algebra.algebraMapSubmonoid (integralClosure R L) m.primeCompl) _ P'
    rw [← hmap, SGRDirect.NVLocal.ramificationIdx_map_localization (R := R) (S := integralClosure R L)
      (Rₘ := Localization.AtPrime m) (Sₘ := integralClosure (Localization.AtPrime m) L) m.primeCompl P'₀
      (by rw [hP'₀u]; exact hdisjR _ hPle)]
    exact h1
  obtain ⟨h𝔓Ap, h𝔓Ac⟩ := hprimeS 𝔓 inferInstance h𝔓le
  obtain ⟨hQAp, hQAc⟩ := hprimeS Q hQ hQle
  haveI : Algebra.IsIntegral (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) L) :=
    inferInstance
  have h𝔓Am : (𝔓.map (algebraMap (integralClosure R L)
      (integralClosure (Localization.AtPrime m) L))).IsMaximal := by
    haveI := h𝔓Ap
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Localization.AtPrime m)
    rw [hunderA 𝔓 inferInstance h𝔓le, h𝔓m, ← hmA]
    exact maximalIdeal.isMaximal _
  have hQAu : (Q.map (algebraMap (integralClosure R L) (integralClosure (Localization.AtPrime m) L))).under
      (Localization.AtPrime m) = Ideal.span {fA} := by
    rw [hunderA Q hQ hQle, hQu, hspanfA]
  obtain ⟨hUB, hN⟩ := h (Localization.AtPrime m) K L hdim fA gA hmA' hfpA p hp hpA hdeg hunrA _ h𝔓Am _
    hQAp hQAu (Ideal.map_mono hQ𝔓)
  refine ⟨fun Q' hQ' hQ'u hQ'𝔓 => ?_, ?_⟩
  · have hQ'le : Q'.under R ≤ m := by rw [hQ'u]; exact hspanf_le
    obtain ⟨hQ'Ap, hQ'Ac⟩ := hprimeS Q' hQ' hQ'le
    have := hUB _ hQ'Ap (by rw [hunderA Q' hQ' hQ'le, hQ'u, hspanfA]) (Ideal.map_mono hQ'𝔓)
    rw [← hQ'Ac, this, hQAc]
  · intro F _ _ _ z hz
    set ιS := algebraMap ↥(integralClosure R L) ↥(integralClosure (Localization.AtPrime m) L) with hιS
    set QA := Q.map ιS with hQA
    set MS := Algebra.algebraMapSubmonoid ↥(integralClosure R L) m.primeCompl with hMS
    have hMQ : ∀ y : MS, (y : ↥(integralClosure R L)) ∉ Q := by
      rintro ⟨_, r, hr, rfl⟩ hy
      exact hr (hQle hy)
    have hM𝔓 : ∀ y : MS, (y : ↥(integralClosure R L)) ∉ 𝔓 := by
      rintro ⟨_, r, hr, rfl⟩ hy
      exact hr (h𝔓le hy)
    let g : ↥(integralClosure R L) →+* F := (algebraMap (↥(integralClosure R L) ⧸ Q) F).comp (Ideal.Quotient.mk Q)
    have hgu : ∀ y : MS, IsUnit (g y) := by
      intro y
      have hy : Ideal.Quotient.mk Q (y : ↥(integralClosure R L)) ≠ 0 := fun h => hMQ y (Ideal.Quotient.eq_zero_iff_mem.mp h)
      exact IsLocalization.map_units F (⟨_, mem_nonZeroDivisors_of_ne_zero hy⟩ : nonZeroDivisors (↥(integralClosure R L) ⧸ Q))
    let ψ : ↥(integralClosure (Localization.AtPrime m) L) →+* F := IsLocalization.lift (M := MS) hgu
    have hψ : ∀ x : ↥(integralClosure R L), ψ (ιS x) = g x := fun x => IsLocalization.lift_eq hgu x
    have hψQ : ∀ a ∈ QA, ψ a = 0 := by
      intro a ha
      have hle : QA ≤ RingHom.ker ψ := Ideal.map_le_iff_le_comap.mpr (by
        intro x hx
        show ψ (ιS x) = 0
        rw [hψ]
        show algebraMap (↥(integralClosure R L) ⧸ Q) F (Ideal.Quotient.mk Q x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero])
      exact (RingHom.mem_ker).mp (hle ha)
    let φ : ↥(integralClosure (Localization.AtPrime m) L) ⧸ QA →+* F := Ideal.Quotient.lift QA ψ hψQ
    letI : Algebra (↥(integralClosure (Localization.AtPrime m) L) ⧸ QA) F := φ.toAlgebra
    let θ : ↥(integralClosure R L) ⧸ Q →+* ↥(integralClosure (Localization.AtPrime m) L) ⧸ QA := Ideal.quotientMap QA ιS Ideal.le_comap_map
    have hφθ : φ.comp θ = algebraMap (↥(integralClosure R L) ⧸ Q) F := by
      apply Ideal.Quotient.ringHom_ext
      ext x
      show ψ (ιS x) = _
      rw [hψ]
    have hrep : ∀ r : ↥(integralClosure (Localization.AtPrime m) L) ⧸ QA, ∃ (c : ↥(integralClosure R L)) (s : MS),
        r = Ideal.Quotient.mk QA (IsLocalization.mk' ↥(integralClosure (Localization.AtPrime m) L) c s) := by
      intro r
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective MS y
      exact ⟨c, s, rfl⟩
    have hφmk : ∀ (c : ↥(integralClosure R L)) (s : MS),
        g s * φ (Ideal.Quotient.mk QA (IsLocalization.mk' ↥(integralClosure (Localization.AtPrime m) L) c s)) = g c := by
      intro c s
      exact ((IsLocalization.lift_mk'_spec (M := MS) hgu c _ s).mp rfl).symm
    have hmem : ∀ (c : ↥(integralClosure R L)) (s : MS), c ∈ Q → IsLocalization.mk' ↥(integralClosure (Localization.AtPrime m) L) c s ∈ QA := by
      intro c s hc
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc)
    have hgc : ∀ c : ↥(integralClosure R L), g c = 0 → c ∈ Q := by
      intro c h
      have : algebraMap (↥(integralClosure R L) ⧸ Q) F (Ideal.Quotient.mk Q c) = algebraMap (↥(integralClosure R L) ⧸ Q) F 0 := by
        rw [map_zero]; exact h
      exact Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.injective (↥(integralClosure R L) ⧸ Q) F this)
    haveI : IsFractionRing (↥(integralClosure (Localization.AtPrime m) L) ⧸ QA) F := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨r, hr⟩
        obtain ⟨c, s, rfl⟩ := hrep r
        have hr0 := nonZeroDivisors.ne_zero hr
        have hc : Ideal.Quotient.mk Q c ≠ 0 := by
          intro h
          exact hr0 (Ideal.Quotient.eq_zero_iff_mem.mpr (hmem c s (Ideal.Quotient.eq_zero_iff_mem.mp h)))
        have hgc' : IsUnit (g c) := IsLocalization.map_units F
          (⟨_, mem_nonZeroDivisors_of_ne_zero hc⟩ : nonZeroDivisors (↥(integralClosure R L) ⧸ Q))
        rw [← hφmk c s] at hgc'
        exact isUnit_of_mul_isUnit_right hgc'
      · intro w
        obtain ⟨⟨a, ⟨b, hb⟩⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (↥(integralClosure R L) ⧸ Q)) w
        have hb0 : θ b ≠ 0 := by
          intro h
          have : algebraMap (↥(integralClosure R L) ⧸ Q) F b = 0 := by rw [← hφθ, RingHom.comp_apply, h, map_zero]
          exact nonZeroDivisors.ne_zero hb
            ((IsFractionRing.injective (↥(integralClosure R L) ⧸ Q) F) (by rw [this, map_zero]))
        refine ⟨⟨θ a, ⟨θ b, mem_nonZeroDivisors_of_ne_zero hb0⟩⟩, ?_⟩
        show w * φ (θ b) = φ (θ a)
        rw [← RingHom.comp_apply φ θ, ← RingHom.comp_apply φ θ, hφθ]
        exact hab
      · intro x y hxy
        refine ⟨1, ?_⟩
        simp only [OneMemClass.coe_one, one_mul]
        by_contra hne
        have hsub : φ (x - y) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hxy
        obtain ⟨c, s, hcs⟩ := hrep (x - y)
        have hne' : x - y ≠ 0 := sub_ne_zero.mpr hne
        rw [hcs] at hsub hne'
        have h1 := hφmk c s
        rw [hsub, mul_zero] at h1
        exact hne' (Ideal.Quotient.eq_zero_iff_mem.mpr (hmem c s (hgc c h1.symm)))
    have hzA : IsIntegral (↥(integralClosure (Localization.AtPrime m) L) ⧸ QA) z := by
      obtain ⟨P, hPm, hP⟩ := hz
      refine ⟨P.map θ, hPm.map θ, ?_⟩
      rw [Polynomial.eval₂_map]
      show Polynomial.eval₂ (φ.comp θ) z P = 0
      rw [hφθ]
      exact hP
    obtain ⟨a, s, hs, hsa⟩ := hN F z hzA
    obtain ⟨⟨a₀, m₁⟩, rfl⟩ := IsLocalization.mk'_surjective MS a
    obtain ⟨⟨s₀, m₂⟩, rfl⟩ := IsLocalization.mk'_surjective MS s
    have hs₀ : s₀ ∉ 𝔓 := by
      intro h
      apply hs
      show IsLocalization.mk' _ s₀ m₂ ∈ Ideal.map ιS 𝔓
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h)
    refine ⟨(m₂ : ↥(integralClosure R L)) * a₀, (m₁ : ↥(integralClosure R L)) * s₀, fun h => (h𝔓.isPrime.mem_or_mem h).elim (hM𝔓 m₁) hs₀, ?_⟩
    show g ((m₁ : ↥(integralClosure R L)) * s₀) * z = g ((m₂ : ↥(integralClosure R L)) * a₀)
    have e1 := hφmk s₀ m₂
    have e2 := hφmk a₀ m₁
    have hsa' : φ (Ideal.Quotient.mk QA (IsLocalization.mk' ↥(integralClosure (Localization.AtPrime m) L) s₀ m₂)) * z =
        φ (Ideal.Quotient.mk QA (IsLocalization.mk' ↥(integralClosure (Localization.AtPrime m) L) a₀ m₁)) := hsa
    rw [map_mul, map_mul, ← e1, ← e2]
    linear_combination (g m₂ * g m₁) * hsa'

end Abhyankar
