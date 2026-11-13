import Mathlib

/-!
# Leaf T1 (`PkgI2.PurityBranchLocus`) reduced to finite algebras of dimension ≥ 2

Combines `T1Dim1.lean` (dimension one is glue) and `T1Finite.lean` (Zariski's Main Theorem reduces
to module-finite algebras); scratch files cannot import each other, so both are copied here.
`PkgI2.PurityBranchLocus` is copied verbatim from `ZInQKernel/HDecomp/Objects.lean`.

Main result: `TPurity2.purityBranchLocus_of_finiteGe2 :
  PurityBranchLocusFiniteGe2 → PkgI2.PurityBranchLocus`, where `PurityBranchLocusFiniteGe2` is
the leaf for module-finite `R → S` with `dim S_q = dim R_p ≥ 2` (no quasi-finiteness hypothesis).
-/

open IsLocalRing TensorProduct

universe u

namespace PkgI2

/-- Copied verbatim from `ZInQKernel/HDecomp/Objects.lean`. -/
def PurityBranchLocus : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    Algebra.QuasiFiniteAt R q →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    1 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

end PkgI2

namespace TPurity2

local notation "𝓀[" R "]" => ResidueField R


/-- Copied from `EtaleLocal.lean` (scratch files cannot import each other). -/
theorem isEtaleAt_of_isUnramifiedAt_of_flat_local {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] [q.LiesOver p] [Algebra.IsUnramifiedAt R q]
    (hflat : letI := Localization.AtPrime.algebraOfLiesOver p q;
      Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)) :
    Algebra.IsEtaleAt R q := by
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom
      (M := Algebra.algebraMapSubmonoid S p.primeCompl)
        (f := Algebra.ofId _ _) (by
      rintro ⟨_, x, hx, rfl⟩
      simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
        by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : Algebra.FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  have : Module.Flat Rp Sq := hflat
  have hU : Algebra.FormallyUnramified R Sq := ‹_›
  have : Algebra.FormallyUnramified Rp Sq := .of_restrictScalars R Rp Sq
  have : IsLocalHom (algebraMap Rp Sq) := by
    rw [Localization.AtPrime.algebraMap_eq p q]
    infer_instance
  have : Algebra.EssFiniteType R Sq := .comp R S Sq
  have : Algebra.EssFiniteType Rp Sq := .of_comp R Rp Sq
  have : Algebra.FormallyEtale 𝓀[Rp] (𝓀[Rp] ⊗[Rp] Sq) :=
    .of_formallyUnramified_of_field _ _
  have : Algebra.FormallySmooth Rp Sq :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor (R := Rp) (S := Sq) (P := Sp)
      (Algebra.algebraMapSubmonoid _ q.primeCompl)
  have : Algebra.FormallySmooth R Sq := .comp R Rp Sq
  exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨hU, ‹_›⟩

/-- A Noetherian local ring with principal maximal ideal: a prime `P ≠ 𝔪` is `⊥` (Nakayama). -/
theorem eq_bot_of_isPrime_of_ne_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hm : (maximalIdeal A).IsPrincipal) (P : Ideal A) [hP : P.IsPrime]
    (hne : P ≠ maximalIdeal A) : P = ⊥ := by
  obtain ⟨x, hx⟩ := hm
  have hxP : x ∉ P := by
    intro h
    apply hne
    refine le_antisymm (le_maximalIdeal hP.ne_top) ?_
    rw [hx, Submodule.span_le, Set.singleton_subset_iff]
    exact h
  have hle : P ≤ maximalIdeal A • P := by
    intro a ha
    have ham : a ∈ maximalIdeal A := le_maximalIdeal hP.ne_top ha
    rw [hx, Submodule.mem_span_singleton] at ham
    obtain ⟨c, rfl⟩ := ham
    have hc : c ∈ P := by
      rcases hP.mem_or_mem (show c * x ∈ P by simpa [smul_eq_mul] using ha) with h | h
      · exact h
      · exact absurd h hxP
    have hxm : x ∈ maximalIdeal A := hx ▸ Submodule.mem_span_singleton_self x
    rw [Ideal.smul_eq_mul, smul_eq_mul, mul_comm c x]
    exact Ideal.mul_mem_mul hxm hc
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal A) P
    (IsNoetherian.noetherian P) hle (by rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top])

/-- **T1, dimension one (GLUE, proved).** -/
theorem purity_dim_one (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))))
    (hdom : IsDomain (Localization.AtPrime q))
    (hqf : Algebra.QuasiFiniteAt R q)
    (hdim : ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))))
    (h1 : ringKrullDim (Localization.AtPrime q) = 1)
    (hunr : ∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 →
      Algebra.IsUnramifiedAt R q') :
    Algebra.IsEtaleAt R q := by
  set p : Ideal R := q.under R with hp
  have : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have hq1 : q.height = 1 := by
    have := IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)
    rw [h1] at this
    exact_mod_cast this.symm
  have : Algebra.IsUnramifiedAt R q := hunr q le_rfl hq1
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have hRp1 : ringKrullDim Rp = 1 := hdim.symm.trans h1
  have hreg' : IsRegularLocalRing Rp := hreg
  -- the maximal ideal of `R_p` is principal
  have hprin : (maximalIdeal Rp).IsPrincipal := by
    rw [← finrank_cotangentSpace_le_one_iff]
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace Rp).mp hreg'
    rw [hRp1] at h
    exact_mod_cast h.le
  -- `R_p → S_q` is injective
  let φ := algebraMap Rp Sq
  have hker : RingHom.ker φ = ⊥ := by
    have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    refine eq_bot_of_isPrime_of_ne_maximalIdeal hprin _ fun hm => ?_
    -- otherwise `⊥` and the maximal ideal of `S_q` both lie over `p`
    have hqf' : Algebra.QuasiFinite R Sq := hqf
    have hbot : (⊥ : Ideal Sq).IsPrime := Ideal.isPrime_bot
    have key : (⊥ : Ideal Sq).under R = (maximalIdeal Sq).under R := by
      rw [← Ideal.under_under (B := S) (maximalIdeal Sq),
        Localization.AtPrime.under_maximalIdeal, ← Ideal.under_under (B := Rp) (⊥ : Ideal Sq)]
      have : (⊥ : Ideal Sq).under Rp = RingHom.ker φ := rfl
      rw [this, hm, Localization.AtPrime.under_maximalIdeal]
    have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) (⊥ : Ideal Sq) (maximalIdeal Sq)
      bot_le key
    have hfield : IsField Sq := IsLocalRing.isField_iff_maximalIdeal_eq.mpr this.symm
    have := ringKrullDim_eq_zero_of_isField hfield
    rw [this] at h1
    exact absurd h1 (by decide)
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr hker
  have : IsDomain Rp := hinj.isDomain φ
  have hnf : ¬ IsField Rp := fun h => by
    rw [ringKrullDim_eq_zero_of_isField h] at hRp1
    exact absurd hRp1 (by decide)
  have : IsDedekindDomain Rp := ((IsDiscreteValuationRing.TFAE Rp hnf).out 5 3).mp hprin
  have : Module.IsTorsionFree Rp Sq := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r s hrs => ?_
    rw [Algebra.smul_def, mul_eq_zero] at hrs
    rcases hrs with h | h
    · exact Or.inl (hinj (by rw [h, map_zero]))
    · exact Or.inr h
  exact isEtaleAt_of_isUnramifiedAt_of_flat_local p q inferInstance


section Finite
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- From `S'[1/r] = S[1/r]`: every `x ∈ S` has `r^N x ∈ S'`. -/
theorem exists_pow_mul_mem (S' : Subalgebra R S) (r : S')
    (hbij : Function.Bijective (Localization.awayMap S'.val.toRingHom r)) (x : S) :
    ∃ N : ℕ, (r : S) ^ N * x ∈ S' := by
  obtain ⟨y, hy⟩ := hbij.2 (algebraMap S (Localization.Away (S'.val.toRingHom r)) x)
  obtain ⟨a, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers r) y
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk',
    IsLocalization.mk'_eq_iff_eq_mul, ← map_mul,
    IsLocalization.eq_iff_exists (Submonoid.powers (S'.val.toRingHom r))] at hy
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := hy
  refine ⟨k + n, ?_⟩
  have e : (r : S) ^ (k + n) * x = (r : S) ^ k * (a : S) := by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_val, map_pow] at hk
    rw [hk, pow_add]; ring
  rw [e]
  exact S'.mul_mem (S'.pow_mem r.2 k) a.2

/-- The localization of `S` at `P ∌ r` is the localization of `S'` at `P ∩ S'`. -/
theorem isLocalization_atPrime_of_pow (S' : Subalgebra R S) (r : S')
    (hpow : ∀ x : S, ∃ N : ℕ, (r : S) ^ N * x ∈ S')
    (P : Ideal S) [P.IsPrime] (hr : (r : S) ∉ P) :
    IsLocalization (P.comap (algebraMap S' S)).primeCompl (Localization.AtPrime P) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    exact IsLocalization.map_units (Localization.AtPrime P) (⟨(s : S), hs⟩ : P.primeCompl)
  · intro z
    obtain ⟨x, ⟨t, ht⟩, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl z
    obtain ⟨N, hN⟩ := hpow x
    obtain ⟨M, hM⟩ := hpow t
    have hden : (⟨(r : S) ^ N * ((r : S) ^ M * t), S'.mul_mem (S'.pow_mem r.2 N) hM⟩ : S') ∈
        (P.comap (algebraMap S' S)).primeCompl := by
      show (r : S) ^ N * ((r : S) ^ M * t) ∉ P
      intro h
      rcases Ideal.IsPrime.mem_or_mem inferInstance h with h | h
      · exact hr (Ideal.IsPrime.mem_of_pow_mem inferInstance N h)
      · rcases Ideal.IsPrime.mem_or_mem inferInstance h with h | h
        · exact hr (Ideal.IsPrime.mem_of_pow_mem inferInstance M h)
        · exact ht h
    refine ⟨⟨⟨(r : S) ^ N * x, hN⟩ * ⟨(r : S) ^ M, S'.pow_mem r.2 M⟩, ⟨_, hden⟩⟩, ?_⟩
    show IsLocalization.mk' (Localization.AtPrime P) x (⟨t, ht⟩ : P.primeCompl) *
        algebraMap S (Localization.AtPrime P) ((r : S) ^ N * ((r : S) ^ M * t)) =
      algebraMap S (Localization.AtPrime P) ((r : S) ^ N * x * (r : S) ^ M)
    have key := IsLocalization.mk'_spec (Localization.AtPrime P) x (⟨t, ht⟩ : P.primeCompl)
    simp only at key
    calc _ = (IsLocalization.mk' (Localization.AtPrime P) x (⟨t, ht⟩ : P.primeCompl) *
          algebraMap S (Localization.AtPrime P) t) *
          algebraMap S (Localization.AtPrime P) ((r : S) ^ N * (r : S) ^ M) := by
            rw [show (r : S) ^ N * ((r : S) ^ M * t) = t * ((r : S) ^ N * (r : S) ^ M) by ring,
              map_mul]; ring
      _ = _ := by rw [key, ← map_mul]; congr 1; ring
  · intro a b hab
    simp only [IsScalarTower.algebraMap_apply S' S (Localization.AtPrime P)] at hab
    obtain ⟨⟨s, hs⟩, hsab⟩ := IsLocalization.exists_of_eq (M := P.primeCompl) hab
    obtain ⟨M, hM⟩ := hpow s
    refine ⟨⟨⟨(r : S) ^ M * s, hM⟩, ?_⟩, ?_⟩
    · show (r : S) ^ M * s ∉ P
      intro h
      rcases Ideal.IsPrime.mem_or_mem inferInstance h with h | h
      · exact hr (Ideal.IsPrime.mem_of_pow_mem inferInstance M h)
      · exact hs h
    · apply Subtype.ext
      show (r : S) ^ M * s * a = (r : S) ^ M * s * b
      rw [mul_assoc, mul_assoc]
      exact congrArg (fun y => (r : S) ^ M * y) hsab

/-- `S'_{P ∩ S'} ≅ S_P` as `R`-algebras when `r ∉ P`. -/
noncomputable def locEquiv (S' : Subalgebra R S) (r : S')
    (hpow : ∀ x : S, ∃ N : ℕ, (r : S) ^ N * x ∈ S') (P : Ideal S) [P.IsPrime] (hr : (r : S) ∉ P) :
    Localization.AtPrime (P.comap (algebraMap S' S)) ≃ₐ[R] Localization.AtPrime P :=
  haveI := isLocalization_atPrime_of_pow S' r hpow P hr
  haveI : IsScalarTower R S' (Localization.AtPrime P) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  (IsLocalization.algEquiv (P.comap (algebraMap S' S)).primeCompl
    (Localization.AtPrime (P.comap (algebraMap S' S))) (Localization.AtPrime P)).restrictScalars R

theorem atPrime_congr_regular {A : Type u} [CommRing A] {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    (h : I = J) : IsRegularLocalRing (Localization.AtPrime I) ↔
      IsRegularLocalRing (Localization.AtPrime J) := by
  subst h; rfl

theorem atPrime_congr_dim {A : Type u} [CommRing A] {I J : Ideal A} [I.IsPrime] [J.IsPrime]
    (h : I = J) : ringKrullDim (Localization.AtPrime I) = ringKrullDim (Localization.AtPrime J) := by
  subst h; rfl

theorem atPrime_congr_unram {A : Type u} [CommRing A] [Algebra R A] {I J : Ideal A} [I.IsPrime]
    [J.IsPrime] (h : I = J) : Algebra.IsUnramifiedAt R I ↔ Algebra.IsUnramifiedAt R J := by
  subst h; rfl

/-- The leaf for module-finite algebras (quasi-finiteness is then automatic). -/
def PurityBranchLocusFinite : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Module.Finite R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    1 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

/-- **T1 reduces to finite `R`-algebras** (via Zariski's Main Theorem). -/
theorem purityBranchLocus_of_finite (h : PurityBranchLocusFinite.{u}) :
    PkgI2.PurityBranchLocus.{u} := by
  intro R S _ _ _ _ _ q _ hreg hdom hic hqf hdim h1 hunr
  obtain ⟨S', hfg, r, hrq, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := R) q
  have hpow := exists_pow_mul_mem S' r hbij
  have : Module.Finite R S' := Module.Finite.iff_fg.mpr hfg
  set q' : Ideal S' := q.comap (algebraMap S' S) with hq'
  let e := locEquiv S' r hpow q hrq
  have hcomap : q'.comap (algebraMap R S') = q.comap (algebraMap R S) := by
    ext x; rfl
  have hdomq : IsDomain (Localization.AtPrime q') :=
    Function.Injective.isDomain (e : Localization.AtPrime q' →+* Localization.AtPrime q)
      e.injective
  have hicq : IsIntegrallyClosed (Localization.AtPrime q') :=
    IsIntegrallyClosed.of_equiv e.symm.toRingEquiv
  have hdimq : ringKrullDim (Localization.AtPrime q') = ringKrullDim (Localization.AtPrime q) :=
    ringKrullDim_eq_of_ringEquiv e.toRingEquiv
  have key : Algebra.IsEtaleAt R q' := by
    refine h R S' q' ((atPrime_congr_regular hcomap).mpr hreg) hdomq hicq
      (by rw [hdimq, hdim, atPrime_congr_dim hcomap]) (by rw [hdimq]; exact h1) ?_
    intro q'' _ hle hht
    have hrq'' : r ∉ q'' := fun hr => hrq (hle hr)
    -- a prime `P` of `S` over `q''`
    let iso := RingEquiv.ofBijective (Localization.awayMap S'.val.toRingHom r) hbij
    have hunit : IsUnit (algebraMap S' (Localization.AtPrime q'') r) :=
      IsLocalization.map_units (Localization.AtPrime q'') (⟨r, hrq''⟩ : q''.primeCompl)
    let ψ : S →+* Localization.AtPrime q'' :=
      (Localization.awayLift (algebraMap S' (Localization.AtPrime q'')) r hunit).comp
        (iso.symm.toRingHom.comp (algebraMap S (Localization.Away (S'.val.toRingHom r))))
    have hψ : ∀ a : S', ψ (a : S) = algebraMap S' (Localization.AtPrime q'') a := by
      intro a
      have h1 : iso (algebraMap S' (Localization.Away r) a) =
          algebraMap S (Localization.Away (S'.val.toRingHom r)) (a : S) := by
        show Localization.awayMap S'.val.toRingHom r (algebraMap S' (Localization.Away r) a) = _
        rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
        rfl
      have h2 : iso.symm (algebraMap S (Localization.Away (S'.val.toRingHom r)) (a : S)) =
          algebraMap S' (Localization.Away r) a := by
        rw [← h1, RingEquiv.symm_apply_apply]
      show Localization.awayLift _ r hunit (iso.symm _) = _
      rw [h2, Localization.awayLift, IsLocalization.Away.lift_eq]
    let P : Ideal S := (maximalIdeal (Localization.AtPrime q'')).comap ψ
    have hPprime : P.IsPrime := Ideal.comap_isPrime ψ _
    have hPc : P.comap (algebraMap S' S) = q'' := by
      ext a
      show ψ (a : S) ∈ maximalIdeal _ ↔ a ∈ q''
      rw [hψ]
      exact IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q'') q'' a
    have hrP : (r : S) ∉ P := by
      show ψ (r : S) ∉ maximalIdeal _
      rw [hψ]
      exact fun hm => (IsLocalRing.mem_maximalIdeal _).mp hm hunit
    have hPle : P ≤ q := by
      intro x hx
      obtain ⟨N, hN⟩ := hpow x
      have : (⟨(r : S) ^ N * x, hN⟩ : S') ∈ q'' := by
        rw [← hPc]
        show ψ ((r : S) ^ N * x) ∈ maximalIdeal _
        rw [map_mul]
        exact Ideal.mul_mem_left _ _ hx
      have hq : (r : S) ^ N * x ∈ q := hle this
      rcases Ideal.IsPrime.mem_or_mem inferInstance hq with h' | h'
      · exact absurd (Ideal.IsPrime.mem_of_pow_mem inferInstance N h') hrq
      · exact h'
    let eP := locEquiv S' r hpow P hrP
    have hPht : P.height = 1 := by
      have a1 := IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
      have a2 := IsLocalization.AtPrime.ringKrullDim_eq_height (P.comap (algebraMap S' S))
        (Localization.AtPrime (P.comap (algebraMap S' S)))
      have a3 := ringKrullDim_eq_of_ringEquiv eP.toRingEquiv
      have a4 : (P.comap (algebraMap S' S)).height = 1 := by rw [hPc]; exact hht
      rw [a4] at a2
      rw [a2, a1] at a3
      exact_mod_cast a3.symm
    have := hunr P hPle hPht
    have hU : Algebra.FormallyUnramified R (Localization.AtPrime (P.comap (algebraMap S' S))) :=
      Algebra.FormallyUnramified.of_equiv eP.symm
    exact (atPrime_congr_unram hPc).mp hU
  exact Algebra.FormallyEtale.of_equiv e


end Finite

/-- **The narrowed leaf T1′**: Zariski–Nagata purity for a *finite* `R → S` in dimension `≥ 2`. -/
def PurityBranchLocusFiniteGe2 : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Module.Finite R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    2 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

theorem dim_eq_one_of_not_two_le {A : Type u} [CommRing A] (h1 : 1 ≤ ringKrullDim A)
    (h2 : ¬ 2 ≤ ringKrullDim A) : ringKrullDim A = 1 := by
  have hlt : ringKrullDim A < 2 := lt_of_not_ge h2
  have hne : ringKrullDim A ≠ ⊥ := by
    intro hb; rw [hb] at h1; exact absurd h1 (by decide)
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hn] at h1 hlt ⊢
  have h1' : (1 : ℕ∞) ≤ n := WithBot.coe_le_coe.mp h1
  have hlt' : n < (2 : ℕ∞) := WithBot.coe_lt_coe.mp hlt
  have : n = 1 := by
    cases n with
    | top => exact absurd hlt' (by decide)
    | coe k =>
      have : 1 ≤ k := by exact_mod_cast h1'
      have : k < 2 := by exact_mod_cast hlt'
      have : k = 1 := by omega
      subst this; rfl
  rw [this]; rfl

theorem finite_of_finiteGe2 (h : PurityBranchLocusFiniteGe2.{u}) : PurityBranchLocusFinite.{u} := by
  intro R S _ _ _ _ _ q _ hreg hdom hic hdim h1 hunr
  by_cases h2 : 2 ≤ ringKrullDim (Localization.AtPrime q)
  · exact h R S q hreg hdom hic hdim h2 hunr
  · have : Algebra.FiniteType R S := inferInstance
    have hqf : Algebra.QuasiFiniteAt R q := inferInstance
    exact purity_dim_one R S q hreg hdom hqf hdim (dim_eq_one_of_not_two_le h1 h2) hunr

/-- **T1 reduces to T1′** (finite, dimension `≥ 2`). -/
theorem purityBranchLocus_of_finiteGe2 (h : PurityBranchLocusFiniteGe2.{u}) :
    PkgI2.PurityBranchLocus.{u} :=
  purityBranchLocus_of_finite (finite_of_finiteGe2 h)

/-- Conversely T1 implies T1′ (finite ⇒ finite type and quasi-finite), so they are equivalent. -/
theorem finiteGe2_of_purityBranchLocus (h : PkgI2.PurityBranchLocus.{u}) :
    PurityBranchLocusFiniteGe2.{u} := by
  intro R S _ _ _ _ _ q _ hreg hdom hic hdim h2 hunr
  have : Algebra.FiniteType R S := inferInstance
  exact h R S q hreg hdom hic inferInstance hdim (le_trans (by decide) h2) hunr

end TPurity2

#print axioms TPurity2.purityBranchLocus_of_finiteGe2
#print axioms TPurity2.finiteGe2_of_purityBranchLocus
