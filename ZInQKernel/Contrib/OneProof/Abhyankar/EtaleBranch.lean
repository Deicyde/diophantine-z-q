import ZInQKernel.Contrib.OneProof.Abhyankar.Defs

/-!
# abhyankar: `EtaleBranch` (branches of a finite étale cover of a regular surface germ)

At a maximal ideal `𝔓'` of a finite étale domain `S'` over a two-dimensional regular local ring `B` with
maximal ideal `(t, u)`, the local ring `C = S'_{𝔓'}` has maximal ideal `(t, u)C` (unramified), so `C/tC` is a
noetherian local ring with principal maximal ideal `(ū)`; if a prime `Q' ∋ t` of `S'` lies strictly inside
`𝔓'`, then `ū` is not nilpotent in `C/tC`, so `C/tC` is a DVR (Krull intersection), every prime `Q'' ∋ t`
strictly inside `𝔓'` has `Q''C = tC`, and `(S'/Q')_{𝔓'} = C/tC` is integrally closed.
-/

open IsLocalRing HDec

set_option linter.all false

noncomputable section

namespace Abhyankar

/-- A noetherian local ring with maximal ideal `(π)`, `π` not nilpotent, is a domain in which every nonzero
element is `π^n · unit` (copied, with the hypotheses adapted, from `CurveGlueCI.isDomain_of_dim_one`,
ZInQKernel/OneProof/H/TailG.lean). -/
theorem principal_local_structure {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {π : R}
    (hspan : maximalIdeal R = Ideal.span {π}) (hπ : ∀ n : ℕ, π ^ n ≠ 0) :
    IsDomain R ∧ ∀ a : R, a ≠ 0 → ∃ (n : ℕ) (u : R), IsUnit u ∧ a = π ^ n * u := by
  classical
  have hdec : ∀ a : R, a ≠ 0 → ∃ (n : ℕ) (u : R), IsUnit u ∧ a = π ^ n * u := by
    intro a ha
    have hex : ∃ k : ℕ, a ∉ maximalIdeal R ^ k := by
      by_contra! h
      apply ha
      have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
      rw [← Submodule.mem_bot R, ← this, Submodule.mem_iInf]
      exact h
    let k := Nat.find hex
    have hk : a ∉ maximalIdeal R ^ k := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      apply hk
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hmem : a ∈ maximalIdeal R ^ n := by
      have := Nat.find_min hex (show n < k by omega)
      push Not at this
      exact this
    rw [hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨u, hu⟩ := hmem
    refine ⟨n, u, ?_, by rw [← hu, mul_comm]⟩
    by_contra hu'
    have hum : u ∈ maximalIdeal R := (mem_maximalIdeal u).2 hu'
    rw [hspan, Ideal.mem_span_singleton'] at hum
    obtain ⟨w, hw⟩ := hum
    apply hk
    rw [hn, hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨w, by rw [← hu, ← hw]; ring⟩
  have : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨n, u, hu, rfl⟩ := hdec a hne.1
    obtain ⟨m, v, hv, rfl⟩ := hdec b hne.2
    have : π ^ (n + m) * (u * v) = 0 := by rw [← hab]; ring
    exact hπ (n + m) ((hu.mul hv).mul_left_eq_zero.mp this)
  exact ⟨NoZeroDivisors.to_isDomain R, hdec⟩

/-- **`EtaleBranch` is proved.** -/
theorem etaleBranch : EtaleBranch := by
  intro B S' _ _ _ _ _ _ hdim t u hm ht0 hét hfin hinj 𝔓' h𝔓' Q' hQ' htQ hQ𝔓 hQne
  classical
  haveI := hét
  haveI := hfin
  set C := Localization.AtPrime 𝔓' with hCdef
  have hunder : 𝔓'.under B = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under B 𝔓')
  haveI : IsLocalHom (algebraMap B C) := ⟨fun x hx => by
    rw [IsScalarTower.algebraMap_apply B S' C] at hx
    have h1 : algebraMap B S' x ∉ 𝔓' := (IsLocalization.AtPrime.isUnit_to_map_iff C 𝔓' _).mp hx
    by_contra hxu
    exact h1 (show x ∈ 𝔓'.under B by rw [hunder]; exact (mem_maximalIdeal x).mpr hxu)⟩
  haveI : Algebra.FormallyUnramified B C := Algebra.FormallyUnramified.comp B S' C
  haveI : Algebra.EssFiniteType B C := Algebra.EssFiniteType.comp B S' C
  set tC := algebraMap B C t with htC
  set uC := algebraMap B C u with huC
  have hmC : maximalIdeal C = Ideal.span {tC, uC} := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := B) (S := C), hm, Ideal.map_span,
      Set.image_pair]
  haveI : IsNoetherianRing S' := IsNoetherianRing.of_finite B S'
  -- primes `Q'' ∋ t` strictly inside `𝔓'`, localized
  have hdisj : ∀ Q'' : Ideal S', Q'' ≤ 𝔓' → Disjoint (𝔓'.primeCompl : Set S') Q'' := by
    intro Q'' h
    rw [Set.disjoint_left]
    intro x hx hxQ
    exact hx (h hxQ)
  have hloc : ∀ Q'' : Ideal S', Q''.IsPrime → Q'' ≤ 𝔓' → Q'' ≠ 𝔓' →
      (Q''.map (algebraMap S' C)).IsPrime ∧ Q''.map (algebraMap S' C) ≠ maximalIdeal C ∧
        (Q''.map (algebraMap S' C)).comap (algebraMap S' C) = Q'' := by
    intro Q'' hQ'' hle hne
    have hP := IsLocalization.isPrime_of_isPrime_disjoint 𝔓'.primeCompl C Q'' hQ'' (hdisj Q'' hle)
    have hc := IsLocalization.comap_map_of_isPrime_disjoint 𝔓'.primeCompl C hQ'' (hdisj Q'' hle)
    refine ⟨hP, ?_, hc⟩
    intro heq
    apply hne
    rw [← hc, heq, Localization.AtPrime.comap_maximalIdeal]
  -- `C/tC`
  set R := C ⧸ Ideal.span {tC} with hRdef
  have htQC : ∀ Q'' : Ideal S', algebraMap B S' t ∈ Q'' → tC ∈ Q''.map (algebraMap S' C) := by
    intro Q'' h
    rw [htC, IsScalarTower.algebraMap_apply B S' C]
    exact Ideal.mem_map_of_mem _ h
  obtain ⟨hQCp, hQCne, hQCc⟩ := hloc Q' hQ' hQ𝔓 hQne
  haveI : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr (by
    intro h
    apply hQCp.ne_top
    rw [eq_top_iff, ← h, Ideal.span_le, Set.singleton_subset_iff]
    exact htQC Q' htQ)
  haveI : IsLocalRing R := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  set uR := Ideal.Quotient.mk (Ideal.span {tC}) uC with huR
  have hmR : maximalIdeal R = Ideal.span {uR} := by
    have h0 : Ideal.Quotient.mk (Ideal.span {tC}) tC = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {tC}))
      Ideal.Quotient.mk_surjective, hmC, Ideal.map_span, Set.image_pair, h0, Ideal.span_insert_zero]
  have hQle : Ideal.span {tC} ≤ Q'.map (algebraMap S' C) :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (htQC Q' htQ))
  have hmax_of : ∀ J : Ideal C, J.IsPrime → tC ∈ J → uC ∈ J → J = maximalIdeal C := by
    intro J hJ ht hu
    apply le_antisymm (le_maximalIdeal hJ.ne_top)
    rw [hmC, Ideal.span_le]
    rintro x (rfl | rfl)
    · exact ht
    · exact hu
  have hπ : ∀ n : ℕ, uR ^ n ≠ 0 := by
    intro n hn
    have h1 : uC ^ n ∈ Ideal.span {tC} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
      exact hn
    exact hQCne (hmax_of _ hQCp (htQC Q' htQ) (hQCp.mem_of_pow_mem n (hQle h1)))
  obtain ⟨hdom, hdec⟩ := principal_local_structure hmR hπ
  haveI := hdom
  haveI : IsLocalHom (Ideal.Quotient.mk (Ideal.span {tC})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hkey : ∀ Q'' : Ideal S', Q''.IsPrime → algebraMap B S' t ∈ Q'' → Q'' ≤ 𝔓' → Q'' ≠ 𝔓' →
      Q''.map (algebraMap S' C) = Ideal.span {tC} := by
    intro Q'' hQ'' ht'' hle hne
    obtain ⟨hP, hPne, -⟩ := hloc Q'' hQ'' hle hne
    have hle' : Ideal.span {tC} ≤ Q''.map (algebraMap S' C) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (htQC Q'' ht''))
    refine le_antisymm ?_ hle'
    intro x hx
    by_contra hxt
    have hx0 : Ideal.Quotient.mk (Ideal.span {tC}) x ≠ 0 :=
      fun h => hxt (Ideal.Quotient.eq_zero_iff_mem.mp h)
    obtain ⟨n, v, hv, hxv⟩ := hdec _ hx0
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hw : IsUnit w := isUnit_of_map_unit (Ideal.Quotient.mk (Ideal.span {tC})) w hv
    have h1 : x - uC ^ n * w ∈ Ideal.span {tC} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, ← huR, ← hxv, sub_self]
    have h2 : uC ^ n * w ∈ Q''.map (algebraMap S' C) := by
      have := sub_mem hx (hle' h1)
      rwa [sub_sub_cancel] at this
    have h3 : uC ^ n ∈ Q''.map (algebraMap S' C) := (hP.mem_or_mem h2).resolve_right
      (fun h => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h hw))
    exact hPne (hmax_of _ hP (htQC Q'' ht'') (hP.mem_of_pow_mem n h3))
  refine ⟨fun Q'' hQ'' ht'' hle hne => ?_, ?_⟩
  · obtain ⟨-, -, hc''⟩ := hloc Q'' hQ'' hle hne
    rw [← hc'', ← hQCc, hkey Q'' hQ'' ht'' hle hne, hkey Q' hQ' htQ hQ𝔓 hQne]
  · intro F _ _ _ z hz
    have hQC : Q'.map (algebraMap S' C) = Ideal.span {tC} := hkey Q' hQ' htQ hQ𝔓 hQne
    -- the DVR `R`
    have hnf : ¬ IsField R := by
      intro hF
      have := (isField_iff_maximalIdeal_eq.mp hF)
      rw [hmR, Ideal.span_singleton_eq_bot] at this
      exact hπ 1 (by rw [pow_one]; exact this)
    haveI : IsDiscreteValuationRing R :=
      ((IsDiscreteValuationRing.TFAE R hnf).out 5 1).mp
        (show (maximalIdeal R).IsPrincipal from ⟨⟨uR, hmR⟩⟩)
    -- the map `C → F`
    let g : S' →+* F := (algebraMap (S' ⧸ Q') F).comp (Ideal.Quotient.mk Q')
    have hgu : ∀ y : 𝔓'.primeCompl, IsUnit (g y) := by
      intro y
      have hy : Ideal.Quotient.mk Q' (y : S') ≠ 0 := by
        intro h
        exact y.2 (hQ𝔓 (Ideal.Quotient.eq_zero_iff_mem.mp h))
      exact IsLocalization.map_units F (⟨_, mem_nonZeroDivisors_of_ne_zero hy⟩ :
        nonZeroDivisors (S' ⧸ Q'))
    let ψ : C →+* F := IsLocalization.lift (M := 𝔓'.primeCompl) hgu
    have hψ : ∀ x : S', ψ (algebraMap S' C x) = g x := fun x => IsLocalization.lift_eq hgu x
    have hψt : ∀ a ∈ Ideal.span {tC}, ψ a = 0 := by
      intro a ha
      rw [← hQC] at ha
      have hle : Q'.map (algebraMap S' C) ≤ RingHom.ker ψ := Ideal.map_le_iff_le_comap.mpr (by
        intro x hx
        show ψ (algebraMap S' C x) = 0
        rw [hψ]
        show algebraMap (S' ⧸ Q') F (Ideal.Quotient.mk Q' x) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero])
      exact (RingHom.mem_ker).mp (hle ha)
    let φ : R →+* F := Ideal.Quotient.lift (Ideal.span {tC}) ψ hψt
    letI : Algebra R F := φ.toAlgebra
    let θ : S' ⧸ Q' →+* R := Ideal.Quotient.lift Q'
      ((Ideal.Quotient.mk (Ideal.span {tC})).comp (algebraMap S' C)) (by
        intro a ha
        show Ideal.Quotient.mk (Ideal.span {tC}) (algebraMap S' C a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, ← hQC]
        exact Ideal.mem_map_of_mem _ ha)
    have hφθ : φ.comp θ = algebraMap (S' ⧸ Q') F := by
      apply Ideal.Quotient.ringHom_ext
      ext x
      show ψ (algebraMap S' C x) = _
      rw [hψ]
    -- every element of `R` is `mk (c / s)`
    have hrep : ∀ r : R, ∃ (c : S') (s : 𝔓'.primeCompl),
        r = Ideal.Quotient.mk (Ideal.span {tC}) (IsLocalization.mk' C c s) := by
      intro r
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔓'.primeCompl y
      exact ⟨c, s, rfl⟩
    have hφmk : ∀ (c : S') (s : 𝔓'.primeCompl),
        g s * φ (Ideal.Quotient.mk (Ideal.span {tC}) (IsLocalization.mk' C c s)) = g c := by
      intro c s
      show g s * ψ (IsLocalization.mk' C c s) = g c
      exact ((IsLocalization.lift_mk'_spec (M := 𝔓'.primeCompl) hgu c _ s).mp rfl).symm
    haveI : IsFractionRing R F := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨r, hr⟩
        obtain ⟨c, s, rfl⟩ := hrep r
        have hr0 := nonZeroDivisors.ne_zero hr
        have hc : Ideal.Quotient.mk Q' c ≠ 0 := by
          intro h
          apply hr0
          rw [Ideal.Quotient.eq_zero_iff_mem, ← hQC]
          have hcQ : c ∈ Q' := Ideal.Quotient.eq_zero_iff_mem.mp h
          rw [IsLocalization.mk'_eq_mul_mk'_one]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hcQ)
        have hgc : IsUnit (g c) := IsLocalization.map_units F
          (⟨_, mem_nonZeroDivisors_of_ne_zero hc⟩ : nonZeroDivisors (S' ⧸ Q'))
        have := hφmk c s
        rw [← this] at hgc
        exact isUnit_of_mul_isUnit_right hgc
      · intro w
        obtain ⟨⟨a, ⟨b, hb⟩⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (S' ⧸ Q')) w
        have hb0 : θ b ≠ 0 := by
          intro h
          have : algebraMap (S' ⧸ Q') F b = 0 := by rw [← hφθ, RingHom.comp_apply, h, map_zero]
          exact nonZeroDivisors.ne_zero hb
            ((IsFractionRing.injective (S' ⧸ Q') F) (by rw [this, map_zero]))
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
        have hc : c ∈ Q' := by
          have : algebraMap (S' ⧸ Q') F (Ideal.Quotient.mk Q' c) = 0 := h1.symm
          rw [← map_zero (algebraMap (S' ⧸ Q') F)] at this
          exact Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.injective (S' ⧸ Q') F this)
        apply hne'
        rw [Ideal.Quotient.eq_zero_iff_mem, ← hQC, IsLocalization.mk'_eq_mul_mk'_one]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hc)
    -- `z` is integral over `R`
    have hzR : IsIntegral R z := by
      obtain ⟨P, hPm, hP⟩ := hz
      refine ⟨P.map θ, hPm.map θ, ?_⟩
      rw [Polynomial.eval₂_map]
      show Polynomial.eval₂ (φ.comp θ) z P = 0
      rw [hφθ]
      exact hP
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzR
    obtain ⟨c, s, rfl⟩ := hrep r
    refine ⟨c, s, s.2, ?_⟩
    have := hφmk c s
    show g s * z = g c
    rw [← hr]
    exact this

end Abhyankar
