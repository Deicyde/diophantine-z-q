import ZInQKernel.Contrib.OneProof.Abhyankar.KummerUnramTame

/-!
# abhyankar: `KummerUnram` from its branch case

`kummerUnram_of_branch : KummerUnramBranch → KummerUnram`. The integral closure `S'` of `A'' = A[t, u]` in
`Ω = L(t, u)` is finite over `A''` (it has the carrier of the integral closure of `A`, finite over `A`), and at a
height-one prime `Q` of `S'`, with `P = Q ∩ A''` and `P₀ = P ∩ A` (both of height one, going down):

* if `f, g ∉ P₀`, `L/K` is unramified over the DVR `A_{P₀}` (the hypothesis of `TameBranchNormal`, with
  separable residue fields by `tame_at`), so `Ω/Frac(A''_P)` is unramified over `A''_P` by base change
  (`unram_of_baseChange`, from `TsKummer.unramBaseChange`);
* if `f ∈ P₀` this is `KummerUnramBranch`; if `g ∈ P₀` it is `KummerUnramBranch` with `f, t` and `g, u`
  exchanged (`(g)` is prime: `span_prime_of_pair`).
-/

open IsLocalRing HDec Polynomial

set_option linter.all false

noncomputable section

namespace Abhyankar

/-- In a two-dimensional noetherian local ring with maximal ideal `(x, y)`, `(y)` is prime (`A/(y)` has
principal maximal ideal `(x̄)` with `x̄` not nilpotent). -/
theorem span_prime_of_pair {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 2) {x y : R} (hm : maximalIdeal R = Ideal.span {x, y}) :
    (Ideal.span {y}).IsPrime := by
  have hy : y ∈ maximalIdeal R := by rw [hm]; exact Ideal.subset_span (by simp)
  have hne : Ideal.span {y} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact (mem_maximalIdeal y).mp hy
  haveI : Nontrivial (R ⧸ Ideal.span {y}) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (R ⧸ Ideal.span {y}) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmR : maximalIdeal (R ⧸ Ideal.span {y}) = Ideal.span {Ideal.Quotient.mk _ x} := by
    have h0 : Ideal.Quotient.mk (Ideal.span {y}) y = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {y}))
      Ideal.Quotient.mk_surjective, hm, Ideal.map_span, Set.image_pair, h0, Set.pair_comm,
      Ideal.span_insert_zero]
  have hπ : ∀ n : ℕ, (Ideal.Quotient.mk (Ideal.span {y}) x) ^ n ≠ 0 := by
    intro n hn
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hn
    -- every prime containing `y` contains `x`, so `m` is minimal over `(y)`
    have hmin : maximalIdeal R ∈ (Ideal.span {y}).minimalPrimes := by
      refine ⟨⟨inferInstance, by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hy⟩, ?_⟩
      intro q ⟨hq, hyq⟩ _
      have hxq : x ∈ q := hq.mem_of_pow_mem n (hyq hn)
      have hyq' : y ∈ q := hyq (Ideal.mem_span_singleton_self y)
      rw [hm, Ideal.span_le]
      rintro z (rfl | rfl)
      · exact hxq
      · exact hyq'
    have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {y}) _ hmin
    rw [TPurity3.height_maximalIdeal_of_dim2 hdim] at h1
    exact absurd h1 (by decide)
  obtain ⟨hdom, -⟩ := principal_local_structure hmR hπ
  exact (Ideal.Quotient.isDomain_iff_prime _).mp hdom

/-- **GLUE (step 2b: the branch case of `KummerUnram`, Abhyankar's lemma for DVRs).** In the setting of
`KummerUnram` (no hypothesis off `fg = 0` is needed), at a height-one prime `Q` of the integral closure of
`A'' = A[t, u]` in `Ω` whose contraction to `A` contains `f` (so it is `(f)`, and `Q ∩ A'' = (t)`), `Q` is
unramified over `A''`. Proof route: Abhyankar's lemma for DVRs (SGA 1 X 3.6, UNVERIFIED; the kernel's T2,
proved as `HDec.HSyn.t2_proved`) at `A_(f)` for `L(t)/L`, `t^N = f`, `e | N` (Galois), gives `L(t)`
unramified over `A[t]_(t)`; base change to `A''_(t)` (`TsKummer.unramBaseChange`). -/
def KummerUnramBranch : Prop :=
  ∀ (A K L Ω : Type) [CommRing A] [IsDomain A] [IsRegularLocalRing A] [Field K] [Field L] [Field Ω]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra L Ω] [Algebra K Ω] [Algebra A Ω]
    [IsScalarTower A K Ω] [IsScalarTower K L Ω] [FiniteDimensional L Ω], ringKrullDim A = 2 →
    ∀ f g : A, maximalIdeal A = Ideal.span {f, g} → (Ideal.span {f}).IsPrime →
    ∀ p : ℕ, p.Prime → (p : A) ∈ maximalIdeal A → Module.finrank K L < p →
    ∀ t u : Ω, t ^ Module.finrank K L = algebraMap A Ω f → u ^ Module.finrank K L = algebraMap A Ω g →
    IntermediateField.adjoin L {t, u} = ⊤ →
    ∀ A'' : Subalgebra A Ω, A'' = Algebra.adjoin A {t, u} →
      ∀ Q : Ideal (integralClosure A'' Ω), [Q.IsPrime] → Q.height = 1 → f ∈ (Q.under A'').under A →
        Algebra.IsUnramifiedAt A'' Q

theorem adjoin_eq_top_toAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E] (S : Set E)
    (h : IntermediateField.adjoin F S = ⊤) :
    letI := (algebraMap F E).toAlgebra; IntermediateField.adjoin F S = ⊤ := by
  have h1 := congrArg IntermediateField.toSubfield h
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield] at h1
  letI := (algebraMap F E).toAlgebra
  apply IntermediateField.toSubfield_injective
  rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield]
  exact h1

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
/-- **`KummerUnram` from `KummerUnramBranch`** (compiled). -/
theorem kummerUnram_of_branch (hBr : KummerUnramBranch) : KummerUnram := by
  intro A K L Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdim f g hm hfp p hp hpm hdeg hunr t u ht hu hadj
  classical
  obtain ⟨hreg, hdim'', hmax''⟩ := kummerBase A Ω (by
      rw [IsScalarTower.algebraMap_eq A K Ω]
      exact (algebraMap K Ω).injective.comp (IsFractionRing.injective A K)) hdim f g hm
    (Module.finrank K L) (Module.finrank K L) Module.finrank_pos Module.finrank_pos t u ht hu
  haveI := hreg
  haveI : IsIntegrallyClosed (Algebra.adjoin A ({t, u} : Set Ω)) :=
    TPurity3.isIntegrallyClosed_of_dim2 hdim''
  haveI : IsIntegrallyClosed A := TPurity3.isIntegrallyClosed_of_dim2 hdim
  have hAΩ : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective A K)
  have hA''Ω : Function.Injective (algebraMap (Algebra.adjoin A ({t, u} : Set Ω)) Ω) :=
    Subtype.val_injective
  have hN : 0 < Module.finrank K L := Module.finrank_pos
  -- separability of `Ω/K`
  have hNL : ((Module.finrank K L : ℕ) : L) ≠ 0 := by
    have hu' := (isUnit_natCast_of_not_dvd hp hpm (n := Module.finrank K L)
      (fun h => absurd (Nat.le_of_dvd hN h) (not_le.mpr hdeg))).map (algebraMap A L)
    rw [map_natCast] at hu'
    exact hu'.ne_zero
  have hf0 : algebraMap A L f ≠ 0 := by
    intro h
    have h1 := TPurity3.ne_zero_of_pair hm (TPurity3.height_maximalIdeal_of_dim2 hdim)
    apply h1
    have hAL : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    exact hAL (by rw [h, map_zero])
  have hg0 : algebraMap A L g ≠ 0 := by
    intro h
    have h1 := TPurity3.ne_zero_of_pair (z := g) (w := f) (by rw [hm, TPurity3.span_pair_comm])
      (TPurity3.height_maximalIdeal_of_dim2 hdim)
    apply h1
    have hAL : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    exact hAL (by rw [h, map_zero])
  haveI : IsScalarTower A L Ω := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [IsScalarTower.algebraMap_apply A K Ω, IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L Ω])
  have ht' : t ^ Module.finrank K L = algebraMap L Ω (algebraMap A L f) := by
    rw [ht, ← IsScalarTower.algebraMap_apply]
  have hu' : u ^ Module.finrank K L = algebraMap L Ω (algebraMap A L g) := by
    rw [hu, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsSeparable L Ω := by
    have h1 := IntermediateField.isSeparable_adjoin_pair_of_isSeparable
      (hx := isSeparable_of_pow hNL hf0 ht') (hy := isSeparable_of_pow hNL hg0 hu')
    rw [hadj] at h1
    exact Algebra.IsSeparable.of_algHom _ _ (IntermediateField.topEquiv (F := L) (E := Ω)).symm.toAlgHom
  haveI : Algebra.IsSeparable K Ω := Algebra.IsSeparable.trans K L Ω
  haveI : FiniteDimensional K Ω := Module.Finite.trans L Ω
  -- finiteness
  haveI hintA : Algebra.IsIntegral A (Algebra.adjoin A ({t, u} : Set Ω)) := Algebra.IsIntegral.adjoin (by
    rintro x (rfl | rfl)
    · exact ⟨_, monic_X_pow_sub_C (algebraMap A A f) hN.ne', by simp [ht]⟩
    · exact ⟨_, monic_X_pow_sub_C (algebraMap A A g) hN.ne', by simp [hu]⟩)
  haveI : Module.Finite A (integralClosure A Ω) := IsIntegralClosure.finite A K Ω (integralClosure A Ω)
  have hmem : ∀ x : Ω, x ∈ integralClosure A Ω ↔ x ∈ integralClosure (Algebra.adjoin A ({t, u} : Set Ω)) Ω := by
    intro x
    rw [mem_integralClosure_iff, mem_integralClosure_iff]
    exact ⟨fun h => h.tower_top, fun h => isIntegral_trans x h⟩
  let eA : integralClosure A Ω ≃ₗ[A] integralClosure (Algebra.adjoin A ({t, u} : Set Ω)) Ω :=
    { toFun := fun x => ⟨x.1, (hmem x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        apply Subtype.ext
        show r • (x : Ω) = _
        rfl }
  haveI : Module.Finite A (integralClosure (Algebra.adjoin A ({t, u} : Set Ω)) Ω) := Module.Finite.equiv eA
  haveI hfin : Module.Finite (Algebra.adjoin A ({t, u} : Set Ω))
      (integralClosure (Algebra.adjoin A ({t, u} : Set Ω)) Ω) :=
    Module.Finite.of_restrictScalars_finite A _ _
  refine ⟨hfin, ?_⟩
  intro Q _ hQ1
  haveI : IsNoetherianRing (integralClosure (Algebra.adjoin A ({t, u} : Set Ω)) Ω) :=
    IsNoetherianRing.of_finite (Algebra.adjoin A ({t, u} : Set Ω)) _
  haveI : FaithfulSMul (Algebra.adjoin A ({t, u} : Set Ω))
      (integralClosure (Algebra.adjoin A ({t, u} : Set Ω)) Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (fun x y h => Subtype.ext (congrArg
      (fun w : integralClosure (Algebra.adjoin A ({t, u} : Set Ω)) Ω => (w : Ω)) h))
  haveI : FaithfulSMul A (Algebra.adjoin A ({t, u} : Set Ω)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (fun x y h => hAΩ (congrArg Subtype.val h))
  have hP1 : (Q.under (Algebra.adjoin A ({t, u} : Set Ω))).height = 1 := height_under_eq_one Q hQ1
  have hP₀1 : ((Q.under (Algebra.adjoin A ({t, u} : Set Ω))).under A).height = 1 :=
    height_under_eq_one _ hP1
  by_cases hfP : f ∈ (Q.under (Algebra.adjoin A ({t, u} : Set Ω))).under A
  · exact hBr A K L Ω hdim f g hm hfp p hp hpm hdeg t u ht hu hadj _ rfl Q hQ1 hfP
  by_cases hgP : g ∈ (Q.under (Algebra.adjoin A ({t, u} : Set Ω))).under A
  · have hgp : (Ideal.span {g}).IsPrime := span_prime_of_pair hdim hm
    have hadj' : IntermediateField.adjoin L {u, t} = ⊤ := by rw [Set.pair_comm]; exact hadj
    exact hBr A K L Ω hdim g f (by rw [hm, TPurity3.span_pair_comm]) hgp p hp hpm hdeg u t hu ht
      hadj' _ (by rw [Set.pair_comm]) Q hQ1 hgP
  -- the generic case
  set P := Q.under (Algebra.adjoin A ({t, u} : Set Ω)) with hPdef
  set P₀ := P.under A with hP₀def
  haveI : P.IsPrime := Ideal.IsPrime.under _ Q
  haveI : P₀.IsPrime := Ideal.IsPrime.under _ P
  letI : Algebra (Localization.AtPrime P₀) K := IsLocalization.localizationAlgebraOfSubmonoidLe _ K
    P₀.primeCompl (nonZeroDivisors A) P₀.primeCompl_le_nonZeroDivisors
  haveI : IsScalarTower A (Localization.AtPrime P₀) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ K _ _ P₀.primeCompl_le_nonZeroDivisors
  haveI : IsFractionRing (Localization.AtPrime P₀) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P₀.primeCompl _ K
  letI : Algebra (Localization.AtPrime P₀) L :=
    ((algebraMap K L).comp (algebraMap (Localization.AtPrime P₀) K)).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime P₀) K L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A (Localization.AtPrime P₀) L := IsScalarTower.of_algebraMap_eq (fun x => by
    show algebraMap A L x = algebraMap K L (algebraMap (Localization.AtPrime P₀) K (algebraMap A _ x))
    rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime P₀) K,
      ← IsScalarTower.algebraMap_apply A K L])
  haveI : IsDomain (Localization.AtPrime P₀) :=
    IsLocalization.isDomain_localization P₀.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing (Localization.AtPrime P₀) := dvr_atPrime P₀ hP₀1
  have htame := tame_at p hp hpm hdeg P₀ (Localization.AtPrime P₀) (K := K) (L := L)
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hPL : ∀ x ∈ P₀.primeCompl, algebraMap A L x ≠ 0 := fun x hx h0 =>
    hx (by rw [hAL (h0.trans (map_zero _).symm)]; exact P₀.zero_mem)
  letI : Algebra (integralClosure A L) (integralClosure (Localization.AtPrime P₀) L) :=
    (TsKummer.intClIncl A _ L).toAlgebra
  obtain ⟨hL1, hL2, hL3⟩ := TsKummer.intCl_isLocalization A (Localization.AtPrime P₀) L P₀.primeCompl hPL
  have hL : ∀ (Q₀ : Ideal (integralClosure (Localization.AtPrime P₀) L)) [Q₀.IsPrime]
      [Q₀.LiesOver (maximalIdeal (Localization.AtPrime P₀))],
      Q₀.ramificationIdx (Localization.AtPrime P₀) = 1 ∧
      Algebra.IsSeparable (Localization.AtPrime P₀ ⧸ maximalIdeal (Localization.AtPrime P₀))
        (integralClosure (Localization.AtPrime P₀) L ⧸ Q₀) := by
    intro Q₀ _ _
    refine ⟨?_, (htame Q₀).2.2⟩
    set P0' := Q₀.comap (algebraMap (integralClosure A L) (integralClosure (Localization.AtPrime P₀) L))
    haveI : P0'.LiesOver P₀ :=
      IsLocalization.AtPrime.liesOver_comap_of_liesOver P₀ (Localization.AtPrime P₀) Q₀
    haveI : P0'.IsPrime := Ideal.IsPrime.comap _
    have hQ : Q₀ = P0'.map (algebraMap _ _) :=
      (IsLocalization.map_under (Algebra.algebraMapSubmonoid (integralClosure A L) P₀.primeCompl)
        (integralClosure (Localization.AtPrime P₀) L) Q₀).symm
    rw [hQ, IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx P₀ (Localization.AtPrime P₀)
      (integralClosure (Localization.AtPrime P₀) L) P0']
    exact hunr P₀ inferInstance hP₀1 hfP hgP P0' inferInstance
      (Ideal.LiesOver.over (P := P0') (p := P₀)).symm
  -- the DVR `T = A''_P`
  have hunitT : ∀ y : P.primeCompl, IsUnit (algebraMap (Algebra.adjoin A ({t, u} : Set Ω)) Ω y) :=
    fun y => isUnit_iff_ne_zero.mpr (fun h0 => y.2 (by
      rw [hA''Ω (h0.trans (map_zero _).symm)]; exact P.zero_mem))
  letI : Algebra (Localization.AtPrime P) Ω :=
    (IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P) hunitT).toAlgebra
  haveI : IsScalarTower (Algebra.adjoin A ({t, u} : Set Ω)) (Localization.AtPrime P) Ω :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunitT x).symm)
  haveI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) := dvr_atPrime P hP1
  let σ : Localization.AtPrime P₀ →+* Localization.AtPrime P :=
    Localization.localRingHom P₀ P (algebraMap A (Algebra.adjoin A ({t, u} : Set Ω))) rfl
  have hσ : ∀ x, algebraMap (Localization.AtPrime P) Ω (σ x) =
      algebraMap L Ω (algebraMap (Localization.AtPrime P₀) L x) := by
    have e : (algebraMap (Localization.AtPrime P) Ω).comp σ =
        (algebraMap L Ω).comp (algebraMap (Localization.AtPrime P₀) L) := by
      apply IsLocalization.ringHom_ext P₀.primeCompl
      ext a
      simp only [RingHom.comp_apply]
      show algebraMap _ Ω (Localization.localRingHom P₀ P
        (algebraMap A (Algebra.adjoin A ({t, u} : Set Ω))) rfl (algebraMap A _ a)) = _
      rw [Localization.localRingHom_to_map,
        ← IsScalarTower.algebraMap_apply (Algebra.adjoin A ({t, u} : Set Ω)) (Localization.AtPrime P) Ω,
        ← IsScalarTower.algebraMap_apply A (Algebra.adjoin A ({t, u} : Set Ω)) Ω,
        ← IsScalarTower.algebraMap_apply A (Localization.AtPrime P₀) L,
        ← IsScalarTower.algebraMap_apply A L Ω]
    exact fun x => RingHom.congr_fun e x
  have hgen0 : IntermediateField.adjoin L
      (Set.range (algebraMap (Algebra.adjoin A ({t, u} : Set Ω)) Ω)) = ⊤ := by
    rw [eq_top_iff, ← hadj]
    apply IntermediateField.adjoin.mono
    intro x hx
    rcases hx with hx | hx
    · exact ⟨⟨x, by rw [hx]; exact Algebra.subset_adjoin (by simp)⟩, rfl⟩
    · exact ⟨⟨x, by rw [Set.mem_singleton_iff.mp hx]; exact Algebra.subset_adjoin (by simp)⟩, rfl⟩
  exact unram_of_baseChange (A₀ := A) (K₀ := K) hA''Ω Q hP1 (Localization.AtPrime P)
    (Localization.AtPrime P₀) K L (algebraMap L Ω) σ hσ (adjoin_eq_top_toAlgebra _ hgen0) hL

end Abhyankar
