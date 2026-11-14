import Mathlib

open CategoryTheory

set_option linter.all false

noncomputable section

namespace CoarseFactorAG

section Alg

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]

/-- A maximal ideal of a finitely generated `ℚ`-algebra is the kernel of a map to `Ω`. -/
theorem exists_hom_ker_eq {R : Type*} [CommRing R] [Algebra ℚ R] [Algebra.FiniteType ℚ R]
    (m : Ideal R) [m.IsMaximal] : ∃ φ : R →+* Ω, RingHom.ker φ = m := by
  letI := Ideal.Quotient.field m
  have : Module.Finite ℚ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℚ (R ⧸ m)
  let τ : (R ⧸ m) →ₐ[ℚ] Ω := IsAlgClosed.lift
  refine ⟨τ.toRingHom.comp (Ideal.Quotient.mk m), ?_⟩
  rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp τ.toRingHom.injective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- Extension of a map `A → Ω` with kernel `m` to a map `B → Ω` with kernel a given maximal `M`
over `m` (`B` integral over `A`). -/
theorem exists_extend {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (m : Ideal A) [m.IsMaximal] (M : Ideal B) [M.IsMaximal]
    (hM : M.comap (algebraMap A B) = m) (ψ : A →+* Ω) (hψ : RingHom.ker ψ = m) :
    ∃ φ : B →+* Ω, RingHom.ker φ = M ∧ φ.comp (algebraMap A B) = ψ := by
  have : M.LiesOver m := ⟨hM.symm⟩
  letI := Ideal.Quotient.field m
  letI := Ideal.Quotient.field M
  let σ : A ⧸ m →+* Ω := Ideal.Quotient.lift m ψ (fun a ha => by rw [← RingHom.mem_ker, hψ]; exact ha)
  letI : Algebra (A ⧸ m) Ω := σ.toAlgebra
  have : Algebra.IsIntegral (A ⧸ m) (B ⧸ M) := inferInstance
  let τ : (B ⧸ M) →ₐ[A ⧸ m] Ω := IsAlgClosed.lift
  refine ⟨τ.toRingHom.comp (Ideal.Quotient.mk M), ?_, ?_⟩
  · rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp τ.toRingHom.injective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  · ext a
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    have : Ideal.Quotient.mk M (algebraMap A B a) =
        algebraMap (A ⧸ m) (B ⧸ M) (Ideal.Quotient.mk m a) := rfl
    rw [this, τ.commutes]
    rfl


/-! Copied verbatim from `scratch/curve-split/CurveBij.lean` (Part D). -/

/-- A localization at a smaller cofinal submonoid. -/
theorem isLocalization_of_cofinal {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M N : Submonoid R) (h₁ : M ≤ N) (h₂ : ∀ n ∈ N, ∃ m ∈ M, n ∣ m) [IsLocalization N S] :
    IsLocalization M S := by
  refine ⟨fun m => IsLocalization.map_units S ⟨m.1, h₁ m.2⟩, fun z => ?_, fun {x y} h => ?_⟩
  · obtain ⟨⟨b, n⟩, hz⟩ := IsLocalization.surj N z
    obtain ⟨m, hm, c, hc⟩ := h₂ n.1 n.2
    refine ⟨⟨b * c, ⟨m, hm⟩⟩, ?_⟩
    simp only at hz ⊢
    rw [hc, map_mul, map_mul, ← mul_assoc, hz]
  · obtain ⟨n, hn⟩ := (IsLocalization.eq_iff_exists N S).mp h
    obtain ⟨m, hm, c, hc⟩ := h₂ n.1 n.2
    refine ⟨⟨m, hm⟩, ?_⟩
    simp only
    rw [hc, mul_comm (n : R) c, mul_assoc, mul_assoc, hn]

/-- **A finite flat injective algebra over a domain, unramified at a prime `q` alone over `p` with
trivial residue extension, is an isomorphism.** -/
theorem bijective_of_unramifiedAt {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [Module.Finite A B] [Module.Flat A B]
    (hinj : Function.Injective (algebraMap A B)) (p : Ideal A) [p.IsPrime] (q : Ideal B)
    [q.IsPrime] [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q)]
    (huniq : p.primesOver B = {q}) [Algebra.IsUnramifiedAt A q]
    (hres : Function.Surjective (algebraMap p.ResidueField q.ResidueField)) :
    Function.Bijective (algebraMap A B) := by
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have hinj' := Localization.localRingHom_injective_of_primesOver_eq_singleton huniq
  have hsurj' := Localization.localRingHom_surjective_of_primesOver_eq_singleton huniq hres
  have hbij : Function.Bijective
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [Localization.AtPrime.algebraMap_eq]; exact ⟨hinj', hsurj'⟩
  -- `B_q` is the localization of `B` at `p`
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl)
      (Localization.AtPrime q) := by
    refine isLocalization_of_cofinal _ q.primeCompl ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact fun h => ha ((Ideal.mem_of_liesOver q p a).mpr h)
    · intro n hn
      obtain ⟨r, hr, hdvd⟩ := Ideal.exists_notMem_dvd_algebraMap_of_primesOver_eq_singleton huniq n hn
      exact ⟨algebraMap A B r, ⟨r, hr, rfl⟩, hdvd⟩
  have hbc := IsLocalizedModule.isBaseChange p.primeCompl (Localization.AtPrime p)
    (IsScalarTower.toAlgHom A B (Localization.AtPrime q)).toLinearMap
  have hrk := Module.rankAtStalk_isBaseChange hbc (IsLocalRing.closedPoint (Localization.AtPrime p))
  have hcomap : (IsLocalRing.closedPoint (Localization.AtPrime p)).comap
      (algebraMap A (Localization.AtPrime p)) = ⟨p, inferInstance⟩ := by
    ext1
    exact Localization.AtPrime.under_maximalIdeal
  rw [hcomap] at hrk
  have e : Localization.AtPrime q ≃ₗ[Localization.AtPrime p] Localization.AtPrime p :=
    (LinearEquiv.ofBijective (Algebra.linearMap _ _) hbij).symm
  rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_self] at hrk
  apply Module.algebraMap_bijective_of_rankAtStalk
  ext P
  rw [Pi.one_apply]
  have e1 := Module.rankAtStalk_eq_of_le_of_finite_of_flat' B (bot_le : (⊥ : Ideal A) ≤ P.asIdeal)
  have e2 := Module.rankAtStalk_eq_of_le_of_finite_of_flat' B (bot_le : (⊥ : Ideal A) ≤ p)
  rw [← e1, e2]
  exact hrk.symm.trans (by simp)



/-- An algebra of fields of dimension `1` is bijective. -/
theorem bijective_of_finrank_eq_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    (h : Module.finrank K L = 1) : Function.Bijective (algebraMap K L) := by
  refine ⟨(algebraMap K L).injective, fun x => ?_⟩
  have htop : (⊤ : IntermediateField K L) = ⊥ := by
    rw [← IntermediateField.finrank_eq_one_iff, IntermediateField.finrank_top', h]
  have hx : x ∈ (⊥ : IntermediateField K L) := htop ▸ IntermediateField.mem_top
  exact IntermediateField.mem_bot.mp hx

/-- **Main algebraic lemma.** `A` a Dedekind domain finitely generated over `ℚ`, `B` a reduced finite
`A`-algebra such that `Spec B → Spec A` is bijective on `Ω`-points. Then `A → B` is an isomorphism. -/
theorem bijective_of_points {A B : Type} [CommRing A] [CommRing B] [IsDedekindDomain A]
    [Algebra ℚ A] [Algebra.FiniteType ℚ A] [Algebra A B] [Module.Finite A B] [IsReduced B]
    (hI : ∀ φ₁ φ₂ : B →+* Ω, φ₁.comp (algebraMap A B) = φ₂.comp (algebraMap A B) → φ₁ = φ₂)
    (hS : ∀ ψ : A →+* Ω, ∃ φ : B →+* Ω, φ.comp (algebraMap A B) = ψ) :
    Function.Bijective (algebraMap A B) := by
  letI : Algebra ℚ B := ((algebraMap A B).comp (algebraMap ℚ A)).toAlgebra
  haveI : IsScalarTower ℚ A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType A B := inferInstance
  haveI : Algebra.FiniteType ℚ B := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  haveI hJA : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℚ)
  haveI hJB : IsJacobsonRing B := isJacobsonRing_of_isIntegral (R := A)
  -- uniqueness of the maximal ideal over a maximal ideal
  have huniqM : ∀ M M' : Ideal B, M.IsMaximal → M'.IsMaximal →
      M.comap (algebraMap A B) = M'.comap (algebraMap A B) → M = M' := by
    intro M M' hM hM' e
    have hm : (M.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ (Algebra.IsIntegral.isIntegral) M
    obtain ⟨ψ, hψ⟩ := exists_hom_ker_eq (Ω := Ω) (M.comap (algebraMap A B))
    obtain ⟨φ, hφ, hφψ⟩ := exists_extend _ M rfl ψ hψ
    obtain ⟨φ', hφ', hφψ'⟩ := exists_extend _ M' e.symm ψ hψ
    rw [← hφ, ← hφ', hI φ φ' (hφψ.trans hφψ'.symm)]
  -- injectivity
  have hinj : Function.Injective (algebraMap A B) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    have hle : RingHom.ker (algebraMap A B) ≤ (⊥ : Ideal A).jacobson := by
      refine le_sInf fun J ⟨_, hJ⟩ => ?_
      obtain ⟨ψ, hψ⟩ := exists_hom_ker_eq (Ω := Ω) J
      obtain ⟨φ, hφ⟩ := hS ψ
      intro a ha
      rw [← hψ, RingHom.mem_ker, ← hφ, RingHom.comp_apply, (RingHom.mem_ker).mp ha, map_zero]
    rw [hJA.out Ideal.isRadical_bot_of_noZeroDivisors] at hle
    exact le_bot_iff.mp hle
  -- `B` is a domain
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  obtain ⟨Q0, -, hQ0, hQ0u⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (⊥ : Ideal A)
    (⊥ : Ideal B) (by
      rw [Ideal.under, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj])
  have hQ0le : Q0 ≤ (⊥ : Ideal B).jacobson := by
    refine le_sInf fun M ⟨_, hM⟩ => ?_
    have hm : (M.comap (algebraMap A B)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ (Algebra.IsIntegral.isIntegral) M
    obtain ⟨Q', hQ'0, hQ', hQ'u⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      (M.comap (algebraMap A B)) Q0 (by rw [hQ0u]; exact bot_le)
    have hQ'm : Q'.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (Algebra.IsIntegral.isIntegral) Q'
        (by rw [show Q'.comap (algebraMap A B) = Q'.under A from rfl, hQ'u]; exact hm)
    rw [huniqM M Q' hM hQ'm hQ'u.symm]
    exact hQ'0
  rw [hJB.out Ideal.isRadical_bot] at hQ0le
  have hQ0bot : Q0 = ⊥ := le_bot_iff.mp hQ0le
  haveI : (⊥ : Ideal B).IsPrime := hQ0bot ▸ hQ0
  haveI : IsDomain B := IsDomain.of_bot_isPrime B
  have : Module.Flat A B := inferInstance
  have : CharZero A := charZero_of_injective_algebraMap (algebraMap ℚ A).injective
  -- an unramified maximal ideal
  have hO := Algebra.isOpen_unramifiedLocus (R := A) (A := B)
  have hbot : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ Algebra.unramifiedLocus A B :=
    Algebra.isUnramifiedAt_bot
  have : JacobsonSpace (PrimeSpectrum B) := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.mp hJB
  obtain ⟨Q, hQO, hQc⟩ := nonempty_inter_closedPoints ⟨_, hbot⟩ hO.isLocallyClosed
  have hQmax : Q.asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal Q).mp hQc
  set q := Q.asIdeal with hqdef
  set p := q.comap (algebraMap A B) with hpdef
  have hpmax : p.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _ (Algebra.IsIntegral.isIntegral) q
  have : q.LiesOver p := ⟨rfl⟩
  have : Algebra.IsUnramifiedAt A q := hQO
  let _ := Localization.AtPrime.algebraOfLiesOver p q
  have huniq : p.primesOver B = {q} := by
    ext Q'
    constructor
    · rintro ⟨hQ'p, hQ'lo⟩
      have hQ'm : Q'.IsMaximal :=
        Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (Algebra.IsIntegral.isIntegral) Q'
          (by rw [show Q'.comap (algebraMap A B) = Q'.under A from rfl, ← hQ'lo.over]; exact hpmax)
      exact huniqM Q' q hQ'm hQmax (by rw [show Q'.comap (algebraMap A B) = Q'.under A from rfl,
        ← hQ'lo.over])
    · rintro rfl
      exact ⟨inferInstance, inferInstance⟩
  -- `κ(q) = κ(p)`
  have hres : Function.Surjective (algebraMap p.ResidueField q.ResidueField) := by
    obtain ⟨ψ, hψ⟩ := exists_hom_ker_eq (Ω := Ω) p
    let σ : p.ResidueField →+* Ω := Ideal.ResidueField.lift p ψ (by rw [hψ]) (by
      intro s hs
      simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
      intro h0
      exact hs (hψ ▸ (RingHom.mem_ker).mpr h0))
    letI : Algebra p.ResidueField Ω := σ.toAlgebra
    letI : Algebra ℚ p.ResidueField := ((algebraMap A _).comp (algebraMap ℚ A)).toAlgebra
    haveI : CharZero p.ResidueField :=
      charZero_of_injective_algebraMap (algebraMap ℚ p.ResidueField).injective
    have hcard := AlgHom.card p.ResidueField q.ResidueField Ω
    have hsub : Subsingleton (q.ResidueField →ₐ[p.ResidueField] Ω) := by
      refine ⟨fun τ₁ τ₂ => ?_⟩
      have key : ∀ τ : q.ResidueField →ₐ[p.ResidueField] Ω,
          ((τ : q.ResidueField →+* Ω).comp (algebraMap B q.ResidueField)).comp (algebraMap A B) =
            σ.comp (algebraMap A p.ResidueField) := by
        intro τ
        ext a
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
        rw [← IsScalarTower.algebraMap_apply A B q.ResidueField,
          IsScalarTower.algebraMap_apply A p.ResidueField q.ResidueField, τ.commutes]
        rfl
      have h := hI _ _ ((key τ₁).trans (key τ₂).symm)
      exact AlgHom.coe_ringHom_injective (Ideal.ResidueField.ringHom_ext h)
    have h1 : Module.finrank p.ResidueField q.ResidueField = 1 := by
      have hle : Fintype.card (q.ResidueField →ₐ[p.ResidueField] Ω) ≤ 1 :=
        Fintype.card_le_one_iff_subsingleton.mpr hsub
      have hpos := Module.finrank_pos (R := p.ResidueField) (M := q.ResidueField)
      omega
    exact (bijective_of_finrank_eq_one h1).2
  exact bijective_of_unramifiedAt hinj p q huniq hres

end Alg

end CoarseFactorAG
#print axioms CoarseFactorAG.bijective_of_points
