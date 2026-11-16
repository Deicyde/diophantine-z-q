import ZInQKernel.Contrib.OneProof.SGRDirectNV

set_option linter.style.haveILetI false

noncomputable section

open Polynomial GlueDescent.B2Q
open HDec HDec.G0ModField HDec.PropTSRed HDec.PropTSGlue HDec.HeckeRestNV

namespace SGRDirect

/-- **Trivial vertical inertia gives an unramified vertical prime** (textbook Hilbert theory over the DVR
`ℤ[X]_{(p)}`; the residue extensions are separable since the degree is `< p`). -/
def VertInertiaTrivial' : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (p : ℕ), p.Prime → Module.finrank (RatFunc ℚ) E < p →
    (letI := intPolyAlg E
     ∀ q : Ideal (integralClosure ℤ[X] E), q.IsPrime → q.under ℤ[X] = vertPrime p →
       ∀ τ ∈ InertiaZ E q, τ = 1) →
    VertUnramWitness E p


/-- A finite extension of degree `< p` of a field in which `p = 0` is separable. -/
theorem isSeparable_of_finrank_lt {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) (hp : p.Prime) (hK : (p : K) = 0)
    (h : Module.finrank K L < p) : Algebra.IsSeparable K L := by
  have hchar : ringChar K = p := by
    have hd : ringChar K ∣ p := (ringChar.spec K p).mp hK
    rcases (Nat.dvd_prime hp).mp hd with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact h1
  constructor
  intro x
  have hint : IsIntegral K x := IsIntegral.of_finite K x
  have hirr := minpoly.irreducible hint
  show (minpoly K x).Separable
  rw [Polynomial.separable_iff_derivative_ne_zero hirr]
  intro hd
  set d := (minpoly K x).natDegree with hddef
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  have hdle : d ≤ Module.finrank K L := minpoly.natDegree_le x
  have hcoeff := congrArg (fun f => Polynomial.coeff f (d - 1)) hd
  simp only [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hcoeff
  rw [Nat.sub_add_cancel hd0] at hcoeff
  have hmon : (minpoly K x).coeff d = 1 := minpoly.monic hint
  rw [hmon, one_mul] at hcoeff
  have hcast : ((d - 1 : ℕ) : K) + 1 = (d : K) := by
    rw [← Nat.cast_succ]
    congr 1
    omega
  rw [hcast] at hcoeff
  have := (ringChar.spec K d).mp hcoeff
  rw [hchar] at this
  have := Nat.le_of_dvd hd0 this
  omega

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem vertInertiaTrivial' : VertInertiaTrivial' := by
  intro E _ _ _ _ _ _ p hp hdeg hI
  letI := intPolyAlg E
  letI := intRatAlg
  haveI : IsScalarTower ℤ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap ℚ[X] E (a.map (Int.castRingHom ℚ)) =
      algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) (a.map (Int.castRingHom ℚ)))
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E])
  haveI := isFractionRing_int
  haveI := vertPrime_isPrime p hp
  -- the DVR `R₀ = ℤ[X]_{(p)}`
  set R₀ := Localization.AtPrime (vertPrime p) with hR₀def
  letI : CommRing R₀ := inferInstanceAs (CommRing (Localization.AtPrime (vertPrime p)))
  have hunit : ∀ y : (vertPrime p).primeCompl, IsUnit (algebraMap ℤ[X] (RatFunc ℚ) y) := by
    intro y
    rw [isUnit_iff_ne_zero, Ne, map_eq_zero_iff _ (IsFractionRing.injective ℤ[X] (RatFunc ℚ))]
    intro h0
    exact y.2 (h0 ▸ Ideal.zero_mem _)
  letI : Algebra R₀ (RatFunc ℚ) := (IsLocalization.lift hunit).toAlgebra
  haveI : IsScalarTower ℤ[X] R₀ (RatFunc ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  haveI : IsFractionRing R₀ (RatFunc ℚ) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (vertPrime p).primeCompl R₀ (RatFunc ℚ)
  letI : Algebra R₀ E := ((algebraMap (RatFunc ℚ) E).comp (algebraMap R₀ (RatFunc ℚ))).toAlgebra
  haveI : IsScalarTower R₀ (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ℤ[X] R₀ E := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [IsScalarTower.algebraMap_apply ℤ[X] (RatFunc ℚ) E, IsScalarTower.algebraMap_apply ℤ[X] R₀ (RatFunc ℚ)]
    rfl)
  haveI : IsNoetherianRing R₀ := IsLocalization.isNoetherianRing (vertPrime p).primeCompl R₀ inferInstance
  haveI : IsIntegrallyClosed R₀ :=
    isIntegrallyClosed_of_isLocalization R₀ (vertPrime p).primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors _)
  haveI : IsDomain R₀ :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (vertPrime p))
  have hpmem : C (p : ℤ) ∈ vertPrime p := Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  have hp0 : algebraMap ℤ[X] R₀ (C (p : ℤ)) ≠ 0 := by
    intro h
    have := congrArg (algebraMap R₀ (RatFunc ℚ)) h
    rw [← IsScalarTower.algebraMap_apply, map_zero,
      map_eq_zero_iff _ (IsFractionRing.injective ℤ[X] (RatFunc ℚ))] at this
    exact hp.ne_zero (by exact_mod_cast (C_eq_zero.mp this))
  have hpm : algebraMap ℤ[X] R₀ (C (p : ℤ)) ∈ IsLocalRing.maximalIdeal R₀ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hpmem
  have hnf : ¬ IsField R₀ := by
    intro hf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.1 hf] at hpm
    exact hp0 (Ideal.mem_bot.1 hpm)
  have huniq : ∃! P : Ideal R₀, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal R₀, ⟨?_, inferInstance⟩, ?_⟩
    · intro h
      rw [h] at hpm
      exact hp0 (Ideal.mem_bot.1 hpm)
    · rintro P' ⟨hne, hprime⟩
      set Q' := P'.comap (algebraMap ℤ[X] R₀) with hQ'def
      haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
      have hQ'le : Q' ≤ vertPrime p := by
        intro b hb
        by_contra hbQ
        have hu : IsUnit (algebraMap ℤ[X] R₀ b) :=
          IsLocalization.map_units R₀ (⟨b, hbQ⟩ : (vertPrime p).primeCompl)
        exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hb hu)
      have hmc : Q'.map (algebraMap ℤ[X] R₀) = P' :=
        IsLocalization.map_under (vertPrime p).primeCompl R₀ P'
      have hQ'ne : Q' ≠ ⊥ := by
        intro h0
        apply hne
        rw [← hmc, h0, Ideal.map_bot]
      have hQ'eq : Q' = vertPrime p := eq_vertPrime hp Q' hQ'ne hQ'le
      rw [← hmc, hQ'eq]
      exact Localization.AtPrime.map_eq_maximalIdeal
  have key : (IsIntegrallyClosed R₀ ∧ ∃! P : Ideal R₀, P ≠ ⊥ ∧ P.IsPrime) ↔
      IsDiscreteValuationRing R₀ := (IsDiscreteValuationRing.TFAE R₀ hnf).out 4 1
  haveI : IsDiscreteValuationRing R₀ := key.mp ⟨inferInstance, huniq⟩
  -- `S₀`, the integral closure of `R₀` in `E`, and the Galois group
  have hR₀E : Function.Injective (algebraMap R₀ E) :=
    (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective R₀ (RatFunc ℚ))
  haveI : Module.IsTorsionFree R₀ E := Module.isTorsionFree_iff_algebraMap_injective.mpr hR₀E
  haveI : Module.Finite R₀ (integralClosure R₀ E) :=
    IsIntegralClosure.finite R₀ (RatFunc ℚ) E (integralClosure R₀ E)
  haveI : Algebra.IsAlgebraic R₀ E :=
    (IsFractionRing.comap_isAlgebraic_iff (K := RatFunc ℚ)).mpr inferInstance
  haveI : IsFractionRing (integralClosure R₀ E) E :=
    integralClosure.isFractionRing_of_algebraic (fun x hx => hR₀E (hx.trans (map_zero _).symm))
  haveI : SMulCommClass Gal(E/RatFunc ℚ) R₀ E := ⟨fun g a x => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply R₀ (RatFunc ℚ) E, AlgEquiv.commutes]⟩
  haveI hG : IsGaloisGroup Gal(E/RatFunc ℚ) R₀ (integralClosure R₀ E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/RatFunc ℚ) R₀ (integralClosure R₀ E) (RatFunc ℚ) E
  have hR₀S : Function.Injective (algebraMap R₀ (integralClosure R₀ E)) := by
    intro x y h
    apply hR₀E
    rw [IsScalarTower.algebraMap_apply R₀ (integralClosure R₀ E) E x,
      IsScalarTower.algebraMap_apply R₀ (integralClosure R₀ E) E y, h]
  haveI : FaithfulSMul R₀ (integralClosure R₀ E) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hR₀S
  haveI : Module.IsTorsionFree R₀ (integralClosure R₀ E) := inferInstance
  haveI : IsDedekindDomain R₀ := inferInstance
  haveI : Module.Flat R₀ (integralClosure R₀ E) := by
    refine (IsDedekindDomain.flat_iff_torsion_eq_bot (R := R₀) (M := integralClosure R₀ E)).mpr ?_
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_torsion_iff] at hx
    obtain ⟨a, ha⟩ := hx
    rw [Submodule.mem_bot]
    have ha' : ((a • x : integralClosure R₀ E) : E) = 0 := by rw [ha]; rfl
    rw [Submonoid.smul_def, Algebra.smul_def, Subalgebra.coe_mul] at ha'
    rcases mul_eq_zero.mp ha' with h0 | h0
    · exfalso
      have : ((algebraMap R₀ (integralClosure R₀ E) (a : R₀) : integralClosure R₀ E) : E) =
          algebraMap R₀ E (a : R₀) := rfl
      rw [this, map_eq_zero_iff _ hR₀E] at h0
      exact nonZeroDivisors.coe_ne_zero a h0
    · exact Subtype.ext h0
  haveI : IsDedekindDomain (integralClosure R₀ E) :=
    integralClosure.isDedekindDomain (A := R₀) (K := RatFunc ℚ) (L := E)
  -- a prime of `S₀` over the maximal ideal
  set m₀ := IsLocalRing.maximalIdeal R₀ with hm₀
  obtain ⟨q₂, hq₂, hq₂u⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := integralClosure R₀ E) m₀ (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      rw [hR₀S (hx.trans (map_zero _).symm)]
      exact Ideal.zero_mem _)
  haveI := hq₂
  haveI : q₂.LiesOver m₀ := ⟨hq₂u.symm⟩
  haveI : Fintype (m₀.primesOver (integralClosure R₀ E)) :=
    Set.Finite.fintype (IsDedekindDomain.primesOver_finite m₀ (integralClosure R₀ E))
  -- the residue extensions over `m₀` are separable (degree `< p`)
  have hcardG : Nat.card Gal(E/RatFunc ℚ) = Module.finrank (RatFunc ℚ) E :=
    IsGalois.card_aut_eq_finrank (RatFunc ℚ) E
  haveI : Algebra.HasSeparableResidueFieldsAt R₀ (integralClosure R₀ E) m₀ := by
    constructor
    intro q _ _
    letI := Localization.AtPrime.algebraOfLiesOver m₀ q
    have hf : q.inertiaDeg R₀ = Module.finrank m₀.ResidueField q.ResidueField :=
      Ideal.inertiaDeg_eq m₀ q
    have hfpos : 0 < q.inertiaDeg R₀ := Ideal.inertiaDeg_pos q R₀
    haveI : Module.Free m₀.ResidueField q.ResidueField := Module.Free.of_divisionRing _ _
    haveI : Module.Finite m₀.ResidueField q.ResidueField :=
      Module.finite_of_finrank_pos (hf ▸ hfpos)
    have hsum := Ideal.sum_ramification_inertia_eq_card m₀ (integralClosure R₀ E)
      (G := Gal(E/RatFunc ℚ))
    have hle : q.inertiaDeg R₀ ≤ Nat.card Gal(E/RatFunc ℚ) := by
      rw [← hsum]
      have hmem : (⟨q, ⟨‹_›, ‹_›⟩⟩ : m₀.primesOver (integralClosure R₀ E)) ∈ Finset.univ :=
        Finset.mem_univ _
      refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)
      exact Nat.le_mul_of_pos_left _ (Ideal.ramificationIdx_pos (R := R₀) (q := q))
    refine isSeparable_of_finrank_lt p hp ?_ ?_
    · have : algebraMap R₀ m₀.ResidueField (algebraMap ℤ[X] R₀ (C (p : ℤ))) = 0 :=
        Ideal.algebraMap_residueField_eq_zero.mpr hpm
      rw [← map_natCast (algebraMap R₀ m₀.ResidueField), ← this]
      congr 1
      rw [← map_natCast (algebraMap ℤ[X] R₀)]
      congr 1
    · omega
  -- `|I(q₂)| = e(q₂)`
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(E/RatFunc ℚ)) m₀ q₂
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx m₀ q₂ Gal(E/RatFunc ℚ)] at hcard
  -- the inclusion `B_ℤ → S₀` and the vertical prime `q₀ = q₂ ∩ B_ℤ`
  let ι : integralClosure ℤ[X] E →+* integralClosure R₀ E :=
    { toFun := fun x => ⟨(x : E), IsIntegral.tower_top (A := R₀) x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hιE : ∀ x, ((ι x : integralClosure R₀ E) : E) = (x : E) := fun _ => rfl
  set q₀ := q₂.comap ι with hq₀def
  haveI hq₀ : q₀.IsPrime := Ideal.comap_isPrime _ _
  have hcomp : ι.comp (algebraMap ℤ[X] (integralClosure ℤ[X] E)) =
      (algebraMap R₀ (integralClosure R₀ E)).comp (algebraMap ℤ[X] R₀) := by
    refine RingHom.ext fun x => Subtype.ext ?_
    show algebraMap ℤ[X] E x = algebraMap R₀ E (algebraMap ℤ[X] R₀ x)
    rw [← IsScalarTower.algebraMap_apply]
  have hq₀u : q₀.under ℤ[X] = vertPrime p := by
    rw [Ideal.under_def, hq₀def, Ideal.comap_comap, hcomp, ← Ideal.comap_comap]
    show Ideal.comap (algebraMap ℤ[X] R₀) (q₂.under R₀) = vertPrime p
    rw [hq₂u, hm₀]
    exact Localization.AtPrime.under_maximalIdeal
  -- the inertia of `q₂` is trivial
  have hItriv : Ideal.inertia Gal(E/RatFunc ℚ) q₂ = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    apply hI q₀ hq₀ hq₀u σ
    intro b
    refine ⟨⟨σ (b : E), ?_⟩, rfl, ?_⟩
    · exact (b.2).map ((σ : E ≃ₐ[RatFunc ℚ] E).toAlgHom.restrictScalars ℤ[X])
    · show ι (_ - b) ∈ q₂
      have h := hσ (ι b)
      convert h using 1
  have he1 : q₂.ramificationIdx R₀ = 1 := by
    rw [← hcard, hItriv, Subgroup.card_bot]
  -- `p` generates the maximal ideal of the local ring `S₀_{q₂}`
  letI : CommRing (Localization.AtPrime q₂) := inferInstance
  have hm : (q₂.under R₀).map (algebraMap R₀ (Localization.AtPrime q₂)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q₂) := by
    have h := he1
    rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
      Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
      IsLocalRing.isMaximal_iff] at h
    exact h
  set x : Localization.AtPrime q₂ :=
    algebraMap R₀ (Localization.AtPrime q₂) (algebraMap ℤ[X] R₀ (C (p : ℤ))) with hxdef
  have hm₀span : m₀ = Ideal.span {algebraMap ℤ[X] R₀ (C (p : ℤ))} := by
    have hv : vertPrime p = Ideal.span {C (p : ℤ)} := by
      unfold vertPrime
      rw [Ideal.map_span, Set.image_singleton]
    have hmap : Ideal.map (algebraMap ℤ[X] R₀) (vertPrime p) =
        Ideal.map (algebraMap ℤ[X] R₀) (Ideal.span {C (p : ℤ)}) := congrArg _ hv
    rw [hm₀, ← Localization.AtPrime.map_eq_maximalIdeal, hmap, Ideal.map_span, Set.image_singleton]
  have hmx : IsLocalRing.maximalIdeal (Localization.AtPrime q₂) = Ideal.span {x} := by
    rw [← hm, hq₂u, hm₀span, Ideal.map_span, Set.image_singleton]
  have hinjL : Function.Injective (algebraMap (integralClosure R₀ E) (Localization.AtPrime q₂)) :=
    haveI := IsLocalization.AtPrime.faithfulSMul (Localization.AtPrime q₂) (integralClosure R₀ E) q₂
    FaithfulSMul.algebraMap_injective _ _
  have hx0 : x ≠ 0 := by
    rw [hxdef, IsScalarTower.algebraMap_apply R₀ (integralClosure R₀ E) (Localization.AtPrime q₂)]
    intro h
    apply hp0
    apply hR₀S
    apply hinjL
    rw [h, map_zero, map_zero]
  have hxm2 : x ∉ (IsLocalRing.maximalIdeal (Localization.AtPrime q₂)) ^ 2 := by
    rw [hmx, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨r, hr⟩
    have h1 : x * ((1 : Localization.AtPrime q₂) - x * r) = 0 := by
      linear_combination hr
    rcases mul_eq_zero.mp h1 with h | h
    · exact hx0 h
    · have hu : IsUnit x := IsUnit.of_mul_eq_one (b := r) (by linear_combination -h)
      have hxm : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q₂) := by
        rw [hmx]; exact Ideal.mem_span_singleton_self x
      exact (IsLocalRing.mem_maximalIdeal x).mp hxm hu
  -- the local-ring witness
  refine vertUnramWitness_of_local E p hp ⟨q₀, Localization.AtPrime q₂, inferInstance, inferInstance,
    (algebraMap (integralClosure R₀ E) (Localization.AtPrime q₂)).comp ι, ?_, hq₀u, ?_⟩
  · rw [hq₀def, ← Ideal.comap_comap]
    congr 1
    exact (Localization.AtPrime.under_maximalIdeal).symm
  · have hψ : ((algebraMap (integralClosure R₀ E) (Localization.AtPrime q₂)).comp ι)
        (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C (p : ℤ))) = x := by
      rw [RingHom.comp_apply, ← RingHom.comp_apply ι, hcomp, RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply]
    rw [hψ]
    exact hxm2

end SGRDirect
#print axioms SGRDirect.vertInertiaTrivial'
