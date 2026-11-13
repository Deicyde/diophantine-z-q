import Mathlib

/-! # ts-hecke: `GenericFibreCount` (development file, Mathlib only)

A finite extension `E/ℚ(X)` with `B` the integral closure of `ℚ[X]` in `E`: some rational `t` has
at least `[E : ℚ(X)]` ring maps `B → Λ` (`Λ` algebraically closed of characteristic 0) sending `X`
to `t`. -/

open Polynomial

namespace GFC

/-- Ring maps to an algebraically closed field extend along integral algebras (lying over and
`IsAlgClosed.lift`). -/
theorem exists_extend {Λ : Type*} [Field Λ] [IsAlgClosed Λ] {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] (φ : R →+* Λ)
    (hker : RingHom.ker (algebraMap R S) ≤ RingHom.ker φ) :
    ∃ ψ : S →+* Λ, ψ.comp (algebraMap R S) = φ := by
  classical
  set p := RingHom.ker φ with hp
  haveI : p.IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal S)
    (by
      intro a ha
      exact hker ((Ideal.mem_comap.1 ha : algebraMap R S a ∈ (⊥ : Ideal S)) |>
        fun h => by simpa [RingHom.mem_ker] using h))
  haveI := hQ
  haveI : Q.LiesOver p := ⟨hQp.symm⟩
  let φ' : R ⧸ p →+* Λ := Ideal.Quotient.lift p φ (fun a ha => ha)
  letI : Algebra (R ⧸ p) Λ := φ'.toAlgebra
  haveI : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  haveI : IsDomain (S ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Module.IsTorsionFree (R ⧸ p) (S ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (R ⧸ p) Λ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    rintro ⟨a⟩ ⟨b⟩ hab
    apply Ideal.Quotient.eq.2
    change φ (a - b) = 0
    rw [map_sub]
    exact sub_eq_zero.2 hab
  haveI : Algebra.IsAlgebraic (R ⧸ p) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let L : (S ⧸ Q) →ₐ[R ⧸ p] Λ := IsAlgClosed.lift
  refine ⟨L.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have h1 := L.commutes (Ideal.Quotient.mk p a)
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at h1
  exact h1

/-- **`GenericFibreCount`, general form** (target field `Λ`; the value `t` avoids a given finite
set `S`). -/
theorem genericFibreCountAvoid (Λ : Type) [Field Λ] [IsAlgClosed Λ] [CharZero Λ]
    (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (S : Finset ℚ) :
    ∃ t : ℚ, t ∉ S ∧ ∃ s : Finset (integralClosure ℚ[X] E →+* Λ),
      Module.finrank (RatFunc ℚ) E ≤ s.card ∧
      ∀ ψ ∈ s, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ Λ t := by
  classical
  -- a primitive element, made integral
  obtain ⟨z, hz⟩ := Field.exists_primitive_element (RatFunc ℚ) E
  have hzalg : IsAlgebraic ℚ[X] z :=
    (IsFractionRing.isAlgebraic_iff ℚ[X] (RatFunc ℚ) E).2
      (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy0, hyint⟩ := hzalg.exists_integral_multiple
  set θ : E := y • z with hθ
  have hyF : algebraMap ℚ[X] (RatFunc ℚ) y ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).2 hy0
  have hθF : IntermediateField.adjoin (RatFunc ℚ) {θ} = ⊤ := by
    rw [eq_top_iff, ← hz, IntermediateField.adjoin_simple_le_iff]
    have hθ' : θ = algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) y) * z := by
      rw [hθ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
    have hz' : z = (algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) y))⁻¹ * θ := by
      rw [hθ', ← mul_assoc, inv_mul_cancel₀ ((_root_.map_ne_zero _).2 hyF), one_mul]
    rw [hz']
    exact IntermediateField.mul_mem _ (IntermediateField.inv_mem _
      (IntermediateField.algebraMap_mem _ _)) (IntermediateField.mem_adjoin_simple_self _ _)
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b h
    have h' := congrArg Subtype.val h
    change algebraMap ℚ[X] E a = algebraMap ℚ[X] E b at h'
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
      IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E b] at h'
    exact IsFractionRing.injective ℚ[X] (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h')
  haveI : Module.IsTorsionFree ℚ[X] (integralClosure ℚ[X] E) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 hinjB
  let θB : integralClosure ℚ[X] E := ⟨θ, hyint⟩
  have hθBint : IsIntegral ℚ[X] θB := integralClosure.isIntegral θB
  set f : ℚ[X][X] := minpoly ℚ[X] θB with hfdef
  have hfE : minpoly ℚ[X] θ = f := by
    rw [hfdef, ← minpoly.algebraMap_eq (Subtype.val_injective) θB]
    rfl
  have hfmonic : f.Monic := minpoly.monic hθBint
  have hfF : minpoly (RatFunc ℚ) θ = f.map (algebraMap ℚ[X] (RatFunc ℚ)) := by
    rw [← hfE]; exact minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc ℚ) hyint
  have hdeg : f.natDegree = Module.finrank (RatFunc ℚ) E := by
    have h1 := IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (R := RatFunc ℚ) θ)
    rw [hθF, IntermediateField.finrank_top', hfF, hfmonic.natDegree_map] at h1
    exact h1.symm
  -- separability, with denominators cleared
  have hsepF : (minpoly (RatFunc ℚ) θ).Separable := Algebra.IsSeparable.isSeparable (RatFunc ℚ) θ
  obtain ⟨a₀, b₀, hab₀⟩ := hsepF
  obtain ⟨c₁, hc₁, ha₁⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℚ[X]) a₀
  obtain ⟨c₂, hc₂, hb₁⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℚ[X]) b₀
  set a₁ := IsLocalization.integerNormalization (nonZeroDivisors ℚ[X]) a₀
  set b₁ := IsLocalization.integerNormalization (nonZeroDivisors ℚ[X]) b₀
  set D : ℚ[X] := c₁ * c₂ with hD
  have hD0 : D ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hc₁) (nonZeroDivisors.ne_zero hc₂)
  have hab : C c₂ * a₁ * f + C c₁ * b₁ * derivative f = C D := by
    apply Polynomial.map_injective _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
    rw [hfF, Polynomial.derivative_map] at hab₀
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, ha₁, hb₁]
    rw [Algebra.smul_def, Algebra.smul_def, Polynomial.algebraMap_apply,
      Polynomial.algebraMap_apply, hD, map_mul, Polynomial.C_mul]
    linear_combination (C (algebraMap ℚ[X] (RatFunc ℚ) c₁) * C (algebraMap ℚ[X] (RatFunc ℚ) c₂)) * hab₀
  -- a good rational value
  obtain ⟨t, ht, htS⟩ : ∃ t : ℚ, D.eval t ≠ 0 ∧ t ∉ S := by
    have hP0 : (∏ s ∈ S, (X - C s) : ℚ[X]) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun s _ => Polynomial.X_sub_C_ne_zero s
    obtain ⟨t, ht⟩ : ∃ t : ℚ, (D * ∏ s ∈ S, (X - C s)).eval t ≠ 0 := by
      by_contra h
      push Not at h
      exact mul_ne_zero hD0 hP0 (Polynomial.funext fun r => by simpa using h r)
    rw [Polynomial.eval_mul] at ht
    refine ⟨t, left_ne_zero_of_mul ht, fun htS => right_ne_zero_of_mul ht ?_⟩
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero htS (by simp)
  set ev : ℚ[X] →+* Λ := (algebraMap ℚ Λ).comp (Polynomial.evalRingHom t) with hev
  set g : Λ[X] := f.map ev with hg
  have hevD : ev D ≠ 0 := by
    simp only [hev, RingHom.comp_apply, Polynomial.coe_evalRingHom]
    exact (map_ne_zero_iff _ (algebraMap ℚ Λ).injective).2 ht
  have hgsep : g.Separable := by
    refine ⟨C (ev D)⁻¹ * (C c₂ * a₁).map ev, C (ev D)⁻¹ * (C c₁ * b₁).map ev, ?_⟩
    have := congrArg (Polynomial.map ev) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.derivative_map] at this
    rw [hg, Polynomial.derivative_map, mul_assoc, mul_assoc, ← mul_add]
    simp only [Polynomial.map_mul, Polynomial.map_C] at this ⊢
    rw [show (ev c₂ : Λ) = ev c₂ from rfl]
    calc C (ev D)⁻¹ * (C (ev c₂) * Polynomial.map ev a₁ * Polynomial.map ev f +
          C (ev c₁) * Polynomial.map ev b₁ * Polynomial.map ev (derivative f))
        = C (ev D)⁻¹ * C (ev D) := by rw [this]
      _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hevD, C_1]
  have hgdeg : g.natDegree = f.natDegree := hfmonic.natDegree_map ev
  have hroots : g.roots.toFinset.card = g.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hgsep),
      IsAlgClosed.card_roots_eq_natDegree]
  -- one ring map per root
  have hext : ∀ r ∈ g.roots, ∃ ψ : integralClosure ℚ[X] E →+* Λ,
      ψ θB = r ∧ ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ Λ t := by
    intro r hr
    letI : Algebra ℚ[X][X] (integralClosure ℚ[X] E) := (Polynomial.aeval θB).toRingHom.toAlgebra
    haveI : IsScalarTower ℚ[X] ℚ[X][X] (integralClosure ℚ[X] E) :=
      IsScalarTower.of_algebraMap_eq fun x => by
        change _ = Polynomial.aeval θB (algebraMap ℚ[X] ℚ[X][X] x)
        rw [Polynomial.algebraMap_eq, Polynomial.aeval_C]
    haveI : Algebra.IsIntegral ℚ[X][X] (integralClosure ℚ[X] E) :=
      Algebra.IsIntegral.tower_top ℚ[X]
    let φ : ℚ[X][X] →+* Λ := Polynomial.eval₂RingHom ev r
    have hker : RingHom.ker (algebraMap ℚ[X][X] (integralClosure ℚ[X] E)) ≤ RingHom.ker φ := by
      intro q hq
      have hq' : Polynomial.aeval θB q = 0 := hq
      obtain ⟨u, rfl⟩ := minpoly.isIntegrallyClosed_dvd hθBint hq'
      rw [RingHom.mem_ker, map_mul]
      have : φ (minpoly ℚ[X] θB) = 0 := by
        change Polynomial.eval₂ ev r f = 0
        rw [← Polynomial.eval_map, ← hg]
        exact (Polynomial.mem_roots'.1 hr).2
      rw [this, zero_mul]
    obtain ⟨ψ, hψ⟩ := GFC.exists_extend φ hker
    refine ⟨ψ, ?_, ?_⟩
    · have h1 := congrArg (fun h : ℚ[X][X] →+* Λ => h X) hψ
      simp only [RingHom.comp_apply] at h1
      have h2 : algebraMap ℚ[X][X] (integralClosure ℚ[X] E) X = θB := Polynomial.aeval_X θB
      rw [h2] at h1
      rw [h1]
      simp [φ]
    · have h1 := congrArg (fun h : ℚ[X][X] →+* Λ => h (C X)) hψ
      simp only [RingHom.comp_apply] at h1
      have h2 : algebraMap ℚ[X][X] (integralClosure ℚ[X] E) (C X) =
          algebraMap ℚ[X] (integralClosure ℚ[X] E) X := Polynomial.aeval_C θB X
      rw [h2] at h1
      rw [h1]
      simp [φ, hev]
  rcases isEmpty_or_nonempty (integralClosure ℚ[X] E →+* Λ) with hE | hne
  · have h0 : g.roots = 0 := Multiset.eq_zero_of_forall_notMem fun r hr =>
      hE.false (hext r hr).choose
    refine ⟨t, htS, ∅, ?_, by simp⟩
    rw [← hdeg, ← hgdeg, ← hroots, h0]
    simp
  choose! Ψ hΨ using hext
  refine ⟨t, htS, g.roots.toFinset.image Ψ, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, hroots, hgdeg, hdeg]
    intro r hr r' hr' h
    have h1 := (hΨ r (Multiset.mem_toFinset.1 hr)).1
    have h2 := (hΨ r' (Multiset.mem_toFinset.1 hr')).1
    rw [← h1, ← h2, h]
  · intro ψ hψ
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hψ
    exact (hΨ r (Multiset.mem_toFinset.1 hr)).2

/-- **`GenericFibreCount`, general form** (target field `Λ`). -/
theorem genericFibreCount (Λ : Type) [Field Λ] [IsAlgClosed Λ] [CharZero Λ]
    (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] :
    ∃ t : ℚ, ∃ s : Finset (integralClosure ℚ[X] E →+* Λ),
      Module.finrank (RatFunc ℚ) E ≤ s.card ∧
      ∀ ψ ∈ s, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ Λ t := by
  obtain ⟨t, -, hs⟩ := genericFibreCountAvoid Λ E ∅
  exact ⟨t, hs⟩

end GFC

#print axioms GFC.genericFibreCount
#print axioms GFC.genericFibreCountAvoid
