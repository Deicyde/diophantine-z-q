/-! ## assemble-port: ts-hecke (scratch/ts-hecke/), its own parts without the copies this file has (mk/mk_tshecke.py) -/

section CICopy

open CategoryTheory AlgebraicGeometry

namespace CIcopy

def ComponentIrreducible : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)), IsProper f →
    SmoothOfRelativeDimension 1 f → ∀ x : X, IsIrreducible (connectedComponent x)

/-! ## (CI) proved: components of a proper smooth curve are irreducible (task curve-glue)

Uses task infra-smooth-dim's `InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension` (local rings
at closed points have Krull dimension 1 and principal maximal ideal). -/

namespace CurveGlueCI

open CategoryTheory AlgebraicGeometry IsLocalRing

/-- **A Noetherian local ring of Krull dimension 1 with principal maximal ideal is a domain.**
(Krull intersection theorem: every nonzero element is `π^n · unit`; `π` is not nilpotent since the
dimension is positive.) -/
theorem isDomain_of_dim_one {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (hspan : (maximalIdeal R).spanFinrank = 1) : IsDomain R := by
  classical
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan'⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
  rw [hspan] at hs
  obtain ⟨π, rfl⟩ := Set.encard_eq_one.1 (by exact_mod_cast hs)
  -- `π` is not nilpotent
  have hπ : ∀ n : ℕ, π ^ n ≠ 0 := by
    intro n hn
    have hsub : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := by
      intro p
      refine le_antisymm (le_maximalIdeal p.2.ne_top) ?_
      rw [← hspan', Ideal.span_le, Set.singleton_subset_iff]
      exact p.2.mem_of_pow_mem n (by rw [hn]; exact p.asIdeal.zero_mem)
    have : Subsingleton (PrimeSpectrum R) :=
      ⟨fun p q => PrimeSpectrum.ext ((hsub p).trans (hsub q).symm)⟩
    have h0 : ringKrullDim R = 0 := Order.krullDim_eq_zero
    rw [hdim] at h0
    norm_num at h0
  -- every nonzero element is `π ^ n * unit`
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
    rw [← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨u, hu⟩ := hmem
    refine ⟨n, u, ?_, by rw [← hu, mul_comm]⟩
    by_contra hu'
    have hum : u ∈ maximalIdeal R := (mem_maximalIdeal u).2 hu'
    rw [← hspan', Ideal.mem_span_singleton'] at hum
    obtain ⟨w, hw⟩ := hum
    apply hk
    rw [hn, ← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨w, by rw [← hu, ← hw]; ring⟩
  have : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨n, u, hu, rfl⟩ := hdec a hne.1
    obtain ⟨m, v, hv, rfl⟩ := hdec b hne.2
    have : π ^ (n + m) * (u * v) = 0 := by rw [← hab]; ring
    exact hπ (n + m) ((hu.mul hv).mul_left_eq_zero.mp this)
  exact NoZeroDivisors.to_isDomain R

/-- **Two irreducible components meeting at a point with a domain stalk coincide.** -/
theorem irreducibleComponent_eq_of_isDomain_stalk {X : Scheme} {Z₁ Z₂ : Set X}
    (h₁ : Z₁ ∈ irreducibleComponents X) (h₂ : Z₂ ∈ irreducibleComponents X) {y : X}
    (hy₁ : y ∈ Z₁) (hy₂ : y ∈ Z₂) (hdom : IsDomain (X.presheaf.stalk y)) : Z₁ = Z₂ := by
  let G : Set X := Set.range (X.fromSpecStalk y)
  have hG : IsIrreducible G := by
    have : IrreducibleSpace (Spec (X.presheaf.stalk y)) := PrimeSpectrum.irreducibleSpace
    show IsIrreducible (Set.range (X.fromSpecStalk y))
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (X.fromSpecStalk y).continuous.continuousOn
  have key : ∀ Z ∈ irreducibleComponents X, y ∈ Z → Z = closure G := by
    intro Z hZ hyZ
    have hcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hgen := hZ.1.isGenericPoint_genericPoint hcl
    have hspec : hZ.1.genericPoint ⤳ y := by
      rw [specializes_iff_mem_closure, hgen.def]; exact hyZ
    have hmem : hZ.1.genericPoint ∈ G := by
      show _ ∈ Set.range (X.fromSpecStalk y)
      rw [Scheme.range_fromSpecStalk]; exact hspec
    have hsub : Z ⊆ closure G := by
      rw [← hgen.def]
      exact closure_mono (Set.singleton_subset_iff.2 hmem)
    exact (hZ.eq_of_subset hG.closure hsub)
  rw [key Z₁ h₁ hy₁, key Z₂ h₂ hy₂]

end CurveGlueCI

/-- **(CI), proved** (from infra-smooth-dim's stalk dimensions). -/
theorem componentIrreducible : ComponentIrreducible := by
  intro K _ X f hP hS x
  have : LocallyOfFiniteType f := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := { }
  have : SmoothOfRelativeDimension 1 f := hS
  -- stalks at closed points are domains
  have hdom : ∀ y : X, IsClosed ({y} : Set X) → IsDomain (X.presheaf.stalk y) := by
    intro y hy
    obtain ⟨h1, h2⟩ := InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension f 1 y hy
    exact CurveGlueCI.isDomain_of_dim_one (by exact_mod_cast h1) h2
  -- irreducible components are pairwise disjoint
  have hdisj : ∀ Z₁ ∈ irreducibleComponents X, ∀ Z₂ ∈ irreducibleComponents X,
      (Z₁ ∩ Z₂).Nonempty → Z₁ = Z₂ := by
    intro Z₁ h₁ Z₂ h₂ hne
    have hcl : IsClosed (Z₁ ∩ Z₂) :=
      (isClosed_of_mem_irreducibleComponents Z₁ h₁).inter (isClosed_of_mem_irreducibleComponents Z₂ h₂)
    obtain ⟨y, ⟨hy₁, hy₂⟩, hyc⟩ := nonempty_inter_closedPoints hne hcl.isLocallyClosed
    exact CurveGlueCI.irreducibleComponent_eq_of_isDomain_stalk h₁ h₂ hy₁ hy₂
      (hdom y (mem_closedPoints_iff.mp hyc))
  -- the irreducible component of `x` is clopen
  set Z := irreducibleComponent x with hZ
  have hZc : IsClosed Z := isClosed_irreducibleComponent
  have hZmem := irreducibleComponent_mem_irreducibleComponents x
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have hcompl : Zᶜ = ⋃ Z' ∈ {Z' ∈ irreducibleComponents X | Z' ≠ Z}, Z' := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hz
      refine ⟨irreducibleComponent z, ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩,
        mem_irreducibleComponent⟩
      intro h
      exact hz (h ▸ mem_irreducibleComponent)
    · rintro ⟨Z', ⟨hZ', hne⟩, hzZ'⟩ hzZ
      exact hne (hdisj Z' hZ' Z hZmem ⟨z, hzZ', hzZ⟩)
  have hZo : IsOpen Z := by
    rw [← isClosed_compl_iff, hcompl]
    exact (hfin.subset fun Z' hZ' => hZ'.1).isClosed_biUnion fun Z' hZ' =>
      isClosed_of_mem_irreducibleComponents Z' hZ'.1
  have h1 : connectedComponent x ⊆ Z :=
    (IsClopen.connectedComponent_subset ⟨hZc, hZo⟩ mem_irreducibleComponent)
  have h2 : Z ⊆ connectedComponent x :=
    isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent mem_irreducibleComponent
  rw [Set.Subset.antisymm h1 h2]
  exact isIrreducible_irreducibleComponent


end CIcopy

end CICopy

section GFCopy

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


end GFCopy

section RamCountCopy

/-! # ts-hecke: ramification index × geometric fibre = degree (development file, Mathlib only)

For a finite Galois extension `E/F`, `F = Frac A` with `A` a principal ideal domain, `B` the
integral closure of `A` in `E`, `φ : A → Ω` (`Ω` algebraically closed of characteristic 0) with
nonzero kernel `P`, and a prime `Q` of `B` over `P`:
`e(Q) · #{ψ : B → Ω | ψ ∘ (A → B) = φ} = [E : F]`. -/

open Polynomial

namespace RamCount

variable {A F E Ω : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E] [FiniteDimensional F E]
  [IsGalois F E] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CharZero Ω]

/-- The fibre of `ψ ↦ ker ψ` over a prime `q` is the set of `A ⧸ P`-embeddings of `B ⧸ q`. -/
noncomputable def fiberEquiv {B : Type} [CommRing B] [Algebra A B] (φ : A →+* Ω)
    (q : (RingHom.ker φ).primesOver B) [q.1.IsMaximal]
    (f : {ψ : B →+* Ω // ψ.comp (algebraMap A B) = φ} → (RingHom.ker φ).primesOver B)
    (hf : ∀ ψ, (f ψ).1 = RingHom.ker ψ.1) :
    letI : Algebra (A ⧸ RingHom.ker φ) Ω :=
      (Ideal.Quotient.lift (RingHom.ker φ) φ (fun _ ha => RingHom.mem_ker.1 ha)).toAlgebra
    {ψ // f ψ = q} ≃ (B ⧸ q.1 →ₐ[A ⧸ RingHom.ker φ] Ω) :=
  letI : Algebra (A ⧸ RingHom.ker φ) Ω :=
    (Ideal.Quotient.lift (RingHom.ker φ) φ (fun _ ha => RingHom.mem_ker.1 ha)).toAlgebra
  letI : Field (B ⧸ q.1) := Ideal.Quotient.field q.1
  { toFun := fun ψ =>
      { toRingHom := Ideal.Quotient.lift q.1 ψ.1.1 (fun x hx => by
          have h : RingHom.ker ψ.1.1 = q.1 := (hf ψ.1).symm.trans (congrArg Subtype.val ψ.2)
          rw [← h] at hx; exact hx)
        commutes' := by
          intro r
          obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
          change ψ.1.1 (algebraMap A B a) = φ a
          exact congrArg (fun g : A →+* Ω => g a) ψ.1.2 }
    invFun := fun χ => ⟨⟨χ.toRingHom.comp (Ideal.Quotient.mk q.1), RingHom.ext fun a => by
        change χ (Ideal.Quotient.mk q.1 (algebraMap A B a)) = φ a
        exact χ.commutes (Ideal.Quotient.mk _ a)⟩, by
        apply Subtype.ext
        rw [hf]
        ext x
        simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply]
        rw [show (χ.toRingHom (Ideal.Quotient.mk q.1 x) = 0) ↔ Ideal.Quotient.mk q.1 x = 0 from
          map_eq_zero_iff χ.toRingHom χ.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]⟩
    left_inv := fun ψ => by
      apply Subtype.ext; apply Subtype.ext
      ext x
      rfl
    right_inv := fun χ => by
      ext x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl }

theorem ramCount (φ : A →+* Ω) (hφ : RingHom.ker φ ≠ ⊥)
    (Q : Ideal (integralClosure A E)) [hQ : Q.IsPrime] (hQP : Q.under A = RingHom.ker φ) :
    Q.ramificationIdx A *
      {ψ : integralClosure A E →+* Ω | ψ.comp (algebraMap A (integralClosure A E)) = φ}.ncard =
      Module.finrank F E := by
  classical
  set P := RingHom.ker φ with hPdef
  haveI hPprime : P.IsPrime := RingHom.ker_isPrime φ
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hφ
  haveI : Q.LiesOver P := ⟨hQP.symm⟩
  have hinjAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A F E]
    exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
  haveI : Module.IsTorsionFree A E := Module.isTorsionFree_iff_algebraMap_injective.2 hinjAE
  haveI : Module.Finite A (integralClosure A E) := IsIntegralClosure.finite A F E _
  haveI : Module.Free A (integralClosure A E) := IsIntegralClosure.module_free A F E _
  haveI : IsFractionRing (integralClosure A E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F E _
  have hrank : Module.finrank A (integralClosure A E) = Module.finrank F E :=
    IsIntegralClosure.rank A F E _
  haveI : SMulCommClass Gal(E/F) A E := ⟨fun g a x => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply A F E, AlgEquiv.commutes]⟩
  haveI : IsGaloisGroup Gal(E/F) A (integralClosure A E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/F) A (integralClosure A E) F E
  haveI : Fintype (P.primesOver (integralClosure A E)) :=
    (Algebra.QuasiFinite.finite_primesOver P).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (integralClosure A E)
  have he : ∀ q : P.primesOver (integralClosure A E),
      q.1.ramificationIdx A = Q.ramificationIdx A :=
    fun q => Ideal.ramificationIdx_eq_of_isGaloisGroup P q.1 Q Gal(E/F)
  -- the count of embeddings
  letI : Algebra (A ⧸ P) Ω := (Ideal.Quotient.lift P φ (fun _ ha => RingHom.mem_ker.1 ha)).toAlgebra
  letI : Field (A ⧸ P) := Ideal.Quotient.field P
  haveI : CharZero (A ⧸ P) := RingHom.charZero (algebraMap (A ⧸ P) Ω)
  let f : {ψ : integralClosure A E →+* Ω // ψ.comp (algebraMap A (integralClosure A E)) = φ} →
      P.primesOver (integralClosure A E) := fun ψ =>
    ⟨RingHom.ker ψ.1, RingHom.ker_isPrime _, ⟨by
      rw [Ideal.under, RingHom.comap_ker, ψ.2]⟩⟩
  have hcount : {ψ : integralClosure A E →+* Ω |
      ψ.comp (algebraMap A (integralClosure A E)) = φ}.ncard =
      ∑ q : P.primesOver (integralClosure A E), q.1.inertiaDeg A := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card {ψ : integralClosure A E →+* Ω //
      ψ.comp (algebraMap A (integralClosure A E)) = φ} = _
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f)]
    have hfib : ∀ q : P.primesOver (integralClosure A E),
        Nat.card {ψ // f ψ = q} = q.1.inertiaDeg A := by
      intro q
      haveI : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 P
      letI : Field (integralClosure A E ⧸ q.1) := Ideal.Quotient.field q.1
      rw [Nat.card_congr (fiberEquiv φ q f (fun _ => rfl)),
        AlgHom.natCard_of_splits (A ⧸ P) (integralClosure A E ⧸ q.1) Ω
          (fun _ => IsAlgClosed.splits _),
        Ideal.inertiaDeg_eq_of_isMaximal P q.1]
    haveI : ∀ q : P.primesOver (integralClosure A E), Finite {ψ // f ψ = q} := by
      intro q
      haveI : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 P
      letI : Field (integralClosure A E ⧸ q.1) := Ideal.Quotient.field q.1
      exact Finite.of_equiv _ (fiberEquiv φ q f (fun _ => rfl)).symm
    rw [Nat.card_sigma]
    exact Finset.sum_congr rfl fun q _ => hfib q
  rw [hcount, Finset.mul_sum, ← hrank, ← hsum]
  exact Finset.sum_congr rfl fun q _ => by rw [he q]

end RamCount


end RamCountCopy

section UnitsCopy

/-! # ts-hecke: `𝒪^× → (𝒪/3𝒪)^×` is onto (development file)

Table of 72 explicit units (`units_table.py`), checked by `decide`. -/

noncomputable section

namespace TSHeckeUnits

open LeafQM LeafQM.AV

/-- The reduced norm in `ofInt` coordinates:
`nrd(n₀ + n₁ i + n₂ (1+j)/2 + n₃ (i+k)/2) = n₀² + n₀n₂ + n₂² − 2(n₁² + n₁n₃ + n₃²)`. -/
def nrdC (n : Fin 4 → ℤ) : ℤ := n 0 ^ 2 + n 0 * n 2 + n 2 ^ 2 - 2 * (n 1 ^ 2 + n 1 * n 3 + n 3 ^ 2)

/-- The conjugate in `ofInt` coordinates. -/
def conjC (n : Fin 4 → ℤ) : Fin 4 → ℤ := ![n 0 + n 2, -n 1, -n 2, -n 3]

theorem nrdC_mul (n m : Fin 4 → ℤ) : nrdC (mulCoord n m) = nrdC n * nrdC m := by
  simp only [nrdC, mulCoord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem mulCoord_smul_conjC (n : Fin 4 → ℤ) (ε : ℤ) :
    mulCoord n (fun i => ε * conjC n i) = ![ε * nrdC n, 0, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [mulCoord, conjC, nrdC] <;> ring

theorem mulCoord_smul_conjC' (n : Fin 4 → ℤ) (ε : ℤ) :
    mulCoord (fun i => ε * conjC n i) n = ![ε * nrdC n, 0, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [mulCoord, conjC, nrdC] <;> ring

/-- A unit of `𝒪` from coordinates of reduced norm `ε = ±1`. -/
def unitOf (n : Fin 4 → ℤ) (ε : ℤ) (hε : nrdC n = ε) (hε2 : ε * ε = 1) : Oˣ where
  val := ⟨ofInt n, n, rfl⟩
  inv := ⟨ofInt (fun i => ε * conjC n i), _, rfl⟩
  val_inv := by
    apply Subtype.ext
    change ofInt n * ofInt (fun i => ε * conjC n i) = 1
    rw [ofInt_mul, mulCoord_smul_conjC, hε, hε2, ofInt_one]
  inv_val := by
    apply Subtype.ext
    change ofInt (fun i => ε * conjC n i) * ofInt n = 1
    rw [ofInt_mul, mulCoord_smul_conjC', hε, hε2, ofInt_one]

def unitTbl : List (Fin 4 → ℤ) :=
  [![0, 0, 0, 0],
   ![1, 0, 0, 0],
   ![-1, 0, 0, 0],
   ![-3, -2, 0, 0],
   ![1, 1, 0, 0],
   ![-1, 1, 0, 0],
   ![-3, 2, 0, 0],
   ![1, -1, 0, 0],
   ![-1, -1, 0, 0],
   ![0, 0, 1, 0],
   ![0, 0, 0, 0],
   ![-1, 0, 1, 0],
   ![0, 1, 1, 0],
   ![1, 1, 1, 0],
   ![-1, 1, 1, 0],
   ![0, -1, 1, 0],
   ![1, -1, 1, 0],
   ![-1, -1, 1, 0],
   ![0, 0, -1, 0],
   ![1, 0, -1, 0],
   ![0, 0, 0, 0],
   ![0, 1, -1, 0],
   ![1, 1, -1, 0],
   ![-1, 1, -1, 0],
   ![0, -1, -1, 0],
   ![1, -1, -1, 0],
   ![-1, -1, -1, 0],
   ![-3, 0, 0, -2],
   ![1, 0, 0, 1],
   ![-1, 0, 0, 1],
   ![0, 0, 0, 0],
   ![1, 1, -3, 1],
   ![-1, 1, 3, 1],
   ![-3, 2, 0, -2],
   ![1, -1, 0, 1],
   ![-1, -1, 0, 1],
   ![0, 0, 1, 1],
   ![1, 0, 1, 1],
   ![-1, 0, 1, 1],
   ![-3, 1, 1, 1],
   ![0, 0, 0, 0],
   ![-1, 1, -2, 1],
   ![0, -1, 1, 1],
   ![1, -1, 1, 1],
   ![-1, -1, 1, 1],
   ![0, 0, -1, 1],
   ![1, 0, -1, 1],
   ![-1, 0, -1, 1],
   ![3, 1, -1, 1],
   ![-2, 1, -1, 1],
   ![0, 0, 0, 0],
   ![0, -1, -1, 1],
   ![1, -1, -1, 1],
   ![-1, -1, -1, 1],
   ![-3, 0, 0, 2],
   ![1, 0, 0, -1],
   ![-1, 0, 0, -1],
   ![-3, -2, 0, 2],
   ![1, 1, 0, -1],
   ![-1, 1, 0, -1],
   ![0, 0, 0, 0],
   ![1, -1, -3, -1],
   ![-1, -1, 3, -1],
   ![0, 0, 1, -1],
   ![1, 0, 1, -1],
   ![-1, 0, 1, -1],
   ![0, 1, 1, -1],
   ![1, 1, 1, -1],
   ![-1, 1, 1, -1],
   ![-3, -1, 1, -1],
   ![0, 0, 0, 0],
   ![-1, -1, -2, -1],
   ![0, 0, -1, -1],
   ![1, 0, -1, -1],
   ![-1, 0, -1, -1],
   ![0, 1, -1, -1],
   ![1, 1, -1, -1],
   ![-1, 1, -1, -1],
   ![3, -1, -1, -1],
   ![-2, -1, -1, -1],
   ![0, 0, 0, 0]]


/-- The table entry for a residue vector. -/
def tbl (c : Fin 4 → ZMod 3) : Fin 4 → ℤ :=
  unitTbl.getD ((c 0).val + 3 * (c 1).val + 9 * (c 2).val + 27 * (c 3).val) 0

/-- The reduced norm mod 3. -/
def nrd3 (c : Fin 4 → ZMod 3) : ZMod 3 :=
  c 0 ^ 2 + c 0 * c 2 + c 2 ^ 2 - 2 * (c 1 ^ 2 + c 1 * c 3 + c 3 ^ 2)

/-- **The table is correct** (checked by `decide`): for every residue of nonzero reduced norm,
the entry reduces to it and has reduced norm `±1`. -/
theorem tbl_spec : ∀ c : Fin 4 → ZMod 3, nrd3 c ≠ 0 →
    (∀ i, ((tbl c i : ℤ) : ZMod 3) = c i) ∧ (nrdC (tbl c) = 1 ∨ nrdC (tbl c) = -1) := by
  decide +kernel

theorem nrdC_cast (n : Fin 4 → ℤ) : ((nrdC n : ℤ) : ZMod 3) = nrd3 (fun i => (n i : ZMod 3)) := by
  simp [nrdC, nrd3]

/-- **`𝒪^× → (𝒪/3𝒪)^×` is onto** (compiled): an element `u₀` of `𝒪` invertible modulo `3𝒪` is
congruent mod `3𝒪` to a unit. -/
theorem exists_unit_congr (u₀ v₀ : O) (h : ∃ c : O, v₀ * u₀ - 1 = 3 * c) :
    ∃ u : Oˣ, ∃ d : O, u₀ - (u : O) = 3 * d := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨nu, hnu⟩ := u₀.2
  obtain ⟨nv, hnv⟩ := v₀.2
  obtain ⟨nc, hnc⟩ := c.2
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  have h1 : ((1 : O) : B) = ofInt ![1, 0, 0, 0] := by rw [ofInt_one]; rfl
  have hcoord : mulCoord nv nu - ![1, 0, 0, 0] = fun i => 3 * nc i := by
    apply ofInt_injective
    rw [← ofInt_sub, ← ofInt_mul, ← three_mul_ofInt, ← hnu, ← hnv, ← hnc, ← h1, ← h33]
    exact congrArg Subtype.val hc
  -- the reduced norm of `u₀` is nonzero mod 3
  have hn1 : ((nrdC (mulCoord nv nu) : ℤ) : ZMod 3) = 1 := by
    have : mulCoord nv nu = fun i => ![1, 0, 0, 0] i + 3 * nc i := by
      funext i
      have := congrFun hcoord i
      simp only [Pi.sub_apply] at this
      linarith
    rw [this, nrdC_cast]
    simp only [nrd3]
    simp [show (3 : ZMod 3) = 0 from rfl]
  have hnu3 : nrd3 (fun i => (nu i : ZMod 3)) ≠ 0 := by
    intro h0
    rw [nrdC_mul, Int.cast_mul, nrdC_cast nu, h0, mul_zero] at hn1
    exact zero_ne_one hn1
  obtain ⟨hred, hε⟩ := tbl_spec _ hnu3
  set n := tbl (fun i => (nu i : ZMod 3))
  have hdvd : ∀ i, (3 : ℤ) ∣ nu i - n i := by
    intro i
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (nu i - n i) 3).1
      (by rw [Int.cast_sub, hred i, sub_self])
    exact_mod_cast this
  let ε : ℤ := nrdC n
  have hε2 : ε * ε = 1 := by rcases hε with h | h <;> simp [ε, h]
  refine ⟨unitOf n ε rfl hε2, ⟨ofInt (fun i => (nu i - n i) / 3), _, rfl⟩, ?_⟩
  apply Subtype.ext
  change (u₀ : B) - ofInt n = ((3 : O) : B) * ofInt (fun i => (nu i - n i) / 3)
  rw [hnu, h33, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  exact (Int.mul_ediv_cancel' (hdvd i)).symm

end TSHeckeUnits

end


end UnitsCopy

/-! ## Part 3b: the Galois property in `CurveGaloisChart` (dev section) -/

noncomputable section

namespace TSHeckeGal

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin G0ModField PropTSRed

/-- Any two morphisms `Spec ℚ̄ → Spec ℚ` agree. -/
theorem specQbar_to_specQ_eq' (f g : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of ℚ)) :
    f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- **A closed point of a scheme locally of finite type over `ℚ` has a `ℚ̄`-point** (compiled). -/
theorem exists_qbar_point {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℚ))
    [LocallyOfFiniteType f] (z : X) (hz : IsClosed ({z} : Set X)) :
    ∃ y : Spec (CommRingCat.of Qbar) ⟶ X, ∀ s, y s = z := by
  have : IsClosedImmersion (X.fromSpecResidueField z) :=
    isClosed_singleton_iff_isClosedImmersion.mp hz
  have : IsFinite (X.fromSpecResidueField z ≫ f) :=
    (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace
      (f := X.fromSpecResidueField z ≫ f)).mpr inferInstance
  let φ := Spec.preimage (X.fromSpecResidueField z ≫ f)
  letI : Algebra ℚ (X.residueField z) := φ.hom.toAlgebra
  have hφ : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, Spec.map_preimage]
    infer_instance
  haveI : Algebra.IsIntegral ℚ (X.residueField z) := ⟨fun x => hφ x⟩
  haveI : Algebra.IsAlgebraic ℚ (X.residueField z) := Algebra.IsIntegral.isAlgebraic
  let L : X.residueField z →ₐ[ℚ] Qbar := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom L.toRingHom) ≫ X.fromSpecResidueField z, fun s => ?_⟩
  rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

variable {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left} {E : Type} [Field E]
  [Algebra ℚ[X] E]

/-- **A `π`-preserving endomorphism maps the chart into itself** (compiled; Jacobson). -/
theorem range_comp_subset [LocallyOfFiniteType Y.hom]
    (h : Spec (CommRingCat.of (integralClosure ℚ[X] E)) ⟶ Y.left) [IsOpenImmersion h]
    (himg : ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) y ≠ OnePoint.infty →
      ∃ y' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of (integralClosure ℚ[X] E)),
        y = y' ≫ h)
    (hval : ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
      π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) =
        OnePoint.some (ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X)))
    (g : Y.left ⟶ Y.left)
    (hg : ∀ z : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) (z ≫ g) = π.val (K := Qbar) z) :
    Set.range (h ≫ g) ⊆ Set.range h := by
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  by_contra hcon
  rw [Set.not_subset] at hcon
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hcon
  set W : Set Y.left := Set.range h ∩ g ⁻¹' (Set.range h)ᶜ
  have hWne : W.Nonempty := ⟨h x, ⟨x, rfl⟩, by simpa using hx⟩
  have hWlc : IsLocallyClosed W :=
    (h.isOpenEmbedding.isOpen_range).isLocallyClosed.inter
      ((h.isOpenEmbedding.isOpen_range).isClosed_compl.preimage g.continuous).isLocallyClosed
  obtain ⟨z, ⟨hzh, hzg⟩, hzc⟩ := nonempty_inter_closedPoints hWne hWlc
  obtain ⟨y, hy⟩ := exists_qbar_point Y.hom z (mem_closedPoints_iff.mp hzc)
  have hyr : Set.range y ⊆ Set.range h := by
    rintro _ ⟨s, rfl⟩; rw [hy s]; exact hzh
  set y'' := IsOpenImmersion.lift h y hyr
  have hy'' : y'' ≫ h = y := IsOpenImmersion.lift_fac h y hyr
  have hfin : π.val (K := Qbar) y ≠ OnePoint.infty := by
    rw [← hy'', ← Spec.map_preimage y'', ← CommRingCat.ofHom_hom (Spec.preimage y''), hval]
    exact OnePoint.coe_ne_infty _
  obtain ⟨y', hy'⟩ := himg (y ≫ g) (by rw [hg]; exact hfin)
  apply hzg
  obtain ⟨s⟩ : Nonempty (Spec (CommRingCat.of Qbar)) := inferInstance
  refine ⟨y' s, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← hy', Scheme.Hom.comp_apply, hy s]

/-- A nonzero prime of `ℚ[X]` is the kernel of evaluation at some `t ∈ ℚ̄` (compiled). -/
theorem exists_ker_eval' (P : Ideal ℚ[X]) [hP : P.IsPrime] (h0 : P ≠ ⊥) :
    ∃ t : Qbar, P = RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t) := by
  have hmax : P.IsMaximal := hP.isMaximal h0
  obtain ⟨p, rfl⟩ := (Submodule.IsPrincipal.principal P)
  have hp0 : p ≠ 0 := by rintro rfl; exact h0 (by simp)
  have hdeg : (p.map (algebraMap ℚ Qbar)).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    intro hd
    rw [Polynomial.eq_C_of_degree_eq_zero hd] at hmax
    apply hmax.ne_top
    rw [Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
    have : p.coeff 0 ≠ 0 := by
      intro hc; apply hp0; rw [Polynomial.eq_C_of_degree_eq_zero hd, hc, map_zero]
    exact Polynomial.isUnit_C.2 (Ne.isUnit this)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨t, hmax.eq_of_le (RingHom.ker_ne_top _) ?_⟩
  rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
  show Polynomial.eval₂ (algebraMap ℚ Qbar) t p = 0
  rw [← Polynomial.eval_map]
  exact ht

/-- **Separation by `ℚ̄`-points** (compiled): in a domain `B` finite over `ℚ[X]`, two elements with
the same value under every ring map `B → ℚ̄` are equal (`B` is Jacobson; every maximal ideal is
the kernel of such a map). -/
theorem eq_of_forall_qbar {B : Type} [CommRing B] [IsDomain B] [Algebra ℚ[X] B]
    [Algebra.IsIntegral ℚ[X] B] (hinj : Function.Injective (algebraMap ℚ[X] B)) (a b : B)
    (h : ∀ ψ : B →+* Qbar, ψ a = ψ b) : a = b := by
  haveI : IsJacobsonRing B := isJacobsonRing_of_isIntegral (R := ℚ[X])
  rw [← sub_eq_zero]
  have hjac := IsJacobsonRing.out (R := B) inferInstance
    (Ideal.isRadical_bot_of_noZeroDivisors (R := B))
  rw [← Ideal.mem_bot, ← hjac, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  haveI := hm
  set P := m.under ℚ[X]
  haveI hPmax : P.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℚ[X]) m
  have hP0 : P ≠ ⊥ := by
    intro h0
    rw [h0] at hPmax
    exact Polynomial.not_isField ℚ (Ring.isField_iff_maximal_bot.2 hPmax)
  obtain ⟨t, ht⟩ := exists_ker_eval' P hP0
  let φ : ℚ[X] →+* Qbar := Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t
  haveI : m.LiesOver P := ⟨rfl⟩
  letI : Algebra (ℚ[X] ⧸ P) Qbar :=
    (Ideal.Quotient.lift P φ (fun x hx => by rw [ht] at hx; exact RingHom.mem_ker.1 hx)).toAlgebra
  letI : Field (ℚ[X] ⧸ P) := Ideal.Quotient.field P
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  haveI : Module.IsTorsionFree (ℚ[X] ⧸ P) (B ⧸ m) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (ℚ[X] ⧸ P) Qbar := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (algebraMap (ℚ[X] ⧸ P) Qbar).injective
  haveI : Algebra.IsAlgebraic (ℚ[X] ⧸ P) (B ⧸ m) := Algebra.IsIntegral.isAlgebraic
  let L : (B ⧸ m) →ₐ[ℚ[X] ⧸ P] Qbar := IsAlgClosed.lift
  have h1 := h (L.toRingHom.comp (Ideal.Quotient.mk m))
  simp only [RingHom.coe_comp, Function.comp_apply] at h1
  have h2 := L.toRingHom.injective h1
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact h2

/-- **The ring map induced by a `π`-preserving endomorphism** (compiled). -/
theorem exists_sigma [LocallyOfFiniteType Y.hom] [Algebra (RatFunc ℚ) E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E]
    (h : Spec (CommRingCat.of (integralClosure ℚ[X] E)) ⟶ Y.left) [IsOpenImmersion h]
    (himg : ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) y ≠ OnePoint.infty →
      ∃ y' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of (integralClosure ℚ[X] E)),
        y = y' ≫ h)
    (hval : ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
      π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) =
        OnePoint.some (ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X)))
    (g : Y.left ⟶ Y.left)
    (hg : ∀ z : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) (z ≫ g) = π.val (K := Qbar) z) :
    ∃ σ : integralClosure ℚ[X] E →+* integralClosure ℚ[X] E,
      Spec.map (CommRingCat.ofHom σ) ≫ h = h ≫ g ∧
      σ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ[X] (integralClosure ℚ[X] E) X := by
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b hab
    have h' := congrArg Subtype.val hab
    change algebraMap ℚ[X] E a = algebraMap ℚ[X] E b at h'
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
      IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E b] at h'
    exact IsFractionRing.injective ℚ[X] (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h')
  have hr := range_comp_subset h himg hval g hg
  set k := IsOpenImmersion.lift h (h ≫ g) hr
  have hk : k ≫ h = h ≫ g := IsOpenImmersion.lift_fac h (h ≫ g) hr
  refine ⟨(Spec.preimage k).hom, ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_preimage, hk]
  · apply eq_of_forall_qbar hinjB
    intro ψ
    have e1 := hval (ψ.comp (Spec.preimage k).hom)
    have e2 : Spec.map (CommRingCat.ofHom (ψ.comp (Spec.preimage k).hom)) ≫ h =
        (Spec.map (CommRingCat.ofHom ψ) ≫ h) ≫ g := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage,
        Category.assoc, hk, Category.assoc]
    rw [e2, hg, hval ψ] at e1
    exact (OnePoint.coe_injective e1).symm

/-- **The field automorphism induced by a `π`-preserving endomorphism** (compiled): the ring map
`σ` of `exists_sigma` fixes `ℚ[X]`, so it extends to an automorphism `τ` of `E` over `ℚ(X)`. -/
theorem exists_tau [Algebra (RatFunc ℚ) E] [IsScalarTower ℚ[X] (RatFunc ℚ) E]
    [FiniteDimensional (RatFunc ℚ) E]
    (σ : integralClosure ℚ[X] E →+* integralClosure ℚ[X] E)
    (hσ : σ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ[X] (integralClosure ℚ[X] E) X) :
    ∃ τ : E ≃ₐ[RatFunc ℚ] E, ∀ b : integralClosure ℚ[X] E,
      τ (algebraMap (integralClosure ℚ[X] E) E b) = algebraMap (integralClosure ℚ[X] E) E (σ b) := by
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b hab
    have h' := congrArg Subtype.val hab
    change algebraMap ℚ[X] E a = algebraMap ℚ[X] E b at h'
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
      IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E b] at h'
    exact IsFractionRing.injective ℚ[X] (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h')
  haveI : Module.IsTorsionFree ℚ[X] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  haveI : IsFractionRing (integralClosure ℚ[X] E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) E _
  -- `σ` fixes `ℚ[X]`
  have hfix : σ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E)) =
      algebraMap ℚ[X] (integralClosure ℚ[X] E) :=
    Polynomial.ringHom_ext (fun a => RingHom.congr_fun (RingHom.ext_rat
      ((σ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E))).comp Polynomial.C)
      ((algebraMap ℚ[X] (integralClosure ℚ[X] E)).comp Polynomial.C)) a) (by simpa using hσ)
  -- `σ` is injective
  have hσinj : Function.Injective σ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hker : (RingHom.ker σ).under ℚ[X] = ⊥ := by
      ext a
      simp only [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      constructor
      · intro ha
        rw [← RingHom.comp_apply, hfix] at ha
        exact hinjB (by rw [ha, map_zero])
      · rintro rfl; simp
    have := Ideal.eq_bot_of_under_eq_bot (R := ℚ[X]) hker
    have hb' : b ∈ RingHom.ker σ := hb
    rw [this] at hb'
    exact hb'
  have hg : Function.Injective ((algebraMap (integralClosure ℚ[X] E) E).comp σ) :=
    (IsFractionRing.injective (integralClosure ℚ[X] E) E).comp hσinj
  let τ₀ : E →+* E := IsFractionRing.lift hg
  have hτ₀ : ∀ b, τ₀ (algebraMap (integralClosure ℚ[X] E) E b) =
      algebraMap (integralClosure ℚ[X] E) E (σ b) := fun b => IsFractionRing.lift_algebraMap hg b
  have hcomm : τ₀.comp (algebraMap (RatFunc ℚ) E) = algebraMap (RatFunc ℚ) E := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℚ[X])
    refine RingHom.ext fun a => ?_
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℚ[X]
      (integralClosure ℚ[X] E) E, hτ₀, ← RingHom.comp_apply σ, hfix,
      ← IsScalarTower.algebraMap_apply]
  let τ₁ : E →ₐ[RatFunc ℚ] E := { τ₀ with commutes' := fun r => RingHom.congr_fun hcomm r }
  exact ⟨AlgEquiv.ofBijective τ₁ (AlgHom.bijective τ₁), fun b => hτ₀ b⟩

/-- **Galois from fibre transitivity** (compiled). If `E` carries the normalization chart of
`(Y, π)`, some rational fibre has at least `[E : ℚ(X)]` points of `Spec B` (generic étaleness),
and any two `ℚ̄`-points with the same `π`-value differ by a `π`-preserving automorphism of `Y`,
then `E/ℚ(X)` is Galois. -/
theorem isGalois_of_transitive [LocallyOfFiniteType Y.hom] [Algebra (RatFunc ℚ) E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    (hM : NormalizationModel Y π E)
    (hG : ∃ t : ℚ, ∃ s : Finset (integralClosure ℚ[X] E →+* Qbar),
      Module.finrank (RatFunc ℚ) E ≤ s.card ∧
      ∀ ψ ∈ s, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ Qbar t)
    (htrans : ∀ y y' : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left →
      ∃ g : Y ≅ Y, y' = y ≫ g.hom ∧
        ∀ z : fieldPt Qbar ⟶ Y, π.val (K := Qbar) (z ≫ g.hom).left = π.val (K := Qbar) z.left) :
    IsGalois (RatFunc ℚ) E := by
  classical
  haveI : Module.IsTorsionFree ℚ[X] E := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  haveI : IsFractionRing (integralClosure ℚ[X] E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) E _
  obtain ⟨h, hO, himg, hval⟩ := hM
  obtain ⟨t, s, hs, hst⟩ := hG
  let ptO : (integralClosure ℚ[X] E →+* Qbar) → (fieldPt Qbar ⟶ Y) := fun ψ =>
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (specQbar_to_specQ_eq' _ _)
  have hnpos : 0 < Module.finrank (RatFunc ℚ) E := Module.finrank_pos
  obtain ⟨ψ₀, hψ₀⟩ : s.Nonempty := by
    rw [← Finset.card_pos]; omega
  -- for each `ψ ∈ s`, an automorphism `τ` and a ring map `σ` with `ψ = ψ₀ ∘ σ`
  have key : ∀ ψ ∈ s, ∃ τ : E ≃ₐ[RatFunc ℚ] E, ∃ σ : integralClosure ℚ[X] E →+* integralClosure ℚ[X] E,
      (∀ b, τ (algebraMap (integralClosure ℚ[X] E) E b) = algebraMap (integralClosure ℚ[X] E) E (σ b)) ∧
      ψ = ψ₀.comp σ := by
    intro ψ hψ
    have hπ : π.val (K := Qbar) (ptO ψ₀).left = π.val (K := Qbar) (ptO ψ).left := by
      show π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ₀) ≫ h) =
        π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h)
      rw [hval, hval, hst ψ₀ hψ₀, hst ψ hψ]
    obtain ⟨g, hgy, hgπ⟩ := htrans (ptO ψ₀) (ptO ψ) hπ
    have hg' : ∀ z : Spec (CommRingCat.of Qbar) ⟶ Y.left,
        π.val (K := Qbar) (z ≫ g.hom.left) = π.val (K := Qbar) z := fun z =>
      hgπ (Over.homMk z (specQbar_to_specQ_eq' _ _))
    obtain ⟨σ, hσh, hσX⟩ := exists_sigma h himg hval g.hom.left hg'
    obtain ⟨τ, hτ⟩ := exists_tau σ hσX
    refine ⟨τ, σ, hτ, ?_⟩
    have e1 : Spec.map (CommRingCat.ofHom ψ) ≫ h = Spec.map (CommRingCat.ofHom (ψ₀.comp σ)) ≫ h := by
      have := congrArg (fun y : fieldPt Qbar ⟶ Y => y.left) hgy
      change Spec.map (CommRingCat.ofHom ψ) ≫ h =
        (Spec.map (CommRingCat.ofHom ψ₀) ≫ h) ≫ g.hom.left at this
      rw [this, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, hσh]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono h).1 e1))
  choose T σT hT hψT using key
  have hTinj : Function.Injective (fun ψ : s => T ψ.1 ψ.2) := by
    rintro ⟨ψ, hψ⟩ ⟨ψ', hψ'⟩ heq
    simp only at heq
    apply Subtype.ext
    simp only
    rw [hψT ψ hψ, hψT ψ' hψ']
    congr 1
    ext1 b
    apply IsFractionRing.injective (integralClosure ℚ[X] E) E
    rw [← hT ψ hψ b, ← hT ψ' hψ' b, heq]
  have hcard : s.card ≤ Fintype.card (E ≃ₐ[RatFunc ℚ] E) := by
    rw [← Fintype.card_coe s]
    exact Fintype.card_le_of_injective _ hTinj
  have hle := AlgEquiv.card_le (F := RatFunc ℚ) (K := E)
  apply IsGalois.of_card_aut_eq_finrank
  rw [Nat.card_eq_fintype_card]
  omega

end TSHeckeGal

end

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# ts-hecke: the five Hecke Props under `CoverModelOfHecke`, settled and reduced

Everything above this line is copied verbatim (see `assemble.py` and `check_identical.py`):
the prop-ts prefix, the five Hecke Props of prop-ts-glue, aut-o-finite's computation of
`Aut(𝒪)/Inn(𝒪^×)`, infra-smooth-dim's stalk dimensions and curve-glue's proof of
`ComponentIrreducible`. Below: the work of task ts-hecke. No `sorry`, no `axiom`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace TSHecke

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin G0ModField PropTSRed PropTSGlue PkgI3
open MonoidalCategory CartesianMonoidalCategory MonObj

/-! ## Part 1: `HeckeIrreducible` -/

/-- **Any two triples satisfying R1fp are related by a surjective morphism** (compiled). The
morphism is `phi_part`'s `g : Y' → Y` with `Φ' = Φ ∘ g`; it is onto because every point `x` of `Y`
is the image of its own `κ(x)`-point, and `Φ'` is onto `M3 κ(x)` while `Φ` is injective. -/
theorem exists_surjective_of_R1fp {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Φ' : PtEquiv Y'} (h : R1fpProps Y Φ) (h' : R1fpProps Y' Φ') :
    ∃ g : Y' ⟶ Y, Function.Surjective g.left := by
  obtain ⟨g, hg⟩ := phi_part (R1fpProps.univ h) h'
  refine ⟨g, fun x => ?_⟩
  let φ : CommRingCat.of ℚ ⟶ Y.left.residueField x :=
    Spec.preimage (Y.left.fromSpecResidueField x ≫ Y.hom)
  letI : Algebra ℚ (Y.left.residueField x) := φ.hom.toAlgebra
  let y : fieldPt (Y.left.residueField x) ⟶ Y :=
    Over.homMk (Y.left.fromSpecResidueField x) (by
      change _ = Spec.map φ
      exact (Spec.map_preimage _).symm)
  obtain ⟨y', hy'⟩ := (Φ' (Y.left.residueField x)).surjective (Φ _ y)
  have hyy : y' ≫ g = y := (Φ _).injective ((hg _ y').symm.trans hy')
  let s : (fieldPt (Y.left.residueField x)).left := IsLocalRing.closedPoint _
  refine ⟨y'.left s, ?_⟩
  have h1 : (y' ≫ g).left s = y.left s := by rw [hyy]
  rw [Over.comp_left, Scheme.Hom.comp_apply] at h1
  rw [h1]
  exact Y.left.fromSpecResidueField_apply x _

/-- **Leaf R1conn (the canonical model `Y₃ = Sh_{K₃}` is connected over `ℚ`), witness form.**
Some triple satisfying the clause list R1fp has a connected underlying space.

*Published statement* (Shimura; Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§2-3,
and *Variétés de Shimura*, Proc. Symp. Pure Math. 33 (1979), §2.1 and Thm 2.6.3; Milne,
*Introduction to Shimura varieties* (2005), §5 and §13; all locators UNVERIFIED): for `G = B^×`
the set of geometric components of `Sh_K` is `ℚ_{>0}^× \ 𝔸_f^× / nrd(K)`, and `Gal(ℚ̄/ℚ)` acts on
it through the cyclotomic character (Artin reciprocity), i.e. through multiplication by `ℤ̂^×`.
*Consequence used*: for `K₃ = ker(𝒪̂^× → (𝒪/3𝒪)^×)`, `nrd(K₃) = ∏_{ℓ≠3} ℤ_ℓ^× × (1 + 3ℤ_3)`, so the
set of components is `(ℤ/3)^×` (two points) and `ℤ̂^×` acts transitively on it: `Y₃` is
`ℚ`-connected (its two geometric components are swapped by `Gal(ℚ(√−3)/ℚ)`, in particular by
complex conjugation).
*Computation* (VERIFIED, `scratch/ts-hecke/pi0_check.py`): in Shimura's uniformization
`Y₃(ℂ) = 𝒪^× \ (ℍ^± × (𝒪/3𝒪)^×)` there are exactly two orbits, separated by `s · nrd(a) mod 3`,
and complex conjugation `(s, a) ↦ (−s, a)` swaps them. -/
def Y3Connected : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ ConnectedSpace Y.left

/-- Connectedness transfers to every triple satisfying R1fp (compiled). -/
theorem connectedSpace_of_R1fp (hC : Y3Connected) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} (h : R1fpProps Y Φ) : ConnectedSpace Y.left := by
  obtain ⟨Y₀, Φ₀, h₀, hc⟩ := hC
  obtain ⟨g, hg⟩ := exists_surjective_of_R1fp h h₀
  exact hg.connectedSpace g.left.continuous

/-- Irreducibility transfers to every triple satisfying R1fp (compiled). -/
theorem irreducibleSpace_of_R1fp {Y₀ Y : Over (Spec (CommRingCat.of ℚ))} {Φ₀ : PtEquiv Y₀}
    {Φ : PtEquiv Y} (h₀ : R1fpProps Y₀ Φ₀) (hI : IrreducibleSpace Y₀.left)
    (h : R1fpProps Y Φ) : IrreducibleSpace Y.left := by
  obtain ⟨g, hg⟩ := exists_surjective_of_R1fp h h₀
  exact hg.irreducibleSpace g.left.continuous

/-- **A connected proper smooth curve over a field is irreducible** (compiled, from curve-glue's
`componentIrreducible`, itself from infra-smooth-dim's stalk dimensions). -/
theorem irreducibleSpace_of_connected {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) (hP : IsProper f) (hS : SmoothOfRelativeDimension 1 f)
    [ConnectedSpace X] : IrreducibleSpace X := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have h := CIcopy.componentIrreducible K X f hP hS x
  rw [PreconnectedSpace.connectedComponent_eq_univ] at h
  exact (irreducibleSpace_def X).2 h

/-- **`HeckeIrreducible` from the leaf R1conn** (compiled). -/
theorem heckeIrreducible_of_connected (hC : Y3Connected) : HeckeIrreducible := by
  intro Y Φ π h1 _ _
  have := connectedSpace_of_R1fp hC h1
  obtain ⟨hP, hS, -⟩ := h1
  exact irreducibleSpace_of_connected Y.hom hP hS

/-- `HeckeIrreducible` is equivalent to the leaf, given one triple (compiled): with the bundle
leaf `R1R2fp`, `HeckeIrreducible → Y3Connected`. So R1conn is exactly what is needed. -/
theorem connected_of_heckeIrreducible (hR : R1R2fp) (hI : HeckeIrreducible) : Y3Connected := by
  obtain ⟨Y, Φ, π, h1, hh, h2⟩ := R1R2fp_Y hR
  have := hI Y Φ π h1 hh h2
  exact ⟨Y, Φ, h1, inferInstance⟩

/-! ## Part 2: `HeckeDegree`

The bound `324 = 4 · 81` is a count of `ℚ̄`-points in one fibre of `π`: four classes of
`Aut(𝒪)` modulo inner automorphisms (aut-o-finite) times at most `81` level structures on a fixed
QM pair (the kernel's leaf `ObjBridge.TorsionStructure`, through `Level3.torsor`). The degree
`[E : ℚ(X)]` is at most the number of `ℚ̄`-points of `Spec B` over a generic rational value
(`GenericFibreCount`, algebra), and those points are distinct points of one `π`-fibre. -/

/-- The classes whose QM pair is an `Aut(𝒪)`-twist of the pair of `P` (the shape of a `π`-fibre
on `ℚ̄`-points, by R2fp). -/
def twistFibre (P : QML3 Qbar) : Set (M3 Qbar) :=
  {c | ∃ Q : QML3 Qbar, c = M3.mk Q ∧ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)}

/-- **Glue (commutative algebra; generic étaleness of a finite separable extension).** For a
finite extension `E/ℚ(X)` (separable: characteristic 0) with `B` the integral closure of `ℚ[X]`
in `E`, some rational value `t` has at least `[E : ℚ(X)]` ring maps `B → ℚ̄` sending `X` to `t`.
*Proof sketch* (STANDARD; e.g. Neukirch, *Algebraic Number Theory*, I.8.3 with I.2.9, or Serre,
*Local Fields*, I §4, locators UNVERIFIED): take a primitive element `θ ∈ B` with monic minimal
polynomial `f ∈ ℚ[X][T]` (`ℚ[X]` is integrally closed); `f` is separable, so `a f + b f' = D(X)`
with `D ≠ 0`; for `t ∈ ℚ` with `D(t) ≠ 0`, `f(t, T)` has `n = [E : ℚ(X)]` distinct roots
`r_i ∈ ℚ̄`; each `ℚ[X][θ] → ℚ̄`, `X ↦ t`, `θ ↦ r_i`, extends to `B` (integral over `ℚ[X][θ]`;
lying over and `ℚ̄` algebraically closed); the extensions are distinct since their values at `θ`
are. Glue, not a leaf. -/
def GenericFibreCount : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E],
    ∃ t : ℚ, ∃ s : Finset (integralClosure ℚ[X] E →+* Qbar),
      Module.finrank (RatFunc ℚ) E ≤ s.card ∧
      ∀ ψ ∈ s, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ Qbar t

section Count

variable {K : Type} [Field K]

theorem end_mul_hom {A : AbVar K} (f g : AbVar.End A) : (f * g).hom = g.hom ≫ f.hom := rfl

theorem end_one_hom {A : AbVar K} : (1 : AbVar.End A).hom = 𝟙 _ := rfl

/-- **Transport of a level structure along a QM isomorphism** (pull back by `G.ψ`). -/
def pullLevel {A₁ A₂ : AbVar K} {q₁ : QMStr A₁} {q₂ : QMStr A₂} (G : QMIso q₁ q₂)
    (e : Level3 q₂) : Level3 q₁ where
  eta := (AbVar.ptMap (L := K) G.ψ).toAdditive.comp e.eta
  linear a b := by
    show Additive.ofMul (Additive.toMul (e.eta (a * b)) ≫ G.ψ.hom) =
      Additive.ofMul ((Additive.toMul (e.eta b) ≫ G.ψ.hom) ≫ (q₁.iota a).hom)
    rw [e.linear a b]
    show Additive.ofMul ((Additive.toMul (e.eta b) ≫ (q₂.iota a).hom) ≫ G.ψ.hom) = _
    rw [Category.assoc, Category.assoc]
    congr 2
    exact (G.symm).equivariant a
  ker a := by
    have hinj : Function.Injective (AbVar.ptMap (L := K) G.ψ).toAdditive := by
      intro x y hxy
      have h' : Additive.toMul x ≫ G.ψ.hom = Additive.toMul y ≫ G.ψ.hom := congrArg Additive.toMul hxy
      have h'' := congrArg (· ≫ G.φ.hom) h'
      simp only [Category.assoc, G.right, Category.comp_id] at h''
      exact Additive.toMul.injective h''
    rw [AddMonoidHom.comp_apply, map_eq_zero_iff _ hinj, e.ker]

/-- The isomorphism of objects underlying `pullLevel`. -/
def pullIso {A₁ A₂ : AbVar K} (s₁ : A₁.dim = 2) (s₂ : A₂.dim = 2) {q₁ : QMStr A₁}
    {q₂ : QMStr A₂} (G : QMIso q₁ q₂) (e : Level3 q₂) :
    QML3.Iso (⟨A₁, s₁, q₁, pullLevel G e⟩ : QML3 K) ⟨A₂, s₂, q₂, e⟩ where
  φ := G.φ
  ψ := G.ψ
  left := G.left
  right := G.right
  equivariant := G.equivariant
  level a := by
    show Additive.ofMul ((Additive.toMul (e.eta a) ≫ G.ψ.hom) ≫ G.φ.hom) = e.eta a
    rw [Category.assoc, G.right, Category.comp_id]
    rfl

/-- **Inner twists are isomorphic** (`ι(v⁻¹) : (A, ι ∘ α) ≅ (A, ι ∘ t)` when `α = Ad(v) ∘ t`). -/
def innerIso {A : AbVar K} (q : QMStr A) (t α : O ≃+* O) (v : Oˣ)
    (h : ∀ a : O, α a = (v : O) * t a * ((v⁻¹ : Oˣ) : O)) : QMIso (q.twist α) (q.twist t) where
  φ := q.iota ((v⁻¹ : Oˣ) : O)
  ψ := q.iota (v : O)
  left := by
    rw [← end_mul_hom, ← map_mul, Units.mul_inv, map_one, end_one_hom]
  right := by
    rw [← end_mul_hom, ← map_mul, Units.inv_mul, map_one, end_one_hom]
  equivariant a := by
    show (q.iota (α a)).hom ≫ (q.iota ((v⁻¹ : Oˣ) : O)).hom =
      (q.iota ((v⁻¹ : Oˣ) : O)).hom ≫ (q.iota (t a)).hom
    rw [← end_mul_hom, ← end_mul_hom, ← map_mul, ← map_mul, h a]
    congr 2
    rw [← _root_.mul_assoc, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]

end Count

/-- `u ∈ 𝒪` and the lift of its coordinates mod 3 differ by an element of `3𝒪`. -/
theorem exists_sub_liftO (u : O) : ∃ c : Fin 4 → ZMod 3, ∃ d : O, u - liftO c = 3 * d := by
  obtain ⟨n, hn⟩ := u.2
  refine ⟨fun i => (n i : ZMod 3), ⟨ofInt (fun i => n i / 3), _, rfl⟩, ?_⟩
  apply Subtype.ext
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  simp only [liftO, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33]
  rw [hn, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply, ZMod.val_intCast]
  have := Int.emod_def (n i) 3
  omega

/-- **The fibre count** (compiled, from the kernel's leaf `TorsionStructure` and aut-o-finite's
`autO_mod_inner_exact`): a twist fibre has at most `4 · 81 = 324` classes. -/
theorem twistFibre_count (hT : ObjBridge.TorsionStructure) (P : QML3 Qbar) :
    (twistFibre P).Finite ∧ (twistFibre P).ncard ≤ 324 := by
  classical
  obtain ⟨t, hcov, -⟩ := LeafQM.AV.Pin.Exact.autO_mod_inner_exact
  let F : Fin 4 × (Fin 4 → ZMod 3) → M3 Qbar := fun kc =>
    if h : ∃ e : Level3 (P.twist (t kc.1)).q,
        ∀ a, e.eta a = (P.twist (t kc.1)).e.eta (a * liftO kc.2) then
      M3.mk ⟨P.A, P.surface, (P.twist (t kc.1)).q, h.choose⟩
    else M3.mk P
  have hsub : twistFibre P ⊆ Set.range F := by
    rintro c ⟨Q, rfl, α, ⟨g⟩⟩
    obtain ⟨k, v, hv⟩ := hcov α
    let G : QMIso (P.twist (t k)).q Q.q := (innerIso P.q (t k) α v hv).symm.trans g
    let e₀ : Level3 (P.twist (t k)).q := pullLevel G Q.e
    obtain ⟨u₀, -, -, hu⟩ := Level3.torsor hT (P.twist (t k)) e₀
    obtain ⟨c, d, hd⟩ := exists_sub_liftO u₀
    have hc : ∀ a, (P.twist (t k)).e.eta (a * u₀) = (P.twist (t k)).e.eta (a * liftO c) := by
      intro a
      rw [(P.twist (t k)).e.eq_iff]
      refine ⟨a * d, ?_⟩
      rw [← _root_.mul_sub, hd]
      noncomm_ring
    have h : ∃ e : Level3 (P.twist (t k)).q,
        ∀ a, e.eta a = (P.twist (t k)).e.eta (a * liftO c) :=
      ⟨e₀, fun a => (hu a).trans (hc a)⟩
    refine ⟨(k, c), ?_⟩
    have he : h.choose = e₀ := Level3.ext' (AddMonoidHom.ext fun a =>
      (h.choose_spec a).trans ((hu a).trans (hc a)).symm)
    simp only [F, dif_pos h, he]
    exact Quotient.sound ⟨pullIso P.surface Q.surface G Q.e⟩
  have hfin : (Set.range F).Finite := Set.finite_range F
  refine ⟨hfin.subset hsub, ?_⟩
  calc (twistFibre P).ncard ≤ (Set.range F).ncard := Set.ncard_le_ncard hsub hfin
    _ = (F '' Set.univ).ncard := by rw [Set.image_univ]
    _ ≤ (Set.univ : Set (Fin 4 × (Fin 4 → ZMod 3))).ncard := Set.ncard_image_le
    _ = 324 := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]; simp

/-- Any two morphisms `Spec ℚ̄ → Spec ℚ` agree. -/
theorem specQbar_to_specQ_eq (f g : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of ℚ)) :
    f = g := by
  rw [← Spec.map_preimage f, ← Spec.map_preimage g]
  congr 1
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- **`HeckeDegree` from `GenericFibreCount` and the kernel's leaf `TorsionStructure`**
(compiled; aut-o-finite's computation inlined). -/
theorem heckeDegree_of (hG : GenericFibreCount) (hT : ObjBridge.TorsionStructure) :
    HeckeDegree := by
  intro Y Φ π _ _ h2 E _ _ _ _ _ _ hM
  obtain ⟨h, hO, -, hval⟩ := hM
  obtain ⟨t, s, hs, hst⟩ := hG E
  let pt : (integralClosure ℚ[X] E →+* Qbar) → (fieldPt Qbar ⟶ Y) := fun ψ =>
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (specQbar_to_specQ_eq _ _)
  have hpt_inj : Function.Injective pt := by
    intro ψ ψ' hψ
    have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ h = Spec.map (CommRingCat.ofHom ψ') ≫ h :=
      congrArg (fun y : fieldPt Qbar ⟶ Y => y.left) hψ
    have h2' := (cancel_mono h).1 h1
    have h3 := Spec.map_injective h2'
    exact congrArg CommRingCat.Hom.hom h3
  have hpt_val : ∀ ψ ∈ s, π.val (K := Qbar) (pt ψ).left = OnePoint.some (algebraMap ℚ Qbar t) := by
    intro ψ hψ
    show π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = _
    rw [hval ψ, hst ψ hψ]
  rcases s.eq_empty_or_nonempty with hs0 | ⟨ψ₀, hψ₀⟩
  · rw [hs0, Finset.card_empty] at hs
    omega
  set P : QML3 Qbar := Quotient.out (Φ Qbar (pt ψ₀)) with hPdef
  have hP : Φ Qbar (pt ψ₀) = M3.mk P := (Quotient.out_eq _).symm
  have hmem : ∀ ψ ∈ s, Φ Qbar (pt ψ) ∈ twistFibre P := by
    intro ψ hψ
    set Q : QML3 Qbar := Quotient.out (Φ Qbar (pt ψ)) with hQdef
    have hQ : Φ Qbar (pt ψ) = M3.mk Q := (Quotient.out_eq _).symm
    refine ⟨Q, hQ, ((h2 (pt ψ₀) (pt ψ) P Q hP hQ).1).1 ?_⟩
    rw [hpt_val ψ₀ hψ₀, hpt_val ψ hψ]
  obtain ⟨hfin, hcard⟩ := twistFibre_count hT P
  have hinj : Set.InjOn (fun ψ => Φ Qbar (pt ψ)) (s : Set _) :=
    fun ψ _ ψ' _ hψ => hpt_inj ((Φ Qbar).injective hψ)
  have := Set.ncard_le_ncard_of_injOn (fun ψ => Φ Qbar (pt ψ)) hmem hinj hfin
  rw [Set.ncard_coe_finset] at this
  omega

/-- **`GenericFibreCount` is proved** (`GFC.genericFibreCount` at `Ω = ℚ̄`, Mathlib only). -/
theorem genericFibreCount : GenericFibreCount := fun E _ _ _ _ _ => GFC.genericFibreCount Qbar E

/-- **`HeckeDegree` from the kernel's textbook leaf `TorsionStructure` alone** (compiled). -/
theorem heckeDegree_of_torsion (hT : ObjBridge.TorsionStructure) : HeckeDegree :=
  heckeDegree_of genericFibreCount hT

/-! ## Part 3: `HeckeNormalizationIrr`

The moduli-theoretic input is **fibre transitivity**: two `ℚ̄`-points with the same `π`-value
differ by an automorphism of `Y` coming from R1hecke (`twist α`, then `rightMul u`), and these
automorphisms preserve `π`. It is proved here from R1hecke, R2fp, the kernel's leaf
`TorsionStructure` (level torsor) and the surjectivity of `𝒪^× → (𝒪/3𝒪)^×` (`Units.lean`). What
is left is one statement of curve theory with no moduli in it, `CurveGaloisChart`; its Galois
property is proved below too (`curveGaloisChart_of`, from `TSHeckeGal.isGalois_of_transitive`), so
that only `CurveNormChart` (the normalization chart, no Galois) remains. -/

/-- **Fibre transitivity on classes** (compiled). -/
theorem fibre_transitive (hT : ObjBridge.TorsionStructure) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (y y' : fieldPt Qbar ⟶ Y)
    (hyy : π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left) :
    ∃ α : O ≃+* O, ∃ u : Oˣ, Φ Qbar y' = M3.rightMul u (M3.twist α (Φ Qbar y)) := by
  set P := Quotient.out (Φ Qbar y)
  set Q := Quotient.out (Φ Qbar y')
  have hP : Φ Qbar y = M3.mk P := (Quotient.out_eq _).symm
  have hQ : Φ Qbar y' = M3.mk Q := (Quotient.out_eq _).symm
  obtain ⟨α, ⟨G⟩⟩ := ((h2 y y' P Q hP hQ).1).1 hyy
  let e₀ : Level3 (P.twist α).q := pullLevel G Q.e
  obtain ⟨u₀, v₀, hvu, hu⟩ := Level3.torsor hT (P.twist α) e₀
  obtain ⟨u, d, hd⟩ := TSHeckeUnits.exists_unit_congr u₀ v₀ hvu
  refine ⟨α, u, ?_⟩
  have he : (P.twist α).e.rightMul u = e₀ := Level3.ext' (AddMonoidHom.ext fun a => by
    rw [hu a]
    show (P.twist α).e.eta (a * u) = (P.twist α).e.eta (a * u₀)
    rw [(P.twist α).e.eq_iff]
    exact ⟨-(a * d), by rw [← _root_.mul_sub, ← neg_sub, hd]; noncomm_ring⟩)
  rw [hQ, hP]
  show M3.mk Q = M3.mk ((P.twist α).rightMul u)
  have hiso : QML3.Iso ((P.twist α).rightMul u) Q := by
    show QML3.Iso ⟨P.A, P.surface, (P.twist α).q, (P.twist α).e.rightMul u⟩ Q
    rw [he]
    exact pullIso P.surface Q.surface G Q.e
  symm
  exact Quotient.sound ⟨hiso⟩

/-- **Fibre transitivity by automorphisms of `Y`** (compiled): two `ℚ̄`-points with the same
`π`-value differ by the composite of two automorphisms supplied by R1hecke. -/
theorem fibre_transitive_aut (hT : ObjBridge.TorsionStructure)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (hh : R1heckeProps Y Φ) (h2 : R2fpProps Y Φ π) (y y' : fieldPt Qbar ⟶ Y)
    (hyy : π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left) :
    ∃ (α : O ≃+* O) (u : Oˣ) (g₁ g₂ : Y ≅ Y),
      (∀ (K : Type) [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y),
        Φ K (z ≫ g₁.hom) = M3.twist α (Φ K z)) ∧
      (∀ (K : Type) [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y),
        Φ K (z ≫ g₂.hom) = M3.rightMul u (Φ K z)) ∧
      y' = y ≫ g₁.hom ≫ g₂.hom := by
  obtain ⟨α, u, hαu⟩ := fibre_transitive hT h2 y y' hyy
  obtain ⟨g₁, hg₁⟩ := hh.1 α
  obtain ⟨g₂, hg₂⟩ := hh.2 u
  refine ⟨α, u, g₁, g₂, hg₁, hg₂, (Φ Qbar).injective ?_⟩
  rw [hαu, ← Category.assoc, hg₂, hg₁]

/-- **The automorphisms of R1hecke preserve `π` on `ℚ̄`-points** (compiled; R2fp's fibre clause).
Twist case. -/
theorem pi_invariant_twist {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (α : O ≃+* O) (g : Y ≅ Y)
    (hg : ∀ (K : Type) [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y),
      Φ K (z ≫ g.hom) = M3.twist α (Φ K z)) (z : fieldPt Qbar ⟶ Y) :
    π.val (K := Qbar) (z ≫ g.hom).left = π.val (K := Qbar) z.left := by
  set P := Quotient.out (Φ Qbar z)
  set Q := Quotient.out (Φ Qbar (z ≫ g.hom))
  have hP : Φ Qbar z = M3.mk P := (Quotient.out_eq _).symm
  have hQ : Φ Qbar (z ≫ g.hom) = M3.mk Q := (Quotient.out_eq _).symm
  have hQP : M3.mk (P.twist α) = M3.mk Q := by rw [← hQ, hg, hP]; rfl
  obtain ⟨f⟩ := Quotient.exact hQP
  have hf : QMIso (P.q.twist α) Q.q := ⟨f.φ, f.ψ, f.left, f.right, f.equivariant⟩
  exact (((h2 z (z ≫ g.hom) P Q hP hQ).1).2 ⟨α, ⟨hf⟩⟩).symm

/-- `rightMul` case. -/
theorem pi_invariant_rightMul {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (u : Oˣ) (g : Y ≅ Y)
    (hg : ∀ (K : Type) [Field K] [Algebra ℚ K] (z : fieldPt K ⟶ Y),
      Φ K (z ≫ g.hom) = M3.rightMul u (Φ K z)) (z : fieldPt Qbar ⟶ Y) :
    π.val (K := Qbar) (z ≫ g.hom).left = π.val (K := Qbar) z.left := by
  set P := Quotient.out (Φ Qbar z)
  set Q := Quotient.out (Φ Qbar (z ≫ g.hom))
  have hP : Φ Qbar z = M3.mk P := (Quotient.out_eq _).symm
  have hQ : Φ Qbar (z ≫ g.hom) = M3.mk Q := (Quotient.out_eq _).symm
  have hQP : M3.mk (P.rightMul u) = M3.mk Q := by rw [← hQ, hg, hP]; rfl
  obtain ⟨f⟩ := Quotient.exact hQP
  have hf : QMIso (P.q.twist (RingEquiv.refl O)) Q.q :=
    ⟨f.φ, f.ψ, f.left, f.right, fun a => f.equivariant a⟩
  exact (((h2 z (z ≫ g.hom) P Q hP hQ).1).2 ⟨RingEquiv.refl O, ⟨hf⟩⟩).symm

/-- **The `π`-fibres on `ℚ̄`-points are finite** (compiled; `twistFibre_count`). -/
theorem fibre_finite (hT : ObjBridge.TorsionStructure) {Y : Over (Spec (CommRingCat.of ℚ))}
    {Φ : PtEquiv Y} {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (t : OnePoint Qbar) :
    {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite := by
  rcases Set.eq_empty_or_nonempty {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t} with
    h | ⟨y₀, hy₀⟩
  · rw [h]; exact Set.finite_empty
  set P := Quotient.out (Φ Qbar y₀)
  have hP : Φ Qbar y₀ = M3.mk P := (Quotient.out_eq _).symm
  refine Set.Finite.of_finite_image ((twistFibre_count hT P).1.subset ?_)
    ((Φ Qbar).injective.injOn)
  rintro _ ⟨y, hy, rfl⟩
  set Q := Quotient.out (Φ Qbar y)
  have hQ : Φ Qbar y = M3.mk Q := (Quotient.out_eq _).symm
  exact ⟨Q, hQ, ((h2 y₀ y P Q hP hQ).1).1 (hy₀.trans hy.symm)⟩

/-- **Glue (curve theory; h-b1 M1, M2, M8), with no moduli in it.** Let `Y` be a proper smooth
irreducible curve over `ℚ` and `π : Y → P¹` a morphism with finite fibres on `ℚ̄`-points, such
that any two `ℚ̄`-points with the same `π`-value differ by an automorphism of `Y` preserving `π` on
`ℚ̄`-points. Then there is a finite Galois `E/ℚ(X)` with `NormalizationModel Y π E`.
*Proof* (STANDARD; Hartshorne II.6.7-6.8, II.5.20 and Ex. II.3.5; Artin's theorem): `π` is
quasi-finite and proper, hence finite (EGA III 4.4.2 / Stacks 02OG); `Y` is normal (smooth), so
`π⁻¹(𝔸¹) = Spec B` with `B` the integral closure of `ℚ[X]` in `E = ℚ(Y)`; the `π`-preserving
automorphisms act on `E` over `ℚ(X)`, faithfully (`Y` integral and separated), and transitively on
a generic geometric fibre, which has `[E : ℚ(X)]` points (generic étaleness in characteristic 0),
so the group `G` they generate has `|G| ≥ [E : ℚ(X)] ≥ [E : E^G] = |G|`; hence `E^G = ℚ(X)` and
`E/ℚ(X)` is Galois (Artin). Locators UNVERIFIED. Glue, not a leaf. -/
def CurveGaloisChart : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → IrreducibleSpace Y.left →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    (∀ y y' : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left →
      ∃ g : Y ≅ Y, y' = y ≫ g.hom ∧
        ∀ z : fieldPt Qbar ⟶ Y, π.val (K := Qbar) (z ≫ g.hom).left = π.val (K := Qbar) z.left) →
    ∃ (E : Type) (_ : Field E) (_ : Algebra (RatFunc ℚ) E) (_ : Algebra ℚ[X] E)
      (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E) (_ : FiniteDimensional (RatFunc ℚ) E)
      (_ : IsGalois (RatFunc ℚ) E), NormalizationModel Y π E

/-- **Glue (curve theory; h-b1 M1, M8): the normalization chart, without the Galois property.**
For a proper smooth irreducible curve `Y/ℚ` and `π : Y → P¹` with finite `ℚ̄`-fibres there is a
finite `E/ℚ(X)` with `NormalizationModel Y π E`. *Proof* (STANDARD; Hartshorne II.6.7-6.8,
Stacks 02OG; locators UNVERIFIED): `π` is quasi-finite and proper, hence finite; `Y` is normal, so
`π⁻¹(𝔸¹) = Spec B` with `B` the integral closure of `ℚ[X]` in `E = ℚ(Y)`. Glue, not a leaf. -/
def CurveNormChart : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → IrreducibleSpace Y.left →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    ∃ (E : Type) (_ : Field E) (_ : Algebra (RatFunc ℚ) E) (_ : Algebra ℚ[X] E)
      (_ : IsScalarTower ℚ[X] (RatFunc ℚ) E) (_ : FiniteDimensional (RatFunc ℚ) E),
      NormalizationModel Y π E

/-- **`CurveGaloisChart` from `CurveNormChart`** (compiled): the Galois property follows from
fibre transitivity (`TSHeckeGal.isGalois_of_transitive`: the `π`-preserving automorphisms map the
chart into itself (Jacobson), induce automorphisms of `B` fixing `ℚ[X]` (separation by
`ℚ̄`-points) and of `E` over `ℚ(X)`, and act transitively on the `[E : ℚ(X)]` points of a generic
fibre, so `|Aut(E/ℚ(X))| = [E : ℚ(X)]`). -/
theorem curveGaloisChart_of (hN : CurveNormChart) : CurveGaloisChart := by
  intro Y π hP hS hI hfin htrans
  obtain ⟨E, i1, i2, i3, i4, i5, hM⟩ := hN Y π hP hS hI hfin
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  exact ⟨E, i1, i2, i3, i4, i5,
    TSHeckeGal.isGalois_of_transitive hM (genericFibreCount E) htrans, hM⟩

/-- **`HeckeNormalizationIrr` from `CurveGaloisChart` and the kernel's leaf `TorsionStructure`**
(compiled). -/
theorem heckeNormalizationIrr_of (hC : CurveGaloisChart) (hT : ObjBridge.TorsionStructure) :
    HeckeNormalizationIrr := by
  intro Y Φ π h1 hh h2 hI
  obtain ⟨hP, hS, -⟩ := h1
  refine hC Y π hP hS hI (fibre_finite hT h2) ?_
  intro y y' hyy
  obtain ⟨α, u, g₁, g₂, hg₁, hg₂, hy⟩ := fibre_transitive_aut hT hh h2 y y' hyy
  refine ⟨g₁ ≪≫ g₂, by rw [hy]; rfl, fun z => ?_⟩
  change π.val (K := Qbar) (z ≫ g₁.hom ≫ g₂.hom).left = _
  rw [← Category.assoc, pi_invariant_rightMul h2 u g₂ hg₂, pi_invariant_twist h2 α g₁ hg₁]

/-- **`HeckeNormalization` (both parts)** from the leaf R1conn, `CurveGaloisChart` and
`TorsionStructure` (compiled). -/
theorem heckeNormalization_of (hconn : Y3Connected) (hC : CurveGaloisChart)
    (hT : ObjBridge.TorsionStructure) : HeckeNormalization :=
  heckeNormalization_of_irr (heckeIrreducible_of_connected hconn) (heckeNormalizationIrr_of hC hT)

/-! ## Part 4: `HeckeBranch`

`e(Q) · #(geometric fibre) = [E : ℚ(X)]` for a Galois extension (`RamOfFibreCount`, algebra); the
geometric fibres of `Spec B → 𝔸¹` (and of the chart at `∞`) are the `π`-fibres of `Y`
(`chart_count`, compiled from `NormalizationModel`; `CurveChartInf`, curve theory, at `∞`); a
`π`-fibre is a twist fibre (`fibre_ncard`, compiled); and the twist fibres have the sizes of the
Baba–Granath elliptic table (`HeckeFibreSizes`, the moduli input). -/

/-- **Glue (commutative algebra; fundamental identity for a Galois extension).** Let `E/ℚ(X)` be
finite Galois and `B` the integral closure of `ℚ[X]` in `E`. (a) A prime over `0` has
ramification index `1` (it is `0`). (b) For `t ∈ ℚ̄` and a prime `Q` of `B` over the kernel of
`ℚ[X] → ℚ̄`, `X ↦ t`: `e(Q) · #{ψ : B → ℚ̄ | ψ(X) = t} = [E : ℚ(X)]`. (c) The same at `∞` for the
integral closure of `ℚ[s]` (`s = 1/X`) and `t = 0`. *Proof* (STANDARD: Serre, *Local Fields*,
I §7 Prop. 21 and I §4; Neukirch I.9.3; locators UNVERIFIED): `B` is a Dedekind domain; Galois
acts transitively on the primes over `P`, so all have the same `e` and `f`, and `e f g = n`; the
residue extensions are separable (characteristic 0), so a prime `Q'` over `P` contributes
`f` maps `B/Q' → ℚ̄` over a fixed `ℚ[X]/P → ℚ̄`; hence the number of `ψ` is `g f = n / e`. Mathlib
has the fundamental identity (`Ideal.sum_ramification_inertia`) and its Galois form. Glue. -/
def RamOfFibreCount : Prop :=
  ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E],
    (∀ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime → Q.under ℚ[X] = ⊥ →
      Q.ramificationIdx ℚ[X] = 1) ∧
    (∀ (t : Qbar) (Q : Ideal (integralClosure ℚ[X] E)), Q.IsPrime →
      Q.under ℚ[X] = RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t) →
      Q.ramificationIdx ℚ[X] *
        {ψ : integralClosure ℚ[X] E →+* Qbar |
          ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = t}.ncard =
        Module.finrank (RatFunc ℚ) E) ∧
    (letI := infAlg E
      ∀ Q : Ideal (integralClosure InfCoord E), Q.IsPrime →
        Q.under InfCoord = Ideal.span {infUnif} →
        Q.ramificationIdx InfCoord *
          {ψ : integralClosure InfCoord E →+* Qbar |
            ψ (algebraMap InfCoord (integralClosure InfCoord E) infUnif) = 0}.ncard =
          Module.finrank (RatFunc ℚ) E)

/-- **The normalization chart at `∞`**: an open immersion `Spec B_∞ → Y` (`B_∞` the integral
closure of `ℚ[s]`, `s = 1/X`, in `E`) whose image contains every `ℚ̄`-point with `π ≠ 0`, along
which `π = ∞` exactly where `s = 0`. -/
def NormalizationModelInf (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) (E : Type)
    [Field E] [Algebra (RatFunc ℚ) E] : Prop :=
  letI := infAlg E
  ∃ h : Spec (CommRingCat.of (integralClosure InfCoord E)) ⟶ Y.left, IsOpenImmersion h ∧
    (∀ y : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) y ≠ OnePoint.some 0 →
      ∃ y' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of (integralClosure InfCoord E)),
        y = y' ≫ h) ∧
    ∀ ψ : integralClosure InfCoord E →+* Qbar,
      (π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = OnePoint.infty ↔
        ψ (algebraMap InfCoord (integralClosure InfCoord E) infUnif) = 0)

/-- **Glue (curve theory): the chart at `∞`.** For a proper smooth curve `Y/ℚ` and `π : Y → P¹`
with finite `ℚ̄`-fibres, a field `E` carrying the chart over `𝔸¹` (`NormalizationModel`) also
carries the chart over `P¹ ∖ {0}`. *Proof* (STANDARD; Hartshorne II.6.7-6.8): finite fibres force
every component of `Y` to meet `π⁻¹(𝔸¹) ≅ Spec B`, so `Y` is irreducible with function field `E`;
`π` is finite and `Y` normal, so `π⁻¹(P¹ ∖ {0}) = Spec B_∞`, with `s = 1/π` there. Glue. -/
def CurveChartInf : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E],
      NormalizationModel Y π E → NormalizationModelInf Y π E

/-- **The moduli input: sizes of the twist fibres** (the shape of Baba–Granath's elliptic table).
There is `M` (it is `144 = |Γ'|`) such that the twist fibre of an object without CM by `ℤ[i]`,
`ℤ[ζ₃]` or `ℤ[√−6]` has exactly `M` classes, and at objects with CM by
`ℤ[i]` (resp. `ℤ[ζ₃]`, `ℤ[√−6]`) `M` divides `4` (resp. `6`, `2`) times the fibre size (the
expected sizes are `36`, `24`, `72`). *Count*: a fixed pair `(A, ι)` over `ℚ̄` has
`72 = |(𝒪/3𝒪)^×|` level structures, permuted freely by `com(ι)^×/{±1}` (trivial unless CM by
`ℤ[i]` or `ℤ[ζ₃]`); `Aut(𝒪)/Inn(𝒪^×) = W` has order 4 and acts freely on the pairs except at CM by
`ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` (stabilizers `⟨w₂⟩`, `⟨w₃⟩`, `⟨w₆⟩`); CM points of discriminants `−8`
and `−12` do not exist on `X₆` (`3` splits in `ℚ(√−2)`; `2` divides conductor and discriminant).
So the sizes are `4·36 = 144`, `2·18 = 36`, `2·12 = 24`, `2·36 = 72`. *Source*: the fibre of
`Y₃ → P¹` through a point `y` has
`|Γ'| / |Stab(y)|` points; `Stab(y)` is trivial off the elliptic points of `Γ*`, whose orders are
`4, 6, 2` at the CM points of discriminants `−4, −3, −24` (Baba–Granath, Canad. J. Math. 60
(2008), §3.1, the elliptic-order table, p. 740 per docs/research/locators.md; signature
`(0; 2, 4, 6)`); the complete list of elliptic elements of the normalizer (h-b1 M9, VERIFIED by
`scratch/rv-h-b1/rv_checks.py`) shows that every point with a nontrivial stabilizer has CM by one of
the three maximal orders; `Γ₃` is torsion-free (`−1 ∉ K₃`). Glue from leaves (Shimura's
uniformization and Baba–Granath). -/
def HeckeFibreSizes : Prop :=
  ∃ M : ℕ,
    (∀ P : QML3 Qbar, ¬ HasCM4 P.q → ¬ HasCM3 P.q → ¬ HasCM24 P.q →
      (twistFibre P).ncard = M) ∧
    (∀ P : QML3 Qbar, HasCM4 P.q → M ∣ 4 * (twistFibre P).ncard) ∧
    (∀ P : QML3 Qbar, HasCM3 P.q → M ∣ 6 * (twistFibre P).ncard) ∧
    (∀ P : QML3 Qbar, HasCM24 P.q → M ∣ 2 * (twistFibre P).ncard)

/-- The `ℚ̄`-points of `Spec B` over `t` are the `π`-fibre over `t` (compiled). -/
theorem chart_count {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left} {E : Type} [Field E]
    [Algebra ℚ[X] E] (hM : NormalizationModel Y π E) (t : Qbar) :
    {ψ : integralClosure ℚ[X] E →+* Qbar |
        ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = t}.ncard =
      {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = OnePoint.some t}.ncard := by
  obtain ⟨h, hO, himg, hval⟩ := hM
  let pt : (integralClosure ℚ[X] E →+* Qbar) → (fieldPt Qbar ⟶ Y) := fun ψ =>
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (specQbar_to_specQ_eq _ _)
  refine Set.ncard_congr (fun ψ _ => pt ψ) ?_ ?_ ?_
  · intro ψ hψ
    show π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = _
    rw [hval ψ, hψ]
  · intro ψ ψ' _ _ hψ
    have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ h = Spec.map (CommRingCat.ofHom ψ') ≫ h :=
      congrArg (fun y : fieldPt Qbar ⟶ Y => y.left) hψ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono h).1 h1))
  · intro y hy
    obtain ⟨y', hy'⟩ := himg y.left (by rw [hy]; exact OnePoint.coe_ne_infty _)
    refine ⟨(Spec.preimage y').hom, ?_, ?_⟩
    · have := hval (Spec.preimage y').hom
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, ← hy', hy] at this
      exact (OnePoint.coe_injective this).symm
    · apply Over.OverMorphism.ext
      show Spec.map (CommRingCat.ofHom (Spec.preimage y').hom) ≫ h = y.left
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, ← hy']

/-- The same at `∞` (compiled). -/
theorem chart_count_inf {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left} {E : Type}
    [Field E] [Algebra (RatFunc ℚ) E] (hM : NormalizationModelInf Y π E) :
    letI := infAlg E
    {ψ : integralClosure InfCoord E →+* Qbar |
        ψ (algebraMap InfCoord (integralClosure InfCoord E) infUnif) = 0}.ncard =
      {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = OnePoint.infty}.ncard := by
  letI := infAlg E
  obtain ⟨h, hO, himg, hval⟩ := hM
  let pt : (integralClosure InfCoord E →+* Qbar) → (fieldPt Qbar ⟶ Y) := fun ψ =>
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (specQbar_to_specQ_eq _ _)
  refine Set.ncard_congr (fun ψ _ => pt ψ) ?_ ?_ ?_
  · intro ψ hψ
    exact (hval ψ).2 hψ
  · intro ψ ψ' _ _ hψ
    have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ h = Spec.map (CommRingCat.ofHom ψ') ≫ h :=
      congrArg (fun y : fieldPt Qbar ⟶ Y => y.left) hψ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono h).1 h1))
  · intro y hy
    obtain ⟨y', hy'⟩ := himg y.left (by
      change π.val (K := Qbar) y.left = OnePoint.infty at hy
      rw [hy]; exact OnePoint.infty_ne_coe _)
    refine ⟨(Spec.preimage y').hom, ?_, ?_⟩
    · apply (hval (Spec.preimage y').hom).1
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, ← hy']
      exact hy
    · apply Over.OverMorphism.ext
      show Spec.map (CommRingCat.ofHom (Spec.preimage y').hom) ≫ h = y.left
      rw [CommRingCat.ofHom_hom, Spec.map_preimage, ← hy']

/-- A `π`-fibre on `ℚ̄`-points is a twist fibre (compiled). -/
theorem fibre_ncard {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (h2 : R2fpProps Y Φ π) (y₀ : fieldPt Qbar ⟶ Y) :
    {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = π.val (K := Qbar) y₀.left}.ncard =
      (twistFibre (Quotient.out (Φ Qbar y₀))).ncard := by
  set P := Quotient.out (Φ Qbar y₀)
  have hP : Φ Qbar y₀ = M3.mk P := (Quotient.out_eq _).symm
  rw [← Set.ncard_image_of_injective _ (Φ Qbar).injective]
  congr 1
  ext c
  constructor
  · rintro ⟨y, hy, rfl⟩
    set Q := Quotient.out (Φ Qbar y)
    have hQ : Φ Qbar y = M3.mk Q := (Quotient.out_eq _).symm
    exact ⟨Q, hQ, ((h2 y₀ y P Q hP hQ).1).1 hy.symm⟩
  · rintro ⟨Q, rfl, hα⟩
    refine ⟨(Φ Qbar).symm (M3.mk Q), ?_, Equiv.apply_symm_apply _ _⟩
    exact (((h2 y₀ _ P Q hP (Equiv.apply_symm_apply _ _)).1).2 hα).symm

/-- The kernel of evaluation at a rational point (compiled). -/
theorem ker_eval_rat (b : ℚ) :
    RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) (algebraMap ℚ Qbar b)) =
      Ideal.span {X - C b} := by
  rw [← Polynomial.ker_evalRingHom]
  ext p
  simp only [RingHom.mem_ker, Polynomial.coe_eval₂RingHom, Polynomial.coe_evalRingHom]
  rw [Polynomial.eval₂_at_apply, map_eq_zero_iff _ (algebraMap ℚ Qbar).injective]

/-- A nonzero prime of `ℚ[X]` is the kernel of evaluation at some `t ∈ ℚ̄` (compiled). -/
theorem exists_ker_eval (P : Ideal ℚ[X]) [hP : P.IsPrime] (h0 : P ≠ ⊥) :
    ∃ t : Qbar, P = RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t) := by
  have hmax : P.IsMaximal := hP.isMaximal h0
  obtain ⟨p, rfl⟩ := (Submodule.IsPrincipal.principal P)
  have hp0 : p ≠ 0 := by rintro rfl; exact h0 (by simp)
  have hdeg : (p.map (algebraMap ℚ Qbar)).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    intro hd
    rw [Polynomial.eq_C_of_degree_eq_zero hd] at hmax
    apply hmax.ne_top
    rw [Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
    have : p.coeff 0 ≠ 0 := by
      intro hc; apply hp0; rw [Polynomial.eq_C_of_degree_eq_zero hd, hc, map_zero]
    exact Polynomial.isUnit_C.2 (Ne.isUnit this)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hdeg
  refine ⟨t, hmax.eq_of_le (RingHom.ker_ne_top _) ?_⟩
  rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
  show Polynomial.eval₂ (algebraMap ℚ Qbar) t p = 0
  rw [← Polynomial.eval_map]
  exact ht

/-- `[E : ℚ(X)]` is at most the size of some twist fibre (compiled; the argument of
`heckeDegree_of`). -/
theorem finrank_le_twistFibre {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (hT : ObjBridge.TorsionStructure) (h2 : R2fpProps Y Φ π)
    (hne : Nonempty (fieldPt Qbar ⟶ Y)) (E : Type)
    [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E] [IsScalarTower ℚ[X] (RatFunc ℚ) E]
    [FiniteDimensional (RatFunc ℚ) E] (hM : NormalizationModel Y π E) :
    ∃ P : QML3 Qbar, Module.finrank (RatFunc ℚ) E ≤ (twistFibre P).ncard := by
  obtain ⟨h, hO, -, hval⟩ := hM
  obtain ⟨t, s, hs, hst⟩ := genericFibreCount E
  let pt : (integralClosure ℚ[X] E →+* Qbar) → (fieldPt Qbar ⟶ Y) := fun ψ =>
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (specQbar_to_specQ_eq _ _)
  have hpt_inj : Function.Injective pt := by
    intro ψ ψ' hψ
    have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ h = Spec.map (CommRingCat.ofHom ψ') ≫ h :=
      congrArg (fun y : fieldPt Qbar ⟶ Y => y.left) hψ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono h).1 h1))
  have hpt_val : ∀ ψ ∈ s, π.val (K := Qbar) (pt ψ).left =
      OnePoint.some (algebraMap ℚ Qbar t) := by
    intro ψ hψ
    show π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = _
    rw [hval ψ, hst ψ hψ]
  rcases s.eq_empty_or_nonempty with hs0 | ⟨ψ₀, hψ₀⟩
  · obtain ⟨y⟩ := hne
    refine ⟨Quotient.out (Φ Qbar y), ?_⟩
    rw [hs0, Finset.card_empty] at hs
    omega
  set P : QML3 Qbar := Quotient.out (Φ Qbar (pt ψ₀))
  have hP : Φ Qbar (pt ψ₀) = M3.mk P := (Quotient.out_eq _).symm
  have hmem : ∀ ψ ∈ s, Φ Qbar (pt ψ) ∈ twistFibre P := by
    intro ψ hψ
    set Q : QML3 Qbar := Quotient.out (Φ Qbar (pt ψ))
    have hQ : Φ Qbar (pt ψ) = M3.mk Q := (Quotient.out_eq _).symm
    refine ⟨Q, hQ, ((h2 (pt ψ₀) (pt ψ) P Q hP hQ).1).1 ?_⟩
    rw [hpt_val ψ₀ hψ₀, hpt_val ψ hψ]
  have hinj : Set.InjOn (fun ψ => Φ Qbar (pt ψ)) (s : Set _) :=
    fun ψ _ ψ' _ hψ => hpt_inj ((Φ Qbar).injective hψ)
  have := Set.ncard_le_ncard_of_injOn (fun ψ => Φ Qbar (pt ψ)) hmem hinj
    (twistFibre_count hT P).1
  rw [Set.ncard_coe_finset] at this
  exact ⟨P, hs.trans this⟩

/-- `[E : ℚ(X)]` is at most the size of the twist fibre through a point over a value `t` given by
`GenericFibreCount` (compiled). -/
theorem finrank_le_twistFibre_of {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (hT : ObjBridge.TorsionStructure) (h2 : R2fpProps Y Φ π) (E : Type)
    [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E] [IsScalarTower ℚ[X] (RatFunc ℚ) E]
    [FiniteDimensional (RatFunc ℚ) E] (hM : NormalizationModel Y π E) (t : ℚ)
    (s : Finset (integralClosure ℚ[X] E →+* Qbar)) (hs : Module.finrank (RatFunc ℚ) E ≤ s.card)
    (hst : ∀ ψ ∈ s, ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = algebraMap ℚ Qbar t) :
    ∃ y : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar t) ∧
      Module.finrank (RatFunc ℚ) E ≤ (twistFibre (Quotient.out (Φ Qbar y))).ncard := by
  obtain ⟨h, hO, -, hval⟩ := hM
  let pt : (integralClosure ℚ[X] E →+* Qbar) → (fieldPt Qbar ⟶ Y) := fun ψ =>
    Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ h) (specQbar_to_specQ_eq _ _)
  have hpt_inj : Function.Injective pt := by
    intro ψ ψ' hψ
    have h1 : Spec.map (CommRingCat.ofHom ψ) ≫ h = Spec.map (CommRingCat.ofHom ψ') ≫ h :=
      congrArg (fun y : fieldPt Qbar ⟶ Y => y.left) hψ
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono h).1 h1))
  have hpt_val : ∀ ψ ∈ s, π.val (K := Qbar) (pt ψ).left =
      OnePoint.some (algebraMap ℚ Qbar t) := by
    intro ψ hψ
    show π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) = _
    rw [hval ψ, hst ψ hψ]
  have hnpos : 0 < Module.finrank (RatFunc ℚ) E := Module.finrank_pos
  obtain ⟨ψ₀, hψ₀⟩ : s.Nonempty := by rw [← Finset.card_pos]; omega
  set P : QML3 Qbar := Quotient.out (Φ Qbar (pt ψ₀))
  have hP : Φ Qbar (pt ψ₀) = M3.mk P := (Quotient.out_eq _).symm
  have hmem : ∀ ψ ∈ s, Φ Qbar (pt ψ) ∈ twistFibre P := by
    intro ψ hψ
    set Q : QML3 Qbar := Quotient.out (Φ Qbar (pt ψ))
    have hQ : Φ Qbar (pt ψ) = M3.mk Q := (Quotient.out_eq _).symm
    refine ⟨Q, hQ, ((h2 (pt ψ₀) (pt ψ) P Q hP hQ).1).1 ?_⟩
    rw [hpt_val ψ₀ hψ₀, hpt_val ψ hψ]
  have hinj : Set.InjOn (fun ψ => Φ Qbar (pt ψ)) (s : Set _) :=
    fun ψ _ ψ' _ hψ => hpt_inj ((Φ Qbar).injective hψ)
  have := Set.ncard_le_ncard_of_injOn (fun ψ => Φ Qbar (pt ψ)) hmem hinj
    (twistFibre_count hT P).1
  rw [Set.ncard_coe_finset] at this
  exact ⟨pt ψ₀, hpt_val ψ₀ hψ₀, hs.trans this⟩

/-- `HasCM4` and its kin pass along isomorphisms of objects. -/
def qmIso_of_iso {P Q : QML3 Qbar} (f : P.Iso Q) : QMIso P.q Q.q :=
  ⟨f.φ, f.ψ, f.left, f.right, f.equivariant⟩

theorem algebraMap_m16_27 : algebraMap ℚ Qbar (-16 / 27) = -16 / 27 := by
  rw [map_div₀, map_neg, map_ofNat, map_ofNat]

/-- The CM point of a CM object (compiled): for an object `P₀`, the point `y₀ = Φ⁻¹[P₀]` and its
class representative `P = out(Φ y₀)`, with an isomorphism `P₀ ≅ P`. -/
theorem out_iso {Y : Over (Spec (CommRingCat.of ℚ))} (Φ : PtEquiv Y) (P₀ : QML3 Qbar) :
    Nonempty (P₀.Iso (Quotient.out (Φ Qbar ((Φ Qbar).symm (M3.mk P₀))))) := by
  rw [Equiv.apply_symm_apply]
  exact Quotient.exact (Quotient.out_eq (M3.mk P₀)).symm

/-- **`HeckeBranch` from `RamOfFibreCount`, `CurveChartInf`, `HeckeFibreSizes`, the kernel's
leaf `TorsionStructure` and the existence of the three CM objects** (compiled; the CM objects
come from the bundle leaf `R1R2fp`, `Pin.cm_objects_of_R1R2fp`). -/
theorem heckeBranch_of (hR : RamOfFibreCount) (hCI : CurveChartInf) (hF : HeckeFibreSizes)
    (hT : ObjBridge.TorsionStructure)
    (hCM : (∃ P : QML3 Qbar, HasCM4 P.q) ∧ (∃ P : QML3 Qbar, HasCM3 P.q) ∧
      (∃ P : QML3 Qbar, HasCM24 P.q)) : HeckeBranch := by
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hM
  obtain ⟨M, hgen, h4, h3, h24⟩ := hF
  obtain ⟨hR0, hRfin, hRinf⟩ := hR E
  obtain ⟨⟨P₄, c₄⟩, ⟨P₃, c₃⟩, ⟨P₂₄, c₂₄⟩⟩ := hCM
  have hfinite := fibre_finite hT h2
  have hMinf := hCI Y π h1.1 h1.2.1 hfinite E hM
  have hnpos : 0 < Module.finrank (RatFunc ℚ) E := Module.finrank_pos
  -- the fibre count over a finite value `t`, through a point of the fibre
  have hfib : ∀ (t : Qbar) (y : fieldPt Qbar ⟶ Y), π.val (K := Qbar) y.left = OnePoint.some t →
      {ψ : integralClosure ℚ[X] E →+* Qbar |
        ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = t}.ncard =
        (twistFibre (Quotient.out (Φ Qbar y))).ncard := by
    intro t y hy
    rw [chart_count hM t, ← hy, fibre_ncard h2 y]
  -- a nonempty fibre from a positive count
  have hne : ∀ (t : Qbar) (Q : Ideal (integralClosure ℚ[X] E)), Q.IsPrime →
      Q.under ℚ[X] = RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t) →
      ∃ y : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = OnePoint.some t := by
    intro t Q hQ hQt
    have h := hRfin t Q hQ hQt
    have hc : {ψ : integralClosure ℚ[X] E →+* Qbar |
        ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) = t}.ncard ≠ 0 := by
      intro h0; rw [h0, mul_zero] at h; omega
    rw [chart_count hM t] at hc
    exact Set.nonempty_of_ncard_ne_zero hc
  -- a generic finite value has fibre size `M`
  have hgenfib : ∀ (t : Qbar) (y : fieldPt Qbar ⟶ Y), π.val (K := Qbar) y.left = OnePoint.some t →
      t ≠ 0 → t ≠ algebraMap ℚ Qbar (-16 / 27) →
      (twistFibre (Quotient.out (Φ Qbar y))).ncard = M := by
    intro t y hy ht0 ht1
    set P := Quotient.out (Φ Qbar y)
    have hP : Φ Qbar y = M3.mk P := (Quotient.out_eq _).symm
    obtain ⟨-, hc4, hc3, hc24⟩ := h2 y y P P hP hP
    refine hgen P (fun h => ht0 ?_) (fun h => ?_) (fun h => ht1 ?_)
    · have := (hy.symm.trans (hc4 h)); exact OnePoint.coe_injective this
    · exact OnePoint.coe_ne_infty _ (hy.symm.trans (hc3 h))
    · have := OnePoint.coe_injective (hy.symm.trans (hc24 h))
      rw [this, algebraMap_m16_27]
  -- `n ≤ M`, through a generic rational value given by `GenericFibreCount`
  have hnM : Module.finrank (RatFunc ℚ) E ≤ M := by
    obtain ⟨t₀, ht₀S, s₀, hs₀, hst₀⟩ := GFC.genericFibreCountAvoid Qbar E {0, -16 / 27}
    obtain ⟨y₀, hy₀, hle₀⟩ := finrank_le_twistFibre_of hT h2 E hM t₀ s₀ hs₀ hst₀
    rw [hgenfib _ y₀ hy₀ (fun h => ht₀S (by
        rw [← map_zero (algebraMap ℚ Qbar)] at h
        simp [(algebraMap ℚ Qbar).injective h]))
      (fun h => ht₀S (by simp [(algebraMap ℚ Qbar).injective h]))] at hle₀
    exact hle₀
  -- `n = M`, through the value `1`
  have hnM' : Module.finrank (RatFunc ℚ) E = M := by
    have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
      intro a b hab
      have h' := congrArg Subtype.val hab
      change algebraMap ℚ[X] E a = algebraMap ℚ[X] E b at h'
      rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
        IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E b] at h'
      exact IsFractionRing.injective ℚ[X] (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h')
    haveI : (RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) 1)).IsPrime :=
      RingHom.ker_isPrime _
    obtain ⟨Q₁, -, hQ₁, hQ₁u⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) 1)) (⊥ : Ideal (integralClosure ℚ[X] E))
      (Ideal.comap_bot_le_of_injective _ hinjB)
    have h := hRfin 1 Q₁ hQ₁ hQ₁u
    obtain ⟨y₁, hy₁⟩ := hne 1 Q₁ hQ₁ hQ₁u
    rw [hfib 1 y₁ hy₁, hgenfib 1 y₁ hy₁ one_ne_zero (by
      rw [← map_one (algebraMap ℚ Qbar)]
      exact fun h => absurd ((algebraMap ℚ Qbar).injective h) (by norm_num))] at h
    have hM0 : 0 < M := lt_of_lt_of_le hnpos hnM
    have he : Q₁.ramificationIdx ℚ[X] ≤ 1 := by
      by_contra hc
      push Not at hc
      have : 2 * M ≤ Q₁.ramificationIdx ℚ[X] * M := Nat.mul_le_mul_right M hc
      omega
    interval_cases (Q₁.ramificationIdx ℚ[X]) <;> omega
  -- the three clauses
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ hS
    by_cases h0 : Q.under ℚ[X] = ⊥
    · exact hR0 Q hQ h0
    haveI : (Q.under ℚ[X]).IsPrime := Ideal.IsPrime.under ℚ[X] Q
    obtain ⟨t, ht⟩ := exists_ker_eval (Q.under ℚ[X]) h0
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hS 0 (by simp)
      rw [ht, ← map_zero (algebraMap ℚ Qbar), ker_eval_rat]
    have ht1 : t ≠ algebraMap ℚ Qbar (-16 / 27) := by
      rintro rfl
      apply hS (-16 / 27) (by simp)
      rw [ht, ker_eval_rat]
    obtain ⟨y, hy⟩ := hne t Q hQ ht
    have h := hRfin t Q hQ ht
    rw [hfib t y hy, hgenfib t y hy ht0 ht1, ← hnM'] at h
    have : Q.ramificationIdx ℚ[X] * Module.finrank (RatFunc ℚ) E =
        1 * Module.finrank (RatFunc ℚ) E := by rw [h, _root_.one_mul]
    exact Nat.eq_of_mul_eq_mul_right hnpos this
  · intro b hb Q hQ hQb
    have hQb' : Q.under ℚ[X] =
        RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) (algebraMap ℚ Qbar b)) := by
      rw [ker_eval_rat]; exact hQb
    have h := hRfin _ Q hQ hQb'
    -- the CM object over `b` and its fibre
    have key : ∀ (P₁ : QML3 Qbar) (k : ℕ),
        π.val (K := Qbar) ((Φ Qbar).symm (M3.mk P₁)).left = OnePoint.some (algebraMap ℚ Qbar b) →
        M ∣ k * (twistFibre (Quotient.out (Φ Qbar ((Φ Qbar).symm (M3.mk P₁))))).ncard →
        Q.ramificationIdx ℚ[X] ∣ k := by
      intro P₁ k hπ hdvd
      rw [hfib _ _ hπ, hnM'] at h
      set F := (twistFibre (Quotient.out (Φ Qbar ((Φ Qbar).symm (M3.mk P₁))))).ncard
      have hF0 : 0 < F := by
        rcases Nat.eq_zero_or_pos F with hF | hF
        · rw [hF, mul_zero] at h; omega
        · exact hF
      rw [← h] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_right hF0 hdvd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · -- `b = 0`: CM by `ℤ[i]`, index `4`
      obtain ⟨f⟩ := out_iso Φ P₄
      have hπ : π.val (K := Qbar) ((Φ Qbar).symm (M3.mk P₄)).left =
          OnePoint.some (algebraMap ℚ Qbar 0) := by
        rw [map_zero]
        exact ((h2 _ _ P₄ P₄ (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _)).2.1) c₄
      have := key P₄ 4 hπ (h4 _ (HasCM4.of_iso (qmIso_of_iso f) c₄))
      simpa [nY3] using this
    · -- `b = −16/27`: CM by `ℤ[√−6]`, index `2`
      obtain ⟨f⟩ := out_iso Φ P₂₄
      have hπ : π.val (K := Qbar) ((Φ Qbar).symm (M3.mk P₂₄)).left =
          OnePoint.some (algebraMap ℚ Qbar (-16 / 27)) := by
        rw [((h2 _ _ P₂₄ P₂₄ (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _)).2.2.2) c₂₄,
          algebraMap_m16_27]
      have := key P₂₄ 2 hπ (h24 _ (HasCM24.of_iso (qmIso_of_iso f) c₂₄))
      simpa [nY3] using this
  · -- `∞`: CM by `ℤ[ζ₃]`, index `6`
    letI := infAlg E
    intro Q hQ hQs
    have h := hRinf Q hQ hQs
    obtain ⟨f⟩ := out_iso Φ P₃
    set y₃ := (Φ Qbar).symm (M3.mk P₃)
    have hπ : π.val (K := Qbar) y₃.left = OnePoint.infty :=
      ((h2 _ _ P₃ P₃ (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _)).2.2.1) c₃
    rw [chart_count_inf hMinf, ← hπ, fibre_ncard h2 y₃, hnM'] at h
    have hdvd := h3 _ (HasCM3.of_iso (qmIso_of_iso f) c₃)
    set F := (twistFibre (Quotient.out (Φ Qbar y₃))).ncard
    have hF0 : 0 < F := by
      rcases Nat.eq_zero_or_pos F with hF | hF
      · rw [hF, mul_zero] at h; omega
      · exact hF
    rw [← h] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_right hF0 hdvd

/-! ### `RamOfFibreCount` is proved (from `RamCount.ramCount`) -/

/-- `ℚ(X)` is the fraction field of `ℚ[s]` through `s ↦ X⁻¹` (compiled). -/
theorem isFractionRing_infCoord : IsFractionRing InfCoord (RatFunc ℚ) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  letI : Invertible (RatFunc.X : RatFunc ℚ) := invertibleOfNonzero hX
  have hev : Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) RatFunc.X =
      algebraMap ℚ[X] (RatFunc ℚ) :=
    Polynomial.ringHom_ext (fun a => RingHom.congr_fun (Subsingleton.elim
      ((Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) RatFunc.X).comp Polynomial.C)
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp Polynomial.C)) a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RatFunc.algebraMap_X])
  have key : ∀ (N : ℕ) (f : ℚ[X]), f.natDegree ≤ N →
      algebraMap InfCoord (RatFunc ℚ) (Polynomial.reflect N f : ℚ[X]) * RatFunc.X ^ N =
        algebraMap ℚ[X] (RatFunc ℚ) f := by
    intro N f hf
    change Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X⁻¹) (Polynomial.reflect N f) *
      RatFunc.X ^ N = _
    rw [show (RatFunc.X⁻¹ : RatFunc ℚ) = ⅟RatFunc.X from (invOf_eq_inv _).symm,
      Polynomial.eval₂_reflect_mul_pow _ _ N f hf, ← hev, Polynomial.coe_eval₂RingHom]
  have hinj : Function.Injective (algebraMap InfCoord (RatFunc ℚ)) := by
    rw [injective_iff_map_eq_zero]
    show ∀ p : ℚ[X], algebraMap InfCoord (RatFunc ℚ) p = 0 → p = 0
    intro p hp
    have h1 := Polynomial.eval₂_reflect_mul_pow (algebraMap ℚ (RatFunc ℚ)) RatFunc.X p.natDegree
      (Polynomial.reflect p.natDegree p) (Polynomial.natDegree_reflect_le.trans (by simp))
    rw [Polynomial.reflect_reflect] at h1
    have hp' : Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (⅟RatFunc.X) p = 0 := by
      rw [invOf_eq_inv]; exact hp
    rw [hp', zero_mul, ← Polynomial.coe_eval₂RingHom, hev] at h1
    have h2 := (map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).1 h1.symm
    rwa [Polynomial.reflect_eq_zero_iff] at h2
  haveI : FaithfulSMul InfCoord (RatFunc ℚ) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine IsFractionRing.of_field InfCoord (RatFunc ℚ) fun z => ?_
  set N := max (RatFunc.num z).natDegree (RatFunc.denom z).natDegree
  refine ⟨(Polynomial.reflect N (RatFunc.num z) : ℚ[X]),
    (Polynomial.reflect N (RatFunc.denom z) : ℚ[X]), ?_⟩
  have h1 := key N (RatFunc.num z) (le_max_left _ _)
  have h2 := key N (RatFunc.denom z) (le_max_right _ _)
  have hXN : (RatFunc.X : RatFunc ℚ) ^ N ≠ 0 := pow_ne_zero _ hX
  calc z = algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.num z) /
        algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.denom z) := (RatFunc.num_div_denom z).symm
    _ = _ := by rw [← h1, ← h2, mul_div_mul_right _ _ hXN]

/-- **`RamOfFibreCount` is proved** (compiled; `RamCount.ramCount` at `ℚ[X]` and at `ℚ[s]`). -/
theorem ramOfFibreCount : RamOfFibreCount := by
  intro E _ _ _ _ _ _
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b hab
    have h' := congrArg Subtype.val hab
    change algebraMap ℚ[X] E a = algebraMap ℚ[X] E b at h'
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E,
      IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E b] at h'
    exact IsFractionRing.injective ℚ[X] (RatFunc ℚ) ((algebraMap (RatFunc ℚ) E).injective h')
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ h0
    have : Q = ⊥ := Ideal.eq_bot_of_under_eq_bot (R := ℚ[X]) h0
    subst this
    exact Ideal.ramificationIdx_bot_eq_one (R := ℚ[X]) (S := integralClosure ℚ[X] E)
  · intro t Q hQ hQt
    have hφ : RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t) ≠ ⊥ := by
      obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (A := Qbar) t
      intro hbot
      apply hp0
      have : p ∈ RingHom.ker (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t) := hp
      rw [hbot] at this
      exact this
    have h := RamCount.ramCount (F := RatFunc ℚ) (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t)
      hφ Q hQt
    convert h using 3
    ext ψ
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hψ
      refine Polynomial.ringHom_ext (fun a => ?_) ?_
      · exact RingHom.congr_fun (Subsingleton.elim
          ((ψ.comp (algebraMap ℚ[X] (integralClosure ℚ[X] E))).comp Polynomial.C)
          ((Polynomial.eval₂RingHom (algebraMap ℚ Qbar) t).comp Polynomial.C)) a
      · simp [hψ]
    · intro hψ
      have := RingHom.congr_fun hψ X
      simpa using this
  · letI := infAlg E
    haveI : IsDomain InfCoord := inferInstanceAs (IsDomain ℚ[X])
    haveI : IsPrincipalIdealRing InfCoord := inferInstanceAs (IsPrincipalIdealRing ℚ[X])
    haveI : IsFractionRing InfCoord (RatFunc ℚ) := isFractionRing_infCoord
    haveI : IsScalarTower InfCoord (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    intro Q hQ hQs
    let φ : InfCoord →+* Qbar := Polynomial.eval₂RingHom (algebraMap ℚ Qbar) 0
    have hker : RingHom.ker φ = Ideal.span {infUnif} := by
      have := ker_eval_rat 0
      rw [map_zero, map_zero, sub_zero] at this
      exact this
    have hφ : RingHom.ker φ ≠ ⊥ := by
      rw [hker]
      intro h
      rw [Ideal.span_singleton_eq_bot] at h
      exact Polynomial.X_ne_zero h
    have h := RamCount.ramCount (F := RatFunc ℚ) φ hφ Q (hQs.trans hker.symm)
    convert h using 3
    ext ψ
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hψ
      refine Polynomial.ringHom_ext (R := ℚ) (f := ψ.comp (algebraMap InfCoord _)) (g := φ)
        (fun a => ?_) ?_
      · exact RingHom.congr_fun (Subsingleton.elim
          ((ψ.comp (algebraMap InfCoord (integralClosure InfCoord E))).comp Polynomial.C)
          (φ.comp Polynomial.C)) a
      · change ψ (algebraMap InfCoord _ infUnif) = φ X
        rw [hψ]
        exact (Polynomial.eval₂_X (algebraMap ℚ Qbar) (0 : Qbar)).symm
    · intro hψ
      have := RingHom.congr_fun hψ (X : ℚ[X])
      change ψ (algebraMap InfCoord _ infUnif) = φ X at this
      rw [this]
      exact Polynomial.eval₂_X (algebraMap ℚ Qbar) (0 : Qbar)

/-- **`HeckeBranch` with the CM objects supplied by the bundle leaf `R1R2fp`** (compiled). -/
theorem heckeBranch_of_R1R2fp (hRR : R1R2fp) (hR : RamOfFibreCount) (hCI : CurveChartInf)
    (hF : HeckeFibreSizes) (hT : ObjBridge.TorsionStructure) : HeckeBranch :=
  heckeBranch_of hR hCI hF hT (cm_objects_of_R1R2fp hRR)

/-! ## Part 5: the composite -/

/-- **`HeckeBranch` from the curve glue `CurveChartInf`, the moduli input `HeckeFibreSizes` and
the leaves `TorsionStructure`, `R1R2fp`** (compiled; `RamOfFibreCount` is proved). -/
theorem heckeBranch_of' (hRR : R1R2fp) (hCI : CurveChartInf) (hF : HeckeFibreSizes)
    (hT : ObjBridge.TorsionStructure) : HeckeBranch :=
  heckeBranch_of_R1R2fp hRR ramOfFibreCount hCI hF hT

/-- **`CoverModelOfHecke` from ts-hecke's reductions** (compiled). Hypotheses:
* leaves: R1conn (`Y3Connected`, Shimura/Deligne `π₀` with reciprocity), the kernel's
  `ObjBridge.TorsionStructure` (Mumford §4) and the bundle leaf `R1R2fp`;
* glue: `CurveGaloisChart`, `CurveChartInf` (curve theory with no moduli), `HeckeFibreSizes`
  (the moduli count of Baba–Granath's elliptic table) and `HeckeNoVertRam` (Lemma NV, open). -/
theorem coverModelOfHecke_of_tsHecke (hconn : Y3Connected) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure) (hCG : CurveGaloisChart) (hCI : CurveChartInf)
    (hF : HeckeFibreSizes) (hV : HeckeNoVertRam) : CoverModelOfHecke :=
  coverModelOfHecke_of_pieces (heckeNormalization_of hconn hCG hT) (heckeDegree_of_torsion hT)
    (heckeBranch_of' hRR hCI hF hT) hV

/-- **`PropTSAll` with ts-hecke's reductions in place of the five Hecke Props** (compiled; through
prop-ts-glue's `propTSAll_final`). Hypotheses: the bundle leaves T2 and `R1R2fp`, the kernel glue
`MobiusGlue`, prop-ts-glue's open glue (`SNSpecialize`, seven Kummer pieces), and ts-hecke's
inputs (leaves `Y3Connected`, `TorsionStructure`; glue `CurveGaloisChart`, `CurveChartInf`,
`HeckeFibreSizes`, `HeckeNoVertRam`). -/
theorem propTSAll_of_tsHecke (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hS : SNSpecialize) (hC : KummerCompositum)
    (hA : KummerAbhyankarFinGlue) (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin)
    (hAI : KummerAbhyankarInfGlue) (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf)
    (hconn : Y3Connected) (hT : ObjBridge.TorsionStructure) (hCG : CurveGaloisChart)
    (hCI : CurveChartInf) (hF : HeckeFibreSizes) (hV : HeckeNoVertRam) : PropTSAll :=
  propTSAll_final t2 hR hM hS hC hA hO hVF hAI hOI hVI (heckeIrreducible_of_connected hconn)
    (heckeNormalizationIrr_of hCG hT) (heckeDegree_of_torsion hT) (heckeBranch_of' hR hCI hF hT) hV

/-- **`CoverModelOfHecke` with `CurveNormChart` in place of `CurveGaloisChart`** (compiled). -/
theorem coverModelOfHecke_of_tsHecke' (hconn : Y3Connected) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure) (hCN : CurveNormChart) (hCI : CurveChartInf)
    (hF : HeckeFibreSizes) (hV : HeckeNoVertRam) : CoverModelOfHecke :=
  coverModelOfHecke_of_tsHecke hconn hRR hT (curveGaloisChart_of hCN) hCI hF hV

/-- **`PropTSAll` with ts-hecke's reductions, `CurveNormChart` form** (compiled). -/
theorem propTSAll_of_tsHecke' (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hS : SNSpecialize) (hC : KummerCompositum)
    (hA : KummerAbhyankarFinGlue) (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin)
    (hAI : KummerAbhyankarInfGlue) (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf)
    (hconn : Y3Connected) (hT : ObjBridge.TorsionStructure) (hCN : CurveNormChart)
    (hCI : CurveChartInf) (hF : HeckeFibreSizes) (hV : HeckeNoVertRam) : PropTSAll :=
  propTSAll_of_tsHecke t2 hR hM hS hC hA hO hVF hAI hOI hVI hconn hT (curveGaloisChart_of hCN)
    hCI hF hV

end TSHecke

end

