import Mathlib

/-! prop-ts-glue: development file for `SNHorizontalTransfer` (Mathlib only; pasted into
`PropTSGlue.lean` when done). -/

open Polynomial

noncomputable section

namespace PropTSGlueDev2

abbrev zxMap (E : Type) [Field E] [Algebra ℚ[X] E] : ℤ[X] →+* E :=
  (algebraMap ℚ[X] E).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem zxMap_injective (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] : Function.Injective (zxMap E) := by
  intro a b h
  simp only [zxMap, RingHom.comp_apply, IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E] at h
  have h1 := (algebraMap (RatFunc ℚ) E).injective h
  have h2 := (IsFractionRing.injective ℚ[X] (RatFunc ℚ)) h1
  exact Polynomial.map_injective _ Int.cast_injective h2

@[reducible] noncomputable def locAlg (E : Type) [Field E] [Algebra (RatFunc ℚ) E]
    [Algebra ℚ[X] E] [IsScalarTower ℚ[X] (RatFunc ℚ) E] (m : Ideal ℤ[X]) [m.IsPrime] :
    Algebra (Localization.AtPrime m) E :=
  (IsLocalization.lift (M := m.primeCompl) (S := Localization.AtPrime m) (g := zxMap E)
    (fun y => by
      rw [isUnit_iff_ne_zero]
      intro h
      apply y.2
      rw [(zxMap_injective E) (h.trans (map_zero _).symm)]
      exact m.zero_mem)).toAlgebra

/-- A field is its own localization at any submonoid of nonzero elements. -/
theorem isLocalization_field_self {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (M : Submonoid A) (hM : ∀ x ∈ M, algebraMap A K x ≠ 0) :
    IsLocalization (Algebra.algebraMapSubmonoid K M) K := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, x, hx, rfl⟩
    exact isUnit_iff_ne_zero.mpr (by simpa using hM x hx)
  · intro z
    exact ⟨⟨z, 1⟩, by simp⟩
  · intro x y h
    exact ⟨1, by simpa using h⟩

section Setup

variable (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]

/-- Step (i): the integral closure of `ℤ[X]_m` in `E` is the localization of the integral closure
of `ℤ[X]` at `ℤ[X] ∖ m`. -/
theorem step_i (m : Ideal ℤ[X]) [m.IsPrime] :
    letI : Algebra ℤ[X] E := (zxMap E).toAlgebra
    letI : Algebra (Localization.AtPrime m) E := locAlg E m
    ∃ (_ : Algebra (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E)),
      IsScalarTower (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E) E ∧
      IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) m.primeCompl)
        (integralClosure (Localization.AtPrime m) E) := by
  letI : Algebra ℤ[X] E := (zxMap E).toAlgebra
  letI : Algebra (Localization.AtPrime m) E := locAlg E m
  have hT : IsScalarTower ℤ[X] (Localization.AtPrime m) E := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (IsLocalization.lift_comp _).symm
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid E m.primeCompl) E :=
    isLocalization_field_self _ (fun x hx h0 => hx (by
      rw [(zxMap_injective E) (h0.trans (map_zero _).symm)]; exact m.zero_mem))
  -- the inclusion `C → S`
  let ι : integralClosure ℤ[X] E →+* integralClosure (Localization.AtPrime m) E :=
    { toFun := fun c => ⟨c.1, IsIntegral.tower_top (A := Localization.AtPrime m) c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI := ι.toAlgebra
  have h1 : IsScalarTower (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have h2 : IsScalarTower ℤ[X] (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply ℤ[X] (Localization.AtPrime m)
      (integralClosure (Localization.AtPrime m) E)]
    change algebraMap (Localization.AtPrime m) E (algebraMap ℤ[X] _ x) = algebraMap ℤ[X] E x
    exact (IsScalarTower.algebraMap_apply _ _ _ x).symm
  exact ⟨ι.toAlgebra, h1, IsLocalization.integralClosure m.primeCompl⟩

end Setup

/-- `P ∩ ℤ = 0` for a prime `P` of `ℤ[X]_m` (`m ∋ p` maximal) not containing `p`. -/
theorem int_notMem (p : ℕ) [hp : Fact p.Prime] (m : Ideal ℤ[X]) [m.IsMaximal]
    (hpm : C (p : ℤ) ∈ m) (P : Ideal (Localization.AtPrime m)) [P.IsPrime]
    (hpP : algebraMap ℤ[X] (Localization.AtPrime m) (C (p : ℤ)) ∉ P) (n : ℤ) (hn : n ≠ 0) :
    algebraMap ℤ[X] (Localization.AtPrime m) (C n) ∉ P := by
  intro hnP
  set J : Ideal ℤ := (P.comap (algebraMap ℤ[X] (Localization.AtPrime m))).comap C
  have hJp : J.IsPrime := Ideal.IsPrime.comap _
  have hJ0 : J ≠ ⊥ := fun h => hn (by
    have : n ∈ J := hnP
    rwa [h, Ideal.mem_bot] at this)
  have hJmax : J.IsMaximal := hJp.isMaximal hJ0
  have hle : J ≤ m.comap C := by
    intro x hx
    have hx' : algebraMap ℤ[X] (Localization.AtPrime m) (C x) ∈ P := hx
    by_contra hxm
    have hu : IsUnit (algebraMap ℤ[X] (Localization.AtPrime m) (C x)) :=
      IsLocalization.map_units (Localization.AtPrime m) (⟨C x, hxm⟩ : m.primeCompl)
    exact (inferInstance : P.IsPrime).ne_top (P.eq_top_of_isUnit_mem hx' hu)
  have hne : m.comap C ≠ ⊤ := fun h => (Ideal.IsMaximal.ne_top ‹m.IsMaximal›)
    (Ideal.comap_eq_top_iff.mp h)
  have hEq : J = m.comap C := hJmax.eq_of_le hne hle
  have : (p : ℤ) ∈ J := hEq ▸ hpm
  exact hpP this

theorem atPrime_congr {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (h : p = q) [IsLocalization.AtPrime S p] :
    IsLocalization.AtPrime S q := by
  subst h
  assumption

attribute [local instance] Polynomial.algebra in
theorem snHorizontalTransfer_aux (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime)
    (m : Ideal ℤ[X]) [m.IsMaximal] (hpm : C (p : ℤ) ∈ m) :
    letI := locAlg E m
    ∀ P : Ideal (Localization.AtPrime m), P.IsPrime → P.height = 1 →
      algebraMap ℤ[X] (Localization.AtPrime m) (C (p : ℤ)) ∉ P →
      ¬ Algebra.IsUnramifiedIn (integralClosure (Localization.AtPrime m) E) P →
      ∃ Q : Ideal (integralClosure ℚ[X] E), Q.IsPrime ∧ Q.ramificationIdx ℚ[X] ≠ 1 ∧
        ∀ F : ℤ[X], F.map (Int.castRingHom ℚ) ∈ Q.under ℚ[X] →
          algebraMap ℤ[X] (Localization.AtPrime m) F ∈ P := by
  letI iE : Algebra (Localization.AtPrime m) E := locAlg E m
  intro P hP _ hpP hnot
  have : Fact p.Prime := ⟨hp⟩
  simp only [Algebra.IsUnramifiedIn, not_forall] at hnot
  obtain ⟨Q', hQ', hlies, hnu⟩ := hnot
  -- the rings
  letI iZ : Algebra ℤ[X] E := (zxMap E).toAlgebra
  have hTR : IsScalarTower ℤ[X] (Localization.AtPrime m) E := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (IsLocalization.lift_comp _).symm
  have hTQ : IsScalarTower ℤ[X] ℚ[X] E := IsScalarTower.of_algebraMap_eq' rfl
  -- `C → S`
  let ιS : integralClosure ℤ[X] E →+* integralClosure (Localization.AtPrime m) E :=
    { toFun := fun c => ⟨c.1, IsIntegral.tower_top (A := Localization.AtPrime m) c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI aCS := ιS.toAlgebra
  have hCSE : IsScalarTower (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E)
      E := IsScalarTower.of_algebraMap_eq' rfl
  have hZCS : IsScalarTower ℤ[X] (integralClosure ℤ[X] E)
      (integralClosure (Localization.AtPrime m) E) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply ℤ[X] (Localization.AtPrime m)
      (integralClosure (Localization.AtPrime m) E)]
    change algebraMap (Localization.AtPrime m) E (algebraMap ℤ[X] _ x) = algebraMap ℤ[X] E x
    exact (IsScalarTower.algebraMap_apply _ _ _ x).symm
  have hlocE : IsLocalization (Algebra.algebraMapSubmonoid E m.primeCompl) E :=
    isLocalization_field_self _ (fun x hx h0 => hx (by
      rw [(zxMap_injective E) (h0.trans (map_zero _).symm)]; exact m.zero_mem))
  have hlocS : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E)
      m.primeCompl) (integralClosure (Localization.AtPrime m) E) :=
    IsLocalization.integralClosure m.primeCompl
  -- `C → B`
  let ιB : integralClosure ℤ[X] E →+* integralClosure ℚ[X] E :=
    { toFun := fun c => ⟨c.1, IsIntegral.tower_top (A := ℚ[X]) c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI aCB := ιB.toAlgebra
  have hCBE : IsScalarTower (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hZCB : IsScalarTower ℤ[X] (integralClosure ℤ[X] E) (integralClosure ℚ[X] E) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply Subtype.ext
    rw [IsScalarTower.algebraMap_apply ℤ[X] ℚ[X] (integralClosure ℚ[X] E)]
    rfl
  set M₀ : Submonoid ℤ[X] := (nonZeroDivisors ℤ).map C with hM₀
  have hlocQ : IsLocalization M₀ ℚ[X] := Polynomial.isLocalization _ _
  have hlocE₀ : IsLocalization (Algebra.algebraMapSubmonoid E M₀) E :=
    isLocalization_field_self _ (by
      rintro _ ⟨n, hn, rfl⟩ h0
      have : C n = 0 := (zxMap_injective E) (h0.trans (map_zero _).symm)
      exact nonZeroDivisors.ne_zero hn (C_eq_zero.mp this))
  have hlocB : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) M₀)
      (integralClosure ℚ[X] E) :=
    IsLocalization.integralClosure M₀
  -- the prime `𝔮` of `C` under `Q'`, and `Q = 𝔮 B`
  set 𝔮 : Ideal (integralClosure ℤ[X] E) :=
    Q'.comap (algebraMap (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E))
    with h𝔮
  have h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.comap _
  have hdisj : Disjoint ((Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) M₀ :
      Submonoid _) : Set (integralClosure ℤ[X] E)) ↑𝔮 := by
    rw [Set.disjoint_left]
    rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩ hmem
    have hmem' : algebraMap (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)
        (algebraMap ℤ[X] (Localization.AtPrime m) (C n)) ∈ Q' := by
      have : algebraMap (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E)
          (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C n)) ∈ Q' := hmem
      rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ[X]
        (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)] at this
    have hP' : algebraMap ℤ[X] (Localization.AtPrime m) (C n) ∈ P := by
      rw [hlies.over]
      exact hmem'
    exact int_notMem p m hpm P hpP n (nonZeroDivisors.ne_zero hn) hP'
  set Q : Ideal (integralClosure ℚ[X] E) := 𝔮.map (algebraMap _ _) with hQdef
  have hQp : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ 𝔮 h𝔮p hdisj
  have hQ𝔮 : Q.comap (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)) = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint _ _ h𝔮p hdisj
  refine ⟨Q, hQp, ?_, ?_⟩
  swap
  · -- elements of `ℤ[X]` in `Q` lie in `P`
    intro F hF
    have h1 : algebraMap ℤ[X] (integralClosure ℤ[X] E) F ∈ 𝔮 := by
      rw [← hQ𝔮]
      change algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E)
        (algebraMap ℤ[X] (integralClosure ℤ[X] E) F) ∈ Q
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ[X] ℚ[X]
        (integralClosure ℚ[X] E)]
      exact hF
    have h2 : algebraMap (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)
        (algebraMap ℤ[X] (Localization.AtPrime m) F) ∈ Q' := by
      have : algebraMap (integralClosure ℤ[X] E) (integralClosure (Localization.AtPrime m) E)
          (algebraMap ℤ[X] (integralClosure ℤ[X] E) F) ∈ Q' := h1
      rwa [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ[X]
        (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) E)] at this
    rw [hlies.over]
    exact h2
  · intro he1
    apply hnu
    have hfinB : Module.Finite ℚ[X] (integralClosure ℚ[X] E) :=
      IsIntegralClosure.finite ℚ[X] (RatFunc ℚ) E (integralClosure ℚ[X] E)
    have : Algebra.EssFiniteType ℚ[X] (integralClosure ℚ[X] E) := inferInstance
    have : CharZero (Q.under ℚ[X]).ResidueField :=
      charZero_of_injective_ringHom
        ((algebraMap ℚ[X] (Q.under ℚ[X]).ResidueField).comp (C : ℚ →+* ℚ[X])).injective
    have : Algebra.HasSeparableResidueFieldsAt ℚ[X] (integralClosure ℚ[X] E) (Q.under ℚ[X]) :=
      inferInstance
    have hunQ : Algebra.IsUnramifiedAt ℚ[X] Q := (Ideal.ramificationIdx_eq_one_iff).mp he1
    have hZQ : Algebra.FormallyUnramified ℤ[X] ℚ[X] :=
      Algebra.FormallyUnramified.of_isLocalization M₀
    have hZB : Algebra.FormallyUnramified ℤ[X] (Localization.AtPrime Q) :=
      Algebra.FormallyUnramified.comp ℤ[X] ℚ[X] (Localization.AtPrime Q)
    -- both local rings are the localization of `C` at `𝔮`
    have hL1 : IsLocalization.AtPrime (Localization Q'.primeCompl) 𝔮 :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) m.primeCompl)
        (Localization Q'.primeCompl) Q'
    have hL2' : IsLocalization.AtPrime (Localization.AtPrime Q)
        (Q.comap (algebraMap (integralClosure ℤ[X] E) (integralClosure ℚ[X] E))) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Algebra.algebraMapSubmonoid (integralClosure ℤ[X] E) M₀) (Localization.AtPrime Q) Q
    have hL2 : IsLocalization.AtPrime (Localization.AtPrime Q) 𝔮 := atPrime_congr hQ𝔮
    let e : Localization Q'.primeCompl ≃ₐ[integralClosure ℤ[X] E] Localization.AtPrime Q :=
      IsLocalization.algEquiv 𝔮.primeCompl _ _
    have t1 : IsScalarTower ℤ[X] (integralClosure ℤ[X] E) (Localization Q'.primeCompl) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      rw [IsScalarTower.algebraMap_apply (integralClosure ℤ[X] E)
        (integralClosure (Localization.AtPrime m) E) (Localization Q'.primeCompl),
        ← IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
          (integralClosure (Localization.AtPrime m) E)]
      rfl
    have t2 : IsScalarTower ℤ[X] (integralClosure ℤ[X] E) (Localization.AtPrime Q) := by
      apply IsScalarTower.of_algebraMap_eq
      intro x
      rw [IsScalarTower.algebraMap_apply (integralClosure ℤ[X] E)
        (integralClosure ℚ[X] E) (Localization.AtPrime Q),
        ← IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
          (integralClosure ℚ[X] E)]
      rfl
    have hZS : Algebra.FormallyUnramified ℤ[X] (Localization Q'.primeCompl) :=
      Algebra.FormallyUnramified.of_equiv (A := Localization.AtPrime Q)
        (AlgEquiv.ofRingEquiv (f := (e.symm : Localization.AtPrime Q ≃+* Localization Q'.primeCompl))
          (fun x => by
            rw [IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
                (Localization.AtPrime Q),
              IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E)
                (Localization Q'.primeCompl)]
            exact e.symm.commutes _))
    have t3 : IsScalarTower ℤ[X] (Localization.AtPrime m) (Localization Q'.primeCompl) :=
      inferInstance
    exact Algebra.FormallyUnramified.of_restrictScalars ℤ[X] (Localization.AtPrime m)
      (Localization Q'.primeCompl)

end PropTSGlueDev2

#print axioms PropTSGlueDev2.snHorizontalTransfer_aux
