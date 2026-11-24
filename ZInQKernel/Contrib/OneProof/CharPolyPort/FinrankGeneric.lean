/-
charpoly-port (2026-11-17): the rank of a finite flat surjective morphism of integral schemes at the
generic point is the degree of the function-field extension (`finrank_genericPoint`), with its
commutative-algebra core (`rankAtStalk_bot_eq_finrank`). Report `docs/research/charpoly-port.md`.
-/
import Mathlib

/-!
# Rank at the generic point of a finite flat morphism

* `rankAtStalk_bot_eq_finrank`: for `R ⊆ S` domains with `S` finite flat over `R`, the rank of `S` at
  the zero prime of `R` is `[Frac S : Frac R]` (`Frac S` is the localization of `S` at `R ∖ 0`, hence the
  base change `Frac R ⊗_R S`).
* `finrank_genericPoint`: for `f : X ⟶ Y` finite, flat and surjective between integral schemes,
  `Scheme.Hom.finrank f` at the generic point is `[K(X) : K(Y)]`, `K(Y) → K(X)` the stalk map.
-/

open Polynomial

namespace ZInQ.Contrib.OneProof.CharPolyPort

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]
  [Module.Finite R S]

/-- A nonzero element of a domain finite over a domain `R` divides a nonzero element of `R`. -/
theorem exists_dvd_algebraMap (b : S) (hb : b ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ b ∣ algebraMap R S r := by
  have hI : (Ideal.span {b}).comap (algebraMap R S) ≠ ⊥ :=
    Ideal.under_ne_bot_of_integral_mem hb (Ideal.mem_span_singleton_self b)
      (Algebra.IsIntegral.isIntegral b)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  exact ⟨r, hr0, Ideal.mem_span_singleton.mp hr⟩

/-- `Frac S` is the localization of `S` at the nonzero elements of `R`. -/
theorem isLocalization_algebraMapSubmonoid [FaithfulSMul R S] (L : Type u) [CommRing L] [Algebra S L]
    [IsFractionRing S L] :
    IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) L where
  map_units m := by
    obtain ⟨_, ⟨r, hr, rfl⟩⟩ := m
    apply IsLocalization.map_units L (M := nonZeroDivisors S) ⟨algebraMap R S r, ?_⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr
        (nonZeroDivisors.ne_zero hr))
  surj z := by
    obtain ⟨⟨x, n⟩, e⟩ := IsLocalization.surj (nonZeroDivisors S) z
    obtain ⟨r, hr0, c, hc⟩ := exists_dvd_algebraMap (R := R) (n : S) (nonZeroDivisors.ne_zero n.2)
    refine ⟨⟨x * c, ⟨algebraMap R S r, r, mem_nonZeroDivisors_of_ne_zero hr0, rfl⟩⟩, ?_⟩
    simp only at e ⊢
    rw [hc, map_mul, map_mul, ← mul_assoc, e]
  exists_of_eq {x y} h := ⟨1, by simp [IsFractionRing.injective S L h]⟩

/-- **The algebra core.** The rank of `S` at the zero prime of `R` is `[Frac S : Frac R]`. -/
theorem rankAtStalk_bot_eq_finrank (K L : Type u) [CommRing K] [CommRing L] [Algebra R K]
    [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [Module.Flat R S] :
    Module.rankAtStalk (R := R) S (⊥ : PrimeSpectrum R) = Module.finrank K L := by
  letI := IsFractionRing.toField R (K := K)
  letI := IsFractionRing.toField S (K := L)
  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have h2 : Function.Injective (algebraMap R L) := by
      rw [IsScalarTower.algebraMap_eq R K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
    rw [IsScalarTower.algebraMap_eq R S L] at h2
    exact Function.Injective.of_comp h2
  haveI := isLocalization_algebraMapSubmonoid (R := R) (S := S) L
  have hpush : Algebra.IsPushout R S K L :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors R) K).mp inferInstance
  have hbc : IsBaseChange K (IsScalarTower.toAlgHom R S L).toLinearMap := hpush.symm.out
  have hfree : Module.rankAtStalk (R := K) L (⊥ : PrimeSpectrum K) = Module.finrank K L :=
    congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := L)) (⊥ : PrimeSpectrum K)
  rw [← hfree, Module.rankAtStalk_isBaseChange hbc]
  congr 1
  ext x
  simp only [PrimeSpectrum.comap_asIdeal]
  change x ∈ (⊥ : Ideal R) ↔ x ∈ Ideal.comap (algebraMap R K) (⊥ : Ideal K)
  rw [Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)]


open CategoryTheory AlgebraicGeometry Limits

/-- A localization at the zero prime of a domain is a fraction ring. -/
theorem isFractionRing_of_atPrime_bot {A B : Type u} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (hp : p = ⊥) [IsLocalization.AtPrime B p] : IsFractionRing A B := by
  have h : p.primeCompl = nonZeroDivisors A := by
    subst hp
    ext a
    simp [Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  have : IsLocalization p.primeCompl B := inferInstance
  rw [h] at this
  exact this

/-- **`FinrankGenericPoint`** (general form). -/
theorem finrank_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsFinite f] [Flat f] (hf : Function.Surjective f) :
    letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
    Scheme.Hom.finrank f (f (genericPoint X)) =
      Module.finrank (Y.presheaf.stalk (f (genericPoint X))) (X.presheaf.stalk (genericPoint X)) := by
  set x := genericPoint X with hxdef
  have hy : f x = genericPoint Y := by
    have h1 := (genericPoint_spec X).image f.continuous
    rw [Set.image_univ_of_surjective hf, closure_univ] at h1
    exact h1.eq (genericPoint_spec Y)
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) trivial
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hxU : x ∈ f ⁻¹ᵁ V := hyV
  haveI : Nonempty V := ⟨⟨f x, hyV⟩⟩
  haveI : Nonempty (f ⁻¹ᵁ V) := ⟨⟨x, hxU⟩⟩
  set φ := f.app V with hφ
  have hsq : IsPullback (Spec.map φ) hU.fromSpec hV.fromSpec f := by
    refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
    · rw [hφ, ← Scheme.Hom.appLE_eq_app]
      exact (IsAffineOpen.SpecMap_appLE_fromSpec f hV hU le_rfl).symm
    · rw [hV.opensRange_fromSpec, hU.opensRange_fromSpec]
  have hfin : φ.hom.Finite := f.finite_app V hV
  have hflat : φ.hom.Flat := by
    rw [hφ, ← Scheme.Hom.appLE_eq_app]
    exact f.flat_appLE hV hU le_rfl
  set p := hV.primeIdealOf ⟨f x, hyV⟩ with hpdef
  have h1 : Scheme.Hom.finrank f (f x) = φ.hom.finrank p := by
    have := Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq.flip p
    rw [hpdef, hV.fromSpec_primeIdealOf] at this
    rw [← this, Scheme.Hom.finrank_SpecMap_eq_finrank hfin hflat]
  rw [h1]
  -- p is the zero prime
  have hp : p = ⊥ := by
    have : (⟨f x, hyV⟩ : V) = ⟨genericPoint Y, hy ▸ hyV⟩ := Subtype.ext hy
    rw [hpdef, this, hV.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  have hq : hU.primeIdealOf ⟨x, hxU⟩ = ⊥ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
  letI : Algebra Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := φ.hom.toAlgebra
  letI : Algebra Γ(Y, V) (Y.presheaf.stalk (f x)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨f x, hyV⟩
  letI : Algebra Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  letI : Algebra Γ(Y, V) (X.presheaf.stalk x) :=
    ((X.presheaf.germ (f ⁻¹ᵁ V) x hxU).hom.comp φ.hom).toAlgebra
  haveI : IsScalarTower Γ(Y, V) Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower Γ(Y, V) (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have := congrArg (fun g => g.hom r) (Scheme.Hom.germ_stalkMap f V x hyV)
    exact this.symm
  haveI : Module.Finite Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hfin
  haveI : Module.Flat Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := hflat
  haveI hlocY := hV.isLocalization_stalk ⟨f x, hyV⟩
  haveI hlocX := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI : IsFractionRing Γ(Y, V) (Y.presheaf.stalk (f x)) :=
    isFractionRing_of_atPrime_bot (p := (hV.primeIdealOf ⟨f x, hyV⟩).asIdeal) (by rw [← hpdef, hp]; rfl)
  haveI : IsFractionRing Γ(X, f ⁻¹ᵁ V) (X.presheaf.stalk x) :=
    isFractionRing_of_atPrime_bot (p := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) (by rw [hq]; rfl)
  rw [hp]
  exact rankAtStalk_bot_eq_finrank (R := Γ(Y, V)) (S := Γ(X, f ⁻¹ᵁ V))
    (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

end ZInQ.Contrib.OneProof.CharPolyPort
