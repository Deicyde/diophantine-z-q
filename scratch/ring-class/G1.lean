import ZInQKernel.Contrib.TYZGenus.RingClass
import ZInQKernel.Contrib.TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount
import ZInQKernel.Contrib.TauCeti.NumberTheory.Chebotarev.SplitsCompletely
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure
open NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory IsDedekindDomain

noncomputable section
namespace ZInQ.Contrib.TYZGenus.RingClass

section Transport

/-- Primes over `p` in `A` correspond to primes over `cO(p)` in `B` under a ring isomorphism
`ψ : A ≃ B` lying over a ring automorphism `cO` of the base. -/
theorem ncard_primesOver_eq_of_ringEquiv {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (ψ : A ≃+* B) (cO : R ≃+* R)
    (hψ : ∀ x, ψ (algebraMap R A x) = algebraMap R B (cO x)) (p : Ideal R) :
    (p.primesOver A).ncard = ((p.comap (cO.symm : R →+* R)).primesOver B).ncard := by
  have hψ' : ∀ x, ψ.symm (algebraMap R B x) = algebraMap R A (cO.symm x) := by
    intro x
    apply ψ.injective
    rw [RingEquiv.apply_symm_apply, hψ, RingEquiv.apply_symm_apply]
  refine Set.ncard_congr (fun Q _ => Q.comap (ψ.symm : B →+* A)) ?_ ?_ ?_
  · rintro Q ⟨hQ, hQo⟩
    refine ⟨Ideal.comap_isPrime _ _, ⟨?_⟩⟩
    ext x
    simp only [Ideal.under_def, Ideal.mem_comap, RingHom.coe_coe]
    rw [hψ', hQo.over, Ideal.under_def, Ideal.mem_comap]
  · intro Q Q' _ _ h
    exact Ideal.comap_injective_of_surjective _ ψ.symm.surjective h
  · rintro Q' ⟨hQ', hQ'o⟩
    refine ⟨Q'.comap (ψ : A →+* B), ⟨Ideal.comap_isPrime _ _, ⟨?_⟩⟩, ?_⟩
    · ext x
      simp only [Ideal.under_def, Ideal.mem_comap, RingHom.coe_coe]
      rw [hψ]
      have := hQ'o.over
      rw [Ideal.under_def] at this
      rw [← Ideal.mem_comap, ← this, Ideal.mem_comap]
      simp
    · ext x
      simp only [Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply]

/-- The number of primes above `p` is invariant under `K`-algebra isomorphisms. -/
theorem ncard_primesOver_congr {K A B : Type*} [Field K] [Field A] [Field B] [Algebra K A]
    [Algebra K B] (e : A ≃ₐ[K] B) (p : Ideal (𝓞 K)) :
    (p.primesOver (𝓞 A)).ncard = (p.primesOver (𝓞 B)).ncard := by
  have := ncard_primesOver_eq_of_ringEquiv (RingOfIntegers.mapRingEquiv e.toRingEquiv)
    (RingEquiv.refl (𝓞 K)) (fun x => by
      apply RingOfIntegers.ext
      simp only [RingOfIntegers.mapRingEquiv_apply, RingEquiv.refl_apply]
      exact e.commutes (x : K)) p
  simpa using this

end Transport

section Bauer

variable (K : Type) [Field K] [NumberField K]

/-- The primes of `K` splitting completely in `L`. -/
def splitSet (L : Type*) [Field L] [Algebra K L] : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L}

theorem hasNaturalDensity_splitSet (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] :
    NumberField.Set.HasNaturalDensity (splitSet K L) (1 / Module.finrank K L) := by
  rw [splitSet, ← NumberField.Chebotarev.frobeniusPrimeSet_one_eq_setOf_ncard_primesOver_eq_finrank]
  have := NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet K L 1
  rwa [ConjClasses.one_eq_mk_one, TauCeti.ConjClasses.card_carrier_mk_one,
    IsGalois.card_aut_eq_finrank, Nat.cast_one] at this

theorem splitSet_congr {A B : Type*} [Field A] [Field B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) : splitSet K A = splitSet K B := by
  ext 𝔭
  simp only [splitSet, Set.mem_ofPred_eq, ncard_primesOver_congr e, e.toLinearEquiv.finrank_eq]

variable {K}

theorem HasNaturalDensity.unique {S : Set (HeightOneSpectrum (𝓞 K))} {a b : ℝ}
    (ha : NumberField.Set.HasNaturalDensity S a) (hb : NumberField.Set.HasNaturalDensity S b) :
    a = b :=
  tendsto_nhds_unique ha hb

/-- `splitSet (E ⊔ E') = splitSet E ∩ splitSet E'` for finite Galois `E, E' ⊆ Kˢ`. -/
theorem splitSet_sup (E E' : IntermediateField K (SeparableClosure K)) [FiniteDimensional K E]
    [FiniteDimensional K E'] [IsGalois K E] [IsGalois K E'] :
    splitSet K ↥(E ⊔ E') = splitSet K E ∩ splitSet K E' := by
  set M := E ⊔ E'
  have : NumberField M := NumberField.of_module_finite K M
  set E₁ : IntermediateField K M := IntermediateField.restrict (le_sup_left : E ≤ M)
  set E₂ : IntermediateField K M := IntermediateField.restrict (le_sup_right : E' ≤ M)
  have htop : E₁ ⊔ E₂ = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict, IntermediateField.lift_restrict,
      IntermediateField.lift_top]
  ext 𝔭
  have h := Ideal.ncard_primesOver_sup_eq_finrank_iff (K := K) (M := M) 𝔭.asIdeal E₁ E₂
  rw [htop] at h
  simp only [splitSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  have e1 := IntermediateField.restrictAlgEquiv (le_sup_left : E ≤ M)
  have e2 := IntermediateField.restrictAlgEquiv (le_sup_right : E' ≤ M)
  have e0 : (⊤ : IntermediateField K M) ≃ₐ[K] M := IntermediateField.topEquiv
  rw [ncard_primesOver_congr e0, e0.toLinearEquiv.finrank_eq,
    ← ncard_primesOver_congr e1, ← e1.toLinearEquiv.finrank_eq,
    ← ncard_primesOver_congr e2, ← e2.toLinearEquiv.finrank_eq] at h
  exact h

/-- **Bauer's theorem** (from Chebotarev's density theorem): for finite Galois `E, E' ⊆ Kˢ`, if
every prime outside a finite set that splits completely in `E` splits completely in `E'`, then
`E' ⊆ E`. -/
theorem le_of_splitSet_diff_subset {E E' : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K E] [FiniteDimensional K E'] [IsGalois K E] [IsGalois K E']
    (T : Set (HeightOneSpectrum (𝓞 K))) (hT : T.Finite) (h : splitSet K E \ T ⊆ splitSet K E') :
    E' ≤ E := by
  set M := E ⊔ E'
  have : NumberField M := NumberField.of_module_finite K M
  have : NumberField E := NumberField.of_module_finite K E
  have hsub : symmDiff (splitSet K M) (splitSet K E) ⊆ T := by
    rw [splitSet_sup]
    intro 𝔭 h𝔭
    rcases h𝔭 with ⟨⟨h1, _⟩, h2⟩ | ⟨h1, h2⟩
    · exact absurd h1 h2
    · by_contra hT'
      exact h2 ⟨h1, h ⟨h1, hT'⟩⟩
  have hM := hasNaturalDensity_splitSet K M
  have hE := hasNaturalDensity_splitSet K E
  have hE' := (NumberField.Set.hasNaturalDensity_iff_of_finite_symmDiff (hT.subset hsub)).1 hM
  have heq := HasNaturalDensity.unique hE hE'
  have hpos1 : (0 : ℝ) < Module.finrank K E := by exact_mod_cast Module.finrank_pos
  have hpos2 : (0 : ℝ) < Module.finrank K M := by exact_mod_cast Module.finrank_pos
  have hfr : Module.finrank K E = Module.finrank K M := by
    have : (Module.finrank K E : ℝ) = Module.finrank K M := by
      field_simp at heq; linarith
    exact_mod_cast this
  have hEM : E = M := IntermediateField.eq_of_le_of_finrank_eq le_sup_left hfr
  rw [hEM]
  exact le_sup_right

end Bauer

end ZInQ.Contrib.TYZGenus.RingClass
