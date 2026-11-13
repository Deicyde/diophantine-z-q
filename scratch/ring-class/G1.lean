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

section Conj

variable {K : Type} [Field K] [NumberField K]

/-- The image `τ(E)` of an intermediate field under a `ℚ`-automorphism `τ` of `Kˢ` lying over an
automorphism `c` of `K`, as an intermediate field of `Kˢ/K`. -/
def conjField (τ : SeparableClosure K →ₐ[ℚ] SeparableClosure K) (c : K ≃ₐ[ℚ] K)
    (hτ : ∀ x, τ (algebraMap K (SeparableClosure K) x) = algebraMap K (SeparableClosure K) (c x))
    (E : IntermediateField K (SeparableClosure K)) : IntermediateField K (SeparableClosure K) :=
  ((E.restrictScalars ℚ).map τ).toSubfield.toIntermediateField (fun x => by
    refine ⟨algebraMap K (SeparableClosure K) (c.symm x), E.algebraMap_mem _, ?_⟩
    simp only [RingHom.coe_coe, hτ, AlgEquiv.apply_symm_apply])

variable (τ : SeparableClosure K →ₐ[ℚ] SeparableClosure K) (c : K ≃ₐ[ℚ] K)
    (hτ : ∀ x, τ (algebraMap K (SeparableClosure K) x) = algebraMap K (SeparableClosure K) (c x))
    (E : IntermediateField K (SeparableClosure K))

theorem mem_conjField {y : SeparableClosure K} :
    y ∈ conjField τ c hτ E ↔ ∃ x ∈ E, τ x = y := Iff.rfl

/-- `τ : E ≃+* τ(E)`. -/
def conjFieldEquiv : E ≃+* conjField τ c hτ E :=
  RingEquiv.ofBijective
    ({ toFun := fun x => ⟨τ x, x, x.2, rfl⟩
       map_one' := by ext; simp
       map_mul' := fun x y => by ext; simp
       map_zero' := by ext; simp
       map_add' := fun x y => by ext; simp } : E →+* conjField τ c hτ E)
    ⟨fun x y h => Subtype.ext (τ.injective (congrArg Subtype.val h)),
      fun ⟨_, x, hx, rfl⟩ => ⟨⟨x, hx⟩, rfl⟩⟩

theorem conjFieldEquiv_algebraMap (k : K) :
    conjFieldEquiv τ c hτ E (algebraMap K E k) = algebraMap K (conjField τ c hτ E) (c k) := by
  apply Subtype.ext
  change τ (algebraMap K (SeparableClosure K) k) = _
  exact hτ k

theorem finrank_conjField : Module.finrank K (conjField τ c hτ E) = Module.finrank K E := by
  have h1 := Module.finrank_mul_finrank ℚ K E
  have h2 := Module.finrank_mul_finrank ℚ K (conjField τ c hτ E)
  have h3 : Module.finrank ℚ E = Module.finrank ℚ (conjField τ c hτ E) :=
    (RingEquiv.toRatAlgEquiv (conjFieldEquiv τ c hτ E)).toLinearEquiv.finrank_eq
  have hK : 0 < Module.finrank ℚ K := Module.finrank_pos
  rw [← h1, ← h2] at h3
  exact (Nat.eq_of_mul_eq_mul_left hK h3).symm

/-- `𝔭` splits completely in `E` iff `c(𝔭)` splits completely in `τ(E)`. -/
theorem ncard_primesOver_conjField (p : Ideal (𝓞 K)) :
    (p.primesOver (𝓞 E)).ncard = ((p.comap
      ((RingOfIntegers.mapRingEquiv c.toRingEquiv).symm : 𝓞 K →+* 𝓞 K)).primesOver
        (𝓞 (conjField τ c hτ E))).ncard :=
  ncard_primesOver_eq_of_ringEquiv (RingOfIntegers.mapRingEquiv (conjFieldEquiv τ c hτ E))
    (RingOfIntegers.mapRingEquiv c.toRingEquiv) (fun x => by
      apply RingOfIntegers.ext
      exact conjFieldEquiv_algebraMap τ c hτ E (x : K)) p

end Conj

section SplitCriterion

open TauCeti.GlobalNumberFields.NumberFieldOrder
open scoped Pointwise

variable {K : Type} [Field K] [NumberField K]

/-- The decomposition group of a prime of the ring class field above a prime `𝔭` prime to the
conductor is generated by the Artin symbol of `𝔭`. -/
theorem stabilizer_eq_zpowers (O : NumberFieldOrder K) (J : integralIdealsPrimeTo O.conductorModulus)
    [(J : Ideal (𝓞 K)).IsMaximal] (Q : Ideal (𝓞 (ringClassField O))) [Q.IsPrime]
    [Q.LiesOver (J : Ideal (𝓞 K))] :
    MulAction.stabilizer Gal(ringClassField O/K) Q =
      Subgroup.zpowers (ringClassArtinEquiv O (O.picClass J)) := by
  have hF := isArithFrobAt_ringClassArtinEquiv_picClass O J Q
  have hmem := hF.mem_stabilizer
  have hle : Subgroup.zpowers (ringClassArtinEquiv O (O.picClass J)) ≤
      MulAction.stabilizer Gal(ringClassField O/K) Q := Subgroup.zpowers_le.mpr hmem
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, MulEquiv.orderOf_eq]
  have h1 := ncard_primesOver_ringClassField_mul_orderOf_picClass O J
  have h2 := MulAction.index_stabilizer Gal(ringClassField O/K) Q
  rw [Algebra.IsInvariant.orbit_eq_primesOver (𝓞 K) (𝓞 (ringClassField O)) Gal(ringClassField O/K)
    (J : Ideal (𝓞 K)) Q] at h2
  have h3 := (MulAction.stabilizer Gal(ringClassField O/K) Q).index_mul_card
  have h4 : Nat.card Gal(ringClassField O/K) = Nat.card (Pic O) :=
    Nat.card_congr (ringClassArtinEquiv O).toEquiv.symm
  rw [h2, h4, ← h1] at h3
  have hpos : 0 < ((J : Ideal (𝓞 K)).primesOver (𝓞 (ringClassField O))).ncard := by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [h, zero_mul] at h1
    exact (Nat.card_pos (α := Pic O)).ne' h1.symm
  exact (Nat.eq_of_mul_eq_mul_left hpos h3).le

/-- **The splitting law for subfields of a ring class field**: a prime `𝔭` of `K` prime to the
conductor splits completely in the fixed field of the Artin image of `S ≤ Pic O` iff the Picard
class of `𝔭 ∩ O` lies in `S`. -/
theorem mem_splitSet_iff (O : NumberFieldOrder K) (S : Subgroup (Pic O))
    (J : integralIdealsPrimeTo O.conductorModulus) [(J : Ideal (𝓞 K)).IsMaximal]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (h𝔭 : 𝔭.asIdeal = J) :
    𝔭 ∈ splitSet K (IntermediateField.lift (IntermediateField.fixedField
      (S.map (ringClassArtinEquiv O).toMonoidHom))) ↔ O.picClass J ∈ S := by
  rw [splitSet_congr K (IntermediateField.liftAlgEquiv _).symm]
  simp only [splitSet, Set.mem_ofPred_eq]
  rw [h𝔭, Ideal.ncard_primesOver_eq_finrank_iff_forall_stabilizer_le (K := K)
    (M := ringClassField O) (J : Ideal (𝓞 K)), IntermediateField.fixingSubgroup_fixedField]
  constructor
  · intro h
    obtain ⟨Q, hQ⟩ := (inferInstance : Nonempty ((J : Ideal (𝓞 K)).primesOver
      (𝓞 (ringClassField O))))
    have := hQ.1
    have := hQ.2
    have h1 := h Q hQ
    rw [stabilizer_eq_zpowers O J Q] at h1
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 (h1 (Subgroup.mem_zpowers _))
    rwa [(ringClassArtinEquiv O).injective hce] at hc
  · intro h Q hQ
    have := hQ.1
    have := hQ.2
    rw [stabilizer_eq_zpowers O J Q]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ h)

end SplitCriterion

section ConjInverse

open TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Redei ZInQ.RouteK.Rank5b
open scoped Pointwise

variable {d : ℕ} [NeZero d]

/-- The ring automorphism of `𝓞_{K_d}` induced by `σ ∈ Aut(K_d/ℚ)`. -/
abbrev cO (σ : QNeg d ≃ₐ[ℚ] QNeg d) : 𝓞 (QNeg d) ≃+* 𝓞 (QNeg d) :=
  RingOfIntegers.mapRingEquiv σ.toRingEquiv

theorem smul_ideal_eq_comap (σ : QNeg d ≃ₐ[ℚ] QNeg d) (I : Ideal (𝓞 (QNeg d))) :
    σ • I = I.comap (cO σ).symm := by
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_comap]
  have : σ⁻¹ • x = (cO σ).symm x := by
    apply RingOfIntegers.ext
    simp [RingOfIntegers.mapRingEquiv_symm_apply]
  rw [this]

/-- `O_{d,4}` is stable under the automorphisms of `K_d`. -/
theorem cO_mem_O4 (σ : QNeg d ≃ₐ[ℚ] QNeg d) {x : 𝓞 (QNeg d)} (hx : x ∈ (O4 d).toRingOfIntegers) :
    cO σ x ∈ (O4 d).toRingOfIntegers := by
  rw [mem_toRingOfIntegers] at hx ⊢
  obtain ⟨a, y, hy⟩ := hx
  refine ⟨a, cO σ y, ?_⟩
  simp only [RingOfIntegers.mapRingEquiv_apply, AlgEquiv.coe_toRingEquiv]
  rw [hy, map_add, map_mul, map_intCast, map_natCast]

theorem cO_mem_conductor (σ : QNeg d ≃ₐ[ℚ] QNeg d) {x : 𝓞 (QNeg d)} (hx : x ∈ (O4 d).conductor) :
    cO σ x ∈ (O4 d).conductor := by
  rw [NumberFieldOrder.mem_conductor_iff] at hx ⊢
  intro y
  have h := hx ((cO σ).symm y)
  have h2 := cO_mem_O4 σ (x := x * (cO σ).symm y) h
  rw [map_mul, RingEquiv.apply_symm_apply] at h2
  simpa using h2

theorem comap_conductor (σ : QNeg d ≃ₐ[ℚ] QNeg d) :
    (O4 d).conductor.comap (cO σ).symm = (O4 d).conductor := by
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_comap] at hx
    have := cO_mem_conductor σ hx
    simpa using this
  · intro x hx
    rw [Ideal.mem_comap]
    have := cO_mem_conductor σ⁻¹ hx
    convert this using 1
    apply RingOfIntegers.ext
    simp [RingOfIntegers.mapRingEquiv_symm_apply]

theorem conj_mem_primeTo (σ : QNeg d ≃ₐ[ℚ] QNeg d) {J : Ideal (𝓞 (QNeg d))}
    (hJ : J ∈ integralIdealsPrimeTo (O4 d).conductorModulus) :
    J.comap (cO σ).symm ∈
      integralIdealsPrimeTo (O4 d).conductorModulus := by
  rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff_sup_eq_top,
    conductorModulus_finitePart] at hJ ⊢
  obtain ⟨h0, h1⟩ := hJ
  refine ⟨?_, ?_⟩
  · intro h
    apply h0
    have : J = (J.comap (cO σ).symm).comap
        (cO σ) := by
      ext x; simp [Ideal.mem_comap]
    rw [this, h]
    ext x; simp [Ideal.mem_comap]
  · rw [← comap_conductor σ, Ideal.comap_symm, Ideal.comap_symm, ← Ideal.map_sup, h1,
      Ideal.map_top]

/-- **Complex conjugation inverts Picard classes**: for `σ ≠ 1`, the class of `σ(J)` is the
inverse of the class of `J` (`J σ(J) = (N J)` is generated by an integer). -/
theorem picClass_conj (σ : QNeg d ≃ₐ[ℚ] QNeg d) (hσ : σ ≠ 1)
    (J : integralIdealsPrimeTo (O4 d).conductorModulus) :
    (O4 d).picClass ⟨_, conj_mem_primeTo σ J.2⟩ = ((O4 d).picClass J)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul, picClass_eq_one_iff]
  refine ⟨((Ideal.absNorm (J : Ideal (𝓞 (QNeg d))) : ℕ) : 𝓞 (QNeg d)), ?_, ?_⟩
  · rw [mem_toRingOfIntegers]
    exact ⟨(Ideal.absNorm (J : Ideal (𝓞 (QNeg d))) : ℤ), 0, by simp⟩
  · have h := mul_conj_ideal d σ hσ (J : Ideal (𝓞 (QNeg d)))
    rw [smul_ideal_eq_comap] at h
    exact h

end ConjInverse

end ZInQ.Contrib.TYZGenus.RingClass
