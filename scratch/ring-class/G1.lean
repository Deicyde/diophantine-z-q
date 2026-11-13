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

section Normality

open TauCeti.GlobalNumberFields.NumberFieldOrder ZInQ.RouteK.Redei ZInQ.RouteK.Rank5b
open scoped Pointwise

variable {d : ℕ} [NeZero d]

/-- The image of a `K`-normal subfield under a `ℚ`-automorphism of `Kˢ` is `K`-normal. -/
theorem normal_conjField (τ : SeparableClosure (QNeg d) ≃ₐ[ℚ] SeparableClosure (QNeg d))
    (c : QNeg d ≃ₐ[ℚ] QNeg d)
    (hτ : ∀ x, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) x) =
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) (c x))
    (E : IntermediateField (QNeg d) (SeparableClosure (QNeg d))) [Normal (QNeg d) E] :
    Normal (QNeg d) (conjField (τ : SeparableClosure (QNeg d) →ₐ[ℚ] SeparableClosure (QNeg d))
      c hτ E) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro g
  rintro _ ⟨y, ⟨x, hx, rfl⟩, rfl⟩
  have hτs : ∀ k, τ.symm (algebraMap (QNeg d) (SeparableClosure (QNeg d)) (c k)) =
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) k := by
    intro k; rw [← hτ, AlgEquiv.symm_apply_apply]
  let g' : Gal(SeparableClosure (QNeg d)/QNeg d) :=
    AlgEquiv.ofRingEquiv (f := τ.toRingEquiv.trans (g.toRingEquiv.trans τ.symm.toRingEquiv))
      (fun k => by
        simp only [RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv]
        rw [hτ, AlgEquiv.commutes, hτs])
  have hg' : g' x ∈ E :=
    (IntermediateField.normal_iff_forall_map_le'.1 inferInstance g') ⟨x, hx, rfl⟩
  refine ⟨g' x, hg', ?_⟩
  simp [g']

/-- The subfield of `H_{d,4}` cut out by `S ≤ Pic(O_{d,4})`. -/
abbrev ringSubfield (S : Subgroup (Pic (O4 d))) :
    IntermediateField (QNeg d) (SeparableClosure (QNeg d)) :=
  IntermediateField.lift (IntermediateField.fixedField (S.map (ringClassArtinEquiv (O4 d)).toMonoidHom))

instance (S : Subgroup (Pic (O4 d))) : FiniteDimensional (QNeg d) (ringSubfield S) :=
  LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv _).toLinearEquiv

instance (S : Subgroup (Pic (O4 d))) : IsGalois (QNeg d) (ringSubfield S) := by
  have : (S.map (ringClassArtinEquiv (O4 d)).toMonoidHom).Normal := Subgroup.normal_of_comm _
  exact IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv _)

theorem finite_conductor_primes :
    {𝔭 : HeightOneSpectrum (𝓞 (QNeg d)) | (O4 d).conductor ≤ 𝔭.asIdeal}.Finite := by
  have h := Ideal.finite_factors (R := 𝓞 (QNeg d)) (I := (O4 d).conductor)
    (by simpa using (O4 d).conductor_ne_bot)
  refine h.subset fun 𝔭 h𝔭 => ?_
  exact Ideal.dvd_iff_le.2 h𝔭

theorem mem_primeTo_of_not_le (𝔭 : HeightOneSpectrum (𝓞 (QNeg d)))
    (h : ¬ (O4 d).conductor ≤ 𝔭.asIdeal) :
    𝔭.asIdeal ∈ integralIdealsPrimeTo (O4 d).conductorModulus := by
  rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff_sup_eq_top,
    conductorModulus_finitePart]
  refine ⟨𝔭.ne_bot, ?_⟩
  by_contra hne
  exact h ((𝔭.isMaximal.eq_of_le hne le_sup_left).symm ▸ le_sup_right)

/-- **`τ(E_S) ⊆ E_S`** for a `ℚ`-automorphism `τ` of `Kˢ` acting on `K` by the nontrivial
automorphism `σ` (Bauer's theorem with `picClass_conj`). -/
theorem conjField_ringSubfield_le (τ : SeparableClosure (QNeg d) ≃ₐ[ℚ] SeparableClosure (QNeg d))
    (σ : QNeg d ≃ₐ[ℚ] QNeg d) (hσ : σ ≠ 1)
    (hτ : ∀ x, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) x) =
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) (σ x))
    (S : Subgroup (Pic (O4 d))) :
    conjField (τ : SeparableClosure (QNeg d) →ₐ[ℚ] SeparableClosure (QNeg d)) σ hτ
      (ringSubfield S) ≤ ringSubfield S := by
  set E := ringSubfield S
  set E' := conjField (τ : SeparableClosure (QNeg d) →ₐ[ℚ] SeparableClosure (QNeg d)) σ hτ E
  have hfr : Module.finrank (QNeg d) E' = Module.finrank (QNeg d) E := finrank_conjField _ _ _ _
  have : FiniteDimensional (QNeg d) E' :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact Module.finrank_pos)
  have : Normal (QNeg d) E' := normal_conjField τ σ hτ E
  have : IsGalois (QNeg d) E' := IsGalois.mk
  refine le_of_splitSet_diff_subset _ finite_conductor_primes ?_
  rintro 𝔭 ⟨h𝔭, hT𝔭⟩
  have hJ := mem_primeTo_of_not_le 𝔭 hT𝔭
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := 𝔭.isMaximal
  have hS : (O4 d).picClass ⟨_, hJ⟩ ∈ S := (mem_splitSet_iff (O4 d) S ⟨_, hJ⟩ 𝔭 rfl).1 h𝔭
  have hp := conj_mem_primeTo σ⁻¹ hJ
  have hpS : (O4 d).picClass ⟨_, hp⟩ ∈ S := by
    rw [picClass_conj σ⁻¹ (inv_ne_one.2 hσ) ⟨_, hJ⟩]; exact inv_mem hS
  have : (𝔭.asIdeal.comap (cO σ⁻¹).symm).IsMaximal := Ideal.comap_isMaximal_of_equiv _
  let 𝔮 : HeightOneSpectrum (𝓞 (QNeg d)) :=
    ⟨𝔭.asIdeal.comap (cO σ⁻¹).symm, inferInstance, by
      intro h
      rw [Ideal.comap_symm, Ideal.map_eq_bot_iff_of_injective (cO σ⁻¹).injective] at h
      exact 𝔭.ne_bot h⟩
  have : ((⟨_, hp⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := (inferInstance : (𝔭.asIdeal.comap (cO σ⁻¹).symm).IsMaximal)
  have h𝔮 : 𝔮 ∈ splitSet (QNeg d) E := (mem_splitSet_iff (O4 d) S ⟨_, hp⟩ 𝔮 rfl).2 hpS
  have htr := ncard_primesOver_conjField (τ : SeparableClosure (QNeg d) →ₐ[ℚ] _) σ hτ E
    (𝔭.asIdeal.comap (cO σ⁻¹).symm)
  have hpp : (𝔭.asIdeal.comap (cO σ⁻¹).symm).comap
      ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm : 𝓞 (QNeg d) →+* 𝓞 (QNeg d)) =
      𝔭.asIdeal := by
    ext x
    simp only [Ideal.mem_comap]
    have : (cO σ⁻¹).symm ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm x) = x := by
      apply RingOfIntegers.ext
      simp only [RingOfIntegers.mapRingEquiv_symm_apply]
      rw [show σ⁻¹ = σ.symm from rfl]
      exact σ.apply_symm_apply (x : QNeg d)
    rw [RingHom.coe_coe, this]
  rw [hpp] at htr
  change (𝔭.asIdeal.primesOver (𝓞 E')).ncard = Module.finrank (QNeg d) E'
  rw [hfr, ← htr]
  exact h𝔮

instance : IsAlgClosure ℚ (SeparableClosure (QNeg d)) := ⟨inferInstance, inferInstance⟩

theorem algebraMap_eq_re_im (x : QNeg d) :
    algebraMap (QNeg d) (SeparableClosure (QNeg d)) x =
      algebraMap ℚ (SeparableClosure (QNeg d)) x.re +
        algebraMap ℚ (SeparableClosure (QNeg d)) x.im *
          algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega := by
  conv_lhs => rw [← QuadraticAlgebra.re_smul_add_im_smul x]
  rw [map_add, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_one, mul_one,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

theorem algEquiv_algebraMap_eq (τ : SeparableClosure (QNeg d) ≃ₐ[ℚ] SeparableClosure (QNeg d))
    (x : QNeg d) :
    τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) x) =
      algebraMap ℚ (SeparableClosure (QNeg d)) x.re +
        algebraMap ℚ (SeparableClosure (QNeg d)) x.im *
          τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega) := by
  rw [algebraMap_eq_re_im x, map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes]

theorem tau_omega_cases (τ : SeparableClosure (QNeg d) ≃ₐ[ℚ] SeparableClosure (QNeg d)) :
    τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega) =
        algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega ∨
      τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega) =
        -algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega := by
  set w := algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega
  have hw : w * w = algebraMap ℚ (SeparableClosure (QNeg d)) (-(d : ℚ)) := by
    rw [← map_mul, ZInQ.RouteK.Redei.omega_sq, ← IsScalarTower.algebraMap_apply]
  have hτw : τ w * τ w = w * w := by
    rw [← map_mul, hw, AlgEquiv.commutes]
  exact mul_self_eq_mul_self_iff.1 hτw

theorem map_le_ringSubfield_of_fix (τ : SeparableClosure (QNeg d) ≃ₐ[ℚ] SeparableClosure (QNeg d))
    (h : τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega) =
        algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega)
    (S : Subgroup (Pic (O4 d))) :
    ((ringSubfield S).restrictScalars ℚ).map
      (τ : SeparableClosure (QNeg d) →ₐ[ℚ] SeparableClosure (QNeg d)) ≤
      (ringSubfield S).restrictScalars ℚ := by
  have hτK : ∀ x : QNeg d, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) x) =
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) x := by
    intro x
    rw [algEquiv_algebraMap_eq τ x, h, ← algebraMap_eq_re_im]
  let g : Gal(SeparableClosure (QNeg d)/QNeg d) := AlgEquiv.ofRingEquiv (f := τ.toRingEquiv) hτK
  rintro _ ⟨y, hy, rfl⟩
  exact (IntermediateField.normal_iff_forall_map_le'.1 inferInstance g) ⟨y, hy, rfl⟩

theorem map_le_ringSubfield_of_conj (τ : SeparableClosure (QNeg d) ≃ₐ[ℚ] SeparableClosure (QNeg d))
    (h : τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega) =
        -algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega)
    (S : Subgroup (Pic (O4 d))) :
    ((ringSubfield S).restrictScalars ℚ).map
      (τ : SeparableClosure (QNeg d) →ₐ[ℚ] SeparableClosure (QNeg d)) ≤
      (ringSubfield S).restrictScalars ℚ := by
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := d)
  have hτK : ∀ x : QNeg d, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) x) =
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) (σ x) := by
    intro x
    rw [algEquiv_algebraMap_eq τ x, h, algebraMap_eq_re_im (σ x), conj_apply σ hσ,
      QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    simp only [map_neg, zero_mul, add_zero]
    ring
  rintro _ ⟨y, hy, rfl⟩
  have hmem : (τ : SeparableClosure (QNeg d) →ₐ[ℚ] SeparableClosure (QNeg d)) y ∈
      conjField (τ : SeparableClosure (QNeg d) →ₐ[ℚ] SeparableClosure (QNeg d)) σ hτK
        (ringSubfield S) := ⟨y, hy, rfl⟩
  exact conjField_ringSubfield_le τ σ hσ hτK S hmem

/-- **Every subfield of `H_{d,4}` cut out by a subgroup of `Pic(O_{d,4})` is Galois over `ℚ`**
(`Gal(H_{d,4}/ℚ)` is generalized dihedral; Cox, *Primes of the form x² + ny²*, Lemma 9.3). -/
theorem normal_ringSubfield (S : Subgroup (Pic (O4 d))) :
    Normal ℚ ((ringSubfield S).restrictScalars ℚ) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro τ
  rcases tau_omega_cases τ with h | h
  · exact map_le_ringSubfield_of_fix τ h S
  · exact map_le_ringSubfield_of_conj τ h S

end Normality

end ZInQ.Contrib.TYZGenus.RingClass
