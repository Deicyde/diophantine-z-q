import ZInQKernel.Contrib.TYZGenus.RingClass
import ZInQKernel.Contrib.TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount
import ZInQKernel.Contrib.TauCeti.NumberTheory.Chebotarev.SplitsCompletely
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure
import ZInQKernel.Contrib.TauCeti.RingTheory.DedekindDomain.Different.Derivative
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.ArtinSymbol

/-!
# Galois theory of ring class fields over `ℚ` (task ring-class)

Companion of `ZInQKernel/Contrib/TYZGenus/RingClass.lean`.

* **Bauer's theorem** from Tau Ceti's Chebotarev density theorem: for finite Galois `E, E' ⊆ Kˢ`,
  if all but finitely many primes splitting completely in `E` split completely in `E'`, then
  `E' ⊆ E` (`le_of_splitSet_diff_subset`). (Neukirch, *Algebraic Number Theory*, VII.13.9;
  UNVERIFIED numbering.)
* **The splitting law** for subfields of a ring class field (`mem_splitSet_iff`).
* **Complex conjugation inverts `Pic(O_{d,4})`** (`picClass_conj`), hence `τ(E_S) = E_S` for every
  `τ ∈ Aut(Kˢ/ℚ)` and every subfield `E_S ⊆ H_{d,4}` cut out by `S ≤ Pic(O_{d,4})`
  (`normal_ringSubfield`): `Gal(H_{d,4}/ℚ)` is generalized dihedral (Cox, *Primes of the form
  x² + ny²*, Lemma 9.3; UNVERIFIED numbering).
* Consequences for TYZ: `H'_d / ℚ` and `H_{d,4} / ℚ` are normal (`normal_Hprimebar`,
  `normal_H4bar`), for every `d ≥ 1`.
* **`K_d(√−1) ⊆ H_{d,4}`** for every `d ≥ 1` (`adjI_le_H4`, `iQ_mem_H4bar`): `K(√−1)/K` is
  unramified outside 2 (Tau Ceti's different bound `natCast_mul_mem_differentIdeal_of_pow_eq`),
  a prime `𝔭 ∤ 2` with trivial class in `Pic(ℤ + 4𝓞_K)` is `β𝓞_K`, `β ∈ ℤ + 4𝓞_K`, so
  `N𝔭 ≡ 1 (mod 4)` and its Frobenius fixes `√−1`; Bauer's theorem concludes.
-/
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

variable {d : ℕ} [NeZero d] {f : ℕ} [NeZero f]

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

/-- `ℤ + f𝓞_{K_d}` is stable under the automorphisms of `K_d`. -/
theorem cO_mem_O4 (σ : QNeg d ≃ₐ[ℚ] QNeg d) {x : 𝓞 (QNeg d)} (hx : x ∈ (conductorOrder (QNeg d) f).toRingOfIntegers) :
    cO σ x ∈ (conductorOrder (QNeg d) f).toRingOfIntegers := by
  rw [mem_toRingOfIntegers] at hx ⊢
  obtain ⟨a, y, hy⟩ := hx
  refine ⟨a, cO σ y, ?_⟩
  simp only [RingOfIntegers.mapRingEquiv_apply, AlgEquiv.coe_toRingEquiv]
  rw [hy, map_add, map_mul, map_intCast, map_natCast]

theorem cO_mem_conductor (σ : QNeg d ≃ₐ[ℚ] QNeg d) {x : 𝓞 (QNeg d)} (hx : x ∈ (conductorOrder (QNeg d) f).conductor) :
    cO σ x ∈ (conductorOrder (QNeg d) f).conductor := by
  rw [NumberFieldOrder.mem_conductor_iff] at hx ⊢
  intro y
  have h := hx ((cO σ).symm y)
  have h2 := cO_mem_O4 σ (x := x * (cO σ).symm y) h
  rw [map_mul, RingEquiv.apply_symm_apply] at h2
  simpa using h2

variable (f) in
theorem comap_conductor (σ : QNeg d ≃ₐ[ℚ] QNeg d) :
    (conductorOrder (QNeg d) f).conductor.comap (cO σ).symm = (conductorOrder (QNeg d) f).conductor := by
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
    (hJ : J ∈ integralIdealsPrimeTo (conductorOrder (QNeg d) f).conductorModulus) :
    J.comap (cO σ).symm ∈
      integralIdealsPrimeTo (conductorOrder (QNeg d) f).conductorModulus := by
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
  · rw [← comap_conductor f σ, Ideal.comap_symm, Ideal.comap_symm, ← Ideal.map_sup, h1,
      Ideal.map_top]

/-- **Complex conjugation inverts Picard classes**: for `σ ≠ 1`, the class of `σ(J)` is the
inverse of the class of `J` (`J σ(J) = (N J)` is generated by an integer). -/
theorem picClass_conj (σ : QNeg d ≃ₐ[ℚ] QNeg d) (hσ : σ ≠ 1)
    (J : integralIdealsPrimeTo (conductorOrder (QNeg d) f).conductorModulus) :
    (conductorOrder (QNeg d) f).picClass ⟨_, conj_mem_primeTo σ J.2⟩ = ((conductorOrder (QNeg d) f).picClass J)⁻¹ := by
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

variable {d : ℕ} [NeZero d] {f : ℕ} [NeZero f]

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
abbrev ringSubfield (S : Subgroup (Pic (conductorOrder (QNeg d) f))) :
    IntermediateField (QNeg d) (SeparableClosure (QNeg d)) :=
  IntermediateField.lift (IntermediateField.fixedField (S.map (ringClassArtinEquiv (conductorOrder (QNeg d) f)).toMonoidHom))

instance (S : Subgroup (Pic (conductorOrder (QNeg d) f))) : FiniteDimensional (QNeg d) (ringSubfield S) :=
  LinearEquiv.finiteDimensional (IntermediateField.liftAlgEquiv _).toLinearEquiv

instance (S : Subgroup (Pic (conductorOrder (QNeg d) f))) : IsGalois (QNeg d) (ringSubfield S) := by
  have : (S.map (ringClassArtinEquiv (conductorOrder (QNeg d) f)).toMonoidHom).Normal := Subgroup.normal_of_comm _
  exact IsGalois.of_algEquiv (IntermediateField.liftAlgEquiv _)

variable (f) in
theorem finite_conductor_primes :
    {𝔭 : HeightOneSpectrum (𝓞 (QNeg d)) | (conductorOrder (QNeg d) f).conductor ≤ 𝔭.asIdeal}.Finite := by
  have h := Ideal.finite_factors (R := 𝓞 (QNeg d)) (I := (conductorOrder (QNeg d) f).conductor)
    (by simpa using (conductorOrder (QNeg d) f).conductor_ne_bot)
  refine h.subset fun 𝔭 h𝔭 => ?_
  exact Ideal.dvd_iff_le.2 h𝔭

theorem mem_primeTo_of_not_le (𝔭 : HeightOneSpectrum (𝓞 (QNeg d)))
    (h : ¬ (conductorOrder (QNeg d) f).conductor ≤ 𝔭.asIdeal) :
    𝔭.asIdeal ∈ integralIdealsPrimeTo (conductorOrder (QNeg d) f).conductorModulus := by
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
    (S : Subgroup (Pic (conductorOrder (QNeg d) f))) :
    conjField (τ : SeparableClosure (QNeg d) →ₐ[ℚ] SeparableClosure (QNeg d)) σ hτ
      (ringSubfield S) ≤ ringSubfield S := by
  set E := ringSubfield S
  set E' := conjField (τ : SeparableClosure (QNeg d) →ₐ[ℚ] SeparableClosure (QNeg d)) σ hτ E
  have hfr : Module.finrank (QNeg d) E' = Module.finrank (QNeg d) E := finrank_conjField _ _ _ _
  have : FiniteDimensional (QNeg d) E' :=
    Module.finite_of_finrank_pos (by rw [hfr]; exact Module.finrank_pos)
  have : Normal (QNeg d) E' := normal_conjField τ σ hτ E
  have : IsGalois (QNeg d) E' := IsGalois.mk
  refine le_of_splitSet_diff_subset _ (finite_conductor_primes f) ?_
  rintro 𝔭 ⟨h𝔭, hT𝔭⟩
  have hJ := mem_primeTo_of_not_le 𝔭 hT𝔭
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (conductorOrder (QNeg d) f).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := 𝔭.isMaximal
  have hS : (conductorOrder (QNeg d) f).picClass ⟨_, hJ⟩ ∈ S := (mem_splitSet_iff (conductorOrder (QNeg d) f) S ⟨_, hJ⟩ 𝔭 rfl).1 h𝔭
  have hp := conj_mem_primeTo σ⁻¹ hJ
  have hpS : (conductorOrder (QNeg d) f).picClass ⟨_, hp⟩ ∈ S := by
    rw [picClass_conj σ⁻¹ (inv_ne_one.2 hσ) ⟨_, hJ⟩]; exact inv_mem hS
  have : (𝔭.asIdeal.comap (cO σ⁻¹).symm).IsMaximal := Ideal.comap_isMaximal_of_equiv _
  let 𝔮 : HeightOneSpectrum (𝓞 (QNeg d)) :=
    ⟨𝔭.asIdeal.comap (cO σ⁻¹).symm, inferInstance, by
      intro h
      rw [Ideal.comap_symm, Ideal.map_eq_bot_iff_of_injective (cO σ⁻¹).injective] at h
      exact 𝔭.ne_bot h⟩
  have : ((⟨_, hp⟩ : integralIdealsPrimeTo (conductorOrder (QNeg d) f).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := (inferInstance : (𝔭.asIdeal.comap (cO σ⁻¹).symm).IsMaximal)
  have h𝔮 : 𝔮 ∈ splitSet (QNeg d) E := (mem_splitSet_iff (conductorOrder (QNeg d) f) S ⟨_, hp⟩ 𝔮 rfl).2 hpS
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
    (S : Subgroup (Pic (conductorOrder (QNeg d) f))) :
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
    (S : Subgroup (Pic (conductorOrder (QNeg d) f))) :
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
theorem normal_ringSubfield (S : Subgroup (Pic (conductorOrder (QNeg d) f))) :
    Normal ℚ ((ringSubfield S).restrictScalars ℚ) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro τ
  rcases tau_omega_cases τ with h | h
  · exact map_le_ringSubfield_of_fix τ h S
  · exact map_le_ringSubfield_of_conj τ h S

end Normality

section HprimeNormal

open ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp.CurveA

variable (d : ℕ) [NeZero d]

set_option maxRecDepth 10000 in
theorem Hprime_eq_ringSubfield : Hprime d = ringSubfield (Subgroup.zpowers (sigmaClass d)) := by
  rw [Hprime, ringSubfield, MonoidHom.map_zpowers]
  rfl

theorem H4_eq_ringSubfield : H4 d = ringSubfield (⊥ : Subgroup (Pic (O4 d))) := by
  rw [ringSubfield, Subgroup.map_bot, IntermediateField.fixedField_bot, IntermediateField.lift_top]

/-- **`H'_d / ℚ` is normal** (inside `K_dˢ`). -/
theorem normal_Hprime : Normal ℚ ((Hprime d).restrictScalars ℚ) := by
  rw [Hprime_eq_ringSubfield]
  exact normal_ringSubfield _

/-- **`H_{d,4} / ℚ` is normal** (inside `K_dˢ`). -/
theorem normal_H4 : Normal ℚ ((H4 d).restrictScalars ℚ) := by
  rw [H4_eq_ringSubfield]
  exact normal_ringSubfield _

omit [NeZero d] in
theorem Hprimebar_zero : Hprimebar 0 = ⊥ := by simp [Hprimebar]

omit [NeZero d] in
theorem H4bar_zero : H4bar 0 = ⊥ := by simp [H4bar]

theorem Hprimebar_eq_map : Hprimebar d = ((Hprime d).restrictScalars ℚ).map (embed d) := by
  simp [Hprimebar, NeZero.ne d]

theorem H4bar_eq_map : H4bar d = ((H4 d).restrictScalars ℚ).map (embed d) := by
  simp [H4bar, NeZero.ne d]

omit [NeZero d] in
/-- **`H'_d / ℚ` is normal**, as a subfield of `ℚ̄` (TYZ Proposition 3.2(1); for `d = 0`,
`Hprimebar 0 = ⊥`). -/
theorem normal_Hprimebar : Normal ℚ (Hprimebar d) := by
  rcases eq_or_ne d 0 with rfl | hd
  · rw [Hprimebar_zero]
    exact Normal.of_algEquiv (IntermediateField.botEquiv ℚ Qbar).symm
  · haveI : NeZero d := ⟨hd⟩
    rw [Hprimebar_eq_map]
    haveI := normal_Hprime d
    exact Normal.of_algEquiv (IntermediateField.equivMap _ (embed d))

omit [NeZero d] in
/-- **`H_{d,4} / ℚ` is normal**, as a subfield of `ℚ̄`. -/
theorem normal_H4bar : Normal ℚ (H4bar d) := by
  rcases eq_or_ne d 0 with rfl | hd
  · rw [H4bar_zero]
    exact Normal.of_algEquiv (IntermediateField.botEquiv ℚ Qbar).symm
  · haveI : NeZero d := ⟨hd⟩
    rw [H4bar_eq_map]
    haveI := normal_H4 d
    exact Normal.of_algEquiv (IntermediateField.equivMap _ (embed d))

end HprimeNormal

open Polynomial

section SqrtNegOne

variable (K : Type) [Field K] [NumberField K]

/-- A square root of `−1` in `Kˢ`. -/
def jK : SeparableClosure K :=
  (IsSepClosed.exists_pow_nat_eq (k := SeparableClosure K) (-1) 2).choose

theorem jK_sq : jK K ^ 2 = -1 :=
  (IsSepClosed.exists_pow_nat_eq (k := SeparableClosure K) (-1) 2).choose_spec

theorem isIntegral_jK : IsIntegral K (jK K) :=
  ⟨X ^ 2 + 1, monic_X_pow_add_C 1 two_ne_zero, by simp [jK_sq]⟩

/-- `K(√−1) ⊆ Kˢ`. -/
abbrev adjI : IntermediateField K (SeparableClosure K) := IntermediateField.adjoin K {jK K}

instance : FiniteDimensional K (adjI K) := IntermediateField.adjoin.finiteDimensional (isIntegral_jK K)

instance : NumberField (adjI K) := NumberField.of_module_finite K (adjI K)

theorem sq_eq_neg_one_iff {F : Type*} [CommRing F] [IsDomain F] {x y : F} (hy : y ^ 2 = -1) :
    x ^ 2 = -1 ↔ x = y ∨ x = -y := by
  rw [← hy]; exact sq_eq_sq_iff_eq_or_eq_neg

instance : Normal K (adjI K) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro g
  rw [IntermediateField.adjoin_map, Set.image_singleton, IntermediateField.adjoin_le_iff,
    Set.singleton_subset_iff]
  have h : g (jK K) ^ 2 = -1 := by rw [← map_pow, jK_sq, map_neg, map_one]
  rcases (sq_eq_neg_one_iff (jK_sq K)).1 h with h | h
  · simp only [AlgEquiv.coe_algHom, h, SetLike.mem_coe]
    exact IntermediateField.mem_adjoin_simple_self K _
  · simp only [AlgEquiv.coe_algHom, h, SetLike.mem_coe]
    exact neg_mem (IntermediateField.mem_adjoin_simple_self K _)

instance : IsGalois K (adjI K) := IsGalois.mk

theorem gen_sq : (IntermediateField.AdjoinSimple.gen K (jK K)) ^ 2 = -1 :=
  Subtype.ext (by simp [jK_sq])

/-- `√−1` as an element of `𝓞_{K(√−1)}`. -/
def jO : 𝓞 (adjI K) :=
  ⟨IntermediateField.AdjoinSimple.gen K (jK K), by
    refine ⟨X ^ 2 + 1, monic_X_pow_add_C 1 two_ne_zero, ?_⟩
    simp [gen_sq]⟩

theorem jO_sq : jO K ^ 2 = -1 := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_one]
  exact gen_sq K

theorem adjoin_jO_eq_top :
    Algebra.adjoin K {algebraMap (𝓞 (adjI K)) (adjI K) (jO K)} = ⊤ :=
  (IntermediateField.adjoin.powerBasis (isIntegral_jK K)).adjoin_gen_eq_top

variable {K}

/-- Primes `Q` of `𝓞_{K(√−1)}` not containing `2` are unramified over `𝓞_K`. -/
theorem isUnramifiedAt_of_two_notMem (Q : Ideal (𝓞 (adjI K))) [Q.IsPrime]
    (h2 : (2 : 𝓞 (adjI K)) ∉ Q) : Algebra.IsUnramifiedAt (𝓞 K) Q := by
  refine not_dvd_differentIdeal_iff.1 fun hdvd => h2 ?_
  have hmem := TauCeti.natCast_mul_mem_differentIdeal_of_pow_eq (A := 𝓞 K) (K := K)
    (L := adjI K) (B := 𝓞 (adjI K)) (adjoin_jO_eq_top K) (n := 2) (a := -1)
    (by rw [jO_sq, map_neg, map_one])
  have := Ideal.le_of_dvd hdvd hmem
  have h' : (2 : 𝓞 (adjI K)) = -(((2 : ℕ) : 𝓞 (adjI K)) * algebraMap (𝓞 K) (𝓞 (adjI K)) (-1)) := by
    simp
  rw [h']
  exact Q.neg_mem_iff.2 this

/-- **An arithmetic Frobenius at a prime of residue norm `≡ 1 (mod 4)` prime to `2` is trivial on
`K(√−1)`.** -/
theorem eq_one_of_isArithFrobAt (Q : Ideal (𝓞 (adjI K))) [Q.IsPrime]
    (h2 : (2 : 𝓞 (adjI K)) ∉ Q) (σ : adjI K ≃ₐ[K] adjI K) (hσ : IsArithFrobAt (𝓞 K) σ Q)
    (hq : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) % 4 = 1) : σ = 1 := by
  have h := hσ (jO K)
  simp only [MulSemiringAction.toAlgHom_apply] at h
  obtain ⟨k, hk⟩ : ∃ k, Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = 4 * k + 1 := ⟨Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) / 4, by omega⟩
  have hpow : jO K ^ Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = jO K := by
    rw [hk, pow_succ, pow_mul, show jO K ^ 4 = (jO K ^ 2) ^ 2 by ring, jO_sq]
    simp
  rw [hpow] at h
  have hsq : (σ • jO K) ^ 2 = -1 := by
    rw [← smul_pow', jO_sq, smul_neg, smul_one]
  have hfix : σ • jO K = jO K := by
    rcases (sq_eq_neg_one_iff (jO_sq K)).1 hsq with h1 | h1
    · exact h1
    · exfalso
      apply h2
      rw [h1] at h
      have : (-jO K - jO K) * jO K ∈ Q := Q.mul_mem_right _ h
      have e : (-jO K - jO K) * jO K = 2 := by
        have := jO_sq K
        linear_combination (-2 : 𝓞 (adjI K)) * this
      rwa [e] at this
  have hfix' : σ (IntermediateField.AdjoinSimple.gen K (jK K)) =
      IntermediateField.AdjoinSimple.gen K (jK K) := congrArg Subtype.val hfix
  apply AlgEquiv.coe_algHom_injective
  apply IntermediateField.adjoin_algHom_ext
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact hfix'

/-- **Primes of residue norm `≡ 1 (mod 4)` prime to `2` split completely in `K(√−1)`.** -/
theorem mem_splitSet_adjI (𝔭 : HeightOneSpectrum (𝓞 K)) (h2 : (2 : 𝓞 K) ∉ 𝔭.asIdeal)
    (hq : Nat.card (𝓞 K ⧸ 𝔭.asIdeal) % 4 = 1) : 𝔭 ∈ splitSet K (adjI K) := by
  have h2Q : ∀ (Q : Ideal (𝓞 (adjI K))) [Q.LiesOver 𝔭.asIdeal], (2 : 𝓞 (adjI K)) ∉ Q := by
    intro Q _ h
    apply h2
    have : algebraMap (𝓞 K) (𝓞 (adjI K)) 2 ∈ Q := by rwa [map_ofNat]
    rwa [← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def Q 𝔭.asIdeal] at this
  have hur : ∀ (Q : Ideal (𝓞 (adjI K))) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q := fun Q _ _ => isUnramifiedAt_of_two_notMem Q (h2Q Q)
  obtain ⟨Q, hQp, hQo⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 (adjI K))))
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q
  obtain ⟨σ, hσ⟩ := exists_isArithFrobAt K Q hQ
  have hσ1 : σ = 1 :=
    eq_one_of_isArithFrobAt Q (h2Q Q) σ hσ (by rwa [← Ideal.over_def Q 𝔭.asIdeal])
  have hA := artinSymbol_eq_mk_of_isArithFrobAt 𝔭.asIdeal hur Q σ hσ
  rw [hσ1, ← ConjClasses.one_eq_mk_one] at hA
  exact (artinSymbol_eq_one_iff_ncard_primesOver_eq_finrank 𝔭.asIdeal hur).1 hA

/-- The residue field of a prime not containing `2` has odd cardinality. -/
theorem card_quot_odd (𝔭 : HeightOneSpectrum (𝓞 K)) (h2 : (2 : 𝓞 K) ∉ 𝔭.asIdeal) :
    Nat.card (𝓞 K ⧸ 𝔭.asIdeal) % 2 = 1 := by
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ 𝔭.asIdeal)
  rw [Nat.card_eq_fintype_card]
  refine FiniteField.odd_card_of_char_ne_two fun hc => h2 ?_
  have : ((2 : ℕ) : 𝓞 K ⧸ 𝔭.asIdeal) = 0 := by
    rw [← hc]; exact ringChar.Nat.cast_ringChar
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
  simpa using this

end SqrtNegOne

section IInH4

open ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei ZInQ.Contrib.TYZDecomp.CurveA TauCeti.GlobalNumberFields.NumberFieldOrder

variable {d : ℕ} [NeZero d]

/-- Norms of elements of `O_{d,4} = ℤ + 4𝓞_K` are `≡ a² (mod 4)`. -/
theorem norm_of_mem_O4 (β : 𝓞 (QNeg d)) (hβ : β ∈ (O4 d).toRingOfIntegers) :
    ∃ a c : ℤ, Algebra.norm ℤ β = a ^ 2 + 4 * c := by
  obtain ⟨a, y, hy⟩ := (NumberFieldOrder.mem_toRingOfIntegers _).1 hβ
  obtain ⟨m, hm⟩ := exists_two_re y
  refine ⟨a, a * m + 4 * Algebra.norm ℤ y, ?_⟩
  have h1 := normZ_eq_re_im β
  have h2 := normZ_eq_re_im y
  rw [hy] at h1
  have hre : ((a : QNeg d) + ((4 : ℕ) : QNeg d) * (y : QNeg d)).re = a + 4 * (y : QNeg d).re := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
      QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast]
    push_cast
    ring
  have him : ((a : QNeg d) + ((4 : ℕ) : QNeg d) * (y : QNeg d)).im = 4 * (y : QNeg d).im := by
    simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast,
      QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast]
    push_cast
    ring
  rw [hre, him] at h1
  have : ((Algebra.norm ℤ β : ℤ) : ℚ) = ((a ^ 2 + 4 * (a * m + 4 * Algebra.norm ℤ y) : ℤ) : ℚ) := by
    push_cast
    rw [h1, h2, ← hm]
    ring
  exact_mod_cast this

theorem finite_two_conductor_primes :
    {𝔭 : HeightOneSpectrum (𝓞 (QNeg d)) |
      (O4 d).conductor * Ideal.span {2} ≤ 𝔭.asIdeal}.Finite := by
  have hne : (O4 d).conductor * Ideal.span {(2 : 𝓞 (QNeg d))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.mul_eq_bot, not_or]
    refine ⟨by simpa using (O4 d).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  refine (Ideal.finite_factors hne).subset fun 𝔭 h𝔭 => ?_
  exact Ideal.dvd_iff_le.2 h𝔭

/-- **`K_d(√−1) ⊆ H_{d,4}`** (genus theory of the order `ℤ + 4𝓞_K`), via Bauer's theorem: a prime
`𝔭 ∤ 2` splitting completely in `H_{d,4}` is `β𝓞_K` with `β ∈ ℤ + 4𝓞_K`, so `N𝔭 ≡ 1 (mod 4)` and
`𝔭` splits completely in `K_d(√−1)`. -/
theorem adjI_le_H4 : adjI (QNeg d) ≤ H4 d := by
  rw [H4_eq_ringSubfield]
  refine le_of_splitSet_diff_subset _ finite_two_conductor_primes ?_
  rintro 𝔭 ⟨h𝔭, hT⟩
  have hT1 : ¬ (O4 d).conductor ≤ 𝔭.asIdeal := fun h => hT (le_trans Ideal.mul_le_left h)
  have h2 : (2 : 𝓞 (QNeg d)) ∉ 𝔭.asIdeal := fun h =>
    hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h))
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := 𝔭.isMaximal
  have h1 := (mem_splitSet_iff (O4 d) ⊥ ⟨_, hJ⟩ 𝔭 rfl).1 h𝔭
  rw [Subgroup.mem_bot, picClass_eq_one_iff] at h1
  obtain ⟨β, hβ, hspan⟩ := h1
  obtain ⟨a, c, hN⟩ := norm_of_mem_O4 β hβ
  have hq : Nat.card (𝓞 (QNeg d) ⧸ 𝔭.asIdeal) = (Algebra.norm ℤ β).natAbs := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    change Ideal.absNorm (((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
      Ideal (𝓞 (QNeg d)))) = _
    rw [hspan, Ideal.absNorm_span_singleton]
  have hodd := card_quot_odd 𝔭 h2
  have hnn := normZ_nonneg (n := d) β
  refine mem_splitSet_adjI 𝔭 h2 ?_
  rw [hq] at hodd ⊢
  have hc : ((Algebra.norm ℤ β).natAbs : ℤ) = Algebra.norm ℤ β := Int.natAbs_of_nonneg hnn
  have h4 : ((Algebra.norm ℤ β).natAbs : ℤ) % 4 = 1 := by
    rw [hc, hN]
    have : ((Algebra.norm ℤ β).natAbs : ℤ) % 2 = 1 := by exact_mod_cast hodd
    rw [hc, hN] at this
    rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
    · obtain ⟨k, hk⟩ : ∃ k, a = 2 * k + a % 2 := ⟨a / 2, by omega⟩
      rw [ha] at hk
      subst hk
      ring_nf at this ⊢
      omega
  omega

/-- **`i ∈ H_{d,4}`** for every `d ≥ 1`: some square root of `−1` of `K_dˢ` lies in `H_{d,4}`. -/
theorem jK_mem_H4 : jK (QNeg d) ∈ H4 d :=
  adjI_le_H4 (IntermediateField.mem_adjoin_simple_self _ _)

omit [NeZero d] in
/-- **`i ∈ H_{d,4} ⊂ ℚ̄`** for every `d ≥ 1`. -/
theorem iQ_mem_H4bar (hd : d ≠ 0) : iQ ∈ H4bar d := by
  have : NeZero d := ⟨hd⟩
  rw [H4bar_eq_map]
  have hmem : embed d (jK (QNeg d)) ∈ ((H4 d).restrictScalars ℚ).map (embed d) :=
    ⟨jK (QNeg d), jK_mem_H4, rfl⟩
  have hsq : (embed d (jK (QNeg d))) ^ 2 = -1 := by
    rw [← map_pow, jK_sq, map_neg, map_one]
  rcases (sq_eq_neg_one_iff hsq).1 iQ_sq with h | h
  · rw [h]; exact hmem
  · rw [h]; exact neg_mem hmem

end IInH4

end ZInQ.Contrib.TYZGenus.RingClass
