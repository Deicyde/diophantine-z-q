import ZInQKernel.Contrib.TYZGenus.RingClassGenus
import ZInQKernel.Contrib.TYZGenus.RingClassBridge

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain

noncomputable section
namespace ZInQ.Contrib.TYZGenus.RingClass

section ConjInvertsArtin

open ZInQ.RouteK.Rank5b ZInQ.RouteK.Redei

variable {d : ℕ} [NeZero d] (τ : SeparableClosure (QNeg d) ≃ₐ[ℚ] SeparableClosure (QNeg d))

theorem mem_H4_of_mem (x : SeparableClosure (QNeg d)) (hx : x ∈ H4 d) : τ x ∈ H4 d := by
  have h := IntermediateField.normal_iff_forall_map_le'.1 (normal_H4 d) τ
  exact h ⟨x, hx, rfl⟩

/-- `τ` restricted to `H_{d,4}` (a ring automorphism; `τ` need not be `K`-linear). -/
def tauH : H4 d ≃+* H4 d where
  toFun x := ⟨τ x, mem_H4_of_mem τ x x.2⟩
  invFun x := ⟨τ.symm x, mem_H4_of_mem τ.symm x x.2⟩
  left_inv x := Subtype.ext (τ.symm_apply_apply _)
  right_inv x := Subtype.ext (τ.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul τ _ _)
  map_add' x y := Subtype.ext (map_add τ _ _)

@[simp] theorem coe_tauH (x : H4 d) : ((tauH τ x : H4 d) : SeparableClosure (QNeg d)) = τ x := rfl
@[simp] theorem coe_tauH_symm (x : H4 d) :
    (((tauH τ).symm x : H4 d) : SeparableClosure (QNeg d)) = τ.symm x := rfl

variable (σ : QNeg d ≃ₐ[ℚ] QNeg d)
  (hτ : ∀ k, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) k) =
    algebraMap (QNeg d) (SeparableClosure (QNeg d)) (σ k))

include hτ in
theorem tauH_algebraMap (k : QNeg d) :
    tauH τ (algebraMap (QNeg d) (H4 d) k) = algebraMap (QNeg d) (H4 d) (σ k) :=
  Subtype.ext (hτ k)

include hτ in
theorem tauH_symm_algebraMap (k : QNeg d) :
    (tauH τ).symm (algebraMap (QNeg d) (H4 d) k) = algebraMap (QNeg d) (H4 d) (σ.symm k) := by
  apply (tauH τ).injective
  rw [RingEquiv.apply_symm_apply, tauH_algebraMap τ σ hτ, AlgEquiv.apply_symm_apply]

/-- `τ g τ⁻¹ ∈ Gal(H_{d,4}/K_d)` for `g ∈ Gal(H_{d,4}/K_d)`. -/
def conjGal (g : Gal(H4 d/QNeg d)) : Gal(H4 d/QNeg d) :=
  AlgEquiv.ofRingEquiv (f := (tauH τ).symm.trans (g.toRingEquiv.trans (tauH τ))) (fun k => by
    simp only [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv]
    rw [tauH_symm_algebraMap τ σ hτ, AlgEquiv.commutes, tauH_algebraMap τ σ hτ,
      AlgEquiv.apply_symm_apply])

theorem conjGal_apply (g : Gal(H4 d/QNeg d)) (x : H4 d) :
    conjGal τ σ hτ g x = tauH τ (g ((tauH τ).symm x)) := rfl

/-- `τ` on `𝓞_{H_{d,4}}`. -/
abbrev tauO : 𝓞 (H4 d) ≃+* 𝓞 (H4 d) := RingOfIntegers.mapRingEquiv (tauH τ)

include hτ in
theorem tauO_symm_algebraMap (x : 𝓞 (QNeg d)) :
    (tauO τ).symm (algebraMap (𝓞 (QNeg d)) (𝓞 (H4 d)) x) =
      algebraMap (𝓞 (QNeg d)) (𝓞 (H4 d)) ((cO σ).symm x) := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.mapRingEquiv_symm_apply, RingOfIntegers.map_mk]
  rw [show ((algebraMap (𝓞 (QNeg d)) (𝓞 (H4 d)) x : 𝓞 (H4 d)) : H4 d) =
      algebraMap (QNeg d) (H4 d) (x : QNeg d) from rfl, tauH_symm_algebraMap τ σ hτ]
  rfl

theorem conjGal_smul (g : Gal(H4 d/QNeg d)) (y : 𝓞 (H4 d)) :
    conjGal τ σ hτ g • y = tauO τ (g • (tauO τ).symm y) := by
  apply RingOfIntegers.ext
  rfl

include hτ in
theorem under_comap_tauO (Q : Ideal (𝓞 (H4 d))) :
    (Q.comap (tauO τ).symm).under (𝓞 (QNeg d)) =
      (Q.under (𝓞 (QNeg d))).comap (cO σ).symm := by
  ext x
  simp only [Ideal.under_def, Ideal.mem_comap, RingHom.coe_coe]
  rw [tauO_symm_algebraMap τ σ hτ]

theorem card_quot_comap_equiv {R : Type*} [CommRing R] (I : Ideal R) (e : R ≃+* R) :
    Nat.card (R ⧸ I.comap e) = Nat.card (R ⧸ I) :=
  Nat.card_congr (Ideal.quotientEquiv _ I e
    (Ideal.map_comap_of_surjective _ e.surjective I).symm).toEquiv

include hτ in
/-- **`τ` transports arithmetic Frobenius elements**: if `g` is an arithmetic Frobenius at `Q`, then
`τ g τ⁻¹` is one at `τ(Q)`. -/
theorem isArithFrobAt_conjGal (g : Gal(H4 d/QNeg d)) (Q : Ideal (𝓞 (H4 d)))
    (hg : IsArithFrobAt (𝓞 (QNeg d)) g Q) :
    IsArithFrobAt (𝓞 (QNeg d)) (conjGal τ σ hτ g)
      (Q.comap (tauO τ).symm) := by
  intro y
  have hq : Nat.card (𝓞 (QNeg d) ⧸
      (Q.comap (tauO τ).symm).under (𝓞 (QNeg d))) =
      Nat.card (𝓞 (QNeg d) ⧸ Q.under (𝓞 (QNeg d))) := by
    rw [under_comap_tauO τ σ hτ, card_quot_comap_equiv]
  simp only [MulSemiringAction.toAlgHom_apply, Ideal.mem_comap, RingHom.coe_coe]
  rw [hq, map_sub, map_pow, conjGal_smul, RingEquiv.symm_apply_apply]
  have := hg ((tauO τ).symm y)
  simpa only [MulSemiringAction.toAlgHom_apply] using this

/-- The action of `σ` on the primes of `K_d`. -/
def conjPrime (𝔭 : HeightOneSpectrum (𝓞 (QNeg d))) : HeightOneSpectrum (𝓞 (QNeg d)) :=
  haveI : (𝔭.asIdeal.comap (cO σ).symm).IsMaximal :=
    Ideal.comap_isMaximal_of_equiv _
  ⟨𝔭.asIdeal.comap (cO σ).symm, inferInstance, by
    intro h
    rw [Ideal.comap_symm, Ideal.map_eq_bot_iff_of_injective (cO σ).injective] at h
    exact 𝔭.ne_bot h⟩

theorem conjPrime_injective : Function.Injective (conjPrime σ) := by
  intro 𝔭 𝔮 h
  apply HeightOneSpectrum.ext
  have := congrArg HeightOneSpectrum.asIdeal h
  exact Ideal.comap_injective_of_surjective _ (cO σ).symm.surjective this

set_option maxRecDepth 10000 in
include hτ in
/-- **Complex conjugation inverts the Artin symbols of `H_{d,4}`**: for `τ ∈ Aut(K_dˢ/ℚ)` acting on
`K_d` by the nontrivial automorphism, `τ ∘ Art(c) ∘ τ⁻¹ = Art(c⁻¹)` on `H_{d,4}` (TYZ: "`c` inverts
`Cl'_n`", `rv-tyz-inputs.md` §1.5; Cox, *Primes of the form x² + ny²*, Lemma 9.3). Proof:
Chebotarev gives a prime `𝔭` in the class of `c` with `σ(𝔭)` unramified; `τ` carries the Frobenius at
`Q | 𝔭` to a Frobenius at `τ(Q) | σ(𝔭)`, and `σ(𝔭)` has class `c⁻¹` (`picClass_conj`). -/
theorem conjGal_artin4 (hσ : σ ≠ 1) (c : Pic (O4 d)) :
    conjGal τ σ hτ (artin4 d c) = artin4 d c⁻¹ := by
  set T : Set (HeightOneSpectrum (𝓞 (QNeg d))) :=
    {𝔭 | (O4 d).conductor ≤ 𝔭.asIdeal} ∪
      conjPrime σ ⁻¹' (NumberField.Chebotarev.ramifiedPrimes (QNeg d) (H4 d) : Set (HeightOneSpectrum (𝓞 (QNeg d))))
  have hT : T.Finite := (finite_conductor_primes 4).union
    ((NumberField.Chebotarev.ramifiedPrimes (QNeg d) (H4 d)).finite_toSet.preimage (conjPrime_injective σ).injOn)
  have hD := NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet (QNeg d) (H4 d)
    (ConjClasses.mk (ringClassArtinEquiv (O4 d) c))
  have hδ : (Nat.card (ConjClasses.mk (ringClassArtinEquiv (O4 d) c)).carrier : ℝ) /
      Nat.card (H4 d ≃ₐ[QNeg d] H4 d) ≠ 0 := by
    apply div_ne_zero
    · have : Nonempty (ConjClasses.mk (ringClassArtinEquiv (O4 d) c)).carrier :=
        ⟨⟨_, ConjClasses.mem_carrier_mk⟩⟩
      exact_mod_cast (Nat.card_pos (α := (ConjClasses.mk
        (ringClassArtinEquiv (O4 d) c)).carrier)).ne'
    · exact_mod_cast (Nat.card_pos (α := H4 d ≃ₐ[QNeg d] H4 d)).ne'
  obtain ⟨𝔭, h𝔭, h𝔭T⟩ := ((hD.infinite hδ).sdiff hT).nonempty
  rw [Set.mem_union, not_or] at h𝔭T
  obtain ⟨hT1, hT2⟩ := h𝔭T
  have hJ := mem_primeTo_of_not_le 𝔭 hT1
  obtain ⟨⟨Q, hQp, hQo⟩, hF⟩ :=
    NumberField.Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk h𝔭
  have hur := NumberField.Chebotarev.isUnramifiedAt_of_mem_frobeniusPrimeSet h𝔭 Q
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := 𝔭.isMaximal
  have : Q.LiesOver ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))) := hQo
  have hc : (O4 d).picClass ⟨_, hJ⟩ = c :=
    (ringClassArtinEquiv (O4 d)).injective (isArithFrobAt_eq_of_isUnramifiedAt
      (isArithFrobAt_ringClassArtinEquiv_picClass (O4 d) ⟨_, hJ⟩ Q) hF)
  -- the transported prime
  obtain ⟨Q', hQ'⟩ : ∃ Q' : Ideal (𝓞 (H4 d)), Q' = Q.comap (tauO τ).symm := ⟨_, rfl⟩
  have hJ' := conj_mem_primeTo σ hJ
  have : ((⟨_, hJ'⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))).IsMaximal := (conjPrime σ 𝔭).isMaximal
  have : Q'.IsPrime := hQ' ▸ Ideal.comap_isPrime _ _
  have hunder : Q'.under (𝓞 (QNeg d)) =
      𝔭.asIdeal.comap (cO σ).symm := by
    rw [hQ', under_comap_tauO τ σ hτ, ← Ideal.over_def Q 𝔭.asIdeal]
  have : Q'.LiesOver ((⟨_, hJ'⟩ : integralIdealsPrimeTo (O4 d).conductorModulus) :
    Ideal (𝓞 (QNeg d))) := ⟨hunder.symm⟩
  have hur' : Algebra.IsUnramifiedAt (𝓞 (QNeg d)) Q' := by
    have h := hT2
    rw [Set.mem_preimage, Finset.mem_coe, NumberField.Chebotarev.mem_ramifiedPrimes_iff,
      not_not] at h
    have : Q'.LiesOver (conjPrime σ 𝔭).asIdeal := ⟨hunder.symm⟩
    exact h Q'
  have hF' := isArithFrobAt_ringClassArtinEquiv_picClass (O4 d) ⟨_, hJ'⟩ Q'
  have hG := isArithFrobAt_conjGal τ σ hτ (artin4 d c) Q hF
  rw [← hQ'] at hG
  rw [isArithFrobAt_eq_of_isUnramifiedAt hG hF', picClass_conj σ hσ ⟨_, hJ⟩, hc]

include hτ in
theorem conj_artin4_apply (hσ : σ ≠ 1) (c : Pic (O4 d)) (x : H4 d) :
    τ ((artin4 d c ((tauH τ).symm x) : H4 d) : SeparableClosure (QNeg d)) =
      ((artin4 d c⁻¹ x : H4 d) : SeparableClosure (QNeg d)) := by
  have := congrArg (fun g : Gal(H4 d/QNeg d) => ((g x : H4 d) : SeparableClosure (QNeg d)))
    (conjGal_artin4 τ σ hτ hσ c)
  simpa only [conjGal_apply, coe_tauH] using this

theorem exists_sigma_of_neg
    (h : τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega) =
      -algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega) :
    ∃ σ : QNeg d ≃ₐ[ℚ] QNeg d, σ ≠ 1 ∧ ∀ k, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) k) =
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) (σ k) := by
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := d)
  refine ⟨σ, hσ, fun x => ?_⟩
  rw [algEquiv_algebraMap_eq τ x, h, algebraMap_eq_re_im (σ x), conj_apply σ hσ,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  simp only [map_neg, zero_mul, add_zero]
  ring

end ConjInvertsArtin

end ZInQ.Contrib.TYZGenus.RingClass

namespace ZInQ.Contrib.TYZGenus.RingClassBridge

open ZInQ.Contrib.TYZGenus.RingClass ZInQ.Contrib.TYZGenus.Package ZInQ.Contrib.TYZDecomp.CurveA
  ZInQ.RouteK.Rank5b TauCeti.GlobalNumberFields

/-- **Complex conjugation inverts `Cl'` in `ℚ̄`**: if `γ ∈ Gal(ℚ̄/ℚ)` is nontrivial on `K_n` and `ρ`
acts on `H_{n,4}` as the Artin symbol of `c`, then `γργ⁻¹` acts as the Artin symbol of `c⁻¹`. -/
theorem actsAsArtin4_conj {n : ℕ} [NeZero n] {γ ρ : ZInQ.Contrib.TYZGenus.CM.GalQ}
    {c : Pic (O4 n)}
    (hγ : γ (embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) ≠
      embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega))
    (hρ : ActsAsArtin4 ρ n c) : ActsAsArtin4 (γ * ρ * γ⁻¹) n c⁻¹ := by
  have hb := (Algebra.IsAlgebraic.algHom_bijective₂ (embed n)
    (IsAlgClosed.lift : Qbar →ₐ[ℚ] SeparableClosure (QNeg n))).1
  set e := AlgEquiv.ofBijective (embed n) hb
  set τ : SeparableClosure (QNeg n) ≃ₐ[ℚ] SeparableClosure (QNeg n) := e.trans (γ.trans e.symm)
  have he : ∀ y, e y = embed n y := fun y => rfl
  have hγτ : ∀ y, γ (embed n y) = embed n (τ y) := by
    intro y
    rw [← he, ← he]
    simp [τ]
  have hγτ' : ∀ y, γ⁻¹ (embed n y) = embed n (τ.symm y) := by
    intro y
    apply γ.injective
    rw [show γ (γ⁻¹ (embed n y)) = embed n y from γ.apply_symm_apply _, hγτ, τ.apply_symm_apply]
  have hneg : τ (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega) =
      -algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega := by
    rcases tau_omega_cases τ with h | h
    · exfalso; apply hγ; rw [hγτ, h]
    · exact h
  obtain ⟨σ, hσ, hτσ⟩ := exists_sigma_of_neg τ hneg
  intro x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hγτ']
  have h1 := hρ ((tauH τ).symm x)
  rw [coe_tauH_symm] at h1
  rw [h1, hγτ, conj_artin4_apply τ σ hτσ hσ c x]

end ZInQ.Contrib.TYZGenus.RingClassBridge
