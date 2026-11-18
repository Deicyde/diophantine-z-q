import ZInQKernel.Contrib.CloudB3RC53.RankCounts.GlobalH1

/-!
# RankCounts: inflation `H¹(G_{K,S₀}, 𝔽₂) ↪ H¹(G_{K,S_T}, 𝔽₂)`

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-residual-bound`, tex 4519–4520:

> Inflation from `G_{K,S₀}` into `G_{K,S_T}` is injective on `H¹` with trivial coefficients.

Lane RC6 takes this as the GLUE field `inflation : h1S0F2 ≤ h1ST` of `ResidualRankCounts`
(`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`). Here it is
PROVED for the genuine groups `G_{K,S} = GaloisGroupS K S` of `GlobalPrints.lean`:

* `normal_unramifiedOutside`: `K_S/K` is normal (a supremum of finite Galois subextensions);
  `unramifiedOutside_mono`: `S ⊆ S'` gives `K_S ⊆ K_{S'}`.
* `resUnrCont`: the restriction `G_{K,S'} → G_{K,S}`, a continuous surjective homomorphism. It is
  defined through `Gal(K̄/K)`: restriction to `K_S` factors through restriction to `K_{S'}`
  (`resAbs_eq_of_resAbs_eq`), and continuity follows because restriction
  `Gal(K̄/K) → G_{K,S'}` is a quotient map (compact to Hausdorff).
* `inflUnr`, `inflUnr_injective`: inflation on `H¹` with trivial `𝔽₂` coefficients is injective,
  through `H¹(G, 𝔽₂) = Hom_cont(G, 𝔽₂)` (`h1triv`, `GlobalH1.lean`) and surjectivity of the
  restriction.
* `RC6Inflation` (finite-dimensional target) and `RC6InflationOfPrint` (finiteness from the print
  `MilneADT_I_5_1_totallyComplex` for `S'` finite containing the primes above `2`, as `S_T` is).

Kinds: everything PROVED.
-/
noncomputable section
namespace ZInQ.Contrib.CloudB3RC53.RankCounts
open NumberField IsDedekindDomain CategoryTheory Topology

variable (K : Type) [Field K] [NumberField K]

/-- the property defining the finite Galois subextensions in `unramifiedOutside` -/
abbrev UnrGal (S : Set (HeightOneSpectrum (𝓞 K))) (L : IntermediateField K (AlgebraicClosure K)) :
    Prop := FiniteDimensional K L ∧ Normal K L ∧ IsUnramifiedOutside K S L

omit [NumberField K] in
theorem unramifiedOutside_eq_iSup_subtype (S : Set (HeightOneSpectrum (𝓞 K))) :
    unramifiedOutside K S = ⨆ (L : {L : IntermediateField K (AlgebraicClosure K) // UnrGal K S L}),
      (L : IntermediateField K (AlgebraicClosure K)) := by
  rw [unramifiedOutside, iSup_subtype']

instance normal_unramifiedOutside (S : Set (HeightOneSpectrum (𝓞 K))) :
    Normal K (unramifiedOutside K S) := by
  rw [unramifiedOutside_eq_iSup_subtype]
  have : ∀ L : {L : IntermediateField K (AlgebraicClosure K) // UnrGal K S L},
      Normal K ((L : IntermediateField K (AlgebraicClosure K))) := fun L => L.2.2.1
  exact IntermediateField.normal_iSup K _ _

omit [NumberField K] in
theorem unramifiedOutside_mono {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S') :
    unramifiedOutside K S ≤ unramifiedOutside K S' := by
  unfold unramifiedOutside
  refine iSup₂_le fun L hL => le_iSup₂_of_le L ⟨hL.1, hL.2.1, fun v hv => hL.2.2 v (fun hvS => hv (h hvS))⟩ le_rfl


section Restriction
variable {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S')

/-- Restriction `Gal(K̄/K) → G_{K,S}`. -/
abbrev resAbs (S : Set (HeightOneSpectrum (𝓞 K))) :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* GaloisGroupS K S :=
  AlgEquiv.restrictNormalHom (unramifiedOutside K S)

omit [NumberField K] in
theorem resAbs_apply_coe (S : Set (HeightOneSpectrum (𝓞 K)))
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : unramifiedOutside K S) :
    ((resAbs K S σ x : unramifiedOutside K S) : AlgebraicClosure K) = σ x :=
  AlgEquiv.restrictNormal_commutes σ (unramifiedOutside K S) x

omit [NumberField K] in
theorem resAbs_surjective (S : Set (HeightOneSpectrum (𝓞 K))) :
    Function.Surjective (resAbs K S) :=
  AlgEquiv.restrictNormalHom_surjective _

omit [NumberField K] in
/-- The restriction to `K_S` is determined by the restriction to `K_{S'} ⊇ K_S`. -/
theorem resAbs_eq_of_resAbs_eq (h : S ⊆ S') {σ₁ σ₂ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (h12 : resAbs K S' σ₁ = resAbs K S' σ₂) : resAbs K S σ₁ = resAbs K S σ₂ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have hx : (x : AlgebraicClosure K) ∈ unramifiedOutside K S' := unramifiedOutside_mono K h x.2
  have := congrArg (fun τ : GaloisGroupS K S' =>
    ((τ ⟨(x : AlgebraicClosure K), hx⟩ : unramifiedOutside K S') : AlgebraicClosure K)) h12
  simp only [resAbs_apply_coe] at this
  rw [resAbs_apply_coe, resAbs_apply_coe]
  exact this

/-- **The restriction `G_{K,S'} → G_{K,S}` for `S ⊆ S'`** (defined through `Gal(K̄/K)`). -/
noncomputable def resUnr : GaloisGroupS K S' →* GaloisGroupS K S where
  toFun τ := resAbs K S (Classical.choose (resAbs_surjective K S' τ))
  map_one' := by
    rw [← map_one (resAbs K S)]
    apply resAbs_eq_of_resAbs_eq K h
    rw [Classical.choose_spec (resAbs_surjective K S' 1), map_one]
  map_mul' τ₁ τ₂ := by
    rw [← map_mul (resAbs K S)]
    apply resAbs_eq_of_resAbs_eq K h
    rw [map_mul, Classical.choose_spec (resAbs_surjective K S' _),
      Classical.choose_spec (resAbs_surjective K S' τ₁),
      Classical.choose_spec (resAbs_surjective K S' τ₂)]

omit [NumberField K] in
theorem resUnr_comp (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    resUnr K h (resAbs K S' σ) = resAbs K S σ :=
  resAbs_eq_of_resAbs_eq K h (Classical.choose_spec (resAbs_surjective K S' _))

omit [NumberField K] in
theorem resUnr_surjective : Function.Surjective (resUnr K h) := by
  intro τ
  obtain ⟨σ, rfl⟩ := resAbs_surjective K S τ
  exact ⟨resAbs K S' σ, resUnr_comp K h σ⟩

theorem resUnr_continuous : Continuous (resUnr K h) := by
  have hq : Topology.IsQuotientMap (resAbs K S') :=
    Topology.IsQuotientMap.of_surjective_continuous (resAbs_surjective K S')
      (InfiniteGalois.restrictNormalHom_continuous (unramifiedOutside K S'))
  rw [hq.continuous_iff]
  have : (resUnr K h) ∘ (resAbs K S') = resAbs K S := funext (resUnr_comp K h)
  rw [this]
  exact InfiniteGalois.restrictNormalHom_continuous (unramifiedOutside K S)

/-- The restriction as a continuous homomorphism. -/
noncomputable def resUnrCont : ContinuousMonoidHom (GaloisGroupS K S') (GaloisGroupS K S) :=
  { resUnr K h with continuous_toFun := resUnr_continuous K h }

theorem resUnrCont_apply (τ : GaloisGroupS K S') : resUnrCont K h τ = resUnr K h τ := rfl
end Restriction

section Inflation
variable {S S' : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S')

/-- Pullback of continuous homomorphisms along the restriction `G_{K,S'} → G_{K,S}`. -/
noncomputable def pullUnr :
    Additive (ContinuousMonoidHom (GaloisGroupS K S) (Multiplicative (ZMod 2))) →+
      Additive (ContinuousMonoidHom (GaloisGroupS K S') (Multiplicative (ZMod 2))) where
  toFun ψ := Additive.ofMul ((Additive.toMul ψ).comp (resUnrCont K h))
  map_zero' := by
    apply Additive.toMul.injective
    ext τ
    simp
  map_add' ψ₁ ψ₂ := by
    apply Additive.toMul.injective
    ext τ
    simp

theorem pullUnr_injective : Function.Injective (pullUnr K h) := by
  intro ψ₁ ψ₂ he
  apply Additive.toMul.injective
  ext τ
  obtain ⟨τ', rfl⟩ := resUnr_surjective K h τ
  have := congrArg (fun ψ => (Additive.toMul ψ) τ') he
  simpa [pullUnr, resUnrCont_apply] using this

/-- **Inflation `H¹(G_{K,S}, 𝔽₂) → H¹(G_{K,S'}, 𝔽₂)` for `S ⊆ S'`**, through
`H¹(G, 𝔽₂) = Hom_cont(G, 𝔽₂)` (`h1triv`). -/
noncomputable def inflUnr :
    continuousCohomology 1 (trivialRepS (GaloisGroupS K S) (ZMod 2)) →+
      continuousCohomology 1 (trivialRepS (GaloisGroupS K S') (ZMod 2)) :=
  (h1triv (GaloisGroupS K S') (ZMod 2)).symm.toAddMonoidHom.comp
    ((pullUnr K h).comp (h1triv (GaloisGroupS K S) (ZMod 2)).toAddMonoidHom)

theorem inflUnr_injective : Function.Injective (inflUnr K h) :=
  (h1triv (GaloisGroupS K S') (ZMod 2)).symm.injective.comp
    ((pullUnr_injective K h).comp (h1triv (GaloisGroupS K S) (ZMod 2)).injective)

end Inflation

/-- **RC6's field `inflation : h1S0F2 ≤ h1ST` (tex 4519–4520; PROVED).** "Inflation from
`G_{K,S₀}` into `G_{K,S_T}` is injective on `H¹` with trivial coefficients": for `S ⊆ S'` and
`H¹(G_{K,S'}, 𝔽₂)` finite-dimensional, `dim H¹(G_{K,S}, 𝔽₂) ≤ dim H¹(G_{K,S'}, 𝔽₂)`. RC6:
`S = S₀`, `S' = S_T`. Source of the field text:
`ZInQKernel/Contrib/OneProof/RC/Limits/ResidualBound.lean`. -/
def RC6Inflation : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (S S' : Set (HeightOneSpectrum (𝓞 K))), S ⊆ S' →
    Module.Finite (ZMod 2) (continuousCohomology 1 (trivialRepS (GaloisGroupS K S') (ZMod 2))) →
    Module.finrank (ZMod 2) (continuousCohomology 1 (trivialRepS (GaloisGroupS K S) (ZMod 2))) ≤
      Module.finrank (ZMod 2) (continuousCohomology 1 (trivialRepS (GaloisGroupS K S') (ZMod 2)))

theorem rc6Inflation_proof : RC6Inflation := by
  intro K _ _ S S' h _
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (inflUnr K h).toZModLinearMap 2) (inflUnr_injective K h)

/-- **RC6's `inflation` from the print (PROVED from `MilneADT_I_5_1_totallyComplex`).** For a
totally complex number field `K` and `S ⊆ S'` with `S'` finite and containing the primes above
`2` (RC6: `S_T`, tex 4469–4475), the finiteness hypothesis of `RC6Inflation` is supplied by
Milne ADT I.5.1, giving `dim H¹(G_{K,S}, 𝔽₂) ≤ dim H¹(G_{K,S'}, 𝔽₂)`. -/
def RC6InflationOfPrint : Prop :=
  MilneADT_I_5_1_totallyComplex →
  ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K →
    ∀ (S S' : Set (HeightOneSpectrum (𝓞 K))), S ⊆ S' → S'.Finite →
      (∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S') →
    Module.finrank (ZMod 2) (continuousCohomology 1 (trivialRepS (GaloisGroupS K S) (ZMod 2))) ≤
      Module.finrank (ZMod 2) (continuousCohomology 1 (trivialRepS (GaloisGroupS K S') (ZMod 2)))

theorem rc6InflationOfPrint_proof : RC6InflationOfPrint := by
  intro h51 K _ _ hK S S' h hS' h2
  have hfin := (h51 K hK S' hS' h2 (trivialRepS (GaloisGroupS K S') (ZMod 2))
    (inferInstanceAs (Finite (ZMod 2))) (inferInstanceAs (DiscreteTopology (ZMod 2)))
    (continuous_trivialRepS_action _ _)).2.1
  exact rc6Inflation_proof K S S' h hfin

end ZInQ.Contrib.CloudB3RC53.RankCounts
