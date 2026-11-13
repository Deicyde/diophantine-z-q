import Mathlib

/-! # g12-det: `ResQFiniteIndex` (copied verbatim from scratch/g0-mod-galois/part_det.lean, with
its dependencies `PkgI4.Qbar`, `PkgI4.GQ` (Split.lean L3940-3943), `G0Galois.resQ`, `qEmbRing`,
`qEmb`, `resQ_spec`, `eq_resQ` (part_galois.lean)), proved from Mathlib alone. -/

namespace PkgI4

abbrev Qbar := AlgebraicClosure ℚ

abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

end PkgI4

noncomputable section

namespace G0Galois

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). Its image is `G_K` inside `G_ℚ` for the
embedding `K ↪ ℚ̄` that the map chooses. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- The embedding `ℚ̄ → K̄` that `Field.absoluteGaloisGroup.map` chooses (`IsAlgClosed.lift`). -/
def qEmbRing (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →+* AlgebraicClosure K :=
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom

/-- `qEmbRing` as a `ℚ`-algebra map (the `i` of g0-mod-newform's `ModData`). -/
def qEmb (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K :=
  (qEmbRing K).toRatAlgHom

/-- `qEmb K ∘ resQ K τ = τ ∘ qEmb K` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
lemma resQ_spec (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure ℚ) :
    qEmbRing K (resQ K τ x) = τ (qEmbRing K x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

/-- `resQ K τ` is the only `σ ∈ G_ℚ` with `qEmb K ∘ σ = τ ∘ qEmb K`. -/
lemma eq_resQ (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (σ : PkgI4.GQ) (h : ∀ x, qEmb K (σ x) = τ (qEmb K x)) : σ = resQ K τ := by
  apply AlgEquiv.ext; intro x
  exact (qEmbRing K).injective ((h x).trans (resQ_spec K τ x).symm)

/-- **`G_K` has finite index in `G_ℚ` (GLUE, unproved; Galois theory: the index is `[K:ℚ]`).** -/
def ResQFiniteIndex : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], (resQ K).range.FiniteIndex

/-! ## Proof -/

/-- Every element of `K̄` is integral over `ℚ` (`K̄/K` algebraic, `K/ℚ` finite). -/
lemma isIntegral_rat (K : Type) [Field K] [NumberField K] (y : AlgebraicClosure K) :
    IsIntegral ℚ y := by
  have : Algebra.IsIntegral ℚ K := inferInstance
  have : Algebra.IsIntegral K (AlgebraicClosure K) := inferInstance
  exact (Algebra.IsIntegral.trans (R := ℚ) (A := K) (B := AlgebraicClosure K)).isIntegral y

/-- `qEmbRing K : ℚ̄ → K̄` is bijective (an algebraically closed field into an algebraic
extension of `ℚ`). -/
lemma qEmbRing_bijective (K : Type) [Field K] [NumberField K] :
    Function.Bijective (qEmbRing K) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  intro y
  obtain ⟨p, hp, hpy⟩ := isIntegral_rat K y
  refine ⟨p.map (algebraMap ℚ (AlgebraicClosure ℚ)), hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  have : (qEmbRing K).comp (algebraMap ℚ (AlgebraicClosure ℚ)) = algebraMap ℚ (AlgebraicClosure K) :=
    RingHom.ext_rat _ _
  rw [this]
  exact hpy

/-- `qEmbRing K` as a ring isomorphism. -/
def qEquiv (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ ≃+* AlgebraicClosure K :=
  RingEquiv.ofBijective (qEmbRing K) (qEmbRing_bijective K)

/-- The embedding `K → ℚ̄` determined by `qEmbRing` (`K ⊆ K̄ ≅ ℚ̄`). -/
def kEmb (K : Type) [Field K] [NumberField K] : K →ₐ[ℚ] AlgebraicClosure ℚ :=
  ((qEquiv K).symm.toRingHom.comp (algebraMap K (AlgebraicClosure K))).toRatAlgHom

/-- The image `K' ⊆ ℚ̄` of `K`. -/
def kField (K : Type) [Field K] [NumberField K] : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  (kEmb K).fieldRange

lemma finrank_kField (K : Type) [Field K] [NumberField K] :
    Module.finrank ℚ (kField K) = Module.finrank ℚ K :=
  (AlgEquiv.ofInjectiveField (kEmb K)).toLinearEquiv.finrank_eq.symm

/-- The fixing subgroup of `K'` is contained in the image of `resQ K`. -/
lemma fixingSubgroup_le_range (K : Type) [Field K] [NumberField K] :
    (kField K).fixingSubgroup ≤ (resQ K).range := by
  intro σ hσ
  let e := qEquiv K
  let τ0 : AlgebraicClosure K ≃+* AlgebraicClosure K :=
    e.symm.trans ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv.trans e)
  have hfix : ∀ k : K, τ0 (algebraMap K (AlgebraicClosure K) k) =
      algebraMap K (AlgebraicClosure K) k := by
    intro k
    have hk : e.symm (algebraMap K (AlgebraicClosure K) k) ∈ kField K := ⟨k, rfl⟩
    have h1 : σ (e.symm (algebraMap K (AlgebraicClosure K) k)) =
        e.symm (algebraMap K (AlgebraicClosure K) k) := hσ ⟨_, hk⟩
    change e (σ (e.symm (algebraMap K (AlgebraicClosure K) k))) = _
    rw [h1, RingEquiv.apply_symm_apply]
  let τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := AlgEquiv.ofRingEquiv hfix
  refine ⟨τ, ?_⟩
  symm
  apply eq_resQ
  intro x
  change qEmbRing K (σ x) = e (σ (e.symm (qEmbRing K x)))
  have : e.symm (qEmbRing K x) = x := e.symm_apply_apply x
  rw [this]
  rfl

/-- **`ResQFiniteIndex`, proved** (Mathlib only). -/
theorem resQFiniteIndex : ResQFiniteIndex := by
  intro K _ _
  haveI : FiniteDimensional ℚ (kField K) :=
    (AlgEquiv.ofInjectiveField (kEmb K)).toLinearEquiv.finiteDimensional
  have hidx : (kField K).fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index, finrank_kField]
    exact Module.finrank_pos.ne'
  have : (kField K).fixingSubgroup.FiniteIndex := ⟨hidx⟩
  exact Subgroup.finiteIndex_of_le (fixingSubgroup_le_range K)

end G0Galois

end

#print axioms G0Galois.resQFiniteIndex
