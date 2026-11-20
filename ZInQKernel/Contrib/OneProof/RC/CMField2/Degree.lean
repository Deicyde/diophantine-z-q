import ZInQKernel.Contrib.OneProof.RC.CMField2.Integrality
import Mathlib.FieldTheory.PrimitiveElement
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.Global.Orders.RayClass

/-! Degree bound by counting conjugates. Provenance (c). -/

noncomputable section

open NumberField Module IntermediateField TauCeti.GlobalNumberFields

namespace ZInQ.Manuscript.RC.CMField2

variable {K : Type} [Field K] [NumberField K]

/-- Exact-order conjugacy, the remaining comparison in the modular-polynomial degree route.
Every rational embedding of the field of one singular modulus lands on a value from an
invertible ideal of the same embedded order. -/
def ConjugateSingularModulus : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ) (I : O.invertibleProperFractionalIdeals)
    (σ : ℚ⟮singularModulus O hk hc κ I⟯ →ₐ[ℚ] ℂ),
    ∃ J : O.invertibleProperFractionalIdeals,
      σ (AdjoinSimple.gen ℚ (singularModulus O hk hc κ I)) = singularModulus O hk hc κ J

set_option maxHeartbeats 800000 in
/-- An embedding of a simple extension is determined by the image of its generator;
if all images lie in a finite family, its degree is bounded by the size of the family. -/
theorem finrank_adjoin_le_of_conjugate_family {F ι : Type} [Field F] [CharZero F] [Algebra F ℂ]
    [Finite ι] (j : ℂ) (hj : IsIntegral F j) (v : ι → ℂ)
    (hv : ∀ σ : F⟮j⟯ →ₐ[F] ℂ, ∃ i, σ (AdjoinSimple.gen F j) = v i) :
    finrank F F⟮j⟯ ≤ Nat.card ι := by
  classical
  let := IntermediateField.adjoin.finiteDimensional hj
  let i (σ : F⟮j⟯ →ₐ[F] ℂ) := (hv σ).choose
  have hi (σ : F⟮j⟯ →ₐ[F] ℂ) : σ (AdjoinSimple.gen F j) = v (i σ) := (hv σ).choose_spec
  have hinj : Function.Injective i := by
    intro σ σ' h
    apply IntermediateField.adjoin_algHom_ext F
    intro y hy
    have hyeq : y = j := Set.mem_singleton_iff.mp hy
    subst y
    change σ (AdjoinSimple.gen F j) = σ' (AdjoinSimple.gen F j)
    rw [hi, hi, h]
  calc
    finrank F F⟮j⟯ = Nat.card (F⟮j⟯ →ₐ[F] ℂ) := by
      rw [Nat.card_eq_fintype_card, AlgHom.card]
    _ ≤ Nat.card ι := Nat.card_le_card_of_injective i hinj

private def picRepresentative (O : NumberFieldOrder K) (c : Pic O) :
    O.invertibleProperFractionalIdeals :=
  (O.mkPic_surjective c).choose

private theorem mkPic_picRepresentative (O : NumberFieldOrder K) (c : Pic O) :
    O.mkPic (picRepresentative O c) = c :=
  (O.mkPic_surjective c).choose_spec

/-- The degree of a singular modulus over ℚ is at most the proper class number,
assuming exact-order conjugacy. -/
theorem singularModulus_finrank_le_of_conjugate (hconj : ConjugateSingularModulus)
    (O : NumberFieldOrder K) (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ) (I : O.invertibleProperFractionalIdeals) :
    finrank ℚ ℚ⟮singularModulus O hk hc κ I⟯ ≤ Nat.card (Pic O) := by
  apply finrank_adjoin_le_of_conjugate_family _
    ((singularModulus_isIntegral O hk hc κ I).tower_top (A := ℚ))
    (fun c => singularModulus O hk hc κ (picRepresentative O c))
  intro σ
  obtain ⟨J, hJ⟩ := hconj K O hk hc κ I σ
  refine ⟨O.mkPic J, hJ.trans (singularModulus_eq_of_mkPic_eq _ hk hc κ ?_)⟩
  exact (mkPic_picRepresentative O _).symm

/-- The same bound over the quadratic field through the chosen embedding.
Restriction to the simple rational field preserves the image of the generator. -/
theorem singularModulus_finrank_over_base_le_of_conjugate (hconj : ConjugateSingularModulus)
    (O : NumberFieldOrder K) (hk : finrank ℚ K = 2) (hc : IsTotallyComplex K)
    (κ : K →+* ℂ) (I : O.invertibleProperFractionalIdeals) :
    letI : Algebra K ℂ := κ.toAlgebra
    finrank K K⟮singularModulus O hk hc κ I⟯ ≤ Nat.card (Pic O) := by
  let : Algebra K ℂ := κ.toAlgebra
  let : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq fun q => (κ.toRatAlgHom.commutes q).symm
  let j := singularModulus O hk hc κ I
  have hI : IsIntegral ℚ j := (singularModulus_isIntegral O hk hc κ I).tower_top
  apply finrank_adjoin_le_of_conjugate_family j (hI.tower_top (A := K))
    (fun c => singularModulus O hk hc κ (picRepresentative O c))
  intro σ
  have hle : ℚ⟮j⟯ ≤ (K⟮j⟯).restrictScalars ℚ :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.subset_adjoin K {j} (Set.mem_singleton j)))
  let ρ : ℚ⟮j⟯ →ₐ[ℚ] ℂ := (σ.restrictScalars ℚ).comp (IntermediateField.inclusion hle)
  obtain ⟨J, hJ⟩ := hconj K O hk hc κ I ρ
  refine ⟨O.mkPic J, hJ.trans (singularModulus_eq_of_mkPic_eq _ hk hc κ ?_)⟩
  exact (mkPic_picRepresentative O _).symm


end ZInQ.Manuscript.RC.CMField2
