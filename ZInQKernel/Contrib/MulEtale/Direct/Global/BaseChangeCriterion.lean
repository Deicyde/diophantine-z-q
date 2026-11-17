/-
Multiplication-etale construction: BaseChangeCriterion.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.Global.PushoutCotangent
import ZInQKernel.Contrib.MulEtale.Direct.LocalCotangentCriterion
import ZInQKernel.Contrib.MulEtale.Direct.CotangentDerivationNaturality
import Mathlib.RingTheory.Kaehler.JacobiZariski

noncomputable section
open scoped TensorProduct

namespace H101DirectGlobalDetection

open H101DirectFieldRoute SourceReuse

/-- Formal etaleness of the actual base-changed ring map makes its native
Jacobi–Zariski cotangent map bijective. No assumed flatness is needed. -/
theorem mapBaseChange_bijective_of_formallyEtale
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.FormallyEtale S T] :
    Function.Bijective (KaehlerDifferential.mapBaseChange R S T) := by
  constructor
  · apply (injective_iff_map_eq_zero _).2
    intro x hx
    obtain ⟨y, hy⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
    rw [← hy, Subsingleton.elim y 0, map_zero]
  · intro x
    have hx : KaehlerDifferential.map R S T T x = 0 := Subsingleton.elim _ _
    exact (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp hx

/-- Tensoring a genuine linear equivalence preserves bijectivity over any
base algebra; it does not need that algebra to be flat. -/
private theorem baseChange_bijective_of_bijective
    {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (l : M →ₗ[A] N)
    (h : Function.Bijective l) (K : Type*) [CommRing K] [Algebra A K] :
    Function.Bijective (l.baseChange K) := by
  let e : M ≃ₗ[A] N := LinearEquiv.ofBijective l h
  have hmap : (e.baseChange A K M N).toLinearMap = l.baseChange K := by
    ext k m
    rfl
  rw [← hmap]
  exact (e.baseChange A K M N).bijective

/-- The residue cotangent map over a formally-etale ring map is bijective.
The field K is only the module-coefficient field, not a restriction on R. -/
theorem residueCotangentMap_bijective_of_formallyEtale
    (R S T K : Type*) [CommRing R] [CommRing S] [CommRing T] [Field K]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra T K] [Algebra S K] [Algebra R K]
    [IsScalarTower S T K] [IsScalarTower R T K] [IsScalarTower R S K]
    [Algebra.FormallyEtale S T] :
    Function.Bijective (residueCotangentMap R S T K) :=
  (baseChange_bijective_of_bijective (KaehlerDifferential.mapBaseChange R S T)
      (mapBaseChange_bijective_of_formallyEtale R S T) K).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S T K K Ω[S⁄R]).symm.bijective

section TwoPushouts

variable (R S T R' S' T' K : Type*)
  [CommRing R] [CommRing S] [CommRing T]
  [CommRing R'] [CommRing S'] [CommRing T'] [Field K]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [Algebra R R'] [Algebra R' S'] [Algebra S S'] [Algebra R S']
  [IsScalarTower R S S'] [IsScalarTower R R' S']
  [Algebra R' T'] [Algebra T T'] [Algebra R T']
  [IsScalarTower R T T'] [IsScalarTower R R' T']
  [Algebra S' T'] [Algebra S T']
  [IsScalarTower R' S' T'] [IsScalarTower S S' T'] [IsScalarTower S T T']
  [Algebra.IsPushout R R' S S'] [Algebra.IsPushout R R' T T']
  [Algebra T' K] [Algebra S' K] [Algebra R' K]
  [Algebra T K] [Algebra S K] [Algebra R K]
  [IsScalarTower S T K] [IsScalarTower R T K] [IsScalarTower R S K]
  [IsScalarTower S' T' K] [IsScalarTower R' T' K] [IsScalarTower R' S' K]
  [IsScalarTower T T' K] [IsScalarTower S S' K]

/-- The canonical cotangent base-change square COMMUTES. It is proved on
universal differentials using the actual scalar-tower identities, not
assumed as a hypothesis. The two vertical maps are genuine equivalences. -/
theorem residueCotangentMap_pushout_square :
    (kaehlerTensorEquivOfIsPushout R T R' T' K).toLinearMap ∘ₗ
        residueCotangentMap R S T K =
      residueCotangentMap R' S' T' K ∘ₗ
        (kaehlerTensorEquivOfIsPushout R S R' S' K).toLinearMap := by
  let F := (kaehlerTensorEquivOfIsPushout R T R' T' K).toLinearMap ∘ₗ
    residueCotangentMap R S T K
  let G := residueCotangentMap R' S' T' K ∘ₗ
    (kaehlerTensorEquivOfIsPushout R S R' S' K).toLinearMap
  have h : (F.restrictScalars S) ∘ₗ (TensorProduct.mk S K Ω[S⁄R] 1) =
      (G.restrictScalars S) ∘ₗ (TensorProduct.mk S K Ω[S⁄R] 1) := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro s
    change kaehlerTensorEquivOfIsPushout R T R' T' K
        (residueCotangentMap R S T K (1 ⊗ₜ[S] KaehlerDifferential.D R S s)) =
      residueCotangentMap R' S' T' K
        (kaehlerTensorEquivOfIsPushout R S R' S' K
          (1 ⊗ₜ[S] KaehlerDifferential.D R S s))
    rw [residueCotangentMap_one_tmul_D,
      kaehlerTensorEquivOfIsPushout_tmul_D,
      kaehlerTensorEquivOfIsPushout_tmul_D,
      residueCotangentMap_one_tmul_D]
    congr 2
    rw [← IsScalarTower.algebraMap_apply S T T',
      ← IsScalarTower.algebraMap_apply S S' T']
  change F = G
  apply (TensorProduct.isBaseChange S Ω[S⁄R] K).algHom_ext
  intro ω
  exact LinearMap.congr_fun h ω

include R' in
/-- Formal etaleness of the genuine base-changed map makes the actual
original residue cotangent map bijective via the proved square. -/
theorem residueCotangentMap_bijective_of_formallyEtale_pushout
    [Algebra.FormallyEtale S' T'] :
    Function.Bijective (residueCotangentMap R S T K) := by
  let E₁ := kaehlerTensorEquivOfIsPushout R S R' S' K
  let E₂ := kaehlerTensorEquivOfIsPushout R T R' T' K
  have H := residueCotangentMap_bijective_of_formallyEtale R' S' T' K
  have hs := residueCotangentMap_pushout_square R S T R' S' T' K
  constructor
  · intro x y hxy
    apply E₁.injective
    apply H.1
    calc
      residueCotangentMap R' S' T' K (E₁ x) =
          E₂ (residueCotangentMap R S T K x) := (LinearMap.congr_fun hs x).symm
      _ = E₂ (residueCotangentMap R S T K y) := congrArg E₂ hxy
      _ = residueCotangentMap R' S' T' K (E₁ y) := LinearMap.congr_fun hs y
  · intro y
    obtain ⟨z, hz⟩ := H.2 (E₂ y)
    refine ⟨E₁.symm z, E₂.injective ?_⟩
    calc
      E₂ (residueCotangentMap R S T K (E₁.symm z)) =
          residueCotangentMap R' S' T' K (E₁ (E₁.symm z)) :=
        LinearMap.congr_fun hs (E₁.symm z)
      _ = residueCotangentMap R' S' T' K z := by rw [E₁.apply_symm_apply]
      _ = E₂ y := hz

end TwoPushouts

/-- Generic local lifting endpoint. Its input is the ACTUAL residue
cotangent map, as an ordinary proof argument, and the later pushout theorem
DERIVES it. Structural smoothness is the only geometric source of finite
free differentials; flatness/etaleness of the investigated map is not input. -/
theorem formallyEtale_of_actual_residueCotangentMap_bijective
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [IsLocalRing T]
    [Algebra.EssFiniteType R S] [Algebra.EssFiniteType R T]
    [Algebra.FormallySmooth R S] [Algebra.FormallySmooth R T]
    (h : Function.Bijective (residueCotangentMap R S T (IsLocalRing.ResidueField T))) :
    Algebra.FormallyEtale S T := by
  let K := IsLocalRing.ResidueField T
  let l := KaehlerDifferential.mapBaseChange R S T
  let E := TensorProduct.AlgebraTensorModule.cancelBaseChange S T K K Ω[S⁄R]
  have hl : Function.Bijective (l.baseChange K) := by
    constructor
    · intro x y hxy
      apply E.injective
      apply h.1
      change l.baseChange K (E.symm (E x)) = l.baseChange K (E.symm (E y))
      simpa only [LinearEquiv.symm_apply_apply] using hxy
    · intro y
      obtain ⟨x, hx⟩ := h.2 y
      exact ⟨E.symm x, hx⟩
  apply H101DirectFieldRoute.formallyEtale_of_residue_cotangent_bijective R S T
  simpa only [LinearMap.baseChange_eq_lTensor] using hl

end H101DirectGlobalDetection
