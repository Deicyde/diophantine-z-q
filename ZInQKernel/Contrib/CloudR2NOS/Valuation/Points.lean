/-
Copyright (c) 2026 H5 Round-2 Lane2 contributors.
Released under Apache 2.0 license as described in the source LICENSE.

New transport proofs for the EXACT PkgI2 objects from HDecomp/Objects.lean.
No replacement point group, action, inertia predicate, algebraic closure or
abelian variety is defined. Every natural torsion order is preserved.
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudR2NOS.Valuation.Imperfect

set_option autoImplicit false
noncomputable section

namespace ZInQ.Contrib.CloudR2NOS.Valuation

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

universe u
variable {K : Type u} [Field K]

section PointAction

variable {L : Type u} [CommRing L] [Algebra K L]

/-- The actual `Spec`-induced PkgI2 endomorphism at the identity. -/
@[simp] theorem galHom_one :
    PkgI2.galHom L (1 : L ≃ₐ[K] L) = 𝟙 (PkgI2.specOver K L) := by
  ext1
  change Spec.map (CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L)) =
    𝟙 (Spec (CommRingCat.of L))
  have h : CommRingCat.ofHom ((1 : L ≃ₐ[K] L) : L →+* L) = 𝟙 (CommRingCat.of L) := rfl
  rw [h]
  simp only [Spec.map_id]

/-- Product order checked with Spec contravariance and the actual AlgEquiv multiplication. -/
theorem galHom_mul (σ τ : L ≃ₐ[K] L) :
    PkgI2.galHom L (σ * τ) = PkgI2.galHom L σ ≫ PkgI2.galHom L τ := by
  ext1
  change Spec.map (CommRingCat.ofHom ((σ * τ : L ≃ₐ[K] L) : L →+* L)) =
    Spec.map (CommRingCat.ofHom (σ : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

variable (A : Grp (Over (Spec (.of K))))

@[simp] theorem galAct_one (x : PkgI2.Pts A L) : PkgI2.galAct A 1 x = x := by
  simp [PkgI2.galAct]

/-- The composition law is for the original `galAct`, not an opposite or replacement action. -/
theorem galAct_mul (σ τ : L ≃ₐ[K] L) (x : PkgI2.Pts A L) :
    PkgI2.galAct A σ (PkgI2.galAct A τ x) = PkgI2.galAct A (σ * τ) x := by
  simp only [PkgI2.galAct, galHom_mul, Category.assoc]

@[simp] theorem galAct_one_point (σ : L ≃ₐ[K] L) :
    PkgI2.galAct A σ (1 : PkgI2.Pts A L) = 1 :=
  MonObj.comp_one (PkgI2.galHom L σ)

theorem galAct_mul_points (σ : L ≃ₐ[K] L) (x y : PkgI2.Pts A L) :
    PkgI2.galAct A σ (x * y) = PkgI2.galAct A σ x * PkgI2.galAct A σ y :=
  MonObj.comp_mul (PkgI2.galHom L σ) x y

theorem galAct_pow (σ : L ≃ₐ[K] L) (x : PkgI2.Pts A L) (m : ℕ) :
    PkgI2.galAct A σ (x ^ m) = PkgI2.galAct A σ x ^ m :=
  MonObj.comp_pow x m (PkgI2.galHom L σ)

/-- Precomposition by the actual Galois endomorphism is a group automorphism of the same points. -/
def galActMulEquiv (σ : L ≃ₐ[K] L) : PkgI2.Pts A L ≃* PkgI2.Pts A L where
  toFun := PkgI2.galAct A σ
  invFun := PkgI2.galAct A σ⁻¹
  left_inv x := by rw [galAct_mul, inv_mul_cancel, galAct_one]
  right_inv x := by rw [galAct_mul, mul_inv_cancel, galAct_one]
  map_mul' := galAct_mul_points A σ

theorem galAct_injective (σ : L ≃ₐ[K] L) : Function.Injective (PkgI2.galAct A σ) :=
  (galActMulEquiv A σ).injective

/-- Every integer order is preserved, including zero; no invertibility guard is needed for transport. -/
theorem torsion_galAct (σ : L ≃ₐ[K] L) {m : ℕ} {x : PkgI2.Pts A L}
    (hx : x ∈ PkgI2.torsion A L m) : PkgI2.galAct A σ x ∈ PkgI2.torsion A L m := by
  change x ^ m = 1 at hx
  change PkgI2.galAct A σ x ^ m = 1
  rw [← galAct_pow, hx, galAct_one_point]

end PointAction

section InertiaTransport

variable {L : Type u} [Field L] [Algebra K L]

/-- Exact bridge from PkgI2's existential nested inertia predicate to the same image subgroup. -/
theorem isInertia_iff_mem_inertiaSubgroupIn (V : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    PkgI2.IsInertia V σ ↔ σ ∈ inertiaSubgroupIn (K := K) V := by
  constructor
  · rintro ⟨h, hσ⟩
    exact Subgroup.mem_map.mpr ⟨⟨σ, h⟩, hσ, rfl⟩
  · intro h
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp h
    exact ⟨d.2, hd⟩

/-- Conjugation of the original PkgI2 inertia predicate, not a replacement subgroup. -/
theorem isInertia_conj_of_isInertia_smul (V : ValuationSubring L) (g : L ≃ₐ[K] L)
    {σ : L ≃ₐ[K] L} (hσ : PkgI2.IsInertia (g • V) σ) :
    PkgI2.IsInertia V (g⁻¹ * σ * g) := by
  exact (isInertia_iff_mem_inertiaSubgroupIn V _).mpr
    (conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul V g
      ((isInertia_iff_mem_inertiaSubgroupIn (g • V) σ).mp hσ))

/-- Use the Type* source implication twice; no universe-zero inertia iff is imported. -/
theorem isInertia_smul_iff (V : ValuationSubring L) (g : L ≃ₐ[K] L) (σ : L ≃ₐ[K] L) :
    PkgI2.IsInertia (g • V) σ ↔ PkgI2.IsInertia V (g⁻¹ * σ * g) := by
  constructor
  · exact isInertia_conj_of_isInertia_smul V g
  · intro h
    have h' : PkgI2.IsInertia (g⁻¹ • (g • V)) (g⁻¹ * σ * g) := by
      simpa only [inv_smul_smul] using h
    have h'' := isInertia_conj_of_isInertia_smul (g • V) g⁻¹ h'
    have he : (g⁻¹)⁻¹ * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
    rw [he] at h''
    exact h''

variable (A : Grp (Over (Spec (.of K))))

/-- Inertia-triviality is invariant under conjugating the prolongation, on the same points. -/
theorem inertiaTrivialOn_smul (V : ValuationSubring L) (g : L ≃ₐ[K] L) (m : ℕ)
    (hV : PkgI2.InertiaTrivialOn A V m) : PkgI2.InertiaTrivialOn A (g • V) m := by
  intro σ hσ x hx
  have hσ' := (isInertia_iff_mem_inertiaSubgroupIn (g • V) σ).mp hσ
  have hconj := conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul V g hσ'
  have hfix := hV (g⁻¹ * σ * g)
    ((isInertia_iff_mem_inertiaSubgroupIn V _).mpr hconj)
    (PkgI2.galAct A g⁻¹ x) (torsion_galAct A g⁻¹ hx)
  apply galAct_injective A g⁻¹
  calc
    PkgI2.galAct A g⁻¹ (PkgI2.galAct A σ x) =
        PkgI2.galAct A (g⁻¹ * σ * g) (PkgI2.galAct A g⁻¹ x) := by
      rw [galAct_mul, galAct_mul]
      congr 1
      group
    _ = PkgI2.galAct A g⁻¹ x := hfix

theorem inertiaTrivialOn_smul_iff (V : ValuationSubring L) (g : L ≃ₐ[K] L) (m : ℕ) :
    PkgI2.InertiaTrivialOn A (g • V) m ↔ PkgI2.InertiaTrivialOn A V m := by
  constructor
  · intro h
    simpa only [inv_smul_smul] using inertiaTrivialOn_smul A (g • V) g⁻¹ m h
  · exact inertiaTrivialOn_smul A V g m

/-- Top inertia is the identity, hence trivial on all original torsion orders. -/
theorem inertiaTrivialOn_top (m : ℕ) :
    PkgI2.InertiaTrivialOn A (⊤ : ValuationSubring L) m := by
  intro σ hσ x _
  have hσ' := (isInertia_iff_mem_inertiaSubgroupIn (⊤ : ValuationSubring L) σ).mp hσ
  rw [eq_one_of_mem_inertiaSubgroupIn_top hσ', galAct_one]

end InertiaTransport

/-- The complete saved fixed-w to all-valuations bridge for the EXACT target vocabulary.
There is no abelian-variety, henselian, perfect-field or torsion-order assumption. -/
theorem inertiaTrivialOn_all_prolongations
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O)
    (A : Grp (Over (Spec (.of K)))) (m : ℕ) (hm : PkgI2.InertiaTrivialOn A w m) :
    ∀ V : ValuationSubring (AlgebraicClosure K),
      (∀ r : O, algebraMap O (AlgebraicClosure K) r ∈ V) → PkgI2.InertiaTrivialOn A V m := by
  intro V hV
  rcases comap_eq_or_top O V hV with hVO | rfl
  · obtain ⟨g, hg⟩ := exists_smul_eq_on_algebraicClosure O V w hVO hw
    have hfixed : PkgI2.InertiaTrivialOn A (g • V) m := by rw [hg]; exact hm
    exact (inertiaTrivialOn_smul_iff A V g m).mp hfixed
  · exact inertiaTrivialOn_top A m

end ZInQ.Contrib.CloudR2NOS.Valuation
