import ZInQKernel.Hypotheses.Height

open AlgebraicGeometry CategoryTheory

namespace ZInQ.HDecAlt

structure AbelianVariety (K : Type) [Field K] where
  G : Over (Spec (CommRingCat.of K))
  [grp : GrpObj G]
  [proper : IsProper G.hom]
  [geomInt : GeometricallyIntegral G.hom]
  [smooth : Smooth G.hom]

structure GalRep (K : Type) [Field K] (E : Type) [Field E] [TopologicalSpace E] where
  n : ℕ
  ρ : Field.absoluteGaloisGroup K →* GL (Fin n) E
  cont : Continuous fun g => (ρ g : Matrix (Fin n) (Fin n) E)

noncomputable instance (K E : Type) [Field K] [Field E] [TopologicalSpace E] : Inhabited (GalRep K E) :=
  ⟨⟨0, 1, by simpa using continuous_const⟩⟩

/-- `g ↦ ρ(g)` as linear endomorphisms of `Eⁿ`. -/
noncomputable def GalRep.act {K E : Type} [Field K] [Field E] [TopologicalSpace E]
    (ρ : GalRep K E) (g : Field.absoluteGaloisGroup K) : (Fin ρ.n → E) →ₗ[E] (Fin ρ.n → E) :=
  Matrix.toLin' (ρ.ρ g : Matrix (Fin ρ.n) (Fin ρ.n) E)

/-- The `G_K`-equivariant linear maps `ρ → σ`. -/
noncomputable def GalRep.intertwiners {K E : Type} [Field K] [Field E] [TopologicalSpace E]
    (ρ σ : GalRep K E) : Submodule E ((Fin ρ.n → E) →ₗ[E] (Fin σ.n → E)) where
  carrier := {f | ∀ g, f ∘ₗ ρ.act g = σ.act g ∘ₗ f}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro a b ha hb g
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.add_comp, LinearMap.comp_add, ha g, hb g]
  smul_mem' := by
    intro c a ha g
    simp only [Set.mem_setOf_eq] at *
    rw [LinearMap.smul_comp, LinearMap.comp_smul, ha g]

noncomputable def GalRep.homDim {K E : Type} [Field K] [Field E] [TopologicalSpace E]
    (ρ σ : GalRep K E) : ℕ := Module.finrank E (ρ.intertwiners σ)

def GalRep.IsSemisimple {K E : Type} [Field K] [Field E] [TopologicalSpace E]
    (ρ : GalRep K E) : Prop :=
  ∀ W : Submodule E (Fin ρ.n → E),
    (∀ g, ∀ v ∈ W, ρ.act g v ∈ W) →
    ∃ W' : Submodule E (Fin ρ.n → E), IsCompl W W' ∧
      ∀ g, ∀ v ∈ W', ρ.act g v ∈ W'

/-- Hasse principle for quaternion algebras over ℚ. -/
def Leaf_HasseQuaternion : Prop :=
  ∀ a b : ℚ, a ≠ 0 → b ≠ 0 →
    (Nonempty (QuaternionAlgebra ℚ a 0 b ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℚ) ↔
      (∀ p : ℕ, ∀ _ : Fact p.Prime,
        Nonempty (QuaternionAlgebra ℚ_[p] (a : ℚ_[p]) 0 (b : ℚ_[p]) ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])) ∧
      Nonempty (QuaternionAlgebra ℝ (a : ℝ) 0 (b : ℝ) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ))

def Leaf_KroneckerWeber : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K],
    (∀ σ τ : K ≃ₐ[ℚ] K, σ * τ = τ * σ) →
      ∃ n : ℕ+, Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)

noncomputable def absLogHeightVec {K : Type} [Field K] [NumberField K] {ι : Type}
    (x : ι → K) : ℝ := Height.logHeight x / (Module.finrank ℚ K : ℝ)

end ZInQ.HDecAlt
