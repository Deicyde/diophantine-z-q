import ZInQKernel.Contrib.CloudR2CM.SerreTate.Assembly
import ZInQKernel.HDecomp.A6.Extend

/-!
# The assembly: proof of `CMPotentialGoodAssembly`

`CMPotentialGoodAssembly` states that the route statements P0–P4 and the Dedekind Néron-model
existence input give `HDec.CMBranch.CMPotentialGood`. All of them are hypotheses of the statement,
so this proof uses no open input of its own. For `E/L` of dimension `1` with `IsCMBy E k R`:

* P0 gives a finite `L'/L` over which every geometric endomorphism is defined;
* P2 (the choice of `L₁`, with `2²` and `3`) gives a finite `L₁ ⊇ L'` over which `E[4]` and `E[3]`
  are rational, and P0 at `M = L₁` gives `End(E_{L₁}) ≅ R`;
* at a finite place `O` of `L₁`, one of `2`, `3` is a unit in `O` (`3 + (-2) = 1` in a local
  ring); for that prime, P1 gives a finite inertia image on `T_ℓ`, the rational torsion is fixed by
  inertia, P2 gives inertia trivial on `T_ℓ`, and P3 gives good reduction at `O`;
* P4, with the Dedekind Néron-model existence input, gives the proper global group model.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace HDec.CMSerreTate

/-- In a local ring, `2` or `3` is a unit: `3 + (-2) = 1`. -/
theorem two_or_three_isUnit (R : Type) [CommRing R] [IsLocalRing R] :
    IsUnit ((2 : ℕ) : R) ∨ IsUnit ((3 : ℕ) : R) := by
  have h : IsUnit (((3 : ℕ) : R) + -((2 : ℕ) : R)) := by
    have e : ((3 : ℕ) : R) + -((2 : ℕ) : R) = 1 := by
      push_cast
      ring
    rw [e]
    exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h3 | h2
  · exact Or.inr h3
  · exact Or.inl ((IsUnit.neg_iff _).mp h2)

/-- A point of `A(K̄)` coming from a `K`-point is fixed by every automorphism of `K̄` over `K`. -/
theorem galAct_extPt_ofId {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (y : A.Pt K) :
    A.galAct σ (_root_.ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y) =
      _root_.ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y := by
  have h := _root_.ZInQ.Contrib.AbVarBC.extPt_galAct A (Algebra.ofId K (AlgebraicClosure K))
    (1 : K ≃ₐ[K] K) σ (by intro x; simp) y
  rw [← h]
  congr 1
  show _root_.PkgI3.AbVar.galHom (1 : K ≃ₐ[K] K) ≫ y = y
  rw [_root_.PkgI3.AbVar.galHom_one, CategoryTheory.Category.id_comp]

/-- **The assembly.** P0, P1, P2, P3, P4 and the Dedekind Néron-model existence input give
`HDec.CMBranch.CMPotentialGood`. -/
theorem cmPotentialGoodAssembly_proof : CMPotentialGoodAssembly := by
  intro hP0 hP1 hP2 hP3 hP4 hN L _ _ E hE k _ _ R hR hCM
  obtain ⟨hRig, hTor⟩ := hP2
  obtain ⟨L', _, _, _, _, _, hdef⟩ := hP0 L E hE k R hR hCM
  obtain ⟨L₁, _, _, _, _, ⟨j⟩, hrat⟩ :=
    hTor L (HDec.LeafAdopt.abVarEquiv L E) L' 2 3 2 1 Nat.prime_two Nat.prime_three
  have hCM₁ : BaseDefinedCM ((HDec.LeafAdopt.abVarEquiv L E).baseChange L₁) R :=
    (hdef L₁ ⟨j⟩).2
  have hdim₁ : ((HDec.LeafAdopt.abVarEquiv L E).baseChange L₁).dim = 1 := by
    rw [_root_.PkgI3.AbVar.dim_baseChange, HDec.LeafAdopt.abVarEquiv_dim]
    exact hE
  have hgood : GoodAtFinitePlaces ((HDec.LeafAdopt.abVarEquiv L E).baseChange L₁) := by
    intro O _ _
    obtain ⟨w, hw⟩ :=
      _root_.GlueA6Alg.exists_valuationSubring_comap_eq (L := AlgebraicClosure L₁) O
    have hfix : ∀ m : ℕ, (m = 2 ^ 2 ∨ m = 3 ^ 1) →
        ∀ σ : AlgebraicClosure L₁ ≃ₐ[L₁] AlgebraicClosure L₁, _root_.PkgI2.IsInertia w σ →
          ∀ x : ((HDec.LeafAdopt.abVarEquiv L E).baseChange L₁).Pt (AlgebraicClosure L₁),
            x ^ m = 1 → ((HDec.LeafAdopt.abVarEquiv L E).baseChange L₁).galAct σ x = x := by
      intro m hm σ _ x hx
      obtain ⟨y, rfl⟩ := hrat m hm x hx
      exact galAct_extPt_ofId _ σ y
    rcases two_or_three_isUnit O with h2 | h3
    · exact hP3 L₁ O w hw _ 2 h2
        (hRig L₁ _ (AlgebraicClosure L₁) w 2 2 (by norm_num)
          (hP1 L₁ _ hdim₁ k R hR hCM₁ O w hw 2 h2) (hfix (2 ^ 2) (Or.inl rfl)))
    · exact hP3 L₁ O w hw _ 3 h3
        (hRig L₁ _ (AlgebraicClosure L₁) w 3 1 (by norm_num)
          (hP1 L₁ _ hdim₁ k R hR hCM₁ O w hw 3 h3) (hfix (3 ^ 1) (Or.inr rfl)))
  obtain ⟨𝒢, h𝒢⟩ := hP4 hN L E L₁ hgood
  exact ⟨L₁, inferInstance, inferInstance, inferInstance, 𝒢, h𝒢⟩

end HDec.CMSerreTate
