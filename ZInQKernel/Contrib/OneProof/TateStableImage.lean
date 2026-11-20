import ZInQKernel.Contrib.OneProof.TateSubgroupQuotient
import ZInQKernel.Contrib.OneProof.TateQuotientImage

/-! # Galois-stable Tate lattices yield algebraic endomorphism images -/

noncomputable section

open CategoryTheory AlgebraicGeometry PkgI3.AbVar
open scoped CategoryTheory.MonObj TensorProduct

namespace ZInQ.Contrib.TateFiniteApproximation

variable {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The image of a stable Tate submodule at a finite torsion level is the
geometric kernel of an isogeny defined over the same number field. -/
theorem hasFiniteQuotient_of_stable (W : Submodule ℤ_[ℓ] (A.T ℓ))
    (hW : ∀ (σ : Field.absoluteGaloisGroup K) (w : A.T ℓ), w ∈ W → A.galT σ w ∈ W)
    (n : ℕ) : HasFiniteQuotient A W n := by
  let S : Subgroup (GeomPt A.X) := {
    carrier := {P | ∃ w ∈ W, P = Additive.toMul (w.1 n)}
    one_mem' := ⟨0, W.zero_mem, rfl⟩
    mul_mem' := by
      rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact ⟨x + y, W.add_mem hx hy, rfl⟩
    inv_mem' := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨-x, W.neg_mem hx, rfl⟩ }
  let N := ℓ^n
  have hN : 0 < N := pow_pos (Fact.out : ℓ.Prime).pos n
  let m := ((N : ℤ) : End A).hom
  have : IsFinite m.left :=
    (AbVarBC.mulIsogeny K A (N : ℤ) (Nat.cast_ne_zero.mpr hN.ne')).1
  have := GapHeight.finite_kerSchPts m (algebraMap K (AlgebraicClosure K))
  have : Finite {P : GeomPt A.X // P ≫ m = 1} :=
    Finite.of_equiv _ (GapHeight.kerSchEquiv m (algebraMap K (AlgebraicClosure K))).symm
  have hf : (S : Set (GeomPt A.X)).Finite := by
    have hset : ({P : GeomPt A.X | P ≫ m = 1} : Set (GeomPt A.X)).Finite :=
      show Finite {P : GeomPt A.X // P ≫ m = 1} from inferInstance
    apply hset.subset
    rintro _ ⟨w, hw, rfl⟩
    change Additive.toMul (w.1 n) ≫ m = 1
    rw [show Additive.toMul (w.1 n) ≫ m = Additive.toMul (w.1 n) ^ N from
      AvSplit.comp_natCast_hom' A _ N]
    exact congrArg Additive.toMul (PkgI3.Tate.pow_smul_eq_zero w.2 n)
  have hs (σ : Field.absoluteGaloisGroup K) : ∀ P ∈ S, galHom σ ≫ P ∈ S := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨A.galT σ w, hW σ w hw, rfl⟩
  obtain ⟨H, hH⟩ := exists_finiteSubgroupScheme A S hf hs
  obtain ⟨B, q, hq, hker⟩ := SubgroupQuotient.exists_isogeny_with_kernel A H
  exact ⟨B, q, hq, fun P => (hker _ P).trans (hH P).symm⟩

/-- A uniform multiple of every Galois-stable Tate submodule is inside the
image of an algebraic ℤℓ-endomorphism whose entire image lies in that submodule. -/
theorem exists_uniform_endomorphism_for_stable_submodules
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (g : ℕ) (height : ℝ) (hdim : A.dim = (g : WithBot ℕ∞))
    (hheight : ZInQ.SemistabAssembly.IsAnStableHeightSS A height) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime] (W : Submodule ℤ_[ℓ] (A.T ℓ)),
      (∀ (σ : Field.absoluteGaloisGroup K) (w : A.T ℓ), w ∈ W → A.galT σ w ∈ W) →
      ∃ ξ : ℤ_[ℓ] ⊗[ℤ] End A, let u := tateHomZl ℓ A A ξ;
        LinearMap.range u ≤ W ∧ ∀ w ∈ W, N • w ∈ LinearMap.range u := by
  obtain ⟨N, hN, h⟩ := exists_uniform_endomorphism_from_quotients A hGR g height hdim hheight
  exact ⟨N, hN, fun ℓ _ W hW => h ℓ W (hasFiniteQuotient_of_stable A W hW)⟩

end ZInQ.Contrib.TateFiniteApproximation
