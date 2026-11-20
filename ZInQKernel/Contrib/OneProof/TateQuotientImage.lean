import ZInQKernel.Contrib.OneProof.TateEndomorphismLimit

/-!
# Algebraic endomorphisms cutting out Tate subspaces

At each finite level, quotient by the images of W on geometric torsion.
The reverse isogeny then realizes their preimage on the Tate lattice.
Gaudron–Rémond bounds the denominator when replacing the quotient variety
by the original variety, uniformly over all levels.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry PkgI3.AbVar
open scoped CategoryTheory.MonObj TensorProduct

namespace ZInQ.Contrib.TateFiniteApproximation

variable {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)

/-- The geometric kernel of the quotient is exactly the image of W in the
ℓ^n-torsion points. -/
def HasFiniteQuotient {ℓ : ℕ} [Fact ℓ.Prime] (W : Submodule ℤ_[ℓ] (A.T ℓ)) (n : ℕ) : Prop :=
  ∃ (B : PkgI3.AbVar K) (q : Hom A B), ZInQ.DefFaltings.IsIsogeny q.hom ∧
    ∀ P : ZInQ.DefFaltings.ptObj K (AlgebraicClosure K) ⟶ A.X,
      P ≫ q.hom = 1 ↔ ∃ w ∈ W, P = Additive.toMul (w.1 n)

/-- The same scalar N works for every prime and every submodule for which
the finite torsion quotients exist over the ground field. -/
theorem exists_uniform_endomorphism_from_quotients
    (hGR : ZInQ.SemistabAssembly.GaudronRemondThm14AnSS)
    (g : ℕ) (height : ℝ) (hdim : A.dim = (g : WithBot ℕ∞))
    (hheight : ZInQ.SemistabAssembly.IsAnStableHeightSS A height) :
    ∃ N : ℕ, 0 < N ∧ ∀ (ℓ : ℕ) [Fact ℓ.Prime] (W : Submodule ℤ_[ℓ] (A.T ℓ)),
      (∀ n : ℕ, HasFiniteQuotient A W n) →
      ∃ ξ : ℤ_[ℓ] ⊗[ℤ] End A, let u := tateHomZl ℓ A A ξ; LinearMap.range u ≤ W ∧ ∀ w ∈ W, N • w ∈ LinearMap.range u := by
  obtain ⟨N, hN, hbound⟩ := GRUniformQuasiInverse.exists_uniform_tate_quasiInverse_of_gaudronRemond
    hGR K A g height hdim hheight
  refine ⟨N, hN, fun ℓ hℓ W hquot => ?_⟩
  have hT := DeRhamPrint.tateModuleFree_of_mumford CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
    K A ℓ (Nat.cast_ne_zero.mpr hℓ.out.ne_zero)
  let := hT.1
  let := hT.2.1
  let E := comparisonImage ℓ A A
  have step (n : ℕ) : ∃ u ∈ E,
      (∀ x : A.T ℓ, ∃ w ∈ W, ∃ z : A.T ℓ, u x - w = (ℓ : ℤ_[ℓ])^n • z) ∧
      ∀ w ∈ W, N • w ∈ LinearMap.range u := by
    obtain ⟨B, q, hq, hk⟩ := hquot n
    have hkill (P : ZInQ.DefFaltings.ptObj K (AlgebraicClosure K) ⟶ A.X) (hP : P ≫ q.hom = 1) :
        P^(ℓ^n) = 1 := by
      obtain ⟨w, _, rfl⟩ := (hk P).mp hP
      exact congrArg Additive.toMul (PkgI3.Tate.pow_smul_eq_zero w.2 n)
    obtain ⟨s, hs⟩ := GRUniformQuasiInverse.exists_homT_range_of_geometric_kernel q hq ℓ n hkill
    obtain ⟨f, _, r, hfr⟩ := hbound B ⟨q.hom, hq⟩
    let v : End A := Hom.mk' (f.hom ≫ s.hom)
    have hv : homT (ℓ := ℓ) v = (homT (ℓ := ℓ) s).comp (homT f) := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      funext j
      change Additive.ofMul (Additive.toMul (x.1 j) ≫ f.hom ≫ s.hom) =
             Additive.ofMul ((Additive.toMul (x.1 j) ≫ f.hom) ≫ s.hom)
      rw [Category.assoc]
    have hmem : homT (ℓ := ℓ) v ∈ E := by
      refine ⟨(1 : ℤ_[ℓ]) ⊗ₜ[ℤ] v, ?_⟩
      change (1 : ℤ_[ℓ]) • homT (ℓ := ℓ) v = homT (ℓ := ℓ) v
      exact one_smul _ _
    refine ⟨homT v, hmem, ?_, ?_⟩
    · intro x
      have hz : homT (ℓ := ℓ) v x ∈ LinearMap.range (homT s) := ⟨homT f x, by rw [hv]; rfl⟩
      obtain ⟨w, hw, he⟩ := (hk _).mp ((hs _).mp hz)
      refine ⟨w, hw, (PkgI3.Tate.coord_eq_zero_iff _ n).mp ?_⟩
      change ((homT (ℓ := ℓ) v x).1 n) - w.1 n = 0
      exact sub_eq_zero.mpr (congrArg Additive.ofMul he)
    · intro w hw
      obtain ⟨b, hb⟩ := (hs w).mpr ((hk _).mpr ⟨w, hw, rfl⟩)
      refine ⟨homT r b, ?_⟩
      rw [hv, LinearMap.comp_apply]
      have h := LinearMap.congr_fun (hfr ℓ).2 b
      change (homT (ℓ := ℓ) f) (homT r b) = N • b at h
      rw [h, map_nsmul, hb]
  obtain ⟨u, ⟨ξ, hξ⟩, hu⟩ := exists_endomorphism_between E W N step
  exact ⟨ξ, hξ ▸ hu⟩

end ZInQ.Contrib.TateFiniteApproximation
