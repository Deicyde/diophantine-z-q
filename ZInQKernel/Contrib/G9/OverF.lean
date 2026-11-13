import ZInQKernel.Contrib.G9.Descent

/-!
# G9: counting equivariant maps through `V ⊗ C ≅ U ⊕ U`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Pure linear algebra on the spaces `Dsp act ρ S` of `Descent.lean`:
* `finrank_Dsp_congr`: an equivariant isomorphism `V ≅ V'` preserves `dim Dsp`;
* `finrank_Dsp_pi`: `dim Dsp(V^ι) = |ι| · dim Dsp(V)`;
* `finrank_Dsp_prod`: `dim Dsp(U × U) = 2 · dim Dsp(U)`;
* `overF_count`: if `C ⊗_K V ≅ U × U` equivariantly (`C/K` finite) and `Dsp(V) ≠ 0`, then
  `[C:K] · dim Dsp(V) = 2 · dim Dsp(U)`.
This is the step "extension of the coefficient field is, on underlying `ℚ_ℓ`-representations, a
finite direct sum; the displayed decomposition therefore makes `r|G_F` de Rham" of N5's Lemma
`lem:de-rham-descent`, done by counting (no closure property of de Rham representations is used).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open Module
open scoped TensorProduct

noncomputable section

section OverF

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [AddCommGroup B] [Module K B]
  (act : G → B →ₗ[K] B)

theorem finrank_Dsp_congr {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (ρ : G → V →ₗ[K] V) (ρ' : G → V' →ₗ[K] V') (S : Set G) (e : V ≃ₗ[K] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank K (Dsp act ρ S) = finrank K (Dsp act ρ' S) := by
  let L : (V →ₗ[K] B) ≃ₗ[K] (V' →ₗ[K] B) := LinearEquiv.arrowCongr e (LinearEquiv.refl K B)
  have hL : ∀ φ v', L φ v' = φ (e.symm v') := fun _ _ => rfl
  have hL' : ∀ φ' v, L.symm φ' v = φ' (e v) := fun _ _ => rfl
  have hmap : (Dsp act ρ S).map (L : (V →ₗ[K] B) →ₗ[K] (V' →ₗ[K] B)) = Dsp act ρ' S := by
    ext φ'
    constructor
    · rintro ⟨φ, hφ, rfl⟩ g hg v'
      have h1 : e.symm (ρ' g v') = ρ g (e.symm v') := by
        apply e.injective
        rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
      change L φ (ρ' g v') = act g (L φ v')
      rw [hL, hL, h1, hφ g hg]
    · intro hφ'
      refine ⟨L.symm φ', ?_, by simp⟩
      intro g hg v
      rw [hL', hL', he, hφ' g hg]
  rw [← hmap, LinearEquiv.finrank_map_eq]

/-- The diagonal action on `ι → V`. -/
def piRep {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (ι : Type*) :
    G → (ι → V) →ₗ[K] (ι → V) :=
  fun g => LinearMap.pi fun i => ρ g ∘ₗ LinearMap.proj i

theorem piRep_apply {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (ι : Type*)
    (g : G) (v : ι → V) (i : ι) : piRep ρ ι g v i = ρ g (v i) := rfl

theorem piRep_single {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (ι : Type*) [DecidableEq ι] (g : G) (i : ι) (v : V) :
    piRep ρ ι g (Pi.single i v) = Pi.single i (ρ g v) := by
  funext j
  rw [piRep_apply]
  by_cases hij : j = i
  · subst hij; simp
  · simp [Pi.single_eq_of_ne hij]

/-- `Dsp(V^ι) ≅ Dsp(V)^ι`. -/
def DspPiEquiv {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Dsp act (piRep ρ ι) S ≃ₗ[K] (ι → Dsp act ρ S) :=
  { toFun := fun φ i => ⟨(φ : (ι → V) →ₗ[K] B) ∘ₗ LinearMap.single K (fun _ => V) i, by
      intro g hg v
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
      rw [← piRep_single, φ.2 g hg]⟩
    map_add' := fun φ ψ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    map_smul' := fun c φ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    invFun := fun ψ => ⟨∑ i, ((ψ i : Dsp act ρ S) : V →ₗ[K] B) ∘ₗ LinearMap.proj i, by
      intro g hg v
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [piRep_apply, (ψ i).2 g hg]⟩
    left_inv := fun φ => by
      apply Subtype.ext
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
        LinearMap.single_apply]
      rw [← map_sum, Finset.univ_sum_single v]
    right_inv := fun ψ => by
      funext i
      apply Subtype.ext
      refine LinearMap.ext fun v => ?_
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
        LinearMap.single_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [Pi.single_eq_of_ne hji, map_zero]
      · intro h; exact absurd (Finset.mem_univ i) h }

theorem finrank_Dsp_pi {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) (ι : Type*) [Fintype ι] [DecidableEq ι] [FiniteDimensional K (Dsp act ρ S)] :
    finrank K (Dsp act (piRep ρ ι) S) = Fintype.card ι * finrank K (Dsp act ρ S) := by
  rw [(DspPiEquiv act ρ S ι).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- `Dsp(U × U) ≅ Dsp(U) × Dsp(U)`. -/
def DspProdEquiv {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (S : Set G) :
    Dsp act (fun g => (ρ g).prodMap (ρ g)) S ≃ₗ[K] (Dsp act ρ S × Dsp act ρ S) :=
  { toFun := fun φ => (⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inl K V V, by
        intro g hg v
        have := φ.2 g hg (v, 0)
        simpa using this⟩,
      ⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inr K V V, by
        intro g hg v
        have := φ.2 g hg (0, v)
        simpa using this⟩)
    map_add' := fun φ ψ => by ext <;> simp
    map_smul' := fun c φ => by ext <;> simp
    invFun := fun ψ => ⟨(ψ.1 : V →ₗ[K] B).coprod (ψ.2 : V →ₗ[K] B), by
      intro g hg v
      simp only [LinearMap.coprod_apply, LinearMap.prodMap_apply, map_add]
      rw [ψ.1.2 g hg, ψ.2.2 g hg]⟩
    left_inv := fun φ => by
      apply Subtype.ext
      ext v <;> simp
    right_inv := fun ψ => by
      ext v <;> simp }

theorem finrank_Dsp_prod {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) [FiniteDimensional K (Dsp act (fun g => (ρ g).prodMap (ρ g)) S)] :
    finrank K (Dsp act (fun g => (ρ g).prodMap (ρ g)) S) = 2 * finrank K (Dsp act ρ S) := by
  let E := DspProdEquiv act ρ S
  have hfin : FiniteDimensional K (Dsp act ρ S × Dsp act ρ S) :=
    LinearEquiv.finiteDimensional E
  have : FiniteDimensional K (Dsp act ρ S) :=
    Module.Finite.of_surjective (LinearMap.fst K (Dsp act ρ S) (Dsp act ρ S))
      LinearMap.fst_surjective
  rw [E.finrank_eq, Module.finrank_prod, two_mul]

/-- `C ⊗_K V ≅ V^ι` for a basis of `C` indexed by `ι`. -/
def tensorPiEquiv {C : Type*} [Field C] [Algebra K C] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bC : Basis ι K C) : C ⊗[K] V ≃ₗ[K] (ι → V) :=
  (TensorProduct.equivFinsuppOfBasisLeft bC).trans (Finsupp.linearEquivFunOnFinite K V ι)

theorem tensorPiEquiv_baseChange {C : Type*} [Field C] [Algebra K C] {V : Type*}
    [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι] (bC : Basis ι K C)
    (f : V →ₗ[K] V)
    (x : C ⊗[K] V) :
    tensorPiEquiv bC (f.baseChange C x) = fun i => f (tensorPiEquiv bC x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul c v =>
    funext i
    simp [tensorPiEquiv, LinearMap.baseChange_tmul]
  | add x y hx hy =>
    funext i
    rw [map_add, map_add, Pi.add_apply, hx, hy, map_add, Pi.add_apply, map_add]

/-- **Counting through `C ⊗_K V ≅ U × U`.** -/
theorem overF_count {C : Type*} [Field C] [Algebra K C] [FiniteDimensional K C]
    {V U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module C U] [Module K U]
    [IsScalarTower K C U]
    (ρV : G → V →ₗ[K] V) (ρU : G → U →ₗ[K] U) (S : Set G)
    (e : C ⊗[K] V ≃ₗ[C] U × U)
    (he : ∀ g x, e ((ρV g).baseChange C x) = ((ρU g).prodMap (ρU g)) (e x))
    (hpos : 0 < finrank K (Dsp act ρV S)) :
    finrank K C * finrank K (Dsp act ρV S) = 2 * finrank K (Dsp act ρU S) := by
  classical
  have : FiniteDimensional K (Dsp act ρV S) := Module.finite_of_finrank_pos hpos
  let bC := Module.finBasis K C
  let ρCV : G → (C ⊗[K] V) →ₗ[K] (C ⊗[K] V) := fun g => ((ρV g).baseChange C).restrictScalars K
  have h1 : finrank K (Dsp act ρCV S) = finrank K C * finrank K (Dsp act ρV S) := by
    rw [finrank_Dsp_congr act ρCV (piRep ρV (Fin (finrank K C))) S (tensorPiEquiv bC)
      (fun g x => tensorPiEquiv_baseChange bC (ρV g) x), finrank_Dsp_pi, Fintype.card_fin]
  have h2 : finrank K (Dsp act ρCV S) =
      finrank K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) :=
    finrank_Dsp_congr act ρCV _ S (e.restrictScalars K) (fun g x => he g x)
  have hfin : FiniteDimensional K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) := by
    apply Module.finite_of_finrank_pos
    rw [← h2, h1]
    exact Nat.mul_pos Module.finrank_pos hpos
  rw [← h1, h2, finrank_Dsp_prod]

/-- **Reverse count**: if `Dsp(U) ≠ 0` (finite-dimensional), then `Dsp(V) ≠ 0`. -/
theorem overF_pos_rev {C : Type*} [Field C] [Algebra K C] [FiniteDimensional K C]
    {V U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module C U] [Module K U]
    [IsScalarTower K C U]
    (ρV : G → V →ₗ[K] V) (ρU : G → U →ₗ[K] U) (S : Set G)
    (e : C ⊗[K] V ≃ₗ[C] U × U)
    (he : ∀ g x, e ((ρV g).baseChange C x) = ((ρU g).prodMap (ρU g)) (e x))
    (hU : 0 < finrank K (Dsp act ρU S)) :
    0 < finrank K (Dsp act ρV S) := by
  classical
  have : FiniteDimensional K (Dsp act ρU S) := Module.finite_of_finrank_pos hU
  let bC := Module.finBasis K C
  let ρCV : G → (C ⊗[K] V) →ₗ[K] (C ⊗[K] V) := fun g => ((ρV g).baseChange C).restrictScalars K
  have hUU : FiniteDimensional K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) :=
    LinearEquiv.finiteDimensional (DspProdEquiv act ρU S).symm
  have h2 : finrank K (Dsp act ρCV S) =
      finrank K (Dsp act (fun g => (ρU g).prodMap (ρU g)) S) :=
    finrank_Dsp_congr act ρCV _ S (e.restrictScalars K) (fun g x => he g x)
  have h1 : finrank K (Dsp act ρCV S) =
      finrank K (Dsp act (piRep ρV (Fin (finrank K C))) S) :=
    finrank_Dsp_congr act ρCV (piRep ρV (Fin (finrank K C))) S (tensorPiEquiv bC)
      (fun g x => tensorPiEquiv_baseChange bC (ρV g) x)
  have hpos : 0 < finrank K (Dsp act (piRep ρV (Fin (finrank K C))) S) := by
    rw [← h1, h2, finrank_Dsp_prod]
    omega
  have : FiniteDimensional K (Dsp act (piRep ρV (Fin (finrank K C))) S) :=
    Module.finite_of_finrank_pos hpos
  have hfinpi : FiniteDimensional K (Fin (finrank K C) → Dsp act ρV S) :=
    LinearEquiv.finiteDimensional (DspPiEquiv act ρV S _)
  have hc : 0 < finrank K C := Module.finrank_pos
  have : FiniteDimensional K (Dsp act ρV S) :=
    Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun _ : Fin (finrank K C) =>
      Dsp act ρV S) ⟨0, hc⟩) (fun x => ⟨fun _ => x, rfl⟩)
  rw [finrank_Dsp_pi, Fintype.card_fin] at hpos
  exact Nat.pos_of_mul_pos_left hpos

end OverF

end

end ZInQ.Contrib.G9
