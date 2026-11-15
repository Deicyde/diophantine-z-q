import ZInQKernel.Contrib.G9.Final

/-!
# G9: the local model, reduced to base change of abelian varieties

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

`G9Bridge.LocalModel` (bridge F2 of `Reduction.lean`) mixes Galois theory with algebraic
geometry. Here the Galois theory is proved, and what remains is one statement about abelian
varieties, `G9Bridge.AbVarBaseChange`: for a field embedding `i : K → L` (characteristic 0) and an
abelian variety `A/K`, there is an abelian variety `A'/L` (pkg-I4's copy of pkg-I3's `AbVar`;
`A' = A ×_K L`) with `dim A' = dim A` and `V_ℓ(A') ≅ V_ℓ(A)` intertwining `G_L` with `G_K` through
Mathlib's `Field.absoluteGaloisGroup.map i`. STANDARD (base change of abelian varieties;
`A[ℓⁿ]` is finite étale over `K` in characteristic `≠ ℓ`, so its points over `K̄` and over `L̄`
agree: Mumford, *Abelian varieties*, §4 and §6, locators UNVERIFIED; dimension is invariant under
field extension, EGA IV 4.1.4, UNVERIFIED).

* `localModel_of_abVarBaseChange : AbVarBaseChange → LocalModel`: `K` embeds into a finite
  Galois `F/ℚ_ℓ` inside `ℚ̄_ℓ` (the normal closure of the `ℚ_ℓ`-span of the image of `K`), and
  the two maps `G_F → G_ℚ` (through `K` and through `ℚ_ℓ`) differ by conjugation, because any two
  embeddings `ℚ̄ → F̄` differ by an automorphism of `ℚ̄`.
* `g9Glue_of_abVarBaseChange : AbVarBaseChange → R10Weights → G9Glue`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open PkgI4 G0Galois Module

noncomputable section

namespace G9Bridge

/-- **Bridge F2' (base change of abelian varieties with their Tate modules).** -/
def AbVarBaseChange : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A : PkgI3.AbVar K) (L : Type) [Field L] (i : K →+* L)
    (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ (A' : PkgI4.I3.AbVar L) (c : A'.V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ), A'.dim = A.dim ∧
      ∀ σ v, c (A'.galRep ℓ σ v) = A.galRep ℓ (Field.absoluteGaloisGroup.map i σ) (c v)

end G9Bridge

section Conj

/-- An element of `G_K` as an automorphism of `K̄`. -/
abbrev galK {K : Type*} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- `Field.absoluteGaloisGroup.map f` is restriction along an embedding `K̄ → L̄`. -/
theorem exists_emb_map {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    ∃ κ : AlgebraicClosure K →+* AlgebraicClosure L,
      ∀ (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K),
        κ (galK (Field.absoluteGaloisGroup.map f σ) x) = galK σ (κ x) := by
  letI : Algebra K L := f.toAlgebra
  let g0 : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := g0.toAlgebra
  exact ⟨g0.toRingHom, fun σ x =>
    AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) (AlgebraicClosure K) x⟩

/-- Two embeddings of `k̄` into a field over `k` differ by an automorphism of `k̄`. -/
theorem exists_aut_comp {k M : Type*} [Field k] [Field M] [Algebra k M]
    (α1 α2 : AlgebraicClosure k →ₐ[k] M) :
    ∃ δ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, ∀ x, α2 x = α1 (δ x) := by
  letI : Algebra (AlgebraicClosure k) M := α1.toRingHom.toAlgebra
  haveI : IsScalarTower k (AlgebraicClosure k) M :=
    IsScalarTower.of_algebraMap_eq (fun c => (α1.commutes c).symm)
  let δ0 : AlgebraicClosure k →ₐ[k] AlgebraicClosure k :=
    α2.restrictNormal (K₁ := AlgebraicClosure k) (AlgebraicClosure k)
  have h : ∀ x, α1 (δ0 x) = α2 x := fun x =>
    AlgHom.restrictNormal_commutes (K₁ := AlgebraicClosure k) α2 (AlgebraicClosure k) x
  exact ⟨AlgEquiv.ofBijective δ0 (Algebra.IsAlgebraic.algHom_bijective δ0),
    fun x => (h x).symm⟩

/-- Restrictions along two embeddings `ℚ̄ → F̄` are conjugate. -/
theorem conj_of_two_embs {M : Type*} [Field M] [CharZero M] (G : Type*) [Group G] (act : G →* (M ≃+* M))
    (α1 α2 : AlgebraicClosure ℚ →+* M) (τ1 τ2 : G → PkgI4.GQ)
    (h1 : ∀ σ x, α1 (τ1 σ x) = act σ (α1 x)) (h2 : ∀ σ x, α2 (τ2 σ x) = act σ (α2 x)) :
    ∃ g : PkgI4.GQ, ∀ σ, τ1 σ = g * τ2 σ * g⁻¹ := by
  obtain ⟨δ, hδ⟩ := exists_aut_comp (k := ℚ) α1.toRatAlgHom α2.toRatAlgHom
  have hδ' : ∀ x, α2 x = α1 (δ x) := hδ
  refine ⟨δ, fun σ => ?_⟩
  apply AlgEquiv.ext
  intro x
  apply α1.injective
  rw [h1]
  change act σ (α1 x) = α1 (δ (τ2 σ (δ⁻¹ x)))
  rw [← hδ', h2, hδ']
  congr 2
  exact (AlgEquiv.apply_symm_apply δ x).symm

end Conj

section Model

variable (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime]

/-- `K → ℚ̄_ℓ`. -/
def psiK : K →ₐ[ℚ] PadicAlgCl ℓ := IsAlgClosed.lift

/-- The `ℚ_ℓ`-span of the image of a `ℚ`-basis of `K`. -/
def spanK : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) :=
  IntermediateField.adjoin ℚ_[ℓ] (Set.range fun k => psiK K ℓ (Module.finBasis ℚ K k))

instance : FiniteDimensional ℚ_[ℓ] (spanK K ℓ) :=
  have : Finite (Set.range fun k => psiK K ℓ (Module.finBasis ℚ K k)) := Set.finite_range _
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

theorem psiK_mem (x : K) : psiK K ℓ x ∈ spanK K ℓ := by
  rw [← (Module.finBasis ℚ K).sum_repr x, map_sum]
  refine IntermediateField.sum_mem _ fun k _ => ?_
  rw [Algebra.smul_def, map_mul, AlgHom.commutes]
  refine IntermediateField.mul_mem _ ?_ (IntermediateField.subset_adjoin _ _ ⟨k, rfl⟩)
  rw [eq_ratCast]
  exact SubfieldClass.ratCast_mem _ _

/-- The local field: the normal closure of `spanK` in `ℚ̄_ℓ`. -/
def locF : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ) :=
  IntermediateField.normalClosure ℚ_[ℓ] (spanK K ℓ) (PadicAlgCl ℓ)

instance : FiniteDimensional ℚ_[ℓ] (locF K ℓ) := by
  unfold locF; infer_instance

instance : IsGalois ℚ_[ℓ] (locF K ℓ) := by
  unfold locF
  exact { }

/-- `K → F`. -/
def iK : K →+* locF K ℓ :=
  (psiK K ℓ).toRingHom.codRestrict (locF K ℓ) fun x =>
    IntermediateField.le_normalClosure (spanK K ℓ) (psiK_mem K ℓ x)

end Model

/-- `decomp ℓ` is restriction along an embedding `ℚ̄ → ℚ̄_ℓ`. -/
theorem exists_emb_decomp (ℓ : ℕ) [Fact ℓ.Prime] : ∃ κ : AlgebraicClosure ℚ →+* PadicAlgCl ℓ,
    ∀ (τ : GQp ℓ) (x : AlgebraicClosure ℚ), κ (decomp ℓ τ x) = τ (κ x) := by
  let g0 : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[ℓ] := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[ℓ]) := g0.toAlgebra
  exact ⟨g0.toRingHom, fun τ x =>
    AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars ℚ τ) (AlgebraicClosure ℚ) x⟩

/-- `σ ↦ σ` as ring automorphisms. -/
def galRingEquivHom (F : Type*) [Field F] :
    Field.absoluteGaloisGroup F →* (AlgebraicClosure F ≃+* AlgebraicClosure F) where
  toFun σ := (galK σ).toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

set_option maxHeartbeats 2000000 in
/-- **The local model from base change of abelian varieties.** -/
theorem localModel_of_abVarBaseChange (h : G9Bridge.AbVarBaseChange) : G9Bridge.LocalModel := by
  intro K _ _ A ℓ _ hdim
  obtain ⟨A', c, hdim', hc⟩ := h K A (locF K ℓ) (iK K ℓ) ℓ
  obtain ⟨κ1, h1⟩ := exists_emb_map (algebraMap ℚ K)
  obtain ⟨κ2, h2⟩ := exists_emb_map (iK K ℓ)
  obtain ⟨κ3, h3⟩ := exists_emb_decomp ℓ
  let j : Field.absoluteGaloisGroup (locF K ℓ) →* Field.absoluteGaloisGroup K :=
    (Field.absoluteGaloisGroup.map (iK K ℓ) : _ →* _)
  have e1 : ∀ σ x, (κ2.comp κ1) (resQ K (j σ) x) =
      galRingEquivHom (locF K ℓ) σ ((κ2.comp κ1) x) := by
    intro σ x
    change κ2 (κ1 (galK (Field.absoluteGaloisGroup.map (algebraMap ℚ K) (j σ)) x)) =
      galK σ (κ2 (κ1 x))
    rw [h1]
    exact h2 σ (κ1 x)
  have e2 : ∀ σ x, ((embF ℓ (locF K ℓ)).comp κ3) (decomp ℓ (gfToGqp ℓ (locF K ℓ) σ) x) =
      galRingEquivHom (locF K ℓ) σ (((embF ℓ (locF K ℓ)).comp κ3) x) := by
    intro σ x
    change embF ℓ (locF K ℓ) (κ3 (decomp ℓ (gfToGqp ℓ (locF K ℓ) σ) x)) =
      galF (locF K ℓ) σ (embF ℓ (locF K ℓ) (κ3 x))
    rw [h3]
    exact embF_gfToGqp ℓ (locF K ℓ) σ (κ3 x)
  obtain ⟨g, hg⟩ := conj_of_two_embs (M := AlgebraicClosure (locF K ℓ))
    (Field.absoluteGaloisGroup (locF K ℓ)) (galRingEquivHom (locF K ℓ))
    (κ2.comp κ1) ((embF ℓ (locF K ℓ)).comp κ3) (fun σ => resQ K (j σ))
    (fun σ => decomp ℓ (gfToGqp ℓ (locF K ℓ) σ)) e1 e2
  have i3 : FiniteDimensional ℚ_[ℓ] (locF K ℓ) := inferInstance
  have i4 : IsGalois ℚ_[ℓ] (locF K ℓ) := inferInstance
  have hc' : ∀ σ v, c (A'.galRep ℓ σ v) = A.galRep ℓ (j σ) (c v) := hc
  have hg' : ∀ σ, resQ K (j σ) = g * decomp ℓ (gfToGqp ℓ (locF K ℓ) σ) * g⁻¹ := hg
  have hd2 : A'.dim = 2 := hdim'.trans hdim
  exact ⟨locF K ℓ, inferInstance, inferInstance, i3, i4, A', j, c, g, hd2, hc', hg'⟩

/-- **G9 from base change of abelian varieties and the weight clause of R10.** -/
theorem g9Glue_of_abVarBaseChange (hBC : G9Bridge.AbVarBaseChange) (hW : G9Bridge.R10Weights) :
    G9Glue :=
  g9Glue_of_localModel (localModel_of_abVarBaseChange hBC) hW

end

end ZInQ.Contrib.G9

#print axioms ZInQ.Contrib.G9.localModel_of_abVarBaseChange
#print axioms ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange
