import ZInQKernel.Contrib.R10.Amend
import ZInQKernel.Contrib.AbVarBC.Dim

/-!
# hodge-split: the p-adic Hodge theory rows of the frontier, split into published-form leaves

Task hodge-split, 2026-11-14.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

namespace ZInQ.Contrib.HodgeSplit

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

/-! ## §0. The row, verbatim

`G0Galois.FiniteImageHT`, copied verbatim from `scratch/leaf-fold5/Leaves5.lean` (l. 50965; origin
`scratch/g12-det/part_weight.lean`). Its objects (`PkgI4.GaloisRep`, `HasHTWeightsAtSelf`) are the
verbatim copies in `ZInQKernel/Contrib/G9/I4Layer.lean`. -/

namespace G0Galois

open PkgI4 (GaloisRep GaloisChar)

/-- **Finite image implies Hodge–Tate of weight 0 (LEAF; Tate, *p-divisible groups* (1967) §3
Thm 2 (`ℂ_p(i)^{G_L} = 0` for `i ≠ 0`) and Ax–Sen–Tate (`ℂ_p^{G_L} = L`), with Hilbert 90 for
the finite extension cut out by the image; Fontaine–Ouyang Prop. 2.15 / Sen 1980 Cor. of Thm 11;
numbering UNVERIFIED).** A representation of `G_ℚ` with finite image is Hodge–Tate at `p` with all
weights `0` (its image lies in `GL_n(E)` for a finite `E/ℚ_p`: finitely many algebraic entries).
-/
def FiniteImageHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GaloisRep p n),
    (Set.range ρ.toHom).Finite → ρ.HasHTWeightsAtSelf p (Multiset.replicate n 0)

end G0Galois

/-! ## §1. Leaves: Tate's two theorems on `ℂ_p(i)^{G_K}`

`K` runs over the finite extensions of `ℚ_p` inside `ℚ̄_p = PadicAlgCl p`; `G_K = Gal(ℚ̄_p/K)` is
`K.fixingSubgroup ⊆ G_{ℚ_p}`; `ℂ_p = ℂ_[p]` is the completion of `ℚ̄_p`, with pkg-I4's action
`cpAct` and cyclotomic character `cyc` (`cycPow σ i = χ(σ)^i`). -/

/-- **LEAF (Tate 1967, §3.3, Theorem 2; locator UNVERIFIED).** Tate, *p-divisible groups*, Proc.
Conf. Local Fields (Driebergen 1966), Springer 1967, pp. 158-183, §3.3: for a complete discretely
valued field `K` of characteristic `0` with perfect residue field of characteristic `p`, and
`i ≠ 0`, `H⁰(G_K, ℂ(i)) = 0`, where `ℂ` is the completion of `K̄` and `ℂ(i)` its twist by the
`i`-th power of the cyclotomic character. Specialization: `K` finite over `ℚ_p` (inside `ℚ̄_p`, so
that `ℂ = ℂ_p` and `G_K = Gal(ℚ̄_p/K)`). -/
def TateTwistInvariants : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (i : ℤ), i ≠ 0 → ∀ x : ℂ_[p],
      (∀ σ ∈ K.fixingSubgroup, cycPow p σ i • cpAct p σ x = x) → x = 0

/-- **LEAF (Tate 1967, §3.3, Theorem 1 — the Ax–Sen–Tate theorem; locator UNVERIFIED).** Same
setting: `H⁰(G_K, ℂ) = K` (Tate 1967 §3.3; also Sen, Ann. of Math. 90 (1969), and Ax, Invent.
Math. 10 (1970), "Zeros of polynomials over local fields — the Galois action"). Specialization:
`K` finite over `ℚ_p` inside `ℚ̄_p`; the inclusion `K ⊆ ℂ_p^{G_K}` is trivial, the published
content is `ℂ_p^{G_K} ⊆ K`. -/
def AxSenTate : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (x : ℂ_[p]), (∀ σ ∈ K.fixingSubgroup, cpAct p σ x = x) →
      ∃ y : K, x = (((y : PadicAlgCl p)) : ℂ_[p])

/-! ## §2. Glue: equivariant maps into a fixed space -/

section FixLemmas

variable {K G B V : Type*} [Field K] [Group G] [AddCommGroup B] [Module K B]
  [AddCommGroup V] [Module K V]

/-- If `ρ` is trivial on `S`, then `S`-equivariant maps `V → B` are the maps into `B^S`. -/
def dspTrivEquiv (act : G → B →ₗ[K] B) (ρ : G → V →ₗ[K] V) (S : Set G)
    (hρ : ∀ g ∈ S, ρ g = LinearMap.id) (W : Submodule K B)
    (hW : ∀ x, x ∈ W ↔ ∀ g ∈ S, act g x = x) :
    Dsp act ρ S ≃ₗ[K] (V →ₗ[K] W) where
  toFun φ := (φ : V →ₗ[K] B).codRestrict W fun v => (hW _).2 fun g hg => by
    have := φ.2 g hg v
    rw [hρ g hg, LinearMap.id_apply] at this
    exact this.symm
  invFun ψ := ⟨W.subtype ∘ₗ ψ, fun g hg v => by
    rw [hρ g hg, LinearMap.id_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact (((hW _).1 (ψ v).2) g hg).symm⟩
  map_add' φ ψ := by ext; simp
  map_smul' c φ := by ext; simp
  left_inv φ := by ext; simp
  right_inv ψ := by ext; simp

theorem finrank_Dsp_triv [FiniteDimensional K V] (act : G → B →ₗ[K] B) (ρ : G → V →ₗ[K] V)
    (S : Set G) (hρ : ∀ g ∈ S, ρ g = LinearMap.id) (W : Submodule K B) [FiniteDimensional K W]
    (hW : ∀ x, x ∈ W ↔ ∀ g ∈ S, act g x = x) :
    finrank K (Dsp act ρ S) = finrank K V * finrank K W := by
  rw [(dspTrivEquiv act ρ S hρ W hW).finrank_eq, Module.finrank_linearMap]

end FixLemmas

variable (p : ℕ) [Fact p.Prime]

/-- `ℂ_p(i)^S`, the vectors fixed by `c ↦ χ(σ)^i σ(c)` for `σ ∈ S`. -/
def fixSp (i : ℤ) (S : Set (GQp p)) : Submodule ℚ_[p] ℂ_[p] where
  carrier := {x | ∀ σ ∈ S, htAct p i σ x = x}
  zero_mem' := fun σ _ => map_zero _
  add_mem' := fun ha hb σ hσ => by rw [map_add, ha σ hσ, hb σ hσ]
  smul_mem' := fun c x hx σ hσ => by rw [map_smul, hx σ hσ]

theorem mem_fixSp (i : ℤ) (S : Set (GQp p)) (x : ℂ_[p]) :
    x ∈ fixSp p i S ↔ ∀ σ ∈ S, htAct p i σ x = x := Iff.rfl

theorem cycPow_zero (σ : GQp p) : cycPow p σ 0 = 1 := by
  simp [cycPow]

/-- Tate's theorem in `fixSp` form. -/
theorem fixSp_eq_bot (hT : TateTwistInvariants) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] {i : ℤ} (hi : i ≠ 0) :
    fixSp p i (K.fixingSubgroup : Set (GQp p)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine hT p K i hi x fun σ hσ => ?_
  have := hx σ hσ
  rwa [htAct_apply] at this

/-- `K → ℂ_p`. -/
def iotaK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : K →ₐ[ℚ_[p]] ℂ_[p] :=
  (cpEmb p).comp K.val

theorem iotaK_injective (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Function.Injective (iotaK p K) :=
  (iotaK p K).toRingHom.injective

/-- Ax–Sen–Tate in `fixSp` form: `ℂ_p^{G_K} = K`. -/
theorem fixSp_zero_eq (hA : AxSenTate) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    fixSp p 0 (K.fixingSubgroup : Set (GQp p)) = LinearMap.range (iotaK p K).toLinearMap := by
  ext x
  rw [mem_fixSp, LinearMap.mem_range]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := hA p K x fun σ hσ => by
      have := hx σ hσ
      rwa [htAct_apply, cycPow_zero, one_smul] at this
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩ σ hσ
    rw [htAct_apply, cycPow_zero, one_smul]
    change cpAct p σ ((((y : PadicAlgCl p)) : ℂ_[p])) = (((y : PadicAlgCl p)) : ℂ_[p])
    rw [cpAct_coe]
    congr 1
    exact hσ y

theorem finrank_fixSp_zero (hA : AxSenTate) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    finrank ℚ_[p] (fixSp p 0 (K.fixingSubgroup : Set (GQp p))) = finrank ℚ_[p] K := by
  rw [fixSp_zero_eq p hA K, LinearMap.finrank_range_of_inj (iotaK_injective p K)]

theorem fixSp_zero_fd (hA : AxSenTate) (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K] :
    FiniteDimensional ℚ_[p] (fixSp p 0 (K.fixingSubgroup : Set (GQp p))) := by
  rw [fixSp_zero_eq p hA K]
  infer_instance

/-! ## §3. The finite-descent count for a representation trivial on `G_M` -/

/-- **Count.** Let `M ⊆ ℚ̄_p` be finite Galois over `ℚ_p`, `E ⊆ ℚ̄_p` finite over `ℚ_p`, and
`ρE : G_{ℚ_p} → GL_n(E)` trivial on `G_M`. Then, with Tate's theorems, `dim_{ℚ_p} H_i(ρE)` is
`n [E:ℚ_p]` for `i = 0` and `0` otherwise. -/
theorem htSpace_finrank_of_trivial (hT : TateTwistInvariants) (hA : AxSenTate)
    (M : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] M] [IsGalois ℚ_[p] M]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E] {n : ℕ}
    (ρE : GQp p →* GL (Fin n) E) (htriv : ∀ σ ∈ M.fixingSubgroup, ρE σ = 1) (i : ℤ) :
    finrank ℚ_[p] (htSpace p ρE i) = if i = 0 then n * finrank ℚ_[p] E else 0 := by
  classical
  let γ : GQp p →* (M ≃ₐ[ℚ_[p]] M) := AlgEquiv.restrictNormalHom M
  have hγ : Function.Surjective γ := AlgEquiv.restrictNormalHom_surjective (PadicAlgCl p)
  have hker : (γ.ker : Set (GQp p)) = (M.fixingSubgroup : Set (GQp p)) := by
    rw [IntermediateField.restrictNormalHom_ker]
  have hsemi : ∀ g x b, htAct p i g (iotaK p M x * b) = iotaK p M (γ g x) * htAct p i g b := by
    intro g x b
    rw [iotaK, AlgHom.comp_apply, htAct_semi, AlgHom.comp_apply]
    congr 2
    exact (AlgEquiv.restrictNormal_commutes g M x).symm
  have hdesc := descent_finrank (htAct p i) (matRep p ρE) (iotaK p M) γ hγ hsemi
  rw [← htSpace_eq_DspMat] at hdesc
  have hρ : ∀ g ∈ (γ.ker : Set (GQp p)), matRep p ρE g = LinearMap.id := by
    intro g hg
    rw [hker] at hg
    refine LinearMap.ext fun v => ?_
    rw [matRep_apply, htriv g hg]
    simp
  have hW : ∀ x, x ∈ fixSp p i (M.fixingSubgroup : Set (GQp p)) ↔
      ∀ g ∈ (γ.ker : Set (GQp p)), htAct p i g x = x := by
    intro x; rw [hker]; rfl
  have hM : 0 < finrank ℚ_[p] M := Module.finrank_pos
  split_ifs with hi
  · subst hi
    haveI := fixSp_zero_fd p hA M
    have h1 := finrank_Dsp_triv (htAct p 0) (matRep p ρE) (γ.ker : Set (GQp p)) hρ
      (fixSp p 0 (M.fixingSubgroup : Set (GQp p))) hW
    rw [h1, finrank_fixSp_zero p hA M, Module.finrank_pi_fintype] at hdesc
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hdesc
    have : finrank ℚ_[p] M * finrank ℚ_[p] (htSpace p ρE 0) =
        finrank ℚ_[p] M * (n * finrank ℚ_[p] E) := by
      rw [← hdesc]; ring
    exact Nat.eq_of_mul_eq_mul_left hM this
  · have hbot := fixSp_eq_bot p hT M hi
    have : FiniteDimensional ℚ_[p] (fixSp p i (M.fixingSubgroup : Set (GQp p))) := by
      rw [hbot]; infer_instance
    have h1 := finrank_Dsp_triv (htAct p i) (matRep p ρE) (γ.ker : Set (GQp p)) hρ
      (fixSp p i (M.fixingSubgroup : Set (GQp p))) hW
    rw [h1, hbot, finrank_bot, mul_zero] at hdesc
    rcases Nat.mul_eq_zero.mp hdesc.symm with h | h
    · omega
    · exact h

/-! ## §4. Continuity, open kernel, finite coefficient field -/

theorem continuous_decomp : Continuous (decomp p) :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])).continuous

theorem continuous_restrictLocal {n : ℕ} (ρ : GaloisRep p n) :
    Continuous (ρ.restrictLocal p) :=
  ρ.continuous_toHom.comp (continuous_decomp p)

/-- A continuous homomorphism from `G_{ℚ_p}` with finite image is trivial on `G_M` for a finite
Galois `M ⊆ ℚ̄_p`. -/
theorem exists_galois_trivial {H : Type*} [Group H] [TopologicalSpace H] [T1Space H]
    (f : GQp p →* H) (hf : Continuous f) (hfin : (Set.range f).Finite) :
    ∃ M : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] M ∧ IsGalois ℚ_[p] M ∧
      ∀ σ ∈ M.fixingSubgroup, f σ = 1 := by
  have hcl : IsClosed (f.ker : Set (GQp p)) := by
    have : (f.ker : Set (GQp p)) = f ⁻¹' {1} := by ext; simp
    rw [this]
    exact isClosed_singleton.preimage hf
  haveI : Finite f.range := by
    have : (f.range : Set H) = Set.range f := MonoidHom.coe_range f
    exact Set.Finite.to_subtype (this ▸ hfin)
  have hopen : IsOpen (f.ker : Set (GQp p)) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  have hnhds : (f.ker : Set (GQp p)) ∈ nhds (1 : GQp p) := hopen.mem_nhds f.ker.one_mem
  obtain ⟨M, hfd, hnorm, hsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[p] (PadicAlgCl p) _).mp hnhds
  haveI := hfd
  haveI := hnorm
  refine ⟨M, hfd, IsGalois.mk, fun σ hσ => ?_⟩
  exact hsub hσ

/-- The entries of a homomorphism with finite image generate a finite extension. -/
theorem exists_coef_field {n : ℕ} (f : GQp p →* GL (Fin n) (PadicAlgCl p))
    (hfin : (Set.range f).Finite) :
    ∃ (E : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] E ∧
      ∀ g i j, (f g : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ E := by
  let X : Set (PadicAlgCl p) := ⋃ A ∈ Set.range f,
    Set.range fun ij : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) (PadicAlgCl p)) ij.1 ij.2
  have hX : X.Finite := hfin.biUnion fun A _ => Set.finite_range _
  haveI : Finite X := hX.to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[p] X, IntermediateField.finiteDimensional_adjoin
    fun x _ => Algebra.IsIntegral.isIntegral x, fun g i j => ?_⟩
  apply IntermediateField.subset_adjoin
  exact Set.mem_biUnion (Set.mem_range_self g) ⟨(i, j), rfl⟩

/-! ## §5. The row -/

theorem count_replicate_zero (n : ℕ) (w : ℤ) :
    (Multiset.replicate n (0 : ℤ)).count w = if w = 0 then n else 0 := by
  rw [Multiset.count_replicate]
  by_cases h : w = 0
  · subst h; simp
  · simp [h, Ne.symm h]

/-- **H-52, `FiniteImageHT`, from Tate's two theorems.** -/
theorem finiteImageHT_of_tate (hT : TateTwistInvariants) (hA : AxSenTate) :
    G0Galois.FiniteImageHT := by
  intro p _ n ρ hfin
  let f := ρ.restrictLocal p
  have hfinf : (Set.range f).Finite :=
    hfin.subset (Set.range_comp_subset_range (decomp p) ρ.toHom)
  obtain ⟨E, hE, hmem⟩ := exists_coef_field p f hfinf
  haveI := hE
  obtain ⟨M, hMfd, hMgal, htriv⟩ := exists_galois_trivial p f (continuous_restrictLocal p ρ) hfinf
  haveI := hMfd
  haveI := hMgal
  let ρE := liftGL E f hmem
  have hρE : ∀ σ ∈ M.fixingSubgroup, ρE σ = 1 := by
    intro σ hσ
    have h1 : f σ = 1 := htriv σ hσ
    have h2 := liftGL_map E f hmem σ
    rw [h1] at h2
    apply Units.ext
    apply Matrix.map_injective (algebraMap E (PadicAlgCl p)).injective
    have h3 := congrArg (fun A : GL (Fin n) (PadicAlgCl p) => (A : Matrix (Fin n) (Fin n) (PadicAlgCl p))) h2
    simp only [Units.val_one] at h3 ⊢
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h3
  refine ⟨E, hE, ρE, fun σ => liftGL_map E f hmem σ, fun w => ?_⟩
  rw [htMult, htSpace_finrank_of_trivial p hT hA M ρE hρE (-w), count_replicate_zero]
  have hEpos : 0 < finrank ℚ_[p] E := Module.finrank_pos
  by_cases hw : w = 0
  · subst hw
    simp [Nat.mul_div_cancel _ hEpos]
  · simp [hw]


/-! ## §6. H-8: R10 amended (`ZInQ.Contrib.R10.DeRhamComparisonHT`)

The row is imported (`ZInQKernel/Contrib/R10/Amend.lean`). Leaves: the Hodge–Tate decomposition of
`ℂ_p ⊗ V_p(A)` (published form, bases chosen), Tate's two theorems (§1), and the de Rham property
of `V_p(A)^∨ = H¹_ét`. -/

section R10

/-- `σ ∈ G_{ℚ_p}` acting on `ℂ_p`, as a `ℚ_p`-linear map. -/
def cpLin (σ : GQp p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] where
  toFun := cpAct p σ
  map_add' := map_add _
  map_smul' := cpAct_smul p σ

theorem cpLin_apply (σ : GQp p) (x : ℂ_[p]) : cpLin p σ x = cpAct p σ x := rfl

/-- **LEAF (Hodge–Tate decomposition of the Tate module of an abelian variety).** Fontaine,
*Formes différentielles et modules de Tate des variétés abéliennes sur les corps locaux*, Invent.
Math. 65 (1982), 379-409, Théorème principal (with Tate 1967 §4, Cor. 2 of Thm 3 for good
reduction, and Faltings, JAMS 1 (1988), for `H¹_ét`; all locators UNVERIFIED): for an abelian
variety `A` of dimension `g` over a finite extension `F` of `ℚ_p` there is a `G_F`-equivariant
`ℂ_p`-linear isomorphism `ℂ_p ⊗_{ℚ_p} V_p(A) ≅ (ℂ_p(1) ⊗_F t_A) ⊕ (ℂ_p ⊗_F t_{A'}^*)` with
`dim_F t_A = dim_F t_{A'}^* = g` (`t` = tangent space at the origin, `A'` the dual). Lean form:
after choosing `F`-bases of the two `g`-dimensional spaces, `ℂ_p(1)^g ⊕ ℂ_p^g`; `G_F` acts on
`ℂ_p ⊗ V` by `σ ⊗ ρ(σ)` and on `ℂ_p(1)` by `c ↦ χ(σ) σ(c)`, through pkg-I4's `gfToGqp`
(the embedding `ℚ̄_p ≅ F̄` behind Mathlib's `Field.absoluteGaloisGroup.map`, which identifies
`ℂ_F` with `ℂ_p`). Specialization of the printed statement (bases chosen). -/
def HodgeTateDecompAbVar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k)))

/-- **LEAF (the de Rham comparison for `H¹` of an abelian variety, in Tate-module form).**
Published: `H¹_ét(A_{F̄}, ℚ_p)` is de Rham (Fontaine 1982 for abelian varieties; Faltings, *Crystalline
cohomology and p-adic Galois representations* (1989); Tsuji, Invent. Math. 137 (1999);
Scholze, Forum Math. Pi 1 (2013), Cor. 1.8; locators UNVERIFIED except Scholze's wording, VERIFIED
by h-leaves §3.1). Lean form: `H¹_ét = V_p(A)^∨` (the standard identification
`H¹_ét(A_{F̄}, ℤ_p) = Hom(T_p A, ℤ_p)`, Milne, *Abelian varieties* (1986), Thm 15.1(a), UNVERIFIED),
and `D_dR(V^∨) = (B_dR ⊗ V^∨)^{G_F}` written as `Hom_{G_F}(V, B_dR)` (pkg-I4's `IsDeRhamOver`).
Étale cohomology is not in Mathlib, so this is the closest statable form; it is the de Rham clause
of the old R10 without the Hodge–Tate counts. -/
def DeRhamH1AbVar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F), IsDeRhamOver p (A.galRep p)

variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- The image of `G_F` in `G_{ℚ_p}` is `G_{F'}`, `F' = fieldF p F` (any finite `F`, not
necessarily Galois; the proof is g9-derham's `range_gfToGqp`). -/
theorem range_gfToGqp_eq (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] :
    Set.range (gfToGqp p F) = ((fieldF p F).fixingSubgroup : Set (GQp p)) := by
  ext τ
  have hmem : τ ∈ (fieldF p F).fixingSubgroup ↔ ∀ y : F, τ (phiF p F y) = phiF p F y := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h y
      exact h _ ⟨y, rfl⟩
    · rintro h _ ⟨y, rfl⟩
      exact h y
  rw [Set.mem_range, SetLike.mem_coe, hmem]
  constructor
  · rintro ⟨σ, rfl⟩ y
    apply (embF_bijective p F).injective
    rw [embF_gfToGqp, embF_phiF]
    exact (galF F σ).commutes y
  · intro h
    let e := embFEquiv p F
    let σr : AlgebraicClosure F ≃+* AlgebraicClosure F :=
      (e.symm.trans τ.toRingEquiv).trans e
    have hσr : ∀ x, σr x = e (τ (e.symm x)) := fun _ => rfl
    let σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F :=
      { σr with
        commutes' := by
          intro y
          change σr (algebraMap F (AlgebraicClosure F) y) = _
          rw [hσr, ← embF_phiF p F y, ← embFEquiv_apply, RingEquiv.symm_apply_apply, h y,
            embFEquiv_apply, embF_phiF] }
    let σ' : Field.absoluteGaloisGroup F := σ
    refine ⟨σ', ?_⟩
    ext x
    apply (embF_bijective p F).injective
    rw [embF_gfToGqp p F σ' x]
    change σr (embF p F x) = embF p F (τ x)
    rw [hσr, ← embFEquiv_apply, RingEquiv.symm_apply_apply]
    rfl

/-! ### Linear algebra on `W = ℂ_pᵍ × ℂ_pᵍ` -/

variable {g : ℕ}

/-- `w ↦ Σ w₁ₖ c₁ₖ + Σ w₂ₖ c₂ₖ`. -/
def psiC (c : (Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) :
    ((Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) →ₗ[ℂ_[p]] ℂ_[p] where
  toFun w := ∑ k, w.1 k * c.1 k + ∑ k, w.2 k * c.2 k
  map_add' w w' := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' a w := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum, mul_add, mul_assoc]

theorem psiC_apply (c w : (Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) :
    psiC p c w = ∑ k, w.1 k * c.1 k + ∑ k, w.2 k * c.2 k := rfl

/-- The coordinates of a linear form on `W`. -/
def coordsW (ℓ : ((Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) →ₗ[ℂ_[p]] ℂ_[p]) :
    (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]) :=
  (fun k => ℓ (Pi.single k 1, 0), fun k => ℓ (0, Pi.single k 1))

theorem psiC_single_fst (c : (Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) (k : Fin g) :
    psiC p c (Pi.single k 1, 0) = c.1 k := by
  simp [psiC_apply, Pi.single_apply]

theorem psiC_single_snd (c : (Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) (k : Fin g) :
    psiC p c (0, Pi.single k 1) = c.2 k := by
  simp [psiC_apply, Pi.single_apply]

theorem psiC_coordsW (ℓ : ((Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) →ₗ[ℂ_[p]] ℂ_[p]) :
    psiC p (coordsW p ℓ) = ℓ := by
  apply LinearMap.prod_ext
  · apply LinearMap.pi_ext'
    intro k
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.coe_single]
    rw [psiC_single_fst]
    rfl
  · apply LinearMap.pi_ext'
    intro k
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearMap.coe_single]
    rw [psiC_single_snd]
    rfl

theorem psiC_add (c c' : (Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) :
    psiC p (c + c') = psiC p c + psiC p c' := by
  refine LinearMap.ext fun w => ?_
  simp only [psiC_apply, LinearMap.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  ring

theorem psiC_smul (a : ℚ_[p]) (c : (Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) :
    psiC p (a • c) = a • psiC p c := by
  refine LinearMap.ext fun w => ?_
  simp only [psiC_apply, LinearMap.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
    Finset.smul_sum, mul_smul_comm, smul_add]

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
  (e : ℂ_[p] ⊗[ℚ_[p]] V ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]))

/-- `c ↦ (v ↦ ψ_c(e(1 ⊗ v)))`. -/
def PsiE : ((Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) →ₗ[ℚ_[p]] (V →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun c := (psiC p c).restrictScalars ℚ_[p] ∘ₗ (e.toLinearMap.restrictScalars ℚ_[p]) ∘ₗ
    TensorProduct.mk ℚ_[p] ℂ_[p] V 1
  map_add' c c' := by ext v; simp [psiC_add]
  map_smul' a c := by ext v; simp [psiC_smul]

theorem PsiE_apply (c : (Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) (v : V) :
    PsiE p e c v = psiC p c (e (1 ⊗ₜ v)) := rfl

theorem tmul_eq_smul_one_tmul (a : ℂ_[p]) (v : V) :
    (a ⊗ₜ[ℚ_[p]] v : ℂ_[p] ⊗[ℚ_[p]] V) = a • ((1 : ℂ_[p]) ⊗ₜ v) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- A `ℂ_p`-linear form on `ℂ_p ⊗ V` vanishing on `1 ⊗ V` vanishes. -/
theorem ext_one_tmul {ℓ ℓ' : ℂ_[p] ⊗[ℚ_[p]] V →ₗ[ℂ_[p]] ℂ_[p]}
    (h : ∀ v, ℓ (1 ⊗ₜ v) = ℓ' (1 ⊗ₜ v)) : ℓ = ℓ' := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => rw [tmul_eq_smul_one_tmul, map_smul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem PsiE_injective : Function.Injective (PsiE p e) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro c hc
  rw [LinearMap.mem_ker] at hc
  rw [Submodule.mem_bot]
  have h1 : (psiC p c) ∘ₗ e.toLinearMap = 0 := by
    apply ext_one_tmul p
    intro v
    have := LinearMap.congr_fun hc v
    rw [PsiE_apply] at this
    simpa using this
  have h2 : psiC p c = 0 := by
    refine LinearMap.ext fun w => ?_
    have := LinearMap.congr_fun h1 (e.symm w)
    simpa using this
  ext k
  · rw [← psiC_single_fst p c k, h2]; rfl
  · rw [← psiC_single_snd p c k, h2]; rfl

theorem PsiE_surjective : Function.Surjective (PsiE p e) := by
  intro φ
  let ℓ := (LinearMap.liftBaseChange ℂ_[p] φ) ∘ₗ e.symm.toLinearMap
  refine ⟨coordsW p ℓ, ?_⟩
  ext v
  rw [PsiE_apply, psiC_coordsW]
  simp [ℓ]

/-! ### The Hodge–Tate spaces of `V` from the decomposition -/

variable (S : Set (GQp p))

/-- `{c ∈ W | c₁ₖ ∈ ℂ_p(i₁)^S, c₂ₖ ∈ ℂ_p(i₂)^S}`. -/
def PSub (i₁ i₂ : ℤ) : Submodule ℚ_[p] ((Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) where
  carrier := {c | ∀ k, c.1 k ∈ fixSp p i₁ S ∧ c.2 k ∈ fixSp p i₂ S}
  zero_mem' k := ⟨(fixSp p i₁ S).zero_mem, (fixSp p i₂ S).zero_mem⟩
  add_mem' ha hb k := ⟨(fixSp p i₁ S).add_mem (ha k).1 (hb k).1,
    (fixSp p i₂ S).add_mem (ha k).2 (hb k).2⟩
  smul_mem' a c hc k := ⟨(fixSp p i₁ S).smul_mem a (hc k).1, (fixSp p i₂ S).smul_mem a (hc k).2⟩

theorem finrank_PSub (i₁ i₂ : ℤ) [FiniteDimensional ℚ_[p] (fixSp p i₁ S)]
    [FiniteDimensional ℚ_[p] (fixSp p i₂ S)] :
    finrank ℚ_[p] (PSub p S (g := g) i₁ i₂) =
      g * finrank ℚ_[p] (fixSp p i₁ S) + g * finrank ℚ_[p] (fixSp p i₂ S) := by
  let ι : ((Fin g → fixSp p i₁ S) × (Fin g → fixSp p i₂ S)) →ₗ[ℚ_[p]]
      ((Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) :=
    ((fixSp p i₁ S).subtype.compLeft (Fin g)).prodMap ((fixSp p i₂ S).subtype.compLeft (Fin g))
  have hinj : Function.Injective ι := by
    intro a b h
    simp only [ι, LinearMap.prodMap_apply, Prod.mk.injEq] at h
    ext k
    · exact congrFun h.1 k
    · exact congrFun h.2 k
  have hrange : LinearMap.range ι = PSub p S i₁ i₂ := by
    ext c
    constructor
    · rintro ⟨a, rfl⟩ k
      exact ⟨(a.1 k).2, (a.2 k).2⟩
    · intro hc
      exact ⟨(fun k => ⟨c.1 k, (hc k).1⟩, fun k => ⟨c.2 k, (hc k).2⟩), rfl⟩
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_prod,
    Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp

variable (he : ∀ σ x, e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) x) =
  ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
    (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k))))

include he in
theorem PsiE_mem_fwd (j : ℤ) (c : (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]))
    (hc : PsiE p e c ∈ htSpaceOver p ρ j) :
    c ∈ PSub p (Set.range (gfToGqp p F)) (j - 1) j := by
  -- extend the equivariance to `ℂ_p ⊗ V`
  have hx : ∀ σ x, psiC p c (e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) x)) =
      cycPow p (gfToGqp p F σ) j • cpAct p (gfToGqp p F σ) (psiC p c (e x)) := by
    intro σ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      rw [TensorProduct.map_tmul, cpLin_apply, tmul_eq_smul_one_tmul p (cpAct p _ a),
        tmul_eq_smul_one_tmul p a, map_smul, map_smul, map_smul, map_smul, smul_eq_mul,
        smul_eq_mul, map_mul]
      have := hc σ v
      rw [PsiE_apply, PsiE_apply] at this
      rw [this, mul_smul_comm]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  intro k
  constructor
  · rintro _ ⟨σ, rfl⟩
    have h1 := hx σ (e.symm (Pi.single k 1, 0))
    rw [he, LinearEquiv.apply_symm_apply, psiC_single_fst] at h1
    have h2 : ((fun m => cycPow p (gfToGqp p F σ) 1 •
        cpAct p (gfToGqp p F σ) (((Pi.single k 1 : Fin g → ℂ_[p]), (0 : Fin g → ℂ_[p])).1 m)),
        (fun m => cpAct p (gfToGqp p F σ) (((Pi.single k 1 : Fin g → ℂ_[p]), (0 : Fin g → ℂ_[p])).2 m))) =
        cycPow p (gfToGqp p F σ) 1 • (((Pi.single k 1 : Fin g → ℂ_[p]), (0 : Fin g → ℂ_[p])) :
          (Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) := by
      ext m
      · by_cases hm : m = k
        · subst hm; simp
        · simp [Pi.single_apply, hm]
      · simp
    rw [h2, LinearMap.map_smul_of_tower, psiC_single_fst] at h1
    rw [htAct_apply]
    have hj : j = (j - 1) + 1 := by ring
    rw [hj, cycPow_add_one, mul_smul] at h1
    exact (smul_right_injective _ (cycPow_one_ne_zero p _) h1).symm
  · rintro _ ⟨σ, rfl⟩
    have h1 := hx σ (e.symm (0, Pi.single k 1))
    rw [he, LinearEquiv.apply_symm_apply, psiC_single_snd] at h1
    have h2 : ((fun m => cycPow p (gfToGqp p F σ) 1 •
        cpAct p (gfToGqp p F σ) (((0 : Fin g → ℂ_[p]), (Pi.single k 1 : Fin g → ℂ_[p])).1 m)),
        (fun m => cpAct p (gfToGqp p F σ) (((0 : Fin g → ℂ_[p]), (Pi.single k 1 : Fin g → ℂ_[p])).2 m))) =
        (((0 : Fin g → ℂ_[p]), (Pi.single k 1 : Fin g → ℂ_[p])) :
          (Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) := by
      ext m
      · simp
      · by_cases hm : m = k
        · subst hm; simp
        · simp [Pi.single_apply, hm]
    rw [h2, psiC_single_snd] at h1
    rw [htAct_apply]
    exact h1.symm

include he in
theorem PsiE_mem_bwd (j : ℤ) (c : (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]))
    (hc : c ∈ PSub p (Set.range (gfToGqp p F)) (j - 1) j) :
    PsiE p e c ∈ htSpaceOver p ρ j := by
  intro σ v
  have h1 : ((1 : ℂ_[p]) ⊗ₜ[ℚ_[p]] ρ σ v) =
      TensorProduct.map (cpLin p (gfToGqp p F σ)) (ρ σ) (1 ⊗ₜ v) := by
    rw [TensorProduct.map_tmul, cpLin_apply, map_one]
  rw [PsiE_apply, PsiE_apply, h1, he]
  obtain ⟨τ, hτ⟩ : ∃ τ, gfToGqp p F σ = τ := ⟨_, rfl⟩
  rw [hτ]
  obtain ⟨w, hw⟩ : ∃ w, e (1 ⊗ₜ v) = w := ⟨_, rfl⟩
  rw [hw]
  have hcj : algebraMap ℚ_[p] ℂ_[p] (cycPow p τ j) =
      algebraMap ℚ_[p] ℂ_[p] (cycPow p τ 1) * algebraMap ℚ_[p] ℂ_[p] (cycPow p τ (j - 1)) := by
    rw [← map_mul, ← cycPow_add_one]
    congr 2
    ring
  have t1 : ∀ m, (cycPow p τ 1 • cpAct p τ (w.1 m)) * c.1 m =
      cycPow p τ j • cpAct p τ (w.1 m * c.1 m) := by
    intro m
    have h := (hc m).1 τ ⟨σ, hτ⟩
    rw [htAct_apply] at h
    conv_lhs => rw [← h]
    rw [map_mul, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, hcj]
    ring
  have t2 : ∀ m, cpAct p τ (w.2 m) * c.2 m = cycPow p τ j • cpAct p τ (w.2 m * c.2 m) := by
    intro m
    have h := (hc m).2 τ ⟨σ, hτ⟩
    rw [htAct_apply] at h
    conv_lhs => rw [← h]
    rw [map_mul, Algebra.smul_def, Algebra.smul_def]
    ring
  rw [psiC_apply, psiC_apply]
  rw [Finset.sum_congr rfl (fun m _ => t1 m), Finset.sum_congr rfl (fun m _ => t2 m)]
  rw [← Finset.smul_sum, ← Finset.smul_sum, ← smul_add, map_add, map_sum, map_sum]

include he in
/-- **The count.** `htSpaceOver j ≅ (ℂ_p(j−1)^{G_F})ᵍ × (ℂ_p(j)^{G_F})ᵍ`. -/
theorem htSpaceOver_eq_map (j : ℤ) :
    htSpaceOver p ρ j = Submodule.map (PsiE p e) (PSub p (Set.range (gfToGqp p F)) (j - 1) j) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨c, rfl⟩ := PsiE_surjective p e φ
    exact ⟨c, PsiE_mem_fwd p ρ e he j c hφ, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact PsiE_mem_bwd p ρ e he j c hc

include he in
theorem finrank_htSpaceOver_of_decomp (j : ℤ) :
    finrank ℚ_[p] (htSpaceOver p ρ j) =
      finrank ℚ_[p] (PSub p (Set.range (gfToGqp p F)) (g := g) (j - 1) j) := by
  rw [htSpaceOver_eq_map p ρ e he j]
  exact (Submodule.equivMapOfInjective _ (PsiE_injective p e) _).finrank_eq.symm

/-- `ℂ_p(i)^{G_F}` for `F` acting through `gfToGqp`: `F'` if `i = 0`, else `0`. -/
theorem fixSp_range_eq_bot (hT : TateTwistInvariants) {i : ℤ} (hi : i ≠ 0) :
    fixSp p i (Set.range (gfToGqp p F)) = ⊥ := by
  rw [range_gfToGqp_eq]
  exact fixSp_eq_bot p hT (fieldF p F) hi

theorem finrank_fixSp_range_zero (hA : AxSenTate) :
    finrank ℚ_[p] (fixSp p 0 (Set.range (gfToGqp p F))) = finrank ℚ_[p] F := by
  rw [range_gfToGqp_eq, finrank_fixSp_zero p hA (fieldF p F), finrank_fieldF]

theorem fd_fixSp_range (hT : TateTwistInvariants) (hA : AxSenTate) (i : ℤ) :
    FiniteDimensional ℚ_[p] (fixSp p i (Set.range (gfToGqp p F))) := by
  by_cases hi : i = 0
  · subst hi
    rw [range_gfToGqp_eq]
    exact fixSp_zero_fd p hA (fieldF p F)
  · rw [fixSp_range_eq_bot p hT hi]
    infer_instance

theorem finrank_fixSp_range (hT : TateTwistInvariants) (hA : AxSenTate) (i : ℤ) :
    finrank ℚ_[p] (fixSp p i (Set.range (gfToGqp p F))) =
      if i = 0 then finrank ℚ_[p] F else 0 := by
  split_ifs with hi
  · subst hi; exact finrank_fixSp_range_zero p hA
  · rw [fixSp_range_eq_bot p hT hi, finrank_bot]

include he in
/-- **Hodge–Tate multiplicities from the decomposition and Tate's theorems.** -/
theorem htMultOver_of_decomp (hT : TateTwistInvariants) (hA : AxSenTate) (w : ℤ) :
    htMultOver p ρ w = g * ((if w = 0 then 1 else 0) + (if w = -1 then 1 else 0)) := by
  have hF : 0 < finrank ℚ_[p] F := Module.finrank_pos
  haveI := fd_fixSp_range p (F := F) hT hA (-w - 1)
  haveI := fd_fixSp_range p (F := F) hT hA (-w)
  rw [htMultOver, finrank_htSpaceOver_of_decomp p ρ e he (-w), finrank_PSub,
    finrank_fixSp_range p hT hA, finrank_fixSp_range p hT hA]
  by_cases h0 : w = 0
  · subst h0
    simp [Nat.mul_div_cancel _ hF]
  by_cases h1 : w = -1
  · subst h1
    simp [Nat.mul_div_cancel _ hF]
  have h2 : -w - 1 ≠ 0 := by omega
  have h3 : -w ≠ 0 := by omega
  simp [h0, h1, h2, h3]

end R10

/-- The dimension of pkg-I4's abelian variety is a natural number (abvar-bc's `dim_finite`,
transported along the `rfl` identification of the two verbatim copies of `AbVar`). -/
theorem dim_finite_I4 {K : Type} [Field K] (A : PkgI4.I3.AbVar K) :
    ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) :=
  _root_.PkgI3.AbVar.dim_finite (@_root_.PkgI3.AbVar.mk K _ A.X A.grp A.proper A.smooth A.geomInt)

/-- **H-8, R10 amended, from four published-form leaves.** -/
theorem deRhamComparisonHT_of_leaves (hHT : HodgeTateDecompAbVar) (hT : TateTwistInvariants)
    (hA : AxSenTate) (hdR : DeRhamH1AbVar) : ZInQ.Contrib.R10.DeRhamComparisonHT := by
  intro p _ F _ _ _ A
  have hmult : ∀ g : ℕ, A.dim = (g : WithBot ℕ∞) → ∀ w : ℤ,
      htMultOver p (A.galRep p) w = g * ((if w = 0 then 1 else 0) + (if w = -1 then 1 else 0)) := by
    intro g hg w
    obtain ⟨e, he⟩ := hHT p F A g hg
    exact htMultOver_of_decomp p (A.galRep p) e he hT hA w
  refine ⟨fun g hg => ⟨hdR p F A, ?_, ?_⟩, fun w hw0 hw1 => ?_⟩
  · rw [hmult g hg 0]; simp
  · rw [hmult g hg (-1)]; simp
  · obtain ⟨g, hg⟩ := dim_finite_I4 A
    rw [hmult g hg w]; simp [hw0, hw1]

end

end ZInQ.Contrib.HodgeSplit

#print axioms ZInQ.Contrib.HodgeSplit.finiteImageHT_of_tate
#print axioms ZInQ.Contrib.HodgeSplit.deRhamComparisonHT_of_leaves
