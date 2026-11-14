import ZInQKernel.Contrib.R10.Amend
import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.HDecomp.ModCurves.C9
import ZInQKernel.HDecomp.Textbook.C10Closed
import ZInQKernel.Contrib.Chebotarev.FrobeniusDense

/-!
# hodge-split: the p-adic Hodge theory rows of the frontier, split into published-form leaves

Task hodge-split, 2026-11-14 (report `docs/research/hodge-split.md`, log `scratch/hodge-split/log.md`).
Check with `lake env lean scratch/hodge-split/HodgeSplit.lean` after building the imported modules.

Rows (frontier r3): H-52 `FiniteImageHT` (§1-§5), H-8 R10 amended (§6, §15), H-32 T23 (§7), H-22 `R14Det`
(§8, §14, §17-§18), H-9 `PanBerger` (§9), H-10 `EigenformHT` (§10, §13, §18), H-51 `SenTwist` (§11, §12,
§16). Main theorem: `hodge_rows_of_leaves`. All references to pkg-I4's objects are written out as
`ZInQ.Contrib.G9.PkgI4.*`, because `ZInQKernel.HDecomp` (imported for the kernel's Chebotarev and
Brauer–Nesbitt) has its own root-level `PkgI4`.
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
`scratch/g12-det/part_weight.lean`). Its objects (`ZInQ.Contrib.G9.PkgI4.GaloisRep`, `HasHTWeightsAtSelf`) are the
verbatim copies in `ZInQKernel/Contrib/G9/I4Layer.lean`. -/

namespace G0Galois

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)

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
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
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
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), IsDeRhamOver p (A.galRep p)

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
theorem dim_finite_I4 {K : Type} [Field K] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar K) :
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


/-! ## §7. H-32: T23 (`ZInQ.Contrib.G9.PkgI4.T23_FontaineClosure`), from Fontaine's Tannakian theorem on `V`

pkg-I4's `IsDeRham ρ` computes `D_dR` on `V^∨` (as `Hom_{G}(V, B_dR)`). The published statement is
about `D_dR(V) = (B_dR ⊗ V)^G`. Here `ddrStd` is that space for `V = ℚ_pⁿ` (coordinates), the leaf
`FontaineDRTannakian` is Fontaine's theorem for it (matrix form), and `isDeRham_iff_std` proves
`IsDeRham ρ ↔ IsDeRhamStd ρ^∨` with `ρ^∨(σ) = ρ(σ⁻¹)ᵀ`. -/

section T23

/-- `(B_dR ⊗_{ℚ_p} ℚ_pⁿ)^{G_{ℚ_p}}` in coordinates: `x ∈ B_dRⁿ` with `ρ(σ) · σ(x) = x`. -/
def ddrStd {n : ℕ} (ρ : GQp p →* GL (Fin n) ℚ_[p]) : Submodule ℚ_[p] (Fin n → BdR p) where
  carrier := {x | ∀ σ, ((ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]).map (algebraMap ℚ_[p] (BdR p))).mulVec
    (fun i => bdrAct p σ (x i)) = x}
  zero_mem' σ := by
    have : (fun i => bdrAct p σ ((0 : Fin n → BdR p) i)) = 0 := by ext; simp
    rw [this, Matrix.mulVec_zero]
  add_mem' {x y} hx hy σ := by
    have : (fun i => bdrAct p σ ((x + y) i)) = (fun i => bdrAct p σ (x i)) + fun i => bdrAct p σ (y i) := by
      ext i; simp
    rw [this, Matrix.mulVec_add, hx σ, hy σ]
  smul_mem' c x hx σ := by
    have : (fun i => bdrAct p σ ((c • x) i)) = c • fun i => bdrAct p σ (x i) := by
      ext i; simp [bdrAct_smul]
    rw [this, Matrix.mulVec_smul, hx σ]

/-- **`V` is de Rham** (Fontaine): `dim_{ℚ_p} (B_dR ⊗ V)^{G_{ℚ_p}} = dim_{ℚ_p} V`, for
`V = ℚ_pⁿ` with the matrix representation `ρ` (`B_dR^{G_{ℚ_p}} = ℚ_p`). -/
def IsDeRhamStd {n : ℕ} (ρ : GQp p →* GL (Fin n) ℚ_[p]) : Prop :=
  finrank ℚ_[p] (ddrStd p ρ) = n

/-- **LEAF (Fontaine: de Rham representations form a Tannakian subcategory).** Fontaine,
*Le corps des périodes p-adiques*, Astérisque 223 (1994), Exp. II, and *Représentations p-adiques
semi-stables*, same volume, Exp. III, §1.5 (for a `(ℚ_p, G)`-regular ring `B`, the `B`-admissible
representations are stable under subobjects, quotients, direct sums, tensor products and duals)
with `B = B_dR` (`(ℚ_p, G_{ℚ_p})`-regular, Exp. II/III); Brinon–Conrad, *CMI summer school notes on
p-adic Hodge theory* (2009), Thm 5.2.1 and §6.3; numbering UNVERIFIED. Lean form: continuous
`ℚ_p`-linear representations on `ℚ_pⁿ` in matrices (a choice of bases), `IsDeRhamStd` the
printed definition `dim_{ℚ_p} (B_dR ⊗ V)^G = dim V`: (a) duals (`σ ↦ ρ(σ)⁻ᵀ`); (b) the
subrepresentation on the last `b` coordinates and the quotient on the first `a` of a block lower
triangular `ρ`; (c) block diagonal direct sums; (d) Kronecker tensor products. Each clause is the
printed statement for the representations in a basis adapted to the construction. -/
def FontaineDRTannakian : Prop :=
  (∀ (n : ℕ) (ρ ρ' : GQp p →* GL (Fin n) ℚ_[p]), ContRep p ρ →
    (∀ σ, (ρ' σ : Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((ρ σ)⁻¹ : GL (Fin n) ℚ_[p]).val.transpose) →
    IsDeRhamStd p ρ → IsDeRhamStd p ρ') ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a + b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]) (Y : GQp p → Matrix (Fin b) (Fin a) ℚ_[p]), ContRep p ρ →
    (∀ σ, (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p]) 0 (Y σ)
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRhamStd p ρ → IsDeRhamStd p ρ₁ ∧ IsDeRhamStd p ρ₂) ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a + b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]), ContRep p ρ₁ → ContRep p ρ₂ →
    (∀ σ, (ρ σ : Matrix (Fin (a + b)) (Fin (a + b)) ℚ_[p]) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p]) 0 0
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRhamStd p ρ₁ → IsDeRhamStd p ρ₂ → IsDeRhamStd p ρ) ∧
  (∀ (a b : ℕ) (ρ : GQp p →* GL (Fin (a * b)) ℚ_[p]) (ρ₁ : GQp p →* GL (Fin a) ℚ_[p])
    (ρ₂ : GQp p →* GL (Fin b) ℚ_[p]), ContRep p ρ₁ → ContRep p ρ₂ →
    (∀ σ, (ρ σ : Matrix (Fin (a * b)) (Fin (a * b)) ℚ_[p]) =
      Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.kroneckerMap (· * ·) (ρ₁ σ : Matrix (Fin a) (Fin a) ℚ_[p])
          (ρ₂ σ : Matrix (Fin b) (Fin b) ℚ_[p]))) →
    IsDeRhamStd p ρ₁ → IsDeRhamStd p ρ₂ → IsDeRhamStd p ρ)

variable {n : ℕ}

theorem gl_inv_mul (ρ : GQp p →* GL (Fin n) ℚ_[p]) (σ : GQp p) :
    (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) * (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem gl_mul_inv (ρ : GQp p →* GL (Fin n) ℚ_[p]) (σ : GQp p) :
    (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) * (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

/-- The contragredient `ρ^∨(σ) = ρ(σ⁻¹)ᵀ`. -/
def dualRep (ρ : GQp p →* GL (Fin n) ℚ_[p]) : GQp p →* GL (Fin n) ℚ_[p] where
  toFun σ := ⟨(ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]).transpose,
    (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]).transpose,
    by rw [← Matrix.transpose_mul, gl_mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, gl_inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' σ τ := Units.ext (by
    simp only [mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul])

theorem dualRep_val (ρ : GQp p →* GL (Fin n) ℚ_[p]) (σ : GQp p) :
    (dualRep p ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) =
      (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]).transpose := rfl

theorem dualRep_dualRep (ρ : GQp p →* GL (Fin n) ℚ_[p]) : dualRep p (dualRep p ρ) = ρ := by
  refine MonoidHom.ext fun σ => Units.ext ?_
  rw [dualRep_val, dualRep_val, inv_inv, Matrix.transpose_transpose]

theorem contRep_dualRep (ρ : GQp p →* GL (Fin n) ℚ_[p]) (h : ContRep p ρ) :
    ContRep p (dualRep p ρ) := by
  unfold ContRep at h ⊢
  simp only [dualRep_val]
  exact (h.comp continuous_inv).matrix_transpose

theorem dualRep_of_eq (ρ ρ' : GQp p →* GL (Fin n) ℚ_[p])
    (h : ∀ σ, (ρ' σ : Matrix (Fin n) (Fin n) ℚ_[p]) =
      ((ρ σ)⁻¹ : GL (Fin n) ℚ_[p]).val.transpose) : ρ' = dualRep p ρ := by
  refine MonoidHom.ext fun σ => Units.ext ?_
  rw [h σ, dualRep_val, map_inv]

/-- The ℚ_p-linear matrix action on `ℚ_pⁿ`. -/
def matLin (ρ : GQp p →* GL (Fin n) ℚ_[p]) (σ : GQp p) : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] (Fin n → ℚ_[p]) :=
  Matrix.mulVecLin (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p])

/-- Coordinates of `f : ℚ_pⁿ → B_dR`. -/
theorem lin_apply_eq_sum (f : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] BdR p) (v : Fin n → ℚ_[p]) :
    f v = ∑ i, v i • f (Pi.single i 1) := by
  conv_lhs => rw [show v = ∑ i, v i • (Pi.single i 1 : Fin n → ℚ_[p]) by
    ext j; simp [Pi.single_apply]]
  rw [map_sum]
  simp [map_smul]

/-- `f ∈ D_dR(V^∨)` iff its coordinate vector satisfies `ρ(σ)ᵀ x = σ(x)`. -/
theorem mem_ddrSpace_iff_coord (ρ : GQp p →* GL (Fin n) ℚ_[p])
    (f : (Fin n → ℚ_[p]) →ₗ[ℚ_[p]] BdR p) :
    f ∈ ddrSpace p ρ ↔ ∀ σ, ((ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]).transpose.map
      (algebraMap ℚ_[p] (BdR p))).mulVec (fun i => f (Pi.single i 1)) =
        fun k => bdrAct p σ (f (Pi.single k 1)) := by
  have hcol : ∀ σ k, f ((ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]).mulVec (Pi.single k 1)) =
      (((ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]).transpose.map
        (algebraMap ℚ_[p] (BdR p))).mulVec (fun i => f (Pi.single i 1))) k := by
    intro σ k
    rw [lin_apply_eq_sum p f]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.transpose_apply,
      Algebra.smul_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Pi.single_apply]
  constructor
  · intro hf σ
    ext k
    rw [← hcol]
    exact hf σ _
  · intro h σ v
    have e1 : f ∘ₗ matLin p ρ σ = (drAct p σ) ∘ₗ f := by
      apply LinearMap.pi_ext
      intro k c
      have hs : (Pi.single k c : Fin n → ℚ_[p]) = c • Pi.single k 1 := by
        ext j; simp [Pi.single_apply]
      rw [hs, map_smul, map_smul]
      congr 1
      simp only [LinearMap.comp_apply, matLin, Matrix.mulVecLin_apply, drAct_apply]
      rw [hcol, h σ]
    have := LinearMap.congr_fun e1 v
    simpa [matLin, drAct_apply] using this

theorem mulVec_map_mulVec (A B : Matrix (Fin n) (Fin n) ℚ_[p]) (x : Fin n → BdR p) :
    (A.map (algebraMap ℚ_[p] (BdR p))).mulVec ((B.map (algebraMap ℚ_[p] (BdR p))).mulVec x) =
      ((A * B).map (algebraMap ℚ_[p] (BdR p))).mulVec x := by
  rw [Matrix.mulVec_mulVec, Matrix.map_mul]

theorem mem_ddrStd_dual_iff (ρ : GQp p →* GL (Fin n) ℚ_[p]) (x : Fin n → BdR p) :
    x ∈ ddrStd p (dualRep p ρ) ↔ ∀ σ, ((ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]).transpose.map
      (algebraMap ℚ_[p] (BdR p))).mulVec x = fun k => bdrAct p σ (x k) := by
  constructor
  · intro hx σ
    have h := hx σ
    rw [dualRep_val] at h
    calc _ = ((ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]).transpose.map (algebraMap ℚ_[p] (BdR p))).mulVec
          ((((ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]).transpose).map (algebraMap ℚ_[p] (BdR p))).mulVec
            (fun i => bdrAct p σ (x i))) := by rw [h]
      _ = _ := by
        rw [mulVec_map_mulVec, ← Matrix.transpose_mul, gl_inv_mul, Matrix.transpose_one,
          Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  · intro h σ
    rw [dualRep_val, ← h σ, mulVec_map_mulVec, ← Matrix.transpose_mul, gl_mul_inv,
      Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

/-- **`IsDeRham ρ ↔ IsDeRhamStd ρ^∨`** (pkg-I4's Hom form of `D_dR(V^∨)` against the printed
`(B_dR ⊗ V^∨)^G`, through coordinates). -/
theorem isDeRham_iff_std (ρ : GQp p →* GL (Fin n) ℚ_[p]) :
    IsDeRham p ρ ↔ IsDeRhamStd p (dualRep p ρ) := by
  let L := LinearEquiv.piRing ℚ_[p] (BdR p) (Fin n) ℚ_[p]
  have hmap : Submodule.map L.toLinearMap (ddrSpace p ρ) = ddrStd p (dualRep p ρ) := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [mem_ddrStd_dual_iff]
      intro σ
      have := (mem_ddrSpace_iff_coord p ρ f).mp hf σ
      have hL : L f = fun i => f (Pi.single i 1) := by
        ext i; simp [L, LinearEquiv.piRing_apply]
      simp only [LinearEquiv.coe_coe]
      rw [hL]
      exact this
    · intro hx
      refine ⟨L.symm x, ?_, by simp⟩
      show L.symm x ∈ ddrSpace p ρ
      rw [mem_ddrSpace_iff_coord]
      intro σ
      have hx' := (mem_ddrStd_dual_iff p ρ x).mp hx σ
      have hc : (fun i => (L.symm x) (Pi.single i 1)) = x := by
        have := L.apply_symm_apply x
        ext i
        rw [← this]
        simp only [L, LinearEquiv.piRing_apply, LinearEquiv.apply_symm_apply]
      rw [hc, show (fun k => bdrAct p σ ((L.symm x) (Pi.single k 1))) = fun k => bdrAct p σ (x k)
        from funext fun k => by rw [congrFun hc k]]
      exact hx'
  have hfin : finrank ℚ_[p] (ddrSpace p ρ) = finrank ℚ_[p] (ddrStd p (dualRep p ρ)) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective _ L.injective _).finrank_eq
  rw [IsDeRham, IsDeRhamStd, hfin, Module.finrank_self, mul_one]

/-- Clause (i) of T23 needs no leaf: conjugation by `P` identifies the two `D_dR`. -/
theorem isDeRham_conj (ρ ρ' : GQp p →* GL (Fin n) ℚ_[p]) (P : GL (Fin n) ℚ_[p])
    (h : ∀ σ, ρ' σ = P * ρ σ * P⁻¹) : IsDeRham p ρ → IsDeRham p ρ' := by
  intro hρ
  let Pm := (P : Matrix (Fin n) (Fin n) ℚ_[p])
  let Qm := ((P⁻¹ : GL (Fin n) ℚ_[p]) : Matrix (Fin n) (Fin n) ℚ_[p])
  have hQP : Qm * Pm = 1 := by simp [Qm, Pm]
  have hPQ : Pm * Qm = 1 := by simp [Qm, Pm]
  have hρ' : ∀ σ, (ρ' σ : Matrix (Fin n) (Fin n) ℚ_[p]) = Pm * (ρ σ : Matrix (Fin n) (Fin n) ℚ_[p]) * Qm := by
    intro σ; rw [h σ]; rfl
  let e : ddrSpace p ρ ≃ₗ[ℚ_[p]] ddrSpace p ρ' :=
    { toFun := fun φ => ⟨φ.1 ∘ₗ Matrix.mulVecLin Qm, fun σ v => by
        simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, hρ', Matrix.mulVec_mulVec]
        rw [← φ.2 σ (Qm.mulVec v), Matrix.mulVec_mulVec]
        congr 2
        simp only [← mul_assoc, hQP, one_mul]⟩
      invFun := fun ψ => ⟨ψ.1 ∘ₗ Matrix.mulVecLin Pm, fun σ v => by
        simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
        rw [← ψ.2 σ (Pm.mulVec v), Matrix.mulVec_mulVec, hρ']
        congr 2
        rw [mul_assoc, mul_assoc, hQP, mul_one]⟩
      map_add' := fun φ ψ => by ext; simp
      map_smul' := fun c φ => by ext; simp
      left_inv := fun φ => Subtype.ext (LinearMap.ext fun v => by
        simp [Matrix.mulVec_mulVec, hQP])
      right_inv := fun ψ => Subtype.ext (LinearMap.ext fun v => by
        simp [Matrix.mulVec_mulVec, hPQ]) }
  rw [IsDeRham] at hρ ⊢
  rw [← e.finrank_eq, hρ]

/-- **H-32, T23, from Fontaine's theorem on `D_dR(V) = (B_dR ⊗ V)^G`.** Clause (i) is proved
outright; (ii)-(v) are the leaf's clauses applied to the contragredients. -/
theorem t23_of_fontaine (hF : FontaineDRTannakian p) : T23_FontaineClosure p := by
  obtain ⟨hdual, hsub, hsum, htens⟩ := hF
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n ρ ρ' P h
    refine ⟨isDeRham_conj p ρ ρ' P h, isDeRham_conj p ρ' ρ P⁻¹ fun σ => ?_⟩
    rw [h σ, inv_inv]
    group
  · intro n ρ ρ' hc h hdR
    rw [dualRep_of_eq p ρ ρ' h, isDeRham_iff_std, dualRep_dualRep]
    rw [isDeRham_iff_std] at hdR
    refine hdual n (dualRep p ρ) ρ (contRep_dualRep p ρ hc) (fun σ => ?_) hdR
    rw [← map_inv, dualRep_val, inv_inv, Matrix.transpose_transpose]
  · intro a b ρ ρ₁ ρ₂ X hc h hdR
    rw [isDeRham_iff_std] at hdR ⊢
    rw [isDeRham_iff_std]
    refine hsub a b (dualRep p ρ) (dualRep p ρ₁) (dualRep p ρ₂) (fun σ => (X σ⁻¹).transpose)
      (contRep_dualRep p ρ hc) (fun σ => ?_) hdR
    rw [dualRep_val, h σ⁻¹, Matrix.transpose_reindex, Matrix.fromBlocks_transpose,
      Matrix.transpose_zero, dualRep_val, dualRep_val]
  · intro a b ρ ρ₁ ρ₂ hc₁ hc₂ h hd₁ hd₂
    rw [isDeRham_iff_std] at hd₁ hd₂ ⊢
    refine hsum a b (dualRep p ρ) (dualRep p ρ₁) (dualRep p ρ₂) (contRep_dualRep p ρ₁ hc₁)
      (contRep_dualRep p ρ₂ hc₂) (fun σ => ?_) hd₁ hd₂
    rw [dualRep_val, h σ⁻¹, Matrix.transpose_reindex, Matrix.fromBlocks_transpose,
      Matrix.transpose_zero, Matrix.transpose_zero, dualRep_val, dualRep_val]
  · intro a b ρ ρ₁ ρ₂ hc₁ hc₂ h hd₁ hd₂
    rw [isDeRham_iff_std] at hd₁ hd₂ ⊢
    refine htens a b (dualRep p ρ) (dualRep p ρ₁) (dualRep p ρ₂) (contRep_dualRep p ρ₁ hc₁)
      (contRep_dualRep p ρ₂ hc₂) (fun σ => ?_) hd₁ hd₂
    rw [dualRep_val, h σ⁻¹, Matrix.transpose_reindex, dualRep_val, dualRep_val,
      ← Matrix.kroneckerMap_transpose]

/-- The row as the bundle states it: `∀ p, T23_FontaineClosure p`. -/
theorem t23_all_of_fontaine (hF : ∀ (p : ℕ) [Fact p.Prime], FontaineDRTannakian p) :
    ∀ (p : ℕ) [Fact p.Prime], T23_FontaineClosure p :=
  fun p _ => t23_of_fontaine p (hF p)

end T23


/-! ## §8. H-22: R14 with the determinant (`G0Galois.R14Det`)

The row, copied verbatim from `scratch/leaf-fold5/Leaves5.lean` l.35303-35330 (origin
`scratch/g0-mod-galois/part_det.lean`): `toRingEquivQ`, `cycQ`, `R14Det`. It is a composite of
Deligne's theorem (`k ≥ 2`; Shimura's `k = 2` case is contained in it) and Deligne–Serre (`k = 1`).
Here: the weight split (proved), the two printed statements in Diamond–Shurman's form (leaves), and
the conversion from each printed form to the row's form, reduced to three named glue Props. -/

namespace G0Galois

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)

/-- `σ ↦ σ` as ring automorphisms of `ℚ̄`. -/
def toRingEquivQ : ZInQ.Contrib.G9.PkgI4.GQ →* (ZInQ.Contrib.G9.PkgI4.Qbar ≃+* ZInQ.Contrib.G9.PkgI4.Qbar) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The `ℓ`-adic cyclotomic character `χ_ℓ : G_ℚ → ℤ_ℓ^× ⊆ ℚ̄_ℓ^×` (Mathlib's
`cyclotomicCharacter` on `ℚ̄`, as `ZInQ.Contrib.G9.PkgI4.cyc` on `G_{ℚ_p}`). -/
def cycQ (ℓ : ℕ) [Fact ℓ.Prime] : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ :=
  (Units.map ((algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter ZInQ.Contrib.G9.PkgI4.Qbar ℓ).comp toRingEquivQ)

/-- **R14 with its published determinant clause (leaf; Shimura 1971 Thm 7.14 for `k = 2`,
Deligne 1971 for `k ≥ 2`, Deligne–Serre 1974 for `k = 1`; locators UNVERIFIED).** For a normalized
eigenform `g` of weight `k ≥ 1` with nebentypus, there is a semisimple `ρ_g` attached to `g` with
`det ρ_g = ε · χ_ℓ^{k−1}`, `ε` of finite image (the nebentypus as a Galois character). This is
`HSyn.EigenformRepExists` plus the determinant, which the published statements contain. -/
def R14Det : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N k),
    0 < N → 1 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g ∧
      ∃ ε : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ, (Set.range ε).Finite ∧
        ∀ σ, (ρ.mat σ).det = ((ε σ * cycQ ℓ σ ^ (k - 1) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)

end G0Galois

section R14

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)
open Polynomial

/-- The row's conclusion for one eigenform. -/
def R14DetConcl (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    {N : ℕ} {k : ℤ} (g : ZInQ.Contrib.G9.PkgI4.CF N k) : Prop :=
  ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g ∧
    ∃ ε : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ, (Set.range ε).Finite ∧
      ∀ σ, (ρ.mat σ).det = ((ε σ * G0Galois.cycQ ℓ σ ^ (k - 1) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)

/-- R14Det in weight `1` only (Deligne–Serre's range). -/
def R14DetWt1 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N 1),
    0 < N → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ → R14DetConcl ℓ ιC ιL g

/-- R14Det in weights `k ≥ 2` only (Deligne's range). -/
def R14DetWtGe2 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N k),
    0 < N → 2 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ → R14DetConcl ℓ ιC ιL g

/-- **The weight split.** -/
theorem r14Det_of_wt (h1 : R14DetWt1) (h2 : R14DetWtGe2) : G0Galois.R14Det := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · subst hk1
    exact h1 ℓ ιC ιL N χ g hN hg
  · exact h2 ℓ ιC ιL N k χ g hN (by omega) hg

/-- **LEAF (Deligne's theorem, in Diamond–Shurman's form).** Diamond–Shurman, *A First Course in
Modular Forms*, GTM 228 (2005), Thm 9.6.5 (for `k ≥ 2`; from Deligne, Sém. Bourbaki 355 (1969)
[the Bourbaki talk, publ. 1971], and Shimura 1971 Thm 7.14 for `k = 2`; numbering UNVERIFIED): for a
normalized eigenform `f ∈ S_k(N, χ)`, `k ≥ 2`, and `λ ∣ ℓ` in `K_f`, there is a continuous
`ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})`, unramified at every `p ∤ ℓN`, such that for every maximal ideal `𝔭`
of `ℤ̄` over `p` the arithmetic Frobenius `Frob_𝔭` has characteristic polynomial
`x² − a_p(f) x + χ(p) p^{k−1}`. Lean form: coefficients extended along `K_{f,λ} → ℚ̄_ℓ` given by
`ιL ∘ ιC⁻¹` (the place `λ` is the one `ιL ∘ ιC⁻¹` induces), places of `ℚ̄` as valuation subrings,
arithmetic Frobenius as pkg-I4's `IsArithFrob`. The semisimplicity of the row is not part of this
form (Ribet 1977 gives irreducibility; here it is the glue `Semisimplification2`). -/
def DSThm965 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N k),
    0 < N → 2 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : GaloisRep ℓ 2, ∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ →
      ρ.UnramifiedAt p ∧ ∃ α β : ZInQ.Contrib.G9.PkgI4.Qbar, ιC α = ZInQ.Contrib.G9.PkgI4.coeff g p ∧
        ιC β = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) ∧
        ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ), ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p →
          (ρ.mat σ).charpoly = X ^ 2 - C (ιL α) * X + C (ιL β)

/-- **LEAF (Deligne–Serre, in Diamond–Shurman's form).** Deligne–Serre, *Formes modulaires de
poids 1*, Ann. Sci. ÉNS 7 (1974), Thm 4.1; Diamond–Shurman Thm 9.6.6 (numbering UNVERIFIED): for a
normalized eigenform `f ∈ S_1(N, χ)` there is a continuous representation `ρ_f : G_ℚ → GL₂(ℂ)`
(Krull topology on `G_ℚ`), with finite image, unramified at every `p ∤ N`, with
`tr ρ_f(Frob_𝔭) = a_p(f)` and `det ρ_f(Frob_𝔭) = χ(p)`. Lean form: places of `ℚ̄` as valuation
subrings, arithmetic Frobenius as pkg-I4's `IsArithFrob`, the unramified condition pkg-I4's, written
for a `GL₂(ℂ)`-valued homomorphism. -/
def DSThm966 : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (g : ZInQ.Contrib.G9.PkgI4.CF N 1),
    0 < N → ZInQ.Contrib.G9.PkgI4.IsNormalizedEigenform g χ →
    ∃ ρ : ZInQ.Contrib.G9.PkgI4.GQ →* GL (Fin 2) ℂ, Continuous ρ ∧ (Set.range ρ).Finite ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        (∀ v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar, ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ∀ σ ∈ v.inertiaSubgroup ℚ, ρ ((σ : v.decompositionSubgroup ℚ) : ZInQ.Contrib.G9.PkgI4.GQ) = 1) ∧
        ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ), ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p →
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).trace = ZInQ.Contrib.G9.PkgI4.coeff g p ∧
          (ρ σ : Matrix (Fin 2) (Fin 2) ℂ).det = χ (p : ZMod N)

/-- **GLUE (semisimplification in dimension 2; STANDARD, not proved here).** A continuous
`ρ : G_ℚ → GL₂(ℚ̄_ℓ)` has a continuous semisimple `ρ^ss` with the same characteristic polynomials,
unramified wherever `ρ` is. Needs: if `ρ` has an invariant line, conjugate it to upper triangular
form `(χ₁ ∗; 0 χ₂)` and take `diag(χ₁, χ₂)` (continuity of `χᵢ` from the entries; trivial on
inertia where `ρ` is). -/
def Semisimplification2 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ρ : GaloisRep ℓ 2), ∃ ρ' : GaloisRep ℓ 2, ρ'.IsSemisimple ∧
    (∀ σ, (ρ'.mat σ).charpoly = (ρ.mat σ).charpoly) ∧ ∀ p, ρ.UnramifiedAt p → ρ'.UnramifiedAt p

/-- **GLUE (the determinant from its values at Frobenius; not proved here).** If a continuous
`ρ : G_ℚ → GL₂(ℚ̄_ℓ)` has `det ρ(Frob_p) = χ(p) p^{k−1}` at the arithmetic Frobenius elements of
every `p ∤ Nℓ`, then `det ρ = ε χ_ℓ^{k−1}` with `ε` of finite image. Needs: `ε := det ρ · χ_ℓ^{1−k}`
is continuous and equals `χ(Frob_p)` at those Frobenius elements (`χ_ℓ(Frob_p) = p`, Mathlib's
cyclotomic character), so it agrees with the finite-order character `χ ∘ (G_ℚ → (ℤ/N)^×)` on a
dense set (Chebotarev: the kernel's T18, `ZInQKernel/Contrib`), hence everywhere. -/
def DetFromFrobenius : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (ρ : GaloisRep ℓ 2), 0 < N →
    (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧
      ∃ β : ZInQ.Contrib.G9.PkgI4.Qbar, ιC β = χ (p : ZMod N) * (p : ℂ) ^ (k - 1) ∧
        ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ), ZInQ.Contrib.G9.PkgI4.LiesOver v p →
          ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p → (ρ.mat σ).det = ιL β) →
    ∃ ε : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ, (Set.range ε).Finite ∧
      ∀ σ, (ρ.mat σ).det = ((ε σ * G0Galois.cycQ ℓ σ ^ (k - 1) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)

/-- **GLUE (an Artin representation as a semisimple `ℓ`-adic one; not proved here).** From
Deligne–Serre's complex `ρ_f` (finite image), a semisimple `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` attached to `f`
with `det ρ` of finite image. Needs: a finite subgroup of `GL₂(ℂ)` is conjugate into `GL₂(ℚ̄)`
(its character values are algebraic and it is realizable over a cyclotomic field: Brauer), then
`ιL`; semisimplicity by Maschke; `ε := det ρ`, `k − 1 = 0`. -/
def ArtinTransport : Prop := DSThm966 → R14DetWt1

theorem trace_of_charpoly {ℓ : ℕ} [Fact ℓ.Prime] (M : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (a b : PadicAlgCl ℓ) (h : M.charpoly = X ^ 2 - C a * X + C b) : M.trace = a := by
  rw [Matrix.trace_eq_neg_charpoly_coeff, h]
  simp [coeff_X_pow, coeff_C, coeff_X]

theorem det_of_charpoly {ℓ : ℕ} [Fact ℓ.Prime] (M : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ))
    (a b : PadicAlgCl ℓ) (h : M.charpoly = X ^ 2 - C a * X + C b) : M.det = b := by
  rw [Matrix.det_eq_sign_charpoly_coeff, h]
  simp [coeff_X_pow, coeff_C, coeff_X]

/-- **R14Det in weights `≥ 2` from Deligne's theorem (Diamond–Shurman form) and two glue Props.** -/
theorem r14DetWtGe2_of_ds (hD : DSThm965) (hS : Semisimplification2) (hdet : DetFromFrobenius) :
    R14DetWtGe2 := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ0, hρ0⟩ := hD ℓ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, hss, hcp, hun⟩ := hS ℓ ρ0
  have hatt : ρ.AttachedTo ιC ιL g := by
    intro p hp hpN
    obtain ⟨hu, α, β, hα, -, hfrob⟩ := hρ0 p hp hpN
    refine ⟨hun p hu, α, hα, fun v σ hv hσ => ?_⟩
    exact trace_of_charpoly _ _ _ ((hcp σ).trans (hfrob v σ hv hσ))
  obtain ⟨ε, hεfin, hε⟩ := hdet ℓ ιC ιL N k χ ρ hN fun p hp hpN => by
    obtain ⟨hu, α, β, -, hβ, hfrob⟩ := hρ0 p hp hpN
    exact ⟨hun p hu, β, hβ, fun v σ hv hσ =>
      det_of_charpoly _ _ _ ((hcp σ).trans (hfrob v σ hv hσ))⟩
  exact ⟨ρ, hss, hatt, ε, hεfin, hε⟩

/-- **H-22, R14Det, from the two printed theorems and three glue Props.** -/
theorem r14Det_of_ds (hD : DSThm965) (hDS : DSThm966) (hS : Semisimplification2)
    (hdet : DetFromFrobenius) (hA : ArtinTransport) : G0Galois.R14Det :=
  r14Det_of_wt (hA hDS) (r14DetWtGe2_of_ds hD hS hdet)

end R14


/-! ## §9. H-9: `ZInQ.Contrib.G9.PkgI4.PanBerger` (Pan + Berger)

Imported from `ZInQKernel/Contrib/G9/I4Layer.lean` (`PanBerger = PanFor LocalIsDeRham`). Pan's
Theorem 1.0.4 and Berger's Théorème 0.7 both involve "potentially semistable", which needs `B_st`
(hence `B_cris`); Mathlib has `BDeRhamPlus`/`BDeRham` but neither `B_cris` nor `B_st`. So neither
theorem can be a leaf over genuine definitions today. What is proved: for **every** predicate
`IsPst`, Pan's template and Berger's template compose to `PanBerger`; the composite becomes a
theorem from two published-form leaves as soon as `IsPst` is instantiated by a genuine
potentially-semistable predicate (built on a genuine `B_st`). -/

section PanBergerSec

/-- **H-9 from the two templates (any `IsPst`).** The continuity Berger needs is that of
`ρ|_{G_{ℚ_p}}` (Mathlib's `Field.absoluteGaloisGroup.map` is continuous). -/
theorem panBerger_of_templates (IsPst : LocalPred) (hP : PanFor IsPst) (hB : BergerDR IsPst) :
    PanBerger := by
  intro p _ hp ρ hirr hfr hdr hodd hdist
  exact hP p hp ρ hirr hfr (hB p 2 (ρ.restrictLocal p) (continuous_restrictLocal p ρ) hdr) hodd hdist

end PanBergerSec

/-! ## §10. H-10: `ZInQ.Contrib.G9.PkgI4.EigenformHT` (Kato, after dualization)

Imported from `I4Layer.lean`. Kato's theorem (Astérisque 295 (2004), §§9.2-9.4, (9.2.2)) is about
Kato's `V_{F_λ}(f)`, a quotient of the étale cohomology of a modular curve with coefficients (or of
a Kuga–Sato variety), defined only for newforms; étale cohomology is not in Mathlib, so the printed
statement cannot be a leaf today. Proved here: the reduction from eigenforms of any level to
newforms (`eigenformHT_of_new`), from the kernel's leaf `NewformOfEigenform` (I4-L5), R14
(`EigenformRepExists`, which `R14Det` implies) and two standard glue Props (Chebotarev with
Brauer–Nesbitt; invariance of Hodge–Tate weights under conjugation, g12-det's `HTConj`). What is
left, `EigenformHTNew`, is Kato's theorem for newforms transported to every semisimple `ρ`
attached to `f` and dualized. -/

section EigenformHTSec

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)

/-- `r` and `ρ'` are conjugate by a fixed matrix (g12-det's `G0Galois.IsConj`, verbatim). -/
def IsConj {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (r ρ' : GaloisRep ℓ n) : Prop :=
  ∃ P : GL (Fin n) (PadicAlgCl ℓ), ∀ σ, r.toHom σ = P * ρ'.toHom σ * P⁻¹

/-- **GLUE `HTConj` (g12-det's `G0Galois.HTConj`, verbatim; about the definition
`LocalHasHTWeights`).** Hodge–Tate weights are invariant under conjugation. Proved below
(`htConj_proof`). -/
def HTConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (r ρ' : GaloisRep ℓ n) (S : Multiset ℤ),
    IsConj r ρ' → r.HasHTWeightsAtSelf ℓ S → ρ'.HasHTWeightsAtSelf ℓ S

/-- **GLUE (Chebotarev density with Brauer–Nesbitt; STANDARD, not proved here).** Two semisimple
`ρ, ρ' : G_ℚ → GL₂(ℚ̄_ℓ)`, unramified and with equal traces at the arithmetic Frobenius elements of
all primes outside a finite set, are conjugate. Needs: Frobenius elements are dense (Chebotarev,
the kernel's T18 `ZInQKernel/Contrib`), continuity of `tr`, and Brauer–Nesbitt for semisimple
representations of a group over a field of characteristic `0` (T19). -/
def AttachedConj : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ρ ρ' : GaloisRep ℓ 2) (S : Finset ℕ),
    ρ.IsSemisimple → ρ'.IsSemisimple →
    (∀ p : ℕ, p.Prime → p ∉ S → ρ.UnramifiedAt p ∧ ρ'.UnramifiedAt p ∧
      ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (σ : ZInQ.Contrib.G9.PkgI4.GQ), ZInQ.Contrib.G9.PkgI4.LiesOver v p →
        ZInQ.Contrib.G9.PkgI4.IsArithFrob σ v p → (ρ.mat σ).trace = (ρ'.mat σ).trace) →
    IsConj ρ ρ'

/-- **The newform case of R13 (GLUE: Kato's theorem for newforms, transported and dualized).**
`EigenformHT` restricted to newforms. Needs, beyond Kato's printed statement (de Rham at `ℓ` with
Hodge–Tate weights `0, k − 1` for `V_{F_λ}(f)`, cohomological normalization): the identification of
any semisimple `ρ` attached to `f` (arithmetic Frobenius, trace `a_p`) with `V_{F_λ}(f)^∨`
(Chebotarev and Brauer–Nesbitt), and the negation of Hodge–Tate weights under duals. Not a leaf:
`V_{F_λ}(f)` is not definable in Mathlib today. -/
def EigenformHTNew : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : ZInQ.Contrib.G9.PkgI4.CF N k) (ρ : GaloisRep ℓ 2),
    0 < N → 2 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

/-- **H-10 reduced to the newform case.** -/
theorem eigenformHT_of_new (hNew : EigenformHTNew) (hL5 : NewformOfEigenform)
    (hR : EigenformRepExists) (hAC : AttachedConj) (hHC : HTConj) : EigenformHT := by
  intro ℓ _ ιC ιL M k χ g ρ hM hk hg hss hatt
  obtain ⟨N, χ', f, hN, hNM, hf, hcoef⟩ := hL5 M k χ g hM hg
  obtain ⟨ρf, hssf, hattf⟩ := hR ℓ ιC ιL N k χ' f hN (by omega) hf.1
  have hHT := hNew ℓ ιC ιL N k χ' f ρf hN hk hf hssf hattf
  -- `ρf` and `ρ` agree at Frobenius outside the primes dividing `M ℓ`
  have hconj : IsConj ρf ρ := by
    refine hAC ℓ ρf ρ (M * ℓ).primeFactors hssf hss fun p hp hpS => ?_
    have hpM : ¬ p ∣ M * ℓ := by
      intro h
      exact hpS (Nat.mem_primeFactors.mpr ⟨hp, h, by
        exact Nat.mul_ne_zero (by omega) (Fact.out : ℓ.Prime).ne_zero⟩)
    have hpN : ¬ p ∣ N * ℓ := fun h => hpM (by
      rcases (Nat.Prime.dvd_mul hp).mp h with h1 | h1
      · exact Dvd.dvd.mul_right (h1.trans hNM) ℓ
      · exact Dvd.dvd.mul_left h1 M)
    obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpM
    obtain ⟨huf, αf, hαf, htrf⟩ := hattf p hp hpN
    have hpM' : ¬ p ∣ M := fun h => hpM (Dvd.dvd.mul_right h ℓ)
    have heq : αf = α := by
      apply ιC.toRingHom.injective
      change ιC αf = ιC α
      rw [hαf, hα, hcoef p hp hpM']
    refine ⟨huf, hu, fun v σ hv hσ => ?_⟩
    rw [htrf v σ hv hσ, htr v σ hv hσ, heq]
  exact hHC ℓ 2 ρf ρ _ hconj hHT

end EigenformHTSec

/-! ## §11. H-51: `G0Galois.SenTwist`

The row, copied verbatim (Leaves5.lean l.50905-50907 `IsTwist`, l.50952-50958 `SenTwist`). Sen's
theory (the Sen operator) is not in Mathlib, so Sen 1980 cannot be a leaf over genuine definitions.
The argument through Tate's theorems (§1) instead: `ρ` and `ψ ⊗ ρ` Hodge–Tate give
`ℂ_p(ψ) ⊗ ⊕ ℂ_p(−w) ≅ ⊕ ℂ_p(−w')`, so `ℂ_p(ψ) ≅ ℂ_p(s)` with `s ∈ ℤ` (a nonzero map between
one-dimensional twists), and twisting by `ℂ_p(s)` shifts all weights by `−s`. It is split into three
glue Props; the third (independence of the coefficient field) is proved below. -/

namespace G0Galois

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)

/-- `ρ'` is the twist `ψ ⊗ ρ`: `ρ'(σ) = ψ(σ) ρ(σ)`. -/
def IsTwist {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} (ρ' : GaloisRep ℓ n) (ψ : GaloisChar ℓ)
    (ρ : GaloisRep ℓ n) : Prop :=
  ∀ σ, ρ'.mat σ = (ψ.toHom σ : PadicAlgCl ℓ) • ρ.mat σ

/-- **Sen weights of a twist (LEAF; Sen, *Continuous cohomology and p-adic Galois
representations*, Invent. Math. 62 (1980), §2 Thm 4 and Cor. (Hodge–Tate iff the Sen operator `Θ`
is semisimple with integer eigenvalues, the Hodge–Tate weights), with
`Θ_{ψ⊗V} = Θ_ψ + Θ_V` (Sen 1980 §2; Fontaine–Ouyang, *Theory of p-adic Galois representations*,
§2.4-2.5); numbering UNVERIFIED).** If `ρ` and `ρ' = ψ ⊗ ρ` (restricted to `G_{ℚ_p}`) are both
Hodge–Tate, with weight multisets `S`, `S'` of full size `n`, then `S' = S + s` for an integer
`s`. Consequence of the published theorems: the Sen operators satisfy `Θ_{ρ'} = Θ_ρ + s_ψ`, both
are semisimple with eigenvalue multisets `S`, `S'`, so `S' = S + s_ψ` in `ℂ_p`, and `s_ψ ∈ ℤ`
when `n ≥ 1` (for `n = 0`, `s = 0`). (Full size is needed: `HasHTWeights S` with `card S < n`
holds for non-Hodge–Tate `ρ`, and then the statement fails.) -/
def SenTwist : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ ρ' : GaloisRep p n) (ψ : GaloisChar p)
    (S S' : Multiset ℤ),
    IsTwist ρ' ψ ρ → Multiset.card S = n → Multiset.card S' = n →
    ρ.HasHTWeightsAtSelf p S → ρ'.HasHTWeightsAtSelf p S' →
    ∃ s : ℤ, S' = S.map (· + s)

end G0Galois

section SenTwistSec

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)

/-- `ψ|_{G_{ℚ_p}} ≅ ℂ_p(s)`: some `c ≠ 0` in `ℂ_p` with `σ(c) = ψ(σ) χ(σ)^{−s} c`, i.e. the basis
`e = c f` of `ℂ_p(ψ)` in terms of a basis `f` of `ℂ_p(s)`. -/
def IsHTCharWt {p : ℕ} [Fact p.Prime] (ψ : GaloisChar p) (s : ℤ) : Prop :=
  ∃ c : ℂ_[p], c ≠ 0 ∧ ∀ σ : GQp p,
    cpAct p σ c = cycPow p σ (-s) • (((ψ.toHom (decomp p σ) : PadicAlgCl p)) : ℂ_[p]) * c

/-- **GLUE S1 (a twist between Hodge–Tate representations is by a Hodge–Tate character; not proved
here).** Needs: the Hodge–Tate decomposition criterion (`V` Hodge–Tate iff
`⊕_i ℂ_p(−i) ⊗ (ℂ_p(i) ⊗ V)^G ≅ ℂ_p ⊗ V`; Serre 1967 / Tate 1967 §3.3 / Brinon–Conrad §2.2-2.4,
built on Tate's theorems of §1), applied embedding by embedding of the coefficient field, and
"a nonzero `G`-map `ℂ_p(ψ) → ℂ_p(j)` is an isomorphism". -/
def HTCharOfTwist : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ ρ' : GaloisRep p n) (ψ : GaloisChar p) (S S' : Multiset ℤ),
    0 < n → G0Galois.IsTwist ρ' ψ ρ → Multiset.card S = n → Multiset.card S' = n →
    ρ.HasHTWeightsAtSelf p S → ρ'.HasHTWeightsAtSelf p S' → ∃ s : ℤ, IsHTCharWt ψ s

/-- **GLUE S2 (twisting by `ℂ_p(s)` shifts the weights by `−s`; not proved here).** Needs: on the
component of `Hom_{ℚ_p}(Eⁿ, ℂ_p)` for each embedding `τ : E → ℂ_p` (`E`-semilinear maps), `φ ↦ c_τ φ`
identifies `H_i(ψ ⊗ ρ)` with `H_{i−s}(ρ)`, where `c_τ = g(c)` for `g ∈ G_{ℚ_p}` with `g|_E = τ`
(`ψ` is a character, so `ψ(g⁻¹σg) = ψ(σ)`). -/
def HTTwistShift : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ ρ' : GaloisRep p n) (ψ : GaloisChar p) (S : Multiset ℤ)
    (s : ℤ), G0Galois.IsTwist ρ' ψ ρ → IsHTCharWt ψ s → ρ.HasHTWeightsAtSelf p S →
    ρ'.HasHTWeightsAtSelf p (S.map (· - s))

/-- **GLUE S3 (the weight multiset does not depend on the coefficient field).** Proved below
(`htWeightsUnique_proof`). -/
def HTWeightsUnique : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (ρ : GQp p →* GL (Fin n) (PadicAlgCl p)) (S S' : Multiset ℤ),
    LocalHasHTWeights p ρ S → LocalHasHTWeights p ρ S' → S = S'

/-- **H-51 from the three glue Props.** -/
theorem senTwist_of_glue (h1 : HTCharOfTwist) (h2 : HTTwistShift) (h3 : HTWeightsUnique) :
    G0Galois.SenTwist := by
  intro p _ n ρ ρ' ψ S S' htw hS hS' hρ hρ'
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, ?_⟩
    rw [Multiset.card_eq_zero] at hS hS'
    simp [hS, hS']
  obtain ⟨s, hs⟩ := h1 p n ρ ρ' ψ S S' hn htw hS hS' hρ hρ'
  have h := h2 p n ρ ρ' ψ S s htw hs hρ
  refine ⟨-s, ?_⟩
  have := h3 p n (ρ'.restrictLocal p) _ _ hρ' h
  rw [this]
  congr 1

end SenTwistSec


/-! ## §12. Glue proved: Hodge–Tate weights do not depend on the coefficient field

`LocalHasHTWeights p ρ S` asks for *some* finite `E ⊆ ℚ̄_p` and an `E`-valued lift. Here: enlarging
`E` does not change `htMult` (`htMult_eq_of_le`); hence the weight multiset is unique
(`htWeightsUnique_proof`, glue S3 of §11) and invariant under conjugation by `GL_n(ℚ̄_p)`
(`htConj_proof`, g12-det's glue `HTConj`). -/

section CoefIndep

theorem finrank_fun_eq {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (d : ℕ) :
    finrank K (Fin d → M) = d * finrank K M := by
  rw [finrank, rank_fun_eq_lift_mul, Cardinal.toNat_mul, Cardinal.toNat_natCast,
    Cardinal.toNat_lift, Fintype.card_fin]
  rfl

theorem finrank_Dsp_pi' {K G B V : Type*} [Field K] [Group G] [AddCommGroup B] [Module K B]
    [AddCommGroup V] [Module K V] (act : G → B →ₗ[K] B) (ρ : G → V →ₗ[K] V) (S : Set G) (d : ℕ) :
    finrank K (Dsp act (piRep ρ (Fin d)) S) = d * finrank K (Dsp act ρ S) := by
  rw [(DspPiEquiv act ρ S (Fin d)).finrank_eq, finrank_fun_eq]

variable {n : ℕ}

/-- The swap `(Fin n → Fin d → E) ≃ (Fin d → Fin n → E)`. -/
def swapEquiv (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] (n d : ℕ) :
    (Fin n → Fin d → M) ≃ₗ[R] (Fin d → Fin n → M) where
  toFun x j i := x i j
  invFun x i j := x j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Core count (abstract fields).** For `E'/E` finite and matrices `M g` over `E`, the
`K`-dimension of the equivariant maps out of `E'ⁿ` (action `M g` read in `E'`) is `[E':E]` times the
one out of `Eⁿ`. -/
theorem dsp_finrank_extend {K E E' G B : Type*} [Field K] [Field E] [Field E'] [Algebra K E]
    [Algebra K E'] [Algebra E E'] [IsScalarTower K E E'] [FiniteDimensional E E'] [Group G]
    [AddCommGroup B] [Module K B] (act : G → B →ₗ[K] B) (M : G → Matrix (Fin n) (Fin n) E)
    (S : Set G) :
    finrank K (Dsp act (fun g => (Matrix.mulVecLin ((M g).map (algebraMap E E'))).restrictScalars K) S)
      = finrank E E' * finrank K (Dsp act (fun g => (Matrix.mulVecLin (M g)).restrictScalars K) S) := by
  classical
  set d := finrank E E'
  let b : Basis (Fin d) E E' := Module.finBasis E E'
  let ΨE : (Fin n → E') ≃ₗ[E] (Fin n → Fin d → E) := LinearEquiv.piCongrRight fun _ => b.equivFun
  let Ψ : (Fin n → E') ≃ₗ[K] (Fin d → Fin n → E) :=
    (ΨE.restrictScalars K).trans (swapEquiv K E n d)
  have hΨ : ∀ y j i, Ψ y j i = b.repr (y i) j := fun _ _ _ => rfl
  have hequiv : ∀ g y, Ψ ((Matrix.mulVecLin ((M g).map (algebraMap E E'))).restrictScalars K y) =
      piRep (fun g => (Matrix.mulVecLin (M g)).restrictScalars K) (Fin d) g (Ψ y) := by
    intro g y
    funext j i
    rw [hΨ, piRep_apply]
    simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.map_apply, ← Algebra.smul_def, map_sum, map_smul, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rfl
  rw [finrank_Dsp_congr act _ (piRep (fun g => (Matrix.mulVecLin (M g)).restrictScalars K) (Fin d))
    S Ψ hequiv, finrank_Dsp_pi']

/-- **Enlarging the coefficient field does not change `htMult`.** -/
theorem htMult_eq_of_le {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)} (hle : E ≤ E')
    [FiniteDimensional ℚ_[p] E] [FiniteDimensional ℚ_[p] E']
    (ρE : GQp p →* GL (Fin n) E) (ρE' : GQp p →* GL (Fin n) E')
    (hent : ∀ σ i j, (((ρE' σ : Matrix (Fin n) (Fin n) E') i j : E') : PadicAlgCl p) =
      (((ρE σ : Matrix (Fin n) (Fin n) E) i j : E) : PadicAlgCl p)) (w : ℤ) :
    htMult p ρE' w = htMult p ρE w := by
  classical
  letI alg : Algebra E E' := (IntermediateField.inclusion hle).toAlgebra
  letI mod : Module E E' := alg.toModule
  haveI fr : Module.Free E E' := Module.Free.of_divisionRing E E'
  have hinc : ∀ a : E, ((algebraMap E E' a : E') : PadicAlgCl p) = (a : PadicAlgCl p) :=
    fun _ => rfl
  haveI tow : IsScalarTower ℚ_[p] E E' := IsScalarTower.of_algebraMap_eq fun c => by
    apply Subtype.ext
    rw [hinc]
    rfl
  haveI fd : FiniteDimensional E E' := FiniteDimensional.right ℚ_[p] E E'
  have hmat : ∀ σ, (ρE' σ : Matrix (Fin n) (Fin n) E') =
      (ρE σ : Matrix (Fin n) (Fin n) E).map (algebraMap E E') := fun σ =>
    Matrix.ext fun i k => Subtype.ext ((hent σ i k).trans (hinc _).symm)
  have hX : ∀ i : ℤ, finrank ℚ_[p] (htSpace p ρE' i) =
      finrank E E' * finrank ℚ_[p] (htSpace p ρE i) := by
    intro i
    rw [htSpace_eq_DspMat, htSpace_eq_DspMat]
    have h1 : (matRep p ρE' : GQp p → (Fin n → E') →ₗ[ℚ_[p]] (Fin n → E')) =
        fun σ => (Matrix.mulVecLin ((ρE σ : Matrix (Fin n) (Fin n) E).map
          (algebraMap E E'))).restrictScalars ℚ_[p] := by
      funext σ; rw [← hmat]; rfl
    have h2 : (matRep p ρE : GQp p → (Fin n → E) →ₗ[ℚ_[p]] (Fin n → E)) =
        fun σ => (Matrix.mulVecLin (ρE σ : Matrix (Fin n) (Fin n) E)).restrictScalars ℚ_[p] := rfl
    rw [h1, h2]
    exact dsp_finrank_extend (htAct p i) (fun σ => (ρE σ : Matrix (Fin n) (Fin n) E)) Set.univ
  have hdeg : finrank ℚ_[p] E' = finrank ℚ_[p] E * finrank E E' :=
    (Module.finrank_mul_finrank ℚ_[p] E E').symm
  have hd : 0 < finrank E E' := Module.finrank_pos
  rw [htMult, htMult, hX, hdeg, mul_comm (finrank ℚ_[p] E) (finrank E E'),
    Nat.mul_div_mul_left _ _ hd]

/-- Two finite coefficient fields give the same multiplicities. -/
theorem htMult_eq_of_lifts (ρ : GQp p →* GL (Fin n) (PadicAlgCl p))
    {E₁ E₂ : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E₁]
    [FiniteDimensional ℚ_[p] E₂] (ρ₁ : GQp p →* GL (Fin n) E₁) (ρ₂ : GQp p →* GL (Fin n) E₂)
    (h₁ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E₁ (PadicAlgCl p)) (ρ₁ σ) = ρ σ)
    (h₂ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E₂ (PadicAlgCl p)) (ρ₂ σ) = ρ σ)
    (w : ℤ) : htMult p ρ₁ w = htMult p ρ₂ w := by
  have hent : ∀ {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρE : GQp p →* GL (Fin n) E),
      (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (ρE σ) = ρ σ) →
      ∀ σ i j, (((ρE σ : Matrix (Fin n) (Fin n) E) i j : E) : PadicAlgCl p) =
        (ρ σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j := by
    intro E ρE h σ i j
    rw [← h σ]
    rfl
  let E₃ := E₁ ⊔ E₂
  have hmem : ∀ σ i j, (ρ σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ E₃ := by
    intro σ i j
    rw [← hent ρ₁ h₁]
    exact (le_sup_left : E₁ ≤ E₃) (((ρ₁ σ : Matrix (Fin n) (Fin n) E₁) i j).2)
  let ρ₃ := liftGL E₃ ρ hmem
  have e1 := htMult_eq_of_le p (le_sup_left : E₁ ≤ E₃) ρ₁ ρ₃
    (fun σ i j => (liftGL_coe E₃ ρ hmem σ i j).trans (hent ρ₁ h₁ σ i j).symm) w
  have e2 := htMult_eq_of_le p (le_sup_right : E₂ ≤ E₃) ρ₂ ρ₃
    (fun σ i j => (liftGL_coe E₃ ρ hmem σ i j).trans (hent ρ₂ h₂ σ i j).symm) w
  rw [← e1, ← e2]

/-- **Glue S3 of §11, proved.** -/
theorem htWeightsUnique_proof : HTWeightsUnique := by
  intro p _ n ρ S S' ⟨E₁, h₁fd, ρ₁, h₁, hw₁⟩ ⟨E₂, h₂fd, ρ₂, h₂, hw₂⟩
  ext w
  rw [← hw₁ w, ← hw₂ w]
  exact htMult_eq_of_lifts p ρ ρ₁ ρ₂ h₁ h₂ w

/-- Conjugation by a matrix over `E` does not change `htMult`. -/
theorem htMult_conj {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]
    (ρ ρ' : GQp p →* GL (Fin n) E) (Pm Qm : Matrix (Fin n) (Fin n) E) (hQP : Qm * Pm = 1)
    (hPQ : Pm * Qm = 1)
    (h : ∀ σ, (ρ σ : Matrix (Fin n) (Fin n) E) = Pm * (ρ' σ : Matrix (Fin n) (Fin n) E) * Qm)
    (w : ℤ) : htMult p ρ w = htMult p ρ' w := by
  let e : (Fin n → E) ≃ₗ[ℚ_[p]] (Fin n → E) :=
    { toFun := fun v => Qm.mulVec v
      invFun := fun v => Pm.mulVec v
      map_add' := fun v v' => Matrix.mulVec_add _ _ _
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        rw [show c • v = algebraMap ℚ_[p] E c • v from (algebraMap_smul E c v).symm,
          Matrix.mulVec_smul, algebraMap_smul]
      left_inv := fun v => by
        simp only [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
      right_inv := fun v => by
        simp only [Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec] }
  have he : ∀ σ v, e (matRep p ρ σ v) = matRep p ρ' σ (e v) := by
    intro σ v
    change Qm.mulVec ((ρ σ : Matrix (Fin n) (Fin n) E).mulVec v) =
      (ρ' σ : Matrix (Fin n) (Fin n) E).mulVec (Qm.mulVec v)
    rw [h σ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc, hQP, one_mul]
  rw [htMult, htMult, htSpace_eq_DspMat, htSpace_eq_DspMat,
    finrank_Dsp_congr (htAct p (-w)) (matRep p ρ) (matRep p ρ') Set.univ e he]

end CoefIndep

section HTConjSec

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)

/-- **g12-det's glue `HTConj`, proved.** -/
theorem htConj_proof : HTConj := by
  intro p _ n r ρ' S ⟨P, hP⟩ ⟨E, hEfd, rE, hrE, hw⟩
  classical
  let Pm := (P : Matrix (Fin n) (Fin n) (PadicAlgCl p))
  let Qm := ((P⁻¹ : GL (Fin n) (PadicAlgCl p)) : Matrix (Fin n) (Fin n) (PadicAlgCl p))
  let X : Set (PadicAlgCl p) := (Set.range fun ij : Fin n × Fin n => Pm ij.1 ij.2) ∪
    Set.range fun ij : Fin n × Fin n => Qm ij.1 ij.2
  haveI : Finite X := (Set.finite_range _ |>.union (Set.finite_range _)).to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] X) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let E₃ := E ⊔ IntermediateField.adjoin ℚ_[p] X
  have hPmem : ∀ i j, Pm i j ∈ E₃ := fun i j =>
    (le_sup_right : _ ≤ E₃) (IntermediateField.subset_adjoin _ _ (Or.inl ⟨(i, j), rfl⟩))
  have hQmem : ∀ i j, Qm i j ∈ E₃ := fun i j =>
    (le_sup_right : _ ≤ E₃) (IntermediateField.subset_adjoin _ _ (Or.inr ⟨(i, j), rfl⟩))
  have hrent : ∀ σ i j, (((rE σ : Matrix (Fin n) (Fin n) E) i j : E) : PadicAlgCl p) =
      (r.restrictLocal p σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j := by
    intro σ i j; rw [← hrE σ]; rfl
  have hrmem : ∀ σ i j, (r.restrictLocal p σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ E₃ := by
    intro σ i j
    rw [← hrent]
    exact (le_sup_left : E ≤ E₃) (((rE σ : Matrix (Fin n) (Fin n) E) i j).2)
  have hρ'eq : ∀ σ, (ρ'.restrictLocal p σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) =
      Qm * (r.restrictLocal p σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) * Pm := by
    intro σ
    have h1 : r.restrictLocal p σ = P * ρ'.restrictLocal p σ * P⁻¹ := hP _
    have h2 : ρ'.restrictLocal p σ = P⁻¹ * r.restrictLocal p σ * P := by
      rw [h1]; group
    rw [h2]; rfl
  have hρ'mem : ∀ σ i j, (ρ'.restrictLocal p σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ E₃ := by
    intro σ i j
    rw [hρ'eq]
    simp only [Matrix.mul_apply]
    refine E₃.sum_mem fun k _ => E₃.mul_mem ?_ (hPmem k j)
    exact E₃.sum_mem fun m _ => E₃.mul_mem (hQmem i m) (hrmem σ m k)
  let r₃ := liftGL E₃ (r.restrictLocal p) hrmem
  let ρ₃ := liftGL E₃ (ρ'.restrictLocal p) hρ'mem
  let Pm₃ : Matrix (Fin n) (Fin n) E₃ := fun i j => ⟨Pm i j, hPmem i j⟩
  let Qm₃ : Matrix (Fin n) (Fin n) E₃ := fun i j => ⟨Qm i j, hQmem i j⟩
  have hinj : Function.Injective (fun A : Matrix (Fin n) (Fin n) E₃ => A.map (algebraMap E₃ (PadicAlgCl p))) :=
    Matrix.map_injective (algebraMap E₃ (PadicAlgCl p)).injective
  have hPm₃ : Pm₃.map (algebraMap E₃ (PadicAlgCl p)) = Pm := by ext; rfl
  have hQm₃ : Qm₃.map (algebraMap E₃ (PadicAlgCl p)) = Qm := by ext; rfl
  have hQP : Qm₃ * Pm₃ = 1 := hinj (by
    simp only [Matrix.map_mul, hPm₃, hQm₃, Matrix.map_one _ (map_zero _) (map_one _)]
    simp [Qm, Pm])
  have hPQ : Pm₃ * Qm₃ = 1 := hinj (by
    simp only [Matrix.map_mul, hPm₃, hQm₃, Matrix.map_one _ (map_zero _) (map_one _)]
    simp [Qm, Pm])
  have hr₃map : ∀ σ, (r₃ σ : Matrix (Fin n) (Fin n) E₃).map (algebraMap E₃ (PadicAlgCl p)) =
      (r.restrictLocal p σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) := fun σ => by ext; rfl
  have hρ₃map : ∀ σ, (ρ₃ σ : Matrix (Fin n) (Fin n) E₃).map (algebraMap E₃ (PadicAlgCl p)) =
      (ρ'.restrictLocal p σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) := fun σ => by ext; rfl
  have hconj : ∀ σ, (ρ₃ σ : Matrix (Fin n) (Fin n) E₃) = Qm₃ * (r₃ σ : Matrix (Fin n) (Fin n) E₃) * Pm₃ :=
    fun σ => hinj (by simp only [Matrix.map_mul, hρ₃map, hr₃map, hPm₃, hQm₃, hρ'eq])
  refine ⟨E₃, inferInstance, ρ₃, fun σ => liftGL_map E₃ _ hρ'mem σ, fun w => ?_⟩
  rw [htMult_conj p ρ₃ r₃ Qm₃ Pm₃ hPQ hQP hconj w,
    htMult_eq_of_le p (le_sup_left : E ≤ E₃) rE r₃
      (fun σ i j => (liftGL_coe E₃ _ hrmem σ i j).trans (hrent σ i j).symm) w]
  exact hw w

end HTConjSec


/-! ## §14. Glue proved: `Semisimplification2` -/

section SemisimpSec

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar)
open Polynomial

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem charpoly_fin_two' (M : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) :
    M.charpoly = X ^ 2 - C M.trace * X + C M.det := by
  rw [Matrix.charpoly, Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _
    (show (0 : Fin 2) ≠ 1 by decide), Matrix.diagonal_apply_ne _ (show (1 : Fin 2) ≠ 0 by decide),
    RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  simp only [map_sub, map_add, map_mul]
  ring

/-- `σ ↦ diag(a σ, d σ)`. -/
def diagHom (a d : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ) : ZInQ.Contrib.G9.PkgI4.GQ →* GL (Fin 2) (PadicAlgCl ℓ) where
  toFun σ := ⟨!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)],
    !![(((a σ)⁻¹ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ), 0; 0, (((d σ)⁻¹ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)],
    by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩
  map_one' := Units.ext (by simp [Matrix.one_fin_two])
  map_mul' σ τ := Units.ext (by simp [Matrix.mul_fin_two])

theorem diagHom_val (a d : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    ((diagHom a d σ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
      !![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)] := rfl

/-- A diagonal representation is semisimple. -/
theorem isSemisimple_diag (a d : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ)
    (W : Submodule (PadicAlgCl ℓ) (Fin 2 → PadicAlgCl ℓ))
    (hW : ∀ σ, W.map (Matrix.toLin' (!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)])) ≤ W) :
    ∃ W', IsCompl W W' ∧ ∀ σ,
      W'.map (Matrix.toLin' (!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)])) ≤ W' := by
  classical
  -- the coordinate lines
  let e0 : Fin 2 → PadicAlgCl ℓ := ![1, 0]
  let e1 : Fin 2 → PadicAlgCl ℓ := ![0, 1]
  have hdiag : ∀ σ (x : Fin 2 → PadicAlgCl ℓ),
      Matrix.toLin' (!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)]) x =
        ![(a σ : PadicAlgCl ℓ) * x 0, (d σ : PadicAlgCl ℓ) * x 1] := by
    intro σ x; ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hline0 : ∀ σ, (PadicAlgCl ℓ ∙ e0).map (Matrix.toLin'
      (!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)])) ≤ (PadicAlgCl ℓ ∙ e0) := by
    intro σ
    rw [Submodule.map_le_iff_le_comap, Submodule.span_singleton_le_iff_mem, Submodule.mem_comap,
      hdiag, Submodule.mem_span_singleton]
    exact ⟨(a σ : PadicAlgCl ℓ), by ext i; fin_cases i <;> simp [e0]⟩
  have hline1 : ∀ σ, (PadicAlgCl ℓ ∙ e1).map (Matrix.toLin'
      (!![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)])) ≤ (PadicAlgCl ℓ ∙ e1) := by
    intro σ
    rw [Submodule.map_le_iff_le_comap, Submodule.span_singleton_le_iff_mem, Submodule.mem_comap,
      hdiag, Submodule.mem_span_singleton]
    exact ⟨(d σ : PadicAlgCl ℓ), by ext i; fin_cases i <;> simp [e1]⟩
  have hc01 : IsCompl (PadicAlgCl ℓ ∙ e0) (PadicAlgCl ℓ ∙ e1) := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      obtain ⟨⟨c, rfl⟩, ⟨c', hc'⟩⟩ := (Submodule.mem_inf.mp hx).imp Submodule.mem_span_singleton.mp
        Submodule.mem_span_singleton.mp
      have h0 := congrFun hc' 0
      have h1 := congrFun hc' 1
      simp [e0, e1] at h0 h1
      rw [Submodule.mem_bot]
      ext i; fin_cases i <;> simp [e0, ← h0]
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have : x = x 0 • e0 + x 1 • e1 := by ext i; fin_cases i <;> simp [e0, e1]
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self _)))
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  by_cases hsc : ∀ σ, (a σ : PadicAlgCl ℓ) = d σ
  · -- scalar: every subspace is invariant
    obtain ⟨W', hW'⟩ := Submodule.exists_isCompl W
    refine ⟨W', hW', fun σ => ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hdiag, ← hsc σ]
    have : ![(a σ : PadicAlgCl ℓ) * x 0, (a σ : PadicAlgCl ℓ) * x 1] = (a σ : PadicAlgCl ℓ) • x := by
      ext i; fin_cases i <;> simp
    rw [this]
    exact W'.smul_mem _ hx
  push_neg at hsc
  obtain ⟨σ₀, hσ₀⟩ := hsc
  by_cases htop : W = ⊤
  · exact ⟨⊥, by rw [htop]; exact isCompl_top_bot, fun σ => by simp⟩
  by_cases hbot : W = ⊥
  · exact ⟨⊤, by rw [hbot]; exact isCompl_bot_top, fun σ => le_top⟩
  -- every vector of `W` lies on a coordinate line
  have key : ∀ z ∈ W, z 0 = 0 ∨ z 1 = 0 := by
    intro z hz
    by_contra h
    push_neg at h
    apply htop
    have hz' : ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1] ∈ W := by
      rw [← hdiag]; exact hW σ₀ ⟨z, hz, rfl⟩
    have hsub : (a σ₀ : PadicAlgCl ℓ) ≠ d σ₀ := hσ₀
    have he0 : e0 ∈ W := by
      have hm : (d σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1] ∈ W :=
        W.sub_mem (W.smul_mem _ hz) hz'
      have hne : ((d σ₀ : PadicAlgCl ℓ) - a σ₀) * z 0 ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr (Ne.symm hsub)) h.1
      have hv : (d σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1] =
          (((d σ₀ : PadicAlgCl ℓ) - a σ₀) * z 0) • e0 := by
        ext i; fin_cases i
        · simp [e0, Matrix.vecHead]; ring
        · simp [e0, Matrix.vecHead, Matrix.vecTail]
      have : e0 = (((d σ₀ : PadicAlgCl ℓ) - a σ₀) * z 0)⁻¹ •
          ((d σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1]) := by
        rw [hv, inv_smul_smul₀ hne]
      rw [this]; exact W.smul_mem _ hm
    have he1 : e1 ∈ W := by
      have hm : (a σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1] ∈ W :=
        W.sub_mem (W.smul_mem _ hz) hz'
      have hne : ((a σ₀ : PadicAlgCl ℓ) - d σ₀) * z 1 ≠ 0 :=
        mul_ne_zero (sub_ne_zero.mpr hsub) h.2
      have hv : (a σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1] =
          (((a σ₀ : PadicAlgCl ℓ) - d σ₀) * z 1) • e1 := by
        ext i; fin_cases i
        · simp [e1, Matrix.vecHead]
        · simp [e1, Matrix.vecHead, Matrix.vecTail]; ring
      have : e1 = (((a σ₀ : PadicAlgCl ℓ) - d σ₀) * z 1)⁻¹ •
          ((a σ₀ : PadicAlgCl ℓ) • z - ![(a σ₀ : PadicAlgCl ℓ) * z 0, (d σ₀ : PadicAlgCl ℓ) * z 1]) := by
        rw [hv, inv_smul_smul₀ hne]
      rw [this]; exact W.smul_mem _ hm
    rw [eq_top_iff]
    intro x _
    have : x = x 0 • e0 + x 1 • e1 := by ext i; fin_cases i <;> simp [e0, e1]
    rw [this]
    exact W.add_mem (W.smul_mem _ he0) (W.smul_mem _ he1)
  by_cases h0 : ∀ x ∈ W, x 1 = 0
  · have hle : W ≤ PadicAlgCl ℓ ∙ e0 := by
      intro x hx
      rw [Submodule.mem_span_singleton]
      exact ⟨x 0, by ext i; fin_cases i <;> simp [e0, h0 x hx]⟩
    have hge : PadicAlgCl ℓ ∙ e0 ≤ W := by
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
      have hx00 : x 0 ≠ 0 := by
        intro h; apply hx0; ext i; fin_cases i <;> simp [h, h0 x hx]
      rw [Submodule.span_singleton_le_iff_mem]
      have : e0 = (x 0)⁻¹ • x := by ext i; fin_cases i <;> simp [e0, h0 x hx, hx00]
      rw [this]; exact W.smul_mem _ hx
    have hWe : W = PadicAlgCl ℓ ∙ e0 := le_antisymm hle hge
    exact ⟨PadicAlgCl ℓ ∙ e1, hWe ▸ hc01, hline1⟩
  push_neg at h0
  obtain ⟨x, hx, hx1⟩ := h0
  have hx0 : x 0 = 0 := (key x hx).resolve_right hx1
  by_cases h1 : ∀ y ∈ W, y 0 = 0
  · have hle : W ≤ PadicAlgCl ℓ ∙ e1 := by
      intro y hy
      rw [Submodule.mem_span_singleton]
      exact ⟨y 1, by ext i; fin_cases i <;> simp [e1, h1 y hy]⟩
    have hge : PadicAlgCl ℓ ∙ e1 ≤ W := by
      rw [Submodule.span_singleton_le_iff_mem]
      have : e1 = (x 1)⁻¹ • x := by ext i; fin_cases i <;> simp [e1, hx0, hx1]
      rw [this]; exact W.smul_mem _ hx
    have hWe : W = PadicAlgCl ℓ ∙ e1 := le_antisymm hle hge
    exact ⟨PadicAlgCl ℓ ∙ e0, hWe ▸ hc01.symm, hline0⟩
  push_neg at h1
  obtain ⟨y, hy, hy0⟩ := h1
  have hy1 : y 1 = 0 := (key y hy).resolve_left hy0
  rcases key (x + y) (W.add_mem hx hy) with h | h
  · exact absurd (by simpa [hx0] using h) hy0
  · exact absurd (by simpa [hy1] using h) hx1

theorem mulVec_e0 (M : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) (i : Fin 2) :
    (M.mulVec ![1, 0]) i = M i 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **`Semisimplification2`, proved.** If `ρ` is not semisimple it has an invariant line; in a
basis through it `ρ` is upper triangular `(a ∗; 0 d)`, and `diag(a, d)` is the semisimplification. -/
theorem semisimplification2_proof : Semisimplification2 := by
  intro ℓ _ ρ
  classical
  by_cases hss : ρ.IsSemisimple
  · exact ⟨ρ, hss, fun _ => rfl, fun _ h => h⟩
  -- an invariant subspace without invariant complement
  have hss' := hss
  simp only [GaloisRep.IsSemisimple, not_forall, not_exists, not_and] at hss'
  obtain ⟨W, hW, hno⟩ := hss'
  have hWbot : W ≠ ⊥ := by
    rintro rfl
    obtain ⟨σ, hσ⟩ := hno ⊤ isCompl_bot_top
    exact hσ le_top
  have hWtop : W ≠ ⊤ := by
    rintro rfl
    obtain ⟨σ, hσ⟩ := hno ⊥ isCompl_top_bot
    exact hσ (by simp)
  obtain ⟨w, hwW, hw⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
  have hfin : Module.finrank (PadicAlgCl ℓ) W = 1 := by
    have h2 : Module.finrank (PadicAlgCl ℓ) W ≤ 2 := by
      have := Submodule.finrank_le W
      simpa using this
    have h0 : Module.finrank (PadicAlgCl ℓ) W ≠ 0 := by
      intro h; exact hWbot (Submodule.finrank_eq_zero.mp h)
    have h2' : Module.finrank (PadicAlgCl ℓ) W ≠ 2 := by
      intro h; apply hWtop
      apply Submodule.eq_top_of_finrank_eq
      simp [h]
    omega
  have hmul : ∀ v ∈ W, ∃ c : PadicAlgCl ℓ, c • w = v := by
    intro v hv
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hwW⟩ : W)
      (fun h => hw (congrArg Subtype.val h))).mp hfin ⟨v, hv⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have heig : ∀ σ, ∃ c : PadicAlgCl ℓ, (ρ.mat σ).mulVec w = c • w := by
    intro σ
    obtain ⟨c, hc⟩ := hmul _ (hW σ ⟨w, hwW, rfl⟩)
    exact ⟨c, by rw [hc, Matrix.toLin'_apply]⟩
  -- a basis through `w`
  let u : Fin 2 → PadicAlgCl ℓ := if w 0 ≠ 0 then ![0, 1] else ![1, 0]
  let P : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) := !![w 0, u 0; w 1, u 1]
  have hdet : P.det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    by_cases h0 : w 0 ≠ 0
    · simp [u, h0]
    · have hw0 : w 0 = 0 := not_not.mp h0
      have h1 : w 1 ≠ 0 := by
        intro h1; apply hw; ext i; fin_cases i <;> simp [hw0, h1]
      simp [u, hw0, h1]
  let Pu : GL (Fin 2) (PadicAlgCl ℓ) := Matrix.nonsingInvUnit P (Ne.isUnit hdet)
  let Q : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) := ((Pu⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix _ _ _)
  have hQP : Q * P = 1 := by
    change (Pu⁻¹).val * Pu.val = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPQ : P * Q = 1 := by
    change Pu.val * (Pu⁻¹).val = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  let T : ZInQ.Contrib.G9.PkgI4.GQ → Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ) := fun σ => Q * ρ.mat σ * P
  have hPe0 : P.mulVec ![1, 0] = w := by
    ext i; rw [mulVec_e0]; fin_cases i <;> simp [P]
  have hT10 : ∀ σ, T σ 1 0 = 0 := by
    intro σ
    obtain ⟨c, hc⟩ := heig σ
    have h1 : (T σ).mulVec ![1, 0] = c • ![1, 0] := by
      simp only [T, ← Matrix.mulVec_mulVec, hPe0, hc, Matrix.mulVec_smul]
      rw [← hPe0, Matrix.mulVec_mulVec, hQP, Matrix.one_mulVec]
    have := congrFun h1 1
    rw [mulVec_e0] at this
    simpa using this
  have hmatmul : ∀ σ τ, ρ.mat (σ * τ) = ρ.mat σ * ρ.mat τ := by
    intro σ τ; simp [GaloisRep.mat]
  have hTmul : ∀ σ τ, T (σ * τ) = T σ * T τ := by
    intro σ τ
    simp only [T, hmatmul]
    rw [show Q * ρ.mat σ * P * (Q * ρ.mat τ * P) = Q * ρ.mat σ * (P * Q) * ρ.mat τ * P by
      simp only [mul_assoc], hPQ, mul_one]
    simp only [mul_assoc]
  have hT1 : T 1 = 1 := by simp [T, GaloisRep.mat, hQP]
  have hdetT : ∀ σ, (T σ).det = T σ 0 0 * T σ 1 1 := by
    intro σ; rw [Matrix.det_fin_two, hT10]; ring
  have hdetT' : ∀ σ, (T σ).det ≠ 0 := by
    intro σ
    simp only [T, Matrix.det_mul]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hdet
    · intro h
      have := congrArg Matrix.det hQP
      rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
      exact zero_ne_one this
    · exact (Matrix.isUnit_iff_isUnit_det _).mp (ρ.toHom σ).isUnit |>.ne_zero
  have ha0 : ∀ σ, T σ 0 0 ≠ 0 := fun σ h => hdetT' σ (by rw [hdetT, h, zero_mul])
  have hd0 : ∀ σ, T σ 1 1 ≠ 0 := fun σ h => hdetT' σ (by rw [hdetT, h, mul_zero])
  let a : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ :=
    { toFun := fun σ => Units.mk0 (T σ 0 0) (ha0 σ)
      map_one' := Units.ext (by simp [hT1])
      map_mul' := fun σ τ => Units.ext (by
        simp only [Units.val_mk0, Units.val_mul, hTmul, Matrix.mul_apply, Fin.sum_univ_two, hT10]
        ring) }
  let d : ZInQ.Contrib.G9.PkgI4.GQ →* (PadicAlgCl ℓ)ˣ :=
    { toFun := fun σ => Units.mk0 (T σ 1 1) (hd0 σ)
      map_one' := Units.ext (by simp [hT1])
      map_mul' := fun σ τ => Units.ext (by
        simp only [Units.val_mk0, Units.val_mul, hTmul, Matrix.mul_apply, Fin.sum_univ_two, hT10]
        ring) }
  have hTc : Continuous T :=
    (continuous_const.matrix_mul (Units.continuous_val.comp ρ.continuous_toHom)).matrix_mul
      continuous_const
  have hac : Continuous fun σ => (a σ : PadicAlgCl ℓ) := hTc.matrix_elem 0 0
  have hdc : Continuous fun σ => (d σ : PadicAlgCl ℓ) := hTc.matrix_elem 1 1
  have hdiagc : ∀ (f g : ZInQ.Contrib.G9.PkgI4.GQ → PadicAlgCl ℓ), Continuous f → Continuous g →
      Continuous fun σ => !![f σ, 0; 0, g σ] := by
    intro f g hf hg
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j
    · simpa using hf
    · simpa using continuous_const
    · simpa using continuous_const
    · simpa using hg
  have hcont : Continuous (diagHom a d) := by
    rw [Units.continuous_iff]
    refine ⟨hdiagc _ _ hac hdc, ?_⟩
    have : (fun σ => (((diagHom a d σ)⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)))
        = fun σ => !![(a σ⁻¹ : PadicAlgCl ℓ), 0; 0, (d σ⁻¹ : PadicAlgCl ℓ)] := by
      funext σ; rw [← map_inv]; rfl
    rw [this]
    exact hdiagc _ _ (hac.comp continuous_inv) (hdc.comp continuous_inv)
  let ρ' : GaloisRep ℓ 2 := ⟨diagHom a d, hcont⟩
  have hρ'mat : ∀ σ, ρ'.mat σ = !![(a σ : PadicAlgCl ℓ), 0; 0, (d σ : PadicAlgCl ℓ)] := fun σ => rfl
  have hρT : ∀ σ, ρ.mat σ = P * T σ * Q := by
    intro σ
    simp only [T]
    rw [show P * (Q * ρ.mat σ * P) * Q = (P * Q) * ρ.mat σ * (P * Q) by simp only [mul_assoc],
      hPQ, one_mul, mul_one]
  refine ⟨ρ', fun W' hW' => ?_, fun σ => ?_, fun p hu => ?_⟩
  · simp only [hρ'mat] at hW' ⊢
    exact isSemisimple_diag a d W' hW'
  · rw [charpoly_fin_two', charpoly_fin_two', hρ'mat, hρT]
    have htr : (P * T σ * Q).trace = (T σ).trace := by
      rw [Matrix.trace_mul_comm, ← mul_assoc, hQP, one_mul]
    have hdt : (P * T σ * Q).det = (T σ).det := by
      rw [Matrix.det_mul, Matrix.det_mul, mul_comm (P.det), mul_assoc, ← Matrix.det_mul, hPQ,
        Matrix.det_one, mul_one]
    rw [htr, hdt, hdetT]
    simp [Matrix.trace_fin_two, Matrix.det_fin_two, a, d]
  · intro v hv σ hσ
    have h1 := hu v hv σ hσ
    apply Units.ext
    change !![(a _ : PadicAlgCl ℓ), 0; 0, (d _ : PadicAlgCl ℓ)] = 1
    have hTσ : T ((σ : v.decompositionSubgroup ℚ) : ZInQ.Contrib.G9.PkgI4.GQ) = 1 := by
      simp only [T, GaloisRep.mat, h1, Units.val_one, mul_one, hQP]
    rw [Matrix.one_fin_two]
    simp [a, d, hTσ]

end SemisimpSec


/-! ## §15. H-8 with the de Rham leaf in tensor form

`DeRhamH1AbVar` states "`V_p(A)^∨` is de Rham" with pkg-I4's Hom form of `D_dR(V^∨)`. Here the
leaf `DeRhamH1AbVarT` states it with the printed definition, `D_dR(W) = (B_dR ⊗ W)^{G_F}` for
`W = Module.Dual ℚ_p V_p(A)` with the contragredient action (Mathlib's `Representation.dual`), and
`isDeRhamOver_iff_tensor_dual` proves the two forms equivalent for finite-dimensional `V`
(`B_dR ⊗ V^∨ ≅ Hom(V, B_dR)`, Mathlib's `dualTensorHomEquiv`); `V_p(A)` is finite-dimensional by the
Hodge–Tate decomposition. -/

section DeRhamTensor

variable {F : Type*} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

/-- `D_dR,F(W) = (B_dR ⊗_{ℚ_p} W)^{G_F}`. -/
def ddrTensorOver {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]
    (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) :
    Submodule ℚ_[p] (BdR p ⊗[ℚ_[p]] W) where
  carrier := {x | ∀ σ, TensorProduct.map (drAct p (gfToGqp p F σ)) (ρW σ) x = x}
  zero_mem' σ := map_zero _
  add_mem' ha hb σ := by rw [map_add, ha σ, hb σ]
  smul_mem' c x hx σ := by rw [map_smul, hx σ]

/-- **`W` is de Rham over `F`** in the printed sense: `dim_F (B_dR ⊗ W)^{G_F} = dim W`. -/
def IsDeRhamTensorOver {W : Type*} [AddCommGroup W] [Module ℚ_[p] W]
    (ρW : Representation ℚ_[p] (Field.absoluteGaloisGroup F) W) : Prop :=
  Module.finrank ℚ_[p] (ddrTensorOver p ρW) = Module.finrank ℚ_[p] F * Module.finrank ℚ_[p] W

/-- **LEAF (the de Rham comparison for `H¹` of an abelian variety, printed `D_dR`).** As
`DeRhamH1AbVar`, with `H¹_ét(A_{F̄}, ℚ_p)` replaced by `Hom_{ℚ_p}(V_p(A), ℚ_p)` with the
contragredient action (the standard identification; Milne, *Abelian varieties*, Thm 15.1(a),
UNVERIFIED) and `D_dR` in its printed form `(B_dR ⊗ W)^{G_F}`. Faltings 1989; Tsuji 1999; Scholze,
Forum Math. Pi 1 (2013), Cor. 1.8; Fontaine 1982 for abelian varieties. -/
def DeRhamH1AbVarT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F), IsDeRhamTensorOver p (A.galRep p).dual

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- `B_dR ⊗ V^∨ ≅ Hom(V, B_dR)`, `b ⊗ f ↦ (v ↦ f(v) b)`. -/
noncomputable def tensorDualEquiv [FiniteDimensional ℚ_[p] V] :
    (BdR p ⊗[ℚ_[p]] Module.Dual ℚ_[p] V) ≃ₗ[ℚ_[p]] (V →ₗ[ℚ_[p]] BdR p) :=
  (TensorProduct.comm ℚ_[p] (BdR p) (Module.Dual ℚ_[p] V)).trans
    (dualTensorHomEquiv ℚ_[p] V (BdR p))

theorem tensorDualEquiv_tmul [FiniteDimensional ℚ_[p] V] (b : BdR p) (f : Module.Dual ℚ_[p] V)
    (v : V) : tensorDualEquiv p (b ⊗ₜ f) v = f v • b := rfl

/-- The tensor action corresponds to `φ ↦ σ ∘ φ ∘ ρ(σ)⁻¹`. -/
theorem tensorDualEquiv_map [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (σ : Field.absoluteGaloisGroup F)
    (x : BdR p ⊗[ℚ_[p]] Module.Dual ℚ_[p] V) (v : V) :
    tensorDualEquiv p (TensorProduct.map (drAct p (gfToGqp p F σ)) (ρ.dual σ) x) v =
      drAct p (gfToGqp p F σ) (tensorDualEquiv p x (ρ σ⁻¹ v)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b f =>
    rw [TensorProduct.map_tmul, tensorDualEquiv_tmul, tensorDualEquiv_tmul, map_smul,
      Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  | add x y hx hy =>
    rw [map_add, map_add, LinearMap.add_apply, hx, hy, map_add, LinearMap.add_apply, map_add]

/-- **The two forms of "`V^∨` is de Rham" agree** (finite-dimensional `V`). -/
theorem isDeRhamOver_iff_tensor_dual [FiniteDimensional ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    IsDeRhamTensorOver p ρ.dual ↔ IsDeRhamOver p ρ := by
  have hmap : Submodule.map (tensorDualEquiv p).toLinearMap (ddrTensorOver p ρ.dual) =
      ddrSpaceOver p ρ := by
    ext φ
    constructor
    · rintro ⟨x, hx, rfl⟩ σ w
      have h := congrArg (fun y => tensorDualEquiv p y (ρ σ w)) (hx σ)
      rw [tensorDualEquiv_map, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply] at h
      exact h.symm
    · intro hφ
      refine ⟨(tensorDualEquiv p).symm φ, fun σ => ?_, by simp⟩
      apply (tensorDualEquiv p).injective
      refine LinearMap.ext fun v => ?_
      rw [tensorDualEquiv_map, LinearEquiv.apply_symm_apply]
      have := hφ σ (ρ σ⁻¹ v)
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
      rw [this]
      rfl
  rw [IsDeRhamTensorOver, IsDeRhamOver, ← hmap, LinearEquiv.finrank_map_eq,
    Subspace.dual_finrank_eq]

/-- `V_p(A)` is finite-dimensional, from the Hodge–Tate decomposition. -/
theorem finiteDimensional_of_decomp {g : ℕ}
    (e : ℂ_[p] ⊗[ℚ_[p]] V ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin g → ℂ_[p])) :
    FiniteDimensional ℚ_[p] V := by
  have h1 := e.lift_rank_eq
  have h2 : Cardinal.lift (Module.rank ℂ_[p] ((Fin g → ℂ_[p]) × (Fin g → ℂ_[p]))) <
      Cardinal.aleph0 := Cardinal.lift_lt_aleph0.mpr (Module.rank_lt_aleph0 _ _)
  rw [← h1, Module.rank_baseChange, Cardinal.lift_lift, Cardinal.lift_lt_aleph0] at h2
  exact Module.rank_lt_aleph0_iff.mp h2

end DeRhamTensor

/-- **H-8 with the tensor-form de Rham leaf.** -/
theorem deRhamComparisonHT_of_leavesT (hHT : HodgeTateDecompAbVar) (hT : TateTwistInvariants)
    (hA : AxSenTate) (hdR : DeRhamH1AbVarT) : ZInQ.Contrib.R10.DeRhamComparisonHT := by
  refine deRhamComparisonHT_of_leaves hHT hT hA fun p _ F _ _ _ A => ?_
  obtain ⟨g, hg⟩ := dim_finite_I4 A
  obtain ⟨e, -⟩ := hHT p F A g hg
  haveI := finiteDimensional_of_decomp p e
  exact (isDeRhamOver_iff_tensor_dual p (A.galRep p)).mp (hdR p F A)


/-! ## §16. H-51 proved: `SenTwist` from Tate's two theorems

Over `G_E` (`E ⊆ ℚ̄_p` finite Galois, containing the entries of `ρ`, `ρ'` and the values of `ψ`),
`E`-linear Hodge–Tate data in coordinates: `Y_i(ρ) = {y ∈ ℂ_pⁿ | ρ(σ)ᵀ y = χ(σ)^i σ(y), σ ∈ G_E}`.
Steps: (T) Tate–Sen independence: `E`-bases of the `Y_j` together are `ℂ_p`-independent (Tate's two
theorems); (B) `dim_ℚp Y_i(ρ) = dim_ℚp H_i(ρ)` (Dedekind's lemma and Galois descent), so the `Y_j(ρ')`
span `ℂ_pⁿ`; (X) a nonzero `y ∈ Y_{i₀}(ρ)`, expanded in that basis, gives `β ∈ ℂ_p^×` with
`σ(β) = ψ(σ)⁻¹ χ(σ)^s β`; (M) multiplication by `β⁻¹` maps `Y_i(ρ)` onto `Y_{i+s}(ρ')`. -/

section SenSec

variable {n : ℕ}

theorem cycPow_add (σ : GQp p) (a b : ℤ) : cycPow p σ (a + b) = cycPow p σ a * cycPow p σ b := by
  simp only [cycPow, zpow_add, Units.val_mul, PadicInt.coe_mul]

theorem cycPow_neg_mul (σ : GQp p) (a : ℤ) : cycPow p σ (-a) * cycPow p σ a = 1 := by
  rw [← cycPow_add, neg_add_cancel, cycPow_zero]

/-- `σ` on `ℂ_pⁿ`, coordinatewise. -/
def vAct (σ : GQp p) (y : Fin n → ℂ_[p]) : Fin n → ℂ_[p] := fun k => cpAct p σ (y k)

theorem vAct_add (σ : GQp p) (y z : Fin n → ℂ_[p]) : vAct p σ (y + z) = vAct p σ y + vAct p σ z := by
  ext k; simp [vAct]

theorem vAct_smul (σ : GQp p) (c : ℂ_[p]) (y : Fin n → ℂ_[p]) :
    vAct p σ (c • y) = cpAct p σ c • vAct p σ y := by
  ext k; simp [vAct]

theorem vAct_sum {ι : Type*} (s : Finset ι) (σ : GQp p) (f : ι → Fin n → ℂ_[p]) :
    vAct p σ (∑ k ∈ s, f k) = ∑ k ∈ s, vAct p σ (f k) := by
  ext m; simp [vAct, Finset.sum_apply, map_sum]

theorem vAct_zero (σ : GQp p) : vAct p σ (0 : Fin n → ℂ_[p]) = 0 := by ext; simp [vAct]

/-- A matrix over `E` read in `ℂ_p`. -/
def matC {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (M : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) ℂ_[p] :=
  M.map (algebraMap E ℂ_[p])

/-- `Y_i(ρ)` over `G_K`: `{y ∈ ℂ_pⁿ | ρ(σ)ᵀ y = χ(σ)^i σ(y), σ ∈ G_K}`, a `K`-subspace. -/
def Ysp {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E) (i : ℤ)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Submodule K (Fin n → ℂ_[p]) where
  carrier := {y | ∀ σ ∈ K.fixingSubgroup,
    (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec y = cycPow p σ i • vAct p σ y}
  zero_mem' σ _ := by simp [vAct_zero]
  add_mem' {y z} hy hz σ hσ := by
    rw [Matrix.mulVec_add, hy σ hσ, hz σ hσ, vAct_add, smul_add]
  smul_mem' a y hy σ hσ := by
    have ha : cpAct p σ (algebraMap K ℂ_[p] a) = algebraMap K ℂ_[p] a := by
      rw [IsScalarTower.algebraMap_apply K (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq, cpAct_coe]
      congr 1
      exact hσ a
    rw [← algebraMap_smul (A := ℂ_[p]) a y, Matrix.mulVec_smul, hy σ hσ, vAct_smul, ha, smul_comm]

theorem matC_mul_inv {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E)
    (σ : GQp p) : matC p (ρ σ : Matrix (Fin n) (Fin n) E) * matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E) = 1 := by
  rw [matC, matC, ← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one,
    Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem matC_inv_mul {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E)
    (σ : GQp p) : matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E) * matC p (ρ σ : Matrix (Fin n) (Fin n) E) = 1 := by
  rw [matC, matC, ← Matrix.map_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
    Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem transpose_mulVec_eq_zero {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) {x : Fin n → ℂ_[p]}
    (h : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec x = 0) : x = 0 := by
  have : (matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E)).transpose.mulVec
      ((matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, matC_mul_inv, Matrix.transpose_one,
      Matrix.one_mulVec]
  rw [← this, h, Matrix.mulVec_zero]

theorem vAct_of_mem {E K : IntermediateField ℚ_[p] (PadicAlgCl p)} {ρ : GQp p →* GL (Fin n) E}
    {i : ℤ} {y : Fin n → ℂ_[p]} (hy : y ∈ Ysp p ρ i K) {σ : GQp p} (hσ : σ ∈ K.fixingSubgroup) :
    vAct p σ y = cycPow p σ (-i) • (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec y := by
  rw [hy σ hσ, smul_smul, cycPow_neg_mul, one_smul]

/-- **(T) Tate–Sen independence.** -/
theorem Ysp_linearIndependent (hT : TateTwistInvariants) (hA : AxSenTate)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι → ℤ) (y : ι → (Fin n → ℂ_[p]))
    (hy : ∀ k, y k ∈ Ysp p ρ (j k) K)
    (hind : ∀ (j₀ : ℤ) (a : ι → K), (∀ k, j k ≠ j₀ → a k = 0) → ∑ k, a k • y k = 0 →
      ∀ k, a k = 0) :
    LinearIndependent ℂ_[p] y := by
  rw [Fintype.linearIndependent_iff]
  suffices H : ∀ (s : Finset ι) (b : ι → ℂ_[p]), (∀ k ∉ s, b k = 0) → ∑ k, b k • y k = 0 →
      ∀ k, b k = 0 from fun b hb => H Finset.univ b (by simp) hb
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro b hbs hb
  by_contra hne
  push_neg at hne
  obtain ⟨k₀, hk₀⟩ := hne
  have hk₀s : k₀ ∈ s := by
    by_contra h; exact hk₀ (hbs k₀ h)
  let b' : ι → ℂ_[p] := fun k => (b k₀)⁻¹ * b k
  have hb' : ∑ k, b' k • y k = 0 := by
    simp only [b', mul_smul, ← Finset.smul_sum, hb, smul_zero]
  have hb'k₀ : b' k₀ = 1 := inv_mul_cancel₀ hk₀
  have hb's : ∀ k ∉ s, b' k = 0 := fun k hk => by simp [b', hbs k hk]
  have key : ∀ σ ∈ K.fixingSubgroup, ∀ k,
      b' k = cycPow p σ (j k₀ - j k) • cpAct p σ (b' k) := by
    intro σ hσ
    let d : ι → ℂ_[p] := fun k => b' k - cycPow p σ (j k₀ - j k) • cpAct p σ (b' k)
    have h1 : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec
        (∑ k, (cycPow p σ (-j k) • cpAct p σ (b' k)) • y k) = 0 := by
      have h0 := congrArg (vAct p σ) hb'
      rw [vAct_sum, vAct_zero] at h0
      rw [Matrix.mulVec_sum]
      rw [← h0]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [vAct_smul, vAct_of_mem p (hy k) hσ, Matrix.mulVec_smul, smul_assoc, smul_comm]
    have h2 := transpose_mulVec_eq_zero p ρ σ h1
    have hd : ∑ k, d k • y k = 0 := by
      have h3 : ∑ k, (cycPow p σ (j k₀ - j k) • cpAct p σ (b' k)) • y k = 0 := by
        have e : ∀ k, (cycPow p σ (j k₀ - j k) • cpAct p σ (b' k)) • y k =
            cycPow p σ (j k₀) • ((cycPow p σ (-j k) • cpAct p σ (b' k)) • y k) := by
          intro k
          rw [← smul_assoc, smul_smul, ← cycPow_add, sub_eq_add_neg]
        simp only [e]
        rw [← Finset.smul_sum, h2, smul_zero]
      simp only [d, sub_smul, Finset.sum_sub_distrib, hb', h3, sub_zero]
    have hds : ∀ k ∉ s.erase k₀, d k = 0 := by
      intro k hk
      by_cases hkk : k = k₀
      · subst hkk
        simp [d, hb'k₀, cycPow_zero]
      · have : k ∉ s := fun h => hk (Finset.mem_erase.mpr ⟨hkk, h⟩)
        simp [d, hb's k this]
    have := ih (s.erase k₀) (Finset.erase_ssubset hk₀s) d hds hd
    intro k
    exact sub_eq_zero.mp (this k)
  have hzero : ∀ k, j k ≠ j k₀ → b' k = 0 := by
    intro k hk
    refine hT p K (j k₀ - j k) (by omega) (b' k) fun σ hσ => (key σ hσ k).symm
  have hKval : ∀ k, j k = j k₀ → ∃ a : K, b' k = algebraMap K ℂ_[p] a := by
    intro k hk
    obtain ⟨a, ha⟩ := hA p K (b' k) fun σ hσ => by
      have := key σ hσ k
      rw [hk, sub_self, cycPow_zero, one_smul] at this
      exact this.symm
    refine ⟨a, ?_⟩
    rw [ha, IsScalarTower.algebraMap_apply K (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]
    rfl
  classical
  let a : ι → K := fun k => if h : j k = j k₀ then (hKval k h).choose else 0
  have ha : ∀ k, j k = j k₀ → b' k = algebraMap K ℂ_[p] (a k) := by
    intro k hk
    simp only [a, dif_pos hk]
    exact (hKval k hk).choose_spec
  have hsum : ∑ k, a k • y k = 0 := by
    rw [← hb']
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : j k = j k₀
    · rw [ha k h, algebraMap_smul]
    · simp only [a, dif_neg h, zero_smul]
      rw [hzero k h, zero_smul]
  have h0 := hind (j k₀) a (fun k hk => by simp [a, dif_neg hk]) hsum k₀
  have h1 := ha k₀ rfl
  rw [h0, map_zero, hb'k₀] at h1
  exact one_ne_zero h1

end SenSec

section SenBridge

variable {n : ℕ} (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]

theorem eC_eq (e : E) : algebraMap E ℂ_[p] e = (((e : PadicAlgCl p)) : ℂ_[p]) := by
  rw [IsScalarTower.algebraMap_apply E (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq]
  rfl

theorem eC_smul (c : ℚ_[p]) (e : E) : algebraMap E ℂ_[p] (c • e) = c • algebraMap E ℂ_[p] e := by
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]

variable [IsGalois ℚ_[p] E]

theorem cpAct_eC (g : GQp p) (e : E) : cpAct p g (algebraMap E ℂ_[p] e) =
    algebraMap E ℂ_[p] (AlgEquiv.restrictNormalHom E g e) := by
  rw [eC_eq, eC_eq, cpAct_coe]
  congr 1
  exact (AlgEquiv.restrictNormal_commutes g E e).symm

/-- `ρ^τ`: `τ` applied to the entries. -/
def rhoTau (τ : E ≃ₐ[ℚ_[p]] E) (ρ : GQp p →* GL (Fin n) E) : GQp p →* GL (Fin n) E :=
  (Matrix.GeneralLinearGroup.map (τ : E →+* E)).comp ρ

theorem matC_rhoTau (τ : E ≃ₐ[ℚ_[p]] E) (ρ : GQp p →* GL (Fin n) E) (σ : GQp p) (a b : Fin n) :
    matC p (rhoTau p E τ ρ σ : Matrix (Fin n) (Fin n) E) a b =
      algebraMap E ℂ_[p] (τ ((ρ σ : Matrix (Fin n) (Fin n) E) a b)) := rfl

/-- **Dedekind coordinates**: `y ↦ (v ↦ Σ_τ Σ_k y_τ,k · τ(v_k))`. -/
def LamC : ((E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) →ₗ[ℂ_[p]] ((Fin n → E) →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun y :=
    { toFun := fun v => ∑ τ, ∑ k, y τ k * algebraMap E ℂ_[p] (τ (v k))
      map_add' := fun v w => by
        simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        have hxs : ∀ (x : E ≃ₐ[ℚ_[p]] E) (e : E), x (c • e) = c • x e := fun x e => by
          rw [Algebra.smul_def, map_mul, AlgEquiv.commutes, ← Algebra.smul_def]
        simp only [Pi.smul_apply, hxs, eC_smul, mul_smul_comm, Finset.smul_sum,
          RingHom.id_apply] }
  map_add' y z := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, add_mul, Finset.sum_add_distrib,
      LinearMap.add_apply]
  map_smul' c y := by
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul, mul_assoc,
      Finset.mul_sum, LinearMap.smul_apply, RingHom.id_apply]

theorem LamC_apply (y : (E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) (v : Fin n → E) :
    LamC p E y v = ∑ τ, ∑ k, y τ k * algebraMap E ℂ_[p] (τ (v k)) := rfl

theorem LamC_injective : Function.Injective (LamC p E (n := n)) := by
  classical
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  rw [LinearMap.mem_ker] at hy
  rw [Submodule.mem_bot]
  -- Dedekind's independence of the characters `e ↦ τ(e)`
  let χτ : (E ≃ₐ[ℚ_[p]] E) → (E →* ℂ_[p]) := fun τ =>
    (algebraMap E ℂ_[p]).toMonoidHom.comp (τ : E →+* E).toMonoidHom
  have hχinj : Function.Injective χτ := by
    intro τ₁ τ₂ h
    exact AlgEquiv.ext fun e => (algebraMap E ℂ_[p]).injective
      (congrArg (fun f : E →* ℂ_[p] => f e) h)
  have hind := (linearIndependent_monoidHom E ℂ_[p]).comp χτ hχinj
  funext τ k
  have hk : ∀ e : E, ∑ τ, y τ k * algebraMap E ℂ_[p] (τ e) = 0 := by
    intro e
    have := LinearMap.congr_fun hy (Pi.single k e)
    rw [LamC_apply, LinearMap.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_eq_single k]
    · simp
    · intro m _ hm; simp [Pi.single_apply, hm]
    · intro h; exact absurd (Finset.mem_univ k) h
  have := Fintype.linearIndependent_iff.mp hind (fun τ => y τ k) (by
    funext e
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    exact hk e)
  exact this τ

theorem LamC_surjective : Function.Surjective (LamC p E (n := n)) := by
  have h1 : Module.finrank ℂ_[p] ((E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) =
      Module.finrank ℂ_[p] ((Fin n → E) →ₗ[ℚ_[p]] ℂ_[p]) := by
    rw [Module.finrank_linearMap, Module.finrank_pi_fintype, Module.finrank_self, mul_one,
      Module.finrank_pi_fintype]
    simp only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Module.finrank_self, mul_one]
    rw [Module.finrank_pi_fintype]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, mul_comm]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h1).mp (LamC_injective p E)

end SenBridge

section SenBridge2

variable {n : ℕ} (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
  [IsGalois ℚ_[p] E]

theorem mem_fixing_iff_ker (σ : GQp p) :
    σ ∈ E.fixingSubgroup ↔ σ ∈ (AlgEquiv.restrictNormalHom (F := ℚ_[p]) (K₁ := PadicAlgCl p) E).ker := by
  rw [IntermediateField.restrictNormalHom_ker]

theorem cpAct_eC_fix {σ : GQp p} (hσ : σ ∈ E.fixingSubgroup) (e : E) :
    cpAct p σ (algebraMap E ℂ_[p] e) = algebraMap E ℂ_[p] e := by
  rw [eC_eq, cpAct_coe]
  congr 1
  exact hσ e

/-- (I1) -/
theorem LamC_matRep (ρ : GQp p →* GL (Fin n) E) (σ : GQp p)
    (y : (E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) (v : Fin n → E) :
    LamC p E y (matRep p ρ σ v) =
      LamC p E (fun τ => (matC p (rhoTau p E τ ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec (y τ)) v := by
  rw [LamC_apply, LamC_apply, matRep_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, matC_rhoTau, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- (I2) -/
theorem LamC_htAct (i : ℤ) {σ : GQp p} (hσ : σ ∈ E.fixingSubgroup)
    (y : (E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) (v : Fin n → E) :
    htAct p i σ (LamC p E y v) = LamC p E (fun τ => cycPow p σ i • vAct p σ (y τ)) v := by
  rw [htAct_apply, LamC_apply, LamC_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, cpAct_eC_fix p E hσ, Pi.smul_apply, smul_mul_assoc]
  rfl

/-- **Membership in Dedekind coordinates.** -/
theorem LamC_mem_iff (ρ : GQp p →* GL (Fin n) E) (i : ℤ)
    (y : (E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) :
    LamC p E y ∈ Dsp (htAct p i) (matRep p ρ)
        ((AlgEquiv.restrictNormalHom (F := ℚ_[p]) (K₁ := PadicAlgCl p) E).ker : Set (GQp p)) ↔
      ∀ τ, y τ ∈ Ysp p (rhoTau p E τ ρ) i E := by
  constructor
  · intro h τ σ hσ
    have hσ' := (mem_fixing_iff_ker p E σ).mp hσ
    have h1 : LamC p E (fun τ => (matC p (rhoTau p E τ ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec (y τ)) =
        LamC p E (fun τ => cycPow p σ i • vAct p σ (y τ)) := by
      refine LinearMap.ext fun v => ?_
      rw [← LamC_matRep, ← LamC_htAct p E i hσ]
      exact h σ hσ' v
    exact congrFun (LamC_injective p E h1) τ
  · intro h σ hσ v
    have hσ' := (mem_fixing_iff_ker p E σ).mpr hσ
    rw [LamC_matRep, LamC_htAct p E i hσ']
    congr 2
    funext τ
    exact h τ σ hσ'

end SenBridge2

section SenBridge3

variable {n : ℕ} (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
  [IsGalois ℚ_[p] E]

theorem vAct_vAct (g h : GQp p) (y : Fin n → ℂ_[p]) : vAct p g (vAct p h y) = vAct p (g * h) y := by
  ext k; simp [vAct, cpAct_mul]

theorem vAct_one' (y : Fin n → ℂ_[p]) : vAct p 1 y = y := by
  ext k; simp [vAct, cpAct_one]

theorem vAct_qsmul (g : GQp p) (c : ℚ_[p]) (y : Fin n → ℂ_[p]) : vAct p g (c • y) = c • vAct p g y := by
  ext k; simp [vAct, cpAct_smul]

theorem vAct_mulVec (g : GQp p) (M : Matrix (Fin n) (Fin n) ℂ_[p]) (y : Fin n → ℂ_[p]) :
    vAct p g (M.mulVec y) = (M.map (cpAct p g)).mulVec (vAct p g y) := by
  ext k; simp [vAct, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem matC_transpose_map (g : GQp p) (M : Matrix (Fin n) (Fin n) E) :
    (matC p M).transpose.map (cpAct p g) =
      (matC p (M.map (AlgEquiv.restrictNormalHom E g : E →+* E))).transpose := by
  ext a b; simp [matC, cpAct_eC]

theorem matC_transpose_map_fix {σ : GQp p} (hσ : σ ∈ E.fixingSubgroup) (M : Matrix (Fin n) (Fin n) E) :
    (matC p M).transpose.map (cpAct p σ) = (matC p M).transpose := by
  ext a b; simp [matC, cpAct_eC_fix p E hσ]

theorem cycPow_conj (g σ : GQp p) (i : ℤ) : cycPow p (g * σ * g⁻¹) i = cycPow p σ i := by
  rw [ZInQ.Contrib.G9.PkgI4.cycPow_mul, ZInQ.Contrib.G9.PkgI4.cycPow_mul, mul_comm (cycPow p g i), mul_assoc,
    ← ZInQ.Contrib.G9.PkgI4.cycPow_mul, mul_inv_cancel, ZInQ.Contrib.G9.PkgI4.cycPow_one, mul_one]

theorem conj_mem_fixing {g σ : GQp p} (hσ : σ ∈ E.fixingSubgroup) : g * σ * g⁻¹ ∈ E.fixingSubgroup := by
  rw [mem_fixing_iff_ker] at hσ ⊢
  exact (AlgEquiv.restrictNormalHom E).normal_ker.conj_mem σ hσ g

theorem matC_mul (A B : Matrix (Fin n) (Fin n) E) : matC p (A * B) = matC p A * matC p B := by
  simp [matC, Matrix.map_mul]

/-- **Conjugation.** `dim_ℚp Y_i(ρ^τ) = dim_ℚp Y_i(ρ)`. -/
theorem finrank_Ysp_rhoTau (ρ : GQp p →* GL (Fin n) E) (i : ℤ) (τ : E ≃ₐ[ℚ_[p]] E) :
    Module.finrank ℚ_[p] (Ysp p (rhoTau p E τ ρ) i E) = Module.finrank ℚ_[p] (Ysp p ρ i E) := by
  have hγ : Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ_[p]) (K₁ := PadicAlgCl p) E) :=
    AlgEquiv.restrictNormalHom_surjective (PadicAlgCl p)
  obtain ⟨g, hg⟩ := hγ τ
  let A := (matC p (ρ g : Matrix (Fin n) (Fin n) E)).transpose
  let A' := (matC p (ρ g⁻¹ : Matrix (Fin n) (Fin n) E)).transpose
  have hAA' : A * A' = 1 := by
    simp only [A, A', ← Matrix.transpose_mul, matC_inv_mul, Matrix.transpose_one]
  have hA'A : A' * A = 1 := by
    simp only [A, A', ← Matrix.transpose_mul, matC_mul_inv, Matrix.transpose_one]
  have hmatτ : ∀ σ, (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.map (cpAct p g) =
      (matC p (rhoTau p E τ ρ σ : Matrix (Fin n) (Fin n) E)).transpose := by
    intro σ
    rw [matC_transpose_map, hg]
    rfl
  have hρmul : ∀ a b, matC p (ρ (a * b) : Matrix (Fin n) (Fin n) E) =
      matC p (ρ a : Matrix (Fin n) (Fin n) E) * matC p (ρ b : Matrix (Fin n) (Fin n) E) := by
    intro a b; rw [map_mul, Units.val_mul, matC_mul]
  -- forward map
  have hF : ∀ y ∈ Ysp p (rhoTau p E τ ρ) i E, A.mulVec (vAct p g⁻¹ y) ∈ Ysp p ρ i E := by
    intro y hy σ' hσ'
    set σ := g * σ' * g⁻¹
    have hσ : σ ∈ E.fixingSubgroup := conj_mem_fixing p E hσ'
    have e1 : (matC p (ρ σ' : Matrix (Fin n) (Fin n) E)).transpose * A =
        A * (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose := by
      simp only [A, ← Matrix.transpose_mul, ← hρmul]
      congr 2; simp [σ, mul_assoc]
    have e2 : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec (vAct p g⁻¹ y) =
        vAct p g⁻¹ ((matC p (rhoTau p E τ ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec y) := by
      rw [← hmatτ, vAct_mulVec, Matrix.map_map]
      congr 1
      exact Matrix.ext fun a b => (cpAct_inv_apply p g _).symm
    rw [Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, e2, hy σ hσ, vAct_qsmul, vAct_vAct,
      Matrix.mulVec_smul, cycPow_conj]
    have e3 : g⁻¹ * σ = σ' * g⁻¹ := by simp [σ, mul_assoc]
    rw [e3, ← vAct_vAct]
    congr 1
    rw [vAct_mulVec, matC_transpose_map_fix p E hσ']
  -- backward map
  have hF' : ∀ w ∈ Ysp p ρ i E, vAct p g (A'.mulVec w) ∈ Ysp p (rhoTau p E τ ρ) i E := by
    intro w hw σ hσ
    set σ'' := g⁻¹ * σ * g
    have hσ'' : σ'' ∈ E.fixingSubgroup := by
      have := conj_mem_fixing p E (g := g⁻¹) hσ
      simpa [σ''] using this
    have e1 : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose * A' =
        A' * (matC p (ρ σ'' : Matrix (Fin n) (Fin n) E)).transpose := by
      simp only [A', ← Matrix.transpose_mul, ← hρmul]
      congr 2; simp [σ'', mul_assoc]
    rw [← hmatτ, ← vAct_mulVec, Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec, hw σ'' hσ'',
      Matrix.mulVec_smul, vAct_qsmul]
    have e3 : (A'.mulVec (vAct p σ'' w)) = vAct p σ'' (A'.mulVec w) := by
      rw [vAct_mulVec, matC_transpose_map_fix p E hσ'']
    rw [e3, vAct_vAct, vAct_vAct]
    have e4 : g * σ'' = σ * g := by simp [σ'', mul_assoc]
    have e5 : cycPow p σ'' i = cycPow p σ i := by
      have := cycPow_conj p g⁻¹ σ i
      simpa [σ''] using this
    rw [e4, e5]
  let e : Ysp p (rhoTau p E τ ρ) i E ≃ₗ[ℚ_[p]] Ysp p ρ i E :=
    { toFun := fun y => ⟨A.mulVec (vAct p g⁻¹ y), hF y y.2⟩
      invFun := fun w => ⟨vAct p g (A'.mulVec w), hF' w w.2⟩
      map_add' := fun y z => by
        apply Subtype.ext
        simp only [Submodule.coe_add, vAct_add, Matrix.mulVec_add]
      map_smul' := fun c y => by
        apply Subtype.ext
        show A.mulVec (vAct p g⁻¹ (c • (y : Fin n → ℂ_[p]))) = c • A.mulVec (vAct p g⁻¹ y)
        rw [vAct_qsmul, Matrix.mulVec_smul]
      left_inv := fun y => by
        apply Subtype.ext
        simp only [Matrix.mulVec_mulVec, hA'A, Matrix.one_mulVec, vAct_vAct, mul_inv_cancel,
          vAct_one']
      right_inv := fun w => by
        apply Subtype.ext
        simp only [vAct_vAct, inv_mul_cancel, vAct_one', Matrix.mulVec_mulVec, hAA',
          Matrix.one_mulVec] }
  exact e.finrank_eq

end SenBridge3

section SenBridge4

variable {n : ℕ}

/-- `Y_i(ρ)` is finite-dimensional over `K` (from (T): `dim_K ≤ n`). -/
theorem Ysp_finiteDimensional (hT : TateTwistInvariants) (hA : AxSenTate)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    FiniteDimensional K (Ysp p ρ i K) := by
  classical
  haveI : Module.Free K (Ysp p ρ i K) := Module.Free.of_divisionRing K _
  refine Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt (rank_le (n := n) fun s hs => ?_)
    (Cardinal.natCast_lt_aleph0 (n := n)))
  -- the vectors of `s` are `ℂ_p`-independent
  have hli : LinearIndependent ℂ_[p] (fun x : s => ((x : Ysp p ρ i K) : Fin n → ℂ_[p])) := by
    refine Ysp_linearIndependent p hT hA K ρ (fun _ => i) _ (fun x => (x : Ysp p ρ i K).2) ?_
    intro j₀ a _ hsum
    have h1 : ∑ k : s, a k • (k : Ysp p ρ i K) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simp only [Submodule.coe_smul]
      exact hsum
    exact Fintype.linearIndependent_iff.mp hs a h1
  calc s.card = Fintype.card s := (Fintype.card_coe s).symm
    _ ≤ Module.finrank ℂ_[p] (Fin n → ℂ_[p]) := hli.fintype_card_le_finrank
    _ = n := Module.finrank_fin_fun _

variable (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]

/-- **(B) the bridge.** `dim_ℚp H_i(ρ) = dim_ℚp Y_i(ρ)`, for `E` finite Galois. -/
theorem finrank_htSpace_eq_Ysp (hT : TateTwistInvariants) (hA : AxSenTate)
    (ρ : GQp p →* GL (Fin n) E) (i : ℤ) :
    Module.finrank ℚ_[p] (htSpace p ρ i) = Module.finrank ℚ_[p] (Ysp p ρ i E) := by
  classical
  haveI : ∀ τ : E ≃ₐ[ℚ_[p]] E, FiniteDimensional E (Ysp p (rhoTau p E τ ρ) i E) :=
    fun τ => Ysp_finiteDimensional p hT hA E _ i
  haveI : ∀ τ : E ≃ₐ[ℚ_[p]] E, FiniteDimensional ℚ_[p] (Ysp p (rhoTau p E τ ρ) i E) :=
    fun τ => Module.Finite.trans E _
  let γ : GQp p →* (E ≃ₐ[ℚ_[p]] E) := AlgEquiv.restrictNormalHom E
  have hγ : Function.Surjective γ := AlgEquiv.restrictNormalHom_surjective (PadicAlgCl p)
  have hsemi : ∀ g x b, htAct p i g (iotaK p E x * b) = iotaK p E (γ g x) * htAct p i g b := by
    intro g x b
    rw [iotaK, AlgHom.comp_apply, htAct_semi, AlgHom.comp_apply]
    congr 2
    exact (AlgEquiv.restrictNormal_commutes g E x).symm
  have hdesc := descent_finrank (htAct p i) (matRep p ρ) (iotaK p E) γ hγ hsemi
  rw [← htSpace_eq_DspMat] at hdesc
  -- `Dsp(G_E)` in Dedekind coordinates
  let P : Submodule ℚ_[p] ((E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) :=
    { carrier := {y | ∀ τ, y τ ∈ Ysp p (rhoTau p E τ ρ) i E}
      zero_mem' := fun τ => (Ysp p (rhoTau p E τ ρ) i E).zero_mem
      add_mem' := fun ha hb τ => (Ysp p (rhoTau p E τ ρ) i E).add_mem (ha τ) (hb τ)
      smul_mem' := fun c y hy τ => by
        have := (Ysp p (rhoTau p E τ ρ) i E).smul_mem (algebraMap ℚ_[p] E c) (hy τ)
        rw [algebraMap_smul] at this
        exact this }
  let L := (LamC p E (n := n)).restrictScalars ℚ_[p]
  have hmap : Submodule.map L P = Dsp (htAct p i) (matRep p ρ) (γ.ker : Set (GQp p)) := by
    ext φ
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (LamC_mem_iff p E ρ i y).mpr hy
    · intro hφ
      obtain ⟨y, rfl⟩ := LamC_surjective p E φ
      exact ⟨y, (LamC_mem_iff p E ρ i y).mp hφ, rfl⟩
  have hfinP : Module.finrank ℚ_[p] P =
      ∑ τ : E ≃ₐ[ℚ_[p]] E, Module.finrank ℚ_[p] (Ysp p (rhoTau p E τ ρ) i E) := by
    let ι : (∀ τ : E ≃ₐ[ℚ_[p]] E, Ysp p (rhoTau p E τ ρ) i E) →ₗ[ℚ_[p]]
        ((E ≃ₐ[ℚ_[p]] E) → (Fin n → ℂ_[p])) :=
      { toFun := fun x τ => (x τ : Fin n → ℂ_[p])
        map_add' := fun x y => rfl
        map_smul' := fun c x => rfl }
    have hinj : Function.Injective ι := fun x y h => funext fun τ => Subtype.ext (congrFun h τ)
    have hrange : LinearMap.range ι = P := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩ τ; exact (x τ).2
      · intro hy; exact ⟨fun τ => ⟨y τ, hy τ⟩, rfl⟩
    haveI : ∀ τ : E ≃ₐ[ℚ_[p]] E, Module.Free ℚ_[p] (Ysp p (rhoTau p E τ ρ) i E) :=
      fun τ => Module.Free.of_divisionRing _ _
    rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]
  have hDsp : Module.finrank ℚ_[p] (Dsp (htAct p i) (matRep p ρ) (γ.ker : Set (GQp p))) =
      Module.finrank ℚ_[p] E * Module.finrank ℚ_[p] (Ysp p ρ i E) := by
    rw [← hmap, ← (Submodule.equivMapOfInjective L (LamC_injective p E) P).finrank_eq, hfinP]
    simp only [finrank_Ysp_rhoTau p E ρ i, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank]
  have hE : 0 < Module.finrank ℚ_[p] E := Module.finrank_pos
  rw [hDsp] at hdesc
  exact (Nat.eq_of_mul_eq_mul_left hE hdesc).symm

end SenBridge4

section SenFinal

variable {n : ℕ}

/-- **Θ is onto.** If `Σ_{j ∈ J} dim_K Y_j = n`, the `K`-bases of the `Y_j` form a `ℂ_p`-basis. -/
theorem exists_basis_Ysp (hT : TateTwistInvariants) (hA : AxSenTate)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρ : GQp p →* GL (Fin n) E) (J : Finset ℤ)
    (hsum : ∑ j ∈ J, Module.finrank K (Ysp p ρ j K) = n) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℂ_[p] (Fin n → ℂ_[p])) (j : ι → ℤ),
      ∀ k, b k ∈ Ysp p ρ (j k) K := by
  classical
  haveI : ∀ j : ℤ, FiniteDimensional K (Ysp p ρ j K) := fun j => Ysp_finiteDimensional p hT hA K ρ j
  haveI : ∀ j : ℤ, Module.Free K (Ysp p ρ j K) := fun j => Module.Free.of_divisionRing _ _
  let d : J → ℕ := fun jj => Module.finrank K (Ysp p ρ jj K)
  let bv : (Σ jj : J, Fin (d jj)) → (Fin n → ℂ_[p]) := fun k =>
    ((Module.finBasis K (Ysp p ρ k.1 K) k.2 : Ysp p ρ k.1 K) : Fin n → ℂ_[p])
  let jf : (Σ jj : J, Fin (d jj)) → ℤ := fun k => k.1
  have hli : LinearIndependent ℂ_[p] bv := by
    refine Ysp_linearIndependent p hT hA K ρ jf bv (fun k => (Module.finBasis K _ k.2).2) ?_
    intro j₀ a ha hs
    by_cases hj₀ : j₀ ∈ J
    · let jj₀ : J := ⟨j₀, hj₀⟩
      have h1 : ∑ m : Fin (d jj₀), a ⟨jj₀, m⟩ • (Module.finBasis K (Ysp p ρ jj₀ K) m) = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum, Submodule.coe_zero]
        simp only [Submodule.coe_smul]
        rw [← hs, Fintype.sum_sigma, Finset.sum_eq_single jj₀]
        · intro jj _ hjj
          refine Finset.sum_eq_zero fun m _ => ?_
          rw [ha ⟨jj, m⟩ (fun h => hjj (Subtype.ext h)), zero_smul]
        · intro h; exact absurd (Finset.mem_univ _) h
      have h2 := Fintype.linearIndependent_iff.mp (Module.finBasis K (Ysp p ρ jj₀ K)).linearIndependent _ h1
      intro k
      by_cases hk : (k.1 : ℤ) = j₀
      · obtain ⟨jj, m⟩ := k
        have : jj = jj₀ := Subtype.ext hk
        subst this
        exact h2 m
      · exact ha k hk
    · intro k
      exact ha k (fun h => hj₀ (h ▸ k.1.2))
  have hcard : Fintype.card (Σ jj : J, Fin (d jj)) = Module.finrank ℂ_[p] (Fin n → ℂ_[p]) := by
    rw [Fintype.card_sigma, Module.finrank_fin_fun]
    simp only [Fintype.card_fin, d]
    rw [Finset.sum_coe_sort J (fun j => Module.finrank K (Ysp p ρ j K)), hsum]
  exact ⟨_, inferInstance, basisOfLinearIndependentOfCardEqFinrank' bv hli hcard, jf,
    fun k => by rw [coe_basisOfLinearIndependentOfCardEqFinrank']; exact (Module.finBasis K _ k.2).2⟩

/-- **(X) the twist scalar.** -/
theorem exists_twist_scalar {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ρ ρ' : GQp p →* GL (Fin n) E) (c : GQp p → E)
    (hc : ∀ σ, matC p (ρ' σ : Matrix (Fin n) (Fin n) E) =
      algebraMap E ℂ_[p] (c σ) • matC p (ρ σ : Matrix (Fin n) (Fin n) E))
    (hc0 : ∀ σ, c σ ≠ 0) {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ_[p] (Fin n → ℂ_[p]))
    (j : ι → ℤ) (hb : ∀ k, b k ∈ Ysp p ρ' (j k) E) {i₀ : ℤ} {y₀ : Fin n → ℂ_[p]}
    (hy₀ : y₀ ∈ Ysp p ρ i₀ E) (hne : y₀ ≠ 0) :
    ∃ (s : ℤ) (β : ℂ_[p]), β ≠ 0 ∧ ∀ σ ∈ E.fixingSubgroup,
      cpAct p σ β = (algebraMap E ℂ_[p] (c σ))⁻¹ * (cycPow p σ s • β) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, b.repr y₀ k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    have : b.repr y₀ = 0 := Finsupp.ext h
    simpa using congrArg b.repr.symm this
  refine ⟨j k - i₀, b.repr y₀ k, hk, fun σ hσ => ?_⟩
  have hcσ : algebraMap E ℂ_[p] (c σ) ≠ 0 := (map_ne_zero _).mpr (hc0 σ)
  set a := fun m => b.repr y₀ m
  have hy : y₀ = ∑ m, a m • b m := (b.sum_repr y₀).symm
  -- `(ρσ)ᵀ b_m = c⁻¹ χ^{j m} σ(b_m)`
  have hbm : ∀ m, (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec (b m) =
      (algebraMap E ℂ_[p] (c σ))⁻¹ • (cycPow p σ (j m) • vAct p σ (b m)) := by
    intro m
    have h := hb m σ hσ
    rw [hc σ, Matrix.transpose_smul, Matrix.smul_mulVec] at h
    rw [← h, smul_smul, inv_mul_cancel₀ hcσ, one_smul]
  have h1 : ∑ m, cpAct p σ (a m) • vAct p σ (b m) =
      ∑ m, ((algebraMap E ℂ_[p] (c σ))⁻¹ * (cycPow p σ (j m - i₀) • a m)) • vAct p σ (b m) := by
    have e1 : vAct p σ y₀ = ∑ m, cpAct p σ (a m) • vAct p σ (b m) := by
      conv_lhs => rw [hy]
      rw [vAct_sum]
      simp only [vAct_smul]
    rw [← e1, vAct_of_mem p hy₀ hσ]
    conv_lhs => rw [hy]
    rw [Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.mulVec_smul, hbm m, sub_eq_add_neg, cycPow_add]
    ext t
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [Algebra.smul_def, map_mul]
    ring
  -- independence of `σ(b_m)`
  have hind : LinearIndependent ℂ_[p] fun m => vAct p σ (b m) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg m
    have h2 := congrArg (vAct p σ⁻¹) hg
    rw [vAct_sum, vAct_zero] at h2
    simp only [vAct_smul, vAct_vAct, inv_mul_cancel, vAct_one'] at h2
    have h3 := Fintype.linearIndependent_iff.mp b.linearIndependent _ h2 m
    have := congrArg (cpAct p σ) h3
    rwa [map_zero, ← cpAct_mul, mul_inv_cancel, cpAct_one] at this
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
  simp only [← sub_smul] at h1
  have := Fintype.linearIndependent_iff.mp hind _ h1 k
  exact sub_eq_zero.mp this

/-- **(M) multiplication by `β⁻¹`.** -/
theorem finrank_Ysp_twist {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ρ ρ' : GQp p →* GL (Fin n) E) (c : GQp p → E)
    (hc : ∀ σ, matC p (ρ' σ : Matrix (Fin n) (Fin n) E) =
      algebraMap E ℂ_[p] (c σ) • matC p (ρ σ : Matrix (Fin n) (Fin n) E))
    (hc0 : ∀ σ, c σ ≠ 0) (s : ℤ) (β : ℂ_[p]) (hβ : β ≠ 0)
    (hrel : ∀ σ ∈ E.fixingSubgroup,
      cpAct p σ β = (algebraMap E ℂ_[p] (c σ))⁻¹ * (cycPow p σ s • β)) (i : ℤ) :
    Module.finrank E (Ysp p ρ i E) = Module.finrank E (Ysp p ρ' (i + s) E) := by
  have hcne : ∀ σ, algebraMap E ℂ_[p] (c σ) ≠ 0 := fun σ => (map_ne_zero _).mpr (hc0 σ)
  have hχ : ∀ σ, algebraMap ℚ_[p] ℂ_[p] (cycPow p σ s) ≠ 0 := by
    intro σ h
    have := cycPow_neg_mul p σ s
    rw [(map_eq_zero _).mp h, mul_zero] at this
    exact zero_ne_one this
  have hfwd : ∀ y ∈ Ysp p ρ i E, β⁻¹ • y ∈ Ysp p ρ' (i + s) E := by
    intro y hy σ hσ
    rw [hc σ, Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, hy σ hσ]
    ext m
    simp only [Pi.smul_apply, vAct, smul_eq_mul, map_mul, map_inv₀, hrel σ hσ]
    simp only [Algebra.smul_def, cycPow_add, map_mul]
    have := hχ σ
    have := hcne σ
    field_simp
  have hbwd : ∀ y ∈ Ysp p ρ' (i + s) E, β • y ∈ Ysp p ρ i E := by
    intro y hy σ hσ
    have h := hy σ hσ
    rw [hc σ, Matrix.transpose_smul, Matrix.smul_mulVec] at h
    have h' : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).transpose.mulVec y =
        (algebraMap E ℂ_[p] (c σ))⁻¹ • (cycPow p σ (i + s) • vAct p σ y) := by
      rw [← h, smul_smul, inv_mul_cancel₀ (hcne σ), one_smul]
    rw [Matrix.mulVec_smul, h']
    ext m
    simp only [Pi.smul_apply, vAct, smul_eq_mul, map_mul, hrel σ hσ]
    simp only [Algebra.smul_def, cycPow_add, map_mul]
    have := hχ σ
    have := hcne σ
    field_simp
  let e : Ysp p ρ i E ≃ₗ[E] Ysp p ρ' (i + s) E :=
    { toFun := fun y => ⟨β⁻¹ • (y : Fin n → ℂ_[p]), hfwd y y.2⟩
      invFun := fun y => ⟨β • (y : Fin n → ℂ_[p]), hbwd y y.2⟩
      map_add' := fun y z => Subtype.ext (smul_add _ _ _)
      map_smul' := fun a y => by
        apply Subtype.ext
        show β⁻¹ • (a • (y : Fin n → ℂ_[p])) = a • (β⁻¹ • (y : Fin n → ℂ_[p]))
        rw [← algebraMap_smul (A := ℂ_[p]) a, ← algebraMap_smul (A := ℂ_[p]) a, smul_comm]
      left_inv := fun y => Subtype.ext (by
        show β • (β⁻¹ • (y : Fin n → ℂ_[p])) = y
        rw [smul_smul, mul_inv_cancel₀ hβ, one_smul])
      right_inv := fun y => Subtype.ext (by
        show β⁻¹ • (β • (y : Fin n → ℂ_[p])) = y
        rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]) }
  exact e.finrank_eq

end SenFinal

section SenAssembly

variable {n : ℕ}

theorem htMult_eq_finrank_Ysp (hT : TateTwistInvariants) (hA : AxSenTate)
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E] [IsGalois ℚ_[p] E]
    (ρ : GQp p →* GL (Fin n) E) (w : ℤ) :
    htMult p ρ w = Module.finrank E (Ysp p ρ (-w) E) := by
  haveI : FiniteDimensional E (Ysp p ρ (-w) E) := Ysp_finiteDimensional p hT hA E ρ (-w)
  haveI : Module.Free E (Ysp p ρ (-w) E) := Module.Free.of_divisionRing _ _
  rw [htMult, finrank_htSpace_eq_Ysp p E hT hA ρ (-w),
    ← Module.finrank_mul_finrank ℚ_[p] E (Ysp p ρ (-w) E)]
  exact Nat.mul_div_cancel_left _ Module.finrank_pos

/-- **H-51, `SenTwist`, from Tate's two theorems.** -/
theorem senTwist_of_tate (hT : TateTwistInvariants) (hA : AxSenTate) : G0Galois.SenTwist := by
  intro p _ n ρ ρ' ψ S S' htw hS hS' hρ hρ'
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, ?_⟩
    rw [Multiset.card_eq_zero] at hS hS'
    simp [hS, hS']
  obtain ⟨E₁, hE₁, ρ₁, h₁, hw₁⟩ := hρ
  obtain ⟨E₂, hE₂, ρ₂, h₂, hw₂⟩ := hρ'
  let E₀ := E₁ ⊔ E₂
  let E := IntermediateField.normalClosure ℚ_[p] E₀ (PadicAlgCl p)
  haveI : FiniteDimensional ℚ_[p] E := inferInstance
  haveI : IsGalois ℚ_[p] E := IsGalois.mk
  have hE₀E : E₀ ≤ E := IntermediateField.le_normalClosure E₀
  let ρL := ρ.restrictLocal p
  let ρ'L := ρ'.restrictLocal p
  have hent₁ : ∀ σ i j, (((ρ₁ σ : Matrix (Fin n) (Fin n) E₁) i j : E₁) : PadicAlgCl p) =
      (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j := by
    intro σ i j; rw [← h₁ σ]; rfl
  have hent₂ : ∀ σ i j, (((ρ₂ σ : Matrix (Fin n) (Fin n) E₂) i j : E₂) : PadicAlgCl p) =
      (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j := by
    intro σ i j; rw [← h₂ σ]; rfl
  have hmem : ∀ σ i j, (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ E := by
    intro σ i j; rw [← hent₁]
    exact hE₀E ((le_sup_left : E₁ ≤ E₀) ((ρ₁ σ : Matrix (Fin n) (Fin n) E₁) i j).2)
  have hmem' : ∀ σ i j, (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) i j ∈ E := by
    intro σ i j; rw [← hent₂]
    exact hE₀E ((le_sup_right : E₂ ≤ E₀) ((ρ₂ σ : Matrix (Fin n) (Fin n) E₂) i j).2)
  let ρE := liftGL E ρL hmem
  let ρ'E := liftGL E ρ'L hmem'
  have hwE : ∀ w, htMult p ρE w = S.count w := fun w =>
    (htMult_eq_of_lifts p ρL ρE ρ₁ (liftGL_map E ρL hmem) h₁ w).trans (hw₁ w)
  have hw'E : ∀ w, htMult p ρ'E w = S'.count w := fun w =>
    (htMult_eq_of_lifts p ρ'L ρ'E ρ₂ (liftGL_map E ρ'L hmem') h₂ w).trans (hw₂ w)
  -- the twist character with values in `E`
  have htwL : ∀ σ, (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) =
      (ψ.toHom (decomp p σ) : PadicAlgCl p) • (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) :=
    fun σ => htw (decomp p σ)
  have hψmem : ∀ σ, (ψ.toHom (decomp p σ) : PadicAlgCl p) ∈ E := by
    intro σ
    have hdet : (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)).det ≠ 0 :=
      Matrix.GeneralLinearGroup.det_ne_zero _
    obtain ⟨j, hj⟩ : ∃ j, (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) ⟨0, hn⟩ j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hdet (Matrix.det_eq_zero_of_row_eq_zero ⟨0, hn⟩ h)
    have e := congrFun (congrFun (htwL σ) ⟨0, hn⟩) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    have : (ψ.toHom (decomp p σ) : PadicAlgCl p) =
        (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) ⟨0, hn⟩ j /
          (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) ⟨0, hn⟩ j := by
      rw [e, mul_div_assoc, div_self hj, mul_one]
    rw [this]
    exact E.div_mem (hmem' σ _ _) (hmem σ _ _)
  let c : GQp p → E := fun σ => ⟨(ψ.toHom (decomp p σ) : PadicAlgCl p), hψmem σ⟩
  have hc0 : ∀ σ, c σ ≠ 0 := fun σ h =>
    (ψ.toHom (decomp p σ)).ne_zero (congrArg Subtype.val h)
  have hc : ∀ σ, matC p (ρ'E σ : Matrix (Fin n) (Fin n) E) =
      algebraMap E ℂ_[p] (c σ) • matC p (ρE σ : Matrix (Fin n) (Fin n) E) := by
    intro σ
    ext a b
    have hE : ((ρ'E σ : Matrix (Fin n) (Fin n) E) a b) = c σ * ((ρE σ : Matrix (Fin n) (Fin n) E) a b) :=
      Subtype.ext (by
        change (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) a b =
          (ψ.toHom (decomp p σ) : PadicAlgCl p) * (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl p)) a b
        rw [htwL σ]
        rfl)
    simp only [matC, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hE, map_mul]
  -- dimensions of the `Y`'s
  have hdY : ∀ i, Module.finrank E (Ysp p ρE i E) = S.count (-i) := by
    intro i; rw [← hwE, htMult_eq_finrank_Ysp p hT hA E ρE (-i), neg_neg]
  have hdY' : ∀ i, Module.finrank E (Ysp p ρ'E i E) = S'.count (-i) := by
    intro i; rw [← hw'E, htMult_eq_finrank_Ysp p hT hA E ρ'E (-i), neg_neg]
  -- a basis of `ℂ_pⁿ` from the `Y_j(ρ')`
  let J' : Finset ℤ := (S'.map fun w => -w).toFinset
  have hsum : ∑ j ∈ J', Module.finrank E (Ysp p ρ'E j E) = n := by
    simp only [hdY']
    have hJ : J' = S'.toFinset.map ⟨fun w => -w, neg_injective⟩ := by
      ext j; simp [J']
    rw [hJ, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, neg_neg]
    rw [Multiset.toFinset_sum_count_eq, hS']
  obtain ⟨ι, _, b, jb, hb⟩ := exists_basis_Ysp p hT hA E ρ'E J' hsum
  -- a nonzero vector in some `Y_{i₀}(ρ)`
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ ∈ S := by
    have : S ≠ 0 := by
      intro h; rw [h, Multiset.card_zero] at hS; omega
    exact Multiset.exists_mem_of_ne_zero this
  haveI : FiniteDimensional E (Ysp p ρE (-w₀) E) := Ysp_finiteDimensional p hT hA E ρE (-w₀)
  have hne : Ysp p ρE (-w₀) E ≠ ⊥ := by
    intro h
    have := hdY (-w₀)
    rw [h, finrank_bot, neg_neg] at this
    exact (Multiset.count_ne_zero.mpr hw₀) this.symm
  obtain ⟨y₀, hy₀, hy₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨s, β, hβ, hrel⟩ := exists_twist_scalar p ρE ρ'E c hc hc0 b jb hb hy₀ hy₀ne
  have hdim : ∀ i, Module.finrank E (Ysp p ρE i E) = Module.finrank E (Ysp p ρ'E (i + s) E) :=
    finrank_Ysp_twist p ρE ρ'E c hc hc0 s β hβ hrel
  refine ⟨-s, ?_⟩
  ext u
  have e1 : S.count (u + s) = S'.count u := by
    have := hdim (-(u + s))
    rw [hdY, hdY', neg_neg] at this
    rw [this]
    congr 1
    ring
  have e2 : (S.map (· + -s)).count u = S.count (u + s) := by
    have := Multiset.count_map_eq_count' (fun w => w + -s) S (add_left_injective _) (u + s)
    simp only [add_neg_cancel_right] at this
    exact this
  rw [e2, e1]

end SenAssembly

/-! ## §13. Glue proved: `AttachedConj` (Chebotarev with Brauer–Nesbitt)

From the kernel's proved leaves T18 (`ZInQ.Contrib.frobeniusDense`, through Tau Ceti's Chebotarev)
and T19 (`TSkolemKW.C10.brauerNesbittChar0'`), via `C9Rhof.iso_of_arithFrob`
(`ZInQKernel/HDecomp/ModCurves/C9.lean`). The bridge: pkg-I4's matrix-valued `GaloisRep` as a
Mathlib `Representation` on `ℚ̄_ℓ²`; its `IsSemisimple` (invariant complements) as
`IsSemisimpleModule` over the group algebra (Mathlib's `Representation.mapSubmodule`). -/

section AttachedConjSec


variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- pkg-I4's `GaloisRep` as a Mathlib `Representation` on `ℚ̄_ℓⁿ`. -/
def galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) :
    Representation (PadicAlgCl ℓ) ZInQ.Contrib.G9.PkgI4.GQ (Fin n → PadicAlgCl ℓ) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) ≃ₐ[PadicAlgCl ℓ] _).toMonoidHom.comp
    ((Units.coeHom _).comp ρ.toHom)

theorem galRepRep_apply {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    galRepRep ρ σ = Matrix.toLin' (ρ.mat σ) := rfl

theorem toMatrix_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (galRepRep ρ σ) = ρ.mat σ := by
  rw [LinearMap.toMatrix_eq_toMatrix', galRepRep_apply, LinearMap.toMatrix'_toLin']

theorem trace_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (σ : ZInQ.Contrib.G9.PkgI4.GQ) :
    LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ σ) = (ρ.mat σ).trace := by
  rw [LinearMap.trace_eq_matrix_trace (PadicAlgCl ℓ) (Pi.basisFun (PadicAlgCl ℓ) (Fin n)),
    toMatrix_galRepRep]

theorem continuous_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) :
    Continuous fun g => LinearMap.toMatrix (Pi.basisFun (PadicAlgCl ℓ) (Fin n))
      (Pi.basisFun (PadicAlgCl ℓ) (Fin n)) (galRepRep ρ g) := by
  simp only [toMatrix_galRepRep]
  exact Units.continuous_val.comp ρ.continuous_toHom

theorem mem_invtSubmodule_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n)
    (W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ)) :
    W ∈ (galRepRep ρ).invtSubmodule ↔ ∀ σ, W.map (Matrix.toLin' (ρ.mat σ)) ≤ W := by
  rw [Representation.mem_invtSubmodule]
  refine forall_congr' fun σ => ?_
  rw [Module.End.mem_invtSubmodule, Submodule.map_le_iff_le_comap, galRepRep_apply]

theorem isSemisimpleModule_galRepRep {n : ℕ} (ρ : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ n) (h : ZInQ.Contrib.G9.PkgI4.GaloisRep.IsSemisimple ρ) :
    IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) ZInQ.Contrib.G9.PkgI4.GQ) (galRepRep ρ).asModule := by
  rw [isSemisimpleModule_iff, ← (galRepRep ρ).mapSubmodule.complementedLattice_iff]
  refine ⟨fun a => ?_⟩
  obtain ⟨W, hW⟩ := a
  obtain ⟨W', hc, hW'⟩ := h W ((mem_invtSubmodule_galRepRep ρ W).mp hW)
  refine ⟨⟨W', (mem_invtSubmodule_galRepRep ρ W').mpr hW'⟩, ?_, ?_⟩
  · rw [disjoint_iff]
    exact Subtype.ext hc.inf_eq_bot
  · rw [codisjoint_iff]
    exact Subtype.ext hc.sup_eq_top

/-- `C9Rhof.FrobeniusDense` from the kernel's proved T18 (same body, other namespace). -/
theorem frobeniusDense_C9 : C9Rhof.FrobeniusDense := by
  intro U hU σ S
  obtain ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩ := ZInQ.Contrib.frobeniusDense U hU σ S
  exact ⟨p, hp, hpS, v, τ, hv, hτ, hU'⟩

/-- **`AttachedConj`, proved** (from T18, T19 in the kernel). -/
theorem attachedConj_proof : AttachedConj := by
  intro ℓ _ ρ ρ' S hss hss' hS
  have htr : ∀ p, p.Prime → p ∉ S → ∀ (v : ValuationSubring ZInQ.Contrib.G9.PkgI4.Qbar) (τ : ZInQ.Contrib.G9.PkgI4.GQ),
      ZInQ.Contrib.G9.PkgI4.LiesOver v p → ZInQ.Contrib.G9.PkgI4.IsArithFrob τ v p →
      LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ τ) =
        LinearMap.trace (PadicAlgCl ℓ) _ (galRepRep ρ' τ) := by
    intro p hp hpS v τ hv hτ
    rw [trace_galRepRep, trace_galRepRep]
    exact (hS p hp hpS).2.2 v τ hv hτ
  obtain ⟨e⟩ := C9Rhof.iso_of_arithFrob TSkolemKW.C10.brauerNesbittChar0' frobeniusDense_C9 S
    (Pi.basisFun (PadicAlgCl ℓ) (Fin 2)) (Pi.basisFun (PadicAlgCl ℓ) (Fin 2))
    (galRepRep ρ) (galRepRep ρ') (continuous_galRepRep ρ) (continuous_galRepRep ρ')
    (isSemisimpleModule_galRepRep ρ hss) (isSemisimpleModule_galRepRep ρ' hss') htr
  let L : (Fin 2 → PadicAlgCl ℓ) ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) :=
    ((galRepRep ρ).asModuleEquiv.symm.trans (e.restrictScalars (PadicAlgCl ℓ))).trans
      (galRepRep ρ').asModuleEquiv
  have hL : ∀ σ v, L (galRepRep ρ σ v) = galRepRep ρ' σ (L v) := by
    intro σ v
    simp only [L, LinearEquiv.trans_apply, Representation.asModuleEquiv_symm_map_rho,
      LinearEquiv.restrictScalars_apply, LinearEquiv.map_smul,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
  let M := LinearMap.toMatrix' L.toLinearMap
  let M' := LinearMap.toMatrix' L.symm.toLinearMap
  have h1 : M' * M = 1 := by
    simp only [M, M', ← LinearMap.toMatrix'_comp]
    rw [show (L.symm.toLinearMap ∘ₗ L.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => L.symm_apply_apply v, LinearMap.toMatrix'_id]
  have h2 : M * M' = 1 := by
    simp only [M, M', ← LinearMap.toMatrix'_comp]
    rw [show (L.toLinearMap ∘ₗ L.symm.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => L.apply_symm_apply v, LinearMap.toMatrix'_id]
  have hcomm : ∀ σ, M * ρ.mat σ = ρ'.mat σ * M := by
    intro σ
    have : L.toLinearMap ∘ₗ galRepRep ρ σ = galRepRep ρ' σ ∘ₗ L.toLinearMap :=
      LinearMap.ext fun v => hL σ v
    have h' := congrArg LinearMap.toMatrix' this
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, galRepRep_apply, galRepRep_apply,
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin'] at h'
    exact h'
  refine ⟨⟨M', M, h1, h2⟩, fun σ => Units.ext ?_⟩
  change ρ.mat σ = M' * ρ'.mat σ * M
  rw [mul_assoc, ← hcomm σ, ← mul_assoc, h1, one_mul]

end AttachedConjSec


/-! ## §17. `DetFromFrobenius` (R14 glue), proved

From the kernel's T18 (density of arithmetic Frobenius elements), Mathlib's cyclotomic characters
(`cyclotomicCharacter`, `modularCyclotomicCharacter`, `cyclotomicCharacter.continuous`) and an
elementary lemma: an arithmetic Frobenius at `v ∣ p` raises roots of unity of order prime to `p`
to the `p`-th power (`arithFrob_pow_of_rootOfUnity`). -/

section DetFrob

open ZInQ.Contrib.G9.PkgI4


theorem val_eq_one_of_pow {v : ValuationSubring Qbar} {x : Qbar} {m : ℕ} (hm : m ≠ 0)
    (hx : x ^ m = 1) : v.valuation x = 1 := by
  have h := congrArg v.valuation hx
  rw [map_pow, map_one] at h
  rcases lt_trichotomy (v.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le h1 hm))
  · exact h1
  · exact absurd h (ne_of_gt (one_lt_pow₀ h1 hm))

/-- An arithmetic Frobenius at `v ∣ p` acts on roots of unity of order prime to `p` as `ζ ↦ ζ^p`. -/
theorem arithFrob_pow_of_rootOfUnity {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime)
    (hv : LiesOver v p) (hσ : IsArithFrob σ v p) {ζ : Qbar} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1)
    (hpm : ¬ p ∣ m) : σ ζ = ζ ^ p := by
  set val := v.valuation
  have hζ1 : val ζ = 1 := val_eq_one_of_pow hm hζ
  have hζv : ζ ∈ v := (v.valuation_le_one_iff ζ).mp hζ1.le
  have hσζm : (σ ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  have hσζ1 : val (σ ζ) = 1 := val_eq_one_of_pow hm hσζm
  have hζp0 : ζ ^ p ≠ 0 := pow_ne_zero _ (by rintro rfl; simp [hm] at hζ)
  set ξ := σ ζ / ζ ^ p with hξ
  have hξm : ξ ^ m = 1 := by
    rw [hξ, div_pow, hσζm, ← pow_mul, mul_comm, pow_mul, hζ, one_pow, div_one]
  have hlt : val (σ ζ - ζ ^ p) < 1 := (v.mem_nonunits_iff).mp (hσ.2 ζ hζv)
  have hξ1 : val (ξ - 1) < 1 := by
    have : ξ - 1 = (σ ζ - ζ ^ p) / ζ ^ p := by rw [hξ]; field_simp
    rw [this, map_div₀, map_pow, hζ1, one_pow, div_one]
    exact hlt
  by_contra hne
  have hξne : ξ ≠ 1 := by
    intro h; apply hne
    rw [hξ, div_eq_one_iff_eq hζp0] at h
    exact h
  -- `Σ_{j<m} ξ^j = 0`
  have hgeom : ∑ j ∈ Finset.range m, ξ ^ j = 0 := by
    have := geom_sum_mul ξ m
    rw [hξm, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hξne)
  -- each `ξ^j - 1` is in the maximal ideal
  have hj : ∀ j, val (ξ ^ j - 1) < 1 := by
    intro j
    have : ξ ^ j - 1 = (ξ - 1) * ∑ i ∈ Finset.range j, ξ ^ i := by
      rw [mul_comm, geom_sum_mul]
    rw [this, map_mul]
    have hs : val (∑ i ∈ Finset.range j, ξ ^ i) ≤ 1 := by
      apply Valuation.map_sum_le
      intro i _
      rw [map_pow]
      have : val ξ = 1 := val_eq_one_of_pow hm hξm
      rw [this, one_pow]
    calc val (ξ - 1) * val (∑ i ∈ Finset.range j, ξ ^ i) ≤ val (ξ - 1) * 1 :=
          mul_le_mul_of_nonneg_left hs zero_le
      _ < 1 := by rw [mul_one]; exact hξ1
  -- so `m ∈` the maximal ideal
  have hmval : val (m : Qbar) < 1 := by
    have : (m : Qbar) = -∑ j ∈ Finset.range m, (ξ ^ j - 1) := by
      rw [Finset.sum_sub_distrib, hgeom]; simp
    rw [this, Valuation.map_neg]
    exact Valuation.map_sum_lt' _ zero_lt_one fun j _ => hj j
  have hpval : val (p : Qbar) < 1 := (v.mem_nonunits_iff).mp hv
  -- `gcd(m, p) = 1` gives `1` in the maximal ideal
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * m + b * p = 1 := by
    have := Nat.Coprime.isCoprime hcop.symm
    obtain ⟨a, b, h⟩ := this
    exact ⟨a, b, by exact_mod_cast h⟩
  have h1 : val (1 : Qbar) < 1 := by
    have : (1 : Qbar) = (a : Qbar) * m + (b : Qbar) * p := by exact_mod_cast hab.symm
    rw [this]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (v.valuation_le_one ⟨_, intCast_mem v a⟩))
        hmval
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (v.valuation_le_one ⟨_, intCast_mem v b⟩))
        hpval
  rw [map_one] at h1
  exact lt_irrefl _ h1

end DetFrob

section DetFrob2

open ZInQ.Contrib.G9.PkgI4

theorem pow_eq_pow_mod_of {M : Type*} [Monoid M] {t : M} {n : ℕ} (ht : t ^ n = 1) (a : ℕ) :
    t ^ a = t ^ (a % n) := by
  conv_lhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, ht, one_pow, mul_one]

/-- The cyclotomic character at an arithmetic Frobenius at `p ≠ ℓ` is `p`. -/
theorem cyc_arithFrob {ℓ : ℕ} [Fact ℓ.Prime] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpl : p ≠ ℓ) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((cyclotomicCharacter Qbar ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = (p : ℤ_[ℓ]) := by
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [cyclotomicCharacter.toZModPow, map_natCast]
  have hl : (ℓ ^ n) ≠ 0 := pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero
  haveI : NeZero (ℓ ^ n) := ⟨hl⟩
  refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
  have htn : (t : Qbar) ^ (ℓ ^ n) = 1 := by
    have := (mem_rootsOfUnity _ _).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  have hpm : ¬ p ∣ ℓ ^ n := fun h =>
    hpl ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).mp (hp.dvd_of_dvd_pow h))
  change σ (t : Qbar) = ((t ^ ((p : ZMod (ℓ ^ n))).val : Qbarˣ) : Qbar)
  rw [arithFrob_pow_of_rootOfUnity hp hv hσ hl htn hpm, Units.val_pow_eq_pow_val, ZMod.val_natCast,
    ← pow_eq_pow_mod_of htn]

/-- The cyclotomic character mod `N` at an arithmetic Frobenius at `p ∤ N` is `p`. -/
theorem modCyc_arithFrob {N : ℕ} [NeZero N] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((modularCyclotomicCharacter Qbar (HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar N)
      σ.toRingEquiv : (ZMod N)ˣ) : ZMod N) = (p : ZMod N) := by
  refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
  have htn : (t : Qbar) ^ N = 1 := by
    have := (mem_rootsOfUnity _ _).mp ht
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  change σ (t : Qbar) = ((t ^ ((p : ZMod N)).val : Qbarˣ) : Qbar)
  rw [arithFrob_pow_of_rootOfUnity hp hv hσ (NeZero.ne N) htn hpN, Units.val_pow_eq_pow_val,
    ZMod.val_natCast, ← pow_eq_pow_mod_of htn]

end DetFrob2

section EpsZero

open ZInQ.Contrib.G9.PkgI4

variable {ℓ : ℕ} [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
  {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- `ιC` on `m`-th roots of unity is a bijection `μ_m(ℚ̄) ≃ μ_m(ℂ)`. -/
noncomputable def rootsEquiv (m : ℕ) [NeZero m] : rootsOfUnity m Qbar ≃* rootsOfUnity m ℂ :=
  MulEquiv.ofBijective (restrictRootsOfUnity ιC m) <| by
    have hinj : Function.Injective (restrictRootsOfUnity ιC m) := by
      intro x y h
      apply Subtype.ext; apply Units.ext
      have := congrArg (fun z : rootsOfUnity m ℂ => ((z : ℂˣ) : ℂ)) h
      simp only [restrictRootsOfUnity_coe_apply] at this
      exact ιC.toRingHom.injective this
    refine (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
    rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar m, Complex.card_rootsOfUnity]

theorem iotaC_rootsEquiv_symm (m : ℕ) [NeZero m] (x : rootsOfUnity m ℂ) :
    ιC (((rootsEquiv ιC m).symm x : Qbarˣ) : Qbar) = ((x : ℂˣ) : ℂ) := by
  have h := (rootsEquiv ιC m).apply_symm_apply x
  conv_rhs => rw [← h]
  rfl

/-- The order of every value of `χ` divides `m = #(ℤ/N)ˣ`. -/
noncomputable def chiRoots : (ZMod N)ˣ →* rootsOfUnity (Nat.card (ZMod N)ˣ) ℂ :=
  MonoidHom.codRestrict χ.toUnitHom _ fun u => by
    rw [mem_rootsOfUnity, ← map_pow, pow_card_eq_one', map_one]

/-- The nebentypus as an `ℓ`-adic character of `(ℤ/N)ˣ`: `u ↦ ιL(ιC⁻¹(χ u))`. -/
noncomputable def chiL : (ZMod N)ˣ →* (PadicAlgCl ℓ)ˣ :=
  haveI : NeZero (Nat.card (ZMod N)ˣ) := ⟨Nat.card_pos.ne'⟩
  (Units.map ιL.toMonoidHom).comp ((rootsOfUnity (Nat.card (ZMod N)ˣ) Qbar).subtype.comp
    ((rootsEquiv ιC (Nat.card (ZMod N)ˣ)).symm.toMonoidHom.comp (chiRoots χ)))

theorem chiL_spec (u : (ZMod N)ˣ) : ∃ γ : Qbar, ιC γ = χ (u : ZMod N) ∧
    ((chiL ιC ιL χ u : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = ιL γ := by
  haveI : NeZero (Nat.card (ZMod N)ˣ) := ⟨Nat.card_pos.ne'⟩
  refine ⟨(((rootsEquiv ιC (Nat.card (ZMod N)ˣ)).symm (chiRoots χ u) : Qbarˣ) : Qbar), ?_, rfl⟩
  rw [iotaC_rootsEquiv_symm]
  rfl

/-- The cyclotomic character mod `N` on `G_ℚ`. -/
noncomputable def modCycQ : GQ →* (ZMod N)ˣ :=
  (modularCyclotomicCharacter Qbar (HasEnoughRootsOfUnity.natCard_rootsOfUnity Qbar N)).comp
    G0Galois.toRingEquivQ

/-- `ε₀ = chiL ∘ modCycQ`: the nebentypus as a Galois character. -/
noncomputable def eps0 : GQ →* (PadicAlgCl ℓ)ˣ := (chiL ιC ιL χ).comp modCycQ

theorem eps0_finite : (Set.range (eps0 ιC ιL χ)).Finite :=
  (Set.finite_range (chiL ιC ιL χ)).subset (by rintro _ ⟨σ, rfl⟩; exact ⟨_, rfl⟩)

theorem eps0_arithFrob {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ∃ γ : Qbar, ιC γ = χ (p : ZMod N) ∧ ((eps0 ιC ιL χ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = ιL γ := by
  obtain ⟨γ, hγ, hval⟩ := chiL_spec ιC ιL χ (modCycQ σ)
  refine ⟨γ, ?_, hval⟩
  rw [hγ]
  congr 1
  exact modCyc_arithFrob hp hpN hv hσ

/-- `ε₀` is trivial on `Gal(ℚ̄/ℚ(μ_N))`, an open subgroup; hence continuous. -/
theorem eps0_continuous : Continuous (eps0 ιC ιL χ) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Qbar N
  let K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {ζ}
  haveI : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  have hK : ∀ σ ∈ K.fixingSubgroup, eps0 ιC ιL χ σ = 1 := by
    intro σ hσ
    have hfix : σ ζ = ζ := hσ ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
    have h1 : modCycQ (N := N) σ = 1 := by
      apply Units.ext
      refine (modularCyclotomicCharacter.unique Qbar _ σ.toRingEquiv fun t ht => ?_).symm
      have htn : (t : Qbar) ^ N = 1 := by
        have := (mem_rootsOfUnity _ _).mp ht
        rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one htn
      change σ (t : Qbar) = ((t ^ ((1 : (ZMod N)ˣ) : ZMod N).val : Qbarˣ) : Qbar)
      rw [← hi, map_pow, hfix, Units.val_pow_eq_pow_val, ← hi]
      by_cases hN1 : N = 1
      · subst hN1
        have : (t : Qbar) = 1 := by simpa using htn
        rw [hi, this, one_pow]
      · haveI : Fact (1 < N) := ⟨by have := NeZero.ne N; omega⟩
        rw [Units.val_one, ZMod.val_one, pow_one]
    simp [eps0, h1]
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  have hnhds : (K.fixingSubgroup : Set GQ) ∈ nhds (1 : GQ) :=
    (IntermediateField.fixingSubgroup_isOpen K).mem_nhds K.fixingSubgroup.one_mem
  exact tendsto_nhds_of_eventually_eq (Filter.mem_of_superset hnhds fun σ hσ => hK σ hσ)

end EpsZero


section DetFrobMain

open ZInQ.Contrib.G9.PkgI4

theorem toRingEquivQ_eq : G0Galois.toRingEquivQ = MulSemiringAction.toRingAut Gal(Qbar/ℚ) Qbar := by
  ext σ x; rfl

theorem continuous_units_map {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M]
    [TopologicalSpace N] {X : Type*} [TopologicalSpace X] (f : M →* N) (hf : Continuous f)
    {c : X → Mˣ} (hc : Continuous c) : Continuous fun x => Units.map f (c x) := by
  rw [Units.continuous_iff]
  exact ⟨hf.comp (Units.continuous_val.comp hc), hf.comp (Units.continuous_coe_inv.comp hc)⟩

theorem continuous_cycQ (ℓ : ℕ) [Fact ℓ.Prime] : Continuous (G0Galois.cycQ ℓ) := by
  have h := cyclotomicCharacter.continuous ℓ ℚ Qbar
  rw [← toRingEquivQ_eq] at h
  have hf : Continuous ((algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp PadicInt.Coe.ringHom) :=
    (continuous_algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp continuous_subtype_val
  exact continuous_units_map _ hf h

theorem cycQ_arithFrob {ℓ : ℕ} [Fact ℓ.Prime] {σ : GQ} {v : ValuationSubring Qbar} {p : ℕ}
    (hp : p.Prime) (hpl : p ≠ ℓ) (hv : LiesOver v p) (hσ : IsArithFrob σ v p) :
    ((G0Galois.cycQ ℓ σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = (p : PadicAlgCl ℓ) := by
  change algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)
    (((cyclotomicCharacter Qbar ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) = _
  rw [cyc_arithFrob hp hpl hv hσ]
  simp

/-- **`DetFromFrobenius`, proved** (from the kernel's T18 and Mathlib's cyclotomic characters). -/
theorem detFromFrobenius_proof : DetFromFrobenius := by
  intro ℓ _ ιC ιL N k χ ρ hN hfrob
  haveI : NeZero N := ⟨hN.ne'⟩
  let detU : GQ →* (PadicAlgCl ℓ)ˣ := Matrix.GeneralLinearGroup.det.comp ρ.toHom
  have hdetU : ∀ σ, ((detU σ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = (ρ.mat σ).det := fun σ => rfl
  have hdetc : Continuous detU := by
    rw [Units.continuous_iff]
    refine ⟨(Units.continuous_val.comp ρ.continuous_toHom).matrix_det, ?_⟩
    have : (fun σ => (((detU σ)⁻¹ : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)) =
        fun σ => (((ρ.toHom σ)⁻¹ : GL (Fin 2) (PadicAlgCl ℓ)) : Matrix (Fin 2) (Fin 2) _).det := by
      funext σ; rfl
    rw [this]
    exact (Units.continuous_coe_inv.comp ρ.continuous_toHom).matrix_det
  let δ : GQ → (PadicAlgCl ℓ)ˣ := fun σ => detU σ * G0Galois.cycQ ℓ σ ^ (-(k - 1))
  have hδc : Continuous δ := hdetc.mul ((continuous_cycQ ℓ).zpow _)
  have hp0 : ∀ p : ℕ, p.Prime → (p : PadicAlgCl ℓ) ≠ 0 := fun p hp => by
    exact_mod_cast hp.ne_zero
  have hEq : δ = eps0 ιC ιL χ := by
    refine C9Rhof.eq_of_eq_on_arithFrob frobeniusDense_C9 (N * ℓ).primeFactors δ (eps0 ιC ιL χ)
      hδc (eps0_continuous ιC ιL χ) fun p hp hpS v τ hv hτ => ?_
    have hNl : N * ℓ ≠ 0 := Nat.mul_ne_zero hN.ne' (Fact.out : ℓ.Prime).ne_zero
    have hpNl : ¬ p ∣ N * ℓ := fun h => hpS (Nat.mem_primeFactors.mpr ⟨hp, h, hNl⟩)
    have hpN : ¬ p ∣ N := fun h => hpNl (Dvd.dvd.mul_right h ℓ)
    have hpl : p ≠ ℓ := fun h => hpNl (h ▸ Dvd.intro_left N rfl)
    obtain ⟨-, β, hβ, hdet⟩ := hfrob p hp hpNl
    obtain ⟨γ, hγ, hε⟩ := eps0_arithFrob ιC ιL χ hp hpN hv hτ
    have hβγ : β = γ * (p : Qbar) ^ (k - 1) := by
      apply ιC.toRingHom.injective
      change ιC β = ιC (γ * (p : Qbar) ^ (k - 1))
      rw [hβ, map_mul, map_zpow₀, map_natCast ιC, hγ]
    apply Units.ext
    change (detU τ : PadicAlgCl ℓ) * ((G0Galois.cycQ ℓ τ ^ (-(k - 1)) : (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ) = _
    rw [hdetU, hdet v τ hv hτ, Units.val_zpow_eq_zpow_val, cycQ_arithFrob hp hpl hv hτ, hε, hβγ,
      map_mul, map_zpow₀, map_natCast ιL, zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (hp0 p hp)),
      mul_one]
  refine ⟨eps0 ιC ιL χ, eps0_finite ιC ιL χ, fun σ => ?_⟩
  rw [← hEq]
  change (ρ.mat σ).det = ((detU σ * G0Galois.cycQ ℓ σ ^ (-(k - 1)) * G0Galois.cycQ ℓ σ ^ (k - 1) :
    (PadicAlgCl ℓ)ˣ) : PadicAlgCl ℓ)
  rw [zpow_neg, inv_mul_cancel_right, hdetU]

end DetFrobMain


section ArtinHelpers

open ZInQ.Contrib.G9.PkgI4

/-- A root of unity in `ℂ` is `ιC` of an element of `ℚ̄`. -/
theorem mem_range_of_pow_eq_one (ιC : Qbar →ₐ[ℚ] ℂ) {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) :
    z ∈ Set.range ιC := by
  haveI : NeZero n := ⟨hn⟩
  have hz0 : z ≠ 0 := by rintro rfl; simp [hn] at hz
  let u : rootsOfUnity n ℂ := ⟨Units.mk0 z hz0, by
    rw [mem_rootsOfUnity]; apply Units.ext; simp [hz]⟩
  refine ⟨(((rootsEquiv ιC n).symm u : Qbarˣ) : Qbar), ?_⟩
  rw [iotaC_rootsEquiv_symm]
  rfl

/-- The trace of a complex `2 × 2` matrix of finite order is `ιC` of an algebraic number. -/
theorem trace_mem_range_of_pow_eq_one (ιC : Qbar →ₐ[ℚ] ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ) {n : ℕ}
    (hn : n ≠ 0) (hM : M ^ n = 1) : M.trace ∈ ιC.range := by
  rw [Matrix.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  refine Subalgebra.multiset_sum_mem _ fun r hr => ?_
  have hroot : M.charpoly.IsRoot r := (Polynomial.mem_roots (Matrix.charpoly_monic M).ne_zero).mp hr
  have hspec : r ∈ spectrum ℂ M := Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hroot
  have hpow : r ^ n ∈ spectrum ℂ (M ^ n) := spectrum.pow_mem_pow M n hspec
  rw [hM, spectrum.one_eq, Set.mem_singleton_iff] at hpow
  obtain ⟨a, ha⟩ := mem_range_of_pow_eq_one ιC hn hpow
  exact ⟨a, ha⟩

end ArtinHelpers


section ArtinHelpers2

open ZInQ.Contrib.G9.PkgI4

/-- The subring of `ℂ` generated by `ιC(ℚ̄)` and a finite set `E`. -/
noncomputable def genRing (ιC : Qbar →ₐ[ℚ] ℂ) (E : Set ℂ) : Subring ℂ :=
  (MvPolynomial.eval₂Hom (ιC : Qbar →+* ℂ) (fun e : E => (e : ℂ))).range

theorem mem_genRing_of_mem (ιC : Qbar →ₐ[ℚ] ℂ) {E : Set ℂ} {e : ℂ} (he : e ∈ E) :
    e ∈ genRing ιC E :=
  ⟨MvPolynomial.X ⟨e, he⟩, by simp⟩

theorem iotaC_mem_genRing (ιC : Qbar →ₐ[ℚ] ℂ) (E : Set ℂ) (a : Qbar) : ιC a ∈ genRing ιC E :=
  ⟨MvPolynomial.C a, by simp⟩

/-- **Specialization (Hilbert's Nullstellensatz).** A ring map `genRing ιC E → ℚ̄` that is `ιC⁻¹`
on `ιC(ℚ̄)`. -/
theorem exists_specialization (ιC : Qbar →ₐ[ℚ] ℂ) (E : Set ℂ) [Finite E] :
    ∃ φ : genRing ιC E →+* Qbar, ∀ a : Qbar, φ ⟨ιC a, iotaC_mem_genRing ιC E a⟩ = a := by
  classical
  let F := MvPolynomial.eval₂Hom (ιC : Qbar →+* ℂ) (fun e : E => (e : ℂ))
  have hI : RingHom.ker F ≠ ⊤ := by
    intro h
    have : (1 : MvPolynomial E Qbar) ∈ RingHom.ker F := h ▸ Submodule.mem_top
    simp [RingHom.mem_ker] at this
  obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal Qbar hm
  let ev : MvPolynomial E Qbar →+* Qbar := MvPolynomial.eval x
  have hle : RingHom.ker F.rangeRestrict ≤ RingHom.ker ev := by
    rw [RingHom.ker_rangeRestrict]
    intro f hf
    have hfm : f ∈ m := hIm hf
    rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hfm
    rw [RingHom.mem_ker]
    exact hfm
  let e := RingHom.quotientKerEquivOfSurjective (F.rangeRestrict_surjective)
  refine ⟨(Ideal.Quotient.lift _ ev (fun a ha => RingHom.mem_ker.mp (hle ha))).comp e.symm.toRingHom, fun a => ?_⟩
  have h1 : (⟨ιC a, iotaC_mem_genRing ιC E a⟩ : genRing ιC E) = F.rangeRestrict (MvPolynomial.C a) := by
    apply Subtype.ext; simp [F]
  rw [h1]
  change Ideal.Quotient.lift _ ev (fun a ha => RingHom.mem_ker.mp (hle ha)) (e.symm (F.rangeRestrict (MvPolynomial.C a))) = a
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  simp [ev]

/-- A homomorphism to `GL_n(ℂ)` with entries in a subring `A` lifts to `GL_n(A)`. -/
def liftGLSub {G : Type*} [Group G] {n : ℕ} (A : Subring ℂ) (f : G →* GL (Fin n) ℂ)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) ℂ) i j ∈ A) : G →* GL (Fin n) A :=
  let M : G → Matrix (Fin n) (Fin n) A := fun g i j => ⟨(f g : Matrix (Fin n) (Fin n) ℂ) i j, h g i j⟩
  have hM : ∀ g, (M g).map A.subtype = (f g : Matrix (Fin n) (Fin n) ℂ) := fun g => by ext i j; rfl
  have hinj : Function.Injective (fun B : Matrix (Fin n) (Fin n) A => B.map A.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hmul : ∀ g g', M (g * g') = M g * M g' := fun g g' => hinj (by
    simp only [Matrix.map_mul, hM, map_mul, Units.val_mul])
  have hone : M 1 = 1 := hinj (by simp only [hM, map_one, Units.val_one, Matrix.map_one,
    map_zero, map_one])
  { toFun := fun g => ⟨M g, M g⁻¹, by rw [← hmul, mul_inv_cancel, hone],
      by rw [← hmul, inv_mul_cancel, hone]⟩
    map_one' := Units.ext hone
    map_mul' := fun g g' => Units.ext (hmul g g') }

theorem liftGLSub_coe {G : Type*} [Group G] {n : ℕ} (A : Subring ℂ) (f : G →* GL (Fin n) ℂ)
    (h : ∀ g i j, (f g : Matrix (Fin n) (Fin n) ℂ) i j ∈ A) (g : G) (i j : Fin n) :
    (((liftGLSub A f h g : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) i j : ℂ) =
      (f g : Matrix (Fin n) (Fin n) ℂ) i j := rfl

/-- **Maschke.** A `GaloisRep` with finite image is semisimple. -/
theorem isSemisimple_of_finite_range {ℓ n : ℕ} [Fact ℓ.Prime] (ρ : GaloisRep ℓ n)
    (h : (Set.range ρ.toHom).Finite) : ρ.IsSemisimple := by
  classical
  let H := ρ.toHom.range
  haveI : Finite H := by
    have : (H : Set (GL (Fin n) (PadicAlgCl ℓ))) = Set.range ρ.toHom := MonoidHom.coe_range _
    exact Set.Finite.to_subtype (this ▸ h)
  haveI : NeZero (Nat.card H : PadicAlgCl ℓ) := ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  let ρH : Representation (PadicAlgCl ℓ) H (Fin n → PadicAlgCl ℓ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ) ≃ₐ[PadicAlgCl ℓ] _).toMonoidHom.comp
      ((Units.coeHom _).comp H.subtype)
  have hρH : ∀ (x : H), ρH x = Matrix.toLin' ((x : GL (Fin n) (PadicAlgCl ℓ)) :
      Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) := fun _ => rfl
  have hss : IsSemisimpleModule (MonoidAlgebra (PadicAlgCl ℓ) H) ρH.asModule := inferInstance
  rw [isSemisimpleModule_iff, ← ρH.mapSubmodule.complementedLattice_iff] at hss
  have hmem : ∀ W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ),
      W ∈ ρH.invtSubmodule ↔ ∀ σ, W.map (Matrix.toLin' (ρ.mat σ)) ≤ W := by
    intro W
    rw [Representation.mem_invtSubmodule]
    constructor
    · intro hW σ
      have := hW ⟨ρ.toHom σ, σ, rfl⟩
      rw [Module.End.mem_invtSubmodule, hρH] at this
      rw [Submodule.map_le_iff_le_comap]
      exact this
    · rintro hW ⟨_, σ, rfl⟩
      rw [Module.End.mem_invtSubmodule, hρH, ← Submodule.map_le_iff_le_comap]
      exact hW σ
  intro W hW
  obtain ⟨b, hb⟩ := hss.exists_isCompl ⟨W, (hmem W).mpr hW⟩
  refine ⟨b.1, ⟨?_, ?_⟩, (hmem b.1).mp b.2⟩
  · rw [disjoint_iff]
    exact congrArg Subtype.val hb.inf_eq_bot
  · rw [codisjoint_iff]
    exact congrArg Subtype.val hb.sup_eq_top

/-- Every prime `p` has an arithmetic Frobenius (from the kernel's Chebotarev files). -/
theorem exists_arithFrob (p : ℕ) (hp : p.Prime) :
    ∃ (v : ValuationSubring Qbar) (τ : GQ), LiesOver v p ∧ IsArithFrob τ v p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨P, -, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := ZInQ.Contrib.ChebFD.C10.Zbar)
    (Ideal.span {(p : ℤ)}) ⊥ (by simp)
  obtain ⟨h, hh⟩ := ZInQ.Contrib.ChebFD.C10.frobExistsAt_of_finite
    ZInQ.Contrib.ChebFD.C10.frobExistsFinite p P hPp
  obtain ⟨hv, hτ⟩ := ZInQ.Contrib.ChebFD.HSyn.liesOver_and_isArithFrob P h p hp hPp hh
  exact ⟨_, h, hv, hτ⟩

end ArtinHelpers2


section ArtinMain

open ZInQ.Contrib.G9.PkgI4

/-- **`ArtinTransport`, proved**: specialize the entries of Deligne–Serre's `ρ_f` to `ℚ̄`
(Nullstellensatz, identity on `ιC(ℚ̄)`), apply `ιL`; semisimple by Maschke; `ε = det`. -/
theorem artinTransport_proof : ArtinTransport := by
  intro hDS ℓ _ ιC ιL N χ g hN hg
  classical
  obtain ⟨ρc, hcont, hfin, hloc⟩ := hDS N χ g hN hg
  let E : Set ℂ := ⋃ M ∈ Set.range ρc,
    Set.range fun ij : Fin 2 × Fin 2 => (M : Matrix (Fin 2) (Fin 2) ℂ) ij.1 ij.2
  haveI : Finite E := (hfin.biUnion fun M _ => Set.finite_range _).to_subtype
  have hmem : ∀ σ i j, (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j ∈ genRing ιC E := fun σ i j =>
    mem_genRing_of_mem ιC (Set.mem_biUnion (Set.mem_range_self σ) ⟨(i, j), rfl⟩)
  obtain ⟨φ, hφ⟩ := exists_specialization ιC E
  let ρA := liftGLSub (genRing ιC E) ρc hmem
  let g' : genRing ιC E →+* PadicAlgCl ℓ := ιL.toRingHom.comp φ
  let ρh : GQ →* GL (Fin 2) (PadicAlgCl ℓ) := (Matrix.GeneralLinearGroup.map g').comp ρA
  have hentry : ∀ σ i j, (ρh σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) i j =
      g' ⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ := fun _ _ _ => rfl
  have hker : ∀ σ, ρc σ = 1 → ρh σ = 1 := by
    intro σ h
    apply Units.ext
    ext i j
    rw [hentry]
    have hval : (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = if i = j then 1 else 0 := by
      rw [h, Units.val_one, Matrix.one_apply]
    by_cases hij : i = j
    · have : (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ : genRing ιC E) = 1 :=
        Subtype.ext (by change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = 1; rw [hval, if_pos hij])
      rw [this, map_one, Units.val_one, Matrix.one_apply, if_pos hij]
    · have : (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j, hmem σ i j⟩ : genRing ιC E) = 0 :=
        Subtype.ext (by change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i j = 0; rw [hval, if_neg hij])
      rw [this, map_zero, Units.val_one, Matrix.one_apply, if_neg hij]
  have hopen : IsOpen (ρc.ker : Set GQ) := by
    have hcl : IsClosed (ρc.ker : Set GQ) := by
      have : (ρc.ker : Set GQ) = ρc ⁻¹' {1} := by ext; simp
      rw [this]; exact isClosed_singleton.preimage hcont
    haveI : Finite ρc.range := by
      have : (ρc.range : Set (GL (Fin 2) ℂ)) = Set.range ρc := MonoidHom.coe_range ρc
      exact Set.Finite.to_subtype (this ▸ hfin)
    exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  have hρhc : Continuous ρh := by
    refine continuous_of_continuousAt_one _ ?_
    rw [ContinuousAt, map_one]
    exact tendsto_nhds_of_eventually_eq
      (Filter.mem_of_superset (hopen.mem_nhds ρc.ker.one_mem) fun σ hσ => hker σ hσ)
  have hdep : ∀ σ σ', ρc σ = ρc σ' → ρh σ = ρh σ' := by
    intro σ σ' h
    have h1 : ρc (σ⁻¹ * σ') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := hker _ h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hρfin : (Set.range ρh).Finite := by
    refine (hfin.image fun M => ρh (Function.invFun ρc M)).subset ?_
    rintro _ ⟨σ, rfl⟩
    refine ⟨ρc σ, ⟨σ, rfl⟩, hdep _ _ ?_⟩
    exact Function.invFun_eq ⟨σ, rfl⟩
  let ρ : GaloisRep ℓ 2 := ⟨ρh, hρhc⟩
  refine ⟨ρ, isSemisimple_of_finite_range ρ hρfin, ?_, ?_⟩
  · intro p hp hpNl
    have hpN : ¬ p ∣ N := fun h => hpNl (Dvd.dvd.mul_right h ℓ)
    obtain ⟨hun, hfr⟩ := hloc p hp hpN
    refine ⟨fun v hv σ hσ => hker _ (hun v hv σ hσ), ?_⟩
    obtain ⟨v₀, τ₀, hv₀, hτ₀⟩ := exists_arithFrob p hp
    have htr₀ := (hfr v₀ τ₀ hv₀ hτ₀).1
    -- `ρc τ₀` has finite order
    haveI : Finite ρc.range := by
      have : (ρc.range : Set (GL (Fin 2) ℂ)) = Set.range ρc := MonoidHom.coe_range ρc
      exact Set.Finite.to_subtype (this ▸ hfin)
    let x : ρc.range := ⟨ρc τ₀, τ₀, rfl⟩
    have hx : IsOfFinOrder x := isOfFinOrder_of_finite x
    have hn : orderOf x ≠ 0 := hx.orderOf_pos.ne'
    have hpow : (ρc τ₀ : Matrix (Fin 2) (Fin 2) ℂ) ^ orderOf x = 1 := by
      have h1 := congrArg Subtype.val (pow_orderOf_eq_one x)
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
      rw [← Units.val_pow_eq_pow_val]
      change ((x : GL (Fin 2) ℂ) ^ orderOf x : GL (Fin 2) ℂ).val = 1
      rw [h1, Units.val_one]
    obtain ⟨α, hα'⟩ := trace_mem_range_of_pow_eq_one ιC _ hn hpow
    have hα : ιC α = (ρc τ₀ : Matrix (Fin 2) (Fin 2) ℂ).trace := hα'
    refine ⟨α, by rw [hα, htr₀], fun v σ hv hσ => ?_⟩
    have htr := (hfr v σ hv hσ).1
    have hsum : (∑ i, (⟨(ρc σ : Matrix (Fin 2) (Fin 2) ℂ) i i, hmem σ i i⟩ : genRing ιC E)) =
        ⟨ιC α, iotaC_mem_genRing ιC E α⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      change (ρc σ : Matrix (Fin 2) (Fin 2) ℂ).trace = ιC α
      rw [htr, ← htr₀, hα]
    change (Matrix.trace fun i j => (ρh σ : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) i j) = ιL α
    simp only [Matrix.trace, Matrix.diag, hentry, ← map_sum, hsum, g', RingHom.comp_apply, hφ]
    rfl
  · refine ⟨Matrix.GeneralLinearGroup.det.comp ρh,
      (hρfin.image Matrix.GeneralLinearGroup.det).subset
        (by rintro _ ⟨σ, rfl⟩; exact ⟨ρh σ, ⟨σ, rfl⟩, rfl⟩), fun σ => ?_⟩
    simp only [sub_self, zpow_zero, mul_one]
    rfl

end ArtinMain



/-! ## §18. H-22 and H-10 closed

`R14Det` from Diamond–Shurman's two printed theorems (all three glue Props proved), and `EigenformHT`
from its newform case, the kernel's I4-L5 and the same two printed theorems. -/

section Closed

open ZInQ.Contrib.G9.PkgI4

/-- **H-22 closed.** `R14Det` from the two printed theorems `DSThm965` (Deligne, via Diamond–Shurman
Thm 9.6.5) and `DSThm966` (Deligne–Serre, via Diamond–Shurman Thm 9.6.6) only. -/
theorem r14Det_of_printed (hD : DSThm965) (hDS : DSThm966) : G0Galois.R14Det :=
  r14Det_of_wt (artinTransport_proof hDS)
    (r14DetWtGe2_of_ds hD semisimplification2_proof detFromFrobenius_proof)

/-- **H-10 from its newform case and the kernel's leaves** (`NewformOfEigenform` = I4-L5,
`EigenformRepExists` = R14 without the determinant). -/
theorem eigenformHT_of_kato (hNew : EigenformHTNew) (hL5 : NewformOfEigenform)
    (hR : EigenformRepExists) : EigenformHT :=
  eigenformHT_of_new hNew hL5 hR attachedConj_proof htConj_proof

/-- `EigenformRepExists` (R14 without the determinant) from `R14Det`. -/
theorem eigenformRepExists_of_r14Det (h : G0Galois.R14Det) : EigenformRepExists := by
  intro ℓ _ ιC ιL N k χ g hN hk hg
  obtain ⟨ρ, hss, hatt, -⟩ := h ℓ ιC ιL N k χ g hN hk hg
  exact ⟨ρ, hss, hatt⟩

/-- **H-10 from its newform case, the kernel's I4-L5 and Diamond–Shurman's two printed theorems.** -/
theorem eigenformHT_of_kato_ds (hNew : EigenformHTNew) (hL5 : NewformOfEigenform)
    (hD : DSThm965) (hDS : DSThm966) : EigenformHT :=
  eigenformHT_of_kato hNew hL5 (eigenformRepExists_of_r14Det (r14Det_of_printed hD hDS))

end Closed


/-! ## Summary: six of the seven rows from the published-form leaves (and Kato's newform case) -/

/-- **The p-adic Hodge theory rows of the frontier.** H-52, H-32, H-8, H-22, H-51 from the seven
published-form leaves; H-10 also from `EigenformHTNew` (Kato's theorem for newforms, not statable in
Mathlib today) and the kernel's leaf I4-L5 `NewformOfEigenform`. (H-9 needs `B_st`.) -/
theorem hodge_rows_of_leaves (hT : TateTwistInvariants) (hA : AxSenTate)
    (hHT : HodgeTateDecompAbVar) (hdR : DeRhamH1AbVarT)
    (hF : ∀ (p : ℕ) [Fact p.Prime], FontaineDRTannakian p) (hD : DSThm965) (hDS : DSThm966)
    (hNew : EigenformHTNew) (hL5 : NewformOfEigenform) :
    G0Galois.FiniteImageHT ∧ (∀ (p : ℕ) [Fact p.Prime], T23_FontaineClosure p) ∧
      ZInQ.Contrib.R10.DeRhamComparisonHT ∧ G0Galois.R14Det ∧ G0Galois.SenTwist ∧ EigenformHT :=
  ⟨finiteImageHT_of_tate hT hA, t23_all_of_fontaine hF, deRhamComparisonHT_of_leavesT hHT hT hA hdR,
    r14Det_of_printed hD hDS, senTwist_of_tate hT hA, eigenformHT_of_kato_ds hNew hL5 hD hDS⟩

end

end ZInQ.Contrib.HodgeSplit

#print axioms ZInQ.Contrib.HodgeSplit.finiteImageHT_of_tate
#print axioms ZInQ.Contrib.HodgeSplit.deRhamComparisonHT_of_leaves
#print axioms ZInQ.Contrib.HodgeSplit.t23_all_of_fontaine
#print axioms ZInQ.Contrib.HodgeSplit.r14Det_of_ds
#print axioms ZInQ.Contrib.HodgeSplit.panBerger_of_templates
#print axioms ZInQ.Contrib.HodgeSplit.eigenformHT_of_new
#print axioms ZInQ.Contrib.HodgeSplit.senTwist_of_glue
#print axioms ZInQ.Contrib.HodgeSplit.htWeightsUnique_proof
#print axioms ZInQ.Contrib.HodgeSplit.htConj_proof
#print axioms ZInQ.Contrib.HodgeSplit.semisimplification2_proof
#print axioms ZInQ.Contrib.HodgeSplit.deRhamComparisonHT_of_leavesT
#print axioms ZInQ.Contrib.HodgeSplit.senTwist_of_tate
#print axioms ZInQ.Contrib.HodgeSplit.attachedConj_proof
#print axioms ZInQ.Contrib.HodgeSplit.detFromFrobenius_proof
#print axioms ZInQ.Contrib.HodgeSplit.artinTransport_proof
#print axioms ZInQ.Contrib.HodgeSplit.r14Det_of_printed
#print axioms ZInQ.Contrib.HodgeSplit.eigenformHT_of_kato_ds
#print axioms ZInQ.Contrib.HodgeSplit.hodge_rows_of_leaves
