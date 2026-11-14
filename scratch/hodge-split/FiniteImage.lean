import ZInQKernel.Contrib.R10.Amend

/-!
# hodge-split, part 1: Tate's theorems and `FiniteImageHT` (frontier row H-52)

Task hodge-split, 2026-11-14.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

namespace ZInQ.Contrib.HodgeSplit

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module

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

end

end ZInQ.Contrib.HodgeSplit

#print axioms ZInQ.Contrib.HodgeSplit.finiteImageHT_of_tate
