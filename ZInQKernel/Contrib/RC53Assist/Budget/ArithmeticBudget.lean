import ZInQKernel.Contrib.CloudB3RC53.ClearingComplex.NewLocalModel
import ZInQKernel.Contrib.CloudB3RC53.RankCounts.LimitDeterminant
import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.Derivative
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.ChangeCondition
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Prints
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.TruncPrints

/-!
# Arithmetic inputs for the fixed-field Smith budget

The target is `ClearingComplex.BudgetInputsAt`, at the free-generator function
`ClearingComplex.fr₀`. This module does not consume an identification structure.
The arithmetic comparison is (5.7c), not the graph support comparison (5.6).

Manuscript `diophantine_zq.tex`, lines 5251–5386:
* the residual ordinary Kummer complex has dimensions `(2,d_K,d_K,2)`;
* two rank-two singular disks contribute at most eight residual dimensions;
* their integral degree-two cohomology has length at most `2 c_E`;
* the condition-change sequence supplies (5.7d).

The primary export is `budgetInputsAt_from_selmer_minimal`: the rank bound
uses the residual exact sequence, (5.7a), and positive central Smith valuations
as in lines 5355–5359. `SmallGradedModel` is retained only as an explicit
assumed degreewise rank-bound input for the nonminimal compatibility route.
No assertion about finiteness of the whole Tate–Shafarevich group is used.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace ZInQ.Contrib.RC53Assist.Budget

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Determinant (Lam OO SmithBlocks)

/-! ## Algebra of the singular quotient -/

section Singular

variable {R : Type} [CommRing R]

/-- The two rank-two singular summands, in degrees one and two. -/
def singularCx (X Y : Matrix (Fin 2) (Fin 2) R) :
    CochainComplex (ModuleCat.{0} R) ℤ :=
  HomologicalComplex.double (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
    (show (ComplexShape.up ℤ).Rel 1 2 from rfl)

/-- The direct product of the two singular cokernels. -/
abbrev singularJ (X Y : Matrix (Fin 2) (Fin 2) R) : Type :=
  ((Fin 2 → R) ⧸ LinearMap.range X.mulVecLin) ×
    ((Fin 2 → R) ⧸ LinearMap.range Y.mulVecLin)

private def singularKerIso (X Y : Matrix (Fin 2) (Fin 2) R) :
    kernel ((singularCx X Y).d 1 2) ≅
      kernel (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin)) :=
  kernelIsoOfEq (HomologicalComplex.double_d _ _ (by decide)) ≪≫
    kernelIsIsoComp (HomologicalComplex.doubleXIso₀ _ _).hom
      (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin) ≫
        (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv) ≪≫
    kernelCompMono (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv

private def singularCokerIso (X Y : Matrix (Fin 2) (Fin 2) R) :
    cokernel ((singularCx X Y).d 1 2) ≅
      cokernel (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin)) :=
  cokernelIsoOfEq ((HomologicalComplex.double_d _ _ (by decide)).trans
    (Category.assoc _ _ _).symm) ≪≫
    cokernelCompIsIso ((HomologicalComplex.doubleXIso₀ _ _).hom ≫
      ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
        (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≪≫
    cokernelEpiComp (HomologicalComplex.doubleXIso₀ _ _).hom
      (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))

private def singularH1Iso (X Y : Matrix (Fin 2) (Fin 2) R) :
    (singularCx X Y).homology 1 ≅
      ModuleCat.of R (LinearMap.ker (X.mulVecLin.prodMap Y.mulVecLin)) :=
  ((singularCx X Y).isoHomologyπ 0 1 (by simp)
    (HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide))).symm ≪≫
    (singularCx X Y).cyclesIsoSc' 0 1 2 (by simp) (by simp) ≪≫
      ShortComplex.cyclesIsoKernel _ ≪≫ singularKerIso X Y ≪≫ ModuleCat.kernelIsoKer _

private def singularH2QuotIso (X Y : Matrix (Fin 2) (Fin 2) R) :
    (singularCx X Y).homology 2 ≅
      ModuleCat.of R (((Fin 2 → R) × (Fin 2 → R)) ⧸
        LinearMap.range (X.mulVecLin.prodMap Y.mulVecLin)) :=
  (singularCx X Y).isoHomologyι 2 3 (by simp)
    (HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide)) ≪≫
    (singularCx X Y).opcyclesIsoSc' 1 2 3 (by simp) (by simp) ≪≫
      ShortComplex.opcyclesIsoCokernel _ ≪≫ singularCokerIso X Y ≪≫
        ModuleCat.cokernelIsoRangeQuotient _

private def quotientProdEquiv {A B : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (f : A →ₗ[R] A) (g : B →ₗ[R] B) :
    ((A × B) ⧸ LinearMap.range (f.prodMap g)) ≃ₗ[R]
      (A ⧸ LinearMap.range f) × (B ⧸ LinearMap.range g) := by
  let p : A × B →ₗ[R] (A ⧸ LinearMap.range f) × (B ⧸ LinearMap.range g) :=
    (LinearMap.range f).mkQ.prodMap (LinearMap.range g).mkQ
  have hp : Function.Surjective p :=
    Function.Surjective.prodMap (Submodule.mkQ_surjective _) (Submodule.mkQ_surjective _)
  have hk : LinearMap.ker p = LinearMap.range (f.prodMap g) := by
    ext x
    change ((LinearMap.range f).mkQ x.1, (LinearMap.range g).mkQ x.2) = 0 ↔
      ∃ a : A × B, (f a.1, g a.2) = x
    simp only [Prod.mk_eq_zero, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      LinearMap.mem_range]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(a, b), Prod.ext ha hb⟩
    · rintro ⟨⟨a, b⟩, h⟩
      exact ⟨⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩⟩
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (p.quotKerEquivOfSurjective hp)

/-- The upper cohomology of the two singular disks is their product cokernel. -/
def singularH2Equiv (X Y : Matrix (Fin 2) (Fin 2) R) :
    (singularCx X Y).homology 2 ≃ₗ[R] singularJ X Y :=
  (singularH2QuotIso X Y).toLinearEquiv.trans (quotientProdEquiv X.mulVecLin Y.mulVecLin)

private theorem singular_homology_zero (X Y : Matrix (Fin 2) (Fin 2) R)
    (n : ℤ) (hn1 : n ≠ 1) (hn2 : n ≠ 2) :
    Subsingleton ((singularCx X Y).homology n) := by
  apply ModuleCat.subsingleton_of_isZero
  exact (HomologicalComplex.sc (singularCx X Y) n).isZero_homology_of_isZero_X₂
    (HomologicalComplex.isZero_double_X
      (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
      (show (ComplexShape.up ℤ).Rel 1 2 from rfl) n hn1 hn2)

end Singular

section PadicSingular

private theorem singular_h1_zero (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    Subsingleton ((singularCx X Y).homology 1) := by
  have hinj : Function.Injective (X.mulVecLin.prodMap Y.mulVecLin) :=
    Function.Injective.prodMap (Matrix.mulVec_injective_of_det_ne_zero hX)
      (Matrix.mulVec_injective_of_det_ne_zero hY)
  have hk : LinearMap.ker (X.mulVecLin.prodMap Y.mulVecLin) = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have : Subsingleton (LinearMap.ker (X.mulVecLin.prodMap Y.mulVecLin)) := by
    rw [hk]
    infer_instance
  exact (singularH1Iso X Y).toLinearEquiv.toEquiv.subsingleton

private theorem coker_isTorsion {n : Type} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℤ_[2]) (hX : X.det ≠ 0) :
    Module.IsTorsion ℤ_[2] ((n → ℤ_[2]) ⧸ LinearMap.range X.mulVecLin) := by
  intro q
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ q
  refine ⟨⟨X.det, mem_nonZeroDivisors_of_ne_zero hX⟩, ?_⟩
  change X.det • (LinearMap.range X.mulVecLin).mkQ v = 0
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨X.adjugate.mulVec v, ?_⟩
  change X.mulVec (X.adjugate.mulVec v) = X.det • v
  rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem singularJ_isTorsion (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (hX : X.det ≠ 0) (hY : Y.det ≠ 0) : Module.IsTorsion ℤ_[2] (singularJ X Y) := by
  rintro ⟨x, y⟩
  obtain ⟨a, ha⟩ := @coker_isTorsion _ _ _ X hX x
  obtain ⟨b, hb⟩ := @coker_isTorsion _ _ _ Y hY y
  refine ⟨a * b, ?_⟩
  refine Prod.ext ?_ ?_
  · change (a * b) • x = 0
    rw [mul_comm, mul_smul, ha, smul_zero]
  · change (a * b) • y = 0
    rw [mul_smul, hb, smul_zero]

end PadicSingular

/-! ## Exactness and free rank; no arithmetic sequence is assumed -/

section Exact

variable {R : Type} [CommRing R]

private theorem functionExact_of_shortComplex (S : ShortComplex (ModuleCat.{0} R))
    (hS : S.Exact) : Function.Exact S.f.hom S.g.hom :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS

private theorem injective_of_exact_zero_left {A B C : Type}
    [AddCommGroup A] [Module R A] [Subsingleton A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) :
    Function.Injective g := by
  intro x y hxy
  have hz : g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨a, ha⟩ := (h (x - y)).mp hz
  have h0 : x - y = 0 := by
    rw [Subsingleton.elim a 0, map_zero] at ha
    exact ha.symm
  exact sub_eq_zero.mp h0

private theorem surjective_of_exact_zero_right {A B C : Type}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [Subsingleton C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) :
    Function.Surjective f := fun b => (h b).mp (Subsingleton.elim _ _)

private theorem exact_change_middle {A B C B' : Type}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup B'] [Module R B']
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) (e : B' ≃ₗ[R] B) :
    Function.Exact (e.symm.toLinearMap ∘ₗ f) (g ∘ₗ e.toLinearMap) := by
  intro b
  change g (e b) = 0 ↔ ∃ a, e.symm (f a) = b
  rw [h (e b)]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [ha, e.symm_apply_apply]⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← ha, e.apply_symm_apply]⟩

private theorem exact_change_source {A B C A' : Type}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup A'] [Module R A']
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) (e : A' ≃ₗ[R] A) :
    Function.Exact (f ∘ₗ e.toLinearMap) g := by
  intro b
  rw [h b]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨e.symm a, by simpa using ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨e a, ha⟩

private theorem exact_change_target {A B C C' : Type}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) (e : C ≃ₗ[R] C') :
    Function.Exact f (e.toLinearMap ∘ₗ g) := by
  intro b
  change e (g b) = 0 ↔ ∃ a, f a = b
  rw [← e.map_zero, e.injective.eq_iff]
  exact h b

private theorem finrank_eq_of_exact_torsion [IsDomain R] {A B C : Type}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hC : Module.IsTorsion R C) :
    Module.finrank R A = Module.finrank R B := by
  have hr : Module.rank R (LinearMap.range g) = 0 := by
    rw [rank_eq_zero_iff]
    intro c
    obtain ⟨a, ha⟩ := @hC c.1
    exact ⟨a, nonZeroDivisors.coe_ne_zero a, Subtype.ext ha⟩
  have h := LinearMap.rank_range_add_rank_ker g
  rw [hr, zero_add, hfg.linearMap_ker_eq] at h
  have he := (LinearEquiv.ofInjective f hf).finrank_eq
  exact he.trans (congrArg Cardinal.toNat h)

end Exact

/-! ## Determinant lengths and the retained precision

The following local determinant-length proof uses the Smith-normal-form
argument of `ZInQKernel.Contrib.OneProof.RC.Determinant.SmithLength`, at the
base source revision, and the corresponding Mathlib submodule bases.
-/

private theorem length_coker_eq_ord_det {R : Type} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] {n : Type} [Fintype n] [DecidableEq n]
    (X : Matrix n n R) (hX : X.det ≠ 0) :
    Module.length R ((n → R) ⧸ LinearMap.range X.mulVecLin) = Ring.ord R X.det := by
  classical
  let N := LinearMap.range X.mulVecLin
  let e : (n → R) ≃ₗ[R] N :=
    LinearEquiv.ofInjective X.mulVecLin (Matrix.mulVec_injective_of_det_ne_zero hX)
  have h : Module.finrank R N = Module.finrank R (n → R) := e.finrank_eq.symm
  let b := Pi.basisFun R n
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  let e' : (n → R) ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
  let f : (n → R) →ₗ[R] (n → R) := N.subtype ∘ₗ e'.toLinearMap
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    simp only [f, e', LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.refl_apply, Submodule.subtype_apply]
    exact Submodule.smithNormalFormBotBasis_def b h i
  have hf : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Module.Basis.repr_self,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hX' : X.mulVecLin = N.subtype ∘ₗ e.toLinearMap := by ext v; rfl
  have hassoc : Associated X.det (∏ i, a i) := by
    rw [← hf, ← LinearMap.det_toLin', Matrix.toLin'_apply', hX']
    exact LinearMap.associated_det_comp_equiv _ _ _
  have hp : Ring.ord R (∏ i, a i) = ∑ i, Ring.ord R (a i) := by
    have hnz : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h
    have hp' : ∀ s : Finset n, Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi,
          Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hnz i)), ih]
    exact hp' Finset.univ
  rw [(N.quotientEquivPiSpan b h).length_eq, Module.length_pi_of_fintype,
    Ring.ord_eq_of_associated hassoc, hp]
  rfl

private theorem length_singularJ (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (hX : X.det ≠ 0) (hY : Y.det ≠ 0) :
    Module.length ℤ_[2] (singularJ X Y) =
      ((X.det.valuation + Y.det.valuation : ℕ) : ℕ∞) := by
  rw [Module.length_prod, length_coker_eq_ord_det X hX, length_coker_eq_ord_det Y hY,
    SmithCx.ord_eq_valuation hX, SmithCx.ord_eq_valuation hY, Nat.cast_add]

/-- The exact integral information furnished by two singular disks. -/
def SingularBounds (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]) (cE : ℕ) : Prop :=
  Subsingleton ((singularCx X Y).homology 0) ∧
  Subsingleton ((singularCx X Y).homology 1) ∧
  Subsingleton ((singularCx X Y).homology 3) ∧
  Module.IsTorsion ℤ_[2] ((singularCx X Y).homology 2) ∧
  Module.length ℤ_[2] ((singularCx X Y).homology 2) ≤ 2 * cE

/-- Nonzero determinants of bounded valuation give the integral singular bounds. -/
theorem singularBounds_of_det (X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]) (cE : ℕ)
    (hX : X.det ≠ 0) (hY : Y.det ≠ 0)
    (hcX : X.det.valuation ≤ cE) (hcY : Y.det.valuation ≤ cE) :
    SingularBounds X Y cE := by
  refine ⟨singular_homology_zero X Y 0 (by decide) (by decide),
    singular_h1_zero X Y hX hY,
    singular_homology_zero X Y 3 (by decide) (by decide), ?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := @singularJ_isTorsion X Y hX hY (singularH2Equiv X Y x)
    refine ⟨a, ?_⟩
    rw [Submonoid.smul_def] at ha ⊢
    apply (singularH2Equiv X Y).injective
    rw [map_smul, map_zero]
    exact ha
  · rw [(singularH2Equiv X Y).length_eq, length_singularJ X Y hX hY]
    exact_mod_cast (show X.det.valuation + Y.det.valuation ≤ 2 * cE by omega)

/-- The singular bounds follow already from one retained coefficient precision at each place. -/
theorem singularBounds_of_retained (X₀ Y₀ X Y : Matrix (Fin 2) (Fin 2) ℤ_[2]) (cE : ℕ)
    (hXX : ∀ i j, X₀ i j - X i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)})
    (hYY : ∀ i j, Y₀ i j - Y i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)})
    (hX₀ : X₀.det ≠ 0) (hY₀ : Y₀.det ≠ 0)
    (hcX₀ : X₀.det.valuation ≤ cE) (hcY₀ : Y₀.det.valuation ≤ cE) :
    SingularBounds X Y cE := by
  obtain ⟨hX, hcX⟩ := singularDiskLimit_proof X₀ X cE hXX hX₀ hcX₀
  obtain ⟨hY, hcY⟩ := singularDiskLimit_proof Y₀ Y cE hYY hY₀ hcY₀
  exact singularBounds_of_det X Y cE hX hY hcX hcY

section ResidualSingular

variable {k : Type} [Field k]

private theorem singular_finiteDimensional (X Y : Matrix (Fin 2) (Fin 2) k) (n : ℤ) :
    FiniteDimensional k ((singularCx X Y).homology n) := by
  by_cases hn1 : n = 1
  · subst n
    exact LinearEquiv.finiteDimensional (singularH1Iso X Y).toLinearEquiv.symm
  by_cases hn2 : n = 2
  · subst n
    exact LinearEquiv.finiteDimensional (singularH2QuotIso X Y).toLinearEquiv.symm
  have := singular_homology_zero X Y n hn1 hn2
  infer_instance

/-- Regardless of its residual differential, two rank-two disks contribute at most eight. -/
theorem residual_singular_bound (X Y : Matrix (Fin 2) (Fin 2) k) :
    ∑ n : Fin 4, Module.finrank k ((singularCx X Y).homology (n : ℤ)) ≤ 8 := by
  have := singular_homology_zero X Y 0 (by decide) (by decide)
  have := singular_homology_zero X Y 3 (by decide) (by decide)
  have h1 := Submodule.finrank_le (LinearMap.ker (X.mulVecLin.prodMap Y.mulVecLin))
  have h2 := Submodule.finrank_quotient_add_finrank
    (LinearMap.range (X.mulVecLin.prodMap Y.mulVecLin))
  have hV : Module.finrank k ((Fin 2 → k) × (Fin 2 → k)) = 4 := by
    simp [Module.finrank_prod]
  simp only [Fin.sum_univ_four]
  change Module.finrank k ((singularCx X Y).homology 0) +
    Module.finrank k ((singularCx X Y).homology 1) +
    Module.finrank k ((singularCx X Y).homology 2) +
    Module.finrank k ((singularCx X Y).homology 3) ≤ 8
  have h0 : Module.finrank k ((singularCx X Y).homology 0) = 0 :=
    Module.finrank_zero_of_subsingleton
  have h3 : Module.finrank k ((singularCx X Y).homology 3) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [h0, h3, (singularH1Iso X Y).toLinearEquiv.finrank_eq,
    (singularH2QuotIso X Y).toLinearEquiv.finrank_eq]
  change 0 + Module.finrank k (LinearMap.ker (X.mulVecLin.prodMap Y.mulVecLin)) +
    Module.finrank k (((Fin 2 → k) × (Fin 2 → k)) ⧸
      LinearMap.range (X.mulVecLin.prodMap Y.mulVecLin)) + 0 ≤ 8
  rw [hV] at h1 h2
  omega

end ResidualSingular

/-! ## Redundant free-rank assumptions at the fixed generator pattern -/

private theorem isTorsion_of_length_le {M : Type} [AddCommGroup M] [Module ℤ_[2] M]
    (m : ℕ) (hM : Module.length ℤ_[2] M ≤ m) : Module.IsTorsion ℤ_[2] M := by
  classical
  intro x
  by_contra hx
  let f : ℤ_[2] →ₗ[ℤ_[2]] M := LinearMap.toSpanSingleton ℤ_[2] M x
  have hf : Function.Injective f := by
    intro a b hab
    change a • x = b • x at hab
    have hc : (a - b) • x = 0 := by rw [sub_smul, hab, sub_self]
    by_cases h : a - b = 0
    · exact sub_eq_zero.mp h
    · exfalso
      exact hx ⟨⟨a - b, mem_nonZeroDivisors_of_ne_zero h⟩,
        by simpa only [Submonoid.smul_def] using hc⟩
  let I : Submodule ℤ_[2] ℤ_[2] := Ideal.span {(2 : ℤ_[2]) ^ (m + 1)}
  have hI : Module.length ℤ_[2] (ℤ_[2] ⧸ I) = (m + 1 : ℕ) := by
    change Ring.ord ℤ_[2] ((2 : ℤ_[2]) ^ (m + 1)) = (m + 1 : ℕ)
    have h2 : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] :=
      mem_nonZeroDivisors_of_ne_zero (by norm_num)
    have hp : Irreducible (2 : ℤ_[2]) := by
      simpa using (PadicInt.irreducible_p (p := 2))
    rw [Ring.ord_pow h2, Ring.ord_of_irreducible hp]
    simp
  have hn : ((m + 1 : ℕ) : ℕ∞) ≤ m := by
    calc
      ((m + 1 : ℕ) : ℕ∞) = Module.length ℤ_[2] (ℤ_[2] ⧸ I) := hI.symm
      _ ≤ Module.length ℤ_[2] ℤ_[2] :=
        Module.length_le_of_surjective I.mkQ I.mkQ_surjective
      _ ≤ Module.length ℤ_[2] M := Module.length_le_of_injective f hf
      _ ≤ m := hM
  have hn' : m + 1 ≤ m := by exact_mod_cast hn
  omega

open ZInQ.Contrib.CloudB3RC53.ClearingComplex (BudgetInputsAt fr₀)

/-- At the fixed generator pattern, the two free-rank hypotheses in the budget are redundant.
The proof uses only the remaining original fields, not an arithmetic corank assertion. -/
theorem budgetInputsAt_of_rankless {S : Type} [CommRing S] (B : SmithBlocks S OO)
    (dK hK cE tK : ℕ)
    (hrank : ∑ k : Fin 4, Module.finrank ℤ_[2] (centralCx B fr₀ k) ≤ 2 * dK + 12)
    {H1C H2C J H3C : Type} [AddCommGroup H1C] [Module ℤ_[2] H1C]
    [AddCommGroup H2C] [Module ℤ_[2] H2C] [AddCommGroup J] [Module ℤ_[2] J]
    [AddCommGroup H3C] [Module ℤ_[2] H3C]
    (e : centralH B fr₀ 1 ≃ₗ[ℤ_[2]] H1C)
    (i : H2C →ₗ[ℤ_[2]] centralH B fr₀ 2) (j : centralH B fr₀ 2 →ₗ[ℤ_[2]] J)
    (δ : J →ₗ[ℤ_[2]] H3C) (l : H3C →ₗ[ℤ_[2]] centralH B fr₀ 3)
    (hseq : Function.Injective i ∧ Function.Exact i j ∧ Function.Exact j δ ∧
      Function.Exact δ l ∧ Function.Surjective l)
    (ht1 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H1C) = tK)
    (ht3 : Module.length ℤ_[2] H3C = tK)
    (hh2 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] H2C) = hK)
    (hJ : Module.length ℤ_[2] J ≤ 2 * cE) :
    BudgetInputsAt B fr₀ dK hK cE tK := by
  have hr1 : Module.finrank ℤ_[2] H1C = 1 := by
    rw [← e.finrank_eq, finrank_centralH]
    rfl
  have hr2 : Module.finrank ℤ_[2] H2C = 1 := by
    rw [finrank_eq_of_exact_torsion i j hseq.1 hseq.2.1
      (isTorsion_of_length_le (2 * cE) hJ), finrank_centralH]
    rfl
  exact ⟨hrank, H1C, H2C, J, H3C, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, e, i, j, δ, l,
    hseq, ht1, ht3, hh2, hJ, hr1, hr2⟩

/-! ## Complementary dimensions from finite self-duality

This is the field-valued homology calculation used by
`ZInQKernel.Contrib.CloudB3RC53.GenuineInst.DualHomology`. The local version
below uses Mathlib's explicit module homology and extension of linear forms.
It assumes no finite-dimensionality of continuous cochain terms.
-/

private abbrev bdrySub {R : Type} [CommRing R] {U V W : Type}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (f : U →ₗ[R] V) (g : V →ₗ[R] W) :
    Submodule R (LinearMap.ker g) :=
  (LinearMap.range f).comap (LinearMap.ker g).subtype

private def quotientEquivOfSurjective {R : Type} [CommRing R] {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    (M ⧸ LinearMap.ker f) ≃ₗ[R] N := f.quotKerEquivOfSurjective hf

private abbrev homologyQuot {R : Type} [CommRing R] {U V W : Type}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (f : U →ₗ[R] V) (g : V →ₗ[R] W) : Type :=
  ↥(LinearMap.ker g) ⧸ bdrySub f g

private def linearHomologyQuotEquiv {R : Type} [CommRing R]
    (S : ShortComplex (ModuleCat.{0} R)) :
    (LinearMap.ker S.g.hom ⧸ bdrySub S.f.hom S.g.hom) ≃ₗ[R] S.homology := by
  have hr : LinearMap.range S.moduleCatToCycles = bdrySub S.f.hom S.g.hom := by
    ext x
    rw [LinearMap.mem_range, Submodule.mem_comap, LinearMap.mem_range]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, congrArg Subtype.val ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, Subtype.ext ha⟩
  exact (Submodule.quotEquivOfEq _ _ hr.symm).trans
    S.moduleCatHomologyIso.toLinearEquiv.symm

private def relationHomologyQuotEquiv {R : Type} [CommRing R]
    (A : GCx R) (i' i j : ℤ) (hi : i' + 1 = i) (hj : i + 1 = j) :
    (LinearMap.ker (A.d i j hj) ⧸ bdrySub (A.d i' i hi) (A.d i j hj)) ≃ₗ[R]
      A.toCC.homology i := by
  let S := A.toCC.sc' i' i j
  have hf : S.f.hom = A.d i' i hi := by
    ext x
    exact A.toCC_d_hom i' i hi x
  have hg : S.g.hom = A.d i j hj := by
    ext x
    exact A.toCC_d_hom i j hj x
  have e := (linearHomologyQuotEquiv S).trans
    (A.toCC.homologyIsoSc' i' i j (by simp; omega)
      (by simpa using hj)).toLinearEquiv.symm
  rw [hf, hg] at e
  exact e

section DualField

variable {k : Type} [CommRing k] {U V W : Type}
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]

private def dualRestrict (f : U →ₗ[k] V) (g : V →ₗ[k] W) :
    LinearMap.ker f.dualMap →ₗ[k] Module.Dual k (LinearMap.ker g ⧸ bdrySub f g) where
  toFun φ := (bdrySub f g).liftQ (φ.1.comp (LinearMap.ker g).subtype) (by
    rintro x ⟨a, ha⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    change φ.1 (x : V) = 0
    have hx : (x : V) = f a := ha.symm
    rw [hx]
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp φ.2) a)
  map_add' φ ψ := by ext x; simp
  map_smul' c φ := by ext x; simp

private theorem dualRestrict_surjective (hk : IsField k) (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (hgf : ∀ a, g (f a) = 0) : Function.Surjective (dualRestrict f g) := by
  letI : Field k := hk.toField
  intro ψ
  obtain ⟨e, he⟩ := LinearMap.exists_extend (ψ.comp (bdrySub f g).mkQ)
  have hf : ∀ a, e (f a) = 0 := by
    intro a
    have h := LinearMap.congr_fun he ⟨f a, LinearMap.mem_ker.mpr (hgf a)⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero (bdrySub f g)
        (x := ⟨f a, LinearMap.mem_ker.mpr (hgf a)⟩)).mpr ⟨a, rfl⟩, map_zero]
  refine ⟨⟨e, LinearMap.mem_ker.mpr (LinearMap.ext hf)⟩, ?_⟩
  refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
  exact LinearMap.congr_fun he x

private theorem ker_dualRestrict (hk : IsField k) (f : U →ₗ[k] V) (g : V →ₗ[k] W) :
    LinearMap.ker (dualRestrict f g) = bdrySub g.dualMap f.dualMap := by
  letI : Field k := hk.toField
  ext φ
  rw [LinearMap.mem_ker, Submodule.mem_comap,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
  constructor
  · intro h x hx
    have hh := LinearMap.congr_fun h (Submodule.Quotient.mk ⟨x, hx⟩)
    exact hh
  · intro h
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    exact h x.1 x.2

private theorem ker_zsmul_eq {A B : Type} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] (L : A →ₗ[k] B) {c : ℤ} (hc : c * c = 1) :
    LinearMap.ker (c • L) = LinearMap.ker L := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.smul_apply]
  constructor
  · intro h
    have hh := congrArg (c • ·) h
    simpa only [smul_smul, hc, one_smul, smul_zero] using hh
  · intro h
    rw [h, smul_zero]

private theorem range_zsmul_eq {A B : Type} [AddCommGroup A] [Module k A]
    [AddCommGroup B] [Module k B] (L : A →ₗ[k] B) {c : ℤ} (hc : c * c = 1) :
    LinearMap.range (c • L) = LinearMap.range L := by
  ext y
  simp only [LinearMap.mem_range, LinearMap.smul_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨c • x, by rw [map_zsmul]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨c • x, by rw [map_zsmul, smul_smul, hc, one_smul]⟩

private theorem neg_sgn_square (n : ℤ) : (-(sgn n)) * (-(sgn n)) = 1 := by
  rw [neg_mul_neg, sgn_mul_self]

/-- Homology of the termwise dual over a field is the dual of complementary homology. -/
def dualHomologyEquiv (hk : IsField k) (A : GCx k) (m n : ℤ) :
    (dualCx A m).toCC.homology n ≃ₗ[k] Module.Dual k (A.toCC.homology (m - n)) := by
  let f := A.d (m - (n + 1)) (m - n) (by omega)
  let g := A.d (m - n) (m - (n - 1)) (by omega)
  have eA := relationHomologyQuotEquiv A (m - (n + 1)) (m - n)
    (m - (n - 1)) (by omega) (by omega)
  have eD := relationHomologyQuotEquiv (dualCx A m) (n - 1) n (n + 1) (by omega) rfl
  change homologyQuot ((-(sgn (n - 1))) • g.dualMap) ((-(sgn n)) • f.dualMap) ≃ₗ[k]
      (dualCx A m).toCC.homology n at eD
  unfold homologyQuot at eD
  rw [show bdrySub ((-(sgn (n - 1))) • g.dualMap) ((-(sgn n)) • f.dualMap) =
      (LinearMap.range ((-(sgn (n - 1))) • g.dualMap)).comap
        (LinearMap.ker ((-(sgn n)) • f.dualMap)).subtype from rfl,
    ker_zsmul_eq _ (neg_sgn_square n), range_zsmul_eq _ (neg_sgn_square (n - 1))] at eD
  let φ := dualRestrict f g
  have hφ : Function.Surjective φ :=
    dualRestrict_surjective hk f g (fun a => A.d_d _ _ _ _ _ a)
  have hkerφ : LinearMap.ker φ = bdrySub g.dualMap f.dualMap := ker_dualRestrict hk f g
  have ec := @quotientEquivOfSurjective k (inferInstance : CommRing k)
    (LinearMap.ker f.dualMap) (Module.Dual k (LinearMap.ker g ⧸ bdrySub f g))
    inferInstance inferInstance inferInstance inferInstance φ hφ
  have eQ := (Submodule.quotEquivOfEq _ _ hkerφ.symm).trans ec
  exact eD.symm.trans (eQ.trans eA.symm.dualMap)

end DualField

/-- The residual Kummer cohomology profile, with the degree-one dimension as its parameter. -/
def ResidualKummerProfile {k : Type} [CommRing k] (C : GCx k) : Prop :=
  (∀ n : Fin 4, Module.Finite k (C.toCC.homology (n : ℤ))) ∧
    ∀ n : Fin 4, Module.finrank k (C.toCC.homology (n : ℤ)) =
      (![2, Module.finrank k (C.toCC.homology 1),
        Module.finrank k (C.toCC.homology 1), 2] : Fin 4 → ℕ) n

/-- The entire profile (5.7a) follows from finite self-duality and the rational rank-two invariants.
Only degree-one finiteness is an input; no dimension is assumed in degrees two or three. -/
theorem residualKummerProfile_of_selfDuality {k : Type} [CommRing k] (hk : IsField k) (C : GCx k)
    (γ : C.toCC ⟶ (dualCx C 3).toCC) (hγ : QuasiIso γ)
    (e0 : C.toCC.homology 0 ≃ₗ[k] (Fin 2 → k))
    [Module.Finite k (C.toCC.homology 1)] : ResidualKummerProfile C := by
  let rk : CommRing k := inferInstance
  letI : Field k := hk.toField
  letI : CommRing k := rk
  letI : CommSemiring k := rk.toCommSemiring
  letI : Semiring k := rk.toSemiring
  have : FiniteDimensional k (C.toCC.homology 0) :=
    LinearEquiv.finiteDimensional e0.symm
  have ed2 := dualHomologyEquiv hk C 3 2
  have ed3 := dualHomologyEquiv hk C 3 3
  norm_num only at ed2 ed3
  let d2 : (dualCx C 3).toCC.homology 2 ≃ₗ[k] Module.Dual k (C.toCC.homology 1) :=
    { toFun := ed2
      invFun := ed2.symm
      left_inv := ed2.left_inv
      right_inv := ed2.right_inv
      map_add' := ed2.map_add
      map_smul' := fun r x => ed2.map_smul r x }
  let d3 : (dualCx C 3).toCC.homology 3 ≃ₗ[k] Module.Dual k (C.toCC.homology 0) :=
    { toFun := ed3
      invFun := ed3.symm
      left_inv := ed3.left_inv
      right_inv := ed3.right_inv
      map_add' := ed3.map_add
      map_smul' := fun r x => ed3.map_smul r x }
  let e2 : C.toCC.homology 2 ≃ₗ[k] Module.Dual k (C.toCC.homology 1) :=
    (asIso (HomologicalComplex.homologyMap γ 2)).toLinearEquiv.trans d2
  let e3 : C.toCC.homology 3 ≃ₗ[k] Module.Dual k (C.toCC.homology 0) :=
    (asIso (HomologicalComplex.homologyMap γ 3)).toLinearEquiv.trans d3
  have : FiniteDimensional k (C.toCC.homology 2) :=
    LinearEquiv.finiteDimensional e2.symm
  have : FiniteDimensional k (C.toCC.homology 3) :=
    LinearEquiv.finiteDimensional e3.symm
  have h0 : Module.finrank k (C.toCC.homology 0) = 2 := by
    rw [e0.finrank_eq]
    simp
  have h2 : Module.finrank k (C.toCC.homology 2) = Module.finrank k (C.toCC.homology 1) := by
    rw [e2.finrank_eq, Subspace.dual_finrank_eq]
  have h3 : Module.finrank k (C.toCC.homology 3) = 2 := by
    rw [e3.finrank_eq, Subspace.dual_finrank_eq]
    exact h0
  constructor
  · intro n
    fin_cases n <;> infer_instance
  · intro n
    fin_cases n
    · exact h0
    · rfl
    · exact h2
    · exact h3

/-! ## The scalar comparison consumed by the budget

The cochain comparison and its residual reduction are independent of any
identification or cancellation structure. The short exact sequences belong to
complexes. Their cohomology sequences are conclusions, never input fields.
-/

/-- Scalar integral and residual comparisons for the old complex in (5.7c).
The maps to the singular models are quasi-isomorphisms, not degreewise isomorphisms. -/
structure ArithmeticComparison {S : Type} [CommRing S] (B : SmithBlocks S OO) where
  X : Matrix (Fin 2) (Fin 2) ℤ_[2]
  Y : Matrix (Fin 2) (Fin 2) ℤ_[2]
  integral : ShortComplex (CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ)
  integral_exact : integral.ShortExact
  e1 : centralH B fr₀ 1 ≃ₗ[ℤ_[2]] integral.X₂.homology 1
  e2 : centralH B fr₀ 2 ≃ₗ[ℤ_[2]] integral.X₂.homology 2
  e3 : centralH B fr₀ 3 ≃ₗ[ℤ_[2]] integral.X₂.homology 3
  q : singularCx X Y ⟶ integral.X₃
  qis : QuasiIso q
  ordinaryRed : GCx (ZMod 2)
  residual : ShortComplex (CochainComplex (ModuleCat.{0} (ZMod 2)) ℤ)
  residual_exact : residual.ShortExact
  redSource : ordinaryRed.toCC ⟶ residual.X₁
  redSource_qis : QuasiIso redSource
  redMiddle : ∀ n : Fin 4,
    centralRed B fr₀ n ≃ₗ[ZMod 2] residual.X₂.homology (n : ℤ)
  redQ : singularCx (X.map PadicInt.toZMod) (Y.map PadicInt.toZMod) ⟶ residual.X₃
  redQ_qis : QuasiIso redQ

namespace ArithmeticComparison

variable {S : Type} [CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)

/-- The residual ordinary Selmer dimension; its arithmetic interpretation is Selmer two. -/
def dK : ℕ := Module.finrank (ZMod 2) (A.ordinaryRed.toCC.homology 1)

/-- The fixed-source degree-one torsion parameter. -/
def tK : ℕ := (Module.length ℤ_[2]
  (Submodule.torsion ℤ_[2] (A.integral.X₁.homology 1))).toNat

/-- The fixed-source degree-two torsion parameter, with no assertion about the whole
Tate–Shafarevich group. -/
def hK : ℕ := (Module.length ℤ_[2]
  (Submodule.torsion ℤ_[2] (A.integral.X₁.homology 2))).toNat

/-- The map on degree two transported into the central Smith coordinates. -/
def i : A.integral.X₁.homology 2 →ₗ[ℤ_[2]] centralH B fr₀ 2 :=
  A.e2.symm.toLinearMap ∘ₗ (HomologicalComplex.homologyMap A.integral.f 2).hom

/-- The singular projection in degree two. -/
def j : centralH B fr₀ 2 →ₗ[ℤ_[2]] A.integral.X₃.homology 2 :=
  (HomologicalComplex.homologyMap A.integral.g 2).hom ∘ₗ A.e2.toLinearMap

/-- The connecting map of the actual cochain short exact sequence. -/
def delta : A.integral.X₃.homology 2 →ₗ[ℤ_[2]] A.integral.X₁.homology 3 :=
  (A.integral_exact.δ 2 3 (by rfl)).hom

/-- The final map in degree three, in central Smith coordinates. -/
def l : A.integral.X₁.homology 3 →ₗ[ℤ_[2]] centralH B fr₀ 3 :=
  A.e3.symm.toLinearMap ∘ₗ (HomologicalComplex.homologyMap A.integral.f 3).hom

private theorem quotient_zero (h : SingularBounds A.X A.Y cE)
    (n : ℤ) (hn : n = 0 ∨ n = 1 ∨ n = 3) :
    Subsingleton (A.integral.X₃.homology n) := by
  have hq := A.qis
  have hz : Subsingleton ((singularCx A.X A.Y).homology n) := by
    rcases hn with rfl | rfl | rfl
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
  exact (asIso (HomologicalComplex.homologyMap A.q n)).toLinearEquiv.symm.toEquiv.subsingleton

/-- The complete exact sequence (5.7d) is derived from the cochain comparison and singular disks. -/
theorem exact_sequence (cE : ℕ) (h : SingularBounds A.X A.Y cE) :
    Function.Injective A.i ∧ Function.Exact A.i A.j ∧ Function.Exact A.j A.delta ∧
      Function.Exact A.delta A.l ∧ Function.Surjective A.l := by
  have := A.quotient_zero h 1 (Or.inr (Or.inl rfl))
  have := A.quotient_zero h 3 (Or.inr (Or.inr rfl))
  have hf2 := injective_of_exact_zero_left
    (A.integral_exact.δ 1 2 (by rfl)).hom
    (HomologicalComplex.homologyMap A.integral.f 2).hom
    (functionExact_of_shortComplex _ (A.integral_exact.homology_exact₁ 1 2 (by rfl)))
  have hf3 := surjective_of_exact_zero_right
    (HomologicalComplex.homologyMap A.integral.f 3).hom
    (HomologicalComplex.homologyMap A.integral.g 3).hom
    (functionExact_of_shortComplex _ (A.integral_exact.homology_exact₂ 3))
  refine ⟨A.e2.symm.injective.comp hf2, ?_, ?_, ?_, A.e3.symm.surjective.comp hf3⟩
  · exact exact_change_middle _ _
      (functionExact_of_shortComplex _ (A.integral_exact.homology_exact₂ 2)) A.e2
  · exact exact_change_source _ _
      (functionExact_of_shortComplex _ (A.integral_exact.homology_exact₃ 2 3 (by rfl))) A.e2
  · exact exact_change_target _ _
      (functionExact_of_shortComplex _ (A.integral_exact.homology_exact₁ 2 3 (by rfl))) A.e3.symm

/-- Degree-one cohomology is unchanged, as stated in (5.7d). -/
def h1Equiv (cE : ℕ) (h : SingularBounds A.X A.Y cE) :
    centralH B fr₀ 1 ≃ₗ[ℤ_[2]] A.integral.X₁.homology 1 := by
  have := A.quotient_zero h 0 (Or.inl rfl)
  have := A.quotient_zero h 1 (Or.inr (Or.inl rfl))
  let f := (HomologicalComplex.homologyMap A.integral.f 1).hom
  have hf : Function.Injective f := injective_of_exact_zero_left
    (A.integral_exact.δ 0 1 (by rfl)).hom f
    (functionExact_of_shortComplex _ (A.integral_exact.homology_exact₁ 0 1 (by rfl)))
  have hfs : Function.Surjective f := surjective_of_exact_zero_right f
    (HomologicalComplex.homologyMap A.integral.g 1).hom
    (functionExact_of_shortComplex _ (A.integral_exact.homology_exact₂ 1))
  exact A.e1.trans (LinearEquiv.ofBijective f ⟨hf, hfs⟩).symm

/-- The singular length field is a consequence of the singular comparison, not a hypothesis. -/
theorem singular_length (cE : ℕ) (h : SingularBounds A.X A.Y cE) :
    Module.length ℤ_[2] (A.integral.X₃.homology 2) ≤ 2 * cE := by
  have hq := A.qis
  rw [← (asIso (HomologicalComplex.homologyMap A.q 2)).toLinearEquiv.length_eq]
  exact h.2.2.2.2

end ArithmeticComparison

/-- The numerical meaning of residual minimality; it contains no field-dependent constant. -/
def ResiduallyMinimal {S : Type} [CommRing S] (B : SmithBlocks S OO) : Prop :=
  ∑ n : Fin 4, Module.finrank ℤ_[2] (centralCx B fr₀ n) ≤
    ∑ n : Fin 4, Module.finrank (ZMod 2) (centralRed B fr₀ n)

/-- Positive valuations of central Smith entries imply residual minimality. -/
theorem residuallyMinimal_of_positive {S : Type} [CommRing S] (B : SmithBlocks S OO)
    (hpos : ∀ i j, 1 ≤ (B.s i j).valuation) : ResiduallyMinimal B := by
  apply Finset.sum_le_sum
  intro n hn
  rw [finrank_centralCx]
  change fr₀ n + SmithCx.db (dd B) n + dd B n ≤
    Module.finrank (ZMod 2) (SmithCx.H (f := fr₀)
      (fun i j => PadicInt.toZMod (σ B i j)) n)
  rw [SmithCx.finrank_H_of_zero _ (toZMod_σ_eq_zero B hpos)]

/-- The remaining integral arithmetic relation (5.7b). It is the length consequence of
integral Kummer self-duality and universal coefficients, manuscript lines 5296–5302
(Nekovář, sections 5.1 and 6.3.4, as cited at lines 5274–5276). This definition is an
explicit unresolved comparison, not a proof of the printed duality theorem. -/
def IntegralKummerLengthComparison (C : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ) : Prop :=
  Module.length ℤ_[2] (C.homology 3) =
    Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (C.homology 1))

private def torsionMap {R : Type} [CommRing R] {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    Submodule.torsion R M →ₗ[R] Submodule.torsion R N where
  toFun x := ⟨f x, by
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (x : M)).mp x.2
    refine (Submodule.mem_torsion_iff _).mpr ⟨a, ?_⟩
    rw [Submonoid.smul_def] at ha ⊢
    rw [← map_smul, ha, map_zero]⟩
  map_add' x y := by ext; simp
  map_smul' r x := by ext; simp

private theorem torsionMap_injective {R : Type} [CommRing R] {M N : Type}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) : Function.Injective (torsionMap f) := by
  intro x y h
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val h

namespace ArithmeticComparison

variable {S : Type} [CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)

/-- The total chain rank is derived from the residual Selmer profile, exactness and minimality. -/
theorem rank_budget (hmin : ResiduallyMinimal B) (hprofile : ResidualKummerProfile A.ordinaryRed) :
    ∑ n : Fin 4, Module.finrank ℤ_[2] (centralCx B fr₀ n) ≤ 2 * A.dK + 12 := by
  have hsrc := A.redSource_qis
  have hq := A.redQ_qis
  have hfiniteC : ∀ n : Fin 4,
      FiniteDimensional (ZMod 2) (A.residual.X₁.homology (n : ℤ)) := by
    intro n
    have : FiniteDimensional (ZMod 2) (A.ordinaryRed.toCC.homology (n : ℤ)) := hprofile.1 n
    exact LinearEquiv.finiteDimensional
      (asIso (HomologicalComplex.homologyMap A.redSource (n : ℤ))).toLinearEquiv
  have hfiniteD : ∀ n : Fin 4,
      FiniteDimensional (ZMod 2) (A.residual.X₂.homology (n : ℤ)) := by
    intro n
    exact LinearEquiv.finiteDimensional (A.redMiddle n)
  have hfiniteQ : ∀ n : Fin 4,
      FiniteDimensional (ZMod 2) (A.residual.X₃.homology (n : ℤ)) := by
    intro n
    have := singular_finiteDimensional (A.X.map PadicInt.toZMod)
      (A.Y.map PadicInt.toZMod) (n : ℤ)
    exact LinearEquiv.finiteDimensional
      (asIso (HomologicalComplex.homologyMap A.redQ (n : ℤ))).toLinearEquiv
  have hle : ∀ n : Fin 4, Module.finrank (ZMod 2) (A.residual.X₂.homology (n : ℤ)) ≤
      Module.finrank (ZMod 2) (A.residual.X₁.homology (n : ℤ)) +
        Module.finrank (ZMod 2) (A.residual.X₃.homology (n : ℤ)) := by
    intro n
    have := hfiniteC n
    have := hfiniteD n
    have := hfiniteQ n
    exact finrank_le_of_exact'
      (HomologicalComplex.homologyMap A.residual.f (n : ℤ)).hom
      (HomologicalComplex.homologyMap A.residual.g (n : ℤ)).hom
      (functionExact_of_shortComplex _ (A.residual_exact.homology_exact₂ (n : ℤ)))
  have hC : ∑ n : Fin 4, Module.finrank (ZMod 2) (A.residual.X₁.homology (n : ℤ)) =
      2 * A.dK + 4 := by
    calc
      _ = ∑ n : Fin 4, Module.finrank (ZMod 2) (A.ordinaryRed.toCC.homology (n : ℤ)) :=
        Finset.sum_congr rfl fun n hn =>
          (asIso (HomologicalComplex.homologyMap A.redSource (n : ℤ))).toLinearEquiv.finrank_eq.symm
      _ = 2 * A.dK + 4 := by
        simp only [hprofile.2, Fin.sum_univ_four]
        simp [dK]
        ring
  have hQ : ∑ n : Fin 4, Module.finrank (ZMod 2) (A.residual.X₃.homology (n : ℤ)) ≤ 8 := by
    calc
      _ = ∑ n : Fin 4, Module.finrank (ZMod 2)
          ((singularCx (A.X.map PadicInt.toZMod) (A.Y.map PadicInt.toZMod)).homology (n : ℤ)) :=
        Finset.sum_congr rfl fun n hn =>
          (asIso (HomologicalComplex.homologyMap A.redQ (n : ℤ))).toLinearEquiv.finrank_eq.symm
      _ ≤ 8 := residual_singular_bound _ _
  calc
    _ ≤ ∑ n : Fin 4, Module.finrank (ZMod 2) (centralRed B fr₀ n) := hmin
    _ = ∑ n : Fin 4, Module.finrank (ZMod 2) (A.residual.X₂.homology (n : ℤ)) :=
      Finset.sum_congr rfl fun n hn => (A.redMiddle n).finrank_eq
    _ ≤ ∑ n : Fin 4, (Module.finrank (ZMod 2) (A.residual.X₁.homology (n : ℤ)) +
        Module.finrank (ZMod 2) (A.residual.X₃.homology (n : ℤ))) :=
      Finset.sum_le_sum fun n hn => hle n
    _ = (∑ n : Fin 4, Module.finrank (ZMod 2) (A.residual.X₁.homology (n : ℤ))) +
        ∑ n : Fin 4, Module.finrank (ZMod 2) (A.residual.X₃.homology (n : ℤ)) :=
      Finset.sum_add_distrib
    _ ≤ 2 * A.dK + 12 := by rw [hC]; omega

/-- Finiteness and the two natural length parameters are derived from the Smith comparison. -/
theorem length_parameters (cE : ℕ) (h : SingularBounds A.X A.Y cE) :
    Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (A.integral.X₁.homology 1)) = A.tK ∧
    Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (A.integral.X₁.homology 2)) = A.hK := by
  have h1 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (A.integral.X₁.homology 1)) =
      ((∑ j, (σ B 0 j).valuation : ℕ) : ℕ∞) := by
    rw [← SmithCx.length_torsion_eq_of_equiv (A.h1Equiv cE h),
      SmithCx.length_torsion_H (σ B) (σ_ne B) 1,
      SmithCx.length_Q_succ (σ B) (σ_ne B) 0]
  have h2 : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (A.integral.X₁.homology 2)) ≤
      ((∑ j, (σ B 1 j).valuation : ℕ) : ℕ∞) := by
    calc
      _ ≤ Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (centralH B fr₀ 2)) :=
        Module.length_le_of_injective (torsionMap A.i)
          (torsionMap_injective A.i (A.exact_sequence cE h).1)
      _ = _ := by
        rw [SmithCx.length_torsion_H (σ B) (σ_ne B) 2,
          SmithCx.length_Q_succ (σ B) (σ_ne B) 1]
  constructor
  · have hn : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (A.integral.X₁.homology 1)) ≠ ⊤ := by
      rw [h1]
      exact ENat.natCast_ne_top _
    exact (ENat.natCast_toNat hn).symm
  · have hn : Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (A.integral.X₁.homology 2)) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) h2
    exact (ENat.natCast_toNat hn).symm

end ArithmeticComparison

/-- The budget is produced without assuming its rank bound, cohomology exact sequence,
singular length, free ranks, or finiteness of the two torsion parameters.
The only remaining integral arithmetic relation is isolated explicitly. -/
theorem budgetInputsAt_of_comparison {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (cE : ℕ) (hmin : ResiduallyMinimal B)
    (hprofile : ResidualKummerProfile A.ordinaryRed) (h : SingularBounds A.X A.Y cE)
    (hdual : IntegralKummerLengthComparison A.integral.X₁) :
    BudgetInputsAt B fr₀ A.dK A.hK cE A.tK := by
  obtain ⟨ht1, hh2⟩ := A.length_parameters cE h
  exact budgetInputsAt_of_rankless B A.dK A.hK cE A.tK (A.rank_budget hmin hprofile)
    (A.h1Equiv cE h) A.i A.j A.delta A.l (A.exact_sequence cE h)
    ht1 (hdual.trans ht1) hh2 (A.singular_length cE h)

/-- Finite self-duality supplies the profile used by the budget, so neither upper residual
dimension is an arithmetic input. -/
theorem budgetInputsAt_of_selfDuality {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (cE : ℕ) (hmin : ResiduallyMinimal B)
    (γ : A.ordinaryRed.toCC ⟶ (dualCx A.ordinaryRed 3).toCC) (hγ : QuasiIso γ)
    (e0 : A.ordinaryRed.toCC.homology 0 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    [Module.Finite (ZMod 2) (A.ordinaryRed.toCC.homology 1)]
    (h : SingularBounds A.X A.Y cE) (hdual : IntegralKummerLengthComparison A.integral.X₁) :
    BudgetInputsAt B fr₀ A.dK A.hK cE A.tK :=
  budgetInputsAt_of_comparison A cE hmin
    (residualKummerProfile_of_selfDuality (Field.toIsField (ZMod 2)) A.ordinaryRed γ hγ e0) h hdual

/-- One retained precision per place suffices for every singular input of the budget. -/
theorem budgetInputsAt_of_retained {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (cE : ℕ) (hmin : ResiduallyMinimal B)
    (γ : A.ordinaryRed.toCC ⟶ (dualCx A.ordinaryRed 3).toCC) (hγ : QuasiIso γ)
    (e0 : A.ordinaryRed.toCC.homology 0 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    [Module.Finite (ZMod 2) (A.ordinaryRed.toCC.homology 1)]
    (X₀ Y₀ : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (hXX : ∀ i j, X₀ i j - A.X i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)})
    (hYY : ∀ i j, Y₀ i j - A.Y i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)})
    (hX₀ : X₀.det ≠ 0) (hY₀ : Y₀.det ≠ 0)
    (hcX₀ : X₀.det.valuation ≤ cE) (hcY₀ : Y₀.det.valuation ≤ cE)
    (hdual : IntegralKummerLengthComparison A.integral.X₁) :
    BudgetInputsAt B fr₀ A.dK A.hK cE A.tK :=
  budgetInputsAt_of_selfDuality A cE hmin γ hγ e0
    (singularBounds_of_retained X₀ Y₀ A.X A.Y cE hXX hYY hX₀ hY₀ hcX₀ hcY₀) hdual

namespace ArithmeticComparison

variable {S : Type} [CommRing S] {B : SmithBlocks S OO} (A : ArithmeticComparison B)

/-- Both integral free ranks are forced by the fixed Smith pattern and the finite singular quotient. -/
theorem free_ranks (cE : ℕ) (h : SingularBounds A.X A.Y cE) :
    Module.finrank ℤ_[2] (A.integral.X₁.homology 1) = 1 ∧
    Module.finrank ℤ_[2] (A.integral.X₁.homology 2) = 1 := by
  constructor
  · rw [← (A.h1Equiv cE h).finrank_eq, finrank_centralH]
    rfl
  · rw [finrank_eq_of_exact_torsion A.i A.j (A.exact_sequence cE h).1
      (A.exact_sequence cE h).2.1 (isTorsion_of_length_le (2 * cE) (A.singular_length cE h)),
      finrank_centralH]
    rfl

/-- Disk and torsion budgets in the exact types consumed by the determinant clearing. -/
theorem smith_budget (cE : ℕ) (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0)
    (hmin : ResiduallyMinimal B) (hprofile : ResidualKummerProfile A.ordinaryRed)
    (h : SingularBounds A.X A.Y cE) (hdual : IntegralKummerLengthComparison A.integral.X₁) :
    B.mTot ≤ A.dK + 5 ∧ B.hSmith ≤ A.hK + 2 * cE + 2 * A.tK := by
  obtain ⟨ht1, hh2⟩ := A.length_parameters cE h
  obtain ⟨hr1, hr2⟩ := A.free_ranks cE h
  exact budget_rank B fr₀ hamp (A.rank_budget hmin hprofile) (A.h1Equiv cE h)
    A.i A.j A.delta A.l (A.exact_sequence cE h) ht1 (hdual.trans ht1) hh2
    (A.singular_length cE h) hr1 hr2

/-- The three parameters depend only on ordinary source cohomology, not on the graph or its Smith bases. -/
theorem parameters_eq {S' : Type} [CommRing S'] {B' : SmithBlocks S' OO}
    (A' : ArithmeticComparison B')
    (e1 : A.integral.X₁.homology 1 ≃ₗ[ℤ_[2]] A'.integral.X₁.homology 1)
    (e2 : A.integral.X₁.homology 2 ≃ₗ[ℤ_[2]] A'.integral.X₁.homology 2)
    (er : A.ordinaryRed.toCC.homology 1 ≃ₗ[ZMod 2] A'.ordinaryRed.toCC.homology 1) :
    A.dK = A'.dK ∧ A.hK = A'.hK ∧ A.tK = A'.tK :=
  ⟨er.finrank_eq, congrArg ENat.toNat (SmithCx.length_torsion_eq_of_equiv e2),
    congrArg ENat.toNat (SmithCx.length_torsion_eq_of_equiv e1)⟩

end ArithmeticComparison

/-! ## Genuine continuous Galois cochains and condition changes -/

open NumberField IsDedekindDomain

section Genuine

variable (K : Type) [Field K] [NumberField K] (supp : Set (HeightOneSpectrum (𝓞 K)))
  (T : Type) [AddCommGroup T] [Module ℤ_[2] T] [DistribMulAction (GKS K supp) T]
  [SMulCommClass (GKS K supp) ℤ_[2] T] [TopologicalSpace T] [ContinuousAdd T]
  [ContinuousConstSMul ℤ_[2] T] [ContinuousSMul (GKS K supp) T]
  (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [DistribMulAction (GKS K supp) W]
  [SMulCommClass (GKS K supp) (ZMod 2) W] [TopologicalSpace W] [DiscreteTopology W]
  [ContinuousSMul (GKS K supp) W]
  {S : Type} [CommRing S] (B : SmithBlocks S OO)
  (Δ Δp : GaloisLocalConditions K supp ℤ_[2] T)
  (Δr Δrp : GaloisLocalConditions K supp (ZMod 2) W)
  (F : GaloisCondInclusion K supp ℤ_[2] T Δ Δp)
  (Fr : GaloisCondInclusion K supp (ZMod 2) W Δr Δrp)

/-- The genuine version of the scalar comparison. Its global and local terms are actual continuous
Galois cochains. For the manuscript, the old conditions are derived Kummer conditions and the
new conditions are full at the two moving places. The singular quasi-isomorphisms encode that
specific local comparison; no degreewise isomorphism of full cochains with a finite tame model is required. -/
structure GenuineComparison where
  X : Matrix (Fin 2) (Fin 2) ℤ_[2]
  Y : Matrix (Fin 2) (Fin 2) ℤ_[2]
  e1 : centralH B fr₀ 1 ≃ₗ[ℤ_[2]] (selCx (galoisSelData K supp ℤ_[2] T Δp)).toCC.homology 1
  e2 : centralH B fr₀ 2 ≃ₗ[ℤ_[2]] (selCx (galoisSelData K supp ℤ_[2] T Δp)).toCC.homology 2
  e3 : centralH B fr₀ 3 ≃ₗ[ℤ_[2]] (selCx (galoisSelData K supp ℤ_[2] T Δp)).toCC.homology 3
  q : singularCx X Y ⟶ (singQuot F).toCC
  qis : QuasiIso q
  redMiddle : ∀ n : Fin 4, centralRed B fr₀ n ≃ₗ[ZMod 2]
    (selCx (galoisSelData K supp (ZMod 2) W Δrp)).toCC.homology (n : ℤ)
  redQ : singularCx (X.map PadicInt.toZMod) (Y.map PadicInt.toZMod) ⟶ (singQuot Fr).toCC
  redQ_qis : QuasiIso redQ

namespace GenuineComparison

variable {K supp T W B Δ Δp Δr Δrp F Fr}

/-- The two cochain short exact sequences are proved by the genuine change-of-condition theorem. -/
def toArithmetic (G : GenuineComparison K supp T W B Δ Δp Δr Δrp F Fr) :
    ArithmeticComparison B where
  X := G.X
  Y := G.Y
  integral := galoisChangeCondSES K supp ℤ_[2] T F
  integral_exact := galoisChangeCondSES_shortExact K supp ℤ_[2] T F
  e1 := G.e1
  e2 := G.e2
  e3 := G.e3
  q := G.q
  qis := G.qis
  ordinaryRed := selCx (galoisSelData K supp (ZMod 2) W Δr)
  residual := galoisChangeCondSES K supp (ZMod 2) W Fr
  residual_exact := galoisChangeCondSES_shortExact K supp (ZMod 2) W Fr
  redSource := 𝟙 _
  redSource_qis := by infer_instance
  redMiddle := G.redMiddle
  redQ := G.redQ
  redQ_qis := G.redQ_qis

/-- The complete old-complex budget from the genuine condition change and one retained precision.
No cohomology exactness or numerical budget field is an input. -/
theorem budgetInputsAt (G : GenuineComparison K supp T W B Δ Δp Δr Δrp F Fr)
    (cE : ℕ) (hmin : ResiduallyMinimal B)
    (γ : (selCx (galoisSelData K supp (ZMod 2) W Δr)).toCC ⟶
      (dualCx (selCx (galoisSelData K supp (ZMod 2) W Δr)) 3).toCC) (hγ : QuasiIso γ)
    (e0 : (selCx (galoisSelData K supp (ZMod 2) W Δr)).toCC.homology 0 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    [Module.Finite (ZMod 2) ((selCx (galoisSelData K supp (ZMod 2) W Δr)).toCC.homology 1)]
    (X₀ Y₀ : Matrix (Fin 2) (Fin 2) ℤ_[2])
    (hXX : ∀ i j, X₀ i j - G.X i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)})
    (hYY : ∀ i j, Y₀ i j - G.Y i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)})
    (hX₀ : X₀.det ≠ 0) (hY₀ : Y₀.det ≠ 0)
    (hcX₀ : X₀.det.valuation ≤ cE) (hcY₀ : Y₀.det.valuation ≤ cE)
    (hdual : IntegralKummerLengthComparison (selCx (galoisSelData K supp ℤ_[2] T Δ)).toCC) :
    BudgetInputsAt B fr₀ G.toArithmetic.dK G.toArithmetic.hK cE G.toArithmetic.tK := by
  have : Module.Finite (ZMod 2) (G.toArithmetic.ordinaryRed.toCC.homology 1) := by
    change Module.Finite (ZMod 2)
      ((selCx (galoisSelData K supp (ZMod 2) W Δr)).toCC.homology 1)
    infer_instance
  exact budgetInputsAt_of_retained G.toArithmetic cE hmin γ hγ e0 X₀ Y₀
    hXX hYY hX₀ hY₀ hcX₀ hcY₀ hdual

end GenuineComparison

end Genuine

/-! ## Residual self-duality from the existing manuscript-cited print

This uses the truncated local target, compatible with degree-zero torsion in
ordinary derived Kummer conditions. It does not assume full-target isotropy.
-/

section GenuineResidualDuality

variable (K : Type) [Field K] [NumberField K] (supp : Set (HeightOneSpectrum (𝓞 K)))
  {W V : Type}
  [AddCommGroup W] [Module (ZMod 2) W] [DistribMulAction (GKS K supp) W]
  [SMulCommClass (GKS K supp) (ZMod 2) W] [TopologicalSpace W] [DiscreteTopology W]
  [ContinuousSMul (GKS K supp) W]
  [AddCommGroup V] [Module (ZMod 2) V] [DistribMulAction (GKS K supp) V]
  [SMulCommClass (GKS K supp) (ZMod 2) V] [TopologicalSpace V] [DiscreteTopology V]
  [ContinuousSMul (GKS K supp) V]
  (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] V)
  (hβ : ∀ (g : GKS K supp) (a b : W), β (g • a) (g • b) = g • β a b)
  (Δ : GaloisLocalConditions K supp (ZMod 2) W)
  (I : GaloisTruncIsotropyData K supp (ZMod 2) β hβ Δ Δ)
  (tr : (galoisCompactTT K supp (ZMod 2) β hβ Δ Δ I).X 3 →ₗ[ZMod 2] ZMod 2)
  (htr : ∀ z, tr ((galoisCompactTT K supp (ZMod 2) β hβ Δ Δ I).d 2 3 rfl z) = 0)

/-- Both upper residual dimensions in (5.7a) follow from the genuine truncated Selmer duality.
The sole printed input is the existing Nekovář proposition; the new result is proved. -/
theorem genuine_residual_profile (hNk : NekovarProp543 K)
    (hsetting : NekovarFiniteSetting K supp 2 (ZMod 2)) [Finite W]
    (hb : Function.Bijective β) (hb' : Function.Bijective β.flip)
    (hV : IsCyclotomicTwist K supp (ZMod 2) V) (htr3 : InducesIsoH3 tr)
    (horth : OrthogonalComplementsT K β hβ Δ Δ I tr htr)
    (e0 : (selCx (galoisSelData K supp (ZMod 2) W Δ)).toCC.homology 0 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    [Module.Finite (ZMod 2) ((selCx (galoisSelData K supp (ZMod 2) W Δ)).toCC.homology 1)] :
    ResidualKummerProfile (selCx (galoisSelData K supp (ZMod 2) W Δ)) := by
  let γ := GHom.toCC (selmerDualityMap (galoisPairDataT K supp (ZMod 2) β hβ Δ Δ I) tr htr)
  have hγ : QuasiIso γ := genuineSelmerDualityT K β hβ Δ Δ I tr htr
    (nekovarProp543T_of K hNk) 2 hsetting hb hb' hV htr3 horth
  exact residualKummerProfile_of_selfDuality (Field.toIsField (ZMod 2)) _ γ hγ e0

end GenuineResidualDuality

/-! ## The integral length relation from a finite free ordinary Selmer model

Only the first Smith differential of that model is used. The other two
matrices are unconstrained apart from being a complex. In particular this
interface does not assume (5.7b) as a length equality.
-/

private abbrev moduleQuot {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    (N : Submodule R M) : Type := M ⧸ N

private def quotientRangeEquiv {R : Type} [CommRing R] {U V U' V' : Type}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup U'] [Module R U'] [AddCommGroup V'] [Module R V']
    (f : U →ₗ[R] V) (g : U' →ₗ[R] V') (eu : U ≃ₗ[R] U') (ev : V ≃ₗ[R] V')
    (h : ∀ x, ev (f x) = g (eu x)) :
    moduleQuot (LinearMap.range f) ≃ₗ[R] moduleQuot (LinearMap.range g) := by
  let ψ : V →ₗ[R] moduleQuot (LinearMap.range g) := (LinearMap.range g).mkQ ∘ₗ ev.toLinearMap
  have hs : Function.Surjective ψ := (LinearMap.range g).mkQ_surjective.comp ev.surjective
  have hk : LinearMap.ker ψ = LinearMap.range f := by
    ext x
    rw [LinearMap.mem_ker]
    change (LinearMap.range g).mkQ (ev x) = 0 ↔ x ∈ LinearMap.range f
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range,
      LinearMap.mem_range]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨eu.symm a, ev.injective ?_⟩
      rw [h, eu.apply_symm_apply, ha]
    · rintro ⟨a, rfl⟩
      exact ⟨eu a, (h a).symm⟩
  have eq := @quotientEquivOfSurjective R (inferInstance : CommRing R) V
    (moduleQuot (LinearMap.range g)) inferInstance inferInstance inferInstance inferInstance ψ hs
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans eq

private def dualFunEquiv {R : Type} [CommRing R] (n : ℕ) :
    Module.Dual R (Fin n → R) ≃ₗ[R] (Fin n → R) :=
  (Pi.basisFun R (Fin n)).dualBasis.equivFun

private theorem dualFunEquiv_apply {R : Type} [CommRing R] (n : ℕ)
    (φ : Module.Dual R (Fin n → R)) (j : Fin n) :
    dualFunEquiv n φ j = φ (Pi.single j 1) := by
  rw [dualFunEquiv, Module.Basis.dualBasis_equivFun]
  simp only [Pi.basisFun_apply]

private def topHomologyEquiv {R : Type} [CommRing R] (C : GCx R) (n : ℤ)
    (hz : C.d n (n + 1) rfl = 0) :
    C.toCC.homology n ≃ₗ[R] moduleQuot (LinearMap.range (C.d (n - 1) n (by omega))) := by
  have hd : C.toCC.d n (n + 1) = 0 := by
    ext x
    rw [C.toCC_d_hom n (n + 1) rfl x, hz]
    rfl
  have e := ((C.toCC.isoHomologyι n (n + 1) (by simp) hd) ≪≫
    C.toCC.opcyclesIsoSc' (n - 1) n (n + 1) (by simp) (by simp) ≪≫
    ShortComplex.opcyclesIsoCokernel _ ≪≫ ModuleCat.cokernelIsoRangeQuotient _).toLinearEquiv
  have hf : (C.toCC.sc' (n - 1) n (n + 1)).f.hom = C.d (n - 1) n (by omega) := by
    ext x
    exact C.toCC_d_hom (n - 1) n (by omega) x
  rw [hf] at e
  exact e

section FirstSmithDual

variable {R : Type} [CommRing R] {U V M : Type}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup M] [Module R M]
    (n : ℕ) (s : Fin n → R) (e0 : U ≃ₗ[R] (Fin n → R))
    (e1 : V ≃ₗ[R] (Fin n → R) × M) (f : U →ₗ[R] V)
    (hf : ∀ x, e1 (f x) = ((Matrix.diagonal s).mulVec (e0 x), 0))

/-- The cokernel of the dual first differential is the first Smith cokernel. -/
private def firstSmithDualCokerEquiv :
    moduleQuot (LinearMap.range f.dualMap) ≃ₗ[R]
      moduleQuot (LinearMap.range (Matrix.diagonal s).mulVecLin) := by
  let e := e0.symm.dualMap.trans (dualFunEquiv n)
  have he : ∀ (φ : Module.Dual R U) (j : Fin n),
      e φ j = φ (e0.symm (Pi.single j 1)) := by
    intro φ j
    rw [LinearEquiv.trans_apply, dualFunEquiv_apply]
    rfl
  have himage : ∀ φ : Module.Dual R V, e (f.dualMap φ) =
      (Matrix.diagonal s).mulVec (fun j => φ (e1.symm (Pi.single j 1, 0))) := by
    intro φ
    funext j
    rw [he, Matrix.mulVec_diagonal]
    change φ (f (e0.symm (Pi.single j 1))) = s j * φ (e1.symm (Pi.single j 1, 0))
    have hfj : f (e0.symm (Pi.single j 1)) = s j • e1.symm (Pi.single j 1, 0) := by
      apply e1.injective
      rw [hf, e0.apply_symm_apply, map_smul, e1.apply_symm_apply]
      apply Prod.ext
      · funext k
        by_cases hk : k = j
        · subst k
          simp [Matrix.mulVec_diagonal]
        · simp [Matrix.mulVec_diagonal, Pi.single_apply, hk]
      · simp
    rw [hfj, map_smul, smul_eq_mul]
  have hr : (LinearMap.range f.dualMap).map e.toLinearMap =
      LinearMap.range (Matrix.diagonal s).mulVecLin := by
    ext y
    rw [Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨φ, ⟨ψ, rfl⟩, hy⟩
      exact ⟨fun j => ψ (e1.symm (Pi.single j 1, 0)), by
        change (Matrix.diagonal s).mulVec _ = y
        rw [← himage ψ]
        exact hy⟩
    · rintro ⟨b, hb⟩
      let ψ : Module.Dual R V := (dualFunEquiv n).symm b ∘ₗ
        LinearMap.fst R (Fin n → R) M ∘ₗ e1.toLinearMap
      have hc : ∀ j, ψ (e1.symm (Pi.single j 1, 0)) = b j := by
        intro j
        dsimp only [ψ, LinearMap.comp_apply]
        change (dualFunEquiv n).symm b ((e1 (e1.symm (Pi.single j 1, 0))).1) = b j
        rw [e1.apply_symm_apply]
        change (dualFunEquiv n).symm b (Pi.single j 1) = b j
        rw [← dualFunEquiv_apply]
        exact congrFun ((dualFunEquiv n).apply_symm_apply b) j
      refine ⟨f.dualMap ψ, ⟨ψ, rfl⟩, ?_⟩
      change e (f.dualMap ψ) = y
      rw [himage, show (fun j => ψ (e1.symm (Pi.single j 1, 0))) = b from funext hc]
      exact hb
  let P := LinearMap.range (Matrix.diagonal s).mulVecLin
  let ψ : Module.Dual R U →ₗ[R] moduleQuot P := P.mkQ ∘ₗ e.toLinearMap
  have hs : Function.Surjective ψ := P.mkQ_surjective.comp e.surjective
  have hk : LinearMap.ker ψ = LinearMap.range f.dualMap := by
    ext x
    rw [LinearMap.mem_ker]
    change P.mkQ (e x) = 0 ↔ x ∈ LinearMap.range f.dualMap
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change e x ∈ LinearMap.range (Matrix.diagonal s).mulVecLin ↔ _
    rw [← hr, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := e.injective hxy
      rwa [← hyx]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have eq := @quotientEquivOfSurjective R (inferInstance : CommRing R)
    (Module.Dual R U) (moduleQuot P) inferInstance inferInstance inferInstance inferInstance ψ hs
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans eq

end FirstSmithDual

/-- The integral ordinary Kummer duality, expressed on a finite free model.
Manuscript lines 5296–5302; Nekovář, Selmer complexes (2006), theorem 6.3.4,
p. 143, with the integral/adic setting and derived orthogonal Kummer conditions.
This is a separate source input. It is not obtained by asserting that the
2-adic integers are self-injective or by termwise dualizing infinite cochains. -/
def IntegralModelDuality (C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex ℤ_[2]) : Prop :=
  ∃ γ : C.toGCx.toCC ⟶ (dualCx C.toGCx 3).toCC, QuasiIso γ

/-- A finite free ordinary Selmer model, with just its first differential in the old Smith
coordinates. Both comparison and duality concern the ordinary source, not the relaxed middle term. -/
structure IntegralFirstSmithModel {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) where
  C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex ℤ_[2]
  M : ModuleCat.{0} ℤ_[2]
  e0 : C.toGCx.X 0 ≃ₗ[ℤ_[2]] (Fin (dd B 0) → ℤ_[2])
  e1 : C.toGCx.X 1 ≃ₗ[ℤ_[2]] (Fin (dd B 0) → ℤ_[2]) × M
  first : ∀ x, e1 (C.toGCx.d 0 1 rfl x) = ((Matrix.diagonal (σ B 0)).mulVec (e0 x), 0)
  phi : C.toGCx.toCC ⟶ A.integral.X₁
  qis : QuasiIso phi

namespace IntegralFirstSmithModel

variable {S : Type} [CommRing S] {B : SmithBlocks S OO} {A : ArithmeticComparison B}
    (P : IntegralFirstSmithModel A)

private def dual_e2 : (dualCx P.C.toGCx 3).X 2 ≃ₗ[ℤ_[2]] Module.Dual ℤ_[2] (P.C.toGCx.X 1) where
  toFun φ := asDual φ
  invFun φ := φ
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def dual_e3 : (dualCx P.C.toGCx 3).X 3 ≃ₗ[ℤ_[2]] Module.Dual ℤ_[2] (P.C.toGCx.X 0) where
  toFun φ := asDual φ
  invFun φ := φ
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem dual_top_zero : (dualCx P.C.toGCx 3).d 3 4 rfl = 0 := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  have hx : x = 0 := by
    funext j
    exact (show Empty from j).elim
  change (-(sgn (3 : ℤ))) • (asDual (A := P.C.toGCx) (m := 3) (n := 3) φ)
    (P.C.toGCx.d (3 - 4) (3 - 3) (by omega) x) = 0
  rw [hx, map_zero, map_zero, smul_zero]

/-- The dual degree-three cohomology has exactly the first Smith torsion length. -/
theorem dual_h3_length : Module.length ℤ_[2] ((dualCx P.C.toGCx 3).toCC.homology 3) =
    ((∑ j, (σ B 0 j).valuation : ℕ) : ℕ∞) := by
  let f := (dualCx P.C.toGCx 3).d 2 3 rfl
  let g := (-(sgn (2 : ℤ))) • (P.C.toGCx.d 0 1 rfl).dualMap
  have hfg : ∀ x, P.dual_e3 (f x) = g (P.dual_e2 x) := by
    intro x
    apply LinearMap.ext
    intro y
    rfl
  have e := topHomologyEquiv (dualCx P.C.toGCx 3) 3 P.dual_top_zero
  have eqc := quotientRangeEquiv f g P.dual_e2 P.dual_e3 hfg
  have eqs := firstSmithDualCokerEquiv (dd B 0) (σ B 0) P.e0 P.e1
    (P.C.toGCx.d 0 1 rfl) P.first
  have hrg : LinearMap.range g = LinearMap.range (P.C.toGCx.d 0 1 rfl).dualMap :=
    range_zsmul_eq _ (neg_sgn_square 2)
  have eqr := Submodule.quotEquivOfEq _ _ hrg
  calc
    _ = Module.length ℤ_[2] (moduleQuot (LinearMap.range f)) := e.length_eq
    _ = Module.length ℤ_[2] (moduleQuot (LinearMap.range g)) := eqc.length_eq
    _ = Module.length ℤ_[2] (moduleQuot (LinearMap.range (P.C.toGCx.d 0 1 rfl).dualMap)) := eqr.length_eq
    _ = Module.length ℤ_[2] (moduleQuot (LinearMap.range (Matrix.diagonal (σ B 0)).mulVecLin)) :=
      eqs.length_eq
    _ = _ := SmithCx.length_Q_succ (σ B) (σ_ne B) 0

/-- The length comparison (5.7b) is derived from model duality, with no torsion length premise. -/
theorem length_comparison (cE : ℕ) (h : SingularBounds A.X A.Y cE)
    (hdual : IntegralModelDuality P.C) : IntegralKummerLengthComparison A.integral.X₁ := by
  obtain ⟨γ, hγ⟩ := hdual
  have hp := P.qis
  change Module.length ℤ_[2] (A.integral.X₁.homology 3) =
    Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (A.integral.X₁.homology 1))
  calc
    _ = Module.length ℤ_[2] (P.C.toGCx.toCC.homology 3) :=
      (asIso (HomologicalComplex.homologyMap P.phi 3)).toLinearEquiv.length_eq.symm
    _ = Module.length ℤ_[2] ((dualCx P.C.toGCx 3).toCC.homology 3) :=
      (asIso (HomologicalComplex.homologyMap γ 3)).toLinearEquiv.length_eq
    _ = ((∑ j, (σ B 0 j).valuation : ℕ) : ℕ∞) := P.dual_h3_length
    _ = Module.length ℤ_[2] (Submodule.torsion ℤ_[2] (A.integral.X₁.homology 1)) := by
      rw [← SmithCx.length_torsion_eq_of_equiv (A.h1Equiv cE h),
        SmithCx.length_torsion_H (σ B) (σ_ne B) 1,
        SmithCx.length_Q_succ (σ B) (σ_ne B) 0]

end IntegralFirstSmithModel

/-- The budget with its integral length relation derived from an ordinary finite free model.
No rank, disk count, torsion length or cohomology exactness field of the old budget is assumed. -/
theorem budgetInputsAt_of_integralModel {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (P : IntegralFirstSmithModel A) (cE : ℕ)
    (hmin : ResiduallyMinimal B) (hprofile : ResidualKummerProfile A.ordinaryRed)
    (h : SingularBounds A.X A.Y cE) (hdual : IntegralModelDuality P.C) :
    BudgetInputsAt B fr₀ A.dK A.hK cE A.tK :=
  budgetInputsAt_of_comparison A cE hmin hprofile h (P.length_comparison cE h hdual)

/-! ## Nonminimal compatibility route with an assumed rank bound

The following embeddings are arbitrary injective linear maps. Together with
the prescribed source basis sizes, they assume degreewise rank inequalities;
they do not encode chain-map compatibility or follow from (5.7c). Unit disks
are permitted only with this extra rank-bound input. The primary export below
uses the residual exact sequence and minimality instead.
-/

section SingularChain

variable {R : Type} [CommRing R]

private theorem singular_chain_free (X Y : Matrix (Fin 2) (Fin 2) R) (n : ℤ) :
    Module.Free R ((singularCx X Y).X n) := by
  by_cases hn1 : n = 1
  · subst n
    exact Module.Free.of_equiv
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
        (show (ComplexShape.up ℤ).Rel 1 2 from rfl)).toLinearEquiv.symm
  by_cases hn2 : n = 2
  · subst n
    exact Module.Free.of_equiv
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
        (show (ComplexShape.up ℤ).Rel 1 2 from rfl) (by decide)).toLinearEquiv.symm
  have : Subsingleton ((singularCx X Y).X n) := ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_double_X (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
      (show (ComplexShape.up ℤ).Rel 1 2 from rfl) n hn1 hn2)
  infer_instance

private theorem singular_chain_finite (X Y : Matrix (Fin 2) (Fin 2) R) (n : ℤ) :
    Module.Finite R ((singularCx X Y).X n) := by
  by_cases hn1 : n = 1
  · subst n
    exact Module.Finite.equiv
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
        (show (ComplexShape.up ℤ).Rel 1 2 from rfl)).toLinearEquiv.symm
  by_cases hn2 : n = 2
  · subst n
    exact Module.Finite.equiv
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
        (show (ComplexShape.up ℤ).Rel 1 2 from rfl) (by decide)).toLinearEquiv.symm
  have : Subsingleton ((singularCx X Y).X n) := ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_double_X (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
      (show (ComplexShape.up ℤ).Rel 1 2 from rfl) n hn1 hn2)
  infer_instance

/-- The two singular disks have total chain rank eight, irrespective of their matrices. -/
theorem singular_chain_total_rank [StrongRankCondition R] (X Y : Matrix (Fin 2) (Fin 2) R) :
    ∑ n : Fin 4, Module.finrank R ((singularCx X Y).X (n : ℤ)) = 8 := by
  have h0 : Subsingleton ((singularCx X Y).X 0) := ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_double_X (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
      (show (ComplexShape.up ℤ).Rel 1 2 from rfl) 0 (by decide) (by decide))
  have h3 : Subsingleton ((singularCx X Y).X 3) := ModuleCat.subsingleton_of_isZero
    (HomologicalComplex.isZero_double_X (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
      (show (ComplexShape.up ℤ).Rel 1 2 from rfl) 3 (by decide) (by decide))
  have h1 : Module.finrank R ((singularCx X Y).X 1) = 4 := by
    let e : (singularCx X Y).X 1 ≃ₗ[R] (Fin 2 → R) × (Fin 2 → R) :=
      (HomologicalComplex.doubleXIso₀ (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
        (show (ComplexShape.up ℤ).Rel 1 2 from rfl)).toLinearEquiv
    rw [e.finrank_eq]
    simp [Module.finrank_prod]
  have h2 : Module.finrank R ((singularCx X Y).X 2) = 4 := by
    let e : (singularCx X Y).X 2 ≃ₗ[R] (Fin 2 → R) × (Fin 2 → R) :=
      (HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (X.mulVecLin.prodMap Y.mulVecLin))
        (show (ComplexShape.up ℤ).Rel 1 2 from rfl) (by decide)).toLinearEquiv
    rw [e.finrank_eq]
    simp [Module.finrank_prod]
  simp only [Fin.sum_univ_four]
  change Module.finrank R ((singularCx X Y).X 0) + Module.finrank R ((singularCx X Y).X 1) +
    Module.finrank R ((singularCx X Y).X 2) + Module.finrank R ((singularCx X Y).X 3) = 8
  rw [Module.finrank_zero_of_subsingleton, h1, h2]
  have hz3 : Module.finrank R ((singularCx X Y).X 3) = 0 := Module.finrank_zero_of_subsingleton
  rw [hz3]

end SingularChain

/-- An explicit assumed degreewise rank-bound input for nonminimal old Smith data.
`bas` prescribes source sizes; `emb` and `emb_injective` assume
`rank D_cⁿ ≤ dim Hⁿ(ordinaryRed) + rank Q_rⁿ`. The maps have no compatibility
condition with differentials, coefficient change, or the cochain comparison.
The manuscript does not supply these embeddings in (5.7c). The model comparison
`phi` and `qis` is retained for compatibility but is not used by `rank_budget`.
This structure is not consumed by the primary minimality export. -/
structure SmallGradedModel {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) where
  C : ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex ℤ_[2]
  phi : C.toGCx.toCC ⟶ A.integral.X₁
  qis : QuasiIso phi
  bas : ∀ n : Fin 4,
    Module.Basis (Fin (Module.finrank (ZMod 2) (A.ordinaryRed.toCC.homology (n : ℤ))))
      ℤ_[2] (C.toGCx.X (n : ℤ))
  emb : ∀ n : Fin 4, centralCx B fr₀ n →ₗ[ℤ_[2]]
    (C.toGCx.X (n : ℤ)) × (singularCx A.X A.Y).X (n : ℤ)
  emb_injective : ∀ n, Function.Injective (emb n)

namespace SmallGradedModel

variable {S : Type} [CommRing S] {B : SmithBlocks S OO} {A : ArithmeticComparison B}
    (D : SmallGradedModel A)

include D in
/-- Summing the assumed degreewise rank bounds, with unit disks allowed.
This is not a derivation of the rank estimate from the residual comparison. -/
theorem rank_budget (hprofile : ResidualKummerProfile A.ordinaryRed) :
    ∑ n : Fin 4, Module.finrank ℤ_[2] (centralCx B fr₀ n) ≤ 2 * A.dK + 12 := by
  have hc : ∀ n : Fin 4, Module.finrank ℤ_[2] (D.C.toGCx.X (n : ℤ)) =
      Module.finrank (ZMod 2) (A.ordinaryRed.toCC.homology (n : ℤ)) := by
    intro n
    rw [Module.finrank_eq_card_basis (D.bas n), Fintype.card_fin]
  have hle : ∀ n : Fin 4, Module.finrank ℤ_[2] (centralCx B fr₀ n) ≤
      Module.finrank (ZMod 2) (A.ordinaryRed.toCC.homology (n : ℤ)) +
        Module.finrank ℤ_[2] ((singularCx A.X A.Y).X (n : ℤ)) := by
    intro n
    have := Module.Free.of_basis (D.bas n)
    have := Module.Finite.of_basis (D.bas n)
    have := singular_chain_free A.X A.Y (n : ℤ)
    have := singular_chain_finite A.X A.Y (n : ℤ)
    have h := LinearMap.finrank_le_finrank_of_injective (D.emb_injective n)
    have hprod : Module.finrank ℤ_[2]
        ((D.C.toGCx.X (n : ℤ)) × (singularCx A.X A.Y).X (n : ℤ)) =
      Module.finrank ℤ_[2] (D.C.toGCx.X (n : ℤ)) +
        Module.finrank ℤ_[2] ((singularCx A.X A.Y).X (n : ℤ)) := Module.finrank_prod
    rw [hprod, hc n] at h
    exact h
  have hC : ∑ n : Fin 4, Module.finrank (ZMod 2) (A.ordinaryRed.toCC.homology (n : ℤ)) =
      2 * A.dK + 4 := by
    simp only [hprofile.2, Fin.sum_univ_four]
    simp [ArithmeticComparison.dK]
    ring
  calc
    _ ≤ ∑ n : Fin 4, (Module.finrank (ZMod 2) (A.ordinaryRed.toCC.homology (n : ℤ)) +
        Module.finrank ℤ_[2] ((singularCx A.X A.Y).X (n : ℤ))) :=
      Finset.sum_le_sum fun n hn => hle n
    _ = (∑ n : Fin 4, Module.finrank (ZMod 2) (A.ordinaryRed.toCC.homology (n : ℤ))) +
        ∑ n : Fin 4, Module.finrank ℤ_[2] ((singularCx A.X A.Y).X (n : ℤ)) :=
      Finset.sum_add_distrib
    _ = 2 * A.dK + 12 := by rw [hC, singular_chain_total_rank]

end SmallGradedModel

/-- Compatibility producer for nonminimal old Smith data and ordinary integral duality.
Its rank field is assumed through `SmallGradedModel`; the cohomology sequence and torsion
length consequences are proved. Use the primary minimality export for the manuscript's
rank derivation. -/
theorem budgetInputsAt_of_smallGradedModel {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (D : SmallGradedModel A) (P : IntegralFirstSmithModel A)
    (cE : ℕ) (hprofile : ResidualKummerProfile A.ordinaryRed)
    (h : SingularBounds A.X A.Y cE) (hdual : IntegralModelDuality P.C) :
    BudgetInputsAt B fr₀ A.dK A.hK cE A.tK := by
  obtain ⟨ht1, hh2⟩ := A.length_parameters cE h
  exact budgetInputsAt_of_rankless B A.dK A.hK cE A.tK (D.rank_budget hprofile)
    (A.h1Equiv cE h) A.i A.j A.delta A.l (A.exact_sequence cE h) ht1
    ((P.length_comparison cE h hdual).trans ht1) hh2 (A.singular_length cE h)

/-- Disk and valuation consequences for nonminimal data with an assumed rank-bound input.
The disk-count conclusion inherits `SmallGradedModel`'s assumed degreewise rank bounds;
the torsion-length conclusion is derived from the integral comparison. -/
theorem smith_budget_of_smallGradedModel {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (D : SmallGradedModel A) (P : IntegralFirstSmithModel A)
    (cE : ℕ) (hamp : ∀ i, 3 ≤ i → i < B.n → B.m i = 0)
    (hprofile : ResidualKummerProfile A.ordinaryRed) (h : SingularBounds A.X A.Y cE)
    (hdual : IntegralModelDuality P.C) :
    B.mTot ≤ A.dK + 5 ∧ B.hSmith ≤ A.hK + 2 * cE + 2 * A.tK := by
  obtain ⟨ht1, hh2⟩ := A.length_parameters cE h
  obtain ⟨hr1, hr2⟩ := A.free_ranks cE h
  exact budget_rank B fr₀ hamp (D.rank_budget hprofile) (A.h1Equiv cE h)
    A.i A.j A.delta A.l (A.exact_sequence cE h) ht1
    ((P.length_comparison cE h hdual).trans ht1) hh2 (A.singular_length cE h) hr1 hr2

/-- Renaming the three computed cohomological parameters.
This holds by reflexivity at their computed values and proves no identification
with arithmetic Selmer groups or rational point torsion; those links are separate. -/
def ParameterAgreement {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (dK hK tK : ℕ) : Prop :=
  A.dK = dK ∧ A.hK = hK ∧ A.tK = tK

/-- Conversion to the unchanged original budget interface at named arithmetic parameters. -/
theorem budgetInputsAt_with_parameters {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (dK hK cE tK : ℕ) (hpar : ParameterAgreement A dK hK tK)
    (h : BudgetInputsAt B fr₀ A.dK A.hK cE A.tK) : BudgetInputsAt B fr₀ dK hK cE tK := by
  simpa only [hpar.1, hpar.2.1, hpar.2.2] using h

/-! ## Arithmetic parameter binding through the Kummer coefficient sequence -/

/-- If a torsion group maps injectively into an integral cohomology group, with exactness
against a torsion-free rational cohomology group, its image is exactly integral torsion.
This is the algebra used at manuscript lines 5288–5295. -/
def torsionIdentificationOfExact {R : Type} [CommRing R] [IsDomain R]
    {T M V : Type} [AddCommGroup T] [Module R T] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] [Module.IsTorsionFree R V]
    (i : T →ₗ[R] M) (j : M →ₗ[R] V) (hi : Function.Injective i)
    (hij : Function.Exact i j) (hT : Module.IsTorsion R T) :
    T ≃ₗ[R] Submodule.torsion R M := by
  let f : T →ₗ[R] Submodule.torsion R M :=
    { toFun := fun x => ⟨i x, by
        obtain ⟨r, hr⟩ := @hT x
        refine (Submodule.mem_torsion_iff _).mpr ⟨r, ?_⟩
        rw [Submonoid.smul_def] at hr ⊢
        rw [← map_smul, hr, map_zero]⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun r x => by ext; simp }
  have hf : Function.Injective f := by
    intro x y h
    apply hi
    exact congrArg Subtype.val h
  have hs : Function.Surjective f := by
    intro x
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff (x : M)).mp x.2
    have hj : j x = 0 := by
      have hmul : (r : R) • j x = 0 := by
        rw [Submonoid.smul_def] at hr
        rw [← map_smul, hr, map_zero]
      exact (smul_eq_zero.mp hmul).resolve_left (nonZeroDivisors.coe_ne_zero r)
    obtain ⟨t, ht⟩ := (hij x).mp hj
    exact ⟨t, Subtype.ext ht⟩
  exact LinearEquiv.ofBijective f ⟨hf, hs⟩

/-- The residual parameter equals the arithmetic Selmer-two dimension once the genuine
Kummer cohomology identification is supplied; no dimension bound is assumed. -/
theorem dK_of_selmer_identification {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (Sel2 : ModuleCat.{0} (ZMod 2))
    (e : A.ordinaryRed.toCC.homology 1 ≃ₗ[ZMod 2] Sel2) :
    A.dK = Module.finrank (ZMod 2) Sel2 := e.finrank_eq

/-- The torsion parameter equals the rational two-primary point-group length once the
coefficient sequence is identified. The group and maps are explicit, not a length premise. -/
theorem tK_of_coefficient_exact {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (Tor V : ModuleCat.{0} ℤ_[2]) [Module.IsTorsionFree ℤ_[2] V]
    (i : Tor →ₗ[ℤ_[2]] A.integral.X₁.homology 1) (j : A.integral.X₁.homology 1 →ₗ[ℤ_[2]] V)
    (hi : Function.Injective i) (hij : Function.Exact i j) (hTor : Module.IsTorsion ℤ_[2] Tor) :
    A.tK = (Module.length ℤ_[2] Tor).toNat :=
  congrArg ENat.toNat (torsionIdentificationOfExact i j hi hij hTor).length_eq.symm

/-- Determinant-cap data represented at one coefficient precision at each place.
Without a binding to actual stage matrices this is logically equivalent to the
nonzero determinant and valuation cap of the limiting matrices: the witnesses
may be chosen equal to those matrices. `cE` is a natural-number parameter here,
not an identified manuscript constant. The singular length bound is derived. -/
structure RetainedSingularStage {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (cE : ℕ) where
  X0 : Matrix (Fin 2) (Fin 2) ℤ_[2]
  Y0 : Matrix (Fin 2) (Fin 2) ℤ_[2]
  congrX : ∀ i j, X0 i j - A.X i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)}
  congrY : ∀ i j, Y0 i j - A.Y i j ∈ Ideal.span {(2 : ℤ_[2]) ^ (cE + 1)}
  detX_ne : X0.det ≠ 0
  detY_ne : Y0.det ≠ 0
  valX : X0.det.valuation ≤ cE
  valY : Y0.det.valuation ≤ cE

/-- Every singular fact used by the budget follows from the retained stage. -/
theorem RetainedSingularStage.bounds {S : Type} [CommRing S] {B : SmithBlocks S OO}
    {A : ArithmeticComparison B} {cE : ℕ} (R : RetainedSingularStage A cE) :
    SingularBounds A.X A.Y cE :=
  singularBounds_of_retained R.X0 R.Y0 A.X A.Y cE R.congrX R.congrY
    R.detX_ne R.detY_ne R.valX R.valY

/-- The former primary export, kept as a nonminimal compatibility producer.
The rank bound is assumed through `SmallGradedModel`, not derived from (5.7c);
its residual comparison fields and `SmallGradedModel.phi`/`qis` are unused here.
Use `budgetInputsAt_from_selmer_minimal` for the residual minimality derivation.
Use `GenuineComparison.toArithmetic` to instantiate the genuine cochain interface. -/
theorem budgetInputsAt_from_selmer_models {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (D : SmallGradedModel A) (P : IntegralFirstSmithModel A)
    (dK hK cE tK : ℕ) (R : RetainedSingularStage A cE)
    (γ : A.ordinaryRed.toCC ⟶ (dualCx A.ordinaryRed 3).toCC) (hγ : QuasiIso γ)
    (e0 : A.ordinaryRed.toCC.homology 0 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    [Module.Finite (ZMod 2) (A.ordinaryRed.toCC.homology 1)]
    (hdual : IntegralModelDuality P.C) (hpar : ParameterAgreement A dK hK tK) :
    BudgetInputsAt B fr₀ dK hK cE tK :=
  budgetInputsAt_with_parameters A dK hK cE tK hpar
    (budgetInputsAt_of_smallGradedModel A D P cE
      (residualKummerProfile_of_selfDuality (Field.toIsField (ZMod 2)) A.ordinaryRed γ hγ e0)
      R.bounds hdual)

/-! ## Primary export: the manuscript's residual minimality route -/

/-- Primary budget producer, found in an independent review.
The rank bound follows from the residual exact sequence of (5.7c), (5.7a),
and positive central Smith valuations, corresponding to cancelling unit entries
at manuscript lines 5355–5359. No `SmallGradedModel` is consumed.
The integral length relation follows from ordinary finite free model duality;
`ParameterAgreement` only renames computed values and `cE` remains an unbound cap. -/
theorem budgetInputsAt_from_selmer_minimal {S : Type} [CommRing S] {B : SmithBlocks S OO}
    (A : ArithmeticComparison B) (P : IntegralFirstSmithModel A)
    (dK hK cE tK : ℕ) (R : RetainedSingularStage A cE)
    (hpos : ∀ i j, 1 ≤ (B.s i j).valuation)
    (γ : A.ordinaryRed.toCC ⟶ (dualCx A.ordinaryRed 3).toCC) (hγ : QuasiIso γ)
    (e0 : A.ordinaryRed.toCC.homology 0 ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
    [Module.Finite (ZMod 2) (A.ordinaryRed.toCC.homology 1)]
    (hdual : IntegralModelDuality P.C) (hpar : ParameterAgreement A dK hK tK) :
    BudgetInputsAt B fr₀ dK hK cE tK :=
  budgetInputsAt_with_parameters A dK hK cE tK hpar
    (budgetInputsAt_of_integralModel A P cE (residuallyMinimal_of_positive B hpos)
      (residualKummerProfile_of_selfDuality (Field.toIsField (ZMod 2)) A.ordinaryRed γ hγ e0)
      R.bounds hdual)

end ZInQ.Contrib.RC53Assist.Budget
