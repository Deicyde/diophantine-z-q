import ZInQKernel.HDecomp.ModCurves.Leaves

/-! # r16-split: `R16_EichlerShimuraJ1'` from a strictly weaker core and `TateModuleFree`

The dimension clause `dim A = [K_f : ℚ]` of R16 follows from the rank-two clause and `T_ℓ(A)` free of
rank `2 dim A` (`PkgI3.TateModuleFree`): `V_ℓ(A)^* ⊗ ℚ̄_ℓ` is the direct sum of the `ι`-eigenfunctionals
over the `[K_f : ℚ]` embeddings `ι : K_f → ℚ̄_ℓ`. -/

noncomputable section

set_option linter.unusedSectionVars false

namespace R16Split

open Module

/-! ## 1. Linear algebra: joint eigenspaces of a field acting on a finite-dimensional space -/

section LinAlg

variable {F Ω W : Type*} [Field F] [Field Ω] [AddCommGroup W] [Module Ω W]

/-- The joint eigenspace of `P : F → End_Ω(W)` for the character `ι : F → Ω`. -/
def jointEig (P : F →+* Module.End Ω W) (ι : F →+* Ω) : Submodule Ω W where
  carrier := {φ | ∀ a, P a φ = ι a • φ}
  zero_mem' := by intro a; simp
  add_mem' := by
    intro x y hx hy a
    simp only [Set.mem_ofPred_eq] at hx hy
    rw [map_add, hx a, hy a, smul_add]
  smul_mem' := by
    intro c x hx a
    simp only [Set.mem_ofPred_eq] at hx
    rw [map_smul, hx a, smul_comm]

/-- The elements `a` with `P a φ = ι a φ` form a subfield. -/
def eqSubfield (P : F →+* Module.End Ω W) (ι : F →+* Ω) (φ : W) : Subfield F where
  carrier := {a | P a φ = ι a • φ}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, map_mul, mul_comm]
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, LinearMap.add_apply, ha, hb, map_add, add_smul]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_neg, LinearMap.neg_apply, ha, map_neg, neg_smul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    by_cases h0 : a = 0
    · simp [h0]
    have h1 : P a⁻¹ (P a φ) = φ := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel₀ h0, map_one, Module.End.one_apply]
    rw [ha, map_smul] at h1
    have hι : ι a ≠ 0 := (map_ne_zero ι).2 h0
    calc P a⁻¹ φ = (ι a)⁻¹ • (ι a • P a⁻¹ φ) := by rw [smul_smul, inv_mul_cancel₀ hι, one_smul]
      _ = ι a⁻¹ • φ := by rw [h1, map_inv₀]

variable [Algebra ℚ F]

/-- A joint eigenvector is an eigenvector of a generator. -/
theorem mem_jointEig_iff (P : F →+* Module.End Ω W) (ι : F →+* Ω) {α : F}
    (hα : Algebra.adjoin ℚ {α} = ⊤) (φ : W) :
    φ ∈ jointEig P ι ↔ P α φ = ι α • φ := by
  refine ⟨fun h => h α, fun h a => ?_⟩
  let M : Subalgebra ℚ F :=
    { (eqSubfield P ι φ).toSubring with
      algebraMap_mem' := fun q => by
        rw [eq_ratCast]
        exact SubfieldClass.ratCast_mem (eqSubfield P ι φ) q }
  have hle : Algebra.adjoin ℚ {α} ≤ M := Algebra.adjoin_le (by simpa [M, eqSubfield] using h)
  rw [hα] at hle
  exact hle (Algebra.mem_top (x := a))

variable [IsAlgClosed Ω] [CharZero Ω] [FiniteDimensional Ω W] [FiniteDimensional ℚ F]

/-- `P(μ_α)(P α) = 0`, written over `Ω`. -/
theorem aeval_minpoly_eq_zero (P : F →+* Module.End Ω W) (α : F) :
    Polynomial.aeval (P α) ((minpoly ℚ α).map (algebraMap ℚ Ω)) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  have hr : (algebraMap Ω (Module.End Ω W)).comp (algebraMap ℚ Ω) = P.comp (algebraMap ℚ F) :=
    RingHom.ext_rat _ _
  rw [hr, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]

/-- **The joint eigenspaces of a number field acting on a finite-dimensional space over an
algebraically closed field of characteristic `0` add up to the whole space.** -/
theorem isInternal_jointEig [DecidableEq (F →ₐ[ℚ] Ω)] (P : F →+* Module.End Ω W) :
    DirectSum.IsInternal (fun ι : F →ₐ[ℚ] Ω => jointEig P ι.toRingHom) := by
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ F
  set α := pb.gen with hαdef
  have hα : Algebra.adjoin ℚ {α} = ⊤ := pb.adjoin_gen_eq_top
  set S := P α with hSdef
  have hE : ∀ ι : F →ₐ[ℚ] Ω, jointEig P ι.toRingHom = S.eigenspace (ι α) := by
    intro ι; ext φ
    rw [mem_jointEig_iff P ι.toRingHom hα, Module.End.mem_eigenspace_iff]
    rfl
  have hinj : Function.Injective (fun ι : F →ₐ[ℚ] Ω => ι α) := fun ι ι' h => pb.algHom_ext h
  have hind : iSupIndep (fun ι : F →ₐ[ℚ] Ω => S.eigenspace (ι α)) :=
    (S.eigenspaces_iSupIndep).comp hinj
  -- semisimplicity
  have hsep : (minpoly ℚ α).Separable := Algebra.IsSeparable.isSeparable ℚ α
  have hsq : Squarefree ((minpoly ℚ α).map (algebraMap ℚ Ω)) := (hsep.map).squarefree
  have hss : S.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (aeval_minpoly_eq_zero P α)
  have hspan : ⨆ ι : F →ₐ[ℚ] Ω, S.eigenspace (ι α) = ⊤ := by
    rw [eq_top_iff, ← hss.iSup_eigenspace_eq_top]
    refine iSup_le fun r => ?_
    by_cases hr : S.eigenspace r = ⊥
    · rw [hr]; exact bot_le
    obtain ⟨x, hx⟩ := Module.End.HasEigenvalue.exists_hasEigenvector (f := S) (μ := r)
      (Module.End.hasEigenvalue_of_hasGenEigenvalue (k := 1) (by
        rw [Module.End.hasGenEigenvalue_iff]; simpa using hr))
    have h0 := Module.End.aeval_apply_of_hasEigenvector (p := (minpoly ℚ α).map (algebraMap ℚ Ω)) hx
    rw [aeval_minpoly_eq_zero P α, LinearMap.zero_apply] at h0
    have hroot : Polynomial.aeval r (minpoly ℚ α) = 0 := by
      have := (smul_eq_zero.mp h0.symm).resolve_right hx.2
      rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    let ι : F →ₐ[ℚ] Ω := pb.lift r hroot
    have hι : ι α = r := pb.lift_gen r hroot
    rw [← hι]
    exact le_iSup (fun ι : F →ₐ[ℚ] Ω => S.eigenspace (ι α)) ι
  have hE' : (fun ι : F →ₐ[ℚ] Ω => jointEig P ι.toRingHom) =
      (fun ι : F →ₐ[ℚ] Ω => S.eigenspace (ι α)) := funext hE
  rw [hE']
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hspan

theorem sum_finrank_jointEig (P : F →+* Module.End Ω W) :
    ∑ ι : F →ₐ[ℚ] Ω, finrank Ω (jointEig P ι.toRingHom) = finrank Ω W := by
  classical
  have e := LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun ι : F →ₐ[ℚ] Ω => jointEig P ι.toRingHom)) (isInternal_jointEig P)
  rw [← e.finrank_eq, Module.finrank_directSum]

/-- The trace of `P a` is `Σ_ι (dim of the ι-eigenspace) ι(a)`. -/
theorem trace_eq_sum_jointEig (P : F →+* Module.End Ω W) (a : F) :
    LinearMap.trace Ω W (P a) =
      ∑ ι : F →ₐ[ℚ] Ω, (finrank Ω (jointEig P ι.toRingHom) : Ω) * ι a := by
  classical
  have hmaps : ∀ ι : F →ₐ[ℚ] Ω, Set.MapsTo (P a) (jointEig P ι.toRingHom)
      (jointEig P ι.toRingHom) := by
    intro ι φ hφ b
    show P b (P a φ) = ι b • P a φ
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, hφ b,
      map_smul]
    rfl
  rw [LinearMap.trace_eq_sum_trace_restrict (isInternal_jointEig P) hmaps]
  refine Finset.sum_congr rfl fun ι _ => ?_
  have hr : (P a).restrict (hmaps ι) = ι a • LinearMap.id := by
    apply LinearMap.ext; intro φ; apply Subtype.ext
    exact φ.2 a
  rw [hr, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

/-- **Characters with rational weighted sums have equal weights.** If `Σ_ι d_ι ι(a) ∈ ℚ` for every
`a ∈ F`, all `d_ι` are equal (trace form nondegenerate, Dedekind independence of characters). -/
theorem weights_eq_of_rational (d : (F →ₐ[ℚ] Ω) → ℕ)
    (h : ∀ a : F, ∃ r : ℚ, ∑ ι : F →ₐ[ℚ] Ω, (d ι : Ω) * ι a = (r : Ω)) (ι ι' : F →ₐ[ℚ] Ω) :
    d ι = d ι' := by
  classical
  choose r hr using h
  have hinjQ : Function.Injective (Rat.cast : ℚ → Ω) := Rat.cast_injective
  let lam : F →ₗ[ℚ] ℚ :=
    { toFun := r
      map_add' := fun a b => hinjQ (by
        rw [Rat.cast_add, ← hr, ← hr, ← hr, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun κ _ => by rw [map_add, mul_add])
      map_smul' := fun q a => hinjQ (by
        rw [RingHom.id_apply, smul_eq_mul, Rat.cast_mul, ← hr, ← hr, Finset.mul_sum]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [map_smul, Rat.smul_def, mul_left_comm]) }
  have hnd := traceForm_nondegenerate ℚ F
  obtain ⟨b, hb⟩ : ∃ b : F, ∀ a, Algebra.trace ℚ F (b * a) = lam a := by
    refine ⟨((Algebra.traceForm ℚ F).toDual hnd).symm lam, fun a => ?_⟩
    have h2 := LinearMap.congr_fun
      (((Algebra.traceForm ℚ F).toDual hnd).apply_symm_apply lam) a
    rw [LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply] at h2
    exact h2
  -- `Σ_κ (d_κ - κ b) κ = 0`
  have hzero : ∀ a : F, ∑ κ : F →ₐ[ℚ] Ω, ((d κ : Ω) - κ b) * κ a = 0 := by
    intro a
    have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) (E := Ω) (x := b * a)
    rw [hb a] at h1
    simp only [sub_mul, Finset.sum_sub_distrib, hr a]
    rw [eq_ratCast] at h1
    change ((r a : ℚ) : Ω) = _ at h1
    rw [h1, sub_eq_zero]
    exact Finset.sum_congr rfl fun κ _ => by rw [map_mul]
  have hli : LinearIndependent Ω (fun κ : F →ₐ[ℚ] Ω => (κ : F → Ω)) := by
    have := (linearIndependent_monoidHom F Ω).comp
      (fun κ : F →ₐ[ℚ] Ω => (κ.toRingHom : F →* Ω))
      (fun κ κ' hκ => AlgHom.ext fun x => DFunLike.congr_fun hκ x)
    exact this
  have hcoef := (Fintype.linearIndependent_iff.mp hli) (fun κ => (d κ : Ω) - κ b) (by
    funext a; simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hzero a)
  have hdb : ∀ κ : F →ₐ[ℚ] Ω, (d κ : F) = b := fun κ => κ.toRingHom.injective (by
    have := hcoef κ
    rw [sub_eq_zero] at this
    simpa using this)
  have h3 := (hdb ι).trans (hdb ι').symm
  rw [← map_natCast (algebraMap ℚ F), ← map_natCast (algebraMap ℚ F) (d ι')] at h3
  exact_mod_cast (algebraMap ℚ F).injective h3

end LinAlg

/-! ## 2. Precomposition: a field acting on `V` acts on `Hom_k(V, Ω)` -/

/-- Precomposition by `T`, an `Ω`-linear endomorphism of `Hom_k(V, Ω)`. -/
def precompL {k V Ω : Type*} [Field k] [AddCommGroup V] [Module k V] [Field Ω] [Algebra k Ω]
    (T : Module.End k V) : Module.End Ω (V →ₗ[k] Ω) :=
  { toFun := fun φ => φ ∘ₗ T
    map_add' := fun φ ψ => LinearMap.add_comp _ _ _
    map_smul' := fun c φ => LinearMap.smul_comp _ _ _ }

/-- `a ↦ (φ ↦ φ ∘ ρ(a))`, a ring homomorphism since `F` is commutative. -/
def precompHom {k V Ω F : Type*} [Field k] [AddCommGroup V] [Module k V] [Field Ω] [Algebra k Ω]
    [Field F] (ρ : F →+* Module.End k V) : F →+* Module.End Ω (V →ₗ[k] Ω) where
  toFun a := precompL (ρ a)
  map_one' := LinearMap.ext fun φ => LinearMap.ext fun v => by simp [precompL]
  map_mul' a b := LinearMap.ext fun φ => LinearMap.ext fun v => by
    show φ (ρ (a * b) v) = φ (ρ b (ρ a v))
    rw [mul_comm, map_mul, Module.End.mul_apply]
  map_zero' := LinearMap.ext fun φ => LinearMap.ext fun v => by simp [precompL]
  map_add' a b := LinearMap.ext fun φ => LinearMap.ext fun v => by simp [precompL]

theorem precompL_apply {k V Ω : Type*} [Field k] [AddCommGroup V] [Module k V] [Field Ω] [Algebra k Ω]
    (T : Module.End k V) (φ : V →ₗ[k] Ω) : precompL T φ = φ ∘ₗ T := rfl

/-- The trace of precomposition by `T` on `Hom_k(V, Ω)` is the trace of `T`. -/
theorem trace_precompL {k V Ω : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Field Ω] [Algebra k Ω] (T : Module.End k V) :
    LinearMap.trace Ω (V →ₗ[k] Ω) (precompL T) = algebraMap k Ω (LinearMap.trace k V T) := by
  classical
  set b := Module.finBasis k V
  set e : (Fin (finrank k V) → Ω) ≃ₗ[Ω] (V →ₗ[k] Ω) := b.constr Ω with he
  set B : Basis (Fin (finrank k V)) Ω (V →ₗ[k] Ω) := (Pi.basisFun Ω _).map e with hB
  rw [LinearMap.trace_eq_matrix_trace Ω B, LinearMap.trace_eq_matrix_trace k b, Matrix.trace,
    Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have hBr : ∀ x, B.repr x i = x (b i) := fun x => by
    rw [hB, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, he, Basis.constr_symm_apply]
  have hBi : B i = b.constr Ω (Pi.single i 1) := by
    rw [hB, Basis.map_apply, Pi.basisFun_apply]
  rw [hBr, hBi]
  rw [precompL_apply, LinearMap.comp_apply, Basis.constr_apply_fintype,
    Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, smul_zero])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, Basis.equivFun_apply,
    Algebra.smul_def, mul_one]

theorem trace_precompHom {k V Ω F : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Field Ω] [Algebra k Ω] [Field F] (ρ : F →+* Module.End k V) (a : F) :
    LinearMap.trace Ω (V →ₗ[k] Ω) (precompHom ρ a) = algebraMap k Ω (LinearMap.trace k V (ρ a)) :=
  trace_precompL (ρ a)

/-! ## 3. `End⁰(A)` acts on `V_ℓ(A)` through a ring homomorphism -/

section Kernel

open PkgI3 PkgI3.AbVar LeafModCurves
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable (ℓ : ℕ) [Fact ℓ.Prime]

theorem homT_mul {K : Type} [Field K] (A : AbVar K) (e e' : A.End) :
    homT (ℓ := ℓ) (e * e') = homT (ℓ := ℓ) e ∘ₗ homT (ℓ := ℓ) e' := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ (e'.hom ≫ e.hom)) =
    Additive.ofMul ((Additive.toMul (x.1 n) ≫ e'.hom) ≫ e.hom)
  exact congrArg Additive.ofMul (Category.assoc _ _ _).symm

theorem homT_one {K : Type} [Field K] (A : AbVar K) :
    homT (ℓ := ℓ) (1 : A.End) = LinearMap.id := by
  apply LinearMap.ext; intro x; apply Subtype.ext; funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ 𝟙 _) = x.1 n
  rw [Category.comp_id]; rfl

theorem homVAdd_mul (A : AbVar ℚ) (e e' : A.End) :
    homVAdd ℓ A (e * e') = homVAdd ℓ A e * homVAdd ℓ A e' := by
  rw [homVAdd_apply, homVAdd_apply, homVAdd_apply, homT_mul, LinearMap.baseChange_comp]; rfl

theorem homVAdd_one (A : AbVar ℚ) : homVAdd ℓ A 1 = 1 := by
  rw [homVAdd_apply, homT_one, LinearMap.baseChange_id]; rfl

theorem endV_tmul (A : AbVar ℚ) (q : ℚ) (e : A.End) :
    endV ℓ A (q ⊗ₜ e) = (q : ℚ_[ℓ]) • homVAdd ℓ A e := by
  simp [endV]

theorem endV_one (A : AbVar ℚ) : endV ℓ A 1 = 1 := by
  rw [Algebra.TensorProduct.one_def, endV_tmul, homVAdd_one]; simp

theorem endV_mul (A : AbVar ℚ) (x y : A.End0) :
    endV ℓ A (x * y) = endV ℓ A x * endV ℓ A y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul q e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul q' e' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, endV_tmul, endV_tmul, endV_tmul, homVAdd_mul,
        Rat.cast_mul, smul_mul_smul_comm]
    | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
  | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]

/-- `θ` followed by `End⁰(A) → End(V_ℓ(A))`, as a ring homomorphism. -/
def rhoV (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0) :
    F →+* Module.End ℚ_[ℓ] (A.V ℓ) where
  toFun a := endV ℓ A (θ a)
  map_one' := by rw [map_one, endV_one]
  map_mul' a b := by rw [map_mul, endV_mul]
  map_zero' := by rw [map_zero, map_zero]
  map_add' a b := by rw [map_add, map_add]

/-- R16's `ι`-eigenfunctionals are the joint eigenspaces of `precompHom (rhoV θ)`. -/
theorem eigenFun_eq (A : AbVar ℚ) {F : Type} [Field F] (θ : F →+* A.End0)
    (emb : F →+* PadicAlgCl ℓ) :
    eigenFun ℓ A θ emb = jointEig (precompHom (Ω := PadicAlgCl ℓ) (rhoV ℓ A θ)) emb :=
  Submodule.ext fun _ => Iff.rfl

theorem eq_of_two_mul {d : WithBot ℕ∞} {n : ℕ}
    (h : (((2 * n : ℕ) : ℕ∞) : WithBot ℕ∞) = 2 * d) : d = (n : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.mul_bot (by norm_num)] at h
    exact absurd h WithBot.coe_ne_bot
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have : (2 : WithBot ℕ∞) * ((⊤ : ℕ∞) : WithBot ℕ∞) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_mul]
        congr 1
      rw [this] at h
      exact ENat.coe_ne_top _ (WithBot.coe_injective h)
    | coe m =>
      have h' : (((2 * n : ℕ) : ℕ∞) : WithBot ℕ∞) = (((2 * m : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [h]; push_cast; rfl
      have := Nat.cast_injective (WithBot.coe_injective h')
      have : n = m := by omega
      subst this; rfl

/-- **Glue (proved): the dimension clause from the rank-two clause.** If a number field `F` acts on
`A` (through `θ : F → End⁰(A)`) and every `ι`-eigenfunctional space of `V_2(A)` has dimension `2`,
then `dim A = [F : ℚ]`. Uses only `PkgI3.TateModuleFree` at `ℓ = 2`. -/
theorem dim_eq_of_rank_two (hT : PkgI3.TateModuleFree) (A : AbVar ℚ) {F : Type} [Field F]
    [Algebra ℚ F] [FiniteDimensional ℚ F] (θ : F →+* A.End0)
    (h2 : ∀ emb : F →+* PadicAlgCl 2, Module.finrank (PadicAlgCl 2) (eigenFun 2 A θ emb) = 2) :
    A.dim = ((Module.finrank ℚ F : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hfree, hfin, hrk⟩ := hT ℚ A 2 (by norm_num)
  have := hfree; have := hfin
  have hV : Module.finrank ℚ_[2] (A.V 2) = Module.finrank ℤ_[2] (A.T 2) :=
    Module.finrank_baseChange
  have hW : Module.finrank (PadicAlgCl 2) (A.V 2 →ₗ[ℚ_[2]] PadicAlgCl 2) =
      Module.finrank ℚ_[2] (A.V 2) := Module.finrank_linearMap_self _ _ _
  have hs := sum_finrank_jointEig (F := F) (Ω := PadicAlgCl 2) (precompHom (rhoV 2 A θ))
  have hc : ∑ κ : F →ₐ[ℚ] PadicAlgCl 2,
      Module.finrank (PadicAlgCl 2) (jointEig (precompHom (rhoV 2 A θ)) κ.toRingHom) =
      ∑ _κ : F →ₐ[ℚ] PadicAlgCl 2, 2 :=
    Finset.sum_congr rfl fun κ _ => by rw [← eigenFun_eq]; exact h2 _
  rw [hc, Finset.sum_const, Finset.card_univ, AlgHom.card, smul_eq_mul] at hs
  have hT2 : Module.finrank ℤ_[2] (A.T 2) = 2 * Module.finrank ℚ F := by omega
  rw [hT2] at hrk
  exact eq_of_two_mul hrk

/-- **Rational traces (from Mumford §19 Thm 4, `PkgI3.CharPolyIndepOfEll`).** Every element of
`End⁰(A)` has rational trace on `V_ℓ(A)`. -/
theorem trace_endV_rat (hCP : PkgI3.CharPolyIndepOfEll) (A : AbVar ℚ)
    [Module.Finite ℚ_[ℓ] (A.V ℓ)] (x : A.End0) :
    ∃ r : ℚ, LinearMap.trace ℚ_[ℓ] (A.V ℓ) (endV ℓ A x) = (r : ℚ_[ℓ]) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul q e =>
    obtain ⟨P, -, hP⟩ := hCP ℚ A e
    have h : LinearMap.trace ℚ_[ℓ] (A.V ℓ) ((homT (ℓ := ℓ) e).baseChange ℚ_[ℓ]) =
        ((-P.nextCoeff : ℤ) : ℚ_[ℓ]) := by
      rw [LinearMap.trace_eq_matrix_trace ℚ_[ℓ] (Module.finBasis ℚ_[ℓ] (A.V ℓ)),
        Matrix.trace_eq_neg_charpoly_nextCoeff,
        hP ℓ (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero) _ _,
        Polynomial.nextCoeff_map (Int.castRingHom ℚ_[ℓ]).injective_int]
      simp
    refine ⟨q * ((-P.nextCoeff : ℤ) : ℚ), ?_⟩
    rw [endV_tmul, map_smul, homVAdd_apply, h, smul_eq_mul]
    push_cast; rfl
  | add x y hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨r', hr'⟩ := hy
    exact ⟨r + r', by rw [map_add, map_add, hr, hr', Rat.cast_add]⟩

/-- **Glue (proved): the rank-two clause from the dimension clause.** If a number field `F` acts on
`A` through `θ` and `dim A = [F : ℚ]`, then every `ι`-eigenfunctional space of `V_ℓ(A)` has
dimension `2`. Uses `PkgI3.TateModuleFree` and `PkgI3.CharPolyIndepOfEll` (Mumford §19 Thm 4). -/
theorem rank_two_of_dim (hT : PkgI3.TateModuleFree) (hCP : PkgI3.CharPolyIndepOfEll)
    (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] (θ : F →+* A.End0)
    (hdim : A.dim = ((Module.finrank ℚ F : ℕ) : WithBot ℕ∞)) (emb : F →+* PadicAlgCl ℓ) :
    Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 := by
  obtain ⟨hfree, hfin, hrk⟩ := hT ℚ A ℓ (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)
  have := hfree; have := hfin
  set P := precompHom (Ω := PadicAlgCl ℓ) (rhoV ℓ A θ) with hPdef
  set d : (F →ₐ[ℚ] PadicAlgCl ℓ) → ℕ := fun κ => Module.finrank (PadicAlgCl ℓ)
    (jointEig P κ.toRingHom) with hd
  -- all weights equal
  have hrat : ∀ a : F, ∃ r : ℚ, ∑ κ : F →ₐ[ℚ] PadicAlgCl ℓ, (d κ : PadicAlgCl ℓ) * κ a =
      (r : PadicAlgCl ℓ) := by
    intro a
    obtain ⟨r, hr⟩ := trace_endV_rat ℓ hCP A (θ a)
    refine ⟨r, ?_⟩
    rw [← trace_eq_sum_jointEig P a, hPdef, trace_precompHom]
    change algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) (LinearMap.trace ℚ_[ℓ] (A.V ℓ) (endV ℓ A (θ a))) = _
    rw [hr, map_ratCast]
  have heq := weights_eq_of_rational d hrat
  -- the sum of the weights
  have hV : Module.finrank ℚ_[ℓ] (A.V ℓ) = Module.finrank ℤ_[ℓ] (A.T ℓ) :=
    Module.finrank_baseChange
  have hW : Module.finrank (PadicAlgCl ℓ) (A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) =
      Module.finrank ℚ_[ℓ] (A.V ℓ) := Module.finrank_linearMap_self _ _ _
  have hs := sum_finrank_jointEig (F := F) (Ω := PadicAlgCl ℓ) P
  rw [hdim] at hrk
  have hT2 : Module.finrank ℤ_[ℓ] (A.T ℓ) = 2 * Module.finrank ℚ F := by
    have h' : (((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((2 * Module.finrank ℚ F : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [hrk]; push_cast; rfl
    exact Nat.cast_injective (WithBot.coe_injective h')
  let κ := emb.toRatAlgHom
  have hκ : κ.toRingHom = emb := RingHom.toRatAlgHom_toRingHom emb
  have hc : ∑ κ' : F →ₐ[ℚ] PadicAlgCl ℓ, d κ' = ∑ _κ' : F →ₐ[ℚ] PadicAlgCl ℓ, d κ :=
    Finset.sum_congr rfl fun κ' _ => heq κ' κ
  rw [hc, Finset.sum_const, Finset.card_univ, AlgHom.card, smul_eq_mul, hW, hV, hT2] at hs
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have h2 : d κ = 2 := by
    have := Nat.eq_of_mul_eq_mul_left hpos (hs.trans (mul_comm _ _))
    exact this
  rw [eigenFun_eq, ← hκ]
  exact h2

end Kernel

/-! ## 4. The core leaf and the composition -/

section Core

open scoped MatrixGroups ModularForm
open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform scaleH
  oldSpace IsNewform)
open LeafModCurves
open WeierstrassCurve AlgebraicGeometry
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar

/-- **R16 without its dimension clause** (Eichler–Shimura for `J₁(N)`, existential form). Literally
`LeafModCurves.R16_EichlerShimuraJ1'` with the conjunct `A.dim = [K_f : ℚ]` deleted, so it is a
consequence of R16 and strictly weaker as a statement. Let `N ≥ 1`, `f ∈ S₂(Γ₁(N))` a newform with
nebentypus `χ`, and `J` a Jacobian of `X₁(N)` over `ℚ`. Then `K_f` is a number field, and there are
an abelian variety `A` over `ℚ`, a surjective homomorphism `π : J → A` and `θ : K_f → End⁰_ℚ(A)`
such that for every prime `ℓ` and every embedding `ι : K_f → ℚ̄_ℓ` the `ι`-component of `V_ℓ(A)` has
dimension `2`, and arithmetic Frobenius at every prime `p ∤ Nℓ` acts on it with trace `ι(a_p(f))`
and determinant `ι(χ(p))p`.

Sources (all at Shimura's `A_f = J₁(N)/I_f J₁(N)`; locators UNVERIFIED, no network):
* `A_f` is a quotient of `J₁(N)` defined over `ℚ`, with `K_f ↪ End⁰_ℚ(A_f)`: Shimura 1973
  (J. Math. Soc. Japan 25), Thm 1, unconditional clauses (audit row R16 of `docs/research/locators.md`);
  Shimura 1971, Thm 7.14; Diamond–Shurman §6.6 with §7.9 (field of definition).
* `K_f` is a number field: Shimura 1971, Thm 3.52; Diamond–Shurman §6.5.
* `V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ` (equivalently every `ι`-component has dimension 2):
  Shimura 1971 §7.4 / Ribet 1977; Diamond–Shurman Lemma 9.5.3.
* characteristic polynomial `X² − a_p X + χ(p)p` of arithmetic Frobenius on `V_ℓ(A_f)` over
  `K_f ⊗ ℚ_ℓ` for `p ∤ Nℓ`: Diamond–Shurman Thm 9.5.4; Shimura 1971 Thm 7.11 (from the
  Eichler–Shimura congruence relation, Shimura 1971 Thm 7.9).
GLUE (composite) until `A_f` and the Hecke algebra are Lean definitions (see the report). -/
def R16CoreX : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J →
    FiniteDimensional ℚ (coeffField f) ∧
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
      Surjective π.hom.left ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 ∧
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          (∀ a : coeffField f, (a : ℂ) = coeff f p →
              LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
          (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
              LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p)

/-- **R16 from its core and `T_ℓ` free of rank `2 dim A`.** -/
theorem r16_of_coreX (hC : R16CoreX) (hT : PkgI3.TateModuleFree) :
    LeafModCurves.R16_EichlerShimuraJ1' := by
  intro N χ f J hN hf hJ
  obtain ⟨hfin, A, π, θ, hs, hgal⟩ := hC N χ f J hN hf hJ
  exact ⟨hfin, A, π, θ, hs, dim_eq_of_rank_two hT A θ (fun emb => (hgal 2 emb).1), hgal⟩

/-- Conversely the core is a consequence of R16 (it is R16 with one conjunct deleted). -/
theorem coreX_of_r16 (h : LeafModCurves.R16_EichlerShimuraJ1') : R16CoreX := by
  intro N χ f J hN hf hJ
  obtain ⟨hfin, A, π, θ, hs, -, hgal⟩ := h N χ f J hN hf hJ
  exact ⟨hfin, A, π, θ, hs, hgal⟩

/-- **R16 without its rank-two clause** (Eichler–Shimura for `J₁(N)`, existential form). Literally
`LeafModCurves.R16_EichlerShimuraJ1'` with the conjunct "the `ι`-component of `V_ℓ(A)` has
dimension 2" deleted, so it is a consequence of R16. `K_f` is a number field, and there are an
abelian variety `A` over `ℚ`, a surjective homomorphism `π : J → A` and `θ : K_f → End⁰_ℚ(A)` with
`dim A = [K_f : ℚ]` such that arithmetic Frobenius at every prime `p ∤ Nℓ` acts on every
`ι`-component of `V_ℓ(A)` with trace `ι(a_p(f))` and determinant `ι(χ(p))p`.

Sources (at Shimura's `A_f`; locators UNVERIFIED): Shimura 1973 Thm 1, unconditional clauses
(audit row R16) for `A_f`, `θ`, `dim A_f = [K_f : ℚ]`; Shimura 1971 Thm 3.52 for `[K_f : ℚ] < ∞`;
Diamond–Shurman Thm 9.5.4 / Shimura 1971 Thm 7.11 for the characteristic polynomial of Frobenius
(from the congruence relation, Shimura 1971 Thm 7.9). Compared with R16 the source "V_ℓ(A_f) is
free of rank 2 over `K_f ⊗ ℚ_ℓ`" (Shimura 1971 §7.4, Ribet 1977) is no longer needed: it is proved
from `dim A_f = [K_f : ℚ]` and Mumford §19 Thm 4 (`rank_two_of_dim`). GLUE (composite). -/
def R16CoreY : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (J : AbVar ℚ),
    0 < N → IsNewform f χ → IsJ1 N J →
    FiniteDimensional ℚ (coeffField f) ∧
    ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
      Surjective π.hom.left ∧
      A.dim = ((Module.finrank ℚ (coeffField f) : ℕ) : WithBot ℕ∞) ∧
      ∀ (ℓ : ℕ) [Fact ℓ.Prime] (emb : coeffField f →+* PadicAlgCl ℓ),
        ∀ (p : ℕ), p.Prime → ¬ p ∣ N * ℓ → ∀ σ : GQ, IsFrobAt σ p →
          (∀ a : coeffField f, (a : ℂ) = coeff f p →
              LinearMap.trace (PadicAlgCl ℓ) _ (frobOn ℓ A θ emb σ) = emb a) ∧
          (∀ c : coeffField f, (c : ℂ) = χ (p : ZMod N) →
              LinearMap.det (frobOn ℓ A θ emb σ) = emb c * p)

/-- **R16 from its core without the rank-two clause, `TateModuleFree` and Mumford §19 Thm 4.** -/
theorem r16_of_coreY (hC : R16CoreY) (hT : PkgI3.TateModuleFree)
    (hCP : PkgI3.CharPolyIndepOfEll) : LeafModCurves.R16_EichlerShimuraJ1' := by
  intro N χ f J hN hf hJ
  obtain ⟨hfin, A, π, θ, hs, hdim, hgal⟩ := hC N χ f J hN hf hJ
  exact ⟨hfin, A, π, θ, hs, hdim, fun ℓ _ emb =>
    ⟨rank_two_of_dim ℓ hT hCP A θ hdim emb, hgal ℓ emb⟩⟩

/-- The core is a consequence of R16. -/
theorem coreY_of_r16 (h : LeafModCurves.R16_EichlerShimuraJ1') : R16CoreY := by
  intro N χ f J hN hf hJ
  obtain ⟨hfin, A, π, θ, hs, hdim, hgal⟩ := h N χ f J hN hf hJ
  exact ⟨hfin, A, π, θ, hs, hdim, fun ℓ _ emb => (hgal ℓ emb).2⟩

end Core

end R16Split

#print axioms R16Split.r16_of_coreX
#print axioms R16Split.coreX_of_r16
#print axioms R16Split.sum_finrank_jointEig
#print axioms R16Split.r16_of_coreY
#print axioms R16Split.coreY_of_r16

