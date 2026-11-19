import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Tate

/-!
# Lane RC28 round 2, part 4: the `Λ`-adic coefficient module `𝕋 = T_2E ⊗_{ℤ₂} Λ(α)`

Manuscript `diophantine_zq.tex` (11/5): finite coefficients at tex 2723–2727;
`Λ = ℤ₂[[t]]` at tex 2747; `T = T₂E` at tex 2836–2838. The module below is the
conditional fixed-character construction described in the following paragraph, not a global
moving-character module asserted at tex 2780–2785.
Height-one fibres `R = Λ_𝔭`: tex 4976–5200.

* `IsContChar α`: a character `α : G_{K,S} → Λˣ` continuous for the product topology of `Λ`;
  `isContChar_lambdaChar`: `α = χ_h Ψ` is one (for `χ_h` with open kernel and continuous `ξ`).
* **`TLam K S W α = Λ ⊗_{ℤ₂} T_2E`**, a `Λ`-module, with the genuine twisted Galois action
  `σ (λ ⊗ P) = α(σ) λ ⊗ σP` (`Λ`-linear: `SMulCommClass`), `TLam.smul_tmul`.
* **The topology**: `lamIdeal n = (2^n, t^n)`; the submodules `(2^n, t^n) 𝕋` form a basis of
  neighbourhoods of zero (`submodulesBasis_tlam`): this is the `(2, t)`-adic topology (the product
  topology on `Λ² ≅ 𝕋` once `T_2E ≅ ℤ₂²`). `𝕋` is a topological group, a topological `Λ`-module
  (`ContinuousSMul Λ 𝕋`), and **the Galois action is continuous** (`ContinuousSMul (GKS K S) 𝕋`).
  The key inputs: `lamIdeal_mem_nhds` (the ideals are open in `Λ`), `mem_ker_projLev_iff`
  (`ker (T → E[2^n]) = 2^n T`) and the continuity of `α`.

Kinds: definitions and PROVED.
-/

/-!
This is a conditional construction for one supplied continuous Λ-valued character on a fixed
G_{K,S}. Its finite levels are the compatible reductions of that character. The manuscript's
moving characters have conductor primes varying with precision and need not be reductions of
one character (tex 2737–2741, 4269–4277). No identification with the retained inner-limit Selmer
diagrams is proved here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.LambdaCoef

open NumberField IsDedekindDomain PowerSeries Filter Topology TensorProduct
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (IsOpenKer isOpen_stabilizer_torsS)
open scoped PowerSeries.WithPiTopology Pointwise

attribute [local instance] lambda_isTopologicalRing

/-! ### Open ideals of `Λ` -/

/-- `(2^n) ⊆ ℤ₂` is open. Kind: PROVED. -/
theorem isOpen_span_two_pow (n : ℕ) :
    IsOpen ((Ideal.span {(2 : ℤ_[2]) ^ n} : Ideal ℤ_[2]) : Set ℤ_[2]) := by
  have h : ((Ideal.span {(2 : ℤ_[2]) ^ n} : Ideal ℤ_[2]) : Set ℤ_[2]) =
      Metric.closedBall 0 ((2 : ℝ) ^ (-(n : ℤ))) := by
    ext x
    rw [SetLike.mem_coe, Metric.mem_closedBall, dist_zero_right]
    have := PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) x n
    push_cast at this
    exact this.symm
  rw [h]
  exact IsUltrametricDist.isOpen_closedBall _ (by positivity)

/-- **The ideal `(2^n, t^n)` of `Λ`.** -/
def lamIdeal (n : ℕ) : Ideal Lambda := Ideal.span {(2 : Lambda) ^ n, (X : Lambda) ^ n}

theorem two_pow_mem_lamIdeal (n : ℕ) : (2 : Lambda) ^ n ∈ lamIdeal n :=
  Ideal.subset_span (by simp)

theorem X_pow_mem_lamIdeal (n : ℕ) : (X : Lambda) ^ n ∈ lamIdeal n :=
  Ideal.subset_span (by simp)

theorem lamIdeal_antitone {m n : ℕ} (h : n ≤ m) : lamIdeal m ≤ lamIdeal n := by
  rw [lamIdeal, Ideal.span_le]
  rintro x (rfl | rfl)
  · rw [← Nat.add_sub_cancel' h, pow_add]
    exact Ideal.mul_mem_right _ _ (two_pow_mem_lamIdeal n)
  · rw [← Nat.add_sub_cancel' h, pow_add]
    exact Ideal.mul_mem_right _ _ (X_pow_mem_lamIdeal n)

/-- A power series whose first `n` coefficients are divisible by `2^n` lies in `(2^n, t^n)`.
Kind: PROVED. -/
theorem mem_lamIdeal_of_coeff (n : ℕ) (a : Lambda)
    (ha : ∀ k < n, coeff k a ∈ (Ideal.span {(2 : ℤ_[2]) ^ n} : Ideal ℤ_[2])) : a ∈ lamIdeal n := by
  classical
  have hd : ∀ k < n, ∃ d : ℤ_[2], d * 2 ^ n = coeff k a := fun k hk =>
    Ideal.mem_span_singleton'.mp (ha k hk)
  let b : Lambda := mk fun k => if h : k < n then Classical.choose (hd k h) else 0
  let c : Lambda := mk fun k => coeff (k + n) a
  have hC : ((2 : Lambda) ^ n) = C ((2 : ℤ_[2]) ^ n) := by rw [map_pow, map_ofNat]
  have hab : a = (2 : Lambda) ^ n * b + (X : Lambda) ^ n * c := by
    refine PowerSeries.ext fun m => ?_
    rw [map_add, coeff_X_pow_mul', hC, coeff_C_mul]
    by_cases hm : m < n
    · rw [if_neg (not_le.mpr hm), add_zero, coeff_mk, dif_pos hm, mul_comm]
      exact (Classical.choose_spec (hd m hm)).symm
    · rw [if_pos (not_lt.mp hm), coeff_mk, dif_neg hm, mul_zero, zero_add, coeff_mk,
        Nat.sub_add_cancel (not_lt.mp hm)]
  rw [hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (two_pow_mem_lamIdeal n))
    (Ideal.mul_mem_right _ _ (X_pow_mem_lamIdeal n))

/-- **`(2^n, t^n)` is a neighbourhood of zero in `Λ`** (product topology). Kind: PROVED. -/
theorem lamIdeal_mem_nhds (n : ℕ) : ((lamIdeal n : Ideal Lambda) : Set Lambda) ∈ 𝓝 (0 : Lambda) := by
  have hopen : IsOpen (⋂ k ∈ Finset.range n,
      (coeff k : Lambda → ℤ_[2]) ⁻¹' ((Ideal.span {(2 : ℤ_[2]) ^ n} : Ideal ℤ_[2]) : Set ℤ_[2])) :=
    isOpen_biInter_finset fun k _ =>
      (PowerSeries.WithPiTopology.continuous_coeff ℤ_[2] k).isOpen_preimage _
        (isOpen_span_two_pow n)
  refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
  · simp only [Set.mem_iInter, Set.mem_preimage, map_zero, SetLike.mem_coe]
    exact fun _ _ => Submodule.zero_mem _
  · intro a ha
    simp only [Set.mem_iInter, Set.mem_preimage, Finset.mem_range, SetLike.mem_coe] at ha
    exact mem_lamIdeal_of_coeff n a ha

/-! ### Continuous characters -/

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K}

/-- A character `α : G_{K,S} → Λˣ` continuous for the product topology of `Λ`. -/
class IsContChar (α : GKS K S →* Lambdaˣ) : Prop where
  continuous_coe : Continuous fun σ => ((α σ : Lambdaˣ) : Lambda)

/-- A character `ξ : G_{K,S} → ℤ₂` that is continuous. -/
class IsContZ2Char (ξ : GKS K S →* Multiplicative ℤ_[2]) : Prop where
  continuous_toAdd : Continuous fun σ => Multiplicative.toAdd (ξ σ)

/-- **`α = χ_h Ψ` is continuous** (tex 2780–2791). Kind: PROVED. -/
instance isContChar_lambdaChar (χ : GKS K S →* ℤˣ) [IsOpenKer χ]
    (ξ : GKS K S →* Multiplicative ℤ_[2]) [hξ : IsContZ2Char ξ] : IsContChar (lambdaChar χ ξ) :=
  ⟨continuous_lambdaChar χ ξ hξ.continuous_toAdd⟩

/-- Non-vacuity: the trivial `ℤ₂`-character is continuous. -/
instance isContZ2Char_one : IsContZ2Char (1 : GKS K S →* Multiplicative ℤ_[2]) :=
  ⟨continuous_const⟩

theorem eventually_sub_one_mem (α : GKS K S →* Lambdaˣ) [hα : IsContChar α] (n : ℕ) :
    ∀ᶠ σ in 𝓝 (1 : GKS K S), ((α σ : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal n := by
  have hc : Tendsto (fun σ => ((α σ : Lambdaˣ) : Lambda) - 1) (𝓝 (1 : GKS K S)) (𝓝 0) :=
    (hα.continuous_coe.sub continuous_const).tendsto' _ _ (by simp)
  exact hc (lamIdeal_mem_nhds n)

/-! ### The module `𝕋` -/

variable (K S W) in
/-- **`𝕋 = Λ ⊗_{ℤ₂} T_2E` with the action twisted by `α`** (tex 2747, 2836–2838). -/
@[nolint unusedArguments]
def TLam (_α : GKS K S →* Lambdaˣ) : Type := Lambda ⊗[ℤ_[2]] TateS K S W

variable (α : GKS K S →* Lambdaˣ)

instance : AddCommGroup (TLam K S W α) := inferInstanceAs (AddCommGroup (Lambda ⊗[ℤ_[2]] _))

instance : Module Lambda (TLam K S W α) := inferInstanceAs (Module Lambda (Lambda ⊗[ℤ_[2]] _))

instance : Module ℤ_[2] (TLam K S W α) := inferInstanceAs (Module ℤ_[2] (Lambda ⊗[ℤ_[2]] _))

instance : IsScalarTower ℤ_[2] Lambda (TLam K S W α) :=
  inferInstanceAs (IsScalarTower ℤ_[2] Lambda (Lambda ⊗[ℤ_[2]] _))

/-- The underlying tensor product. -/
def TLam.equiv : TLam K S W α ≃ₗ[Lambda] Lambda ⊗[ℤ_[2]] TateS K S W := LinearEquiv.refl _ _

/-- Induction on `𝕋`. -/
theorem TLam.induction {motive : TLam K S W α → Prop} (x : TLam K S W α) (zero : motive 0)
    (tmul : ∀ (l : Lambda) (P : TateS K S W), motive (show TLam K S W α from l ⊗ₜ P))
    (add : ∀ x y : TLam K S W α, motive x → motive y → motive (x + y)) : motive x :=
  TensorProduct.induction_on x zero tmul add

variable (K S W) in
/-- `σ` acting `ℤ₂`-linearly on `T_2E`. -/
def actLin (σ : GKS K S) : TateS K S W →ₗ[ℤ_[2]] TateS K S W where
  toFun P := σ • P
  map_add' := smul_add σ
  map_smul' a P := smul_comm σ a P

variable {α}

/-- The twisted action, `Λ`-linear. -/
def TLam.act (σ : GKS K S) : TLam K S W α →ₗ[Lambda] TLam K S W α :=
  ((α σ : Lambdaˣ) : Lambda) • (actLin K S W σ).baseChange Lambda

theorem TLam.act_tmul (σ : GKS K S) (l : Lambda) (P : TateS K S W) :
    TLam.act (α := α) σ (show TLam K S W α from l ⊗ₜ P) =
      show TLam K S W α from (((α σ : Lambdaˣ) : Lambda) * l) ⊗ₜ (σ • P) := by
  change ((α σ : Lambdaˣ) : Lambda) • (l ⊗ₜ[ℤ_[2]] (σ • P)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul]

theorem TLam.act_one (x : TLam K S W α) : TLam.act (α := α) 1 x = x := by
  induction x using TLam.induction with
  | zero => exact map_zero _
  | tmul l P => rw [TLam.act_tmul, map_one, Units.val_one, one_mul, one_smul]
  | add x y hx hy => rw [map_add, hx, hy]

theorem TLam.act_mul (σ τ : GKS K S) (x : TLam K S W α) :
    TLam.act (α := α) (σ * τ) x = TLam.act σ (TLam.act τ x) := by
  induction x using TLam.induction with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul l P =>
    rw [TLam.act_tmul, TLam.act_tmul, TLam.act_tmul, map_mul, Units.val_mul, mul_smul, mul_assoc]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

/-- **The genuine Galois action on `𝕋`**: `σ (λ ⊗ P) = α(σ) λ ⊗ σ P`. -/
instance tlam_distribMulAction : DistribMulAction (GKS K S) (TLam K S W α) where
  smul σ x := TLam.act σ x
  one_smul := TLam.act_one
  mul_smul := TLam.act_mul
  smul_zero σ := map_zero _
  smul_add σ := map_add _

theorem TLam.smul_def (σ : GKS K S) (x : TLam K S W α) : σ • x = TLam.act σ x := rfl

theorem TLam.smul_tmul (σ : GKS K S) (l : Lambda) (P : TateS K S W) :
    σ • (show TLam K S W α from l ⊗ₜ P) =
      show TLam K S W α from (((α σ : Lambdaˣ) : Lambda) * l) ⊗ₜ (σ • P) :=
  TLam.act_tmul σ l P

/-- The Galois action is `Λ`-linear. Kind: PROVED. -/
instance tlam_smulCommClass : SMulCommClass (GKS K S) Lambda (TLam K S W α) where
  smul_comm σ a x := (TLam.act σ).map_smul a x

/-! ### The `(2, t)`-adic topology -/

variable (K S W α) in
/-- The basic neighbourhoods `(2^n, t^n) 𝕋`. -/
def tlamNbhd (n : ℕ) : Submodule Lambda (TLam K S W α) := lamIdeal n • ⊤

theorem submodulesBasis_tlam : SubmodulesBasis (tlamNbhd K S W α) where
  inter i j := ⟨max i j, le_inf (Submodule.smul_mono_left (lamIdeal_antitone (le_max_left i j)))
    (Submodule.smul_mono_left (lamIdeal_antitone (le_max_right i j)))⟩
  smul m i := by
    filter_upwards [lamIdeal_mem_nhds i] with a ha
    exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- **The `(2, t)`-adic topology on `𝕋`.** -/
instance tlamTop : TopologicalSpace (TLam K S W α) :=
  (submodulesBasis_tlam (K := K) (S := S) (W := W) (α := α)).topology

instance tlam_isTopologicalAddGroup : IsTopologicalAddGroup (TLam K S W α) :=
  AddGroupFilterBasis.isTopologicalAddGroup _

/-- **`𝕋` is a topological `Λ`-module.** Kind: PROVED. -/
instance tlam_continuousSMul_lambda : ContinuousSMul Lambda (TLam K S W α) :=
  ModuleFilterBasis.continuousSMul _

/-- The basic neighbourhoods of zero. Kind: PROVED. -/
theorem tlam_hasBasis_nhds_zero :
    (𝓝 (0 : TLam K S W α)).HasBasis (fun _ => True) (fun n => (tlamNbhd K S W α n : Set _)) := by
  have h := (submodulesBasis_tlam (K := K) (S := S) (W := W) (α := α)).toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis
  refine ⟨fun t => ?_⟩
  rw [h.mem_iff]
  constructor
  · rintro ⟨V, ⟨i, rfl⟩, hV⟩
    exact ⟨i, trivial, hV⟩
  · rintro ⟨i, -, hi⟩
    exact ⟨_, ⟨i, rfl⟩, hi⟩

theorem act_mem_tlamNbhd (σ : GKS K S) (n : ℕ) {x : TLam K S W α} (hx : x ∈ tlamNbhd K S W α n) :
    σ • x ∈ tlamNbhd K S W α n := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ?_) (fun x y hx hy => ?_)
  · rw [smul_comm]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [smul_add]
    exact Submodule.add_mem _ hx hy

theorem tate_pt_sub (P Q : TateS K S W) (n : ℕ) : (P - Q).pt n = P.pt n - Q.pt n := rfl

/-- Near `1`, `σ P - P ∈ 2^n T_2E`. Kind: PROVED. -/
theorem eventually_smul_sub_mem (P : TateS K S W) (n : ℕ) :
    ∀ᶠ σ in 𝓝 (1 : GKS K S), ∃ Q : TateS K S W, (2 : ℤ_[2]) ^ n • Q = σ • P - P := by
  have hopen := isOpen_stabilizer_torsS (projLev (K := K) (S := S) (W := W) n P)
  filter_upwards [hopen.mem_nhds (MulAction.stabilizer _ _).one_mem] with σ hσ
  refine (mem_ker_projLev_iff n (σ • P - P)).mp ?_
  have hσ' : σ • projLev n P = projLev n P := hσ
  rw [tate_pt_sub, ← coe_projLev, ← coe_projLev, projLev_smul, hσ', sub_self]

theorem smul_tmul_sub_mem (σ : GKS K S) (n : ℕ) (l : Lambda) (P : TateS K S W)
    (hα : ((α σ : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal n)
    (hP : ∃ Q : TateS K S W, (2 : ℤ_[2]) ^ n • Q = σ • P - P) :
    σ • (show TLam K S W α from l ⊗ₜ P) - (show TLam K S W α from l ⊗ₜ P) ∈
      tlamNbhd K S W α n := by
  obtain ⟨Q, hQ⟩ := hP
  rw [TLam.smul_tmul]
  have h2 : ((2 : Lambda) ^ n * l) ⊗ₜ[ℤ_[2]] Q = l ⊗ₜ[ℤ_[2]] ((2 : ℤ_[2]) ^ n • Q) := by
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, map_pow, map_ofNat]
  have e : ((((α σ : Lambdaˣ) : Lambda) * l) ⊗ₜ[ℤ_[2]] (σ • P) - l ⊗ₜ[ℤ_[2]] P :
      Lambda ⊗[ℤ_[2]] TateS K S W) =
      (((α σ : Lambdaˣ) : Lambda) - 1) • (l ⊗ₜ[ℤ_[2]] (σ • P)) +
        ((2 : Lambda) ^ n) • (l ⊗ₜ[ℤ_[2]] Q) := by
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, sub_mul,
      one_mul, TensorProduct.sub_tmul, h2, hQ, TensorProduct.tmul_sub]
    abel
  have e' : (show TLam K S W α from (((α σ : Lambdaˣ) : Lambda) * l) ⊗ₜ (σ • P)) -
      (show TLam K S W α from l ⊗ₜ P) =
      (((α σ : Lambdaˣ) : Lambda) - 1) • (show TLam K S W α from l ⊗ₜ (σ • P)) +
        ((2 : Lambda) ^ n) • (show TLam K S W α from l ⊗ₜ Q) := e
  rw [e']
  exact Submodule.add_mem _ (Submodule.smul_mem_smul hα Submodule.mem_top)
    (Submodule.smul_mem_smul (two_pow_mem_lamIdeal n) Submodule.mem_top)

/-- **The Galois action on `𝕋` is continuous** for its `(2, t)`-adic topology. Kind: PROVED. -/
instance tlam_continuousSMul [IsContChar α] : ContinuousSMul (GKS K S) (TLam K S W α) := by
  refine continuousSMul_of_hasBasis (fun n => (tlamNbhd K S W α n).toAddSubgroup)
    tlam_hasBasis_nhds_zero (fun σ n x hx => act_mem_tlamNbhd σ n hx) (fun v n => ?_)
  induction v using TLam.induction with
  | zero => exact Eventually.of_forall fun σ => by rw [smul_zero, sub_zero]; exact Submodule.zero_mem _
  | tmul l P =>
    filter_upwards [eventually_sub_one_mem α n, eventually_smul_sub_mem P n] with σ h1 h2
    exact smul_tmul_sub_mem σ n l P h1 h2
  | add x y hx hy =>
    filter_upwards [hx, hy] with σ h1 h2
    rw [smul_add, add_sub_add_comm]
    exact Submodule.add_mem _ h1 h2

end ZInQ.Manuscript.RC.LambdaCoef
