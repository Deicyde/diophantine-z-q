import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.TateBasis
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Bridge
import ZInQKernel.Contrib.OneProof.RC.CoefModules.NonVacuity

/-!
# Lane RC28 round 2: ranks of `𝕋 = Λ ⊗ T_2E` and of its fibres `V_𝔭`

Manuscript `diophantine_zq.tex` (11/5): finite coefficients at tex 2723–2727; `Λ = ℤ₂[[t]]` at
tex 2747; `T = T₂E` at tex 2836–2838. Here `𝕋 = (T_2E ⊗ Λ)(α)` is the conditional
fixed-character construction described in the paragraph below, not a global moving-character
module asserted at tex 2780–2785. Tex 4976–5200: the characteristic-zero fibres over
`R = Λ_𝔭`, `k = k(𝔭)`. Under `E[2^∞] ⊆ E(K_S)`
(`HasFullTwoTorsion`, GLUE input: Néron–Ogg–Shafarevich, Silverman AEC VII.7.1):

* `tlamBasis`: a `Λ`-basis of `𝕋` indexed by `Fin 2` (base change of `tateBasis`); `𝕋` is free and
  finite of rank `2` (`finrank_tlam`);
* `vpBasis`: a `k(𝔭)`-basis of `V_𝔭`, `finrank_vp`: `V_𝔭` is a `2`-dimensional `k(𝔭)`-vector
  space, nontrivial and finite-dimensional;
* `fibreEquiv`: **`V_𝔭 = 𝕋 ⊗_Λ k(𝔭)`** as `k(𝔭)`-modules (no hypothesis), Galois equivariant for
  `id ⊗ σ` (`fibreEquiv_baseChange_act`);
* **the `(2, t)`-adic topology of `𝕋` is the product topology of `Λ²` through the basis**:
  `continuous_tlam_repr`, `continuous_tlam_basis_sum`, `tlamHomeomorph : 𝕋 ≃ₜ Λ²`;
* non-vacuity examples over `ℚ`, all primes, `E_1`, `𝔭 = (t)`, `α = 1`.

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
open Module (Basis)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open scoped PowerSeries.WithPiTopology Pointwise

attribute [local instance] lambda_isTopologicalRing

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} {α : GKS K S →* Lambdaˣ}

/-! ### The `Λ`-basis of `𝕋` -/

/-- **A `Λ`-basis of `𝕋 = Λ ⊗_{ℤ₂} T_2E`**: `1 ⊗ e_i` for the `ℤ₂`-basis `e` of `T_2E`.
Kind: definition (tex 2747, 2836–2838). -/
def tlamBasis [W.IsElliptic] [HasFullTwoTorsion K S W] : Basis (Fin 2) Lambda (TLam K S W α) :=
  (Algebra.TensorProduct.basis Lambda (tateBasis (K := K) (S := S) (W := W))).map
    (TLam.equiv α).symm

/-- The basis vectors. Kind: PROVED (tex 2747, 2836–2838). -/
theorem tlamBasis_apply [W.IsElliptic] [HasFullTwoTorsion K S W] (i : Fin 2) :
    (tlamBasis (α := α) i : TLam K S W α) =
      show TLam K S W α from (1 : Lambda) ⊗ₜ (tateBasis i : TateS K S W) := by
  rw [tlamBasis, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
  rfl

/-- `𝕋` is a free `Λ`-module. Kind: PROVED (tex 2747, 2836–2838). -/
instance tlam_free [W.IsElliptic] [HasFullTwoTorsion K S W] : Module.Free Lambda (TLam K S W α) :=
  Module.Free.of_basis tlamBasis

/-- `𝕋` is a finite `Λ`-module. Kind: PROVED (tex 2747, 2836–2838). -/
instance tlam_finite [W.IsElliptic] [HasFullTwoTorsion K S W] :
    Module.Finite Lambda (TLam K S W α) :=
  Module.Finite.of_basis tlamBasis

/-- **`rank_Λ 𝕋 = 2`.** Kind: PROVED (tex 2747, 2836–2838). -/
theorem finrank_tlam [W.IsElliptic] [HasFullTwoTorsion K S W] :
    Module.finrank Lambda (TLam K S W α) = 2 := by
  rw [Module.finrank_eq_card_basis (tlamBasis (K := K) (S := S) (W := W) (α := α)),
    Fintype.card_fin]

/-! ### The `k(𝔭)`-basis of `V_𝔭` -/

variable (P : Ideal Lambda) [P.IsPrime]

variable {P} in
/-- `V_𝔭` is the tensor product `k(𝔭) ⊗_{ℤ₂} T_2E`. Kind: definition (tex 4976–5200). -/
def vpEquiv : VP K S W P α ≃ₗ[ResAt P] ResAt P ⊗[ℤ_[2]] TateS K S W := LinearEquiv.refl _ _

/-- **A `k(𝔭)`-basis of `V_𝔭`**: `1 ⊗ e_i`. Kind: definition (tex 4976–5200). -/
def vpBasis [W.IsElliptic] [HasFullTwoTorsion K S W] : Basis (Fin 2) (ResAt P) (VP K S W P α) :=
  (Algebra.TensorProduct.basis (ResAt P) (tateBasis (K := K) (S := S) (W := W))).map
    (vpEquiv (P := P) (α := α)).symm

/-- **`V_𝔭` is a `2`-dimensional vector space over `k(𝔭)`** (of characteristic zero for a
height-one `𝔭 ≠ (2)`, `charZero_fibreField`). Kind: PROVED (tex 4976–5200). -/
theorem finrank_vp [W.IsElliptic] [HasFullTwoTorsion K S W] :
    Module.finrank (ResAt P) (VP K S W P α) = 2 := by
  rw [Module.finrank_eq_card_basis (vpBasis (K := K) (S := S) (W := W) (α := α) P),
    Fintype.card_fin]

/-- `V_𝔭` is nonzero. Kind: PROVED (tex 4976–5200). -/
instance vp_nontrivial [W.IsElliptic] [HasFullTwoTorsion K S W] :
    Nontrivial (VP K S W P α) :=
  Module.nontrivial_of_finrank_pos (R := ResAt P) (by rw [finrank_vp]; norm_num)

/-- `V_𝔭` is finite-dimensional over `k(𝔭)`. Kind: PROVED (tex 4976–5200). -/
instance vp_finiteDimensional [W.IsElliptic] [HasFullTwoTorsion K S W] :
    FiniteDimensional (ResAt P) (VP K S W P α) :=
  Module.Finite.of_basis (vpBasis P)

/-! ### `V_𝔭 = 𝕋 ⊗_Λ k(𝔭)` -/

variable {P} in
/-- **`k(𝔭) ⊗_Λ 𝕋 ≃ V_𝔭`** (cancel the base change `Λ ⊗_{ℤ₂}`; no hypothesis on the curve).
Kind: definition (tex 4976–5200). -/
def fibreEquiv : ResAt P ⊗[Lambda] TLam K S W α ≃ₗ[ResAt P] VP K S W P α :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[2] Lambda (ResAt P) (ResAt P)
    (TateS K S W)

/-- `fibreEquiv (c ⊗ (l ⊗ Q)) = (c l̄) ⊗ Q`. Kind: PROVED (tex 4976–5200). -/
theorem fibreEquiv_tmul (c : ResAt P) (l : Lambda) (Q : TateS K S W) :
    fibreEquiv (c ⊗ₜ (show TLam K S W α from l ⊗ₜ Q)) =
      show VP K S W P α from (c * algebraMap Lambda (ResAt P) l) ⊗ₜ Q := by
  change (l • c) ⊗ₜ[ℤ_[2]] Q = (c * algebraMap Lambda (ResAt P) l) ⊗ₜ[ℤ_[2]] Q
  rw [Algebra.smul_def, mul_comm]

/-- **`fibreEquiv` is Galois equivariant**: `id ⊗ σ` on `k(𝔭) ⊗_Λ 𝕋` corresponds to the twisted
action on `V_𝔭`. Kind: PROVED (tex 4976–5200). -/
theorem fibreEquiv_baseChange_act (σ : GKS K S) (x : ResAt P ⊗[Lambda] TLam K S W α) :
    fibreEquiv ((TLam.act (α := α) σ).baseChange (ResAt P) x) = σ • fibreEquiv x := by
  induction x using TensorProduct.inductionOn with
  | tmul c y =>
    induction y using TLam.induction with
    | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero, smul_zero]
    | tmul l Q =>
      rw [LinearMap.baseChange_tmul, TLam.act_tmul, fibreEquiv_tmul, fibreEquiv_tmul,
        VP.smul_tmul, coe_resChar]
      have e : c * algebraMap Lambda (ResAt P) (((α σ : Lambdaˣ) : Lambda) * l) =
          algebraMap Lambda (ResAt P) ((α σ : Lambdaˣ) : Lambda) *
            (c * algebraMap Lambda (ResAt P) l) := by
        rw [map_mul]
        ring
      rw [e]
    | add y z hy hz => rw [TensorProduct.tmul_add, map_add, map_add, hy, hz, map_add, smul_add]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, smul_add]

/-! ### The topology of `𝕋` is the product topology through the basis -/

/-- An element of `(2^n, t^n)` has its first `n` coefficients in `2^n ℤ₂`. Kind: PROVED
(tex 2747). -/
theorem coeff_mem_of_mem_lamIdeal {n k : ℕ} (hk : k < n) {a : Lambda} (ha : a ∈ lamIdeal n) :
    coeff k a ∈ (Ideal.span {(2 : ℤ_[2]) ^ n} : Ideal ℤ_[2]) := by
  obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.mp ha
  have hC : ((2 : Lambda) ^ n) = C ((2 : ℤ_[2]) ^ n) := by rw [map_pow, map_ofNat]
  rw [map_add, hC, coeff_mul_C, coeff_mul_X_pow']
  simp only [show ¬ n ≤ k from not_le.mpr hk, ↓reduceIte, add_zero]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- `2^m ℤ₂` lies in the closed ball of radius `2^-m`. Kind: PROVED (tex 2747). -/
theorem norm_le_of_mem_span_two_pow {m : ℕ} {y : ℤ_[2]}
    (hy : y ∈ (Ideal.span {(2 : ℤ_[2]) ^ m} : Ideal ℤ_[2])) : ‖y‖ ≤ ((1 : ℝ) / 2) ^ m := by
  have h := PadicInt.norm_le_pow_iff_mem_span_pow (p := 2) y m
  push_cast at h
  rw [one_div, inv_pow, ← zpow_natCast, ← zpow_neg]
  exact h.mpr hy

/-- The coordinates map `(2^n, t^n) 𝕋` into `(2^n, t^n)`. Kind: PROVED (tex 2747, 2836–2838). -/
theorem tlamBasis_repr_mem [W.IsElliptic] [HasFullTwoTorsion K S W] {n : ℕ}
    {x : TLam K S W α} (hx : x ∈ tlamNbhd K S W α n) (i : Fin 2) :
    tlamBasis.repr x i ∈ lamIdeal n := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ha
  · rw [map_add, Finsupp.add_apply]
    exact Ideal.add_mem _ hx hy

/-- Each coefficient of each coordinate is continuous. Kind: PROVED (tex 2747, 2836–2838). -/
theorem continuous_coeff_tlam_repr [W.IsElliptic] [HasFullTwoTorsion K S W] (i : Fin 2)
    (k : ℕ) : Continuous fun x : TLam K S W α => coeff k (tlamBasis.repr x i) := by
  let f : TLam K S W α →+ ℤ_[2] :=
    (coeff k : Lambda →ₗ[ℤ_[2]] ℤ_[2]).toAddMonoidHom.comp
      ((tlamBasis (K := K) (S := S) (W := W) (α := α)).coord i).toAddMonoidHom
  have hf : Continuous f := by
    refine continuous_of_continuousAt_zero f ?_
    unfold ContinuousAt
    rw [map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    filter_upwards [tlam_hasBasis_nhds_zero.mem_of_mem (i := n + k + 1) trivial] with x hx
    have hmem := coeff_mem_of_mem_lamIdeal (by omega : k < n + k + 1) (tlamBasis_repr_mem hx i)
    rw [dist_zero_right]
    calc ‖f x‖ ≤ ((1 : ℝ) / 2) ^ (n + k + 1) := norm_le_of_mem_span_two_pow hmem
      _ ≤ ((1 : ℝ) / 2) ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ < ε := hn
  exact hf

/-- A map into `Λ` is continuous when all its coefficients are. Kind: PROVED (tex 2747). -/
theorem continuous_lambda_of_coeff {X : Type*} [TopologicalSpace X] (f : X → Lambda)
    (hf : ∀ d, Continuous fun x => coeff d (f x)) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x =>
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto (R := ℤ_[2]) f (𝓝 x) (f x)).mpr fun d =>
      (hf d).tendsto x

/-- **The coordinates `𝕋 → Λ` are continuous** (`(2, t)`-adic to product topology). Kind: PROVED
(tex 2747, 2836–2838). -/
theorem continuous_tlam_repr [W.IsElliptic] [HasFullTwoTorsion K S W] (i : Fin 2) :
    Continuous fun x : TLam K S W α => tlamBasis.repr x i :=
  continuous_lambda_of_coeff _ fun k => continuous_coeff_tlam_repr i k

/-- **`Λ² → 𝕋`, `c ↦ Σ c_i b_i`, is continuous.** Kind: PROVED (tex 2747, 2836–2838). -/
theorem continuous_tlam_basis_sum [W.IsElliptic] [HasFullTwoTorsion K S W] :
    Continuous fun c : Fin 2 → Lambda => ∑ i, c i • (tlamBasis (α := α) i : TLam K S W α) :=
  continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const

/-- **`𝕋 ≃ₜ Λ²` through the basis.** Kind: definition (tex 2747, 2836–2838). -/
def tlamHomeomorph [W.IsElliptic] [HasFullTwoTorsion K S W] :
    TLam K S W α ≃ₜ (Fin 2 → Lambda) where
  toEquiv := (tlamBasis (K := K) (S := S) (W := W) (α := α)).equivFun.toEquiv
  continuous_toFun := continuous_pi fun i => (continuous_tlam_repr i).congr fun _ => rfl
  continuous_invFun := continuous_tlam_basis_sum.congr fun c =>
    ((tlamBasis (K := K) (S := S) (W := W) (α := α)).equivFun_symm_apply c).symm

/-- `tlamHomeomorph` is the coordinate map. Kind: PROVED (tex 2747, 2836–2838). -/
theorem tlamHomeomorph_apply [W.IsElliptic] [HasFullTwoTorsion K S W] (x : TLam K S W α)
    (i : Fin 2) : tlamHomeomorph x i = tlamBasis.repr x i := rfl

/-! ### Non-vacuity -/

/-- `E_1 : y² = x³ + 2x² − 3x` (round 1's `curveEll 1`) is elliptic. Kind: PROVED
(tex 2836–2838). -/
theorem isElliptic_curveEll_one :
    (ZInQ.Manuscript.RC.CoefModules.curveEll (1 : ℚ)).IsElliptic :=
  ZInQ.Manuscript.RC.CoefModules.isElliptic_curveEll one_ne_zero

attribute [local instance] isElliptic_curveEll_one

/-- Non-vacuity: over `ℚ`, all primes, `E_1`, `α = 1`: `rank_Λ 𝕋 = 2`, the coordinates are
continuous. Kind: PROVED (tex 2747, 2836–2838). -/
example : Module.finrank Lambda
      (TLam ℚ Set.univ (ZInQ.Manuscript.RC.CoefModules.curveEll (1 : ℚ)) 1) = 2 ∧
    Continuous fun x : TLam ℚ Set.univ (ZInQ.Manuscript.RC.CoefModules.curveEll (1 : ℚ)) 1 =>
      tlamBasis.repr x 0 := by
  exact ⟨finrank_tlam, continuous_tlam_repr 0⟩

/-- Non-vacuity: at `𝔭 = (t)`, `V_𝔭` is a nonzero `2`-dimensional `k(𝔭)`-vector space. Kind:
PROVED (tex 4976–5200). -/
example : Module.finrank (ResAt (Ideal.span {(X : Lambda)}))
      (VP ℚ Set.univ (ZInQ.Manuscript.RC.CoefModules.curveEll (1 : ℚ))
        (Ideal.span {(X : Lambda)}) 1) = 2 ∧
    Nontrivial (VP ℚ Set.univ (ZInQ.Manuscript.RC.CoefModules.curveEll (1 : ℚ))
        (Ideal.span {(X : Lambda)}) 1) := by
  exact ⟨finrank_vp _, inferInstance⟩

/-- Non-vacuity of `fibreEquiv` (no hypothesis on the curve). Kind: PROVED (tex 4976–5200). -/
example (W : WeierstrassCurve ℚ) :
    ResAt (Ideal.span {(X : Lambda)}) ⊗[Lambda] TLam ℚ Set.univ W 1 ≃ₗ[ResAt (Ideal.span {X})]
      VP ℚ Set.univ W (Ideal.span {(X : Lambda)}) 1 :=
  fibreEquiv

end ZInQ.Manuscript.RC.LambdaCoef
