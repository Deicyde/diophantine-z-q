import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.TateLambda
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.HeightOne

/-!
# Lane RC28 round 2, part 5: the characteristic-zero fibres `V_𝔭 = 𝕋 ⊗_Λ k(𝔭)`

Manuscript `diophantine_zq.tex` (11/5), tex 4976–5200: at a height-one prime `𝔭 ≠ (2)` of `Λ`
the switching argument works over `R = Λ_𝔭` and its residue field `k = Frac(Λ/𝔭)`, of characteristic
zero; the fibres of the Selmer complexes have coefficients `𝕋 ⊗_Λ k(𝔭)`.

* `resChar P α : G_{K,S} → k(𝔭)ˣ` (the reduction of `α`).
* **`VP K S W P α = k(𝔭) ⊗_{ℤ₂} T_2E`** (`= 𝕋 ⊗_Λ k(𝔭)` by cancelling `Λ`, `fibreEquiv`) with the
  twisted action `σ (c ⊗ P) = ᾱ(σ) c ⊗ σP`: a `k(𝔭)`-vector space with a `k(𝔭)`-linear action.
* **The natural (`𝔭`-adic) topology**: the lattice `latt = image of Λ ⊗ T_2E` and the basis of
  neighbourhoods `2^n latt` (`fibNbhd`); since `k(𝔭) = (Λ/𝔭)[1/2]` with `Λ/𝔭` finite over `ℤ₂`
  (`HeightOne.lean`, Weierstrass preparation), this is the topology of a finite-dimensional
  `ℚ₂`-vector space. **Every instance required by lane RC26's `galoisSelData` holds**:
  `IsTopologicalAddGroup` (hence `ContinuousAdd`), `ContinuousConstSMul (ResAt P)`,
  `ContinuousSMul (GKS K S)` (for continuous `α`), with no finiteness and no discreteness.

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
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open scoped PowerSeries.WithPiTopology Pointwise

attribute [local instance] lambda_isTopologicalRing

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} (P : Ideal Lambda) [P.IsPrime]

/-- **A height-one prime `𝔭 ≠ (2)` of `Λ`** (the primes of the switching argument, tex 4976). -/
class IsHeightOneOdd (P : Ideal Lambda) : Prop where
  height_eq : P.height = 1
  ne_two : P ≠ Ideal.span {2}

/-- Non-vacuity: `(t)` is a height-one prime `≠ (2)`. Kind: PROVED. -/
instance isHeightOneOdd_span_X : IsHeightOneOdd (Ideal.span {(X : Lambda)}) :=
  ⟨ZInQ.Manuscript.RC.CoefModules.height_span_X, ZInQ.Manuscript.RC.CoefModules.span_X_ne_span_two⟩

theorem algebraMap_resAt_eq (l : Lambda) :
    algebraMap Lambda (ResAt P) l = resAt P (algebraMap Lambda (Localization.AtPrime P) l) := rfl

theorem algebraMap_resAt_eq_zero {l : Lambda} (hl : l ∈ P) : algebraMap Lambda (ResAt P) l = 0 := by
  rw [algebraMap_resAt_eq, IsLocalRing.residue_eq_zero_iff]
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P l).mpr hl

/-- The reduction `ᾱ : G_{K,S} → k(𝔭)ˣ` of a `Λ`-adic character. -/
def resChar (α : GKS K S →* Lambdaˣ) : GKS K S →* (ResAt P)ˣ :=
  (Units.map (algebraMap Lambda (ResAt P)).toMonoidHom).comp α

theorem coe_resChar (α : GKS K S →* Lambdaˣ) (σ : GKS K S) :
    ((resChar P α σ : (ResAt P)ˣ) : ResAt P) = algebraMap Lambda (ResAt P) (α σ) := rfl

variable (K S W) in
/-- **The fibre `V_𝔭 = k(𝔭) ⊗_{ℤ₂} T_2E`** with the action twisted by `ᾱ` (tex 4976–5200). -/
@[nolint unusedArguments]
def VP (P : Ideal Lambda) [P.IsPrime] (_α : GKS K S →* Lambdaˣ) : Type :=
  ResAt P ⊗[ℤ_[2]] TateS K S W

variable (α : GKS K S →* Lambdaˣ)

instance : AddCommGroup (VP K S W P α) := inferInstanceAs (AddCommGroup (ResAt P ⊗[ℤ_[2]] _))

instance : Module (ResAt P) (VP K S W P α) := inferInstanceAs (Module (ResAt P) (ResAt P ⊗[ℤ_[2]] _))

instance : Module Lambda (VP K S W P α) := inferInstanceAs (Module Lambda (ResAt P ⊗[ℤ_[2]] _))

instance : Module ℤ_[2] (VP K S W P α) := inferInstanceAs (Module ℤ_[2] (ResAt P ⊗[ℤ_[2]] _))

instance : IsScalarTower Lambda (ResAt P) (VP K S W P α) :=
  inferInstanceAs (IsScalarTower Lambda (ResAt P) (ResAt P ⊗[ℤ_[2]] _))

instance : IsScalarTower ℤ_[2] Lambda (VP K S W P α) :=
  inferInstanceAs (IsScalarTower ℤ_[2] Lambda (ResAt P ⊗[ℤ_[2]] _))

instance : IsScalarTower ℤ_[2] (ResAt P) (VP K S W P α) :=
  inferInstanceAs (IsScalarTower ℤ_[2] (ResAt P) (ResAt P ⊗[ℤ_[2]] _))

/-- Induction on `V_𝔭`. -/
theorem VP.induction {motive : VP K S W P α → Prop} (x : VP K S W P α) (zero : motive 0)
    (tmul : ∀ (c : ResAt P) (Q : TateS K S W), motive (show VP K S W P α from c ⊗ₜ Q))
    (add : ∀ x y : VP K S W P α, motive x → motive y → motive (x + y)) : motive x :=
  TensorProduct.induction_on x zero tmul add

variable {α}

/-- The twisted action on `V_𝔭`, `k(𝔭)`-linear. -/
def VP.act (σ : GKS K S) : VP K S W P α →ₗ[ResAt P] VP K S W P α :=
  ((resChar P α σ : (ResAt P)ˣ) : ResAt P) • (actLin K S W σ).baseChange (ResAt P)

theorem VP.act_tmul (σ : GKS K S) (c : ResAt P) (Q : TateS K S W) :
    VP.act P σ (show VP K S W P α from c ⊗ₜ Q) =
      show VP K S W P α from (((resChar P α σ : (ResAt P)ˣ) : ResAt P) * c) ⊗ₜ (σ • Q) := by
  change ((resChar P α σ : (ResAt P)ˣ) : ResAt P) • (c ⊗ₜ[ℤ_[2]] (σ • Q)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul]

theorem VP.act_one (x : VP K S W P α) : VP.act P 1 x = x := by
  induction x using VP.induction with
  | zero => exact map_zero _
  | tmul c Q => rw [VP.act_tmul, map_one, Units.val_one, one_mul, one_smul]
  | add x y hx hy => rw [map_add, hx, hy]

theorem VP.act_mul (σ τ : GKS K S) (x : VP K S W P α) :
    VP.act P (σ * τ) x = VP.act P σ (VP.act P τ x) := by
  induction x using VP.induction with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul c Q =>
    rw [VP.act_tmul, VP.act_tmul, VP.act_tmul, map_mul, Units.val_mul, mul_smul, mul_assoc]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

/-- **The genuine Galois action on the fibre.** -/
instance vp_distribMulAction : DistribMulAction (GKS K S) (VP K S W P α) where
  smul σ x := VP.act P σ x
  one_smul := VP.act_one P
  mul_smul := VP.act_mul P
  smul_zero σ := map_zero _
  smul_add σ := map_add _

theorem VP.smul_def (σ : GKS K S) (x : VP K S W P α) : σ • x = VP.act P σ x := rfl

theorem VP.smul_tmul (σ : GKS K S) (c : ResAt P) (Q : TateS K S W) :
    σ • (show VP K S W P α from c ⊗ₜ Q) =
      show VP K S W P α from (((resChar P α σ : (ResAt P)ˣ) : ResAt P) * c) ⊗ₜ (σ • Q) :=
  VP.act_tmul P σ c Q

/-- The Galois action is `k(𝔭)`-linear. Kind: PROVED. -/
instance vp_smulCommClass : SMulCommClass (GKS K S) (ResAt P) (VP K S W P α) where
  smul_comm σ a x := (VP.act P σ).map_smul a x

theorem VP.smul_lambda_comm (σ : GKS K S) (l : Lambda) (x : VP K S W P α) :
    σ • (l • x) = l • (σ • x) := by
  rw [← algebraMap_smul (ResAt P) l x, smul_comm, algebraMap_smul]

/-! ### The lattice and the natural topology -/

variable (K S W α) in
/-- **The lattice** `latt = Λ · (1 ⊗ T_2E) ⊆ V_𝔭` (the image of `Λ ⊗ T_2E`). -/
def latt : Submodule Lambda (VP K S W P α) :=
  Submodule.span Lambda (Set.range fun Q : TateS K S W => show VP K S W P α from (1 : ResAt P) ⊗ₜ Q)

theorem one_tmul_mem_latt (Q : TateS K S W) :
    (show VP K S W P α from (1 : ResAt P) ⊗ₜ Q) ∈ latt K S W P α :=
  Submodule.subset_span ⟨Q, rfl⟩

theorem algebraMap_tmul_mem_latt (l : Lambda) (Q : TateS K S W) :
    (show VP K S W P α from algebraMap Lambda (ResAt P) l ⊗ₜ Q) ∈ latt K S W P α := by
  have h : (show VP K S W P α from algebraMap Lambda (ResAt P) l ⊗ₜ Q) =
      l • (show VP K S W P α from (1 : ResAt P) ⊗ₜ Q) := by
    change algebraMap Lambda (ResAt P) l ⊗ₜ[ℤ_[2]] Q = l • ((1 : ResAt P) ⊗ₜ[ℤ_[2]] Q)
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
  rw [h]
  exact Submodule.smul_mem _ _ (one_tmul_mem_latt P Q)

variable (K S W α) in
/-- **The basic neighbourhoods `2^n latt`.** -/
def fibNbhd (n : ℕ) : Submodule ℤ_[2] (VP K S W P α) :=
  (((2 : Lambda) ^ n) • latt K S W P α).restrictScalars ℤ_[2]

theorem mem_fibNbhd {n : ℕ} {x : VP K S W P α} :
    x ∈ fibNbhd K S W P α n ↔ ∃ y ∈ latt K S W P α, ((2 : Lambda) ^ n) • y = x := by
  rw [fibNbhd, Submodule.restrictScalars_mem, Submodule.mem_smul_pointwise_iff_exists]

theorem two_pow_smul_mem_fibNbhd {n : ℕ} {y : VP K S W P α} (hy : y ∈ latt K S W P α) :
    ((2 : Lambda) ^ n) • y ∈ fibNbhd K S W P α n :=
  mem_fibNbhd P |>.mpr ⟨y, hy, rfl⟩

theorem fibNbhd_antitone {m n : ℕ} (h : n ≤ m) : fibNbhd K S W P α m ≤ fibNbhd K S W P α n := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_fibNbhd P).mp hx
  rw [← Nat.add_sub_cancel' h, pow_add, mul_smul]
  exact two_pow_smul_mem_fibNbhd P (Submodule.smul_mem _ _ hy)

/-! ### The topology -/

variable (K S W α) in
/-- The basic neighbourhoods as `ℤ`-submodules (to build the group topology). -/
def fibNbhdZ (n : ℕ) : Submodule ℤ (VP K S W P α) := (fibNbhd K S W P α n).restrictScalars ℤ

theorem submodulesBasis_fib : SubmodulesBasis (fibNbhdZ K S W P α) where
  inter i j := ⟨max i j, le_inf (fun x hx => fibNbhd_antitone P (le_max_left i j) hx)
    (fun x hx => fibNbhd_antitone P (le_max_right i j) hx)⟩
  smul m i := by
    rw [nhds_discrete, Filter.eventually_pure, zero_smul]
    exact Submodule.zero_mem _

/-- **The natural topology on `V_𝔭`**: the `2`-adic topology of the lattice `latt`, i.e. the
neighbourhoods of zero are the `2^n latt`. -/
instance vpTop : TopologicalSpace (VP K S W P α) :=
  (submodulesBasis_fib (K := K) (S := S) (W := W) P (α := α)).topology

instance vp_isTopologicalAddGroup : IsTopologicalAddGroup (VP K S W P α) :=
  AddGroupFilterBasis.isTopologicalAddGroup _

/-- The basic neighbourhoods of zero of `V_𝔭`. Kind: PROVED. -/
theorem fib_hasBasis_nhds_zero :
    (𝓝 (0 : VP K S W P α)).HasBasis (fun _ => True) (fun n => (fibNbhd K S W P α n : Set _)) := by
  have h := (submodulesBasis_fib (K := K) (S := S) (W := W) P (α := α)).toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis
  refine ⟨fun t => ?_⟩
  rw [h.mem_iff]
  constructor
  · rintro ⟨V, ⟨i, rfl⟩, hV⟩
    exact ⟨i, trivial, hV⟩
  · rintro ⟨i, -, hi⟩
    exact ⟨_, ⟨i, rfl⟩, hi⟩

theorem lambda_smul_mem_fibNbhd (l : Lambda) {n : ℕ} {x : VP K S W P α}
    (hx : x ∈ fibNbhd K S W P α n) : l • x ∈ fibNbhd K S W P α n := by
  obtain ⟨y, hy, rfl⟩ := (mem_fibNbhd P).mp hx
  rw [smul_comm]
  exact two_pow_smul_mem_fibNbhd P (Submodule.smul_mem _ _ hy)

/-- The lattice is Galois stable. Kind: PROVED. -/
theorem smul_mem_latt (σ : GKS K S) {y : VP K S W P α} (hy : y ∈ latt K S W P α) :
    σ • y ∈ latt K S W P α := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨Q, rfl⟩ := hx
    rw [VP.smul_tmul, mul_one, coe_resChar]
    exact algebraMap_tmul_mem_latt P _ _
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul l x _ hx => rw [VP.smul_lambda_comm]; exact Submodule.smul_mem _ _ hx

theorem smul_mem_fibNbhd (σ : GKS K S) (n : ℕ) {x : VP K S W P α}
    (hx : x ∈ fibNbhd K S W P α n) : σ • x ∈ fibNbhd K S W P α n := by
  obtain ⟨y, hy, rfl⟩ := (mem_fibNbhd P).mp hx
  rw [VP.smul_lambda_comm]
  exact two_pow_smul_mem_fibNbhd P (smul_mem_latt P σ hy)

variable [hPo : IsHeightOneOdd P]

/-- **Every vector of `V_𝔭` is `2^{-J}` times a lattice vector** (`k(𝔭) = (Λ/𝔭)[1/2]`).
Kind: PROVED. -/
theorem exists_two_pow_smul_mem_latt (v : VP K S W P α) :
    ∃ J : ℕ, ((2 : Lambda) ^ J) • v ∈ latt K S W P α := by
  induction v using VP.induction with
  | zero => exact ⟨0, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | tmul c Q =>
    obtain ⟨l, j, hl⟩ := exists_two_pow_mul_eq hPo.height_eq hPo.ne_two c
    refine ⟨j, ?_⟩
    have h : ((2 : Lambda) ^ j) • (show VP K S W P α from c ⊗ₜ Q) =
        show VP K S W P α from algebraMap Lambda (ResAt P) l ⊗ₜ Q := by
      change ((2 : Lambda) ^ j) • (c ⊗ₜ[ℤ_[2]] Q) = algebraMap Lambda (ResAt P) l ⊗ₜ[ℤ_[2]] Q
      rw [TensorProduct.smul_tmul', Algebra.smul_def, map_pow, map_ofNat, algebraMap_resAt_eq, ← hl]
    rw [h]
    exact algebraMap_tmul_mem_latt P l Q
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ ha
    · rw [pow_add, mul_smul]
      exact Submodule.smul_mem _ _ hb

/-- `2` acts invertibly on `V_𝔭`. Kind: PROVED. -/
theorem two_pow_smul_injective (J : ℕ) :
    Function.Injective fun v : VP K S W P α => ((2 : Lambda) ^ J) • v := by
  intro v w h
  have hu : IsUnit ((2 : ResAt P) ^ J) := (isUnit_two_resAt hPo.height_eq hPo.ne_two).pow J
  have h' : ((2 : ResAt P) ^ J) • v = ((2 : ResAt P) ^ J) • w := by
    have e : ∀ u : VP K S W P α, ((2 : Lambda) ^ J) • u = ((2 : ResAt P) ^ J) • u := fun u => by
      rw [← algebraMap_smul (ResAt P) ((2 : Lambda) ^ J) u, map_pow, map_ofNat]
    rw [← e, ← e]
    exact h
  exact (hu.smul_left_cancel).mp h'

/-- **`V_𝔭` is a topological `k(𝔭)`-vector space** (each `c • ·` is continuous). Kind: PROVED. -/
instance vp_continuousConstSMul : ContinuousConstSMul (ResAt P) (VP K S W P α) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨l, j, hl⟩ := exists_two_pow_mul_eq hPo.height_eq hPo.ne_two c
  refine continuous_of_hasBasis (fun n => (fibNbhd K S W P α n).toAddSubgroup)
    (fun n => (fibNbhd K S W P α n).toAddSubgroup) (fib_hasBasis_nhds_zero P)
    (fib_hasBasis_nhds_zero P) (AddMonoidHom.mk' (fun v : VP K S W P α => c • v) (smul_add c))
    (fun n => ⟨n + j, fun x hx => ?_⟩)
  obtain ⟨y, hy, rfl⟩ := (mem_fibNbhd P).mp hx
  change c • (((2 : Lambda) ^ (n + j)) • y) ∈ fibNbhd K S W P α n
  have e : c • (((2 : Lambda) ^ (n + j)) • y) = ((2 : Lambda) ^ n) • (l • y) := by
    rw [pow_add, mul_smul, smul_comm c, smul_comm c, ← algebraMap_smul (ResAt P) l y,
      ← algebraMap_smul (ResAt P) ((2 : Lambda) ^ j) (c • y), smul_smul, map_pow, map_ofNat,
      algebraMap_resAt_eq, ← hl]
  rw [e]
  exact two_pow_smul_mem_fibNbhd P (Submodule.smul_mem _ _ hy)

/-- The ideal `(2^M, t^M)` reduces into `2^m (Λ/𝔭)` for `M` large. Kind: PROVED. -/
theorem exists_lamIdeal_reduce (m : ℕ) :
    ∃ M : ℕ, ∀ a ∈ lamIdeal M, ∃ b : Lambda,
      algebraMap Lambda (ResAt P) a = 2 ^ m * algebraMap Lambda (ResAt P) b := by
  obtain ⟨M₀, hM₀⟩ := exists_X_pow_mem hPo.height_eq hPo.ne_two m
  refine ⟨max m M₀, fun a ha => ?_⟩
  have hle : lamIdeal (max m M₀) ≤ P ⊔ Ideal.span {(2 : Lambda) ^ m} := by
    rw [lamIdeal, Ideal.span_le]
    rintro x (rfl | rfl)
    · rw [← Nat.add_sub_cancel' (le_max_left m M₀), pow_add]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    · rw [← Nat.add_sub_cancel' (le_max_right m M₀), pow_add]
      exact Ideal.mul_mem_right _ _ hM₀
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp (hle ha)
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hq
  refine ⟨b, ?_⟩
  rw [map_add, algebraMap_resAt_eq_zero P hp, zero_add, map_mul, map_pow, map_ofNat, mul_comm]

theorem eventually_one_tmul (α : GKS K S →* Lambdaˣ) [IsContChar α] (Q : TateS K S W) (m : ℕ) :
    ∀ᶠ σ in 𝓝 (1 : GKS K S), σ • (show VP K S W P α from (1 : ResAt P) ⊗ₜ Q) -
      (show VP K S W P α from (1 : ResAt P) ⊗ₜ Q) ∈ fibNbhd K S W P α m := by
  obtain ⟨M, hM⟩ := exists_lamIdeal_reduce P m
  filter_upwards [eventually_sub_one_mem α M, eventually_smul_sub_mem Q m] with σ h1 h2
  obtain ⟨b, hb⟩ := hM _ h1
  obtain ⟨Q', hQ'⟩ := h2
  rw [VP.smul_tmul, mul_one, coe_resChar]
  have e : (show VP K S W P α from algebraMap Lambda (ResAt P) (α σ) ⊗ₜ (σ • Q)) -
      (show VP K S W P α from (1 : ResAt P) ⊗ₜ Q) =
      ((2 : Lambda) ^ m) • (b • (show VP K S W P α from (1 : ResAt P) ⊗ₜ (σ • Q))) +
        ((2 : Lambda) ^ m) • (show VP K S W P α from (1 : ResAt P) ⊗ₜ Q') := by
    have hα : algebraMap Lambda (ResAt P) (α σ) =
        1 + 2 ^ m * algebraMap Lambda (ResAt P) b := by
      rw [← hb, map_sub, map_one, add_sub_cancel]
    change algebraMap Lambda (ResAt P) (α σ) ⊗ₜ[ℤ_[2]] (σ • Q) - (1 : ResAt P) ⊗ₜ[ℤ_[2]] Q =
      ((2 : Lambda) ^ m) • (b • ((1 : ResAt P) ⊗ₜ[ℤ_[2]] (σ • Q))) +
        ((2 : Lambda) ^ m) • ((1 : ResAt P) ⊗ₜ[ℤ_[2]] Q')
    have h2 : ((2 : Lambda) ^ m) • ((1 : ResAt P) ⊗ₜ[ℤ_[2]] Q') =
        (1 : ResAt P) ⊗ₜ[ℤ_[2]] ((2 : ℤ_[2]) ^ m • Q') := by
      rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul Lambda ((2 : ℤ_[2]) ^ m)
        ((1 : ResAt P) ⊗ₜ[ℤ_[2]] Q')]
      congr 1
      rw [map_pow, map_ofNat]
    rw [h2, hQ', hα, TensorProduct.add_tmul, TensorProduct.tmul_sub, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul', Algebra.smul_def, Algebra.smul_def, mul_one, map_pow, map_ofNat]
    abel
  rw [e]
  exact Submodule.add_mem _ (two_pow_smul_mem_fibNbhd P (Submodule.smul_mem _ _
    (one_tmul_mem_latt P _))) (two_pow_smul_mem_fibNbhd P (one_tmul_mem_latt P _))

theorem eventually_latt (α : GKS K S →* Lambdaˣ) [IsContChar α] {y : VP K S W P α}
    (hy : y ∈ latt K S W P α) (m : ℕ) :
    ∀ᶠ σ in 𝓝 (1 : GKS K S), σ • y - y ∈ fibNbhd K S W P α m := by
  induction hy using Submodule.span_induction generalizing m with
  | mem x hx =>
    obtain ⟨Q, rfl⟩ := hx
    exact eventually_one_tmul P α Q m
  | zero => exact Eventually.of_forall fun σ => by rw [smul_zero, sub_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    filter_upwards [hx m, hy m] with σ h1 h2
    rw [smul_add, add_sub_add_comm]
    exact Submodule.add_mem _ h1 h2
  | smul l x _ hx =>
    filter_upwards [hx m] with σ h
    rw [VP.smul_lambda_comm, ← smul_sub]
    exact lambda_smul_mem_fibNbhd P l h

/-- **The Galois action on `V_𝔭` is continuous** for its natural topology. Kind: PROVED. -/
instance vp_continuousSMul [IsContChar α] : ContinuousSMul (GKS K S) (VP K S W P α) := by
  refine continuousSMul_of_hasBasis (fun n => (fibNbhd K S W P α n).toAddSubgroup)
    (fib_hasBasis_nhds_zero P) (fun σ n x hx => smul_mem_fibNbhd P σ n hx) (fun v n => ?_)
  obtain ⟨J, hJ⟩ := exists_two_pow_smul_mem_latt P v
  filter_upwards [eventually_latt P α hJ (n + J)] with σ hσ
  obtain ⟨y, hy, hyeq⟩ := (mem_fibNbhd P).mp hσ
  have e : σ • v - v = ((2 : Lambda) ^ n) • y := by
    apply two_pow_smul_injective P J
    change ((2 : Lambda) ^ J) • (σ • v - v) = ((2 : Lambda) ^ J) • (((2 : Lambda) ^ n) • y)
    rw [smul_sub, ← VP.smul_lambda_comm, ← hyeq, pow_add, mul_comm, mul_smul]
  change σ • v - v ∈ fibNbhd K S W P α n
  rw [e]
  exact two_pow_smul_mem_fibNbhd P hy

end ZInQ.Manuscript.RC.LambdaCoef
