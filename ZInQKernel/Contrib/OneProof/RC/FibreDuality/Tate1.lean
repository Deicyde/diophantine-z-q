import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Print
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Cyclotomic2

/-!
# Lane RC31, part 4: the coefficient twist `k(𝔭)(1)` with its lattice topology

Manuscript `diophantine_zq.tex`: the characteristic-zero fibres of the switching argument
(tex 4976–5200; a height-one prime `𝔭 ≠ (2)` of `Λ = ℤ₂⟦t⟧`, `k = k(𝔭) = Frac(Λ/𝔭)`), whose
pairings take values in the cyclotomic twist of the coefficients (tex 2798–2805: the Weil pairing
takes values in `R(1)`, "and `e_2` transforms by the cyclotomic character").
Source: J. Nekovář, *Selmer complexes*, Astérisque 310 (2006), 5.2.1, p. 114:
`A(1) = A ⊗_{ℤ_p} ℤ_p(1)`.

* `Tate1P K S P`: **`k(𝔭)(1) = k(𝔭) ⊗_{ℤ₂} ℤ₂(1)`**, the one-dimensional `k(𝔭)`-vector space on
  which `σ ∈ G_{K,S}` acts by the `2`-adic cyclotomic character `χ(σ) ∈ ℤ₂ˣ ⊆ k(𝔭)ˣ`.
* `tLatt`: the lattice `Λ · 1` (the image of `Λ`, i.e. of `Λ/𝔭`); the topology of `Tate1P` has the
  neighbourhood basis `2^n · tLatt` (the topology of a finite-dimensional `ℚ₂`-vector space, as
  `Λ/𝔭` is finite over `ℤ₂`).
* `isLatticeTop_tate1P`: Nekovář's topology hypothesis `IsLatticeTop` holds.
* `isTateTwistFibre_tate1P`: under `μ_{2^∞} ⊆ K_S`, the twist hypothesis `IsTateTwistFibre` holds
  with the identity identification and `c = χ`.
* Instances: `IsTopologicalAddGroup`, `ContinuousConstSMul (ResAt P)`, `ContinuousSMul (GKS K S)`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain Filter Topology
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt resAt)
open ZInQ.Manuscript.RC.SelmerComplex (GKS toGal)
open ZInQ.Manuscript.RC.CoefModules (KS galS HasRootsOfUnity card_rootsOfUnity_KS)
open ZInQ.Manuscript.RC.LambdaCoef (IsHeightOneOdd resN exists_two_pow_mul_eq
  continuousSMul_of_hasBasis continuous_of_hasBasis)
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside)
open scoped Pointwise

/-- **The coefficient twist `k(𝔭)(1) = k(𝔭) ⊗_{ℤ₂} ℤ₂(1)`** at a prime `𝔭` of `Λ` (Nekovář,
*Selmer complexes*, 5.2.1, p. 114: `A(1) = A ⊗_{ℤ_p} ℤ_p(1)`; manuscript tex 4976–5200 and
tex 2798–2805): as a `k(𝔭)`-vector space it is `k(𝔭)`; the Galois group `G_{K,S}` acts through the
`2`-adic cyclotomic character (`Tate1P.smul_def`). Kind: definition. -/
@[nolint unusedArguments]
def Tate1P (K : Type) [Field K] [NumberField K] (_S : Set (HeightOneSpectrum (𝓞 K)))
    (P : Ideal Lambda) [P.IsPrime] : Type :=
  ResAt P

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {P : Ideal Lambda} [P.IsPrime]

/-- The additive group of `k(𝔭)(1)` (that of `k(𝔭)`). Kind: definition (instance). -/
instance tate1P_addCommGroup : AddCommGroup (Tate1P K S P) :=
  inferInstanceAs (AddCommGroup (ResAt P))

/-- `k(𝔭)(1)` is a `k(𝔭)`-vector space. Kind: definition (instance). -/
instance tate1P_module : Module (ResAt P) (Tate1P K S P) :=
  inferInstanceAs (Module (ResAt P) (ResAt P))

/-- `k(𝔭)(1)` is a `Λ`-module (through `Λ → k(𝔭)`). Kind: definition (instance). -/
instance tate1P_moduleLambda : Module Lambda (Tate1P K S P) :=
  inferInstanceAs (Module Lambda (ResAt P))

/-- `k(𝔭)(1)` is a `ℤ₂`-module (through `ℤ₂ → k(𝔭)`). Kind: definition (instance). -/
instance tate1P_moduleZ2 : Module ℤ_[2] (Tate1P K S P) := inferInstanceAs (Module ℤ_[2] (ResAt P))

/-- `Λ → k(𝔭)` is compatible with the actions on `k(𝔭)(1)`. Kind: PROVED (instance). -/
instance tate1P_isScalarTower_lambda : IsScalarTower Lambda (ResAt P) (Tate1P K S P) :=
  inferInstanceAs (IsScalarTower Lambda (ResAt P) (ResAt P))

/-- `ℤ₂ → k(𝔭)` is compatible with the actions on `k(𝔭)(1)`. Kind: PROVED (instance). -/
instance tate1P_isScalarTower_z2 : IsScalarTower ℤ_[2] (ResAt P) (Tate1P K S P) :=
  inferInstanceAs (IsScalarTower ℤ_[2] (ResAt P) (ResAt P))

/-- `ℤ₂ → Λ` is compatible with the actions on `k(𝔭)(1)`. Kind: PROVED (instance). -/
instance tate1P_isScalarTower_z2_lambda : IsScalarTower ℤ_[2] Lambda (Tate1P K S P) :=
  inferInstanceAs (IsScalarTower ℤ_[2] Lambda (ResAt P))

variable (K S P) in
/-- **The cyclotomic character with values in `k(𝔭)`**: `σ ↦ χ(σ) ∈ ℤ₂ → k(𝔭)` (manuscript
tex 2798–2805; Nekovář 5.2.1, p. 114). Kind: definition. -/
def chiP (σ : GKS K S) : ResAt P :=
  algebraMap ℤ_[2] (ResAt P) (cyc2 K S σ : ℤ_[2])

omit [NumberField K] in
/-- `χ(1) = 1`. Kind: PROVED. -/
theorem chiP_one : chiP K S P 1 = 1 := by
  rw [chiP, map_one, Units.val_one, map_one]

omit [NumberField K] in
/-- `χ(στ) = χ(σ)χ(τ)`. Kind: PROVED. -/
theorem chiP_mul (σ τ : GKS K S) : chiP K S P (σ * τ) = chiP K S P σ * chiP K S P τ := by
  rw [chiP, chiP, chiP, map_mul, Units.val_mul, map_mul]

/-- **The Galois action on `k(𝔭)(1)`**: `σ • x = χ(σ) x` (Nekovář 5.2.1, p. 114; manuscript
tex 2798–2805). Kind: definition (instance). -/
instance tate1P_distribMulAction : DistribMulAction (GKS K S) (Tate1P K S P) where
  smul σ x := chiP K S P σ • x
  one_smul x := by
    change chiP K S P 1 • x = x
    rw [chiP_one, one_smul]
  mul_smul σ τ x := by
    change chiP K S P (σ * τ) • x = chiP K S P σ • chiP K S P τ • x
    rw [chiP_mul, mul_smul]
  smul_zero σ := smul_zero (chiP K S P σ)
  smul_add σ := smul_add (chiP K S P σ)

/-- **`σ • x = χ(σ) x`** on `k(𝔭)(1)` (Nekovář 5.2.1, p. 114; manuscript tex 2798–2805).
Kind: PROVED. -/
theorem Tate1P.smul_def (σ : GKS K S) (x : Tate1P K S P) :
    σ • x = (show Tate1P K S P from
      algebraMap ℤ_[2] (ResAt P) (cyc2 K S σ : ℤ_[2]) * (show ResAt P from x)) :=
  rfl

/-- **The Galois action is `k(𝔭)`-linear** (manuscript tex 4976–5200). Kind: PROVED (instance). -/
instance tate1P_smulCommClass : SMulCommClass (GKS K S) (ResAt P) (Tate1P K S P) where
  smul_comm σ c x := smul_comm (chiP K S P σ) c x

/-- The Galois action commutes with `Λ` (manuscript tex 4976–5200). Kind: PROVED. -/
theorem Tate1P.smul_lambda_comm (σ : GKS K S) (l : Lambda) (x : Tate1P K S P) :
    σ • (l • x) = l • (σ • x) := by
  rw [← algebraMap_smul (ResAt P) l x, smul_comm, algebraMap_smul]

/-- `Λ` acts on `k(𝔭)(1)` through `Λ → k(𝔭)` (manuscript tex 4976–5200). Kind: PROVED. -/
theorem Tate1P.lambda_smul_def (l : Lambda) (x : Tate1P K S P) :
    l • x = (show Tate1P K S P from
      algebraMap Lambda (ResAt P) l * (show ResAt P from x)) :=
  Algebra.smul_def l (show ResAt P from x)

/-! ### The lattice -/

variable (K S P) in
/-- The vector `1 ∈ k(𝔭)(1)` (`1 ⊗ ζ_{2^∞}`, Nekovář 5.2.1, p. 114; manuscript tex 4976–5200).
Kind: definition. -/
def tOne : Tate1P K S P := (1 : ResAt P)

variable (K S P) in
/-- **The lattice** `Λ · 1 ⊆ k(𝔭)(1)`, the image of `Λ` (equivalently of `Λ/𝔭`) (manuscript
tex 4976–5200; Nekovář 3.3.1, 3.7.3 for the lattice description of the topology).
Kind: definition. -/
def tLatt : Submodule Lambda (Tate1P K S P) :=
  Submodule.span Lambda {tOne K S P}

/-- **Membership in the lattice**: `x ∈ Λ · 1` iff `x` is the residue of an element of `Λ`
(manuscript tex 4976–5200). Kind: PROVED. -/
theorem mem_tLatt_iff (x : Tate1P K S P) :
    x ∈ tLatt K S P ↔ ∃ l : Lambda, (show ResAt P from x) = algebraMap Lambda (ResAt P) l := by
  rw [tLatt, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨l, rfl⟩
    refine ⟨l, ?_⟩
    rw [Tate1P.lambda_smul_def]
    exact mul_one _
  · rintro ⟨l, hl⟩
    refine ⟨l, ?_⟩
    rw [Tate1P.lambda_smul_def]
    exact (mul_one _).trans hl.symm

/-- **The residues of `Λ` lie in the lattice** (manuscript tex 4976–5200). Kind: PROVED. -/
theorem algebraMap_mem_tLatt (l : Lambda) :
    (show Tate1P K S P from algebraMap Lambda (ResAt P) l) ∈ tLatt K S P :=
  (mem_tLatt_iff _).mpr ⟨l, rfl⟩

omit [NumberField K] in
/-- `χ(σ) ∈ k(𝔭)` is the residue of `χ(σ) ∈ ℤ₂ ⊆ Λ` (manuscript tex 2798–2805). Kind: PROVED. -/
theorem chiP_eq_algebraMap (σ : GKS K S) :
    chiP K S P σ = algebraMap Lambda (ResAt P) (algebraMap ℤ_[2] Lambda (cyc2 K S σ : ℤ_[2])) :=
  rfl

/-- **The lattice is Galois stable** (`χ(σ) ∈ ℤ₂ ⊆ Λ`; manuscript tex 4976–5200 and
tex 2798–2805). Kind: PROVED. -/
theorem tate1P_smul_mem_tLatt (σ : GKS K S) {y : Tate1P K S P} (hy : y ∈ tLatt K S P) :
    σ • y ∈ tLatt K S P := by
  change chiP K S P σ • y ∈ tLatt K S P
  rw [chiP_eq_algebraMap, algebraMap_smul]
  exact Submodule.smul_mem _ _ hy

/-! ### The topology -/

variable (K S P) in
/-- The basic neighbourhoods `2^n · tLatt` as `ℤ`-submodules (to build the group topology;
manuscript tex 4976–5200). Kind: definition. -/
def tNbhdZ (n : ℕ) : Submodule ℤ (Tate1P K S P) :=
  (((2 : Lambda) ^ n) • tLatt K S P).restrictScalars ℤ

/-- Membership in `2^n · tLatt` (manuscript tex 4976–5200). Kind: PROVED. -/
theorem mem_two_pow_smul_tLatt {n : ℕ} {x : Tate1P K S P} :
    x ∈ ((2 : Lambda) ^ n) • tLatt K S P ↔ ∃ y ∈ tLatt K S P, ((2 : Lambda) ^ n) • y = x :=
  Submodule.mem_smul_pointwise_iff_exists _ _ _

/-- `2^n y ∈ 2^n · tLatt` for `y` in the lattice (manuscript tex 4976–5200). Kind: PROVED. -/
theorem two_pow_smul_mem {n : ℕ} {y : Tate1P K S P} (hy : y ∈ tLatt K S P) :
    ((2 : Lambda) ^ n) • y ∈ ((2 : Lambda) ^ n) • tLatt K S P :=
  mem_two_pow_smul_tLatt.mpr ⟨y, hy, rfl⟩

/-- The neighbourhoods `2^n · tLatt` decrease (manuscript tex 4976–5200). Kind: PROVED. -/
theorem tNbhdZ_antitone {m n : ℕ} (h : n ≤ m) : tNbhdZ K S P m ≤ tNbhdZ K S P n := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_two_pow_smul_tLatt.mp hx
  change ((2 : Lambda) ^ m) • y ∈ ((2 : Lambda) ^ n) • tLatt K S P
  rw [← Nat.add_sub_cancel' h, pow_add, mul_smul]
  exact two_pow_smul_mem (Submodule.smul_mem _ _ hy)

/-- The neighbourhoods `2^n · tLatt` form a basis of submodules (manuscript tex 4976–5200).
Kind: PROVED. -/
theorem submodulesBasis_tate1P : SubmodulesBasis (tNbhdZ K S P) where
  inter i j := ⟨max i j, le_inf (fun x hx => tNbhdZ_antitone (le_max_left i j) hx)
    (fun x hx => tNbhdZ_antitone (le_max_right i j) hx)⟩
  smul m i := by
    rw [nhds_discrete, Filter.eventually_pure, zero_smul]
    exact Submodule.zero_mem _

/-- **The natural topology on `k(𝔭)(1)`**: the `2`-adic topology of the lattice `Λ · 1`; the
neighbourhoods of zero are the `2^n · tLatt` (Nekovář 3.3.1, 3.7.2–3.7.3; manuscript
tex 4976–5200). Kind: definition (instance). -/
instance tate1PTop : TopologicalSpace (Tate1P K S P) :=
  (submodulesBasis_tate1P (K := K) (S := S) (P := P)).topology

/-- `k(𝔭)(1)` is a topological additive group (manuscript tex 4976–5200). Kind: PROVED
(instance). -/
instance tate1P_isTopologicalAddGroup : IsTopologicalAddGroup (Tate1P K S P) :=
  AddGroupFilterBasis.isTopologicalAddGroup _

/-- **The basic neighbourhoods of zero of `k(𝔭)(1)` are the `2^n · tLatt`** (the shape required
by `IsLatticeTop`; manuscript tex 4976–5200). Kind: PROVED. -/
theorem tate1P_hasBasis_nhds_zero :
    (𝓝 (0 : Tate1P K S P)).HasBasis (fun _ : ℕ => True)
      (fun n => ((((2 : Lambda) ^ n) • tLatt K S P : Submodule Lambda _) : Set _)) := by
  have h := (submodulesBasis_tate1P (K := K) (S := S)
    (P := P)).toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis
  refine ⟨fun t => ?_⟩
  rw [h.mem_iff]
  constructor
  · rintro ⟨V, ⟨i, rfl⟩, hV⟩
    exact ⟨i, trivial, hV⟩
  · rintro ⟨i, -, hi⟩
    exact ⟨_, ⟨i, rfl⟩, hi⟩

/-- The basis of neighbourhoods by additive subgroups (manuscript tex 4976–5200). Kind: PROVED. -/
theorem tate1P_hasBasis_nhds_zero' :
    (𝓝 (0 : Tate1P K S P)).HasBasis (fun _ : ℕ => True)
      (fun n => ((tNbhdZ K S P n).toAddSubgroup : Set (Tate1P K S P))) :=
  tate1P_hasBasis_nhds_zero

/-- The Galois action preserves each `2^n · tLatt` (manuscript tex 4976–5200). Kind: PROVED. -/
theorem smul_mem_two_pow_smul_tLatt (σ : GKS K S) (n : ℕ) {x : Tate1P K S P}
    (hx : x ∈ ((2 : Lambda) ^ n) • tLatt K S P) : σ • x ∈ ((2 : Lambda) ^ n) • tLatt K S P := by
  obtain ⟨y, hy, rfl⟩ := mem_two_pow_smul_tLatt.mp hx
  rw [Tate1P.smul_lambda_comm]
  exact two_pow_smul_mem (tate1P_smul_mem_tLatt σ hy)

variable [hPo : IsHeightOneOdd P]

/-- **Every vector of `k(𝔭)(1)` is `2^{-J}` times a lattice vector** (`k(𝔭) = (Λ/𝔭)[1/2]`;
manuscript tex 4976–5200). Kind: PROVED. -/
theorem exists_two_pow_smul_mem_tLatt (x : Tate1P K S P) :
    ∃ J : ℕ, ((2 : Lambda) ^ J) • x ∈ tLatt K S P := by
  obtain ⟨l, j, hl⟩ := exists_two_pow_mul_eq hPo.height_eq hPo.ne_two (show ResAt P from x)
  refine ⟨j, (mem_tLatt_iff _).mpr ⟨l, ?_⟩⟩
  rw [Tate1P.lambda_smul_def]
  change algebraMap Lambda (ResAt P) ((2 : Lambda) ^ j) * (show ResAt P from x) = _
  rw [map_pow, map_ofNat]
  exact hl

/-- **`k(𝔭)(1)` is a topological `k(𝔭)`-vector space** (each `c • ·` is continuous: write
`c = l / 2^j`; manuscript tex 4976–5200). Kind: PROVED (instance). -/
instance tate1P_continuousConstSMul : ContinuousConstSMul (ResAt P) (Tate1P K S P) := by
  refine ⟨fun c => ?_⟩
  obtain ⟨l, j, hl⟩ := exists_two_pow_mul_eq hPo.height_eq hPo.ne_two c
  refine continuous_of_hasBasis (fun n => (tNbhdZ K S P n).toAddSubgroup)
    (fun n => (tNbhdZ K S P n).toAddSubgroup) tate1P_hasBasis_nhds_zero'
    tate1P_hasBasis_nhds_zero'
    (AddMonoidHom.mk' (fun v : Tate1P K S P => c • v) (smul_add c))
    (fun n => ⟨n + j, fun x hx => ?_⟩)
  obtain ⟨y, hy, rfl⟩ := mem_two_pow_smul_tLatt.mp hx
  change c • (((2 : Lambda) ^ (n + j)) • y) ∈ ((2 : Lambda) ^ n) • tLatt K S P
  have e : c • (((2 : Lambda) ^ (n + j)) • y) = ((2 : Lambda) ^ n) • (l • y) := by
    rw [pow_add, mul_smul, smul_comm c, smul_comm c, ← algebraMap_smul (ResAt P) l y,
      ← algebraMap_smul (ResAt P) ((2 : Lambda) ^ j) (c • y), smul_smul, map_pow, map_ofNat,
      ZInQ.Manuscript.RC.LambdaCoef.algebraMap_resAt_eq, ← hl]
  rw [e]
  exact two_pow_smul_mem (Submodule.smul_mem _ _ hy)

/-- `σ x − x ∈ 2^n · tLatt` for `σ` near `1` (`χ(σ) ≡ 1 mod 2^{n+J}`; manuscript tex 4976–5200
and tex 2798–2805). Kind: PROVED. -/
theorem eventually_smul_sub_mem (x : Tate1P K S P) (n : ℕ) :
    ∀ᶠ σ in 𝓝 (1 : GKS K S), σ • x - x ∈ ((2 : Lambda) ^ n) • tLatt K S P := by
  obtain ⟨J, hJ⟩ := exists_two_pow_smul_mem_tLatt x
  filter_upwards [eventually_cyc2_sub_one_mem (K := K) (S := S) (n + J)] with σ hσ
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hσ
  have e : σ • x - x = ((2 : Lambda) ^ n) •
      ((algebraMap ℤ_[2] Lambda b) • (((2 : Lambda) ^ J) • x)) := by
    have h1 : σ • x - x = (chiP K S P σ - 1) • x := by
      rw [sub_smul, one_smul]
      rfl
    have h2 : chiP K S P σ - 1 = algebraMap Lambda (ResAt P)
        ((2 : Lambda) ^ n * (algebraMap ℤ_[2] Lambda b * (2 : Lambda) ^ J)) := by
      have h3 : chiP K S P σ - 1 = algebraMap Lambda (ResAt P)
          (algebraMap ℤ_[2] Lambda ((cyc2 K S σ : ℤ_[2]) - 1)) := by
        rw [map_sub, map_sub, map_one, map_one]
        rfl
      rw [h3, ← hb, map_mul, map_pow, map_ofNat, pow_add]
      congr 1
      ring
    rw [h1, h2, algebraMap_smul, mul_smul, mul_smul]
  rw [e]
  exact two_pow_smul_mem (Submodule.smul_mem _ _ hJ)

/-- **The Galois action on `k(𝔭)(1)` is continuous** for its lattice topology (`χ` is continuous;
manuscript tex 4976–5200 and tex 2798–2805). Kind: PROVED (instance). -/
instance tate1P_continuousSMul : ContinuousSMul (GKS K S) (Tate1P K S P) :=
  continuousSMul_of_hasBasis (fun n => (tNbhdZ K S P n).toAddSubgroup) tate1P_hasBasis_nhds_zero'
    (fun σ n _ hx => smul_mem_two_pow_smul_tLatt σ n hx) (fun v n => eventually_smul_sub_mem v n)

variable (K S P) in
/-- **`k(𝔭)(1)` carries Nekovář's topology** (`IsLatticeTop`, with the lattice `Λ · 1`: finitely
generated, Galois stable, `2^J x ∈ Λ · 1` for every `x`, neighbourhood basis `2^n · Λ · 1`;
Nekovář 3.3.1, 3.3.4, 3.7.2–3.7.3; manuscript tex 4976–5200). Kind: PROVED. -/
theorem isLatticeTop_tate1P : IsLatticeTop (GKS K S) (Tate1P K S P) :=
  ⟨⟨tLatt K S P, Submodule.fg_span_singleton _, fun g _ hy => tate1P_smul_mem_tLatt g hy,
    exists_two_pow_smul_mem_tLatt, tate1P_hasBasis_nhds_zero⟩⟩

omit hPo

variable (K S P) in
/-- The identification `k(𝔭)(1) ≃ k(𝔭)` of `k(𝔭)`-vector spaces (the identity; Nekovář 5.2.1,
p. 114; manuscript tex 4976–5200). Kind: definition. -/
def Tate1P.equiv : Tate1P K S P ≃ₗ[ResAt P] ResAt P :=
  LinearEquiv.refl (ResAt P) (ResAt P)

/-- **`K_S` contains exactly `2^n` roots of unity of order dividing `2^n`** (a primitive one
exists, and `K_S` is a field; manuscript tex 2798–2805). Kind: PROVED. -/
theorem card_two_pow_roots [h : HasTwoPowerRoots K S] (n : ℕ) :
    Nat.card {ζ : unramifiedOutside K S // ζ ^ (2 ^ n) = 1} = 2 ^ n := by
  have hμ : HasRootsOfUnity K S (2 ^ n) := h.roots n
  have e : {x : KS K S // x ^ (2 ^ n) = 1} ≃ rootsOfUnity (2 ^ n) (KS K S) :=
    { toFun := fun x => ⟨Units.mk0 x.1 (by
          rintro h0
          have := x.2
          rw [h0, zero_pow (NeZero.ne (2 ^ n))] at this
          exact zero_ne_one this), by
          rw [mem_rootsOfUnity]
          exact Units.ext (by simpa using x.2)⟩
      invFun := fun u => ⟨((u : (KS K S)ˣ) : KS K S), by
          have := (mem_rootsOfUnity _ _).mp u.2
          rw [← Units.val_pow_eq_pow_val, this, Units.val_one]⟩
      left_inv := fun x => rfl
      right_inv := fun u => by ext; rfl }
  rw [Nat.card_congr e, card_rootsOfUnity_KS hμ]

variable (K S P) in
/-- **`k(𝔭)(1)` is the Tate twist of `k(𝔭)`** (`IsTateTwistFibre`, with the identity
identification and `c = χ`, the `2`-adic cyclotomic character; Nekovář 5.2.1, p. 114:
`A(1) = A ⊗_{ℤ_p} ℤ_p(1)`; manuscript tex 2798–2805 and tex 4976–5200), when `μ_{2^∞} ⊆ K_S`.
Kind: PROVED. -/
theorem isTateTwistFibre_tate1P [HasTwoPowerRoots K S] :
    IsTateTwistFibre K S P (Tate1P K S P) :=
  ⟨Tate1P.equiv K S P, fun σ => (cyc2 K S σ : ℤ_[2]), card_two_pow_roots,
    fun g n ζ hζ => cyc2_spec g n ζ hζ, fun _ _ => rfl⟩

end ZInQ.Manuscript.RC.FibreDuality
