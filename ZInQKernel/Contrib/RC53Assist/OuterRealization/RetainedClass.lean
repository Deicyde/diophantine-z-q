import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineOuterTies
import ZInQKernel.Contrib.CloudB3RC53.UniformSwitch.PrimitiveKernel

/-!
# The outer switching models on the actual retained classes

Proposition `ex:limits-uniform-lower-bound`, proof, tex L4927–4964 (the outer switching), with the
class-functional coordinate of `ex:arith-coordinate` (tex L3877–3892) and the integral paired
functional of `ex:arith-paired-functional` with exponent `a = 0` (tex L3864–3869).

**The departure.** `SwitchInputs.InstanceModel` (`GenuineOuter.lean`) asks that its class `zR` be
primitive (`hprim : ∃ i, ¬ ϖ ∣ zR i`), so its class must be primitive, whereas the text's actual
retained class may be divisible. The text keeps the two apart (tex L4939–4950): "In each generic
one-dimensional kernel choose a primitive vector `v_j`. Its outer image is nonzero, so the outer
kernel dimension `s` is at least one. [...] The actual inner class is a nonzero scalar multiple of
`v_j`. Even if this scalar tends to zero, its generic localization is nonzero on an outer-large set.
Exact switch preservation therefore keeps each inner determinant valuation." The actual class may be
divisible by `ϖ`; the coordinate is that of the actual class and the actual functional (tex
L3882–3892).

**The realization.** `RetainedInstanceModel R K n` holds the data of one instance in the roles of
the text's actual data (the structure does not tie them to the instance; in the (3.5) leaf the
family is existential): the integral two-term model `M`, the actual retained class `z` (an integral
cycle, required only to be NONZERO, tex L4928–4934), the actual paired functional `lam` (integral
and closed) and an admissible complement. Its coordinate `coord` is computed from `z` and `lam`. A
primitive kernel vector of its two-term stage (`UniformSwitch.PrimitiveKernelVector` for the residue
map of `R`: `M v = 0`, `v̄ ≠ 0`, `ι z = c · ι v` with `c ≠ 0`, tex L4987–4992) gives the integral
scalar `c₀` (`pkScalar`, `ι c₀ = c`), and `ofPrimitiveVector` is the `InstanceModel` with class
`zR = v` and functional `lamR = c₀ • lam`: the scalar is moved into the functional. PROVED:

* `ofPrimitiveVector_class_functional`: `c₀ ≠ 0`, `ι z = ι c₀ · ι zR` (the actual class is the
  nonzero scalar multiple of the model class, tex L4948) and `lamR = c₀ • lam`;
* `ofPrimitiveVector_vecMulVec`: the class-functional tensor is unchanged, `zR ⊗ lamR = z ⊗ lam`,
  hence `ofPrimitiveVector_isClassFunctionalCoord` (the same central coordinate);
* `ofPrimitiveVector_coordOf`: the computed coordinate of the model is the actual coordinate;
* `exists_primitiveVector`: for `R → K` injective the primitive kernel vector EXISTS (the RC53
  group's `exists_primitiveKernelVector`, the saturation of `ker d`, tex L4987–4990), so
  `toInstanceModel` asks nothing beyond the retained data; `toInstanceModel_class_eq`: then
  `z = c₀ • zR` in `R`; `localization_ne_zero`: a localization nonzero on `v̄` is generically
  nonzero on the actual class (tex L4949–4950);
* `ofInstanceModel`: every old instance model is a retained one with the same coordinate (a
  primitive class is nonzero), so the retained form asks no more than the old one.

**The outer models.** `RetainedOuterModels R K Inst P` is a family of retained models (every
instance `i`, every configuration `l` of derivative-prime labels), and `toGenuine` is the family
of `SwitchInputs.GenuineOuterModels` it determines; its models have the actual matrices
(`toGenuine_M`) and the actual coordinates (`toGenuine_coordOf`), and its stages the outer kernel
dimension of the actual matrices (`toGenuine_stage_outerDim`) and the actual inner coordinates
(`toGenuine_stage_coord`; for a single sequence `realizedStage_outerDim`, `realizedStage_coord`);
the outer kernel vector of a realized stage is the nonzero outer image of the primitive vectors
(`toGenuine_stage_zout`), so the outer kernel dimension of the actual matrices is at least one
(`one_le_outerKerDim`, tex L4940–4941). The switch input is stated on the actual data alone:
`RetainedSwitchStep` (definition; ELLIOT switch input with GLUE comparisons, tex L4940–4950) and
`RetainedOuterSwitchData`;
`retainedOuterSwitchData_iff` identifies them with `SwitchInputs.GenuineOuterSwitchData` of
`toGenuine`. PROVED: `uniform_lower_bound_of_retained` ((5.5) for the actual coordinates),
`retainedOuterPart_iff` (the outer conjunct of the (3.5) leaves, on retained families, is equivalent
to the one on genuine families) and its instance `eq35OuterPart_iff` over lane RC20's `𝒪`, whose
right side with `cap = eq51Cap ℓ A` is verbatim the outer conjunct at `A` of
`Eq35InputsGenuineABounded` (`GenuineEq35Pad.lean`) and of `Eq35InputsGenuineABoundedH`;
`eq55_of_retained` ((5.5) at the companion pairs from the retained conjunct);
`RetainedInstanceModel.h1_nontrivial` (a genuine retained model forces nonzero genuine `H¹`, from
the nonzero actual class) and `RetainedInstanceModel.zeroSelData_not_model`.

**Scope of the data.** The structures record supplied matrices, classes, functionals and
complements. Their identification with the actual arithmetic instance and its retained class and
paired functional is OPEN (ELLIOT + GLUE). References below to actual data are conditional on
that identification. `IsGenuineTwoTermModel` concerns the matrix alone and supplies no class or
functional identification. Examples with `Gen := True` establish structural satisfiability only.

**What remains.** The retained family itself (the actual minimal models, the actual classes with
`z ≠ 0` at every configuration, the actual paired functionals and complements: ELLIOT + GLUE, tex
L4927–4953, L3864–3869), the genuineness of the matrices, the coordinate clause, and the switch
input `RetainedOuterSwitchData` (ELLIOT switch input with GLUE comparisons, tex L4940–4950).
Primitivity of the actual class is not among them.

Non-vacuity: `exRetained` over `ℤ₂ ⊂ ℚ₂`, the model `[ℤ₂ --0--> ℤ₂]` with the DIVISIBLE actual
class `2` (`exRetained_not_primitive`) and functional `1`; its realization `exRealized` has class
`1`, functional `2` and coordinate `2`, the actual one; the constant family `exRetainedModels`, its
switching data, its uniform bound and its outer conjunct (`exRetainedOuterPart`). The sequence
`exScaled` (actual classes `2^j`, the scalar tending to zero) shows why the outer kernel vector must
be the outer image of the primitive vectors: the outer image of the actual classes is `0`
(`exScaled_outerVec_eq_zero`), that of the realized classes is not
(`exScaled_realized_zout_ne_zero`).
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.OuterRealization

open Matrix Module Filter
open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Central ZInQ.Manuscript.RC.Limits
open ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.SwitchInputs (InstanceModel GenuineOuterModels configStage
  OuterSwitchStep IsPiAdicOn SelmerNonquadStep)
open ZInQ.Contrib.CloudB3RC53.UniformSwitch (TwoTermStage SwitchCoordData)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (selCx)

/-! ### The retained data of one instance -/

section Retained

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]

variable (R K) in
/-- **The retained data of one instance** (in the roles of the text's actual data; not tied to the
instance) (tex L4927–4940, L4957–4961, L3864–3869): an integral two-term model
`[R^{n+1} --M--> R^{n+1}]` over `R`, the actual retained class `z` (an integral cycle, required only
to be nonzero: tex L4928–4934, "the retained central class nonzero [...] the actual lifted cycle
would vanish, contradicting its central value"), the actual paired functional `lam` (integral and
closed, exponent `a = 0`) and an admissible complement `(w, y)` (tex L3882–3892). No primitivity is
asked of `z` (tex L4948: "The actual inner class is a nonzero scalar multiple of `v_j`"). Kind:
definition. -/
structure RetainedInstanceModel (n : ℕ) where
  /-- The integral model (tex L4937–4938). -/
  M : Matrix (Fin (n + 1)) (Fin (n + 1)) R
  /-- The actual retained class (tex L4928–4934, L4948). -/
  z : Fin (n + 1) → R
  /-- The actual paired functional (tex L3864–3869). -/
  lam : Fin (n + 1) → R
  hz : M *ᵥ z = 0
  hlam : lam ᵥ* M = 0
  /-- The complement (tex L3882–3892). -/
  w : Fin n → Fin (n + 1) → K
  y : Fin (n + 1) → K
  hden : detCols (colsDWY (M.map (algebraMap R K)) w y) ≠ 0
  /-- The actual class is nonzero, not necessarily primitive (tex L4928–4934, L4948); it follows
  from a nonzero actual coordinate (`class_ne_zero_of_coord_ne_zero`). -/
  hz0 : z ≠ 0

/-- **A nonzero coordinate forces a nonzero class** (tex L4931–4934: "If the generic kernel of the
resulting two-term free complex vanished, the actual lifted cycle would vanish, contradicting its
central value"): if the class-functional coordinate of an integral cycle `z` (for any functional
and complement) is nonzero, then `z ≠ 0`. So the field `hz0` of `RetainedInstanceModel` follows from
a nonzero actual coordinate. Kind: PROVED. -/
theorem class_ne_zero_of_coord_ne_zero {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (z lam : Fin (n + 1) → R) (w : Fin n → Fin (n + 1) → K) (y : Fin (n + 1) → K)
    (h : classFunctionalCoordWith (M.map (algebraMap R K)) (fun i => algebraMap R K (z i))
      (fun i => algebraMap R K (lam i)) w y ≠ 0) : z ≠ 0 := by
  rintro rfl
  apply h
  have h0 : (fun i => algebraMap R K ((0 : Fin (n + 1) → R) i)) = 0 := by
    funext i
    simp
  rw [classFunctionalCoordWith, h0, detCols_colsZW_zero, zero_mul, zero_div]

namespace RetainedInstanceModel

variable {n : ℕ}

/-- **The actual coordinate** (tex L3877–3892, `ex:arith-coordinate`): the class-functional
coordinate of the actual class and the actual paired functional, computed through the complement
(RC16's `classFunctionalCoordWith`). Kind: definition. -/
def coord (X : RetainedInstanceModel R K n) : K :=
  classFunctionalCoordWith (X.M.map (algebraMap R K)) (fun i => algebraMap R K (X.z i))
    (fun i => algebraMap R K (X.lam i)) X.w X.y

/-- The actual class is a generic cycle (tex L4937–4940). Kind: PROVED. -/
theorem map_mulVec (X : RetainedInstanceModel R K n) :
    X.M.map (algebraMap R K) *ᵥ (fun i => algebraMap R K (X.z i)) = 0 := by
  ext a
  have h := congrFun X.hz a
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at h ⊢
  rw [← map_zero (algebraMap R K), ← h, map_sum]
  exact Finset.sum_congr rfl fun b _ => (map_mul _ _ _).symm

/-- The actual functional is generically closed (tex L3864–3869). Kind: PROVED. -/
theorem map_vecMul (X : RetainedInstanceModel R K n) :
    (fun i => algebraMap R K (X.lam i)) ᵥ* X.M.map (algebraMap R K) = 0 := by
  ext a
  have h := congrFun X.hlam a
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.zero_apply] at h ⊢
  rw [← map_zero (algebraMap R K), ← h, map_sum]
  exact Finset.sum_congr rfl fun b _ => (map_mul _ _ _).symm

/-- **The actual coordinate in the central normalization** (tex L3877–3892): over `K`,
`z ⊗ λ = ((-1)^n u) · adj M` (from RC16's identity `den_mul_eq`). Kind: PROVED. -/
theorem isClassFunctionalCoord (X : RetainedInstanceModel R K n) :
    IsClassFunctionalCoord (X.M.map (algebraMap R K)) (fun i => algebraMap R K (X.z i))
      (fun i => algebraMap R K (X.lam i)) ((-1) ^ n * X.coord) := by
  have hd := X.hden
  have hnum : detCols (colsZW (fun i => algebraMap R K (X.z i)) X.w) *
      ((fun i => algebraMap R K (X.lam i)) ⬝ᵥ X.y) =
      X.coord * detCols (colsDWY (X.M.map (algebraMap R K)) X.w X.y) := by
    rw [coord, classFunctionalCoordWith, div_mul_cancel₀ _ hd]
  unfold IsClassFunctionalCoord
  ext c d
  have e := den_mul_eq (X.M.map (algebraMap R K)) (fun i => algebraMap R K (X.z i))
    (fun i => algebraMap R K (X.lam i)) X.map_mulVec X.map_vecMul X.w X.y c d
  rw [vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
  apply mul_left_cancel₀ hd
  linear_combination e + (-1) ^ n * (X.M.map (algebraMap R K)).adjugate c d * hnum

/-- **The two-term stage of the instance** (UniformSwitch's `TwoTermStage` over
`ι = algebraMap R K`, tex L4983–4992): the model `M`, the actual class, the actual functional and
the actual coordinate in the central normalization. Kind: definition. -/
def stage (X : RetainedInstanceModel R K n) : TwoTermStage (algebraMap R K) where
  n := n
  D := X.M
  z := X.z
  w := X.lam
  u := (-1) ^ n * X.coord
  hz := X.hz
  hw := X.hlam
  hu := X.isClassFunctionalCoord

/-- **The old instance models are retained models** (tex L4936–4940): an `InstanceModel`
(primitive, hence nonzero, class) with its class and functional as the actual ones.
Kind: definition. -/
def ofInstanceModel {ϖ : R} (X : InstanceModel ϖ K n) : RetainedInstanceModel R K n where
  M := X.M
  z := X.zR
  lam := X.lamR
  hz := X.hz
  hlam := X.hlam
  w := X.w
  y := X.y
  hden := X.hden
  hz0 h := by
    obtain ⟨i, hi⟩ := X.hprim
    exact hi (by rw [h]; exact dvd_zero ϖ)

/-- The coordinate of an old instance model is unchanged (tex L3882–3892). Kind: PROVED. -/
theorem ofInstanceModel_coord {ϖ : R} (X : InstanceModel ϖ K n) :
    (ofInstanceModel X).coord = X.coordOf :=
  rfl

section Primitive

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **The primitive kernel vectors of an instance** (tex L4939–4940, L4987–4992): UniformSwitch's
`PrimitiveKernelVector` of the instance's two-term stage for the residue map of `R`: `v ∈ ker M`
with `v̄ ≠ 0`, and `ι z = c · ι v` with `c ≠ 0`. Kind: definition. -/
abbrev PrimitiveVector (X : RetainedInstanceModel R K n) : Type :=
  UniformSwitch.PrimitiveKernelVector X.stage (IsLocalRing.residue R)

/-- The primitive kernel vector as a vector of the instance's size (tex L4939–4940).
Kind: definition. -/
def pvec {X : RetainedInstanceModel R K n} (P : X.PrimitiveVector) : Fin (n + 1) → R := P.v

/-- The primitive kernel vector is a cycle (tex L4987–4988). Kind: PROVED. -/
theorem pvec_mulVec {X : RetainedInstanceModel R K n} (P : X.PrimitiveVector) :
    X.M *ᵥ pvec P = 0 := P.hv

/-- A coordinate of the primitive kernel vector with nonzero residue (tex L4990: `v̄ ≠ 0`).
Kind: definition. -/
def pkIndex {X : RetainedInstanceModel R K n} (P : X.PrimitiveVector) : Fin (n + 1) :=
  P.hprim.choose

/-- That coordinate is a unit of the local ring `R` (tex L4990). Kind: PROVED. -/
theorem isUnit_pkIndex {X : RetainedInstanceModel R K n} (P : X.PrimitiveVector) :
    IsUnit (pvec P (pkIndex P)) :=
  (IsLocalRing.residue_ne_zero_iff_isUnit _).mp P.hprim.choose_spec

/-- **The integral scalar** `c₀ = z_{i₀} · v_{i₀}⁻¹ ∈ R` (tex L4948, L4992: the actual class is a
nonzero scalar multiple of the primitive vector), `i₀ = pkIndex P`. Kind: definition. -/
def pkScalar {X : RetainedInstanceModel R K n} (P : X.PrimitiveVector) : R :=
  X.z (pkIndex P) * ↑(isUnit_pkIndex P).unit⁻¹

/-- The relation `ι z = c · ι v` of the primitive kernel vector (tex L4992). Kind: PROVED. -/
theorem class_eq_c {X : RetainedInstanceModel R K n} (P : X.PrimitiveVector)
    (i : Fin (n + 1)) :
    algebraMap R K (X.z i) = P.c * algebraMap R K (pvec P i) :=
  P.hzv i

/-- The scalar of the primitive kernel vector is integral: `ι c₀ = c` (tex L4948, L4992).
Kind: PROVED. -/
theorem algebraMap_pkScalar {X : RetainedInstanceModel R K n} (P : X.PrimitiveVector) :
    algebraMap R K (pkScalar P) = P.c := by
  rw [pkScalar, map_mul, class_eq_c P, mul_assoc, ← map_mul, (isUnit_pkIndex P).mul_val_inv,
    map_one, mul_one]

/-- The scalar is nonzero (tex L4948: "a nonzero scalar multiple"). Kind: PROVED. -/
theorem pkScalar_ne_zero {X : RetainedInstanceModel R K n} (P : X.PrimitiveVector) :
    pkScalar P ≠ 0 := fun h0 =>
  P.hc (by rw [← algebraMap_pkScalar P, h0, map_zero])

/-- The actual class is the scalar multiple `ι z = ι c₀ · ι v` (tex L4948). Kind: PROVED. -/
theorem class_eq_pkScalar {X : RetainedInstanceModel R K n} (P : X.PrimitiveVector)
    (i : Fin (n + 1)) :
    algebraMap R K (X.z i) = algebraMap R K (pkScalar P) * algebraMap R K (pvec P i) := by
  rw [algebraMap_pkScalar]
  exact class_eq_c P i

/-- **Switches selected by `v̄` see the actual class generically** (tex L4949–4950: "Even if this
scalar tends to zero, its generic localization is nonzero"; tex L4993–4995): for `R → K`
injective, an `R`-linear localization `L` that is nonzero on the reduction of the primitive vector
is, over `K`, nonzero on the actual class (the RC53 group's
`localization_ne_zero_of_primitiveKernel`). Kind: PROVED. -/
theorem localization_ne_zero (hinj : Function.Injective (algebraMap R K))
    {X : RetainedInstanceModel R K n} (P : X.PrimitiveVector) {m : Type*} [Fintype m]
    (L : Matrix m (Fin (n + 1)) R)
    (hL : L.map (IsLocalRing.residue R) *ᵥ (fun i => IsLocalRing.residue R (pvec P i)) ≠ 0) :
    L.map (algebraMap R K) *ᵥ (fun i => algebraMap R K (X.z i)) ≠ 0 :=
  UniformSwitch.localization_ne_zero_of_primitiveKernel hinj P L hL

variable (ϖ : R) [Fact (Irreducible ϖ)]

/-- **The outer instance model on the actual retained class** (tex L4936–4950): from a primitive
kernel vector `v` of the instance, the `InstanceModel` with the actual model `M`, class `zR = v`
(primitive: `v_{i₀}` is a unit), functional `lamR = c₀ • lam` (the scalar `c₀` of `z = c₀ v` moved
into the actual paired functional; integral and closed) and the actual complement. Kind:
definition. -/
def ofPrimitiveVector (X : RetainedInstanceModel R K n) (P : X.PrimitiveVector) :
    InstanceModel ϖ K n where
  M := X.M
  zR := pvec P
  lamR := pkScalar P • X.lam
  hz := pvec_mulVec P
  hlam := by rw [smul_vecMul, X.hlam, smul_zero]
  w := X.w
  y := X.y
  hden := X.hden
  hprim := ⟨pkIndex P, fun h =>
    (Fact.out : Irreducible ϖ).not_isUnit (isUnit_of_dvd_unit h (isUnit_pkIndex P))⟩

/-- The model of the realization is the actual model (tex L4937–4938). Kind: PROVED. -/
theorem ofPrimitiveVector_M (X : RetainedInstanceModel R K n) (P : X.PrimitiveVector) :
    (X.ofPrimitiveVector ϖ P).M = X.M := rfl

/-- **The class of the realization is the actual retained class, up to the scalar moved into
the functional** (tex L4948, L4992): `c₀ ≠ 0`, `ι z = ι c₀ · ι zR` and `lamR = c₀ • lam`.
Kind: PROVED. -/
theorem ofPrimitiveVector_class_functional (X : RetainedInstanceModel R K n)
    (P : X.PrimitiveVector) :
    pkScalar P ≠ 0 ∧
      (∀ i, algebraMap R K (X.z i) =
        algebraMap R K (pkScalar P) * algebraMap R K ((X.ofPrimitiveVector ϖ P).zR i)) ∧
      (X.ofPrimitiveVector ϖ P).lamR = pkScalar P • X.lam :=
  ⟨pkScalar_ne_zero P, class_eq_pkScalar P, rfl⟩

/-- **The class-functional tensor of the realization is the actual one** (tex L3882–3892, the
coordinate of `[z] ⊗ [λ]`): `zR ⊗ lamR = z ⊗ lam` over `K`. Kind: PROVED. -/
theorem ofPrimitiveVector_vecMulVec (X : RetainedInstanceModel R K n) (P : X.PrimitiveVector) :
    vecMulVec (fun i => algebraMap R K ((X.ofPrimitiveVector ϖ P).zR i))
        (fun i => algebraMap R K ((X.ofPrimitiveVector ϖ P).lamR i)) =
      vecMulVec (fun i => algebraMap R K (X.z i)) (fun i => algebraMap R K (X.lam i)) := by
  ext a b
  simp only [vecMulVec_apply, ofPrimitiveVector, Pi.smul_apply, smul_eq_mul, map_mul,
    class_eq_pkScalar P a]
  ring

/-- **The realization has the actual coordinate in the central normalization** (tex L3877–3892):
`zR ⊗ lamR = ((-1)^n u) · adj M` with `u` the actual coordinate. Kind: PROVED. -/
theorem ofPrimitiveVector_isClassFunctionalCoord (X : RetainedInstanceModel R K n)
    (P : X.PrimitiveVector) :
    IsClassFunctionalCoord (X.M.map (algebraMap R K))
      (fun i => algebraMap R K ((X.ofPrimitiveVector ϖ P).zR i))
      (fun i => algebraMap R K ((X.ofPrimitiveVector ϖ P).lamR i)) ((-1) ^ n * X.coord) := by
  unfold IsClassFunctionalCoord
  rw [ofPrimitiveVector_vecMulVec]
  exact X.isClassFunctionalCoord

/-- **The computed coordinate of the realization is the actual coordinate** (tex L3882–3892,
L4948–4951: the coordinate is that of the actual class and the actual functional).
Kind: PROVED. -/
theorem ofPrimitiveVector_coordOf (X : RetainedInstanceModel R K n) (P : X.PrimitiveVector) :
    (X.ofPrimitiveVector ϖ P).coordOf = X.coord := by
  have hz : (fun i => algebraMap R K (X.z i)) =
      algebraMap R K (pkScalar P) • fun i => algebraMap R K (pvec P i) :=
    funext fun i => class_eq_pkScalar P i
  have hl : (fun i => algebraMap R K ((pkScalar P • X.lam) i)) =
      algebraMap R K (pkScalar P) • fun i => algebraMap R K (X.lam i) :=
    funext fun i => by simp
  show classFunctionalCoordWith (X.M.map (algebraMap R K)) (fun i => algebraMap R K (pvec P i))
      (fun i => algebraMap R K ((pkScalar P • X.lam) i)) X.w X.y =
    classFunctionalCoordWith (X.M.map (algebraMap R K)) (fun i => algebraMap R K (X.z i))
      (fun i => algebraMap R K (X.lam i)) X.w X.y
  rw [hz, hl]
  unfold classFunctionalCoordWith
  rw [detCols_colsZW_smul, smul_dotProduct, smul_eq_mul]
  ring

variable {ϖ}

/-- **The primitive kernel vector exists** (tex L4987–4990: "`ker d` is saturated in `R^s`:
divide a nonzero kernel vector by its largest common power of a uniformizer"): for `R → K`
injective, the nonzero actual class gives a primitive kernel vector (the RC53 group's
`exists_primitiveKernelVector`). Kind: PROVED. -/
theorem exists_primitiveVector (hinj : Function.Injective (algebraMap R K))
    (X : RetainedInstanceModel R K n) : Nonempty X.PrimitiveVector :=
  UniformSwitch.exists_primitiveKernelVector hinj (IsLocalRing.residue R) X.stage
    (Function.ne_iff.mp X.hz0)

variable (ϖ)

/-- **The outer instance model of the retained data** (tex L4936–4950): `ofPrimitiveVector` at a
primitive kernel vector chosen by `exists_primitiveVector` (the text: "In each generic
one-dimensional kernel choose a primitive vector `v_j`"). Kind: definition. -/
def toInstanceModel (hinj : Function.Injective (algebraMap R K))
    (X : RetainedInstanceModel R K n) : InstanceModel ϖ K n :=
  X.ofPrimitiveVector ϖ (X.exists_primitiveVector hinj).some

/-- The model is the actual model (tex L4937–4938). Kind: PROVED. -/
theorem toInstanceModel_M (hinj : Function.Injective (algebraMap R K))
    (X : RetainedInstanceModel R K n) : (X.toInstanceModel ϖ hinj).M = X.M := rfl

/-- **The computed coordinate is the actual coordinate** (tex L3882–3892, L4948–4951).
Kind: PROVED. -/
theorem toInstanceModel_coordOf (hinj : Function.Injective (algebraMap R K))
    (X : RetainedInstanceModel R K n) : (X.toInstanceModel ϖ hinj).coordOf = X.coord :=
  X.ofPrimitiveVector_coordOf ϖ _

/-- **The class-functional tensor is the actual one** (tex L3882–3892). Kind: PROVED. -/
theorem toInstanceModel_vecMulVec (hinj : Function.Injective (algebraMap R K))
    (X : RetainedInstanceModel R K n) :
    vecMulVec (fun i => algebraMap R K ((X.toInstanceModel ϖ hinj).zR i))
        (fun i => algebraMap R K ((X.toInstanceModel ϖ hinj).lamR i)) =
      vecMulVec (fun i => algebraMap R K (X.z i)) (fun i => algebraMap R K (X.lam i)) :=
  X.ofPrimitiveVector_vecMulVec ϖ _

/-- **The actual class is a nonzero multiple of the model class in `R`, the scalar moved into the
functional** (tex L4948): `z = c₀ • zR` and `lamR = c₀ • lam` with `c₀ ∈ R`, `c₀ ≠ 0`.
Kind: PROVED. -/
theorem toInstanceModel_class_eq (hinj : Function.Injective (algebraMap R K))
    (X : RetainedInstanceModel R K n) :
    ∃ c : R, c ≠ 0 ∧ X.z = c • (X.toInstanceModel ϖ hinj).zR ∧
      (X.toInstanceModel ϖ hinj).lamR = c • X.lam := by
  refine ⟨pkScalar (X.exists_primitiveVector hinj).some,
    pkScalar_ne_zero _, funext fun i => hinj ?_, rfl⟩
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  exact class_eq_pkScalar _ i

/-- Realizing the retained model of an old instance model keeps its coordinate (tex L3882–3892).
Kind: PROVED. -/
theorem toInstanceModel_ofInstanceModel_coordOf (hinj : Function.Injective (algebraMap R K))
    (X : InstanceModel ϖ K n) :
    ((ofInstanceModel X).toInstanceModel ϖ hinj).coordOf = X.coordOf :=
  (toInstanceModel_coordOf ϖ hinj _).trans (ofInstanceModel_coord X)

end Primitive

end RetainedInstanceModel

end Retained

/-! ### The retained switched models and their outer switching data -/

section Family

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {Inst P : Type}

variable (R K) in
/-- **The retained switched models** (tex L4936–4953): for every instance `i` and every list `l`
of derivative-prime labels, the actual retained data of the minimal model of `i` after the
switches `l` (`model i []` that of the actual minimal model of `i`), of size `nOf l` (the bounded
size fixed on an outer-large set, tex L4936–4939; the common size is batch 3's departure of form,
as in `GenuineOuterModels`). The actual classes are only nonzero (tex L4948). Kind: definition. -/
structure RetainedOuterModels (Inst P : Type) where
  nOf : List P → ℕ
  model : Inst → (l : List P) → RetainedInstanceModel R K (nOf l)

namespace RetainedOuterModels

/-- **The retained family of a genuine family** (tex L4936–4940): every old instance model as a
retained model (`RetainedInstanceModel.ofInstanceModel`). Kind: definition. -/
def ofGenuine {ϖ : R} (G : GenuineOuterModels ϖ K Inst P) : RetainedOuterModels R K Inst P where
  nOf := G.nOf
  model i l := RetainedInstanceModel.ofInstanceModel (G.model i l)

/-- The coordinates of the retained family of a genuine family are its coordinates
(tex L3882–3892). Kind: PROVED. -/
theorem ofGenuine_coord {ϖ : R} (G : GenuineOuterModels ϖ K Inst P) (i : Inst) (l : List P) :
    ((ofGenuine G).model i l).coord = (G.model i l).coordOf := rfl

end RetainedOuterModels

variable {J : Type} (𝒰 : Ultrafilter J)
variable [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) [Fact (Irreducible ϖ)]

/-- **The outer kernel dimension of a sequence of integral models** (tex L4732–4734,
L4940–4941): the dimension `s` of the kernel of their genuine outer matrix (RC6's `outerMatrix`)
over `Frac 𝒪_∞`. Kind: definition. -/
def outerKerDim {n : ℕ} (M : J → Matrix (Fin (n + 1)) (Fin (n + 1)) R) : ℕ :=
  finrank (FractionRing (OInf 𝒰 ϖ)) (LinearMap.ker
    ((outerMatrix 𝒰 ϖ M).map (algebraMap (OInf 𝒰 ϖ) (FractionRing (OInf 𝒰 ϖ)))).mulVecLin)

/-- **The realized stage of a sequence of retained models has the outer kernel dimension of the
actual matrices** (tex L4940–4941): the stage `configStage` of the realized models. Kind: PROVED. -/
theorem realizedStage_outerDim (hinj : Function.Injective (algebraMap R K)) {n : ℕ}
    (X : J → RetainedInstanceModel R K n) :
    (configStage 𝒰 fun j => (X j).toInstanceModel ϖ hinj).base.toOuterStage.outerDim =
      outerKerDim 𝒰 ϖ (fun j => (X j).M) := rfl

/-- **The realized stage of a sequence of retained models has the actual inner coordinates** (tex
L4948–4951). Kind: PROVED. -/
theorem realizedStage_coord (hinj : Function.Injective (algebraMap R K)) {n : ℕ}
    (X : J → RetainedInstanceModel R K n) (j : J) :
    (configStage 𝒰 fun j => (X j).toInstanceModel ϖ hinj).base.toOuterStage.coord j =
      (X j).coord :=
  (X j).toInstanceModel_coordOf ϖ hinj

namespace RetainedOuterModels

/-- **The primitive-vector realization of a retained family** (tex L4936–4950): every supplied
model is realized at a primitive kernel vector, with the scalar moved into the functional. The
matrix, class-functional tensor and coordinate are preserved; the class and functional need not be
preserved separately. Arithmetic identification remains open. Kind: definition. -/
def toGenuine (T : RetainedOuterModels R K Inst P) (hinj : Function.Injective (algebraMap R K)) :
    GenuineOuterModels ϖ K Inst P where
  nOf := T.nOf
  model i l := (T.model i l).toInstanceModel ϖ hinj

variable {ϖ}

/-- The realized models have the sizes of the retained ones (tex L4936–4939). Kind: PROVED. -/
theorem toGenuine_nOf (T : RetainedOuterModels R K Inst P)
    (hinj : Function.Injective (algebraMap R K)) : (T.toGenuine ϖ hinj).nOf = T.nOf := rfl

/-- **The realized models have the actual matrices** (tex L4937–4938). Kind: PROVED. -/
theorem toGenuine_M (T : RetainedOuterModels R K Inst P)
    (hinj : Function.Injective (algebraMap R K)) (i : Inst) (l : List P) :
    ((T.toGenuine ϖ hinj).model i l).M = (T.model i l).M := rfl

/-- **The realized models have the actual coordinates** (tex L3882–3892, L4948–4951).
Kind: PROVED. -/
theorem toGenuine_coordOf (T : RetainedOuterModels R K Inst P)
    (hinj : Function.Injective (algebraMap R K)) (i : Inst) (l : List P) :
    ((T.toGenuine ϖ hinj).model i l).coordOf = (T.model i l).coord :=
  (T.model i l).toInstanceModel_coordOf ϖ hinj

/-- **The outer dimension of a realized stage is that of the actual matrices** (tex L4940–4941).
Kind: PROVED. -/
theorem toGenuine_stage_outerDim (T : RetainedOuterModels R K Inst P)
    (hinj : Function.Injective (algebraMap R K)) (inst : J → Inst) (l : List P) :
    ((T.toGenuine ϖ hinj).stage 𝒰 inst l).base.toOuterStage.outerDim =
      outerKerDim 𝒰 ϖ (fun j => (T.model (inst j) l).M) := rfl

/-- **The inner coordinates of a realized stage are the actual coordinates** (tex L4948–4951:
"Exact switch preservation therefore keeps each inner determinant valuation"). Kind: PROVED. -/
theorem toGenuine_stage_coord (T : RetainedOuterModels R K Inst P)
    (hinj : Function.Injective (algebraMap R K)) (inst : J → Inst) (l : List P) (j : J) :
    ((T.toGenuine ϖ hinj).stage 𝒰 inst l).base.toOuterStage.coord j =
      (T.model (inst j) l).coord :=
  (T.model (inst j) l).toInstanceModel_coordOf ϖ hinj

/-- **The outer kernel vector of a realized stage is the outer image of the primitive vectors,
and is nonzero** (tex L4939–4941: "Its outer image is nonzero"). Kind: PROVED. -/
theorem toGenuine_stage_zout (T : RetainedOuterModels R K Inst P)
    (hinj : Function.Injective (algebraMap R K)) (inst : J → Inst) (l : List P) :
    ((T.toGenuine ϖ hinj).stage 𝒰 inst l).base.zout =
        SwitchInputs.outerClass 𝒰 (fun j => (T.model (inst j) l).toInstanceModel ϖ hinj) ∧
      ((T.toGenuine ϖ hinj).stage 𝒰 inst l).base.zout ≠ 0 :=
  ⟨rfl, ((T.toGenuine ϖ hinj).stage 𝒰 inst l).base.hzout0⟩

/-- **The outer kernel dimension of the actual matrices is at least one** (tex L4940–4941: "so
the outer kernel dimension `s` is at least one"), from the nonzero actual classes alone.
Kind: PROVED. -/
theorem one_le_outerKerDim (T : RetainedOuterModels R K Inst P)
    (hinj : Function.Injective (algebraMap R K)) (inst : J → Inst) (l : List P) :
    1 ≤ outerKerDim 𝒰 ϖ (fun j => (T.model (inst j) l).M) :=
  ((T.toGenuine ϖ hinj).stage 𝒰 inst l).base.toOuterStage.one_le_outerDim

end RetainedOuterModels

/-- **The switch input on the actual data** (tex L4940–4950; definition; ELLIOT switch input with
GLUE comparisons, for the actual configurations): the fields of `OuterSwitchStep` with the outer
dimensions those of the actual matrices and the inner coordinates the actual coordinates — a
Selmer-level nonquadratic step over `Frac 𝒪_∞` (Plug's `SelmerNonquadStep`) whose side dimensions
are the outer kernel dimensions before and after the switch, and, on an outer-large set, switch
coordinate data with volume normalizations images of units of `R` whose finite and singular
coordinates are the actual coordinates before and after the switch. Kind: definition. -/
structure RetainedSwitchStep {n n' : ℕ} (X : J → RetainedInstanceModel R K n)
    (X' : J → RetainedInstanceModel R K n') where
  sel : SelmerNonquadStep (FractionRing (OInf 𝒰 ϖ))
  hs : outerKerDim 𝒰 ϖ (fun j => (X j).M) =
    finrank (FractionRing (OInf 𝒰 ϖ)) ((selCx sel.SF.Dside).toCC.homology 1)
  hs' : outerKerDim 𝒰 ϖ (fun j => (X' j).M) =
    finrank (FractionRing (OInf 𝒰 ϖ)) ((selCx sel.SS.Dside).toCC.homology 1)
  coords : ∀ᶠ j in (𝒰 : Filter J), ∃ (Y : SwitchCoordData K) (mF mS : R),
    IsUnit mF ∧ IsUnit mS ∧ Y.μF = algebraMap R K mF ∧ Y.μS = algebraMap R K mS ∧
      (X j).coord = Y.uF ∧ (X' j).coord = Y.uS

variable {𝒰 ϖ}

/-- **The outer switch step of the realized stages** (tex L4940–4950): a switch input on the actual
data is the switch input `OuterSwitchStep` of the stages of the realized models. Kind: PROVED. -/
def RetainedSwitchStep.toOuterSwitchStep (hinj : Function.Injective (algebraMap R K))
    {n n' : ℕ} {X : J → RetainedInstanceModel R K n} {X' : J → RetainedInstanceModel R K n'}
    (S : RetainedSwitchStep 𝒰 ϖ X X') :
    OuterSwitchStep (configStage 𝒰 fun j => (X j).toInstanceModel ϖ hinj).base.toOuterStage
      (configStage 𝒰 fun j => (X' j).toInstanceModel ϖ hinj).base.toOuterStage where
  X := S.sel
  hs := S.hs
  hs' := S.hs'
  coords := S.coords.mono fun j ⟨Y, mF, mS, hF, hS, hYF, hYS, h1, h2⟩ =>
    ⟨Y, mF, mS, hF, hS, hYF, hYS, ((X j).toInstanceModel_coordOf ϖ hinj).trans h1,
      ((X' j).toInstanceModel_coordOf ϖ hinj).trans h2⟩

/-- **The switch input on the actual data from that of the realized stages** (tex L4940–4950).
Kind: PROVED. -/
def RetainedSwitchStep.ofOuterSwitchStep (hinj : Function.Injective (algebraMap R K))
    {n n' : ℕ} {X : J → RetainedInstanceModel R K n} {X' : J → RetainedInstanceModel R K n'}
    (S : OuterSwitchStep (configStage 𝒰 fun j => (X j).toInstanceModel ϖ hinj).base.toOuterStage
      (configStage 𝒰 fun j => (X' j).toInstanceModel ϖ hinj).base.toOuterStage) :
    RetainedSwitchStep 𝒰 ϖ X X' where
  sel := S.X
  hs := S.hs
  hs' := S.hs'
  coords := S.coords.mono fun j ⟨Y, mF, mS, hF, hS, hYF, hYS, h1, h2⟩ =>
    ⟨Y, mF, mS, hF, hS, hYF, hYS, ((X j).toInstanceModel_coordOf ϖ hinj).symm.trans h1,
      ((X' j).toInstanceModel_coordOf ϖ hinj).symm.trans h2⟩

/-- **The switch input of old instance models on their retained data** (old ⇒ new; tex
L4940–4950). Kind: PROVED. -/
def RetainedSwitchStep.ofInstanceModels {n n' : ℕ} {X : J → InstanceModel ϖ K n}
    {X' : J → InstanceModel ϖ K n'}
    (S : OuterSwitchStep (configStage 𝒰 X).base.toOuterStage (configStage 𝒰 X').base.toOuterStage) :
    RetainedSwitchStep 𝒰 ϖ (fun j => RetainedInstanceModel.ofInstanceModel (X j))
      (fun j => RetainedInstanceModel.ofInstanceModel (X' j)) where
  sel := S.X
  hs := S.hs
  hs' := S.hs'
  coords := S.coords

variable (𝒰 ϖ)

/-- **The outer switching data on the actual data** (tex L4936–4964; definition; ELLIOT switch input
with GLUE comparisons, for the actual configurations): for a retained family `T` and a sequence
`inst` of instances, at every configuration `l` whose actual matrices have outer kernel dimension
`> 1`, a derivative-prime label `p` and a `RetainedSwitchStep` between the actual data at `l` and at
`l ++ [p]`. Kind: definition. -/
structure RetainedOuterSwitchData (T : RetainedOuterModels R K Inst P) (inst : J → Inst) :
    Prop where
  step : ∀ l : List P, 1 < outerKerDim 𝒰 ϖ (fun j => (T.model (inst j) l).M) →
    ∃ p : P, Nonempty (RetainedSwitchStep 𝒰 ϖ (fun j => T.model (inst j) l)
      fun j => T.model (inst j) (l ++ [p]))

variable {𝒰 ϖ}

/-- **The genuine outer switching data of the realized family** (tex L4936–4964). Kind: PROVED. -/
theorem RetainedOuterSwitchData.toGenuine (hinj : Function.Injective (algebraMap R K))
    {T : RetainedOuterModels R K Inst P} {inst : J → Inst}
    (H : RetainedOuterSwitchData 𝒰 ϖ T inst) :
    SwitchInputs.GenuineOuterSwitchData 𝒰 (T.toGenuine ϖ hinj) inst where
  step l hl := by
    obtain ⟨p, ⟨S⟩⟩ := H.step l hl
    exact ⟨p, ⟨S.toOuterSwitchStep hinj⟩⟩

/-- **The outer switching data on the actual data from those of the realized family** (tex
L4936–4964). Kind: PROVED. -/
theorem RetainedOuterSwitchData.ofGenuine (hinj : Function.Injective (algebraMap R K))
    {T : RetainedOuterModels R K Inst P} {inst : J → Inst}
    (H : SwitchInputs.GenuineOuterSwitchData 𝒰 (T.toGenuine ϖ hinj) inst) :
    RetainedOuterSwitchData 𝒰 ϖ T inst where
  step l hl := by
    obtain ⟨p, ⟨S⟩⟩ := H.step l hl
    exact ⟨p, ⟨RetainedSwitchStep.ofOuterSwitchStep hinj S⟩⟩

/-- **The switch input on the actual data is that of the realized family** (tex L4936–4964).
Kind: PROVED. -/
theorem retainedOuterSwitchData_iff (hinj : Function.Injective (algebraMap R K))
    (T : RetainedOuterModels R K Inst P) (inst : J → Inst) :
    RetainedOuterSwitchData 𝒰 ϖ T inst ↔
      SwitchInputs.GenuineOuterSwitchData 𝒰 (T.toGenuine ϖ hinj) inst :=
  ⟨RetainedOuterSwitchData.toGenuine hinj, RetainedOuterSwitchData.ofGenuine hinj⟩

/-- **Old switching data are switching data on the retained data of the old family** (tex
L4936–4964). Kind: PROVED. -/
theorem RetainedOuterSwitchData.ofGenuineModels {G : GenuineOuterModels ϖ K Inst P}
    {inst : J → Inst} (H : SwitchInputs.GenuineOuterSwitchData 𝒰 G inst) :
    RetainedOuterSwitchData 𝒰 ϖ (RetainedOuterModels.ofGenuine G) inst where
  step l hl := by
    obtain ⟨p, ⟨S⟩⟩ := H.step l hl
    exact ⟨p, ⟨RetainedSwitchStep.ofInstanceModels S⟩⟩

variable (ϖ)

/-- **(5.5) for the actual coordinates** (tex L4909–4972): for a retained family `T` over the DVR
`R` (with `R → K` injective and `v` a `ϖ`-adic valuation of `K`), if the outer switching data on
the actual data exist along the fixed nonprincipal ultrafilter for every sequence of instances,
then the actual coordinates `(T.model i []).coord` are bounded below uniformly. Kind: PROVED (from
the inputs, through batch 3's `uniform_lower_bound_of_genuine` for `T.toGenuine`). -/
theorem uniform_lower_bound_of_retained (v : AddValuation K (WithTop ℤ))
    (T : RetainedOuterModels R K Inst P) (hinj : Function.Injective (algebraMap R K))
    (hv : IsPiAdicOn ϖ v)
    (inputs : ∀ inst : ℕ → Inst, RetainedOuterSwitchData (Filter.hyperfilter ℕ) ϖ T inst) :
    ∃ C : ℕ, ∀ i, (((-C : ℤ)) : WithTop ℤ) ≤ v (T.model i []).coord := by
  obtain ⟨C, hC⟩ := SwitchInputs.uniform_lower_bound_of_genuine (T.toGenuine ϖ hinj) hinj hv
    fun inst => (inputs inst).toGenuine hinj
  exact ⟨C, fun i => (hC i).trans_eq (congrArg v (T.toGenuine_coordOf hinj i []))⟩

end Family

/-! ### The outer conjunct of the (3.5) leaves -/

section OuterPart

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R)
  [Fact (Irreducible ϖ)] (K : Type) [Field K] [Algebra R K]

/-- **The outer conjunct of the (3.5) leaves, on genuine outer models** (tex L4909–4972,
L4453–4460): a label type `Pl` and a family `G` of `GenuineOuterModels` for the instances `Inst`
with sizes at most `cap` of the number of switches, every matrix satisfying `Gen`, the computed
coordinates of the starting models with the valuations of the targets `u`, and batch 3's
`GenuineOuterSwitchData` along the fixed nonprincipal ultrafilter for every sequence of instances.
Kind: definition. -/
def GenuineOuterPart (Inst : Type) (cap : ℕ → ℕ)
    (Gen : ∀ {n : ℕ}, Matrix (Fin (n + 1)) (Fin (n + 1)) R → Prop)
    (v : AddValuation K (WithTop ℤ)) (u : Inst → K) : Prop :=
  ∃ (Pl : Type) (G : GenuineOuterModels ϖ K Inst Pl), (∀ l, G.nOf l ≤ cap l.length) ∧
    (∀ i l, Gen (G.model i l).M) ∧ (∀ i, v (G.model i []).coordOf = v (u i)) ∧
    ∀ inst : ℕ → Inst, SwitchInputs.GenuineOuterSwitchData (Filter.hyperfilter ℕ) G inst

/-- **The outer conjunct of the (3.5) leaves, on the actual retained data** (tex L4909–4972,
L4453–4460): as `GenuineOuterPart`, with a retained family `T` (actual classes only nonzero), the
ACTUAL coordinates of the starting data, and the switch input on the actual data
(`RetainedOuterSwitchData`). Kind: definition. -/
def RetainedOuterPart (Inst : Type) (cap : ℕ → ℕ)
    (Gen : ∀ {n : ℕ}, Matrix (Fin (n + 1)) (Fin (n + 1)) R → Prop)
    (v : AddValuation K (WithTop ℤ)) (u : Inst → K) : Prop :=
  ∃ (Pl : Type) (T : RetainedOuterModels R K Inst Pl), (∀ l, T.nOf l ≤ cap l.length) ∧
    (∀ i l, Gen (T.model i l).M) ∧ (∀ i, v (T.model i []).coord = v (u i)) ∧
    ∀ inst : ℕ → Inst, RetainedOuterSwitchData (Filter.hyperfilter ℕ) ϖ T inst

/-- **The outer conjunct on the actual retained data is the outer conjunct of the leaves**
(tex L4936–4972): `→` realizes the retained family (`toGenuine`: actual matrices, actual
coordinates, the switch data transported); `←` reads every old family as a retained one
(`ofGenuine`). Kind: PROVED. -/
theorem retainedOuterPart_iff (hinj : Function.Injective (algebraMap R K)) (Inst : Type)
    (cap : ℕ → ℕ) (Gen : ∀ {n : ℕ}, Matrix (Fin (n + 1)) (Fin (n + 1)) R → Prop)
    (v : AddValuation K (WithTop ℤ)) (u : Inst → K) :
    RetainedOuterPart ϖ K Inst cap Gen v u ↔ GenuineOuterPart ϖ K Inst cap Gen v u := by
  constructor
  · rintro ⟨Pl, T, hcap, hgen, hcoord, hsw⟩
    exact ⟨Pl, T.toGenuine ϖ hinj, hcap, hgen,
      fun i => (congrArg v (T.toGenuine_coordOf hinj i [])).trans (hcoord i),
      fun inst => (hsw inst).toGenuine hinj⟩
  · rintro ⟨Pl, G, hcap, hgen, hcoord, hsw⟩
    exact ⟨Pl, RetainedOuterModels.ofGenuine G, hcap, hgen, hcoord,
      fun inst => RetainedOuterSwitchData.ofGenuineModels (hsw inst)⟩

end OuterPart

/-! ### The outer conjunct of the current (3.5) leaf over `𝒪` -/

section Eq35

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Rings CategoryTheory
open ZInQ.Manuscript.RC.Determinant (OO)
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData)

/-- **A two-term model of genuine Galois Selmer data over `𝒪`** (tex L4927–4940): the condition of
`IsGenuineInstanceModel` on the matrix alone — genuine Galois Selmer data over `𝒪` (lane RC26's
`galoisSelData`) with a homotopy equivalence from their Selmer complex to
`[𝒪^{n+1} --M--> 𝒪^{n+1}]` (GLUE identification, owners as at `IsGenuineInstanceModel`).
Kind: definition. -/
def IsGenuineTwoTermModel {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) OO) : Prop :=
  ∃ D : SelData OO, IsGaloisSelData D ∧
    Nonempty (HomotopyEquiv (selCx D).toCC (integralTwoTerm M))

/-- `IsGenuineInstanceModel` is a condition on the matrix (tex L4927–4940; its class and functional
do not enter). Kind: PROVED. -/
theorem isGenuineInstanceModel_iff {n : ℕ} (X : InstanceModel (2 : OO) (FractionRing OO) n) :
    IsGenuineInstanceModel X ↔ IsGenuineTwoTermModel X.M := Iff.rfl

/-- The realization of a retained model over `𝒪` is a genuine instance model iff its actual matrix
is a genuine two-term model (tex L4927–4940). Kind: PROVED. -/
theorem isGenuineInstanceModel_toInstanceModel {n : ℕ}
    (X : RetainedInstanceModel OO (FractionRing OO) n) :
    IsGenuineInstanceModel (X.toInstanceModel (2 : OO) injective_algebraMap_OO) ↔
      IsGenuineTwoTermModel X.M := Iff.rfl

/-- **A genuine retained model forces nonzero genuine `H¹`** (tex L4928–4934): if the actual matrix
is a genuine two-term model, the genuine Galois Selmer data it models have `H¹ ≠ 0`; the nonzero
actual class is a nonzero cycle of the model (no primitivity is used, compare
`IsGenuineInstanceModel.h1_nontrivial`). Kind: PROVED. -/
theorem RetainedInstanceModel.h1_nontrivial {n : ℕ}
    {X : RetainedInstanceModel OO (FractionRing OO) n} (h : IsGenuineTwoTermModel X.M) :
    ∃ D : SelData OO, IsGaloisSelData D ∧ Nontrivial ((selCx D).toCC.homology 1) := by
  obtain ⟨D, hD, ⟨e⟩⟩ := h
  have := integralTwoTerm_h1_nontrivial X.M X.z X.hz X.hz0
  exact ⟨D, hD, ((e.toHomologyIso 1).toLinearEquiv.toEquiv).nontrivial⟩

/-- **The zero genuine data model no retained model** (tex L4928–4934): there is no homotopy
equivalence from the Selmer complex of the zero genuine Galois data over `𝒪` to the two-term
complex of a retained model (its `H¹` is zero, that of the model contains the nonzero actual class;
compare `zeroSelData_not_model`). Kind: PROVED. -/
theorem RetainedInstanceModel.zeroSelData_not_model {n : ℕ}
    (X : RetainedInstanceModel OO (FractionRing OO) n) :
    IsEmpty (HomotopyEquiv (selCx (zeroSelData OO)).toCC (integralTwoTerm X.M)) := by
  refine ⟨fun e => ?_⟩
  have hn := integralTwoTerm_h1_nontrivial X.M X.z X.hz X.hz0
  have hs := homology_subsingleton_of_X _ 1 (zeroSelData_X1_subsingleton OO)
  have hn' : Nontrivial ((selCx (zeroSelData OO)).toCC.homology 1) :=
    ((e.toHomologyIso 1).toLinearEquiv.toEquiv).nontrivial
  exact (not_nontrivial_iff_subsingleton.mpr hs) hn'

/-- **The outer conjunct of the (3.5) leaf at `A`, on the actual retained classes** (tex
L4909–4972, L4453–4460, at the ring instances of tex L2418–2446, over lane RC20's `𝒪` with
`K = Frac 𝒪`, `v = v_𝒪`): for every size bound `cap`, the outer conjunct on retained families
(actual classes only nonzero, actual coordinates, switch input on the actual data) is equivalent
to the outer conjunct on batch 3's `GenuineOuterModels`. With `cap = eq51Cap ℓ A` the right side
is verbatim the conjunct at `A` of `Eq35InputsGenuineABounded W` (`GenuineEq35Pad.lean`) and of
`Eq35InputsGenuineABoundedH W` (`GenuineEq35H.lean`). Kind: PROVED. -/
theorem eq35OuterPart_iff {ℓ : ℕ} (W : WData ℓ) (A : ℕ) (cap : ℕ → ℕ)
    (uprim : ℤ → ℤ → FractionRing RC.Uniform.Lambda) :
    (∃ (Pl : Type) (T : RetainedOuterModels OO (FractionRing OO) (CompanionPair W A) Pl),
      (∀ l, T.nOf l ≤ cap l.length) ∧ (∀ i l, IsGenuineTwoTermModel (T.model i l).M) ∧
      (∀ i : CompanionPair W A, vO (T.model i []).coord = vO (iotaO (uprim i.h i.k))) ∧
      ∀ inst : ℕ → CompanionPair W A,
        RetainedOuterSwitchData (Filter.hyperfilter ℕ) (2 : OO) T inst) ↔
    ∃ (Pl : Type)
      (G : GenuineOuterModels (2 : OO) (FractionRing OO) (CompanionPair W A) Pl),
      (∀ l, G.nOf l ≤ cap l.length) ∧ (∀ i l, IsGenuineInstanceModel (G.model i l)) ∧
      (∀ i : CompanionPair W A, vO (G.model i []).coordOf = vO (iotaO (uprim i.h i.k))) ∧
      ∀ inst : ℕ → CompanionPair W A,
        SwitchInputs.GenuineOuterSwitchData (Filter.hyperfilter ℕ) G inst :=
  retainedOuterPart_iff (2 : OO) (FractionRing OO) injective_algebraMap_OO (CompanionPair W A) cap
    IsGenuineTwoTermModel vO fun i => iotaO (uprim i.h i.k)

/-- **(5.5) at the companion pairs from the outer conjunct on the actual retained classes**
(tex L4927–4972): for each `A`, a retained family as in `eq35OuterPart_iff` bounds the actual
coordinates, hence `v_𝒪 (ι_𝒪 u_prim)`, below uniformly. Kind: PROVED (from the inputs, through
`uniform_lower_bound_of_retained` and lane RC20's `isPiAdicOn_two_vO`). -/
theorem eq55_of_retained {ℓ : ℕ} {W : WData ℓ} {A : ℕ} {Pl : Type}
    (uprim : ℤ → ℤ → FractionRing RC.Uniform.Lambda)
    (T : RetainedOuterModels OO (FractionRing OO) (CompanionPair W A) Pl)
    (hcoord : ∀ i : CompanionPair W A, vO (T.model i []).coord = vO (iotaO (uprim i.h i.k)))
    (hsw : ∀ inst : ℕ → CompanionPair W A,
      RetainedOuterSwitchData (Filter.hyperfilter ℕ) (2 : OO) T inst) :
    ∃ C : ℕ, ∀ i : CompanionPair W A, (((-C : ℤ)) : WithTop ℤ) ≤ vO (iotaO (uprim i.h i.k)) := by
  obtain ⟨C, hC⟩ := uniform_lower_bound_of_retained (2 : OO) vO T injective_algebraMap_OO
    isPiAdicOn_two_vO hsw
  exact ⟨C, fun i => (hC i).trans_eq (hcoord i)⟩

end Eq35

/-! ### Non-vacuity -/

section Examples

/-- The inclusion `ℤ₂ → ℚ₂` is injective (the hypothesis `R → K` injective of tex L4987–4990 in the
example). Kind: PROVED. -/
theorem padicInt_algebraMap_injective : Function.Injective (algebraMap ℤ_[2] ℚ_[2]) :=
  Subtype.coe_injective

/-- **A retained instance whose actual class is divisible** (tex L4948: the actual class a
divisible scalar multiple of the primitive vector): over `ℤ₂ ⊂ ℚ₂`, the model `[ℤ₂ --0--> ℤ₂]` with
actual class `2`, functional `1` and complement `y = 1`. Kind: definition. -/
def exRetained : RetainedInstanceModel ℤ_[2] ℚ_[2] 0 where
  M := 0
  z := fun _ => 2
  lam := fun _ => 1
  hz := by simp
  hlam := by simp
  w := Fin.elim0
  y := fun _ => 1
  hden := (SwitchInputs.exModelStage (Filter.hyperfilter ℕ)).hden 0
  hz0 h := two_ne_zero (congrFun h 0)

/-- **The actual class of `exRetained` is not primitive** (tex L4948): the old field `hprim` fails
for it. Kind: PROVED. -/
theorem exRetained_not_primitive : ¬ ∃ i, ¬ (2 : ℤ_[2]) ∣ exRetained.z i :=
  fun ⟨_, hi⟩ => hi (dvd_refl _)

/-- The actual coordinate of `exRetained` is `2` (tex L3882–3892). Kind: PROVED. -/
theorem exRetained_coord : exRetained.coord = 2 := by
  have hnum : detCols (colsZW (fun _ : Fin 1 => algebraMap ℤ_[2] ℚ_[2] 2)
      (Fin.elim0 : Fin 0 → Fin 1 → ℚ_[2])) = 2 := by
    simp only [detCols, colsMat, colsZW]
    rw [Matrix.det_fin_one]
    simp only [Matrix.of_apply, Fin.cons_zero]
    exact map_ofNat _ 2
  have hden : detCols (colsDWY ((0 : Matrix (Fin 1) (Fin 1) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2]))
      (Fin.elim0 : Fin 0 → Fin 1 → ℚ_[2]) fun _ => 1) = 1 := by
    simp only [detCols, colsMat, colsDWY]
    rw [Matrix.det_fin_one]
    simp [Fin.snoc]
  show detCols (colsZW (fun _ : Fin 1 => algebraMap ℤ_[2] ℚ_[2] 2) Fin.elim0) *
      ((fun _ : Fin 1 => algebraMap ℤ_[2] ℚ_[2] 1) ⬝ᵥ fun _ => 1) /
      detCols (colsDWY ((0 : Matrix (Fin 1) (Fin 1) ℤ_[2]).map (algebraMap ℤ_[2] ℚ_[2]))
        Fin.elim0 fun _ => 1) = 2
  rw [hnum, hden]
  simp [dotProduct]

/-- **The text's primitive vector of `exRetained`** (tex L4939–4940, L4987–4992): `v = 1`, with
`z = 2 v`. Kind: definition. -/
def exPrimitiveVector : exRetained.PrimitiveVector where
  v := fun _ => 1
  hv := by
    change (0 : Matrix (Fin 1) (Fin 1) ℤ_[2]) *ᵥ _ = 0
    exact Matrix.zero_mulVec _
  hprim := ⟨0, by simp⟩
  c := 2
  hc := two_ne_zero
  hzv _ := by
    change algebraMap ℤ_[2] ℚ_[2] 2 = 2 * algebraMap ℤ_[2] ℚ_[2] 1
    rw [map_ofNat, map_one, mul_one]

/-- **The realization of `exRetained`** at the primitive vector `1` (tex L4936–4950).
Kind: definition. -/
def exRealized : InstanceModel (2 : ℤ_[2]) ℚ_[2] 0 :=
  exRetained.ofPrimitiveVector 2 exPrimitiveVector

/-- The scalar of `exRetained` at `v = 1` is `2` (tex L4948). Kind: PROVED. -/
theorem exPkScalar : RetainedInstanceModel.pkScalar exPrimitiveVector = 2 :=
  padicInt_algebraMap_injective (by rw [RetainedInstanceModel.algebraMap_pkScalar, map_ofNat]; rfl)

/-- **The realization of `exRetained`** (tex L4936–4951): class `1` (primitive), functional `2`
(the scalar moved into the functional), coordinate `2` (the actual coordinate). Kind: PROVED. -/
theorem exRealized_spec :
    exRealized.zR = (fun _ => 1) ∧ exRealized.lamR = (fun _ => 2) ∧ exRealized.coordOf = 2 := by
  refine ⟨rfl, ?_, (exRetained.ofPrimitiveVector_coordOf 2 exPrimitiveVector).trans
    exRetained_coord⟩
  show RetainedInstanceModel.pkScalar exPrimitiveVector • exRetained.lam = _
  rw [exPkScalar]
  funext i
  show (2 : ℤ_[2]) * 1 = 2
  rw [mul_one]

/-- **The constant retained family** (tex L4936–4953; every configuration `exRetained`).
Kind: definition. -/
def exRetainedModels : RetainedOuterModels ℤ_[2] ℚ_[2] Unit Unit where
  nOf _ := 0
  model _ _ := exRetained

/-- The outer kernel dimension of the actual matrices of the constant family is one (tex
L4940–4941). Kind: PROVED. -/
theorem exRetained_outerKerDim (𝒰 : Ultrafilter ℕ) (inst : ℕ → Unit) (l : List Unit) :
    outerKerDim 𝒰 (2 : ℤ_[2]) (fun j => (exRetainedModels.model (inst j) l).M) = 1 := by
  have h0 : (outerMatrix 𝒰 (2 : ℤ_[2]) (fun j => (exRetainedModels.model (inst j) l).M)).map
      (algebraMap (OInf 𝒰 (2 : ℤ_[2])) (FractionRing (OInf 𝒰 (2 : ℤ_[2])))) = 0 := by
    ext a b
    simp only [exRetainedModels, exRetained, outerMatrix, Matrix.zero_apply]
    exact (algebraMap (OInf 𝒰 (2 : ℤ_[2])) (FractionRing (OInf 𝒰 (2 : ℤ_[2])))).map_zero
  unfold outerKerDim
  rw [h0, Matrix.mulVecLin_zero, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun]
  rfl

/-- **The switching data on the actual data of the constant family** (tex L4936–4964; outer
dimension one, so no switch is required). Kind: PROVED. -/
theorem exRetainedOuterSwitchData (𝒰 : Ultrafilter ℕ) (inst : ℕ → Unit) :
    RetainedOuterSwitchData 𝒰 (2 : ℤ_[2]) exRetainedModels inst where
  step l hl := by
    rw [exRetained_outerKerDim] at hl
    exact absurd hl (lt_irrefl 1)

/-- **The uniform bound for the actual coordinates of the constant family** (tex L4909–4972;
consistency check of `uniform_lower_bound_of_retained`, with the divisible actual class `2`).
Kind: PROVED. -/
theorem exRetained_uniform_bound :
    ∃ C : ℕ, ∀ i, (((-C : ℤ)) : WithTop ℤ) ≤
      (Padic.addValuation (p := 2)) (exRetainedModels.model i []).coord :=
  uniform_lower_bound_of_retained (2 : ℤ_[2]) (Padic.addValuation (p := 2)) exRetainedModels
    padicInt_algebraMap_injective SwitchInputs.isPiAdicOn_padic
    fun inst => exRetainedOuterSwitchData _ inst

/-- **The outer conjunct on the actual retained data is satisfiable** (tex L4909–4972; the constant
family, with the trivially true matrix condition and target coordinates `2`), hence so is the
outer conjunct on genuine models. Kind: PROVED. -/
theorem exRetainedOuterPart :
    RetainedOuterPart (2 : ℤ_[2]) ℚ_[2] Unit (fun _ => 0) (fun _ => True)
      (Padic.addValuation (p := 2)) (fun _ => 2) ∧
    GenuineOuterPart (2 : ℤ_[2]) ℚ_[2] Unit (fun _ => 0) (fun _ => True)
      (Padic.addValuation (p := 2)) (fun _ => 2) := by
  have h : RetainedOuterPart (2 : ℤ_[2]) ℚ_[2] Unit (fun _ => 0) (fun _ => True)
      (Padic.addValuation (p := 2)) (fun _ => 2) :=
    ⟨Unit, exRetainedModels, fun _ => le_rfl, fun _ _ => trivial,
      fun _ => congrArg _ exRetained_coord, fun inst => exRetainedOuterSwitchData _ inst⟩
  exact ⟨h, (retainedOuterPart_iff (2 : ℤ_[2]) ℚ_[2] padicInt_algebraMap_injective Unit
    (fun _ => 0) (fun _ => True) (Padic.addValuation (p := 2)) (fun _ => 2)).mp h⟩

/-- **Retained instances whose scalar tends to zero** (tex L4949: "Even if this scalar tends to
zero"): over `ℤ₂ ⊂ ℚ₂`, the models `[ℤ₂ --0--> ℤ₂]` with actual classes `2^j` and functional `1`.
Kind: definition. -/
def exScaled (j : ℕ) : RetainedInstanceModel ℤ_[2] ℚ_[2] 0 where
  M := 0
  z := fun _ => 2 ^ j
  lam := fun _ => 1
  hz := by simp
  hlam := by simp
  w := Fin.elim0
  y := fun _ => 1
  hden := (SwitchInputs.exModelStage (Filter.hyperfilter ℕ)).hden 0
  hz0 h := pow_ne_zero j two_ne_zero (congrFun h 0)

/-- **The outer image of the actual classes can vanish** (tex L4939–4941, L4949): the classes
`2^j` of `exScaled` are infinitesimal along the hyperfilter, so their outer image is `0` and they
cannot serve as the outer kernel vector; the text uses the primitive vectors instead.
Kind: PROVED. -/
theorem exScaled_outerVec_eq_zero :
    outerVec (Filter.hyperfilter ℕ) (2 : ℤ_[2]) (fun j => (exScaled j).z) = 0 := by
  funext a
  show toOInf (Filter.hyperfilter ℕ) (2 : ℤ_[2]) (fun j => (2 : ℤ_[2]) ^ j) = 0
  rw [toOInf_eq_zero_iff]
  intro m
  have hm : ∀ᶠ j in (Filter.hyperfilter ℕ : Filter ℕ), m ≤ j :=
    Filter.hyperfilter_le_cofinite (Filter.eventually_cofinite.mpr (by
      simpa only [not_le] using Set.finite_lt_nat m))
  filter_upwards [hm] with j hj
  exact pow_dvd_pow 2 hj

/-- **The realized outer class of `exScaled` is nonzero** (tex L4939–4941: "Its outer image is
nonzero"): the stage of the realized models has a nonzero outer kernel vector, the outer image of
the primitive vectors. Kind: PROVED. -/
theorem exScaled_realized_zout_ne_zero :
    (configStage (Filter.hyperfilter ℕ) fun j =>
      (exScaled j).toInstanceModel (2 : ℤ_[2]) padicInt_algebraMap_injective).base.zout ≠ 0 :=
  (configStage (Filter.hyperfilter ℕ) fun j =>
    (exScaled j).toInstanceModel (2 : ℤ_[2]) padicInt_algebraMap_injective).base.hzout0

end Examples

end ZInQ.Contrib.RC53Assist.OuterRealization
