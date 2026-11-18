import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuity

/-!
# RC53 SwitchInputs: integrality on the outer side of the switching argument

Proposition `ex:limits-uniform-lower-bound`, proof, tex L4935–4964, with the outer ring (5.3),
tex L4706–4714:

> Determinant-one Schur operations in a square two-term rank-one-kernel complex give
> `u = ±αβ/Δ`, where `α` is an integral surviving cycle coordinate and `β` has valuation at least
> `−a`.

UniformSwitch's `OuterSwitchData` carries the GLUE fields `cycle_integral` (the inner cycles are
integral) and `functional_bound` (`v λ_j ≥ −a`). In the integral two-term models of the text the
actual class and the paired functional are integral (the paired functional with exponent `a = 0`,
`PairedFunctional/Proposition.lean`, tex L3864–3869), so these fields follow from the integral
model itself.

Nodes:
* `exists_primitive_kernel_vector` (PROVED, tex L4927–4940: "the inner kernels have primitive
  vectors"): over a DVR `R` with fraction-field-type `K`, every nonzero kernel vector over `K` of an
  integral matrix is a `K`-multiple of an integral kernel vector one of whose coordinates is not
  divisible by `ϖ`; `exists_primitive_closed_functional` (PROVED): the same for closed functionals.
* `IntegralModelStage` (model): a `ModelStage` (Plug.lean) whose inner cycles and functionals are
  images of integral vectors; `IntegralModelStage.cycle_integral`, `functional_bound` (PROVED, for
  every exponent `a ≥ 0`).
* `OuterSwitchStep` (model): the switch input of the outer process at a configuration: a
  Selmer-level nonquadratic step over `K_out = Frac 𝒪_∞` (Plug's `SelmerNonquadStep`, whose
  duality and detection are GLUE) with the identification of the two outer dimensions, and, on an
  outer-large set, switch coordinate data whose volume normalizations are units of `R`. Then
  `OuterSwitchStep.toSwitchField` (PROVED) gives the `switch` clause of `OuterSwitchData` (`v μ = 0`
  for unit normalizations, `v_unit_eq_zero`).
* `OuterSwitchData.ofIntegralModels` (PROVED): `OuterSwitchData` from integral model stages and outer
  switch steps; `minor_link`, `cycle_integral` and `functional_bound` are proved, the switch comes
  from `OuterSwitchStep`.
* Non-vacuity (LESSON 2): `exIntegralModelStage` (over `ℤ₂ ⊂ ℚ₂`), `exOuterOfIntegralModels`, and
  `exOuterSwitchStepInputs` (the switch-input components: `NonquadDims 3 1` and unit-normalized
  switch coordinates over `ℚ₂`).

Finding (no manuscript issue; recorded for the non-vacuity rule): for a genuine outer model built
from integral inner models with primitive integral cycles and functionals, a configuration of outer
dimension `> 1` forces `v u_j → −∞` along `𝒰` (all maximal outer minors vanish, i.e. all inner
maximal minors are infinitesimal, and `u_j Δ_j = ±α_jβ_j` with `α_j, β_j` units at a suitable
position). Since switches preserve the inner valuations and the terminal configuration bounds them
below, such configurations occur only inside Elliot's proof by contradiction (tex L4935–4964: "Suppose
no uniform lower bound exists"). Hence the genuine-model instance below has outer dimension one (the
switch clause vacuous); the switch inputs are checked for consistency separately.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open Module Matrix Filter ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Uniform.QuadraticCase
  ZInQ.Contrib.CloudB3RC53.UniformSwitch ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-! ### Primitive integral kernel vectors -/

section Primitive

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}

omit [IsDiscreteValuationRing R] in
/-- Dividing out powers of `ϖ`: an integral kernel vector some coordinate of which is not divisible
by `ϖ ^ N` is `ϖ ^ k` times an integral kernel vector some coordinate of which is not divisible by
`ϖ`. -/
theorem primitive_kernel_aux (hϖ : Irreducible ϖ) {m n : ℕ} (D : Matrix (Fin m) (Fin n) R) :
    ∀ (N : ℕ) (z : Fin n → R) (i : Fin n), D *ᵥ z = 0 → ¬ ϖ ^ N ∣ z i →
      ∃ (k : ℕ) (z' : Fin n → R), D *ᵥ z' = 0 ∧ z = ϖ ^ k • z' ∧ ∃ i', ¬ ϖ ∣ z' i' := by
  intro N
  induction N with
  | zero => intro z i _ h; exact absurd (by simp) h
  | succ N ih =>
    intro z i hz hN
    by_cases hall : ∀ i', ϖ ∣ z i'
    · choose w hw using hall
      have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
      have hzw : z = ϖ • w := funext fun i' => by rw [hw i']; rfl
      have hDw : D *ᵥ w = 0 := by
        have : ϖ • (D *ᵥ w) = 0 := by rw [← Matrix.mulVec_smul, ← hzw, hz]
        funext a
        have ha := congrFun this a
        simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at ha
        exact (mul_eq_zero.mp ha).resolve_left hϖ0
      have hwN : ¬ ϖ ^ N ∣ w i := by
        rintro ⟨c, hc⟩
        exact hN ⟨c, by rw [hw i, hc, pow_succ]; ring⟩
      obtain ⟨k, z', hz', hwz, hi'⟩ := ih w i hDw hwN
      refine ⟨k + 1, z', hz', ?_, hi'⟩
      rw [hzw, hwz, smul_smul, pow_succ, mul_comm]
    · push Not at hall
      obtain ⟨i', hi'⟩ := hall
      exact ⟨0, z, hz, by simp, i', hi'⟩

/-- **Primitive integral kernel vectors** (tex L4927–4940: "the inner kernels have primitive
vectors"). Let `R` be a DVR with uniformizer `ϖ`, `K` a field with `R → K` making `K` the fraction
field of `R`, and `D` an integral matrix. Every nonzero kernel vector `x` of `D` over `K` is a
nonzero `K`-multiple of the image of an integral kernel vector `z` of `D` some coordinate of which is
not divisible by `ϖ`. Classification: PROVED. -/
def PrimitiveKernelVector : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (m n : ℕ)
      (D : Matrix (Fin m) (Fin n) R) (x : Fin n → K),
      (D.map (algebraMap R K)) *ᵥ x = 0 → x ≠ 0 →
      ∃ (z : Fin n → R) (c : K), c ≠ 0 ∧ D *ᵥ z = 0 ∧ (∃ i, ¬ ϖ ∣ z i) ∧
        (fun i => algebraMap R K (z i)) = c • x

theorem primitiveKernelVector_proof : PrimitiveKernelVector := by
  intro R _ _ _ ϖ hϖ K _ _ _ m n D x hx hx0
  -- clear denominators
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) Finset.univ x
  choose y hy using fun i => hb i (Finset.mem_univ i)
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hyx : (fun i => algebraMap R K (y i)) = algebraMap R K (b : R) • x := by
    funext i; rw [hy i, Algebra.smul_def]; rfl
  have hDy : D *ᵥ y = 0 := by
    funext a
    apply hinj
    have : (D.map (algebraMap R K)) *ᵥ (fun i => algebraMap R K (y i)) = 0 := by
      rw [hyx, Matrix.mulVec_smul, hx, smul_zero]
    have ha := congrFun this a
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at ha
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, map_sum, map_mul, map_zero]
    exact ha
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push Not at h; exact hx0 (funext h)
  have hy0 : y i0 ≠ 0 := by
    intro h0
    have := congrFun hyx i0
    simp only [h0, map_zero, Pi.smul_apply, smul_eq_mul] at this
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hb0) hi0 this.symm
  obtain ⟨N, hN⟩ : ∃ N, ¬ ϖ ^ N ∣ y i0 := by
    by_contra h; push Not at h; exact hy0 (eq_zero_of_forall_pow_dvd hϖ h)
  obtain ⟨k, z, hz, hyz, hi⟩ := primitive_kernel_aux hϖ D N y i0 hDy hN
  have hϖk : algebraMap R K (ϖ ^ k) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero _ hϖ.ne_zero)
  refine ⟨z, (algebraMap R K (ϖ ^ k))⁻¹ * algebraMap R K (b : R),
    mul_ne_zero (inv_ne_zero hϖk) ((map_ne_zero_iff _ hinj).mpr hb0), hz, hi, ?_⟩
  funext i
  have h1 := congrFun hyx i
  rw [hyz] at h1
  simp only [Pi.smul_apply, smul_eq_mul, map_mul] at h1 ⊢
  rw [mul_assoc, ← h1, ← mul_assoc, inv_mul_cancel₀ hϖk, one_mul]

/-- **Primitive integral closed functionals** (tex L4957–4961, the functional side): every nonzero
closed functional `λ` (`λ D = 0`) of an integral square matrix over `K` is a nonzero `K`-multiple of
the image of an integral closed functional one of whose coordinates is not divisible by `ϖ`.
Classification: PROVED (from `PrimitiveKernelVector` for `Dᵀ`). -/
def PrimitiveClosedFunctional : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (n : ℕ)
      (D : Matrix (Fin n) (Fin n) R) (lam : Fin n → K),
      lam ᵥ* (D.map (algebraMap R K)) = 0 → lam ≠ 0 →
      ∃ (l : Fin n → R) (c : K), c ≠ 0 ∧ l ᵥ* D = 0 ∧ (∃ i, ¬ ϖ ∣ l i) ∧
        (fun i => algebraMap R K (l i)) = c • lam

theorem primitiveClosedFunctional_proof : PrimitiveClosedFunctional := by
  intro R _ _ _ ϖ hϖ K _ _ _ n D lam hlam hlam0
  have h1 : (Dᵀ.map (algebraMap R K)) *ᵥ lam = 0 := by
    rw [Matrix.transpose_map, Matrix.mulVec_transpose, hlam]
  obtain ⟨l, c, hc, hl, hi, hll⟩ := primitiveKernelVector_proof R ϖ hϖ K n n Dᵀ lam h1 hlam0
  exact ⟨l, c, hc, by rw [← Matrix.mulVec_transpose, hl], hi, hll⟩

end Primitive

/-! ### Integral model stages and the integrality fields -/

section Integral

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  [Fact (Irreducible ϖ)] {J : Type} (𝒰 : Ultrafilter J)
  {K : Type} [Field K] [Algebra R K] (v : AddValuation K (WithTop ℤ))

/-- **An integral model stage** (tex L4927–4961): a `ModelStage` (Plug.lean: integral inner models
`M j`, their genuine outer model in `Frac 𝒪_∞`) whose inner cycles `z_j` and closed functionals
`λ_j` are the images of integral vectors `zR j`, `lamR j` over `R` (the actual class and the paired
functional are integral, the latter with exponent `a = 0`, tex L3864–3869). -/
structure IntegralModelStage (ϖ : R) (K : Type) [Field K] [Algebra R K] where
  base : ModelStage 𝒰 ϖ K
  zR : J → Fin (base.n + 1) → R
  lamR : J → Fin (base.n + 1) → R
  hzR : ∀ j i, base.z j i = algebraMap R K (zR j i)
  hlamR : ∀ j i, base.lam j i = algebraMap R K (lamR j i)

variable {𝒰}

/-- **`cycle_integral`** (tex L4957–4961: "`α` is an integral surviving cycle coordinate"): the inner
cycles of an integral model stage have nonnegative valuation. Classification: PROVED. -/
theorem IntegralModelStage.cycle_integral (hv : IsPiAdicOn ϖ v)
    (X : IntegralModelStage 𝒰 ϖ K) (j : J) (i : Fin (X.base.toOuterStage.n + 1)) :
    (0 : WithTop ℤ) ≤ v (X.base.toOuterStage.z j i) := by
  change (0 : WithTop ℤ) ≤ v (X.base.z j i)
  exact le_of_le_of_eq (hv.nonneg (X.zR j i)) (congrArg v (X.hzR j i).symm)

/-- **`functional_bound`** (tex L4957–4961: "`β` has valuation at least `−a`"): for every exponent
`a`, the inner functionals of an integral model stage have valuation at least `−a`.
Classification: PROVED. -/
theorem IntegralModelStage.functional_bound (hv : IsPiAdicOn ϖ v)
    (X : IntegralModelStage 𝒰 ϖ K) (a : ℕ) (j : J) (i : Fin (X.base.toOuterStage.n + 1)) :
    (((-a : ℤ)) : WithTop ℤ) ≤ v (X.base.toOuterStage.lam j i) := by
  change (((-a : ℤ)) : WithTop ℤ) ≤ v (X.base.lam j i)
  refine le_trans ?_ (le_of_le_of_eq (hv.nonneg (X.lamR j i)) (congrArg v (X.hlamR j i).symm))
  exact_mod_cast (by omega : (-(a : ℤ)) ≤ 0)

omit [IsDomain R] [IsDiscreteValuationRing R] [Fact (Irreducible ϖ)] in
/-- Units of `R` have valuation zero for a `ϖ`-adic valuation. PROVED. -/
theorem v_unit_eq_zero (hv : IsPiAdicOn ϖ v) {u : R} (hu : IsUnit u) :
    v (algebraMap R K u) = 0 := by
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h1 := hv.nonneg u
  have h2 := hv.nonneg w
  have hsum : v (algebraMap R K u) + v (algebraMap R K w) = 0 := by
    rw [← AddValuation.map_mul, ← map_mul, hw, map_one, AddValuation.map_one]
  have hne : v (algebraMap R K u) ≠ ⊤ := by
    intro h; rw [h, top_add] at hsum; exact WithTop.top_ne_zero hsum
  have hne' : v (algebraMap R K w) ≠ ⊤ := by
    intro h; rw [h, add_top] at hsum; exact WithTop.top_ne_zero hsum
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hne'
  rw [← ha, ← hb] at hsum
  rw [← ha] at h1 ⊢
  rw [← hb] at h2
  have hab : a + b = 0 := by exact_mod_cast hsum
  have ha0 : 0 ≤ a := by exact_mod_cast h1
  have hb0 : 0 ≤ b := by exact_mod_cast h2
  have : a = 0 := by omega
  rw [this]; rfl

/-- **The outer switch input at a configuration** (tex L4940–4950): a Selmer-level nonquadratic
step over `K_out = Frac 𝒪_∞` (Plug's `SelmerNonquadStep`: the relaxed localization, its two sides,
duality and detection as GLUE) whose side cohomology dimensions are the outer dimensions of the old
and new configurations, and, on an outer-large set, switch coordinate data whose volume
normalizations `μ_F, μ_S` are images of units of `R` and whose finite and singular coordinates are
the old and new inner coordinates.

Caveat: the stages are not tied to the genuine fibre models; a one-stage datum of fibre dimension 1
(no switch demanded, so no `OuterSwitchStep` is required) satisfies the data built from these steps
(`exOuterOfIntegralModels`), so as a hypothesis it is equivalent to its conclusion (compare RC's
`regularityInputsS_iff`). Linking the stages to the genuine fibre models is pending. -/
structure OuterSwitchStep (S S' : OuterStage (FractionRing (OInf 𝒰 ϖ)) K J) where
  X : SelmerNonquadStep (FractionRing (OInf 𝒰 ϖ))
  hs : S.outerDim = finrank (FractionRing (OInf 𝒰 ϖ)) ((selCx X.SF.Dside).toCC.homology 1)
  hs' : S'.outerDim = finrank (FractionRing (OInf 𝒰 ϖ)) ((selCx X.SS.Dside).toCC.homology 1)
  coords : ∀ᶠ j in (𝒰 : Filter J), ∃ (Y : SwitchCoordData K) (mF mS : R),
    IsUnit mF ∧ IsUnit mS ∧ Y.μF = algebraMap R K mF ∧ Y.μS = algebraMap R K mS ∧
      S.coord j = Y.uF ∧ S'.coord j = Y.uS

/-- **The switch clause from an outer switch step** (tex L4940–4950): the outer dimension drop
(`NonquadDims` over `K_out` from the Selmer data) and the switch coordinate data with `v μ_F =
v μ_S = 0` (unit normalizations), on an outer-large set — the `switch` clause of `OuterSwitchData`
for this pair of configurations. Classification: PROVED. -/
theorem OuterSwitchStep.toSwitchField (hv : IsPiAdicOn ϖ v)
    {S S' : OuterStage (FractionRing (OInf 𝒰 ϖ)) K J} (T : OuterSwitchStep S S') :
    Nonempty (NonquadDims (k := FractionRing (OInf 𝒰 ϖ)) S.outerDim S'.outerDim) ∧
      ∀ᶠ j in (𝒰 : Filter J), ∃ Y : SwitchCoordData K,
        v Y.μF = 0 ∧ v Y.μS = 0 ∧ S.coord j = Y.uF ∧ S'.coord j = Y.uS := by
  refine ⟨⟨T.X.toNonquadDims T.hs T.hs'⟩, T.coords.mono fun j hj => ?_⟩
  obtain ⟨Y, mF, mS, hF, hS, hYF, hYS, h1, h2⟩ := hj
  exact ⟨Y, by rw [hYF]; exact v_unit_eq_zero v hv hF, by rw [hYS]; exact v_unit_eq_zero v hv hS,
    h1, h2⟩

/-- **Outer switching data from integral model stages** (tex L4927–4964): UniformSwitch's
`OuterSwitchData` in which `minor_link` (from the genuine outer model, `OuterMinors`),
`cycle_integral` and `functional_bound` (from integrality, for every exponent `a`) are PROVED; the
`switch` clause comes from outer switch steps (`OuterSwitchStep`, whose Selmer-level duality and
detection, and coordinate data, are its inputs). Classification: PROVED (from the stated inputs). -/
def OuterSwitchData.ofIntegralModels (hinj : Function.Injective (algebraMap R K))
    (hv : IsPiAdicOn ϖ v) (a : ℕ) (Stage : Type) (stage : Stage → IntegralModelStage 𝒰 ϖ K)
    (step : ∀ S, 1 < (stage S).base.toOuterStage.outerDim → ∃ S',
      Nonempty (OuterSwitchStep (stage S).base.toOuterStage (stage S').base.toOuterStage)) :
    OuterSwitchData (Kout := FractionRing (OInf 𝒰 ϖ)) v 𝒰 a :=
  OuterSwitchData.ofModels v hinj hv Stage (fun S => (stage S).base)
    (fun S j i => (stage S).cycle_integral v hv j i)
    (fun S j i => (stage S).functional_bound v hv a j i)
    (fun S hS => by
      obtain ⟨S', ⟨T⟩⟩ := step S hS
      exact ⟨S', T.toSwitchField v hv⟩)

end Integral

/-! ### Non-vacuity (LESSON 2) -/

section Examples

/-- **An integral model stage** over `R = ℤ₂`, `K = ℚ₂`: `exModelStage` (inner models
`[ℤ₂ --0--> ℤ₂]`, cycle and functional `1`), with integral cycle and functional `1`. -/
noncomputable def exIntegralModelStage (𝒰 : Ultrafilter ℕ) :
    IntegralModelStage 𝒰 (2 : ℤ_[2]) ℚ_[2] where
  base := exModelStage 𝒰
  zR := fun _ _ => 1
  lamR := fun _ _ => 1
  hzR := fun _ _ => by simp [exModelStage]
  hlamR := fun _ _ => by simp [exModelStage]

/-- **`OuterSwitchData.ofIntegralModels` is inhabited** (genuine outer model of integral inner
models over `ℤ₂ ⊂ ℚ₂`; outer dimension one, so the switch clause is vacuous — see the module
docstring for why a genuine switch-exercising instance cannot exist outside the contradiction
hypothesis). -/
noncomputable def exOuterOfIntegralModels (𝒰 : Ultrafilter ℕ) :
    OuterSwitchData (Kout := FractionRing (OInf 𝒰 (2 : ℤ_[2]))) (Padic.addValuation (p := 2)) 𝒰 0 :=
  OuterSwitchData.ofIntegralModels (Padic.addValuation (p := 2)) Subtype.coe_injective
    isPiAdicOn_padic 0 Unit (fun _ => exIntegralModelStage 𝒰)
    (fun _ hs => by
      change 1 < (exModelStage 𝒰).toOuterStage.outerDim at hs
      rw [exModelStage_outerDim] at hs; exact absurd hs (lt_irrefl 1))

/-- **The components of an outer switch step are jointly satisfiable**: a `NonquadDims 3 1`
(the dimension drop of a switch) and switch coordinate data whose volume normalizations `μ_F = 1`,
`μ_S = −1` are images of units (here of `ℤ` in `ℚ`, `exSwitchCoordData`), with coordinates
`u_F = 1`, `u_S = 1`. -/
theorem exOuterSwitchStepInputs :
    Nonempty (NonquadDims (k := ℚ) 3 1) ∧
      ∃ (Y : SwitchCoordData ℚ) (mF mS : ℤ), IsUnit mF ∧ IsUnit mS ∧
        Y.μF = algebraMap ℤ ℚ mF ∧ Y.μS = algebraMap ℤ ℚ mS ∧ Y.uF = 1 ∧ Y.uS = 1 := by
  refine ⟨⟨exNonquadDims⟩, exSwitchCoordData 1 (-1), 1, -1, isUnit_one, isUnit_one.neg,
    by simp [exSwitchCoordData], by simp [exSwitchCoordData], exSwitchCoordData_uF 1 (-1), ?_⟩
  rw [exSwitchCoordData_uS, neg_neg]

end Examples

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
