import ZInQKernel.Contrib.CloudB3RC53.UniformSwitch.Regularity

/-!
# RC53 UniformSwitch: the primitive kernel vector, separate from the actual class

Proposition `ex:limits-uniform-lower-bound`, paragraph "Height-one regularity, including quadratic
specializations", tex 4983–4995, 5145–5157.

The text separates two vectors in `ker d` of the two-term model `C = [R^s --d--> R^s]` over the DVR
`R = Λ_𝔭`:

* a **primitive kernel vector** `v` (tex 4987–4990: "Choose a primitive vector `v ∈ ker d`. Such a
  vector exists because `ker d` is saturated in `R^s`: divide a nonzero kernel vector by its
  largest common power of a uniformizer. Thus `v̄ ≠ 0` in `V = H¹(C ⊗ k)` and `dim_k V = s ≥ 1`");
* the **actual class** `z`, "a nonzero fraction-field multiple of `v`" (tex 4991). The vector `v` is
  used only to select the switching prime (switches nonzero on `v̄`, so the generic localization
  of `z` is nonzero, tex 4992–4995); "we do not replace the actual class by the chosen primitive
  vector" (tex 5145–5147); the fibre dimension is at least one because the generic kernel "has a
  primitive integral vector" (tex 5154–5157).

`HeightOneSwitchData.primitive` (`Regularity.lean`) instead asks that the actual class itself be
primitive, `∃ i, ρ (z i) ≠ 0`. That is stronger than the text: the stage `[A --0--> A]` with
`z = w = ϖ` has fibre dimension one and a nonzero generic class, but `z̄ = 0`
(`peerStage_not_primitive`). In `toProcess` the field is used only for `pos` (fibre dimension
`≥ 1`). This file gives the text-faithful variant, additively:

* `PrimitiveKernelVector S ρ`: a kernel vector `v` of the stage's model with `v̄ ≠ 0`, and the
  relation `ι ∘ z = c · ι ∘ v` with `c ≠ 0` in the fraction field;
* `one_le_fiberDim_of_primitiveKernel`: `pos` from `v` (tex 5154–5157);
* `exists_primitiveKernelVector`: over a DVR the primitive kernel vector EXISTS as soon as the
  actual class is nonzero (saturation of `ker d`, tex 4988–4989): `z = ϖ^m v` with
  `span{z_i} = (ϖ^m)`;
* `localization_ne_zero_of_primitiveKernel`: a localization (any `R`-matrix `L`) that is nonzero
  on `v̄` is generically nonzero on the actual class `z` (tex 4992–4995);
* `HeightOneSwitchDataPK` (the switching data with `primitiveKernel` in place of `primitive`),
  `HeightOneSwitchDataPK.toProcess`, `regular_of_switchDataPK`, `processAtPrimePK`: the regularity
  conclusion re-derived; `HeightOneSwitchData.toPK`: the old data give the new (`v = z`, `c = 1`);
* nodes `PrimitiveKernelExists`, `RegularityFromPrimitiveKernel` (PROVED);
* Non-vacuity: the stage `[ℚ⟦X⟧ --0--> ℚ⟦X⟧]` with `z = w = X` (`peerStage`), which the new form
  admits (`v = 1`, `c = X`) and the old field rejects; `peerSwitchDataPK` and its regular terminal
  coordinate `X²`.

**Classification.** Definitions and PROVED statements (the switch fields remain the GLUE inputs of
`HeightOneSwitchData`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.UniformSwitch

open Matrix Module ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.Uniform.QuadraticCase
  ZInQ.Manuscript.RC.Central

section Vector

variable {A F k : Type*} [CommRing A] [Field F] [Field k]

/-- **A primitive kernel vector for a stage** (tex 4987–4991): `v ∈ ker D` with `v̄ ≠ 0`, and the
actual class `z` a nonzero fraction-field multiple of `v`, `ι ∘ z = c · ι ∘ v`, `c ≠ 0`. -/
structure PrimitiveKernelVector {ι : A →+* F} (S : TwoTermStage ι) (ρ : A →+* k) where
  v : Fin (S.n + 1) → A
  hv : S.D *ᵥ v = 0
  hprim : ∃ i, ρ (v i) ≠ 0
  c : F
  hc : c ≠ 0
  hzv : ∀ i, ι (S.z i) = c * ι (v i)

/-- **`pos` from the primitive kernel vector** (tex 4989–4990, 5154–5157): `v̄ ≠ 0` lies in
`ker(D ⊗ k)`, so the fibre dimension is at least one. PROVED. -/
theorem one_le_fiberDim_of_primitiveKernel {ι : A →+* F} {S : TwoTermStage ι} {ρ : A →+* k}
    (P : PrimitiveKernelVector S ρ) : 1 ≤ S.fiberDim ρ := by
  obtain ⟨i, hi⟩ := P.hprim
  have hmem : (fun j => ρ (P.v j)) ∈ LinearMap.ker (S.D.map ρ).mulVecLin := by
    rw [LinearMap.mem_ker, mulVecLin_apply]
    ext j
    have := congrFun P.hv j
    simp only [mulVec, dotProduct, map_apply, Pi.zero_apply] at this ⊢
    rw [← map_zero ρ, ← this, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_mul]
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  have hbot := Submodule.finrank_eq_zero.mp h0
  rw [hbot, Submodule.mem_bot] at hmem
  exact hi (congrFun hmem i)

/-- **Switches selected by `v̄` see the actual class generically** (tex 4992–4995): if an
`R`-linear localization `L` is nonzero on `v̄`, then `L ⊗ F` is nonzero on the actual class.
PROVED. -/
theorem localization_ne_zero_of_primitiveKernel {ι : A →+* F} {S : TwoTermStage ι} {ρ : A →+* k}
    (hι : Function.Injective ι) (P : PrimitiveKernelVector S ρ) {m : Type*} [Fintype m]
    (L : Matrix m (Fin (S.n + 1)) A)
    (hL : (L.map ρ) *ᵥ (fun i => ρ (P.v i)) ≠ 0) :
    (L.map ι) *ᵥ (fun i => ι (S.z i)) ≠ 0 := by
  have hρ : (L.map ρ) *ᵥ (fun i => ρ (P.v i)) = fun j => ρ ((L *ᵥ P.v) j) := by
    ext j; simp [mulVec, dotProduct, map_sum]
  have hzι : (L.map ι) *ᵥ (fun i => ι (S.z i)) = fun j => P.c * ι ((L *ᵥ P.v) j) := by
    ext j
    simp only [mulVec, dotProduct, map_apply, P.hzv, map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hzι]
  intro h0
  apply hL
  rw [hρ]
  ext j
  have hj := congrFun h0 j
  simp only [Pi.zero_apply, mul_eq_zero, P.hc, false_or] at hj
  rw [(map_eq_zero_iff ι hι).mp hj, map_zero, Pi.zero_apply]

/-- The old field gives a primitive kernel vector (`v = z`, `c = 1`): the new form is weaker.
PROVED. -/
def primitiveKernelVector_of_primitive {ι : A →+* F} (S : TwoTermStage ι) (ρ : A →+* k)
    (h : ∃ i, ρ (S.z i) ≠ 0) : PrimitiveKernelVector S ρ where
  v := S.z
  hv := S.hz
  hprim := h
  c := 1
  hc := one_ne_zero
  hzv _ := (one_mul _).symm

end Vector

section DVR

variable {A F k : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F] [Field k]

/-- **The primitive kernel vector exists over a DVR** (tex 4988–4989: "`ker d` is saturated in
`R^s`: divide a nonzero kernel vector by its largest common power of a uniformizer"): if the actual
class `z` is nonzero, then `span{z_i} = (ϖ^m)`, `z = ϖ^m v`, some `v_i` is a unit (so `v̄ ≠ 0`),
`D v = 0`, and `c = ι(ϖ^m) ≠ 0`. PROVED. -/
theorem exists_primitiveKernelVector {ι : A →+* F} (hι : Function.Injective ι) (ρ : A →+* k)
    (S : TwoTermStage ι) (hz : ∃ i, S.z i ≠ 0) : Nonempty (PrimitiveKernelVector S ρ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hI : Ideal.span (Set.range S.z) ≠ ⊥ := by
    obtain ⟨i, hi⟩ := hz
    intro h
    have hmem : S.z i ∈ Ideal.span (Set.range S.z) := Ideal.subset_span ⟨i, rfl⟩
    rw [h, Ideal.mem_bot] at hmem
    exact hi hmem
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have hdiv : ∀ i, ∃ a, a * ϖ ^ m = S.z i := fun i => by
    have h : S.z i ∈ Ideal.span (Set.range S.z) := Ideal.subset_span ⟨i, rfl⟩
    rw [hm] at h
    exact Ideal.mem_span_singleton'.mp h
  choose v hv using hdiv
  have hϖm : ϖ ^ m ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have hmem : ϖ ^ m ∈ Ideal.span (Set.range S.z) := by
    rw [hm]; exact Ideal.subset_span rfl
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hmem
  have hsum : ∑ i, c i * v i = 1 := by
    apply mul_right_cancel₀ hϖm
    rw [one_mul, Finset.sum_mul]
    conv_rhs => rw [← hc]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul, ← hv i, mul_assoc]
  have hprim : ∃ i, IsUnit (v i) := by
    by_contra hne
    push Not at hne
    have h1 : ∑ i, c i * v i ∈ IsLocalRing.maximalIdeal A :=
      Ideal.sum_mem _ fun i _ =>
        Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hne i)))
    rw [hsum] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨i₀, hi₀⟩ := hprim
  have hDv : S.D *ᵥ v = 0 := by
    ext j
    have h := congrFun S.hz j
    have h' : ϖ ^ m * (S.D *ᵥ v) j = 0 := by
      rw [Pi.zero_apply] at h
      rw [← h]
      simp only [mulVec, dotProduct, Finset.mul_sum, ← hv]
      exact Finset.sum_congr rfl fun _ _ => by ring
    exact (mul_eq_zero.mp h').resolve_left hϖm
  exact ⟨⟨v, hDv, ⟨i₀, (hi₀.map ρ).ne_zero⟩, ι (ϖ ^ m), (map_ne_zero_iff ι hι).mpr hϖm,
    fun i => by rw [← hv i, map_mul, mul_comm]⟩⟩

end DVR

/-! ### The switching data with a primitive kernel vector -/

section Process

variable {A F k : Type*} [CommRing A] [Field F] [Field k]

/-- **The height-one switching data, text-faithful form** (tex 4976–5193): `HeightOneSwitchData`
with the field `primitive` (the actual class itself primitive) replaced by `primitiveKernel`: each
stage has a primitive kernel vector `v`, of which the actual class is a nonzero fraction-field
multiple (tex 4987–4991, 5145–5157). The other fields are those of `HeightOneSwitchData`
(GLUE inputs carrying the hypotheses of RC16's cores). -/
structure HeightOneSwitchDataPK (ι : A →+* F) (ρ : A →+* k) where
  Stage : Type
  stage : Stage → TwoTermStage ι
  /-- Whether the specialization is quadratic (`𝔭 = (t)` or `(t+2)`). -/
  quadratic : Prop
  sp : Stage → ℕ
  sm : Stage → ℕ
  /-- GLUE (tex 5035–5054): the sign decomposition `H¹(C ⊗ k) = V₊ ⊕ V₋` at a quadratic prime. -/
  sign_sum : quadratic → ∀ S, sp S + sm S = (stage S).fiberDim ρ
  /-- tex 4987–4991, 5154–5157: a primitive kernel vector, the actual class a nonzero
  fraction-field multiple of it. -/
  primitiveKernel : ∀ S, Nonempty (PrimitiveKernelVector (stage S) ρ)
  /-- GLUE inputs for a switch when both signs occur (or nonquadratic), tex 4997–5003, 5116–5122,
  5137–5153. -/
  switch_mixed : ∀ S, (¬ quadratic ∨ (0 < sp S ∧ 0 < sm S)) → 1 < (stage S).fiberDim ρ →
    ∃ S', Nonempty (CoordStep ι (stage S).u (stage S').u) ∧
      (quadratic → Nonempty (QuadMixedDims (k := k) (sp S) (sm S) (sp S') (sm S'))) ∧
      (¬ quadratic →
        Nonempty (NonquadDims (k := k) ((stage S).fiberDim ρ) ((stage S').fiberDim ρ)))
  /-- GLUE inputs for a switch when one sign only occurs, tex 5123–5136, 5137–5153. -/
  switch_single : ∀ S, quadratic → ¬ (0 < sp S ∧ 0 < sm S) → 1 < (stage S).fiberDim ρ →
    ∃ S' a b, Nonempty (CoordStep ι (stage S).u (stage S').u) ∧
      Nonempty (QuadSingleDims (k := k) ((stage S).fiberDim ρ) a b) ∧
      ((sp S' = a ∧ sm S' = b) ∨ (sp S' = b ∧ sm S' = a))

/-- **The old data give the new**: `primitive` yields `primitiveKernel` with `v = z`, `c = 1`.
PROVED. -/
def HeightOneSwitchData.toPK {ι : A →+* F} {ρ : A →+* k} (P : HeightOneSwitchData ι ρ) :
    HeightOneSwitchDataPK ι ρ where
  Stage := P.Stage
  stage := P.stage
  quadratic := P.quadratic
  sp := P.sp
  sm := P.sm
  sign_sum := P.sign_sum
  primitiveKernel S := ⟨primitiveKernelVector_of_primitive _ ρ (P.primitive S)⟩
  switch_mixed := P.switch_mixed
  switch_single := P.switch_single

/-- **The instance of RC16's `RegularitySwitchProcess`** from the text-faithful switching data
(tex 4976–5193): as `HeightOneSwitchData.toProcess`, with `pos` from the primitive kernel vector
(`one_le_fiberDim_of_primitiveKernel`). PROVED. -/
def HeightOneSwitchDataPK.toProcess [IsLocalRing A] {ι : A →+* F} (hι : Function.Injective ι)
    {ρ : A →+* k} (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) (Reg : F → Prop)
    (hReg : ∀ a : A, Reg (ι a)) (P : HeightOneSwitchDataPK ι ρ) : RegularitySwitchProcess Reg where
  Stage := P.Stage
  fiberDim S := (P.stage S).fiberDim ρ
  mixed S := ¬ P.quadratic ∨ (0 < P.sp S ∧ 0 < P.sm S)
  coord S := (P.stage S).u
  pos S := one_le_fiberDim_of_primitiveKernel (P.primitiveKernel S).some
  switch_mixed S hmix hs := by
    obtain ⟨S', ⟨hC⟩, hQ, hN⟩ := P.switch_mixed S hmix hs
    obtain ⟨c, hc⟩ := hC.relation
    refine ⟨S', ?_, ι c, hReg c, hc⟩
    by_cases hq : P.quadratic
    · obtain ⟨Q⟩ := hQ hq
      have h := Q.drop
      rw [P.sign_sum hq S, P.sign_sum hq S'] at h
      exact h
    · obtain ⟨N⟩ := hN hq
      exact N.drop
  switch_single S hmix hs := by
    have hq : P.quadratic := by
      by_contra hq; exact hmix (Or.inl hq)
    have hns : ¬ (0 < P.sp S ∧ 0 < P.sm S) := fun h => hmix (Or.inr h)
    obtain ⟨S', a, b, ⟨hC⟩, ⟨hQ⟩, hab⟩ := P.switch_single S hq hns hs
    obtain ⟨c, hc⟩ := hC.relation
    obtain ⟨hsum, ha, hb⟩ := hQ.result
    refine ⟨S', ?_, Or.inr ?_, ι c, hReg c, hc⟩
    · rw [← P.sign_sum hq S']
      rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    · rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  terminal S h1 := by
    obtain ⟨u₀, hu₀⟩ := (P.stage S).coord_integral_of_fiberDim_one hι ρ hρ h1
    rw [← hu₀]; exact hReg u₀

/-- **Regularity of every stage coordinate** from the text-faithful switching data (tex
5154–5193). PROVED. -/
theorem regular_of_switchDataPK [IsLocalRing A] {ι : A →+* F} (hι : Function.Injective ι)
    {ρ : A →+* k} (hρ : ∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0)
    (P : HeightOneSwitchDataPK ι ρ) (S : P.Stage) : ∃ a : A, ι a = (P.stage S).u :=
  regular_of_switchProcess (Reg := fun x : F => ∃ a : A, ι a = x)
    (fun x y ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, by rw [map_mul, ha, hb]⟩)
    (P.toProcess hι hρ (fun x => ∃ a : A, ι a = x) (fun a => ⟨a, rfl⟩)) S

end Process

section Genuine

variable (P : Ideal Lambda) [P.IsPrime]

/-- **The height-one switching process over the genuine `Λ_𝔭`** from the text-faithful switching
data, as an instance of RC16's `RegularitySwitchProcess (RegularAtPrime 𝔭)`. PROVED (from the
GLUE switch inputs). -/
def processAtPrimePK (D : HeightOneSwitchDataPK (toFracAt P)
    (IsLocalRing.residue (Localization.AtPrime P))) : RegularitySwitchProcess (RegularAtPrime P) :=
  D.toProcess (toFracAt_injective P) (fun _ hx => (IsLocalRing.residue_eq_zero_iff _).2 hx)
    (RegularAtPrime P) (fun a => ⟨a, rfl⟩)

/-- **The input shape of RC16's `mem_lambdaHalf_of_regularity`** from the text-faithful switching
data. PROVED. -/
theorem exists_process_of_switchDataPK (u : FractionRing Lambda)
    (D : HeightOneSwitchDataPK (toFracAt P) (IsLocalRing.residue (Localization.AtPrime P)))
    (S₀ : D.Stage) (hS₀ : (D.stage S₀).u = u) :
    ∃ (Pr : RegularitySwitchProcess (RegularAtPrime P)) (S₀ : Pr.Stage), Pr.coord S₀ = u :=
  ⟨processAtPrimePK P D, S₀, hS₀⟩

end Genuine

/-! ### Nodes -/

section Nodes

/-- **Node: the primitive kernel vector exists** (tex 4987–4991). Claim: over a DVR `R` with
injective fraction-field map `ι` and any residue map `ρ : R → k`, every two-term stage whose actual
class `z` is nonzero has a primitive kernel vector `v` (`D v = 0`, `v̄ ≠ 0`) with `ι ∘ z = c · ι ∘ v`,
`c ≠ 0`. Kind: PROVED (`primitiveKernelExists_proof`). -/
def PrimitiveKernelExists : Prop :=
  ∀ (A F k : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field F] [Field k]
    (ι : A →+* F), Function.Injective ι → ∀ (ρ : A →+* k) (S : TwoTermStage ι),
    (∃ i, S.z i ≠ 0) → Nonempty (PrimitiveKernelVector S ρ)

theorem primitiveKernelExists_proof : PrimitiveKernelExists := by
  intro A F k _ _ _ _ _ ι hι ρ S hz
  exact exists_primitiveKernelVector hι ρ S hz

/-- **Node: height-one regularity from the text-faithful switching data** (tex 4976–5193). Claim:
over a local ring `R` with injective `ι : R → F` and a residue map `ρ` vanishing on the maximal
ideal, for switching data whose stages carry a primitive kernel vector (the actual class a nonzero
fraction-field multiple of it, not itself primitive), every stage coordinate lies in `ι(R)`. Kind:
PROVED (`regularityFromPrimitiveKernel_proof`); the switch fields are the GLUE inputs of
`HeightOneSwitchData`; Non-vacuity: `peerSwitchDataPK`. -/
def RegularityFromPrimitiveKernel : Prop :=
  ∀ (A F k : Type) [CommRing A] [IsLocalRing A] [Field F] [Field k] (ι : A →+* F),
    Function.Injective ι → ∀ (ρ : A →+* k), (∀ x ∈ IsLocalRing.maximalIdeal A, ρ x = 0) →
    ∀ (P : HeightOneSwitchDataPK ι ρ) (S : P.Stage), ∃ a : A, ι a = (P.stage S).u

theorem regularityFromPrimitiveKernel_proof : RegularityFromPrimitiveKernel := by
  intro A F k _ _ _ _ ι hι ρ hρ P S
  exact regular_of_switchDataPK hι hρ P S

end Nodes

/-! ### Non-vacuity: the stage `[A --0--> A]` with `z = w = ϖ` -/

section Example

/-- The fraction-field embedding of `ℚ⟦X⟧` (a DVR with uniformizer `X`). -/
abbrev psι : PowerSeries ℚ →+* FractionRing (PowerSeries ℚ) :=
  algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))

/-- The residue map `ℚ⟦X⟧ → ℚ` (constant coefficient). -/
abbrev psρ : PowerSeries ℚ →+* ℚ := PowerSeries.constantCoeff

theorem psι_injective : Function.Injective psι :=
  IsFractionRing.injective (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))

theorem psρ_maximalIdeal : ∀ x ∈ IsLocalRing.maximalIdeal (PowerSeries ℚ), psρ x = 0 := by
  intro x hx
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
    isUnit_iff_ne_zero, not_not] at hx
  exact hx

/-- **The peer's stage** `[ℚ⟦X⟧ --0--> ℚ⟦X⟧]` with actual class `z = X`, functional `w = X` and
coordinate `u = X²` (`z wᵀ = u · adj 0`, `adj` of a `1 × 1` matrix being `1`). -/
def peerStage : TwoTermStage psι where
  n := 0
  D := 0
  z := fun _ => PowerSeries.X
  w := fun _ => PowerSeries.X
  u := psι (PowerSeries.X ^ 2)
  hz := by simp
  hw := by simp
  hu := by
    unfold IsClassFunctionalCoord
    rw [adjugate_fin_one]
    ext i j; fin_cases i; fin_cases j; simp [vecMulVec, pow_two]

theorem peerStage_fiberDim : peerStage.fiberDim psρ = 1 := by
  have hD : peerStage.D.map psρ = 0 := by
    change (0 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ)).map psρ = 0
    exact Matrix.map_zero _ (map_zero psρ)
  have h0 : (peerStage.D.map psρ).mulVecLin = 0 := by
    rw [hD]
    apply LinearMap.ext; intro v
    simp
  rw [TwoTermStage.fiberDim, h0, LinearMap.ker_zero, finrank_top, finrank_fin_fun]; rfl

/-- **The old field fails at the peer's stage**: the actual class reduces to `0`. PROVED. -/
theorem peerStage_not_primitive : ¬ ∃ i, psρ (peerStage.z i) ≠ 0 := by
  rintro ⟨i, hi⟩
  exact hi (by simp [peerStage])

/-- **The new form admits the peer's stage**: `v = 1`, `z = X · v`. PROVED. -/
def peerPrimitiveKernel : PrimitiveKernelVector peerStage psρ where
  v := fun _ => 1
  hv := by
    change (0 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ)) *ᵥ _ = 0
    exact Matrix.zero_mulVec _
  hprim := ⟨0, by simp⟩
  c := psι PowerSeries.X
  hc := (map_ne_zero_iff psι psι_injective).mpr PowerSeries.X_ne_zero
  hzv _ := by simp [peerStage]

/-- The same vector from the saturation argument over the DVR `ℚ⟦X⟧` (`z = X ≠ 0`). PROVED. -/
theorem peerPrimitiveKernel_of_dvr : Nonempty (PrimitiveKernelVector peerStage psρ) :=
  exists_primitiveKernelVector psι_injective psρ peerStage ⟨0, PowerSeries.X_ne_zero⟩

/-- **Non-vacuity of `HeightOneSwitchDataPK`** at a stage the old `HeightOneSwitchData` rejects:
the peer's stage alone (fibre dimension one, nonquadratic). PROVED. -/
def peerSwitchDataPK : HeightOneSwitchDataPK psι psρ where
  Stage := Unit
  stage _ := peerStage
  quadratic := False
  sp _ := 0
  sm _ := 0
  sign_sum h := h.elim
  primitiveKernel _ := ⟨peerPrimitiveKernel⟩
  switch_mixed _ _ hs := by rw [peerStage_fiberDim] at hs; omega
  switch_single _ h := h.elim

/-- The regularity conclusion at the peer's data: the coordinate `X²` is integral. PROVED. -/
theorem peerSwitchDataPK_regular :
    ∃ a : PowerSeries ℚ, psι a = (peerSwitchDataPK.stage ()).u :=
  regular_of_switchDataPK psι_injective psρ_maximalIdeal peerSwitchDataPK ()

end Example

end ZInQ.Contrib.CloudB3RC53.UniformSwitch
