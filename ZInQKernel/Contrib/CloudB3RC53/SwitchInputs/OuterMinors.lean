import ZInQKernel.Contrib.OneProof.RC.Limits.OuterDVR
import ZInQKernel.Contrib.OneProof.RC.Uniform.OuterContradiction

/-!
# RC53 SwitchInputs: the outer minors are the classes of the inner minors

Proposition `ex:limits-uniform-lower-bound`, proof, tex L4935–4964, with the outer ring (5.3)
of Lemma `ex:limits-outer-evaluation`, tex L4706–4714:

> At terminal outer dimension one a maximal boundary minor `Δ` is nonzero. Its inner minors have
> one finite valuation `b` on an outer-large set.

The outer model is the entrywise image of the inner integral models in `𝒪_∞ = (∏_𝒰 𝒪_j)/(…)` and
in its fraction field. This file derives, from that genuine construction, the GLUE field
`minor_link` of the outer switching data (`UniformSwitch/Outer.lean`, `OuterSwitchData.minor_link`,
in its round-3 shape: a nonzero outer minor gives inner minors at a position that are nonzero on an
outer-large set, integral and not outer-negligible).

Setup. `R` is a DVR with uniformizer `ϖ` (Elliot's `𝒪`, uniformizer `2`), `K` a field containing
`R` (`algebraMap R K` injective; in the text `K = Frac 𝒪`), `v : AddValuation K (WithTop ℤ)` the
`ϖ`-adic valuation on the image of `R`, characterized by `hv : (n : ℤ) ≤ v (r) ↔ ϖ ^ n ∣ r` for
`r ∈ R`, `n ∈ ℕ`. The inner models are integral matrices `M j` over `R`, viewed over `K`; the outer
model is `outerMatrix U ϖ M` (RC6) viewed over `Frac 𝒪_∞`.

Nodes (PROVED):
* `outerMatrix_minor` (tex L4732): every minor of the outer model is the class of the inner minors
  at the same position.
* `outerMinor_ne_zero_iff` (tex L4724–4727): a minor of the outer model over `Frac 𝒪_∞` is nonzero
  iff the sequence of inner minors is not infinitesimal.
* `outerNegligible_iff_mem_infinitesimals` (tex L4706–4714, L4724): RC16's `OuterNegligible v 𝒰`
  for the images in `K` is RC6's `infinitesimals U ϖ`.
* `MinorLinkEventually` (tex L4957–4959): a nonzero outer minor gives inner minors at the same
  position that are integral, nonzero on an outer-large set, and not outer-negligible. This is the
  content of the round-3 field `minor_link` (Elliot: "Its inner minors have one finite valuation
  `b` on an outer-large set"); `SwitchInputs/Plug.lean` (`ModelStage.minorLink`) uses it directly.
* `MinorLinkRestricted`: a stronger optional form, kept for reference. After restricting the
  instances to an outer-large set (with the restricted ultrafilter), the inner minors are nonzero at
  every instance. It was the workaround for the pre-round-3 shape `∀ j, minor_j ≠ 0` of
  `minor_link`, which a minor sequence vanishing on a `𝒰`-small set does not satisfy; the round-3
  field no longer needs it.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.SwitchInputs

open Matrix Filter ZInQ.Manuscript.RC.Limits ZInQ.Manuscript.RC.Uniform

section Minors

variable {R : Type*} [CommRing R] {ι : Type*} (U : Ultrafilter ι) (ϖ : R) {n : ℕ}

/-- The determinant of a matrix of sequences, evaluated at `j`, is the determinant at `j`. -/
theorem det_seqMatrix_apply {m : Type*} [Fintype m] [DecidableEq m] (M : ι → Matrix m m R)
    (j : ι) : (seqMatrix M).det j = (M j).det := by
  have h := RingHom.map_det (Pi.evalRingHom (fun _ : ι => R) j) (seqMatrix M)
  rw [RingHom.mapMatrix_apply] at h
  rw [show (seqMatrix M).det j = Pi.evalRingHom (fun _ : ι => R) j (seqMatrix M).det from rfl, h]
  congr 1

/-- **The outer minors are the classes of the inner minors** (tex L4732: integral matrices pass
to (5.3); applied to minors). Classification: PROVED. -/
theorem outerMatrix_minor {m p : Type*} [Fintype p] [DecidableEq p] (M : ι → Matrix m m R)
    (r c : p → m) :
    ((outerMatrix U ϖ M).submatrix r c).det =
      toOInf U ϖ (fun j => ((M j).submatrix r c).det) := by
  rw [outerMatrix_eq_map, submatrix_map]
  have h := RingHom.map_det (toOInf U ϖ) ((seqMatrix M).submatrix r c)
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  congr 1
  funext j
  have := det_seqMatrix_apply (fun j => (M j).submatrix r c) j
  rw [← this]
  rfl

end Minors

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  [Fact (Irreducible ϖ)] {ι : Type*} (U : Ultrafilter ι)

/-- **A minor of the outer model over `Frac 𝒪_∞` is nonzero iff the inner minors are not
infinitesimal** (tex L4724–4727). Classification: PROVED. -/
theorem outerMinor_ne_zero_iff {m p : Type*} [Fintype p] [DecidableEq p] (M : ι → Matrix m m R)
    (r c : p → m) :
    (((outerMatrix U ϖ M).map (algebraMap (OInf U ϖ) (FractionRing (OInf U ϖ)))).submatrix
        r c).det ≠ 0 ↔
      (fun j => ((M j).submatrix r c).det) ∉ infinitesimals U ϖ := by
  rw [submatrix_map]
  have h := RingHom.map_det (algebraMap (OInf U ϖ) (FractionRing (OInf U ϖ)))
    ((outerMatrix U ϖ M).submatrix r c)
  rw [RingHom.mapMatrix_apply] at h
  have hinj := IsFractionRing.injective (OInf U ϖ) (FractionRing (OInf U ϖ))
  rw [← h, outerMatrix_minor, Ne,
    ← (algebraMap (OInf U ϖ) (FractionRing (OInf U ϖ))).map_zero, hinj.eq_iff, toOInf_eq_zero_iff]

end DVR

section Valuation

variable {R : Type*} [CommRing R] {ϖ : R} {ι : Type*} (U : Ultrafilter ι)
  {K : Type*} [Field K] [Algebra R K] (v : AddValuation K (WithTop ℤ))

/-- `v` is the `ϖ`-adic valuation on the image of `R`: `n ≤ v r ↔ ϖ ^ n ∣ r`. -/
def IsPiAdicOn (ϖ : R) (v : AddValuation K (WithTop ℤ)) : Prop :=
  ∀ (r : R) (n : ℕ), (((n : ℤ)) : WithTop ℤ) ≤ v (algebraMap R K r) ↔ ϖ ^ n ∣ r

theorem IsPiAdicOn.nonneg {v : AddValuation K (WithTop ℤ)} (hv : IsPiAdicOn ϖ v) (r : R) :
    (0 : WithTop ℤ) ≤ v (algebraMap R K r) := by
  have := (hv r 0).mpr (by simp)
  simpa using this

/-- **RC16's outer negligibility is RC6's infinitesimality** (tex L4706–4714, L4724): for integral
sequences, `OuterNegligible v 𝒰 (x_j)` holds iff `(x_j) ∈ infinitesimals U ϖ`.
Classification: PROVED. -/
theorem outerNegligible_iff_mem_infinitesimals (hv : IsPiAdicOn ϖ v) (x : ι → R) :
    OuterNegligible v U (fun j => algebraMap R K (x j)) ↔ x ∈ infinitesimals U ϖ := by
  constructor
  · intro h n
    filter_upwards [h n] with j hj
    exact (hv (x j) n).mp hj
  · intro h N
    rcases le_or_gt N 0 with hN | hN
    · exact Eventually.of_forall fun j =>
        le_trans (by exact_mod_cast hN) (hv.nonneg (x j))
    · filter_upwards [h N.toNat] with j hj
      have := (hv (x j) N.toNat).mpr hj
      rwa [Int.toNat_of_nonneg hN.le] at this

end Valuation

section Link

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  [Fact (Irreducible ϖ)] {ι : Type*} (U : Ultrafilter ι)
  {K : Type*} [Field K] [Algebra R K] (v : AddValuation K (WithTop ℤ))

/-- A non-infinitesimal sequence is nonzero on an outer-large set. -/
theorem eventually_ne_zero_of_not_mem {x : ι → R} (hx : x ∉ infinitesimals U ϖ) :
    ∀ᶠ j in (U : Filter ι), x j ≠ 0 := by
  rcases Ultrafilter.eventually_or.mp (Eventually.of_forall fun j => em (x j = 0) :
      ∀ᶠ j in (U : Filter ι), x j = 0 ∨ ¬ x j = 0) with h | h
  · exact absurd (mem_infinitesimals_of_eventually_eq_zero U ϖ h) hx
  · exact h

/-- **Minor link, eventual form** (tex L4957–4959: "a maximal boundary minor `Δ` is nonzero. Its
inner minors have one finite valuation `b` on an outer-large set"). For integral inner models
`M j` with outer model `outerMatrix U ϖ M` over `Frac 𝒪_∞`: if a maximal minor of the outer model is
nonzero, the inner minors at the same position (viewed in `K`) are integral, nonzero on an
outer-large set, and not outer-negligible: the content of the round-3 field `OuterSwitchData.minor_link`
(`UniformSwitch/Outer.lean`). Classification: PROVED. -/
def MinorLinkEventually : Prop :=
  ∀ (n : ℕ) (M : ι → Matrix (Fin (n + 1)) (Fin (n + 1)) R), Function.Injective (algebraMap R K) →
    IsPiAdicOn ϖ v →
    ∀ k0 j0 : Fin (n + 1),
      (((outerMatrix U ϖ M).map (algebraMap (OInf U ϖ) (FractionRing (OInf U ϖ)))).submatrix
        k0.succAbove j0.succAbove).det ≠ 0 →
      (∀ᶠ j in (U : Filter ι),
        (((M j).map (algebraMap R K)).submatrix k0.succAbove j0.succAbove).det ≠ 0) ∧
      (∀ j, (0 : WithTop ℤ) ≤
        v ((((M j).map (algebraMap R K)).submatrix k0.succAbove j0.succAbove).det)) ∧
      ¬ OuterNegligible v U
        (fun j => (((M j).map (algebraMap R K)).submatrix k0.succAbove j0.succAbove).det)

/-- The inner minor over `K` is the image of the integral minor. -/
theorem minor_map {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (k0 j0 : Fin (n + 1)) :
    ((M.map (algebraMap R K)).submatrix k0.succAbove j0.succAbove).det =
      algebraMap R K ((M.submatrix k0.succAbove j0.succAbove).det) := by
  rw [submatrix_map]
  have h := RingHom.map_det (algebraMap R K) (M.submatrix k0.succAbove j0.succAbove)
  rw [RingHom.mapMatrix_apply] at h
  exact h.symm

theorem minorLinkEventually_proof : MinorLinkEventually U v (ϖ := ϖ) (K := K) := by
  intro n M hinj hv k0 j0 hout
  have hx := (outerMinor_ne_zero_iff U M k0.succAbove j0.succAbove).mp hout
  simp only [minor_map]
  refine ⟨?_, fun j => hv.nonneg _, ?_⟩
  · filter_upwards [eventually_ne_zero_of_not_mem U hx] with j hj
    exact fun h0 => hj (hinj (by rw [h0, map_zero]))
  · rw [outerNegligible_iff_mem_infinitesimals U v hv]
    exact hx

end Link

section Restricted

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {ϖ : R}
  [Fact (Irreducible ϖ)] {ι : Type*} (U : Ultrafilter ι)
  {K : Type*} [Field K] [Algebra R K] (v : AddValuation K (WithTop ℤ))

/-- The outer-large set of instances at which every inner minor whose sequence is not
infinitesimal is nonzero (finitely many positions). -/
def goodSet {n : ℕ} (M : ι → Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Set ι :=
  {j | ∀ k0 j0 : Fin (n + 1),
    (fun i => ((M i).submatrix k0.succAbove j0.succAbove).det) ∉ infinitesimals U ϖ →
      ((M j).submatrix k0.succAbove j0.succAbove).det ≠ 0}

theorem goodSet_mem {n : ℕ} (M : ι → Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    goodSet U (ϖ := ϖ) M ∈ (U : Filter ι) := by
  have : ∀ k0 j0 : Fin (n + 1), ∀ᶠ j in (U : Filter ι),
      (fun i => ((M i).submatrix k0.succAbove j0.succAbove).det) ∉ infinitesimals U ϖ →
        ((M j).submatrix k0.succAbove j0.succAbove).det ≠ 0 := by
    intro k0 j0
    by_cases hx : (fun i => ((M i).submatrix k0.succAbove j0.succAbove).det) ∈
        infinitesimals U ϖ
    · exact Eventually.of_forall fun _ h => absurd hx h
    · filter_upwards [eventually_ne_zero_of_not_mem U hx] with j hj
      exact fun _ => hj
  exact Filter.eventually_all.mpr fun k0 => Filter.eventually_all.mpr fun j0 => this k0 j0

/-- The restricted ultrafilter on an outer-large set of instances. -/
def restrictUltra (P : Set ι) (hP : P ∈ (U : Filter ι)) : Ultrafilter P :=
  U.comap Subtype.val_injective (by rwa [Subtype.range_coe])

/-- Infinitesimality is unchanged by restriction to an outer-large set. -/
theorem mem_infinitesimals_restrict_iff (P : Set ι) (hP : P ∈ (U : Filter ι)) (x : ι → R) :
    (fun i : P => x i) ∈ infinitesimals (restrictUltra U P hP) ϖ ↔ x ∈ infinitesimals U ϖ := by
  simp only [mem_infinitesimals, restrictUltra, Ultrafilter.coe_comap]
  constructor
  · intro h n
    have h' := (h n)
    rw [Filter.eventually_comap] at h'
    filter_upwards [h', hP] with j hj hjP
    exact hj ⟨j, hjP⟩ rfl
  · intro h n
    rw [Filter.eventually_comap]
    filter_upwards [h n] with j hj
    rintro ⟨i, hi⟩ rfl
    exact hj

/-- **Minor link at every instance, after restriction to an outer-large set** (tex L4957–4959). A
stronger optional form of `MinorLinkEventually`, written for the pre-round-3 shape of
`OuterSwitchData.minor_link` (`∀ j, minor_j ≠ 0`); the round-3 field asks only for nonvanishing on
an outer-large set, which `MinorLinkEventually` gives directly. Let `P = goodSet` be
the outer-large set of instances at which the finitely many non-infinitesimal inner minors are
nonzero, `U_P` the restricted ultrafilter, `D j = M j` over `K` for `j ∈ P`, and `D_out` the outer
model of the restricted family over `Frac 𝒪_∞`. Then for every position with nonzero outer minor,
the inner minors at the same position are nonzero at every instance, integral on an outer-large
set, and not outer-negligible (with `k1 = k0`, `j1 = j0`). Classification: PROVED. -/
def MinorLinkRestricted : Prop :=
  ∀ (n : ℕ) (M : ι → Matrix (Fin (n + 1)) (Fin (n + 1)) R), Function.Injective (algebraMap R K) →
    IsPiAdicOn ϖ v →
    let P := goodSet U (ϖ := ϖ) M
    let UP := restrictUltra U P (goodSet_mem U M)
    let D : P → Matrix (Fin (n + 1)) (Fin (n + 1)) K := fun j => (M j).map (algebraMap R K)
    let Dout := (outerMatrix UP ϖ (fun j : P => M j)).map
      (algebraMap (OInf UP ϖ) (FractionRing (OInf UP ϖ)))
    ∀ (k0 j0 : Fin (n + 1)),
      (Dout.submatrix k0.succAbove j0.succAbove).det ≠ 0 →
      ∃ (k1 j1 : Fin (n + 1)),
        (∀ j, ((D j).submatrix k1.succAbove j1.succAbove).det ≠ 0) ∧
        (∀ᶠ j in (UP : Filter P), (0 : WithTop ℤ) ≤ v (((D j).submatrix k1.succAbove j1.succAbove).det)) ∧
        ¬ OuterNegligible v UP (fun j => ((D j).submatrix k1.succAbove j1.succAbove).det)

theorem minorLinkRestricted_proof : MinorLinkRestricted U v (ϖ := ϖ) (K := K) := by
  intro n M hinj hv P UP D Dout k0 j0 hout
  have hxP := (outerMinor_ne_zero_iff UP (fun j : P => M j) k0.succAbove j0.succAbove).mp hout
  have hx : (fun i => ((M i).submatrix k0.succAbove j0.succAbove).det) ∉ infinitesimals U ϖ := by
    intro h
    exact hxP ((mem_infinitesimals_restrict_iff U P (goodSet_mem U M) _).mpr h)
  refine ⟨k0, j0, fun j => ?_, Eventually.of_forall fun j => ?_, ?_⟩
  · simp only [D, minor_map]
    intro h0
    exact j.2 k0 j0 hx (hinj (by rw [h0, map_zero]))
  · simp only [D, minor_map]; exact hv.nonneg _
  · simp only [D, minor_map]
    rw [outerNegligible_iff_mem_infinitesimals UP v hv]
    exact hxP

end Restricted

section Example

/-- Non-vacuity of `IsPiAdicOn`: for `R = ℤ_[2]` inside `K = ℚ_[2]` with Mathlib's 2-adic additive
valuation, `n ≤ v r ↔ 2^n ∣ r`. PROVED. -/
theorem isPiAdicOn_padic : IsPiAdicOn (K := ℚ_[2]) (2 : ℤ_[2]) (Padic.addValuation (p := 2)) := by
  intro r n
  by_cases hr : r = 0
  · subst hr; simp
  · have hr' : (algebraMap ℤ_[2] ℚ_[2] r) ≠ 0 := by
      simpa using hr
    rw [Padic.addValuation.apply hr', WithTop.coe_le_coe]
    change (n : ℤ) ≤ (r : ℚ_[2]).valuation ↔ _
    rw [PadicInt.valuation_coe, Nat.cast_le, ← PadicInt.mem_span_pow_iff_le_valuation r hr n,
      Ideal.mem_span_singleton]
    norm_num

end Example

end ZInQ.Contrib.CloudB3RC53.SwitchInputs
