import Mathlib

/-!
# Lane RC6-limits: the inner ultrafilter limit

This file formalizes the *inner ultrafilter limit* of Elliot Glazer's Lemma
`ex:limits-inner-limit` (manuscript lines 4401-4406 of the statement and lines 4444-4450 of the
proof), and the inner-limit half of the identities (5.2)
(lines 4674-4684).

Manuscript text being formalized (lines 4444-4450):

> Fix one nonprincipal ultrafilter on coefficient stages. Bounded ranks can be fixed on a set in
> that ultrafilter. Each finite tuple of matrix entries then has a compatible limit at every
> coefficient precision, giving matrices over `Λ`. Every polynomial identity between the matrices
> survives. Retained homotopy inverses remain homotopy inverses.

## Contents

* Part 1 (general).  `R` is a compact Hausdorff commutative topological ring, `I : ℕ → Ideal R`
  tends to zero (`IdealsTendToZero`), and `U` is a nonprincipal ultrafilter on the coefficient
  stages `ℕ`.  `ulim U x` is the limit of the pushforward ultrafilter `U.map x`; `ulimVec`,
  `ulimMat` are the coordinatewise versions.  Main results: `ulimHom` (a ring hom),
  `ulim_eq_zero_of_mem`, `ulim_eq_ulim_of_sub_mem` (independence of lifts),
  `eventually_sub_ulim_mem` (compatibility at every precision), `polynomial_identity_survives`,
  `matrix_identity_survives`, `homotopy_inverse_survives`, `contraction_survives`,
  `bounded_ranks_fixed`.
* Part 2 (instance).  `Lambda = ℤ₂[[t]]` (line 2747) with the coefficientwise (product)
  topology, and the stage ideals `stageIdeal i = (2^i, t^i)`, which are open and tend to zero;
  `stageEquiv : Λ/(2^i, t^i) ≃+* (ℤ/2^i)[t]/t^i = A_i` identifies the quotients with the finite
  stages of line 2725.
* Part 3 ((5.2) in the inner limit).  On the product group `Γ = ∏ i, G i`, the ultralimit
  `rhoInf` of approximate representations is a monoid hom and the ultralimit `cInf` of
  approximate cocycles is an exact crossed homomorphism.

Everything in this file is `PROVED`.
-/

namespace ZInQ.Manuscript.RC.Limits

open Filter Topology
open scoped Matrix

noncomputable section

/-! ## Part 1: the ultralimit in a compact Hausdorff ring -/

section Ultralimit

variable {X : Type*} [TopologicalSpace X]

/-- The ultralimit of a sequence of coefficient-stage data along an ultrafilter `U` on the
stages: the limit of the pushforward ultrafilter `U.map x`.

Manuscript: lines 4444-4447 ("Fix one nonprincipal ultrafilter on coefficient stages. ... Each
finite tuple of matrix entries then has a compatible limit at every coefficient precision").
Kind: definition (used by `PROVED` results).  In a compact Hausdorff space this is the unique
`U`-limit (`tendsto_ulim`, `ulim_eq_of_tendsto`). -/
def ulim (U : Ultrafilter ℕ) (x : ℕ → X) : X :=
  (U.map x).lim

/-- Coordinatewise ultralimit of a sequence of tuples `x i : σ → X` (a finite tuple of matrix
entries, line 4446).  Kind: definition. -/
def ulimVec {σ : Type*} (U : Ultrafilter ℕ) (x : ℕ → σ → X) : σ → X :=
  fun s => ulim U (fun i => x i s)

/-- Entrywise ultralimit of a sequence of matrices ("giving matrices over `Λ`", line 4447).
Kind: definition. -/
def ulimMat {m n : Type*} (U : Ultrafilter ℕ) (M : ℕ → Matrix m n X) : Matrix m n X :=
  Matrix.of fun a b => ulim U (fun i => M i a b)

/-- Coordinates of `ulimVec`.  Kind: `PROVED` (helper). -/
theorem ulimVec_apply {σ : Type*} (U : Ultrafilter ℕ) (x : ℕ → σ → X) (s : σ) :
    ulimVec U x s = ulim U (fun i => x i s) := rfl

/-- Entries of `ulimMat`.  Kind: `PROVED` (helper). -/
theorem ulimMat_apply {m n : Type*} (U : Ultrafilter ℕ) (M : ℕ → Matrix m n X) (a : m) (b : n) :
    ulimMat U M a b = ulim U (fun i => M i a b) := rfl

variable [CompactSpace X]

/-- The sequence converges to its ultralimit along `U`.  Lines 4444-4447.  Kind: `PROVED`. -/
theorem tendsto_ulim (U : Ultrafilter ℕ) (x : ℕ → X) :
    Tendsto x (U : Filter ℕ) (𝓝 (ulim U x)) := by
  have h := (U.map x).le_nhds_lim
  rw [Ultrafilter.coe_map] at h
  exact h

/-- Coordinatewise convergence of tuples.  Line 4446.  Kind: `PROVED`. -/
theorem tendsto_ulimVec {σ : Type*} (U : Ultrafilter ℕ) (x : ℕ → σ → X) :
    Tendsto x (U : Filter ℕ) (𝓝 (ulimVec U x)) :=
  tendsto_pi_nhds.2 fun s => tendsto_ulim U (fun i => x i s)

/-- Entrywise convergence of matrices.  Lines 4446-4447.  Kind: `PROVED`. -/
theorem tendsto_ulimMat {m n : Type*} (U : Ultrafilter ℕ) (M : ℕ → Matrix m n X) :
    Tendsto M (U : Filter ℕ) (𝓝 (ulimMat U M)) :=
  tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => tendsto_ulim U (fun i => M i a b)

variable [T2Space X]

/-- Uniqueness: any `U`-limit is the ultralimit.  Kind: `PROVED`. -/
theorem ulim_eq_of_tendsto {U : Ultrafilter ℕ} {x : ℕ → X} {a : X}
    (h : Tendsto x (U : Filter ℕ) (𝓝 a)) : ulim U x = a :=
  tendsto_nhds_unique (tendsto_ulim U x) h

/-- The ultralimit is characterized by convergence along `U`.  Kind: `PROVED` (helper). -/
theorem ulim_eq_iff_tendsto {U : Ultrafilter ℕ} {x : ℕ → X} {a : X} :
    ulim U x = a ↔ Tendsto x (U : Filter ℕ) (𝓝 a) :=
  ⟨fun h => h ▸ tendsto_ulim U x, ulim_eq_of_tendsto⟩

/-- Uniqueness for tuples.  Kind: `PROVED` (helper). -/
theorem ulimVec_eq_of_tendsto {σ : Type*} {U : Ultrafilter ℕ} {x : ℕ → σ → X} {a : σ → X}
    (h : Tendsto x (U : Filter ℕ) (𝓝 a)) : ulimVec U x = a :=
  funext fun s => ulim_eq_of_tendsto (tendsto_pi_nhds.1 h s)

/-- Uniqueness for matrices.  Kind: `PROVED` (helper). -/
theorem ulimMat_eq_of_tendsto {m n : Type*} {U : Ultrafilter ℕ} {M : ℕ → Matrix m n X}
    {A : Matrix m n X} (h : Tendsto M (U : Filter ℕ) (𝓝 A)) : ulimMat U M = A := by
  ext a b
  exact ulim_eq_of_tendsto (tendsto_pi_nhds.1 (tendsto_pi_nhds.1 h a) b)

/-- Constant sequences.  Kind: `PROVED` (helper). -/
theorem ulim_const (U : Ultrafilter ℕ) (a : X) : ulim U (fun _ => a) = a :=
  ulim_eq_of_tendsto tendsto_const_nhds

/-- Constant matrix sequences.  Kind: `PROVED` (helper). -/
theorem ulimMat_const {m n : Type*} (U : Ultrafilter ℕ) (A : Matrix m n X) :
    ulimMat U (fun _ => A) = A :=
  ulimMat_eq_of_tendsto tendsto_const_nhds

/-- Only `U`-many stages matter. -/
theorem ulim_congr {U : Ultrafilter ℕ} {x y : ℕ → X} (h : ∀ᶠ i in (U : Filter ℕ), x i = y i) :
    ulim U x = ulim U y :=
  ulim_eq_of_tendsto ((tendsto_ulim U y).congr' (EventuallyEq.symm h))

end Ultralimit

section Ring

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R]

/-- The ultralimit is additive, multiplicative and preserves `1`: it is a ring homomorphism
`(ℕ → R) →+* R`.  Lines 4444-4448 (limits of entries respect the ring operations, the basis of
"Every polynomial identity between the matrices survives").  Kind: `PROVED`. -/
def ulimHom (U : Ultrafilter ℕ) : (ℕ → R) →+* R where
  toFun := ulim U
  map_one' := ulim_const U 1
  map_mul' x y := ulim_eq_of_tendsto ((tendsto_ulim U x).mul (tendsto_ulim U y))
  map_zero' := ulim_const U 0
  map_add' x y := ulim_eq_of_tendsto ((tendsto_ulim U x).add (tendsto_ulim U y))

/-- Kind: `PROVED` (helper). -/
theorem ulimHom_apply (U : Ultrafilter ℕ) (x : ℕ → R) : ulimHom U x = ulim U x := rfl

/-- Additivity (line 4447).  Kind: `PROVED` (helper). -/
theorem ulim_add (U : Ultrafilter ℕ) (x y : ℕ → R) :
    ulim U (fun i => x i + y i) = ulim U x + ulim U y :=
  map_add (ulimHom U) x y

/-- Kind: `PROVED` (helper). -/
theorem ulim_sub (U : Ultrafilter ℕ) (x y : ℕ → R) :
    ulim U (fun i => x i - y i) = ulim U x - ulim U y :=
  map_sub (ulimHom U) x y

/-- Kind: `PROVED` (helper). -/
theorem ulim_neg (U : Ultrafilter ℕ) (x : ℕ → R) :
    ulim U (fun i => -x i) = -ulim U x :=
  map_neg (ulimHom U) x

/-- Multiplicativity (line 4447).  Kind: `PROVED` (helper). -/
theorem ulim_mul (U : Ultrafilter ℕ) (x y : ℕ → R) :
    ulim U (fun i => x i * y i) = ulim U x * ulim U y :=
  map_mul (ulimHom U) x y

omit [IsTopologicalRing R] in
/-- Kind: `PROVED` (helper). -/
theorem ulim_one (U : Ultrafilter ℕ) : ulim U (fun _ => (1 : R)) = 1 :=
  ulim_const U 1

omit [IsTopologicalRing R] in
/-- Kind: `PROVED` (helper). -/
theorem ulim_zero (U : Ultrafilter ℕ) : ulim U (fun _ => (0 : R)) = 0 :=
  ulim_const U 0

/-- Integer casts are preserved. -/
theorem ulim_intCast (U : Ultrafilter ℕ) (k : ℤ) : ulim U (fun _ => (k : R)) = k :=
  map_intCast (ulimHom U) k

/-- Kind: `PROVED` (helper). -/
theorem ulim_natCast (U : Ultrafilter ℕ) (k : ℕ) : ulim U (fun _ => (k : R)) = k :=
  map_natCast (ulimHom U) k

/-- Finite sums.  Kind: `PROVED` (helper). -/
theorem ulim_sum {ι : Type*} (U : Ultrafilter ℕ) (s : Finset ι) (f : ι → ℕ → R) :
    ulim U (fun i => ∑ k ∈ s, f k i) = ∑ k ∈ s, ulim U (f k) :=
  ulim_eq_of_tendsto (tendsto_finsetSum s fun k _ => tendsto_ulim U (f k))

/-- A sequence of ideals of `R` *tends to zero*: every neighbourhood of `0` contains `I i` for
all large `i`.  For `Λ = ℤ₂[[t]]` these are the stage ideals `(2^i, t^i)` defining the finite
coefficient stages `A_i = Λ/(2^i, t^i)` (lines 2725, 2747; see `stageIdeal_tendsToZero`).
Kind: definition. -/
def IdealsTendToZero (I : ℕ → Ideal R) : Prop :=
  ∀ V ∈ 𝓝 (0 : R), ∀ᶠ i in atTop, (I i : Set R) ⊆ V

/-- On `ℕ`, being below the cofinite filter is the same as being below `atTop`
(nonprincipality of an ultrafilter on the coefficient stages). -/
theorem le_cofinite_iff_le_atTop (U : Ultrafilter ℕ) :
    (U : Filter ℕ) ≤ cofinite ↔ (U : Filter ℕ) ≤ atTop := by
  rw [Nat.cofinite_eq_atTop]

omit [IsTopologicalRing R] [CompactSpace R] [T2Space R] in
/-- A sequence lying `U`-eventually in the stage ideals tends to `0` along a nonprincipal `U`.
Kind: `PROVED`. -/
theorem tendsto_zero_of_eventually_mem {I : ℕ → Ideal R} (hI : IdealsTendToZero I)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) {x : ℕ → R}
    (h : ∀ᶠ i in (U : Filter ℕ), x i ∈ I i) : Tendsto x (U : Filter ℕ) (𝓝 0) := by
  refine tendsto_iff_forall_eventually_mem.2 fun V hV => ?_
  have h1 : ∀ᶠ i in (U : Filter ℕ), (I i : Set R) ⊆ V :=
    Eventually.filter_mono ((le_cofinite_iff_le_atTop U).1 hU) (hI V hV)
  filter_upwards [h, h1] with i hi h1i
  exact h1i hi

omit [IsTopologicalRing R] in
/-- `ulim_eq_zero_of_mem`: if `x i ∈ I i` for `U`-many stages, the ultralimit vanishes.
Lines 4446-4448.  Kind: `PROVED`. -/
theorem ulim_eq_zero_of_mem {I : ℕ → Ideal R} (hI : IdealsTendToZero I) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) {x : ℕ → R} (h : ∀ᶠ i in (U : Filter ℕ), x i ∈ I i) :
    ulim U x = 0 :=
  ulim_eq_of_tendsto (tendsto_zero_of_eventually_mem hI hU h)

/-- Independence of lifts: two sequences of lifts of the same stage data (they differ by an
element of `I i` for `U`-many `i`) have the same ultralimit.  Lines 4444-4447.
Kind: `PROVED`. -/
theorem ulim_eq_ulim_of_sub_mem {I : ℕ → Ideal R} (hI : IdealsTendToZero I) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) {x y : ℕ → R}
    (h : ∀ᶠ i in (U : Filter ℕ), x i - y i ∈ I i) : ulim U x = ulim U y := by
  have h0 := ulim_eq_zero_of_mem hI hU (x := fun i => x i - y i) h
  rw [ulim_sub] at h0
  exact sub_eq_zero.1 h0

omit [T2Space R] in
/-- Compatibility at every precision: for every open ideal `J` (e.g. every stage ideal of `Λ`,
`stageIdeal_isOpen`), `x i ≡ ulim U x (mod J)` for `U`-many `i` ("a compatible limit at every
coefficient precision", line 4446).  Kind: `PROVED`. -/
theorem eventually_sub_ulim_mem {J : Ideal R} (hJ : IsOpen (J : Set R)) (U : Ultrafilter ℕ)
    (x : ℕ → R) : ∀ᶠ i in (U : Filter ℕ), x i - ulim U x ∈ J := by
  have hmem : {r : R | r - ulim U x ∈ J} ∈ 𝓝 (ulim U x) := by
    refine IsOpen.mem_nhds (hJ.preimage (continuous_sub_right (ulim U x))) ?_
    show ulim U x - ulim U x ∈ J
    rw [sub_self]
    exact J.zero_mem
  exact (tendsto_ulim U x).eventually hmem

/-- Characterization of the ultralimit as *the* compatible limit at every precision: if the
ideals `I n` are open and tend to zero, then `a = ulim U x` iff `x i ≡ a (mod I n)` for `U`-many
`i`, for every precision `n`.  Line 4446.  Kind: `PROVED`. -/
theorem ulim_eq_iff_forall_eventually_sub_mem {I : ℕ → Ideal R} (hI : IdealsTendToZero I)
    (hopen : ∀ n, IsOpen (I n : Set R)) (U : Ultrafilter ℕ) (x : ℕ → R) (a : R) :
    ulim U x = a ↔ ∀ n, ∀ᶠ i in (U : Filter ℕ), x i - a ∈ I n := by
  constructor
  · rintro rfl n
    exact eventually_sub_ulim_mem (hopen n) U x
  · intro h
    refine ulim_eq_of_tendsto (tendsto_sub_nhds_zero_iff.1 ?_)
    refine tendsto_iff_forall_eventually_mem.2 fun V hV => ?_
    obtain ⟨n, hn⟩ := (hI V hV).exists
    filter_upwards [h n] with i hi
    exact hn hi

/-! ### Coordinatewise and matrix versions -/

/-- Independence of lifts for tuples.  Kind: `PROVED` (helper). -/
theorem ulimVec_eq_of_sub_mem {σ : Type*} {I : ℕ → Ideal R} (hI : IdealsTendToZero I)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) {x y : ℕ → σ → R}
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ s, x i s - y i s ∈ I i) : ulimVec U x = ulimVec U y :=
  funext fun s => ulim_eq_ulim_of_sub_mem hI hU (h.mono fun _ hi => hi s)

/-- Independence of lifts for matrices.  Kind: `PROVED` (helper). -/
theorem ulimMat_eq_of_sub_mem {m n : Type*} {I : ℕ → Ideal R} (hI : IdealsTendToZero I)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) {M N : ℕ → Matrix m n R}
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ a b, M i a b - N i a b ∈ I i) : ulimMat U M = ulimMat U N := by
  ext a b
  exact ulim_eq_ulim_of_sub_mem hI hU (h.mono fun _ hi => hi a b)

/-- Kind: `PROVED` (helper). -/
theorem ulimMat_add {m n : Type*} (U : Ultrafilter ℕ) (M N : ℕ → Matrix m n R) :
    ulimMat U (fun i => M i + N i) = ulimMat U M + ulimMat U N := by
  ext a b
  exact ulim_add U (fun i => M i a b) (fun i => N i a b)

/-- Kind: `PROVED` (helper). -/
theorem ulimMat_sub {m n : Type*} (U : Ultrafilter ℕ) (M N : ℕ → Matrix m n R) :
    ulimMat U (fun i => M i - N i) = ulimMat U M - ulimMat U N := by
  ext a b
  exact ulim_sub U (fun i => M i a b) (fun i => N i a b)

/-- The entrywise ultralimit of a product of matrices is the product of the ultralimits.
Kind: `PROVED` (helper). -/
theorem ulimMat_mul {m k n : Type*} [Fintype k] (U : Ultrafilter ℕ) (M : ℕ → Matrix m k R)
    (N : ℕ → Matrix k n R) : ulimMat U (fun i => M i * N i) = ulimMat U M * ulimMat U N := by
  ext a b
  rw [ulimMat_apply, Matrix.mul_apply]
  simp only [Matrix.mul_apply, ulimMat_apply]
  exact ulim_eq_of_tendsto
    (tendsto_finsetSum _ fun j _ => (tendsto_ulim U _).mul (tendsto_ulim U _))

omit [IsTopologicalRing R] in
/-- Kind: `PROVED` (helper). -/
theorem ulimMat_one {n : Type*} [DecidableEq n] (U : Ultrafilter ℕ) :
    ulimMat U (fun _ => (1 : Matrix n n R)) = 1 :=
  ulimMat_const U 1

omit [IsTopologicalRing R] in
/-- Kind: `PROVED` (helper). -/
theorem ulimMat_zero {m n : Type*} (U : Ultrafilter ℕ) :
    ulimMat U (fun _ => (0 : Matrix m n R)) = 0 :=
  ulimMat_const U 0

/-- Ultralimits commute with matrix-vector products.  Kind: `PROVED` (helper). -/
theorem ulimVec_mulVec {m n : Type*} [Fintype n] (U : Ultrafilter ℕ) (M : ℕ → Matrix m n R)
    (v : ℕ → n → R) : ulimVec U (fun i => M i *ᵥ v i) = ulimMat U M *ᵥ ulimVec U v := by
  funext a
  simp only [ulimVec_apply, Matrix.mulVec, dotProduct, ulimMat_apply]
  exact ulim_eq_of_tendsto
    (tendsto_finsetSum _ fun j _ => (tendsto_ulim U _).mul (tendsto_ulim U _))

/-- Kind: `PROVED` (helper). -/
theorem ulimVec_add {σ : Type*} (U : Ultrafilter ℕ) (x y : ℕ → σ → R) :
    ulimVec U (fun i => x i + y i) = ulimVec U x + ulimVec U y :=
  funext fun s => ulim_add U (fun i => x i s) (fun i => y i s)

/-- Kind: `PROVED` (helper). -/
theorem ulimVec_sub {σ : Type*} (U : Ultrafilter ℕ) (x y : ℕ → σ → R) :
    ulimVec U (fun i => x i - y i) = ulimVec U x - ulimVec U y :=
  funext fun s => ulim_sub U (fun i => x i s) (fun i => y i s)

omit [IsTopologicalRing R] in
/-- Kind: `PROVED` (helper). -/
theorem ulimVec_zero {σ : Type*} (U : Ultrafilter ℕ) :
    ulimVec U (fun _ => (0 : σ → R)) = 0 :=
  funext fun _ => ulim_zero U

/-- `ulim_eq_zero_of_mem` for matrices.  Kind: `PROVED` (helper). -/
theorem ulimMat_eq_zero_of_mem {m n : Type*} {I : ℕ → Ideal R} (hI : IdealsTendToZero I)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) {M : ℕ → Matrix m n R}
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ a b, M i a b ∈ I i) : ulimMat U M = 0 := by
  rw [← ulimMat_zero (R := R) U]
  exact ulimMat_eq_of_sub_mem hI hU (h.mono fun i hi a b => by simpa using hi a b)

/-! ### Polynomial identities survive -/

/-- Evaluation of an integer polynomial commutes with the coordinatewise ultralimit.
Kind: `PROVED`. -/
theorem eval₂_ulimVec {σ : Type*} (U : Ultrafilter ℕ) (x : ℕ → σ → R) (P : MvPolynomial σ ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom R) (ulimVec U x) P =
      ulim U (fun i => MvPolynomial.eval₂ (Int.castRingHom R) (x i) P) := by
  have key : MvPolynomial.eval₂Hom (Int.castRingHom R) (ulimVec U x) =
      (ulimHom U).comp (RingHom.pi fun i => MvPolynomial.eval₂Hom (Int.castRingHom R) (x i)) := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun s => ?_
    rw [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, ulimHom_apply, ulimVec_apply]
    congr 1
    funext i
    rw [RingHom.pi_apply, MvPolynomial.eval₂Hom_X']
  exact RingHom.congr_fun key P

/-- `polynomial_identity_survives` ("Every polynomial identity between the matrices survives",
lines 4447-4448).  If an integer polynomial identity `P = 0` between finitely or infinitely many
entries holds modulo the stage ideal `I i` for `U`-many stages `i`, then it holds exactly for the
ultralimit entries.  Kind: `PROVED`. -/
theorem polynomial_identity_survives {σ : Type*} {I : ℕ → Ideal R} (hI : IdealsTendToZero I)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (x : ℕ → σ → R) (P : MvPolynomial σ ℤ)
    (h : ∀ᶠ i in (U : Filter ℕ), MvPolynomial.eval₂ (Int.castRingHom R) (x i) P ∈ I i) :
    MvPolynomial.eval₂ (Int.castRingHom R) (ulimVec U x) P = 0 := by
  rw [eval₂_ulimVec]
  exact ulim_eq_zero_of_mem hI hU h

/-- Stage form of `polynomial_identity_survives`: the identity is assumed in the finite
coefficient stages `R ⧸ I i` (for `Λ` these are `A_i = Λ/(2^i, t^i)`, line 2725) for the
reductions of the lifts `x i`, for `U`-many `i`.  Lines 4444-4448.  Kind: `PROVED`. -/
theorem polynomial_identity_survives_of_stages {σ : Type*} {I : ℕ → Ideal R}
    (hI : IdealsTendToZero I) {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    (x : ℕ → σ → R) (P : MvPolynomial σ ℤ)
    (h : ∀ᶠ i in (U : Filter ℕ), MvPolynomial.eval₂ (Int.castRingHom (R ⧸ I i))
      (fun s => Ideal.Quotient.mk (I i) (x i s)) P = 0) :
    MvPolynomial.eval₂ (Int.castRingHom R) (ulimVec U x) P = 0 := by
  refine polynomial_identity_survives hI hU x P (h.mono fun i hi => ?_)
  rw [← Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.eval₂_comp_left,
    show (Ideal.Quotient.mk (I i)).comp (Int.castRingHom R) = Int.castRingHom (R ⧸ I i) from
      RingHom.ext_int _ _]
  exact hi

/-- Independence of lifts, stage form: lifts with the same reductions in `R ⧸ I i` for `U`-many
`i` have the same ultralimit.  Kind: `PROVED`. -/
theorem ulimVec_eq_of_stages {σ : Type*} {I : ℕ → Ideal R} (hI : IdealsTendToZero I)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) {x y : ℕ → σ → R}
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ s, Ideal.Quotient.mk (I i) (x i s) =
      Ideal.Quotient.mk (I i) (y i s)) : ulimVec U x = ulimVec U y :=
  ulimVec_eq_of_sub_mem hI hU (h.mono fun _ hi s => Ideal.Quotient.eq.1 (hi s))

/-! ### Matrix identities and retained homotopy inverses -/

/-- `matrix_identity_survives`: if `X i * Y i ≡ Z i` entrywise modulo `I i` for `U`-many `i`,
then `ulim X * ulim Y = ulim Z` exactly ("preserving its matrix identities", line 4404;
lines 4447-4448).  Kind: `PROVED`. -/
theorem matrix_identity_survives {m k n : Type*} [Fintype k] {I : ℕ → Ideal R}
    (hI : IdealsTendToZero I) {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    (X : ℕ → Matrix m k R) (Y : ℕ → Matrix k n R) (Z : ℕ → Matrix m n R)
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ a b, (X i * Y i - Z i) a b ∈ I i) :
    ulimMat U X * ulimMat U Y = ulimMat U Z := by
  rw [← ulimMat_mul]
  exact ulimMat_eq_of_sub_mem hI hU h

/-- `homotopy_inverse_survives` ("Retained homotopy inverses remain homotopy inverses",
lines 4405, 4448-4449).  If `f_i g_i - 1 ≡ d_i s_i + s_i d'_i` entrywise modulo `I i` for `U`-many
`i`, then `f g - 1 = d s + s d'` holds exactly for the ultralimit matrices.  Kind: `PROVED`.
DEPARTURE (of form): a bounded finite free complex is presented as one matrix `d` on its total
free module (all degrees together, square of size the total rank), so `d`, `d'` are the
differentials, `s` the retained homotopy, and `f`, `g` the retained maps; the grading is not
recorded, and is not needed for the survival of the identity. -/
theorem homotopy_inverse_survives {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    {I : ℕ → Ideal R} (hI : IdealsTendToZero I) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (f : ℕ → Matrix m n R) (g : ℕ → Matrix n m R)
    (d s d' : ℕ → Matrix m m R)
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ a b,
      (f i * g i - 1 - (d i * s i + s i * d' i) : Matrix m m R) a b ∈ I i) :
    ulimMat U f * ulimMat U g - 1 = ulimMat U d * ulimMat U s + ulimMat U s * ulimMat U d' := by
  have h0 := ulimMat_eq_zero_of_mem hI hU h
  rw [ulimMat_sub U (fun i => f i * g i - 1) (fun i => d i * s i + s i * d' i),
    ulimMat_sub U (fun i => f i * g i) (fun _ => 1),
    ulimMat_add U (fun i => d i * s i) (fun i => s i * d' i),
    ulimMat_mul, ulimMat_mul, ulimMat_mul, ulimMat_one] at h0
  exact sub_eq_zero.1 h0

/-- `contraction_survives`: the retained contraction data of a finite free model (lines
4421-4437: `d^2 = 0`, `p i = 1`, `1 - i p = d h + h d`, and the chain-map identities
`d i = i d_C`, `p d = d_C p`), holding modulo `I j` at `U`-many stages `j`, hold exactly for the
ultralimit matrices.  Manuscript names: `perturbed_inclusion = i`, `perturbed_projection = p`,
`perturbed_homotopy = h`, model differential `d_C`.  Lines 4437, 4447-4449.  Kind: `PROVED`. -/
theorem contraction_survives {N c : Type*} [Fintype N] [Fintype c] [DecidableEq N]
    [DecidableEq c] {I : ℕ → Ideal R} (hI : IdealsTendToZero I) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (d : ℕ → Matrix N N R) (dC : ℕ → Matrix c c R)
    (perturbed_inclusion : ℕ → Matrix N c R) (perturbed_projection : ℕ → Matrix c N R)
    (perturbed_homotopy : ℕ → Matrix N N R)
    (hd : ∀ᶠ j in (U : Filter ℕ), ∀ a b, (d j * d j) a b ∈ I j)
    (hpi : ∀ᶠ j in (U : Filter ℕ), ∀ a b,
      (perturbed_projection j * perturbed_inclusion j - 1 : Matrix c c R) a b ∈ I j)
    (hhtpy : ∀ᶠ j in (U : Filter ℕ), ∀ a b,
      (1 - perturbed_inclusion j * perturbed_projection j -
        (d j * perturbed_homotopy j + perturbed_homotopy j * d j) : Matrix N N R) a b ∈ I j)
    (hi : ∀ᶠ j in (U : Filter ℕ), ∀ a b,
      (d j * perturbed_inclusion j - perturbed_inclusion j * dC j) a b ∈ I j)
    (hp : ∀ᶠ j in (U : Filter ℕ), ∀ a b,
      (perturbed_projection j * d j - dC j * perturbed_projection j) a b ∈ I j) :
    ulimMat U d * ulimMat U d = 0 ∧
    ulimMat U perturbed_projection * ulimMat U perturbed_inclusion = 1 ∧
    1 - ulimMat U perturbed_inclusion * ulimMat U perturbed_projection =
      ulimMat U d * ulimMat U perturbed_homotopy + ulimMat U perturbed_homotopy * ulimMat U d ∧
    ulimMat U d * ulimMat U perturbed_inclusion = ulimMat U perturbed_inclusion * ulimMat U dC ∧
    ulimMat U perturbed_projection * ulimMat U d = ulimMat U dC * ulimMat U perturbed_projection := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← ulimMat_zero (R := R) U]
    exact matrix_identity_survives hI hU d d (fun _ => 0) (hd.mono fun j hj a b => by simpa using hj a b)
  · rw [← ulimMat_one (R := R) U]
    exact matrix_identity_survives hI hU _ _ (fun _ => 1) hpi
  · have h0 := ulimMat_eq_zero_of_mem hI hU hhtpy
    rw [ulimMat_sub U (fun j => 1 - perturbed_inclusion j * perturbed_projection j)
        (fun j => d j * perturbed_homotopy j + perturbed_homotopy j * d j),
      ulimMat_sub U (fun _ => 1) (fun j => perturbed_inclusion j * perturbed_projection j),
      ulimMat_add U (fun j => d j * perturbed_homotopy j) (fun j => perturbed_homotopy j * d j),
      ulimMat_mul, ulimMat_mul, ulimMat_mul, ulimMat_one] at h0
    exact sub_eq_zero.1 h0
  · exact (matrix_identity_survives hI hU _ _ (fun j => perturbed_inclusion j * dC j) hi).trans
      (ulimMat_mul U _ _)
  · exact (matrix_identity_survives hI hU _ _ (fun j => dC j * perturbed_projection j) hp).trans
      (ulimMat_mul U _ _)

/-! ### Bounded ranks can be fixed -/

/-- `bounded_ranks_fixed` ("Bounded ranks can be fixed on a set in that ultrafilter", lines
4401-4402, 4444-4445): a sequence of ranks bounded by `B` is constant on a set in `U`.
Kind: `PROVED`. -/
theorem bounded_ranks_fixed (U : Ultrafilter ℕ) {B : ℕ} (r : ℕ → ℕ) (hr : ∀ i, r i ≤ B) :
    ∃ r₀ ≤ B, ∀ᶠ i in (U : Filter ℕ), r i = r₀ := by
  have h : ∀ᶠ i in (U : Filter ℕ), ∃ a ∈ Set.Iic B, r i = a :=
    Eventually.of_forall fun i => ⟨r i, hr i, rfl⟩
  obtain ⟨a, ha, h'⟩ := (Ultrafilter.eventually_exists_mem_iff (Set.finite_Iic B)).1 h
  exact ⟨a, ha, h'⟩

/-- `bounded_ranks_fixed` for any function into a finite type (e.g. a tuple of ranks of the
graded pieces of a model, each bounded).  Kind: `PROVED`. -/
theorem eventually_eq_const_of_finite {β : Type*} [Finite β] (U : Ultrafilter ℕ) (r : ℕ → β) :
    ∃ b, ∀ᶠ i in (U : Filter ℕ), r i = b :=
  Ultrafilter.eventually_exists_iff.1 (Eventually.of_forall fun i => ⟨r i, rfl⟩)

/-- Tuple version of `bounded_ranks_fixed`: finitely many bounded rank sequences (ranks in each
degree of a bounded model) are simultaneously constant on one set in `U`.  Kind: `PROVED`. -/
theorem bounded_rank_tuples_fixed {ι : Type*} [Finite ι] (U : Ultrafilter ℕ) {B : ℕ}
    (r : ℕ → ι → ℕ) (hr : ∀ i j, r i j ≤ B) :
    ∃ r₀ : ι → ℕ, (∀ j, r₀ j ≤ B) ∧ ∀ᶠ i in (U : Filter ℕ), r i = r₀ := by
  have hfin : (Set.univ.pi fun _ : ι => Set.Iic B).Finite :=
    Set.Finite.pi fun _ => Set.finite_Iic B
  have h : ∀ᶠ i in (U : Filter ℕ), ∃ a ∈ Set.univ.pi (fun _ : ι => Set.Iic B), r i = a :=
    Eventually.of_forall fun i => ⟨r i, fun j _ => hr i j, rfl⟩
  obtain ⟨a, ha, h'⟩ := (Ultrafilter.eventually_exists_mem_iff hfin).1 h
  exact ⟨a, fun j => ha j (Set.mem_univ j), h'⟩

/-! ### A criterion for ideals tending to zero -/

omit [IsTopologicalRing R] [T2Space R] in
/-- In a compact ring, a decreasing sequence of closed ideals with zero intersection
tends to zero.  Kind: `PROVED`. -/
theorem idealsTendToZero_of_antitone {I : ℕ → Ideal R} (hanti : Antitone I)
    (hclosed : ∀ n, IsClosed (I n : Set R)) (hinter : ∀ r, (∀ n, r ∈ I n) → r = 0) :
    IdealsTendToZero I := by
  intro V hV
  have hanti' : Antitone fun n => (I n : Set R) := fun a b hab =>
    SetLike.coe_subset_coe.2 (hanti hab)
  have hsub : (⋂ n, (I n : Set R)) ⊆ {0} := fun r hr =>
    hinter r fun n => Set.mem_iInter.1 hr n
  have hV' : V ∈ 𝓝ˢ (⋂ n, (I n : Set R)) := nhdsSet_mono hsub (by rwa [nhdsSet_singleton])
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_compactSpace hanti'.directed_ge hclosed hV'
  exact eventually_atTop.2 ⟨n, fun m hm => (hanti' hm).trans hn⟩

end Ring

/-! ## Part 2: the instance `Λ = ℤ₂[[t]]` with stages `A_i = (ℤ/2^i)[t]/t^i` -/

section Lambda

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- `Λ = ℤ₂[[t]]` (line 2747: "Put `Λ = ℤ_2[[t]]`"), with the coefficientwise (product)
topology `PowerSeries.WithPiTopology`.  Kind: definition. -/
abbrev Lambda : Type := PowerSeries ℤ_[2]

/-- `Λ` is compact (Tychonoff: it is a product of copies of the compact ring `ℤ₂`).
Kind: `PROVED`. -/
instance lambda_compactSpace : CompactSpace Lambda := by
  unfold Lambda PowerSeries
  exact inferInstanceAs (CompactSpace ((Unit →₀ ℕ) → ℤ_[2]))

/-- `Λ` is Hausdorff.  Kind: `PROVED`. -/
theorem lambda_t2Space : T2Space Lambda := inferInstance

/-- `Λ` is a topological ring.  Kind: `PROVED`. -/
theorem lambda_isTopologicalRing : IsTopologicalRing Lambda := inferInstance

/-- The stage ideal `(2^i, t^i)` of `Λ`, so that the finite coefficient stage of line 2725 is
`A_i = (ℤ/2^iℤ)[t]/t^i ≅ Λ ⧸ stageIdeal i` (the ring isomorphism is `stageEquiv`).
Kind: definition. -/
def stageIdeal (i : ℕ) : Ideal Lambda :=
  Ideal.span {(2 : Lambda) ^ i, X ^ i}

/-- Kind: `PROVED` (helper). -/
theorem two_pow_eq_C (n : ℕ) : (2 : Lambda) ^ n = C ((2 : ℤ_[2]) ^ n) := by
  rw [map_pow, map_ofNat]

/-- An element of the stage ideal `(2^n, t^n)` is exactly a power series whose first `n`
coefficients are divisible by `2^n`.  Kind: `PROVED`. -/
theorem mem_stageIdeal_iff {n : ℕ} {f : Lambda} :
    f ∈ stageIdeal n ↔ ∀ k < n, (2 : ℤ_[2]) ^ n ∣ coeff k f := by
  constructor
  · intro hf k hk
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hf
    have hnk : ¬n ≤ k := by omega
    rw [map_add, two_pow_eq_C, coeff_mul_C, coeff_mul_X_pow']
    simp only [hnk, ↓reduceIte, add_zero]
    exact dvd_mul_left _ _
  · intro hf
    set T : Lambda := ∑ k ∈ Finset.range n, monomial k (coeff k f) with hTdef
    have hT : T ∈ stageIdeal n := by
      refine Ideal.sum_mem _ fun k hk => ?_
      obtain ⟨c, hc⟩ := hf k (Finset.mem_range.1 hk)
      have hmon : monomial k (coeff k f) = (2 : Lambda) ^ n * monomial k c := by
        rw [hc, two_pow_eq_C]
        ext m
        rw [coeff_C_mul, coeff_monomial, coeff_monomial]
        split_ifs <;> simp
      rw [hmon]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    have hX : (X : Lambda) ^ n ∣ f - T := by
      rw [X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hTdef, map_sum]
      simp only [coeff_monomial]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_range.2 hm, ↓reduceIte, sub_self]
    obtain ⟨q, hq⟩ := hX
    have hf' : f = T + q * X ^ n := by
      rw [mul_comm, ← hq]
      ring
    rw [hf']
    exact Ideal.add_mem _ hT
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

/-- The ideal `2^n ℤ₂` is open in `ℤ₂`.  Kind: `PROVED`. -/
theorem isOpen_span_two_pow (n : ℕ) :
    IsOpen ((Ideal.span {(2 : ℤ_[2]) ^ n} : Ideal ℤ_[2]) : Set ℤ_[2]) := by
  refine AddSubgroup.isOpen_of_mem_nhds (Ideal.span {(2 : ℤ_[2]) ^ n}).toAddSubgroup (g := 0) ?_
  refine Filter.mem_of_superset
    (Metric.ball_mem_nhds (0 : ℤ_[2]) (by positivity : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℤ)))) ?_
  intro x hx
  have h1 : ‖x‖ ≤ ((2 : ℕ) : ℝ) ^ (-(n : ℤ)) := by
    rw [mem_ball_zero_iff] at hx
    exact_mod_cast hx.le
  have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow x n).1 h1
  simpa using h2

/-- The stage ideal `(2^n, t^n)` as the set `{f | ∀ k < n, 2^n ∣ coeff k f}`.  Kind: `PROVED` (helper). -/
theorem stageIdeal_coe_eq (n : ℕ) :
    (stageIdeal n : Set Lambda) =
      ⋂ k ∈ Finset.range n, (fun f : Lambda => coeff k f) ⁻¹'
        ((Ideal.span {(2 : ℤ_[2]) ^ n} : Ideal ℤ_[2]) : Set ℤ_[2]) := by
  ext f
  simp only [SetLike.mem_coe, mem_stageIdeal_iff, Set.mem_iInter, Set.mem_preimage,
    Finset.mem_range, Ideal.mem_span_singleton]

/-- Each stage ideal `(2^n, t^n)` is open in `Λ`: it is `{f | ∀ k < n, 2^n ∣ coeff k f}`, a
finite intersection of preimages of open sets under continuous coefficient maps.
Kind: `PROVED`. -/
theorem stageIdeal_isOpen (n : ℕ) : IsOpen (stageIdeal n : Set Lambda) := by
  rw [stageIdeal_coe_eq]
  exact isOpen_biInter_finset fun k _ =>
    (isOpen_span_two_pow n).preimage (WithPiTopology.continuous_coeff ℤ_[2] k)

/-- The stage ideals decrease.  Kind: `PROVED` (helper). -/
theorem stageIdeal_antitone : Antitone stageIdeal := by
  intro m n hmn f hf
  rw [mem_stageIdeal_iff] at hf ⊢
  intro k hk
  exact (pow_dvd_pow 2 hmn).trans (hf k (lt_of_lt_of_le hk hmn))

/-- `⋂ₙ 2^n ℤ₂ = 0`.  Kind: `PROVED` (helper). -/
theorem eq_zero_of_forall_two_pow_dvd {a : ℤ_[2]} (h : ∀ n, (2 : ℤ_[2]) ^ n ∣ a) : a = 0 := by
  by_contra ha
  have h1 := (PadicInt.mem_span_pow_iff_le_valuation a ha (a.valuation + 1)).1
    (by simpa [Ideal.mem_span_singleton] using h (a.valuation + 1))
  omega

/-- The stage ideals `(2^i, t^i)` tend to zero in `Λ`.  Kind: `PROVED`. -/
theorem stageIdeal_tendsToZero : IdealsTendToZero stageIdeal := by
  refine idealsTendToZero_of_antitone stageIdeal_antitone
    (fun n => AddSubgroup.isClosed_of_isOpen (stageIdeal n).toAddSubgroup (stageIdeal_isOpen n))
    fun f hf => ?_
  refine PowerSeries.ext fun k => ?_
  rw [map_zero]
  refine eq_zero_of_forall_two_pow_dvd fun n => ?_
  have hmem := mem_stageIdeal_iff.1 (hf (max n (k + 1))) k (by omega)
  exact (pow_dvd_pow 2 (le_max_left n (k + 1))).trans hmem

/-! ### The finite stages `A_i = (ℤ/2^i)[t]/t^i` -/

/-- The finite coefficient stage `A_i = (ℤ/2^iℤ)[t]/t^i` of line 2725.  Kind: definition. -/
abbrev StageA (i : ℕ) : Type :=
  Polynomial (ZMod (2 ^ i)) ⧸ Ideal.span {(Polynomial.X : Polynomial (ZMod (2 ^ i))) ^ i}

/-- A polynomial is congruent to its truncation below degree `i` modulo `t^i`.  Kind: `PROVED` (helper). -/
theorem X_pow_dvd_sub_trunc {A : Type*} [CommRing A] (i : ℕ) (p : Polynomial A) :
    (Polynomial.X : Polynomial A) ^ i ∣ p - trunc i (p : PowerSeries A) := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rw [Polynomial.coeff_sub, coeff_trunc]
  simp only [hd, ↓reduceIte, Polynomial.coeff_coe, sub_self]

/-- Truncation below degree `i`, as a ring hom `A[[t]] →+* A[t]/(t^i)`.  Kind: definition. -/
def truncQuot (A : Type*) [CommRing A] (i : ℕ) :
    PowerSeries A →+* Polynomial A ⧸ Ideal.span {(Polynomial.X : Polynomial A) ^ i} where
  toFun f := Ideal.Quotient.mk _ (trunc i f)
  map_one' := by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    have h := X_pow_dvd_sub_trunc i (1 : Polynomial A)
    rw [Polynomial.coe_one] at h
    rw [← neg_sub, Ideal.neg_mem_iff]
    exact Ideal.mem_span_singleton.2 h
  map_mul' f g := by
    rw [← map_mul, Ideal.Quotient.eq, ← trunc_trunc_mul_trunc, ← Polynomial.coe_mul, ← neg_sub,
      Ideal.neg_mem_iff]
    exact Ideal.mem_span_singleton.2 (X_pow_dvd_sub_trunc i _)
  map_zero' := by simp
  map_add' f g := by simp

/-- The reduction map `Λ → A_i`: reduce coefficients modulo `2^i` and truncate below `t^i`.
Kind: definition. -/
def stageMap (i : ℕ) : Lambda →+* StageA i :=
  (truncQuot (ZMod (2 ^ i)) i).comp (PowerSeries.map (PadicInt.toZModPow i))

/-- `Λ → A_i` is surjective.  Kind: `PROVED` (helper). -/
theorem stageMap_surjective (i : ℕ) : Function.Surjective (stageMap i) := by
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨PowerSeries.mk fun d => ((p.coeff d).val : ℤ_[2]), ?_⟩
  have hmap : PowerSeries.map (PadicInt.toZModPow i)
      (PowerSeries.mk fun d => ((p.coeff d).val : ℤ_[2])) = (p : PowerSeries (ZMod (2 ^ i))) := by
    refine PowerSeries.ext fun d => ?_
    rw [coeff_map, coeff_mk, Polynomial.coeff_coe, map_natCast, ZMod.natCast_zmod_val]
  show Ideal.Quotient.mk _ (trunc i (PowerSeries.map (PadicInt.toZModPow i)
      (PowerSeries.mk fun d => ((p.coeff d).val : ℤ_[2])))) = _
  rw [hmap, Ideal.Quotient.eq, ← neg_sub, Ideal.neg_mem_iff]
  exact Ideal.mem_span_singleton.2 (X_pow_dvd_sub_trunc i p)

/-- The kernel of `Λ → A_i` is the stage ideal `(2^i, t^i)`.  Kind: `PROVED`. -/
theorem ker_stageMap (i : ℕ) : RingHom.ker (stageMap i) = stageIdeal i := by
  ext f
  rw [RingHom.mem_ker, mem_stageIdeal_iff]
  show Ideal.Quotient.mk _ (trunc i (PowerSeries.map (PadicInt.toZModPow i) f)) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff]
  refine forall_congr' fun k => imp_congr_right fun hk => ?_
  rw [coeff_trunc]
  simp only [hk, ↓reduceIte]
  rw [coeff_map, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton,
    Nat.cast_ofNat]

/-- `stageEquiv`: `Λ/(2^i, t^i) ≃+* (ℤ/2^iℤ)[t]/t^i = A_i` (lines 2725, 2747).
Kind: `PROVED` (definition of a ring isomorphism). -/
def stageEquiv (i : ℕ) : Lambda ⧸ stageIdeal i ≃+* StageA i :=
  (Ideal.quotEquivOfEq (ker_stageMap i).symm).trans
    (RingHom.quotientKerEquivOfSurjective (stageMap_surjective i))

/-- Kind: `PROVED` (helper). -/
theorem stageEquiv_mk (i : ℕ) (f : Lambda) :
    stageEquiv i (Ideal.Quotient.mk (stageIdeal i) f) = stageMap i f := rfl

/-- The inner limit over `Λ` (lines 4401-4406, 4444-4447): for a nonprincipal ultrafilter `U`
and a sequence of matrices `M i` over `Λ` (lifts of stage-`i` data), the entrywise ultralimit
`ulimMat U M` is a compatible limit at every coefficient precision `(2^n, t^n)`, it is the
unique such matrix over `Λ`, and it does not depend on the choice of lifts.
Kind: `PROVED`. -/
theorem lambda_inner_limit {m k : Type*} [Finite m] [Finite k] {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (M : ℕ → Matrix m k Lambda) :
    (∀ n, ∀ᶠ i in (U : Filter ℕ), ∀ a b, M i a b - ulimMat U M a b ∈ stageIdeal n) ∧
    (∀ A : Matrix m k Lambda,
      (∀ n, ∀ᶠ i in (U : Filter ℕ), ∀ a b, M i a b - A a b ∈ stageIdeal n) → A = ulimMat U M) ∧
    (∀ M' : ℕ → Matrix m k Lambda,
      (∀ᶠ i in (U : Filter ℕ), ∀ a b, M' i a b - M i a b ∈ stageIdeal i) →
        ulimMat U M' = ulimMat U M) := by
  refine ⟨fun n => ?_, fun A hA => ?_, fun M' hM' => ulimMat_eq_of_sub_mem stageIdeal_tendsToZero hU hM'⟩
  · exact eventually_all.2 fun a => eventually_all.2 fun b =>
      eventually_sub_ulim_mem (stageIdeal_isOpen n) U (fun i => M i a b)
  · refine Matrix.ext fun a b => ?_
    refine ((ulim_eq_iff_forall_eventually_sub_mem stageIdeal_tendsToZero stageIdeal_isOpen U
      (fun i => M i a b) (A a b)).2 fun n => ?_).symm
    exact (hA n).mono fun i hi => hi a b

/-- `polynomial_identity_survives` over `Λ`, stage form: an integer polynomial identity between
the entries that holds in the finite stages `A_i = Λ/(2^i, t^i)` for `U`-many `i` holds exactly
for the ultralimit entries over `Λ`.  Lines 4447-4448.  Kind: `PROVED`. -/
theorem lambda_polynomial_identity_survives {σ : Type*} {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (x : ℕ → σ → Lambda) (P : MvPolynomial σ ℤ)
    (h : ∀ᶠ i in (U : Filter ℕ), MvPolynomial.eval₂ (Int.castRingHom (Lambda ⧸ stageIdeal i))
      (fun s => Ideal.Quotient.mk (stageIdeal i) (x i s)) P = 0) :
    MvPolynomial.eval₂ (Int.castRingHom Lambda) (ulimVec U x) P = 0 :=
  polynomial_identity_survives_of_stages stageIdeal_tendsToZero hU x P h

/-- `polynomial_identity_survives` over `Λ`, with the identity assumed in the actual finite
stages `A_i = (ℤ/2^iℤ)[t]/t^i` (line 2725) for the reductions `stageMap i (x i s)` of the lifts,
for `U`-many `i`.  Lines 4444-4448.  Kind: `PROVED`. -/
theorem lambda_polynomial_identity_survives_of_A {σ : Type*} {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (x : ℕ → σ → Lambda) (P : MvPolynomial σ ℤ)
    (h : ∀ᶠ i in (U : Filter ℕ), MvPolynomial.eval₂ (Int.castRingHom (StageA i))
      (fun s => stageMap i (x i s)) P = 0) :
    MvPolynomial.eval₂ (Int.castRingHom Lambda) (ulimVec U x) P = 0 := by
  refine polynomial_identity_survives stageIdeal_tendsToZero hU x P (h.mono fun i hi => ?_)
  rw [← ker_stageMap, RingHom.mem_ker, MvPolynomial.eval₂_comp_left,
    show (stageMap i).comp (Int.castRingHom Lambda) = Int.castRingHom (StageA i) from
      RingHom.ext_int _ _]
  exact hi

/-- Independence of lifts over `Λ`: lifts `x i, y i : σ → Λ` of the same stage data in `A_i`
(for `U`-many `i`) have the same ultralimit.  Lines 4444-4447.  Kind: `PROVED`. -/
theorem lambda_ulimVec_eq_of_A {σ : Type*} {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    {x y : ℕ → σ → Lambda}
    (h : ∀ᶠ i in (U : Filter ℕ), ∀ s, stageMap i (x i s) = stageMap i (y i s)) :
    ulimVec U x = ulimVec U y := by
  refine ulimVec_eq_of_sub_mem stageIdeal_tendsToZero hU (h.mono fun i hi s => ?_)
  rw [← ker_stageMap, RingHom.mem_ker, map_sub, hi s, sub_self]

end Lambda

/-! ## Part 3: the identities (5.2) in the inner limit -/

section InnerCocycle

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R]
variable {G : ℕ → Type*} [∀ i, Group (G i)] {n : Type*}

/-- `ρ∞ g = ulim_U ρ_i(g_i)` on the product group `Γ = ∏ i, G i` (line 4674: "`Γ_K = ∏_i G_K`").
Kind: definition.
DEPARTURE (generality/form): the stage groups `G i` may vary with `i` (for `G i = G_K` this is
`Γ_K = ∏_i G_K`); the simultaneous complex conjugation of line 4675 is not needed for (5.2) and
is not included; the retained cochain maps are recorded through their evaluations, a matrix
`ρ_i(g)` and a cochain value `c_i(g)` on a free module of fixed rank `n` (ranks fixed on a set
in `U` by `bounded_ranks_fixed`). -/
def rhoInf (U : Ultrafilter ℕ) (ρ : ∀ i, G i → Matrix n n R) (g : ∀ i, G i) : Matrix n n R :=
  ulimMat U (fun i => ρ i (g i))

/-- `c∞ g = ulim_U c_i(g_i)`, the ultralimit of a sequence of 1-cochains evaluated at a sequence
`g = (g_i)` (lines 4675-4679).  Kind: definition. -/
def cInf (U : Ultrafilter ℕ) (c : ∀ i, G i → n → R) (g : ∀ i, G i) : n → R :=
  ulimVec U (fun i => c i (g i))

/-- `ρ∞` is multiplicative when the `ρ_i` are multiplicative modulo `I i` for `U`-many `i`.
Lines 4674-4681.  Kind: `PROVED`. -/
theorem rhoInf_mul [Fintype n] {I : ℕ → Ideal R} (hI : IdealsTendToZero I) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (ρ : ∀ i, G i → Matrix n n R)
    (hmul : ∀ᶠ i in (U : Filter ℕ), ∀ g h : G i, ∀ a b,
      (ρ i (g * h) - ρ i g * ρ i h) a b ∈ I i) (g h : ∀ i, G i) :
    rhoInf U ρ (g * h) = rhoInf U ρ g * rhoInf U ρ h := by
  unfold rhoInf
  rw [← ulimMat_mul]
  exact ulimMat_eq_of_sub_mem hI hU (hmul.mono fun i hi a b => hi (g i) (h i) a b)

/-- `ρ∞(1) = 1` when `ρ_i(1) ≡ 1 (mod I i)` for `U`-many `i`.  Lines 4674-4681.
Kind: `PROVED`. -/
theorem rhoInf_one [DecidableEq n] {I : ℕ → Ideal R} (hI : IdealsTendToZero I) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (ρ : ∀ i, G i → Matrix n n R)
    (hone : ∀ᶠ i in (U : Filter ℕ), ∀ a b, (ρ i 1 - 1 : Matrix n n R) a b ∈ I i) :
    rhoInf U ρ 1 = 1 := by
  unfold rhoInf
  rw [← ulimMat_one (R := R) U]
  exact ulimMat_eq_of_sub_mem hI hU hone

/-- `ρ∞ : Γ →* GL`-type monoid hom `∏ i, G i →* Matrix n n R` ("One fixed ultrafilter supplies
these identities for all sequences", line 4681).  No continuity on a single original Galois
group is asserted (lines 4683-4684).  Kind: `PROVED`. -/
def rhoInfHom [Fintype n] [DecidableEq n] {I : ℕ → Ideal R} (hI : IdealsTendToZero I) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (ρ : ∀ i, G i → Matrix n n R)
    (hmul : ∀ᶠ i in (U : Filter ℕ), ∀ g h : G i, ∀ a b,
      (ρ i (g * h) - ρ i g * ρ i h) a b ∈ I i)
    (hone : ∀ᶠ i in (U : Filter ℕ), ∀ a b, (ρ i 1 - 1 : Matrix n n R) a b ∈ I i) :
    (∀ i, G i) →* Matrix n n R where
  toFun := rhoInf U ρ
  map_one' := rhoInf_one hI hU ρ hone
  map_mul' := rhoInf_mul hI hU ρ hmul

/-- Kind: `PROVED` (helper). -/
theorem rhoInfHom_apply [Fintype n] [DecidableEq n] {I : ℕ → Ideal R} (hI : IdealsTendToZero I) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) (ρ : ∀ i, G i → Matrix n n R) hmul hone (g : ∀ i, G i) :
    rhoInfHom hI hU ρ hmul hone g = rhoInf U ρ g := rfl

/-- `crossed_homomorphism_inner_limit` (5.2), line 4679 `e^2_{g,h} d = ρ(g)e^1_h - e^1_{gh} + e^1_g`,
and lines 4681-4684: if the crossed-homomorphism defects `ρ_i(g) c_i(h) - c_i(gh) + c_i(g)` of the
stage cochains lie in `I i` for `U`-many `i` (uniformly in `g, h`; the differentials tend to
zero), then `c∞` is an exact crossed homomorphism of the product group `Γ = ∏ i, G i`:
`ρ∞(g) c∞(h) - c∞(gh) + c∞(g) = 0` for all sequences `g = (g_i)`, `h = (h_i)`.
"A cycle therefore defines an abstract crossed homomorphism of the product group."  We do not
assert that its restriction to one original Galois group is a continuous pointwise limit.
Kind: `PROVED`. -/
theorem crossed_homomorphism_inner_limit [Fintype n] {I : ℕ → Ideal R} (hI : IdealsTendToZero I)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (ρ : ∀ i, G i → Matrix n n R)
    (c : ∀ i, G i → n → R)
    (hcoc : ∀ᶠ i in (U : Filter ℕ), ∀ g h : G i, ∀ a,
      (ρ i g *ᵥ c i h - c i (g * h) + c i g) a ∈ I i) (g h : ∀ i, G i) :
    rhoInf U ρ g *ᵥ cInf U c h - cInf U c (g * h) + cInf U c g = 0 := by
  have h0 : ulimVec U (fun i => ρ i (g i) *ᵥ c i (h i) - c i (g i * h i) + c i (g i)) = 0 := by
    rw [← ulimVec_zero (R := R) U]
    exact ulimVec_eq_of_sub_mem hI hU (hcoc.mono fun i hi a => by simpa using hi (g i) (h i) a)
  rw [ulimVec_add U (fun i => ρ i (g i) *ᵥ c i (h i) - c i (g i * h i)) (fun i => c i (g i)),
    ulimVec_sub U (fun i => ρ i (g i) *ᵥ c i (h i)) (fun i => c i (g i * h i)),
    ulimVec_mulVec] at h0
  exact h0

omit [∀ i, Group (G i)] in
/-- The first identity of (5.2), line 4679 `e^1_g d = (ρ(g) - 1) e^0`, in the inner limit: if
the stage cochains `c_i` agree modulo `I i` with the coboundaries `g ↦ ρ_i(g) w_i - w_i` of
0-cochains `w_i` for `U`-many `i`, then `c∞(g) = ρ∞(g) w∞ - w∞` exactly.  Kind: `PROVED`. -/
theorem coboundary_inner_limit [Fintype n] {I : ℕ → Ideal R} (hI : IdealsTendToZero I)
    {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite) (ρ : ∀ i, G i → Matrix n n R)
    (c : ∀ i, G i → n → R) (w : ℕ → n → R)
    (hcob : ∀ᶠ i in (U : Filter ℕ), ∀ g : G i, ∀ a, c i g a - (ρ i g *ᵥ w i - w i) a ∈ I i)
    (g : ∀ i, G i) :
    cInf U c g = rhoInf U ρ g *ᵥ ulimVec U w - ulimVec U w := by
  unfold cInf rhoInf
  rw [ulimVec_eq_of_sub_mem hI hU (y := fun i => ρ i (g i) *ᵥ w i - w i)
      (hcob.mono fun i hi a => hi (g i) a),
    ulimVec_sub U (fun i => ρ i (g i) *ᵥ w i) w, ulimVec_mulVec]

end InnerCocycle

/-! ## Satisfiability of the hypotheses -/

section Examples

open scoped PowerSeries.WithPiTopology

/-- A nonprincipal ultrafilter on the coefficient stages exists. -/
example : ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) ≤ cofinite := hyperfilter_le_cofinite

/-- The hypotheses of Part 1 are met by `Λ = ℤ₂[[t]]` and its stage ideals. -/
example : CompactSpace Lambda ∧ T2Space Lambda ∧ IsTopologicalRing Lambda ∧
    IdealsTendToZero stageIdeal ∧ ∀ n, IsOpen (stageIdeal n : Set Lambda) :=
  ⟨inferInstance, lambda_t2Space, lambda_isTopologicalRing, stageIdeal_tendsToZero,
    stageIdeal_isOpen⟩

/-- A genuinely approximate identity: `(1 + 2^i) * 1 ≡ 1 (mod (2^i, t^i))`; the hypothesis of
`polynomial_identity_survives` holds and the identity survives exactly. -/
example : ∀ᶠ i in ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ),
    MvPolynomial.eval₂ (Int.castRingHom Lambda) (![1 + 2 ^ i, 1] : Fin 2 → Lambda)
      (MvPolynomial.X 0 * MvPolynomial.X 1 - 1) ∈ stageIdeal i := by
  refine Eventually.of_forall fun i => ?_
  simp only [MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_one, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
    add_sub_cancel_left]
  exact Ideal.subset_span (Set.mem_insert _ _)

/-- The ultralimit of `2^i` in `Λ` is `0`. -/
example : ulim (hyperfilter ℕ) (fun i => (2 : Lambda) ^ i) = 0 :=
  ulim_eq_zero_of_mem stageIdeal_tendsToZero hyperfilter_le_cofinite
    (Eventually.of_forall fun _ => Ideal.subset_span (Set.mem_insert _ _))

/-- The hypotheses of `contraction_survives` are satisfiable (the identity contraction:
`d = d_C = 0`, `i = p = 1`, `h = 0`). -/
example : ∀ᶠ j in ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ), ∀ a b,
    ((1 : Matrix (Fin 2) (Fin 2) Lambda) - 1 * 1 - (0 * 0 + 0 * 0) : Matrix (Fin 2) (Fin 2) Lambda)
      a b ∈ stageIdeal j :=
  Eventually.of_forall fun _ _ _ => by simp

/-- The hypotheses of Part 3 are satisfiable: the trivial representations give a monoid hom
`ρ∞` of the product group. -/
example (G : ℕ → Type) [∀ i, Group (G i)] : (∀ i, G i) →* Matrix (Fin 2) (Fin 2) Lambda :=
  rhoInfHom stageIdeal_tendsToZero hyperfilter_le_cofinite (fun _ _ => 1)
    (Eventually.of_forall fun _ _ _ _ _ => by simp) (Eventually.of_forall fun _ _ _ => by simp)

/-- The crossed-homomorphism hypothesis of Part 3 is satisfiable with nonzero stage defects:
trivial `ρ_i` and the constant cochains `c_i(g) = (2^i, 2^i)`, whose defect is `2^i`. -/
example (G : ℕ → Type) [∀ i, Group (G i)] (g h : ∀ i, G i) :
    let ρ : ∀ i, G i → Matrix (Fin 2) (Fin 2) Lambda := fun _ _ => 1
    let c : ∀ i, G i → Fin 2 → Lambda := fun i _ _ => 2 ^ i
    rhoInf (hyperfilter ℕ) ρ g *ᵥ cInf (hyperfilter ℕ) c h - cInf (hyperfilter ℕ) c (g * h) +
      cInf (hyperfilter ℕ) c g = 0 := by
  intro ρ c
  refine crossed_homomorphism_inner_limit stageIdeal_tendsToZero hyperfilter_le_cofinite ρ c
    (Eventually.of_forall fun i _ _ _ => ?_) g h
  simp only [ρ, c, Matrix.one_mulVec, sub_self, zero_add]
  exact Ideal.subset_span (Set.mem_insert _ _)

end Examples

end

end ZInQ.Manuscript.RC.Limits
