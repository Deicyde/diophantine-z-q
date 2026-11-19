import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageGlobal
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedTransport
import ZInQKernel.Contrib.OneProof.RC.Limits.GradedFiniteFree

/-!
# Lane RC31, round 3: non-vacuity of the stage interfaces on an explicit perfect complex

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451), with the split
local model `L = D⁰ ⊕ (F ⊕ S)[−1] ⊕ D²[−2]` (tex 4860–4868).

Over any commutative ring `A`: the complex `X₀` (`A²` in degrees `0` and `1`, zero differentials),
its identity graded model `R₀`, the pairing data `P₀` (localization onto `D⁰` and the finite part
`F`, zero global trace pairing, hyperbolic local pairing on `F ⊕ S`), and an explicit
`StageMatrixDiagram A exRank` whose model data are exactly `modelRes R₀ P₀`, `modelGlob R₀ P₀`,
`P₀.loc`, with explicit reverse map and homotopies. Its forward matrix in degree `0` is the
identity (nonzero over a nontrivial ring). The complex is flat, bounded, and has finite residual
cohomology over a local ring. The same holds over every coefficient stage `A_i`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open CategoryTheory Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit (splitLocalComplex splitLocalTerms Vec2 Coords)
open ZInQ.Manuscript.RC.Limits (GRetract GradedModel matCx residualCohomologyAt)

/-- **The ranks of the example** (non-vacuity, tex 4391–4451): `2` in degrees `0` and `1`, `0`
otherwise; by pattern matching, so that `Fin (exRank 0)` is `Fin 2` definitionally. Kind:
definition. -/
def exRank : ℤ → ℕ
  | .ofNat 0 => 2
  | .ofNat 1 => 2
  | _ => 0

/-- The example ranks vanish outside degrees `0` and `1` (tex 4391–4451). Kind: PROVED. -/
theorem exRank_eq_zero (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) : exRank n = 0 := by
  rcases n with (_ | _ | m) | m
  · exact absurd rfl h0
  · exact absurd rfl h1
  · rfl
  · rfl

/-- The example coordinates are empty outside degrees `0` and `1` (tex 4391–4451). Kind: PROVED. -/
theorem exRank_isEmpty (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) : IsEmpty (Fin (exRank n)) :=
  ⟨fun i => by
    have h : (i : ℕ) < exRank n := i.2
    have h' := exRank_eq_zero n h0 h1
    omega⟩

/-- The coordinates of the split model are empty outside degrees `0`, `1`, `2` (split model tex
4860–4868). Kind: PROVED. -/
theorem exLIdx_isEmpty (n : ℤ) (h : n < 0 ∨ 2 < n) : IsEmpty (lIdx n) := by
  rcases n with (_ | _ | _ | m) | m
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact inferInstanceAs (IsEmpty Empty)
  · exact inferInstanceAs (IsEmpty Empty)

/-- The coordinates of the compactly supported example complex are empty outside degrees `0` to `3`
(tex 4391–4451; split model tex 4860–4868). Kind: PROVED. -/
theorem exCIdx_isEmpty (n : ℤ) (h : n < 0 ∨ 3 < n) : IsEmpty (cIdxOf exRank n) := by
  have h1 := exRank_isEmpty n (by omega) (by omega)
  have h2 := exLIdx_isEmpty (n - 1) (by omega)
  exact isEmpty_sum.mpr ⟨h1, h2⟩

variable (A : Type) [CommRing A]

/-- **The model differentials of the example**: all zero (tex 4391–4451). Kind: definition. -/
def exD : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (exRank b)) (Fin (exRank a)) A :=
  fun _ _ _ => 0

/-- `d² = 0` for the zero differentials (tex 4391–4451). Kind: PROVED. -/
theorem exD_sq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c),
    exD A b c hbc * exD A a b hab = 0 :=
  fun _ _ _ _ _ => Matrix.zero_mul _

/-- **The example complex** `X₀`: `A²` in degrees `0` and `1`, zero elsewhere, zero differentials; a
perfect complex of free modules (tex 4391–4451). Kind: definition. -/
abbrev exCx : GCx A := matCx exRank (exD A) (exD_sq A)

/-- **The example graded model** `R₀`: the complex as its own graded finite free model via the
identity retract (tex 4391–4451). Kind: definition. -/
abbrev exModel : GradedModel (exCx A) := matCx.gradedModel exRank (exD A) (exD_sq A)

/-- The components of the example localization: the identity onto `L⁰ = A²` in degree `0`, `x ↦ (x,
0)` into the finite part of `L¹ = F ⊕ S` in degree `1`, zero elsewhere (split model tex 4860–4868).
Kind: definition. -/
def exResLin : ∀ n : ℤ, (Fin (exRank n) → A) →ₗ[A] (splitLocalComplex A).X n
  | .ofNat 0 => LinearMap.id
  | .ofNat 1 => LinearMap.inl A (Vec2 A) (Vec2 A)
  | _ => 0

/-- **The example localization** `X₀ → L` as a chain map (both complexes have zero differentials)
(tex 4391–4451; split model tex 4860–4868). Kind: definition (PROVED chain property). -/
def exRes : GHom (exCx A) (splitLocalComplex A) where
  f a b h := by
    subst h
    exact exResLin A a
  comm i i₁ j j₁ hij h₁ h₂ hj x := by
    subst hij hj h₁
    exact (congrArg (exResLin A (i + 1))
      (Matrix.zero_mulVec (x : Fin (exRank i) → A))).trans (map_zero _)

/-- **The hyperbolic matrix** `[[0, 1], [1, 0]]` on `F ⊕ S` (the local pairing in degree `1` of the
split model, split model tex 4860–4868). Kind: definition. -/
def exHyp : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) A := Matrix.fromBlocks 0 1 1 0

/-- **The example local pairing**: `1` in degrees `(0, 2)` and `(2, 0)`, the hyperbolic matrix in
degrees `(1, 1)`, zero elsewhere (split model tex 4860–4868). Kind: definition. -/
def exLoc : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) A
  | .ofNat 0, .ofNat 2 => (1 : Matrix (Fin 2) (Fin 2) A)
  | .ofNat 1, .ofNat 1 => exHyp A
  | .ofNat 2, .ofNat 0 => (1 : Matrix (Fin 2) (Fin 2) A)
  | _, _ => 0

/-- The finite part is isotropic for the hyperbolic pairing (split model tex 4860–4868). Kind:
PROVED. -/
theorem exHyp_iso (x y : Fin 2 → A) :
    Sum.elim x 0 ⬝ᵥ (exHyp A *ᵥ Sum.elim y 0) = 0 := by
  simp [exHyp, dotProduct, Fintype.sum_sum_type, Matrix.mulVec, fromBlocks]

/-- The example complex vanishes outside degrees `0` and `1` (tex 4391–4451). Kind: PROVED. -/
theorem exCx_eq_zero (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) (x : (exCx A).X n) : x = 0 := by
  have := exRank_isEmpty n h0 h1
  exact funext fun i => isEmptyElim i

/-- **The example stage pairing data** `P₀`: localization `exRes`, zero global trace pairing (no `a
+ b = 3` has both ranks nonzero), local pairing `exLoc`; reciprocity holds since the finite part is
isotropic and the differentials vanish (tex 4391–4451; split model tex 4860–4868). Kind: definition
(PROVED reciprocity). -/
def exPair : StagePairingInput (exCx A) where
  res := exRes A
  glob _ _ _ := 0
  loc := exLoc A
  recip a b h x y := by
    simp only [LinearMap.zero_apply, smul_zero, add_zero]
    rcases (show a = 1 ∨ a ≠ 0 ∧ a ≠ 1 ∨ a = 0 by omega) with rfl | ha | rfl
    · obtain rfl : b = 1 := by omega
      rw [locForm_apply]
      exact (neg_eq_zero.mpr (exHyp_iso A x y)).symm
    · rw [exCx_eq_zero A a ha.1 ha.2 x, map_zero, map_zero, LinearMap.zero_apply, neg_zero]
    · rw [exCx_eq_zero A b (by omega) (by omega) y, map_zero, map_zero, neg_zero]


/-- The localization matrix in degree `1`: `x ↦ (x, 0)` into `F ⊕ S` (split model tex 4860–4868).
Kind: definition. -/
def exRes1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) A := Matrix.fromRows 1 0

/-- **The localization matrices of the example**: `1` in degree `0`, `exRes1` in degree `1`, zero
elsewhere (tex 4391–4451; split model tex 4860–4868). Kind: definition. -/
def exResM : ∀ n : ℤ, Matrix (lIdx n) (Fin (exRank n)) A
  | .ofNat 0 => (1 : Matrix (Fin 2) (Fin 2) A)
  | .ofNat 1 => exRes1 A
  | _ => 0

/-- The (zero) global trace pairing matrices of the example (tex 4391–4451). Kind: definition. -/
def exGlob : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (exRank a)) (Fin (exRank b)) A :=
  fun _ _ _ => 0

/-- The model localization of the example in degree `0` is the identity (tex 4391–4451). Kind:
PROVED. -/
theorem exModelRes_zero :
    @Eq (Matrix (Fin 2) (Fin 2) A) (modelRes (exModel A) (exPair A) 0) 1 := by
  refine Matrix.ext fun (i : Fin 2) (j : Fin 2) => ?_
  change (Pi.single j 1 : Fin 2 → A) i = (1 : Matrix (Fin 2) (Fin 2) A) i j
  rw [Matrix.one_apply, Pi.single_apply]

/-- The model localization of the example in degree `1` is `exRes1` (tex 4391–4451; split model tex
4860–4868). Kind: PROVED. -/
theorem exModelRes_one :
    @Eq (Matrix (Fin 2 ⊕ Fin 2) (Fin 2) A) (modelRes (exModel A) (exPair A) 1) (exRes1 A) := by
  refine Matrix.ext fun (i : Fin 2 ⊕ Fin 2) (j : Fin 2) => ?_
  rcases i with i | i
  · change (Pi.single j 1 : Fin 2 → A) i = exRes1 A (Sum.inl i) j
    rw [exRes1, Matrix.fromRows_apply_inl, Matrix.one_apply, Pi.single_apply]
  · rfl

/-- **The model localization of the example** is `exResM` in every degree (tex 4391–4451). Kind:
PROVED. -/
theorem exModelRes_eq : modelRes (exModel A) (exPair A) = exResM A := by
  funext n
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n < 0 ∨ 2 < n by omega) with rfl | rfl | rfl | h | h
  · exact exModelRes_zero A
  · exact exModelRes_one A
  · ext i j
    exact ((exRank_isEmpty 2 (by decide) (by decide)).false j).elim
  · ext i j
    exact ((exLIdx_isEmpty n (by omega)).false i).elim
  · ext i j
    exact ((exLIdx_isEmpty n (by omega)).false i).elim

/-- The model trace pairing of the example is zero (tex 4391–4451). Kind: PROVED. -/
theorem exModelGlob_eq : modelGlob (exModel A) (exPair A) = exGlob A := by
  funext a b h
  ext i j
  rfl

/-- The forward matrix in degree `0`: the identity onto the `D²` coordinates (tex 4391–4451). Kind:
definition. -/
def exF0 : Matrix (Fin 0 ⊕ Fin 2) (Fin 2) A := Matrix.fromRows 0 1

/-- The forward matrix in degree `1`: `x ↦ (0, −x)` into the singular part (tex 4391–4451). Kind:
definition. -/
def exF1 : Matrix (Fin 0 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 2) A := Matrix.fromRows 0 (Matrix.fromRows 0 (-1))

/-- The dual differential from degree `1` to `2`: `(f, s) ↦ (f, 0)` (tex 4391–4451). Kind:
definition. -/
def exDD12 : Matrix (Fin 2 ⊕ Fin 2) (Fin 0 ⊕ (Fin 2 ⊕ Fin 2)) A :=
  Matrix.fromBlocks 0 (Matrix.fromCols 1 0) 0 0

/-- The dual differential from degree `2` to `3`: `(u, w) ↦ −w` (tex 4391–4451). Kind: definition.
-/
def exDD23 : Matrix (Fin 2 ⊕ Empty) (Fin 2 ⊕ Fin 2) A := Matrix.fromBlocks 0 (-1) 0 0

/-- The reverse map in degree `0`: the identity from the `D²` coordinates (tex 4391–4451). Kind:
definition. -/
def exRev0 : Matrix (Fin 2) (Fin 0 ⊕ Fin 2) A := Matrix.fromCols 0 1

/-- The reverse map in degree `1`: `(f, s) ↦ −s` (tex 4391–4451). Kind: definition. -/
def exRev1 : Matrix (Fin 2) (Fin 0 ⊕ (Fin 2 ⊕ Fin 2)) A :=
  Matrix.fromCols 0 (Matrix.fromCols 0 (-1))

/-- The target homotopy from degree `2` to `1`: `(u, w) ↦ (−u, 0)` (tex 4391–4451). Kind:
definition. -/
def exT21 : Matrix (Fin 0 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 2 ⊕ Fin 2) A :=
  Matrix.fromRows 0 (Matrix.fromBlocks (-1) 0 0 0)

/-- The target homotopy from degree `3` to `2`: `t ↦ (0, t)` (tex 4391–4451). Kind: definition. -/
def exT32 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Empty) A := Matrix.fromBlocks 0 0 1 0

/-- **The reverse map of the example**: `exRev0`, `exRev1` in degrees `0`, `1`, zero elsewhere (tex
4391–4451). Kind: definition. -/
def exRev : ∀ a : ℤ, Matrix (Fin (exRank a)) (cIdxOf exRank (3 - a)) A
  | .ofNat 0 => exRev0 A
  | .ofNat 1 => exRev1 A
  | _ => 0

/-- The source homotopy of the example: zero (tex 4391–4451). Kind: definition. -/
def exSrc (a b : ℤ) (_ : b + 1 = a) : Matrix (Fin (exRank b)) (Fin (exRank a)) A := 0

/-- The target homotopy of the example by degrees: `exT21`, `exT32`, zero elsewhere (tex 4391–4451).
Kind: definition. -/
def exTgtAux : ∀ a b : ℤ, Matrix (cIdxOf exRank (3 - b)) (cIdxOf exRank (3 - a)) A
  | .ofNat 2, .ofNat 1 => exT21 A
  | .ofNat 3, .ofNat 2 => exT32 A
  | _, _ => 0

/-- **The target homotopy of the example** (tex 4391–4451). Kind: definition. -/
def exTgt (a b : ℤ) (_ : b + 1 = a) : Matrix (cIdxOf exRank (3 - b)) (cIdxOf exRank (3 - a)) A :=
  exTgtAux A a b

/-- The forward matrix of the example in degree `0` (tex 4391–4451). Kind: PROVED. -/
theorem ex_fwd0 : forwardMatOf (exGlob A) (exLoc A) (exResM A) 0 = exF0 A := by
  unfold forwardMatOf
  change Matrix.fromRows (0 : Matrix (Fin 2) (Fin 0) A)ᵀ
    (((sgn 0 : ℤ) : A) • ((1 : Matrix (Fin 2) (Fin 2) A)ᵀ * (1 : Matrix (Fin 2) (Fin 2) A))) =
    exF0 A
  ext i j
  rcases i with i | i
  · exact i.elim0
  · fin_cases i <;> fin_cases j <;> simp [exF0, sgn]

/-- The forward matrix of the example in degree `1` (tex 4391–4451). Kind: PROVED. -/
theorem ex_fwd1 : forwardMatOf (exGlob A) (exLoc A) (exResM A) 1 = exF1 A := by
  unfold forwardMatOf
  change Matrix.fromRows (0 : Matrix (Fin 2) (Fin 0) A)ᵀ
    (((sgn 1 : ℤ) : A) • ((exHyp A)ᵀ * exRes1 A)) = exF1 A
  rw [sgn_one]
  ext i j
  rcases i with i | i | i
  · exact i.elim0
  · fin_cases i <;> fin_cases j <;>
      simp [exF1, exHyp, exRes1, Matrix.mul_apply, Fintype.sum_sum_type]
  · fin_cases i <;> fin_cases j <;>
      simp [exF1, exHyp, exRes1, Matrix.mul_apply, Fintype.sum_sum_type]

/-- The dual differential of the example from degree `0` to `1` is zero (tex 4391–4451). Kind:
PROVED. -/
theorem ex_dd01 : dualDiffMatOf (exD A) (exResM A) 0 (0 + 1) rfl = 0 := by
  unfold dualDiffMatOf compactDiffMatOf
  change (-((sgn 0 : ℤ) : A)) • (Matrix.fromBlocks (0 : Matrix (Fin 0) (Fin 0) A)
    (0 : Matrix (Fin 0) (Fin 2 ⊕ Fin 2) A) (0 : Matrix (Fin 2) (Fin 0) A)
    (0 : Matrix (Fin 2) (Fin 2 ⊕ Fin 2) A))ᵀ = 0
  simp

/-- The dual differential of the example from degree `1` to `2` (tex 4391–4451). Kind: PROVED. -/
theorem ex_dd12 : dualDiffMatOf (exD A) (exResM A) 1 (1 + 1) rfl = exDD12 A := by
  unfold dualDiffMatOf compactDiffMatOf
  change (-((sgn 1 : ℤ) : A)) • (Matrix.fromBlocks (0 : Matrix (Fin 0) (Fin 2) A)
    (0 : Matrix (Fin 0) (Fin 2) A) (exRes1 A) (0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) A))ᵀ =
    exDD12 A
  rw [sgn_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j | j
  all_goals first
    | exact j.elim0
    | (fin_cases i <;> fin_cases j <;> simp [exDD12, exRes1])

/-- The dual differential of the example from degree `2` to `3` (tex 4391–4451). Kind: PROVED. -/
theorem ex_dd23 : dualDiffMatOf (exD A) (exResM A) 2 (2 + 1) rfl = exDD23 A := by
  unfold dualDiffMatOf compactDiffMatOf
  change (-((sgn 2 : ℤ) : A)) • (Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) A)
    (0 : Matrix (Fin 2) Empty A) (1 : Matrix (Fin 2) (Fin 2) A) (0 : Matrix (Fin 2) Empty A))ᵀ =
    exDD23 A
  rw [sgn_two]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals first
    | exact i.elim
    | (fin_cases i <;> fin_cases j <;> simp [exDD23])


/-- A matrix product through an empty index is zero (tex 4391–4451). Kind: PROVED. -/
theorem matrix_mul_eq_zero_of_isEmpty {l n m : Type} [Fintype n] [IsEmpty n] (M : Matrix l n A)
    (N : Matrix n m A) : M * N = 0 := by
  ext i j
  simp [Matrix.mul_apply]

/-- The first homotopy-inverse identity in degree `0`, explicitly (tex 4391–4451). Kind: PROVED. -/
theorem ex_src0c : exRev0 A * exF0 A - 1 = 0 := by
  rw [sub_eq_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exRev0, exF0, Matrix.mul_apply]

/-- The first homotopy-inverse identity in degree `1`, explicitly (tex 4391–4451). Kind: PROVED. -/
theorem ex_src1c : exRev1 A * exF1 A - 1 = 0 := by
  rw [sub_eq_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exRev1, exF1, Matrix.mul_apply, Fintype.sum_sum_type]

/-- The second homotopy-inverse identity in degree `0`, explicitly (tex 4391–4451). Kind: PROVED. -/
theorem ex_tgt0c : exF0 A * exRev0 A - 1 = 0 := by
  rw [sub_eq_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals first
    | exact i.elim0
    | exact j.elim0
    | (fin_cases i <;> fin_cases j <;>
        simp [exRev0, exF0, Matrix.mul_apply])

/-- The second homotopy-inverse identity in degree `1`, explicitly (tex 4391–4451). Kind: PROVED. -/
theorem ex_tgt1c : exF1 A * exRev1 A - exT21 A * exDD12 A - 1 = 0 := by
  rw [sub_eq_zero]
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j
  all_goals first
    | exact i.elim0
    | exact j.elim0
    | (fin_cases i <;> fin_cases j <;>
        simp [exRev1, exF1, exT21, exDD12, Matrix.mul_apply, Fintype.sum_sum_type])

/-- The second homotopy-inverse identity in degree `2`, explicitly (tex 4391–4451). Kind: PROVED. -/
theorem ex_tgt2c : -(exT32 A * exDD23 A) - exDD12 A * exT21 A - 1 = 0 := by
  rw [sub_eq_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    fin_cases i <;> fin_cases j <;>
      simp [exT32, exDD23, exT21, exDD12, Matrix.mul_apply, Fintype.sum_sum_type]

/-- The second homotopy-inverse identity in degree `3`, explicitly (tex 4391–4451). Kind: PROVED. -/
theorem ex_tgt3c : -(exDD23 A * exT32 A) - 1 = 0 := by
  rw [sub_eq_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals first
    | exact i.elim
    | exact j.elim
    | (fin_cases i <;> fin_cases j <;>
        simp [exT32, exDD23, Matrix.mul_apply, Fintype.sum_sum_type])

/-- The reverse map of the example is a chain map, in every degree (tex 4391–4451). Kind: PROVED. -/
theorem ex_chain (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (exRank n)) A) (hRk : Rk = exResM A)
    (a : ℤ) : exRev A (a + 1) * dualDiffMatOf (exD A) Rk a (a + 1) rfl -
      exD A a (a + 1) rfl * exRev A a = 0 := by
  subst hRk
  rw [show exD A a (a + 1) rfl = 0 from rfl, Matrix.zero_mul, sub_zero]
  rcases (show a = 0 ∨ a < 0 ∨ 0 < a by omega) with rfl | h | h
  · rw [ex_dd01, Matrix.mul_zero]
  · ext i j
    exact ((exCIdx_isEmpty (3 - a) (by omega)).false j).elim
  · ext i j
    exact ((exRank_isEmpty (a + 1) (by omega) (by omega)).false i).elim

/-- The first homotopy-inverse identity of the example, in every degree (tex 4391–4451). Kind:
PROVED. -/
theorem ex_src (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (exRank a)) (Fin (exRank b)) A)
    (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (exRank n)) A) (hMbg : Mbg = exGlob A)
    (hRk : Rk = exResM A) (a : ℤ) :
    exRev A a * forwardMatOf Mbg (exLoc A) Rk a - exSrc A (a + 1) a rfl * exD A a (a + 1) rfl -
      exD A (a - 1) a (by omega) * exSrc A a (a - 1) (by omega) - 1 = 0 := by
  subst hMbg hRk
  rw [exSrc, exSrc, Matrix.zero_mul, Matrix.mul_zero, sub_zero, sub_zero]
  rcases (show a = 0 ∨ a = 1 ∨ (a ≠ 0 ∧ a ≠ 1) by omega) with rfl | rfl | h
  · rw [ex_fwd0]
    exact ex_src0c A
  · rw [ex_fwd1]
    exact ex_src1c A
  · ext i j
    exact ((exRank_isEmpty a h.1 h.2).false i).elim

/-- The second homotopy-inverse identity of the example, in every degree (tex 4391–4451). Kind:
PROVED. -/
theorem ex_tgt (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (exRank a)) (Fin (exRank b)) A)
    (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (exRank n)) A) (hMbg : Mbg = exGlob A)
    (hRk : Rk = exResM A) (a : ℤ) :
    forwardMatOf Mbg (exLoc A) Rk a * exRev A a -
      exTgt A (a + 1) a rfl * dualDiffMatOf (exD A) Rk a (a + 1) rfl -
      dualDiffMatOf (exD A) Rk (a - 1) a (by omega) * exTgt A a (a - 1) (by omega) - 1 = 0 := by
  subst hMbg hRk
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a < 0 ∨ 3 < a by omega)
    with rfl | rfl | rfl | rfl | h | h
  · have := exCIdx_isEmpty (3 - (0 - 1)) (by omega)
    rw [ex_fwd0, ex_dd01,
      matrix_mul_eq_zero_of_isEmpty A (dualDiffMatOf (exD A) (exResM A) (0 - 1) 0 _)]
    simp only [Matrix.mul_zero, sub_zero]
    exact ex_tgt0c A
  · rw [ex_fwd1, ex_dd12,
      show dualDiffMatOf (exD A) (exResM A) (1 - 1) 1 (by omega) =
        dualDiffMatOf (exD A) (exResM A) 0 (0 + 1) rfl from rfl,
      ex_dd01]
    simp only [Matrix.zero_mul, sub_zero]
    exact ex_tgt1c A
  · have := exRank_isEmpty 2 (by decide) (by decide)
    rw [matrix_mul_eq_zero_of_isEmpty A (forwardMatOf (exGlob A) (exLoc A) (exResM A) 2), ex_dd23,
      show dualDiffMatOf (exD A) (exResM A) (2 - 1) 2 (by omega) =
        dualDiffMatOf (exD A) (exResM A) 1 (1 + 1) rfl from rfl,
      ex_dd12]
    simp only [zero_sub]
    exact ex_tgt2c A
  · have := exRank_isEmpty 3 (by decide) (by decide)
    have := exCIdx_isEmpty (3 - (3 + 1)) (by omega)
    rw [matrix_mul_eq_zero_of_isEmpty A (forwardMatOf (exGlob A) (exLoc A) (exResM A) 3),
      matrix_mul_eq_zero_of_isEmpty A (exTgt A (3 + 1) 3 rfl),
      show dualDiffMatOf (exD A) (exResM A) (3 - 1) 3 (by omega) =
        dualDiffMatOf (exD A) (exResM A) 2 (2 + 1) rfl from rfl,
      ex_dd23]
    simp only [sub_zero, zero_sub]
    exact ex_tgt3c A
  · ext i j
    exact ((exCIdx_isEmpty (3 - a) (by omega)).false i).elim
  · ext i j
    exact ((exCIdx_isEmpty (3 - a) (by omega)).false i).elim

/-- **The example stagewise matrix diagram** `S₀`: the model data `dC`, `modelRes`, `modelGlob`,
`loc` of `(R₀, P₀)` with the explicit reverse map and homotopies (tex 4391–4451). Kind: definition
(PROVED identities). -/
def exDiagram : StageMatrixDiagram A exRank where
  dC := (exModel A).dC
  dC_sq := (exModel A).dC_sq
  res := modelRes (exModel A) (exPair A)
  res_comm := modelRes_comm (exModel A) (exPair A)
  glob := modelGlob (exModel A) (exPair A)
  loc := (exPair A).loc
  recip := modelRecip (exModel A) (exPair A)
  rev := exRev A
  srcHom := exSrc A
  tgtHom := exTgt A
  chain := ex_chain A _ (exModelRes_eq A)
  src := ex_src A _ _ (exModelGlob_eq A) (exModelRes_eq A)
  tgt := ex_tgt A _ _ (exModelGlob_eq A) (exModelRes_eq A)


/-- **Non-vacuity of the stagewise matrix diagram** over every commutative ring (tex 4391–4451).
Kind: PROVED. -/
theorem stageMatrixDiagram_nonempty : Nonempty (StageMatrixDiagram A exRank) :=
  ⟨exDiagram A⟩

/-- The forward matrix in degree `0`, for data equal to the example data (tex 4391–4451). Kind:
PROVED. -/
theorem ex_fwd0_gen (Mbg : ∀ a b : ℤ, a + b = 3 → Matrix (Fin (exRank a)) (Fin (exRank b)) A)
    (Rk : ∀ n : ℤ, Matrix (lIdx n) (Fin (exRank n)) A) (hMbg : Mbg = exGlob A)
    (hRk : Rk = exResM A) : forwardMatOf Mbg (exLoc A) Rk 0 = exF0 A := by
  subst hMbg hRk
  exact ex_fwd0 A

/-- **The forward matrix of the example diagram in degree `0` is the identity** onto the `D²`
coordinates (tex 4391–4451). Kind: PROVED. -/
theorem exDiagram_forward_zero :
    forwardMatOf (exDiagram A).glob (exDiagram A).loc (exDiagram A).res 0 = exF0 A :=
  ex_fwd0_gen A _ _ (exModelGlob_eq A) (exModelRes_eq A)

/-- The degree-zero forward matrix is nonzero over a nontrivial ring (tex 4391–4451). Kind: PROVED.
-/
theorem exF0_ne_zero [Nontrivial A] : exF0 A ≠ 0 := by
  intro h
  have e := congrFun (congrFun h (Sum.inr 0)) 0
  simp [exF0] at e

/-- **Non-degeneracy**: the forward matrix of the example diagram in degree `0` is nonzero over a
nontrivial ring (tex 4391–4451). Kind: PROVED. -/
theorem exDiagram_forward_zero_ne_zero [Nontrivial A] :
    forwardMatOf (exDiagram A).glob (exDiagram A).loc (exDiagram A).res 0 ≠ 0 :=
  fun h => exF0_ne_zero A ((exDiagram_forward_zero A).symm.trans h)

/-- **The example complex is flat** (free) in every degree (tex 4391–4451). Kind: PROVED. -/
theorem exCx_flat (n : ℤ) : Module.Flat A ((exCx A).X n) :=
  inferInstanceAs (Module.Flat A (Fin (exRank n) → A))

/-- Residual cohomology of a degreewise finite complex over a local ring is finite over the residue
field (tex 4391–4451). Kind: PROVED. -/
theorem residualCohomologyAt_finite_of_finite [IsLocalRing A] (X : GCx A)
    (hX : ∀ n, Module.Finite A (X.X n)) (n : ℤ) :
    Module.Finite (IsLocalRing.ResidueField A) (residualCohomologyAt X n) := by
  have := hX n
  infer_instance

/-- Every matrix complex has finite residual cohomology in every degree (tex 4391–4451). Kind:
PROVED. -/
theorem matCx_residual_finite [IsLocalRing A] (rank : ℤ → ℕ)
    (dC : ∀ a b : ℤ, a + 1 = b → Matrix (Fin (rank b)) (Fin (rank a)) A)
    (hsq : ∀ a b c (hab : a + 1 = b) (hbc : b + 1 = c), dC b c hbc * dC a b hab = 0) (n : ℤ) :
    Module.Finite (IsLocalRing.ResidueField A) (residualCohomologyAt (matCx rank dC hsq) n) :=
  residualCohomologyAt_finite_of_finite A _
    (fun m => inferInstanceAs (Module.Finite A (Fin (rank m) → A))) n

/-- **The example complex has finite residual cohomology** in every degree (tex 4391–4451). Kind:
PROVED. -/
theorem exCx_residual_finite [IsLocalRing A] (n : ℤ) :
    Module.Finite (IsLocalRing.ResidueField A) (residualCohomologyAt (exCx A) n) :=
  matCx_residual_finite A exRank (exD A) (exD_sq A) n

/-- **The example complex is bounded**: it vanishes in degrees below `0` and above `1` (tex
4391–4451). Kind: PROVED. -/
theorem exCx_subsingleton (n : ℤ) (h : n < 0 ∨ 1 < n) : Subsingleton ((exCx A).X n) :=
  ⟨fun x y => (exCx_eq_zero A n (by omega) (by omega) x).trans
    (exCx_eq_zero A n (by omega) (by omega) y).symm⟩

/-- Non-vacuity of the stagewise matrix diagram over every finite coefficient stage `A_i` (tex
4391–4451). Kind: PROVED. -/
theorem stageMatrixDiagram_nonempty_stageA (i : ℕ) :
    Nonempty (StageMatrixDiagram (ZInQ.Manuscript.RC.Limits.StageA i) exRank) :=
  stageMatrixDiagram_nonempty _

/-- The finite coefficient stage `A_i` is nontrivial for `i ≠ 0` (tex 4391–4451). Kind: PROVED. -/
theorem stageA_nontrivial (i : ℕ) (hi : i ≠ 0) :
    Nontrivial (ZInQ.Manuscript.RC.Limits.StageA i) := by
  have : Fact (1 < 2 ^ i) := ⟨Nat.one_lt_two_pow hi⟩
  refine Ideal.Quotient.nontrivial_iff.mpr ?_
  rw [Ne, Ideal.span_singleton_eq_top]
  intro hu
  have h0 := hu.map (Polynomial.evalRingHom (0 : ZMod (2 ^ i)))
  rw [map_pow, Polynomial.coe_evalRingHom, Polynomial.eval_X, zero_pow hi] at h0
  exact not_isUnit_zero h0

/-- Non-degeneracy of the example diagram over `A_i`, `i ≠ 0` (tex 4391–4451). Kind: PROVED. -/
theorem exDiagram_stageA_forward_ne_zero (i : ℕ) (hi : i ≠ 0) :
    forwardMatOf (exDiagram (ZInQ.Manuscript.RC.Limits.StageA i)).glob
      (exDiagram (ZInQ.Manuscript.RC.Limits.StageA i)).loc
      (exDiagram (ZInQ.Manuscript.RC.Limits.StageA i)).res 0 ≠ 0 := by
  have := stageA_nontrivial i hi
  exact exDiagram_forward_zero_ne_zero _

end ZInQ.Manuscript.RC.FibreDuality
