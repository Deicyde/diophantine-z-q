import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitCertificate
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.NonVacuity

/-!
# Lane RC31, round 2, part 8: non-vacuity of the retained inner-limit hypotheses (a toy)

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451), Lemma
`ex:limits-derivative-switch` (tex 4834–4907) and the transported cross pairing
`β(x, y) = ε e₂(x, J y)` (tex 5037).

`fibreInnerLimitPairingCertificate_of_retained` (`LimitCertificate.lean`) takes the retained stage
data `RetainedLimitPairingStages` and `RetainedGlobalDualityStages` and the identification `hloc`
of the retained local pairing with the transported one. This file shows that **every hypothesis
is satisfiable**, by an explicit **TOY** instance. The toy is *not* the realized Galois diagram
(other lanes supply that); it only certifies that the hypotheses are consistent and that the
certificate can be produced.

The toy (all stages constant, all identities exact over `Λ`, so every stage condition holds with
`0 ∈ stageIdeal i`):

* the global model `G` (`toyStages`): ranks `2` in degrees `1, 2`, `0` otherwise, zero
  differentials;
* the localization (`toyRes`): `G¹ → F ⊕ S`, `x ↦ (x, 0)` (the finite plane), `G² → D²` the
  identity; the global trace pairing is `0`;
* the local pairing (`toyLoc A`): `D⁰ × D²` and `D² × D⁰` by `Aᵀ`, `(F ⊕ S) × (F ⊕ S)` by
  `[[0, −Aᵀ], [−A, 0]]`; with `A = (Ω J_Λ)ᵀ`, `Ω = [[0, 1], [−1, 0]]` and `J_Λ` the matrix of
  `ρ_T(τ)` on `T₂E₁` over `Λ` (`conjLam`), this is the transported pairing at `k(𝔭)` (`toy_hloc`);
* the retained global duality (`toyDuality A B`): for any `B` inverse to `A`, an explicit reverse
  map and target homotopy; the source homotopy is `0`.

Main results: `toy_hloc`, **`limitCertificate_nonvacuous`** (the certificate for `E₁ : y² =
x(x−1)(x+3)` over `ℚ`, `S = Set.univ`, the prime `(t)`, an actual complex conjugation, and any
nonprincipal ultrafilter), and the switching duality `FibreInnerLimitDuality` as an `example`.

Kinds: definitions (the toy data) and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open Filter Matrix NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Manuscript.RC.Limits (ulimMat ulimMat_const stageIdeal)
open ZInQ.Manuscript.RC.Uniform (Lambda switchPairing crossPairing crossPairing_apply weil
  planePairing_apply)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef (curveE1 Pt0 HasFullTwoTorsion tateBasis)
open scoped PowerSeries.WithPiTopology

/-! ### Block-matrix helpers -/

section Blocks

variable {R : Type} [CommRing R]

/-- Differences of block matrices (tex 4391–4451). Kind: PROVED. -/
theorem toy_fromBlocks_sub {l m n o : Type} (A A' : Matrix n l R) (B B' : Matrix n m R)
    (C C' : Matrix o l R) (D D' : Matrix o m R) :
    fromBlocks A B C D - fromBlocks A' B' C' D' =
      fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext (i | i) (j | j) <;> rfl

/-- Ring homomorphisms commute with negation of matrices (tex 4391–4451). Kind: PROVED. -/
theorem toy_map_neg {T m n : Type} [CommRing T] (f : R →+* T) (M : Matrix m n R) :
    (-M).map f = -M.map f := by
  ext i j
  simp

/-- A block matrix vanishes iff its blocks do (tex 4391–4451). Kind: PROVED. -/
theorem toy_fromBlocks_eq_zero {l m n o : Type} (A : Matrix n l R) (B : Matrix n m R)
    (C : Matrix o l R) (D : Matrix o m R) :
    fromBlocks A B C D = 0 ↔ A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  rw [← fromBlocks_zero, fromBlocks_inj]

/-- Columns `0 | (rows)` form a block matrix (tex 4391–4451). Kind: PROVED. -/
theorem toy_fromCols_zero_fromRows {m₁ m₂ n₁ n₂ : Type} (B₁₂ : Matrix m₁ n₂ R)
    (B₂₂ : Matrix m₂ n₂ R) :
    fromCols (0 : Matrix (m₁ ⊕ m₂) n₁ R) (fromRows B₁₂ B₂₂) = fromBlocks 0 B₁₂ 0 B₂₂ := by
  ext (i | i) (j | j) <;> rfl

/-- Columns `(rows) | 0` form a block matrix (tex 4391–4451). Kind: PROVED. -/
theorem toy_fromCols_fromRows_zero {m₁ m₂ n₁ n₂ : Type} (B₁₁ : Matrix m₁ n₁ R)
    (B₂₁ : Matrix m₂ n₁ R) :
    fromCols (fromRows B₁₁ B₂₁) (0 : Matrix (m₁ ⊕ m₂) n₂ R) = fromBlocks B₁₁ 0 B₂₁ 0 := by
  ext (i | i) (j | j) <;> rfl

/-- Columns `0 | (blocks)` form a block matrix (tex 4391–4451). Kind: PROVED. -/
theorem toy_fromCols_zero_fromBlocks {m₁ m₂ n₀ n₁ n₂ : Type} (P : Matrix m₁ n₁ R)
    (Q : Matrix m₁ n₂ R) (C : Matrix m₂ n₁ R) (D : Matrix m₂ n₂ R) :
    fromCols (0 : Matrix (m₁ ⊕ m₂) n₀ R) (fromBlocks P Q C D) =
      fromBlocks 0 (fromCols P Q) 0 (fromCols C D) := by
  ext (i | i) (j | j | j) <;> rfl

/-- Matrices with no rows are all equal, as a rewriting rule (tex 4391–4451). Kind: PROVED. -/
theorem toy_eq_fin0 {α n : Type} (M N : Matrix (Fin 0) n α) : (M = N) ↔ True :=
  iff_true_intro (Matrix.ext fun i _ => i.elim0)

/-- Matrices with no rows are all equal (tex 4391–4451). Kind: PROVED. -/
theorem toy_rows_empty {α m n : Type} [IsEmpty m] (M N : Matrix m n α) : M = N :=
  Matrix.ext fun i _ => isEmptyElim i

/-- A product through an empty index vanishes (tex 4391–4451). Kind: PROVED. -/
theorem toy_mul_empty {m n p : Type} [Fintype n] [IsEmpty n] (M : Matrix m n R)
    (N : Matrix n p R) : M * N = 0 := by
  ext i j
  simp [Matrix.mul_apply]

end Blocks

/-! ### The matrix `Ω` of the Weil pairing -/

section Omega

variable (R : Type) [CommRing R]

/-- **The matrix of the Weil pairing** `e₂(x, y) = x₀ y₁ − x₁ y₀` (tex 5037). Kind:
definition. -/
def omegaMat : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

/-- `Ωᵀ Ω = 1` (tex 5037). Kind: PROVED. -/
theorem omegaMat_transpose_mul : (omegaMat R)ᵀ * omegaMat R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omegaMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Ω Ωᵀ = 1` (tex 5037). Kind: PROVED. -/
theorem omegaMat_mul_transpose : omegaMat R * (omegaMat R)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omegaMat, Matrix.mul_apply, Fin.sum_univ_two]

variable {R}

/-- `Ω` is preserved by ring homomorphisms (tex 5037). Kind: PROVED. -/
theorem omegaMat_map {T : Type} [CommRing T] (f : R →+* T) : (omegaMat R).map f = omegaMat T := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [omegaMat]

/-- For mutually inverse `J² = 1`, `A = (Ω J)ᵀ` and `B = Ω Jᵀ` satisfy `A B = 1` (tex 5037).
Kind: PROVED. -/
theorem omega_conj_mul {J : Matrix (Fin 2) (Fin 2) R} (hJ : J * J = 1) :
    (omegaMat R * J)ᵀ * (omegaMat R * Jᵀ) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (omegaMat R)ᵀ,
    omegaMat_transpose_mul, Matrix.one_mul, ← Matrix.transpose_mul, hJ, Matrix.transpose_one]

/-- For `J² = 1`, `B A = 1` with `A = (Ω J)ᵀ`, `B = Ω Jᵀ` (tex 5037). Kind: PROVED. -/
theorem omega_conj_mul' {J : Matrix (Fin 2) (Fin 2) R} (hJ : J * J = 1) :
    (omegaMat R * Jᵀ) * (omegaMat R * J)ᵀ = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Jᵀ, ← Matrix.transpose_mul, hJ,
    Matrix.transpose_one, Matrix.one_mul, omegaMat_mul_transpose]

end Omega

/-! ### The toy global model -/

/-- **TOY ranks**: `2` in degrees `1, 2`, `0` otherwise (tex 4391–4451). Kind: definition. -/
def toyRank : ℤ → ℕ
  | .ofNat 1 => 2
  | .ofNat 2 => 2
  | _ => 0

/-- Outside degrees `1, 2` the toy ranks vanish (tex 4391–4451). Kind: PROVED. -/
theorem toyRank_eq_zero (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) : toyRank n = 0 := by
  rcases n with ((_ | _ | _ | n) | n)
  · rfl
  · exact absurd rfl h1
  · exact absurd rfl h2
  · rfl
  · rfl

/-- The toy model is bounded (tex 4391–4451). Kind: PROVED. -/
theorem toyRank_bounded (n : ℤ) (hn : n < 1 ∨ 2 < n) : toyRank n = 0 :=
  toyRank_eq_zero n (by omega) (by omega)

/-- Outside degrees `1, 2` the toy coordinates are empty (tex 4391–4451). Kind: PROVED. -/
theorem toyRank_isEmpty (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) : IsEmpty (Fin (toyRank n)) := by
  rw [toyRank_eq_zero n h1 h2]
  infer_instance

/-- **The TOY global model** over `Λ` (tex 4391–4451): constant stages, ranks `toyRank`, zero
differentials. It is a toy, not the realized Galois diagram. Kind: definition. -/
def toyStages (U : Ultrafilter ℕ) : ComplexStages (R := Lambda) stageIdeal U where
  rank := toyRank
  low := 1
  high := 2
  bounded := toyRank_bounded
  d _ _ _ _ := 0
  square _ _ _ _ _ := Filter.Eventually.of_forall fun i x y => by simp

/-- An exact zero matrix satisfies every stage condition (tex 4391–4451). Kind: PROVED. -/
theorem toy_mem_stage {m n : Type} [Fintype m] {i : ℕ} {M : Matrix m n Lambda} (h : M = 0)
    (x : m) (y : n) : M x y ∈ stageIdeal i := by
  rw [h]
  exact Submodule.zero_mem _

/-! ### The toy retained pairing data -/

/-- The TOY localization in degree `1`: `x ↦ (x, 0)`, onto the finite plane (tex 4860–4868).
Kind: definition. -/
def toyResOne : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) Lambda := fromRows 1 0

/-- **TOY localization** (tex 4860–4868): `G¹ → F ⊕ S`, `x ↦ (x, 0)` (the finite plane),
`G² → D²` the identity, zero otherwise. Kind: definition. -/
def toyRes : ∀ n : ℤ, Matrix (lIdx n) (Fin (toyRank n)) Lambda
  | .ofNat 1 => toyResOne
  | .ofNat 2 => (1 : Matrix (Fin 2) (Fin 2) Lambda)
  | _ => 0

/-- The TOY local pairing on `F ⊕ S`: `[[0, −Aᵀ], [−A, 0]]` (tex 4860–4868, 5037). Kind:
definition. -/
def toyLocOne {R : Type} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  fromBlocks 0 (-Aᵀ) (-A) 0

/-- **TOY local pairing** (tex 4860–4868, 5037): `D⁰ × D²` and `D² × D⁰` by `Aᵀ`, and
`(F ⊕ S) × (F ⊕ S)` by `toyLocOne A`, zero otherwise. Kind: definition. -/
def toyLoc {R : Type} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) R
  | .ofNat 0, .ofNat 2 => (Aᵀ : Matrix (Fin 2) (Fin 2) R)
  | .ofNat 1, .ofNat 1 => toyLocOne A
  | .ofNat 2, .ofNat 0 => (Aᵀ : Matrix (Fin 2) (Fin 2) R)
  | _, _ => 0

/-- The finite plane is isotropic for the toy local pairing (tex 4860–4868). Kind: PROVED. -/
theorem toy_recip_11 (A : Matrix (Fin 2) (Fin 2) Lambda) :
    toyResOneᵀ * toyLocOne A * toyResOne = 0 := by
  simp [toyResOne, toyLocOne, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

/-- **Toy reciprocity**: `Rᵀ β R = 0` in every total degree two (tex 4860–4868). Kind:
PROVED. -/
theorem toy_recip (A : Matrix (Fin 2) (Fin 2) Lambda) (a b : ℤ) (h : a + b = 2) :
    (toyRes a)ᵀ * toyLoc A a b * toyRes b = 0 := by
  by_cases h1 : a = 1
  · subst h1
    obtain rfl : b = 1 := by omega
    exact toy_recip_11 A
  · by_cases h2 : a = 2
    · subst h2
      obtain rfl : b = 0 := by omega
      exact Matrix.ext fun _ y => Fin.elim0 y
    · have := toyRank_isEmpty a h1 h2
      exact toy_rows_empty _ _

/-- **The TOY retained pairing data** (tex 4391–4451, 4860–4868), constant in the stage: the
localization `toyRes`, the global trace pairing `0` and the local pairing `toyLoc A`. A toy, not
the realized diagram. Kind: definition. -/
def toyPairing (U : Ultrafilter ℕ) (A : Matrix (Fin 2) (Fin 2) Lambda) :
    RetainedLimitPairingStages U (toyStages U) where
  res n _ := toyRes n
  res_comm n := Filter.Eventually.of_forall fun _ x y => toy_mem_stage (Matrix.mul_zero _) x y
  glob _ _ _ _ := 0
  loc a b _ := toyLoc A a b
  recip a b h := Filter.Eventually.of_forall fun _ x y => toy_mem_stage (by
    simp only [Matrix.mul_zero, Matrix.zero_mul, smul_zero, zero_add]
    exact toy_recip A a b h) x y

/-! ### The toy retained global duality -/

/-- The TOY reverse map in degree `1`: `(g, f, s) ↦ B s` (tex 4391–4451). Kind: definition. -/
def toyRevOne (B : Matrix (Fin 2) (Fin 2) Lambda) :
    Matrix (Fin 2) (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) Lambda :=
  fromCols 0 (fromCols 0 B)

/-- The TOY reverse map in degree `2`: `(g, u) ↦ B u` (tex 4391–4451). Kind: definition. -/
def toyRevTwo (B : Matrix (Fin 2) (Fin 2) Lambda) : Matrix (Fin 2) (Fin 2 ⊕ Fin 2) Lambda :=
  fromCols 0 B

/-- **TOY reverse map** of the global duality (tex 4391–4451): `toyRevOne B`, `toyRevTwo B` in
degrees `1, 2`, zero otherwise. Kind: definition. -/
def toyRev (B : Matrix (Fin 2) (Fin 2) Lambda) :
    ∀ a : ℤ, Matrix (Fin (toyRank a)) (cIdxOf toyRank (3 - a)) Lambda
  | .ofNat 1 => toyRevOne B
  | .ofNat 2 => toyRevTwo B
  | _ => 0

/-- The TOY target homotopy from degree `1` to `0`: `(g, f, s) ↦ g` (tex 4391–4451). Kind:
definition. -/
def toyTgtOne : Matrix (Fin 0 ⊕ Fin 2) (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) Lambda := fromBlocks 0 0 1 0

/-- The TOY target homotopy from degree `2` to `1`: `(g, u) ↦ (0, −g, 0)` (tex 4391–4451). Kind:
definition. -/
def toyTgtTwo : Matrix (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 2 ⊕ Fin 2) Lambda :=
  fromBlocks 0 0 (fromRows (-1) 0) 0

/-- **TOY target homotopy** (tex 4391–4451): `toyTgtOne`, `toyTgtTwo`, zero otherwise. Kind:
definition. -/
def toyTgt : ∀ a b : ℤ, Matrix (cIdxOf toyRank (3 - b)) (cIdxOf toyRank (3 - a)) Lambda
  | .ofNat 1, .ofNat 0 => toyTgtOne
  | .ofNat 2, .ofNat 1 => toyTgtTwo
  | _, _ => 0

/-- The differential `2 → 3` of the toy `Cone(res)[−1]` (tex 4391–4451). Kind: definition. -/
def toyConeTwo : Matrix (Fin 0 ⊕ Fin 2) (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) Lambda := fromBlocks 0 0 1 0

/-- The differential `1 → 2` of the toy `Cone(res)[−1]` (tex 4391–4451). Kind: definition. -/
def toyConeOne : Matrix (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 2 ⊕ Fin 2) Lambda :=
  fromBlocks 0 0 toyResOne 0

/-- The forward matrix of the toy global duality in degree `1` (tex 4391–4451). Kind:
definition. -/
def toyFwdOne (A : Matrix (Fin 2) (Fin 2) Lambda) :
    Matrix (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 2) Lambda :=
  fromRows (0 : Matrix (Fin 2) (Fin 2) Lambda)ᵀ (((sgn 1 : ℤ) : Lambda) •
    ((toyLocOne A)ᵀ * toyResOne))

/-- The forward matrix of the toy global duality in degree `2` (tex 4391–4451). Kind:
definition. -/
def toyFwdTwo (A : Matrix (Fin 2) (Fin 2) Lambda) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) Lambda :=
  fromRows (0 : Matrix (Fin 2) (Fin 2) Lambda)ᵀ (((sgn 2 : ℤ) : Lambda) •
    ((Aᵀ)ᵀ * (1 : Matrix (Fin 2) (Fin 2) Lambda)))

/-- The dual differential `0 → 1` of the toy (tex 4391–4451). Kind: definition. -/
def toyDualZero : Matrix (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) (Fin 0 ⊕ Fin 2) Lambda :=
  (-((sgn 0 : ℤ) : Lambda)) • toyConeTwoᵀ

/-- The dual differential `1 → 2` of the toy (tex 4391–4451). Kind: definition. -/
def toyDualOne : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ (Fin 2 ⊕ Fin 2)) Lambda :=
  (-((sgn 1 : ℤ) : Lambda)) • toyConeOneᵀ

/-- `sgn 0 = 1` in `Λ` (tex 4391–4451). Kind: PROVED. -/
theorem toy_sgn0 : ((sgn 0 : ℤ) : Lambda) = 1 := by
  simp [sgn]

/-- `sgn 1 = −1` in `Λ` (tex 4391–4451). Kind: PROVED. -/
theorem toy_sgn1 : ((sgn 1 : ℤ) : Lambda) = -1 := by
  simp [sgn]

/-- `sgn 2 = 1` in `Λ` (tex 4391–4451). Kind: PROVED. -/
theorem toy_sgn2 : ((sgn 2 : ℤ) : Lambda) = 1 := by
  rw [sgn, Int.negOnePow_even 2 even_two]
  simp

section Duality

variable (A B : Matrix (Fin 2) (Fin 2) Lambda)

/-- Toy chain-map identity in degree `0` (tex 4391–4451). Kind: PROVED. -/
theorem toy_chain_0 : toyRevOne B * toyDualZero = 0 := by
  simp [toyRevOne, toyDualZero, toyConeTwo, fromBlocks_transpose, fromCols_mul_fromBlocks]

/-- Toy chain-map identity in degree `1` (tex 4391–4451). Kind: PROVED. -/
theorem toy_chain_1 : toyRevTwo B * toyDualOne = 0 := by
  simp [toyRevTwo, toyDualOne, toyConeOne, fromBlocks_transpose, fromCols_mul_fromBlocks]

/-- **The toy reverse map is a chain map** (tex 4391–4451). Kind: PROVED. -/
theorem toy_chain (a : ℤ) :
    toyRev B (a + 1) * dualDiffMatOf (rank := toyRank) (fun _ _ _ => 0) toyRes a (a + 1) rfl -
      (0 : Matrix (Fin (toyRank (a + 1))) (Fin (toyRank a)) Lambda) * toyRev B a = 0 := by
  rw [Matrix.zero_mul, sub_zero]
  by_cases h0 : a = 0
  · subst h0
    exact toy_chain_0 B
  · by_cases h1 : a = 1
    · subst h1
      exact toy_chain_1 B
    · have := toyRank_isEmpty (a + 1) (by omega) (by omega)
      exact toy_rows_empty _ _

/-- Toy first homotopy-inverse identity in degree `1` (tex 4391–4451). Kind: PROVED. -/
theorem toy_src_1 (hBA : B * A = 1) : toyRevOne B * toyFwdOne A - 1 = 0 := by
  simp [toyRevOne, toyFwdOne, toyLocOne, toyResOne, fromBlocks_transpose,
    fromBlocks_mul_fromRows, fromCols_mul_fromRows, toy_sgn1, hBA]

/-- Toy first homotopy-inverse identity in degree `2` (tex 4391–4451). Kind: PROVED. -/
theorem toy_src_2 (hBA : B * A = 1) : toyRevTwo B * toyFwdTwo A - 1 = 0 := by
  simp [toyRevTwo, toyFwdTwo, fromCols_mul_fromRows, toy_sgn2, hBA]

/-- **The toy first homotopy-inverse identity** (tex 4391–4451). Kind: PROVED. -/
theorem toy_src (hBA : B * A = 1) (a : ℤ) :
    toyRev B a * forwardMatOf (rank := toyRank) (fun _ _ _ => 0) (fun a b => toyLoc A a b)
        toyRes a -
      (0 : Matrix (Fin (toyRank a)) (Fin (toyRank (a + 1))) Lambda) *
        (0 : Matrix (Fin (toyRank (a + 1))) (Fin (toyRank a)) Lambda) -
      (0 : Matrix (Fin (toyRank a)) (Fin (toyRank (a - 1))) Lambda) *
        (0 : Matrix (Fin (toyRank (a - 1))) (Fin (toyRank a)) Lambda) - 1 = 0 := by
  rw [Matrix.zero_mul, Matrix.zero_mul, sub_zero, sub_zero]
  by_cases h1 : a = 1
  · subst h1
    exact toy_src_1 A B hBA
  · by_cases h2 : a = 2
    · subst h2
      exact toy_src_2 A B hBA
    · have := toyRank_isEmpty a h1 h2
      exact toy_rows_empty _ _

/-- Toy second homotopy-inverse identity in degree `0` (tex 4391–4451). Kind: PROVED. -/
theorem toy_tgt_0 (F : Matrix (Fin 0 ⊕ Fin 2) (Fin 0) Lambda)
    (Rv : Matrix (Fin 0) (Fin 0 ⊕ Fin 2) Lambda)
    (Dm : Matrix (Fin 0 ⊕ Fin 2) (Fin 0 ⊕ Empty) Lambda)
    (H0 : Matrix (Fin 0 ⊕ Empty) (Fin 0 ⊕ Fin 2) Lambda) :
    F * Rv - toyTgtOne * toyDualZero - Dm * H0 - 1 = 0 := by
  rw [toy_mul_empty F Rv, toy_mul_empty Dm H0]
  simp [toyTgtOne, toyDualZero, toyConeTwo, fromBlocks_transpose, fromBlocks_multiply, toy_sgn0,
    toy_fromBlocks_sub, ← fromBlocks_one, toy_fromBlocks_eq_zero, toy_eq_fin0]

/-- Toy second homotopy-inverse identity in degree `1` (tex 4391–4451). Kind: PROVED. -/
theorem toy_tgt_1 (hAB : A * B = 1) :
    toyFwdOne A * toyRevOne B - toyTgtTwo * toyDualOne - toyDualZero * toyTgtOne - 1 = 0 := by
  simp [toyFwdOne, toyRevOne, toyTgtTwo, toyDualOne, toyDualZero, toyTgtOne, toyConeOne,
    toyConeTwo, toyLocOne, toyResOne, fromBlocks_transpose, fromBlocks_mul_fromRows,
    fromBlocks_multiply, transpose_fromRows, toy_sgn0, toy_sgn1, toy_fromBlocks_sub,
    ← fromBlocks_one, hAB, fromBlocks_add, toy_fromCols_zero_fromRows,
    toy_fromCols_zero_fromBlocks, toy_fromCols_fromRows_zero]

/-- Toy second homotopy-inverse identity in degree `2` (tex 4391–4451). Kind: PROVED. -/
theorem toy_tgt_2 (hAB : A * B = 1) (H3 : Matrix (Fin 2 ⊕ Fin 2) (Fin 0 ⊕ Empty) Lambda)
    (D23 : Matrix (Fin 0 ⊕ Empty) (Fin 2 ⊕ Fin 2) Lambda) :
    toyFwdTwo A * toyRevTwo B - H3 * D23 - toyDualOne * toyTgtTwo - 1 = 0 := by
  rw [toy_mul_empty H3 D23]
  simp [toyFwdTwo, toyRevTwo, toyDualOne, toyTgtTwo, toyConeOne, toyResOne,
    fromBlocks_transpose, fromBlocks_multiply, fromCols_mul_fromRows, transpose_fromRows,
    toy_sgn1, toy_sgn2, toy_fromBlocks_sub, ← fromBlocks_one, hAB, toy_fromCols_zero_fromRows]

/-- **The toy second homotopy-inverse identity** (tex 4391–4451). Kind: PROVED. -/
theorem toy_tgt (hAB : A * B = 1) (a : ℤ) :
    forwardMatOf (rank := toyRank) (fun _ _ _ => 0) (fun a b => toyLoc A a b) toyRes a *
        toyRev B a -
      toyTgt (a + 1) a * dualDiffMatOf (rank := toyRank) (fun _ _ _ => 0) toyRes a (a + 1) rfl -
      dualDiffMatOf (rank := toyRank) (fun _ _ _ => 0) toyRes (a - 1) a (by omega) *
        toyTgt a (a - 1) - 1 = 0 := by
  by_cases h0 : a = 0
  · subst h0
    exact toy_tgt_0 _ _ _ _
  · by_cases h1 : a = 1
    · subst h1
      exact toy_tgt_1 A B hAB
    · by_cases h2 : a = 2
      · subst h2
        exact toy_tgt_2 A B hAB _ _
      · have := toyRank_isEmpty (3 - a) (by omega) (by omega)
        have := lIdx_isEmpty (3 - a - 1) (by omega) (by omega) (by omega)
        exact toy_rows_empty _ _

end Duality

/-- **The TOY retained global duality** (tex 4391–4451), constant in the stage, for any pair of
mutually inverse matrices `A, B`: the reverse map `toyRev B`, the source homotopy `0` and the
target homotopy `toyTgt`. A toy, not the realized diagram. Kind: definition. -/
def toyDuality (U : Ultrafilter ℕ) (A B : Matrix (Fin 2) (Fin 2) Lambda) (hAB : A * B = 1)
    (hBA : B * A = 1) : RetainedGlobalDualityStages (toyPairing U A) where
  rev a _ := toyRev B a
  srcHom _ _ _ _ := 0
  tgtHom a b _ _ := toyTgt a b
  chain a := Filter.Eventually.of_forall fun _ x y => toy_mem_stage (toy_chain B a) x y
  src a := Filter.Eventually.of_forall fun _ x y => toy_mem_stage (toy_src A B hBA a) x y
  tgt a := Filter.Eventually.of_forall fun _ x y => toy_mem_stage (toy_tgt A B hAB a) x y

/-! ### The local pairing of the toy is the transported one -/

section Local

variable {k : Type} [Field k]

/-- `x ⬝ (Ω J y) = e₂(x, J y)` (tex 5037). Kind: PROVED. -/
theorem bilinOfMat_omega (J : Matrix (Fin 2) (Fin 2) k) :
    bilinOfMat (omegaMat k * J) = crossPairing 1 J := by
  refine LinearMap.ext₂ fun x y => ?_
  rw [bilinOfMat_apply, crossPairing_apply, ← Matrix.mulVec_mulVec]
  simp [omegaMat, weil, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- `(Ω J)₀ⱼ = J₁ⱼ` (tex 5037). Kind: PROVED. -/
theorem omegaMat_mul_zero {R : Type} [CommRing R] (J : Matrix (Fin 2) (Fin 2) R) (j : Fin 2) :
    (omegaMat R * J) 0 j = J 1 j := by
  simp [omegaMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- `(Ω J)₁ⱼ = −J₀ⱼ` (tex 5037). Kind: PROVED. -/
theorem omegaMat_mul_one {R : Type} [CommRing R] (J : Matrix (Fin 2) (Fin 2) R) (j : Fin 2) :
    (omegaMat R * J) 1 j = -J 0 j := by
  simp [omegaMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- The `(F ⊕ S)`-block of the toy local pairing in coordinates is
`b₁₁(p, q) = −switchPairing 1 1 J q p` (tex 4860–4868, 5037). Kind: PROVED. -/
theorem toy_switch_coords (J : Matrix (Fin 2) (Fin 2) k) (p q : Coords k) :
    Sum.elim p.1 p.2 ⬝ᵥ ((fromBlocks 0 (-(omegaMat k * J)) (-(omegaMat k * J)ᵀ) 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) *ᵥ Sum.elim q.1 q.2) =
    -(switchPairing 1 1 J q p) := by
  simp only [planePairing_apply, crossPairing_apply, weil, LinearMap.mk₂_apply]
  simp [-Matrix.transpose_mul, dotProduct, Matrix.mulVec, Fin.sum_univ_two, Fintype.sum_sum_type,
    omegaMat_mul_zero, omegaMat_mul_one]
  ring

/-- The `(F ⊕ S)`-block of the toy local pairing is `b₁₁(p, q) = −switchPairing 1 1 J q p`
(tex 4860–4868, 5037). Kind: PROVED. -/
theorem bilinOfMat_switch (J : Matrix (Fin 2) (Fin 2) k) :
    (bilinOfMat (fromBlocks 0 (-(omegaMat k * J)) (-(omegaMat k * J)ᵀ) 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k)).compl₁₂ (lCoord k 1).toLinearMap
      (lCoord k 1).toLinearMap = -(switchPairing 1 1 J).flip :=
  LinearMap.ext₂ fun p q => toy_switch_coords J p q

/-- **A local pairing matrix of the toy shape is the transported pairing** with
`ε₀ = ε₂ = ε = σ = 1` (tex 4860–4868, 5037). Kind: PROVED. -/
theorem localPairingOfMat_toy (J : Matrix (Fin 2) (Fin 2) k)
    (M : ∀ a b : ℤ, Matrix (lIdx a) (lIdx b) k) (h02 : M 0 2 = omegaMat k * J)
    (h11 : M 1 1 = (fromBlocks 0 (-(omegaMat k * J)) (-(omegaMat k * J)ᵀ) 0 :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k))
    (h20 : M 2 0 = omegaMat k * J) :
    localPairingOfMat M = transportedPairing 1 1 1 1 J := by
  unfold localPairingOfMat transportedPairing
  rw [h02, h11, h20]
  congr 1
  · exact bilinOfMat_omega J
  · exact bilinOfMat_switch J
  · exact bilinOfMat_omega J

end Local

/-! ### The matrix of `J = ρ_T(τ)` over `Λ` -/

section Conj

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (Cn : ActualConj K S) (W : WeierstrassCurve K) (hW : W.map (Cn.κ : K →+* K) = W)
  [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **The matrix `J_Λ` of `ρ_T(τ)` on `T₂E` over `Λ`** in lane RC28's basis (tex 5037). Kind:
definition. -/
def conjLam : Matrix (Fin 2) (Fin 2) Lambda :=
  (LinearMap.toMatrix (tateBasis (K := K) (S := S) (W := W)) tateBasis
    (conjTate Cn W hW)).map (algebraMap ℤ_[2] Lambda)

/-- `J_Λ² = 1` (tex 5037). Kind: PROVED. -/
theorem conjLam_mul_self : conjLam Cn W hW * conjLam Cn W hW = 1 := by
  have h : conjTate Cn W hW * conjTate Cn W hW = 1 :=
    LinearMap.ext fun x => conjTate_conjTate Cn W hW x
  unfold conjLam
  rw [← Matrix.map_mul, ← LinearMap.toMatrix_mul, h, LinearMap.toMatrix_one, Matrix.map_one _
    (map_zero _) (map_one _)]

/-- `J_Λ` read in `k(𝔭)` is `conjMatrix` (tex 5037). Kind: PROVED. -/
theorem conjLam_map (P : Ideal Lambda) [P.IsPrime] :
    (conjLam Cn W hW).map (algebraMap Lambda (ResAt P)) = conjMatrix Cn W hW P := by
  unfold conjLam conjMatrix
  rw [Matrix.map_map]
  ext i j
  exact (IsScalarTower.algebraMap_apply ℤ_[2] Lambda (ResAt P) _).symm

/-- The toy matrix `A = (Ω J_Λ)ᵀ` (tex 5037). Kind: definition. -/
def toyA : Matrix (Fin 2) (Fin 2) Lambda := (omegaMat Lambda * conjLam Cn W hW)ᵀ

/-- The toy matrix `B = Ω J_Λᵀ`, inverse to `A` (tex 5037). Kind: definition. -/
def toyB : Matrix (Fin 2) (Fin 2) Lambda := omegaMat Lambda * (conjLam Cn W hW)ᵀ

/-- `A B = 1` (tex 5037). Kind: PROVED. -/
theorem toyA_mul_toyB : toyA Cn W hW * toyB Cn W hW = 1 :=
  omega_conj_mul (conjLam_mul_self Cn W hW)

/-- `B A = 1` (tex 5037). Kind: PROVED. -/
theorem toyB_mul_toyA : toyB Cn W hW * toyA Cn W hW = 1 :=
  omega_conj_mul' (conjLam_mul_self Cn W hW)

/-- **The toy satisfies `hloc`**: its retained local pairing at `k(𝔭)` is the transported pairing
with `J = conjMatrix Cn W hW P` (tex 5037). Kind: PROVED. -/
theorem toy_hloc (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime] :
    localPairingOfMat ((toyPairing U (toyA Cn W hW)).locK P) =
      transportedPairing 1 1 1 1 (conjMatrix Cn W hW P) := by
  refine localPairingOfMat_toy _ _ ?_ ?_ ?_
  · change (ulimMat U (fun _ => ((omegaMat Lambda * conjLam Cn W hW)ᵀ)ᵀ)).map
      (algebraMap Lambda (ResAt P)) = _
    rw [ulimMat_const, Matrix.transpose_transpose, Matrix.map_mul, omegaMat_map, conjLam_map]
  · change (ulimMat U (fun _ => (fromBlocks 0 (-((omegaMat Lambda * conjLam Cn W hW)ᵀ)ᵀ)
      (-(omegaMat Lambda * conjLam Cn W hW)ᵀ) 0 :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) Lambda))).map (algebraMap Lambda (ResAt P)) = _
    rw [ulimMat_const, Matrix.transpose_transpose, fromBlocks_map]
    simp [toy_map_neg, Matrix.map_mul, omegaMat_map, conjLam_map, Matrix.transpose_map]
  · change (ulimMat U (fun _ => ((omegaMat Lambda * conjLam Cn W hW)ᵀ)ᵀ)).map
      (algebraMap Lambda (ResAt P)) = _
    rw [ulimMat_const, Matrix.transpose_transpose, Matrix.map_mul, omegaMat_map, conjLam_map]

end Conj

/-! ### The certificate for the toy -/

/-- **Non-vacuity of the inner-limit producer contract** (tex 4391–4451, 4834–4907, 5037): for any
nonprincipal ultrafilter `U`, every hypothesis of `fibreInnerLimitPairingCertificate_of_retained`
holds for the TOY data (`toyStages`, `toyPairing`, `toyDuality`, `toy_hloc`) with `E₁` over `ℚ`,
`S = Set.univ`, an actual complex conjugation and the prime `(t)`, so the certificate holds for the
toy. The toy is not the realized Galois diagram. Kind: PROVED. -/
theorem limitCertificate_nonvacuous (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite) :
    FibreInnerLimitPairingCertificate U hU Pt0 (toyStages U)
      ((toyPairing U (toyA (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ))).resLimit
        hU Pt0) 1 1
      (conjMatrix (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ) Pt0) :=
  fibreInnerLimitPairingCertificate_of_retained hU
    (toyDuality U _ _ (toyA_mul_toyB (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ))
      (toyB_mul_toyA (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ)))
    Pt0 (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ) 1 1 1 1 one_ne_zero
    one_ne_zero one_ne_zero
    (toy_hloc (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ) U Pt0)

/-- The certificate for the toy at a concrete nonprincipal ultrafilter, the hyperfilter. -/
example : FibreInnerLimitPairingCertificate (Filter.hyperfilter ℕ) Filter.hyperfilter_le_cofinite
    Pt0 (toyStages (Filter.hyperfilter ℕ))
    ((toyPairing (Filter.hyperfilter ℕ)
      (toyA (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ))).resLimit
        Filter.hyperfilter_le_cofinite Pt0) 1 1
    (conjMatrix (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ) Pt0) :=
  limitCertificate_nonvacuous _ _

/-- The switching duality `FibreInnerLimitDuality` for the toy (tex 5065–5070). -/
example (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ Filter.cofinite) :
    FibreInnerLimitDuality U hU Pt0 (toyStages U)
      ((toyPairing U (toyA (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ))).resLimit
        hU Pt0) 1 1
      (conjMatrix (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ) Pt0) one_ne_zero
      one_ne_zero
      (conjMatrix_mul_self (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ) Pt0) :=
  fibreInnerLimitDuality_of_retained hU
    (toyDuality U _ _ (toyA_mul_toyB (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ))
      (toyB_mul_toyA (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ)))
    Pt0 (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ) 1 1 1 1 one_ne_zero
    one_ne_zero one_ne_zero
    (toy_hloc (actualConjQ Set.univ) curveE1 (curveE1_map_conj Set.univ) U Pt0)

end ZInQ.Manuscript.RC.FibreDuality
