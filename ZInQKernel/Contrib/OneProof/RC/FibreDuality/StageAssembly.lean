import ZInQKernel.Contrib.OneProof.RC.FibreDuality.StageDiagram
import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitCertificate

/-!
# Lane RC31, round 3, part 3: from stagewise matrix diagrams to the retained diagram over `Λ`

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit`, statement (tex 4400–4406): "For
one fixed active support and binary family, retain a tuple whose model ranks are bounded over the
finite coefficient stages. One fixed nonprincipal ultrafilter gives a diagram over `Λ` at all
coefficient precisions, preserving its matrix identities and retained homotopy inverses"; and its
proof (tex 4443–4451): "Bounded ranks can be fixed on a set in that ultrafilter. Each finite tuple
of matrix entries then has a compatible limit at every coefficient precision, giving matrices over
`Λ`. Every polynomial identity between the matrices survives. Retained homotopy inverses remain
homotopy inverses."

Given, at every stage `A_i = Λ/(2^i, t^i)`, a stagewise matrix diagram `S i` (exact identities over
`A_i`) of model ranks `r i`, supported in a fixed degree window `[lo, hi]` and bounded by `B`:

* the ranks are equal to one fixed rank function `r₀` on an ultrafilter-large set
  (`exists_eventually_rank_eq`);
* lifting every entry along the surjection `Λ → A_i` on that set (and putting zero elsewhere) gives
  a retained global model `ComplexStages`, retained pairing data `RetainedLimitPairingStages` and
  a retained global duality `RetainedGlobalDualityStages`, with every identity holding modulo the
  stage ideals on the ultrafilter-large set (the identities map to the exact identities of `S i`,
  and the kernel of `Λ → A_i` is the stage ideal);
* **`exists_retained_of_stageDiagrams`**: the assembled data exist, and their matrices are lifts of
  the stage matrices (after transporting `S i` along `r i = r₀` by `StageMatrixDiagram.cast`).

Everything is ring-generic algebra. Kinds: definitions and PROVED.

There is no zero-rank stage diagram over a nontrivial ring: in degree `2` the dual coordinates
contain `lIdx 0`, the forward matrix and the dual differentials vanish there, and the target
homotopy-inverse identity would force `1 = 0`. Non-vacuity is therefore not exhibited here.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open Filter Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Manuscript.RC.Limits (StageA stageMap stageMap_surjective ker_stageMap stageIdeal
  bounded_rank_tuples_fixed)
open ZInQ.Manuscript.RC.Uniform (Lambda)

/-! ### Transport of a stage diagram along an equality of ranks -/

section Cast

variable {A : Type} [CommRing A]

/-- **Transport of a stagewise matrix diagram along an equality of rank functions** (tex
4443–4445: the ranks are fixed on a large set, and the stage diagrams are then compared in the
fixed ranks). Kind: definition. -/
def StageMatrixDiagram.cast {r r' : ℤ → ℕ} (h : r = r') (S : StageMatrixDiagram A r) :
    StageMatrixDiagram A r' :=
  h ▸ S

/-- Transport along `rfl` is the identity (tex 4443–4445). Kind: PROVED. -/
@[simp]
theorem StageMatrixDiagram.cast_rfl {r : ℤ → ℕ} (S : StageMatrixDiagram A r) :
    S.cast rfl = S :=
  rfl

/-- Transport does not change the local pairing, whose index types do not involve the ranks
(tex 4443–4445). Kind: PROVED. -/
@[simp]
theorem StageMatrixDiagram.cast_loc {r r' : ℤ → ℕ} (h : r = r') (S : StageMatrixDiagram A r)
    (a b : ℤ) : (S.cast h).loc a b = S.loc a b := by
  subst h
  rfl

end Cast

/-! ### Lifting a stage diagram along a section of a ring homomorphism -/

section Lift

variable {R A : Type} [CommRing R] [CommRing A] {f : R →+* A} (g : A → R) {rk : ℤ → ℕ}
  (T : StageMatrixDiagram A rk)

/-- The lifted model differentials (tex 4445–4447: "giving matrices over `Λ`"). Kind:
definition. -/
def StageMatrixDiagram.liftD (a b : ℤ) (h : a + 1 = b) : Matrix (Fin (rk b)) (Fin (rk a)) R :=
  (T.dC a b h).map g

/-- The lifted localization (tex 4445–4447). Kind: definition. -/
def StageMatrixDiagram.liftRes (n : ℤ) : Matrix (lIdx n) (Fin (rk n)) R :=
  (T.res n).map g

/-- The lifted global trace pairing (tex 4445–4447). Kind: definition. -/
def StageMatrixDiagram.liftGlob (a b : ℤ) (h : a + b = 3) : Matrix (Fin (rk a)) (Fin (rk b)) R :=
  (T.glob a b h).map g

/-- The lifted local pairing (tex 4445–4447). Kind: definition. -/
def StageMatrixDiagram.liftLoc (a b : ℤ) : Matrix (lIdx a) (lIdx b) R :=
  (T.loc a b).map g

/-- The lifted reverse map (tex 4445–4447). Kind: definition. -/
def StageMatrixDiagram.liftRev (a : ℤ) : Matrix (Fin (rk a)) (cIdxOf rk (3 - a)) R :=
  (T.rev a).map g

/-- The lifted source homotopy (tex 4445–4447). Kind: definition. -/
def StageMatrixDiagram.liftSrc (a b : ℤ) (h : b + 1 = a) : Matrix (Fin (rk b)) (Fin (rk a)) R :=
  (T.srcHom a b h).map g

/-- The lifted target homotopy (tex 4445–4447). Kind: definition. -/
def StageMatrixDiagram.liftTgt (a b : ℤ) (h : b + 1 = a) :
    Matrix (cIdxOf rk (3 - b)) (cIdxOf rk (3 - a)) R :=
  (T.tgtHom a b h).map g

variable {g} (hfg : ∀ x, f (g x) = x)
include hfg

/-- A lift along a section maps back to the original matrix (tex 4445–4447). Kind: PROVED. -/
theorem map_map_of_section {m n : Type} (M : Matrix m n A) : (M.map g).map f = M := by
  ext x y
  simp [hfg]

/-- The lifted differentials map back to the stage differentials (tex 4445–4447). Kind:
PROVED. -/
theorem StageMatrixDiagram.map_liftD (a b : ℤ) (h : a + 1 = b) :
    (T.liftD g a b h).map f = T.dC a b h :=
  map_map_of_section hfg _

/-- The lifted localization maps back (tex 4445–4447). Kind: PROVED. -/
theorem StageMatrixDiagram.map_liftRes (n : ℤ) : (T.liftRes g n).map f = T.res n :=
  map_map_of_section hfg _

/-- The lifted global pairing maps back (tex 4445–4447). Kind: PROVED. -/
theorem StageMatrixDiagram.map_liftGlob (a b : ℤ) (h : a + b = 3) :
    (T.liftGlob g a b h).map f = T.glob a b h :=
  map_map_of_section hfg _

/-- The lifted local pairing maps back (tex 4445–4447). Kind: PROVED. -/
theorem StageMatrixDiagram.map_liftLoc (a b : ℤ) : (T.liftLoc g a b).map f = T.loc a b :=
  map_map_of_section hfg _

/-- The lifted reverse map maps back (tex 4445–4447). Kind: PROVED. -/
theorem StageMatrixDiagram.map_liftRev (a : ℤ) : (T.liftRev g a).map f = T.rev a :=
  map_map_of_section hfg _

/-- The lifted source homotopy maps back (tex 4445–4447). Kind: PROVED. -/
theorem StageMatrixDiagram.map_liftSrc (a b : ℤ) (h : b + 1 = a) :
    (T.liftSrc g a b h).map f = T.srcHom a b h :=
  map_map_of_section hfg _

/-- The lifted target homotopy maps back (tex 4445–4447). Kind: PROVED. -/
theorem StageMatrixDiagram.map_liftTgt (a b : ℤ) (h : b + 1 = a) :
    (T.liftTgt g a b h).map f = T.tgtHom a b h :=
  map_map_of_section hfg _

omit hfg in
/-- A matrix killed entrywise by `f` has its entries in the kernel of `f` (tex 4447–4448: "Every
polynomial identity between the matrices survives"). Kind: PROVED. -/
theorem mem_ker_of_map_eq_zero {m n : Type} {M : Matrix m n R} (hM : M.map f = 0) :
    ∀ x y, M x y ∈ RingHom.ker f := by
  intro x y
  rw [RingHom.mem_ker]
  have e := congrArg (fun N : Matrix m n A => N x y) hM
  simpa using e

/-- `d_C² = 0` for the lifts holds modulo the kernel (tex 4447–4448). Kind: PROVED. -/
theorem StageMatrixDiagram.lift_sq (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c) :
    ∀ x y, (T.liftD g b c hbc * T.liftD g a b hab) x y ∈ RingHom.ker f := by
  apply mem_ker_of_map_eq_zero
  rw [Matrix.map_mul, T.map_liftD hfg, T.map_liftD hfg]
  exact T.dC_sq a b c hab hbc

/-- The lifted localization is a chain map modulo the kernel (tex 4447–4448). Kind: PROVED. -/
theorem StageMatrixDiagram.lift_res_comm (n : ℤ) :
    ∀ x y, (T.liftRes g (n + 1) * T.liftD g n (n + 1) rfl) x y ∈ RingHom.ker f := by
  apply mem_ker_of_map_eq_zero
  rw [Matrix.map_mul, T.map_liftD hfg, T.map_liftRes hfg]
  exact T.res_comm n

/-- Chain-level reciprocity for the lifts modulo the kernel (tex 4447–4448). Kind: PROVED. -/
theorem StageMatrixDiagram.lift_recip (a b : ℤ) (h : a + b = 2) :
    ∀ x y, ((T.liftD g a (a + 1) rfl)ᵀ * T.liftGlob g (a + 1) b (by omega) +
        sgn a • (T.liftGlob g a (b + 1) (by omega) * T.liftD g b (b + 1) rfl) +
        (T.liftRes g a)ᵀ * T.liftLoc g a b * T.liftRes g b) x y ∈ RingHom.ker f := by
  apply mem_ker_of_map_eq_zero
  rw [map_recip_formula]
  simp only [T.map_liftD hfg, T.map_liftRes hfg, T.map_liftGlob hfg, T.map_liftLoc hfg]
  exact T.recip a b h

/-- The lifted reverse map is a chain map modulo the kernel (tex 4447–4450). Kind: PROVED. -/
theorem StageMatrixDiagram.lift_chain (a : ℤ) :
    ∀ x y, (T.liftRev g (a + 1) * dualDiffMatOf (T.liftD g) (T.liftRes g) a (a + 1) rfl -
      T.liftD g a (a + 1) rfl * T.liftRev g a) x y ∈ RingHom.ker f := by
  apply mem_ker_of_map_eq_zero
  rw [matrix_map_sub, Matrix.map_mul, Matrix.map_mul, dualDiffMatOf_map]
  simp only [T.map_liftD hfg, T.map_liftRes hfg, T.map_liftRev hfg]
  exact T.chain a

/-- The first homotopy-inverse identity for the lifts modulo the kernel (tex 4449–4450:
"Retained homotopy inverses remain homotopy inverses"). Kind: PROVED. -/
theorem StageMatrixDiagram.lift_src (a : ℤ) :
    ∀ x y, (T.liftRev g a * forwardMatOf (T.liftGlob g) (T.liftLoc g) (T.liftRes g) a -
      T.liftSrc g (a + 1) a rfl * T.liftD g a (a + 1) rfl -
      T.liftD g (a - 1) a (by omega) * T.liftSrc g a (a - 1) (by omega) - 1 :
        Matrix (Fin (rk a)) (Fin (rk a)) R) x y ∈ RingHom.ker f := by
  apply mem_ker_of_map_eq_zero
  rw [matrix_map_sub, matrix_map_sub, matrix_map_sub, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, forwardMatOf_map, Matrix.map_one _ (map_zero f) (map_one f)]
  simp only [T.map_liftD hfg, T.map_liftRes hfg, T.map_liftGlob hfg, T.map_liftLoc hfg,
    T.map_liftRev hfg, T.map_liftSrc hfg]
  exact T.src a

/-- The second homotopy-inverse identity for the lifts modulo the kernel (tex 4449–4450).
Kind: PROVED. -/
theorem StageMatrixDiagram.lift_tgt (a : ℤ) :
    ∀ x y, (forwardMatOf (T.liftGlob g) (T.liftLoc g) (T.liftRes g) a * T.liftRev g a -
      T.liftTgt g (a + 1) a rfl * dualDiffMatOf (T.liftD g) (T.liftRes g) a (a + 1) rfl -
      dualDiffMatOf (T.liftD g) (T.liftRes g) (a - 1) a (by omega) *
        T.liftTgt g a (a - 1) (by omega) - 1 :
        Matrix (cIdxOf rk (3 - a)) (cIdxOf rk (3 - a)) R) x y ∈ RingHom.ker f := by
  apply mem_ker_of_map_eq_zero
  rw [matrix_map_sub, matrix_map_sub, matrix_map_sub, Matrix.map_mul, Matrix.map_mul,
    Matrix.map_mul, forwardMatOf_map, dualDiffMatOf_map, dualDiffMatOf_map,
    Matrix.map_one _ (map_zero f) (map_one f)]
  simp only [T.map_liftD hfg, T.map_liftRes hfg, T.map_liftGlob hfg, T.map_liftLoc hfg,
    T.map_liftRev hfg, T.map_liftTgt hfg]
  exact T.tgt a

end Lift

/-! ### Fixing the ranks on an ultrafilter-large set -/

/-- **Bounded ranks can be fixed on a set in the ultrafilter** (tex 4400–4402, 4444–4445): rank
functions vanishing outside the window `[lo, hi]` and bounded by `B` are equal to one fixed rank
function `r₀` (also vanishing outside the window and bounded by `B`) on a set in `U`. Kind:
PROVED. -/
theorem exists_eventually_rank_eq (U : Ultrafilter ℕ) (r : ℕ → ℤ → ℕ) (lo hi : ℤ) (B : ℕ)
    (hbdd : ∀ i n, n < lo ∨ hi < n → r i n = 0) (hB : ∀ i n, r i n ≤ B) :
    ∃ r₀ : ℤ → ℕ, (∀ n, r₀ n ≤ B) ∧ (∀ n, n < lo ∨ hi < n → r₀ n = 0) ∧
      ∀ᶠ i in (U : Filter ℕ), r i = r₀ := by
  obtain ⟨t, htB, ht⟩ := bounded_rank_tuples_fixed U (B := B)
    (fun i (j : Finset.Icc lo hi) => r i j) (fun i j => hB i j)
  refine ⟨fun n => if h : n ∈ Finset.Icc lo hi then t ⟨n, h⟩ else 0, ?_, ?_, ?_⟩
  · intro n
    by_cases hn : n ∈ Finset.Icc lo hi
    · beta_reduce
      rw [dite_eq_left hn]
      exact htB _
    · beta_reduce
      rw [dite_eq_right hn]
      exact Nat.zero_le B
  · intro n hn
    have hn' : n ∉ Finset.Icc lo hi := by
      rw [Finset.mem_Icc]
      omega
    beta_reduce
    rw [dite_eq_right hn']
  · refine ht.mono fun i hti => funext fun n => ?_
    by_cases hn : n ∈ Finset.Icc lo hi
    · rw [dite_eq_left hn]
      exact congrFun hti ⟨n, hn⟩
    · rw [dite_eq_right hn]
      apply hbdd
      rw [Finset.mem_Icc] at hn
      omega

/-! ### The assembled matrices over `Λ` -/

/-- A chosen lift `A_i → Λ` along the surjection `Λ → A_i` (tex 4445–4447). Kind:
definition. -/
def stageLift (i : ℕ) : StageA i → Lambda :=
  Function.surjInv (stageMap_surjective i)

/-- The chosen lift is a section of `Λ → A_i` (tex 4445–4447). Kind: PROVED. -/
theorem stageMap_stageLift (i : ℕ) (x : StageA i) : stageMap i (stageLift i x) = x :=
  Function.surjInv_eq (stageMap_surjective i) x

section Assembly

variable (r₀ : ℤ → ℕ) (r : ℕ → ℤ → ℕ) (S : ∀ i, StageMatrixDiagram (StageA i) (r i))

open Classical in
/-- The assembled differentials over `Λ`: lifts of the stage differentials at the stages where
the ranks are `r₀`, zero elsewhere (tex 4445–4447). Kind: definition. -/
def assembledD (i : ℕ) (a b : ℤ) (hab : a + 1 = b) : Matrix (Fin (r₀ b)) (Fin (r₀ a)) Lambda :=
  if h : r i = r₀ then ((S i).cast h).liftD (stageLift i) a b hab else 0

open Classical in
/-- The assembled localization over `Λ` (tex 4445–4447). Kind: definition. -/
def assembledRes (i : ℕ) (n : ℤ) : Matrix (lIdx n) (Fin (r₀ n)) Lambda :=
  if h : r i = r₀ then ((S i).cast h).liftRes (stageLift i) n else 0

open Classical in
/-- The assembled global trace pairing over `Λ` (tex 4445–4447). Kind: definition. -/
def assembledGlob (i : ℕ) (a b : ℤ) (hab : a + b = 3) :
    Matrix (Fin (r₀ a)) (Fin (r₀ b)) Lambda :=
  if h : r i = r₀ then ((S i).cast h).liftGlob (stageLift i) a b hab else 0

/-- The assembled local pairing over `Λ` (its index types do not involve the ranks, so it is the
lift at every stage; tex 4445–4447). Kind: definition. -/
def assembledLoc (i : ℕ) (a b : ℤ) : Matrix (lIdx a) (lIdx b) Lambda :=
  (S i).liftLoc (stageLift i) a b

open Classical in
/-- The assembled reverse map over `Λ` (tex 4445–4447). Kind: definition. -/
def assembledRev (i : ℕ) (a : ℤ) : Matrix (Fin (r₀ a)) (cIdxOf r₀ (3 - a)) Lambda :=
  if h : r i = r₀ then ((S i).cast h).liftRev (stageLift i) a else 0

open Classical in
/-- The assembled source homotopy over `Λ` (tex 4445–4447). Kind: definition. -/
def assembledSrc (i : ℕ) (a b : ℤ) (hab : b + 1 = a) :
    Matrix (Fin (r₀ b)) (Fin (r₀ a)) Lambda :=
  if h : r i = r₀ then ((S i).cast h).liftSrc (stageLift i) a b hab else 0

open Classical in
/-- The assembled target homotopy over `Λ` (tex 4445–4447). Kind: definition. -/
def assembledTgt (i : ℕ) (a b : ℤ) (hab : b + 1 = a) :
    Matrix (cIdxOf r₀ (3 - b)) (cIdxOf r₀ (3 - a)) Lambda :=
  if h : r i = r₀ then ((S i).cast h).liftTgt (stageLift i) a b hab else 0

variable {r₀ r S} {i : ℕ} (h : r i = r₀)
include h

/-- On a stage with ranks `r₀`, the assembled differentials are the lifts (tex 4445–4447).
Kind: PROVED. -/
theorem assembledD_eq : assembledD r₀ r S i = ((S i).cast h).liftD (stageLift i) := by
  funext a b hab
  unfold assembledD
  rw [dite_eq_left h]

/-- On a stage with ranks `r₀`, the assembled localization is the lift (tex 4445–4447). Kind:
PROVED. -/
theorem assembledRes_eq : assembledRes r₀ r S i = ((S i).cast h).liftRes (stageLift i) := by
  funext n
  unfold assembledRes
  rw [dite_eq_left h]

/-- On a stage with ranks `r₀`, the assembled global pairing is the lift (tex 4445–4447). Kind:
PROVED. -/
theorem assembledGlob_eq : assembledGlob r₀ r S i = ((S i).cast h).liftGlob (stageLift i) := by
  funext a b hab
  unfold assembledGlob
  rw [dite_eq_left h]

/-- The assembled local pairing is the lift of the transported one (tex 4445–4447). Kind:
PROVED. -/
theorem assembledLoc_eq : assembledLoc r S i = ((S i).cast h).liftLoc (stageLift i) := by
  funext a b
  unfold assembledLoc StageMatrixDiagram.liftLoc
  rw [StageMatrixDiagram.cast_loc]

/-- On a stage with ranks `r₀`, the assembled reverse map is the lift (tex 4445–4447). Kind:
PROVED. -/
theorem assembledRev_eq : assembledRev r₀ r S i = ((S i).cast h).liftRev (stageLift i) := by
  funext a
  unfold assembledRev
  rw [dite_eq_left h]

/-- On a stage with ranks `r₀`, the assembled source homotopy is the lift (tex 4445–4447). Kind:
PROVED. -/
theorem assembledSrc_eq : assembledSrc r₀ r S i = ((S i).cast h).liftSrc (stageLift i) := by
  funext a b hab
  unfold assembledSrc
  rw [dite_eq_left h]

/-- On a stage with ranks `r₀`, the assembled target homotopy is the lift (tex 4445–4447). Kind:
PROVED. -/
theorem assembledTgt_eq : assembledTgt r₀ r S i = ((S i).cast h).liftTgt (stageLift i) := by
  funext a b hab
  unfold assembledTgt
  rw [dite_eq_left h]

omit h in
/-- The assembled local pairing maps to the stage local pairing at every stage (tex 4445–4447).
Kind: PROVED. -/
theorem map_assembledLoc (i : ℕ) (a b : ℤ) :
    (assembledLoc r S i a b).map (stageMap i) = (S i).loc a b :=
  (S i).map_liftLoc (stageMap_stageLift i) a b

/-! #### The identities modulo the stage ideal, at a stage with ranks `r₀` -/

/-- `d_C² = 0` modulo the stage ideal (tex 4447–4448). Kind: PROVED. -/
theorem assembled_square_at (a b c : ℤ) (hab : a + 1 = b) (hbc : b + 1 = c) :
    ∀ x y, (assembledD r₀ r S i b c hbc * assembledD r₀ r S i a b hab) x y ∈ stageIdeal i := by
  rw [assembledD_eq h, ← ker_stageMap]
  exact ((S i).cast h).lift_sq (stageMap_stageLift i) a b c hab hbc

/-- The localization is a chain map modulo the stage ideal (tex 4447–4448). Kind: PROVED. -/
theorem assembled_res_comm_at (n : ℤ) :
    ∀ x y, (assembledRes r₀ r S i (n + 1) * assembledD r₀ r S i n (n + 1) rfl) x y ∈
      stageIdeal i := by
  rw [assembledD_eq h, assembledRes_eq h, ← ker_stageMap]
  exact ((S i).cast h).lift_res_comm (stageMap_stageLift i) n

/-- Chain-level reciprocity modulo the stage ideal (tex 4447–4448). Kind: PROVED. -/
theorem assembled_recip_at (a b : ℤ) (hs : a + b = 2) :
    ∀ x y, ((assembledD r₀ r S i a (a + 1) rfl)ᵀ * assembledGlob r₀ r S i (a + 1) b (by omega) +
        sgn a • (assembledGlob r₀ r S i a (b + 1) (by omega) * assembledD r₀ r S i b (b + 1) rfl) +
        (assembledRes r₀ r S i a)ᵀ * assembledLoc r S i a b * assembledRes r₀ r S i b) x y ∈
      stageIdeal i := by
  rw [assembledD_eq h, assembledRes_eq h, assembledGlob_eq h, assembledLoc_eq h, ← ker_stageMap]
  exact ((S i).cast h).lift_recip (stageMap_stageLift i) a b hs

/-- The reverse map is a chain map modulo the stage ideal (tex 4447–4450). Kind: PROVED. -/
theorem assembled_chain_at (a : ℤ) :
    ∀ x y, (assembledRev r₀ r S i (a + 1) *
        dualDiffMatOf (assembledD r₀ r S i) (assembledRes r₀ r S i) a (a + 1) rfl -
      assembledD r₀ r S i a (a + 1) rfl * assembledRev r₀ r S i a) x y ∈ stageIdeal i := by
  rw [assembledD_eq h, assembledRes_eq h, assembledRev_eq h, ← ker_stageMap]
  exact ((S i).cast h).lift_chain (stageMap_stageLift i) a

/-- The first homotopy-inverse identity modulo the stage ideal (tex 4449–4450). Kind:
PROVED. -/
theorem assembled_src_at (a : ℤ) :
    ∀ x y, (assembledRev r₀ r S i a *
        forwardMatOf (assembledGlob r₀ r S i) (assembledLoc r S i) (assembledRes r₀ r S i) a -
      assembledSrc r₀ r S i (a + 1) a rfl * assembledD r₀ r S i a (a + 1) rfl -
      assembledD r₀ r S i (a - 1) a (by omega) * assembledSrc r₀ r S i a (a - 1) (by omega) - 1 :
        Matrix (Fin (r₀ a)) (Fin (r₀ a)) Lambda) x y ∈ stageIdeal i := by
  rw [assembledD_eq h, assembledRes_eq h, assembledGlob_eq h, assembledLoc_eq h,
    assembledRev_eq h, assembledSrc_eq h, ← ker_stageMap]
  exact ((S i).cast h).lift_src (stageMap_stageLift i) a

/-- The second homotopy-inverse identity modulo the stage ideal (tex 4449–4450). Kind:
PROVED. -/
theorem assembled_tgt_at (a : ℤ) :
    ∀ x y, (forwardMatOf (assembledGlob r₀ r S i) (assembledLoc r S i)
        (assembledRes r₀ r S i) a * assembledRev r₀ r S i a -
      assembledTgt r₀ r S i (a + 1) a rfl *
        dualDiffMatOf (assembledD r₀ r S i) (assembledRes r₀ r S i) a (a + 1) rfl -
      dualDiffMatOf (assembledD r₀ r S i) (assembledRes r₀ r S i) (a - 1) a (by omega) *
        assembledTgt r₀ r S i a (a - 1) (by omega) - 1 :
        Matrix (cIdxOf r₀ (3 - a)) (cIdxOf r₀ (3 - a)) Lambda) x y ∈ stageIdeal i := by
  rw [assembledD_eq h, assembledRes_eq h, assembledGlob_eq h, assembledLoc_eq h,
    assembledRev_eq h, assembledTgt_eq h, ← ker_stageMap]
  exact ((S i).cast h).lift_tgt (stageMap_stageLift i) a

/-! #### The assembled matrices are lifts of the stage matrices -/

/-- The assembled differentials map to the stage differentials (tex 4445–4447). Kind:
PROVED. -/
theorem map_assembledD (a b : ℤ) (hab : a + 1 = b) :
    (assembledD r₀ r S i a b hab).map (stageMap i) = ((S i).cast h).dC a b hab := by
  rw [assembledD_eq h]
  exact ((S i).cast h).map_liftD (stageMap_stageLift i) a b hab

/-- The assembled localization maps to the stage localization (tex 4445–4447). Kind: PROVED. -/
theorem map_assembledRes (n : ℤ) :
    (assembledRes r₀ r S i n).map (stageMap i) = ((S i).cast h).res n := by
  rw [assembledRes_eq h]
  exact ((S i).cast h).map_liftRes (stageMap_stageLift i) n

/-- The assembled global pairing maps to the stage global pairing (tex 4445–4447). Kind:
PROVED. -/
theorem map_assembledGlob (a b : ℤ) (hab : a + b = 3) :
    (assembledGlob r₀ r S i a b hab).map (stageMap i) = ((S i).cast h).glob a b hab := by
  rw [assembledGlob_eq h]
  exact ((S i).cast h).map_liftGlob (stageMap_stageLift i) a b hab

/-- The assembled reverse map maps to the stage reverse map (tex 4445–4447). Kind: PROVED. -/
theorem map_assembledRev (a : ℤ) :
    (assembledRev r₀ r S i a).map (stageMap i) = ((S i).cast h).rev a := by
  rw [assembledRev_eq h]
  exact ((S i).cast h).map_liftRev (stageMap_stageLift i) a

/-- The assembled source homotopy maps to the stage source homotopy (tex 4445–4447). Kind:
PROVED. -/
theorem map_assembledSrc (a b : ℤ) (hab : b + 1 = a) :
    (assembledSrc r₀ r S i a b hab).map (stageMap i) = ((S i).cast h).srcHom a b hab := by
  rw [assembledSrc_eq h]
  exact ((S i).cast h).map_liftSrc (stageMap_stageLift i) a b hab

/-- The assembled target homotopy maps to the stage target homotopy (tex 4445–4447). Kind:
PROVED. -/
theorem map_assembledTgt (a b : ℤ) (hab : b + 1 = a) :
    (assembledTgt r₀ r S i a b hab).map (stageMap i) = ((S i).cast h).tgtHom a b hab := by
  rw [assembledTgt_eq h]
  exact ((S i).cast h).map_liftTgt (stageMap_stageLift i) a b hab

end Assembly

/-! ### The assembled retained diagram -/

section Retained

variable (r₀ : ℤ → ℕ) (r : ℕ → ℤ → ℕ) (S : ∀ i, StageMatrixDiagram (StageA i) (r i))
  (U : Ultrafilter ℕ) (lo hi : ℤ) (hbdd₀ : ∀ n, n < lo ∨ hi < n → r₀ n = 0)
  (hr : ∀ᶠ i in (U : Filter ℕ), r i = r₀)

/-- **The assembled retained global model** (tex 4400–4406, 4443–4448): ranks `r₀` in the window
`[lo, hi]`, differentials the assembled lifts, `d_C² = 0` modulo the stage ideals on the set in
`U` where the stage ranks are `r₀`. Kind: definition. -/
def assembledComplex : ComplexStages (R := Lambda) stageIdeal U where
  rank := r₀
  low := lo
  high := hi
  bounded := hbdd₀
  d := assembledD r₀ r S
  square a b c hab hbc := hr.mono fun _ h => assembled_square_at h a b c hab hbc

/-- **The assembled retained pairing data** (tex 4400–4406, 4443–4448): the assembled
localization, global trace pairing and local pairing, with the chain-map property and chain-level
reciprocity modulo the stage ideals on the set in `U`. Kind: definition. -/
def assembledPairing :
    RetainedLimitPairingStages U (assembledComplex r₀ r S U lo hi hbdd₀ hr) where
  res n i := assembledRes r₀ r S i n
  res_comm n := hr.mono fun _ h => assembled_res_comm_at h n
  glob a b hab i := assembledGlob r₀ r S i a b hab
  loc a b i := assembledLoc r S i a b
  recip a b hs := hr.mono fun _ h => assembled_recip_at h a b hs

/-- **The assembled retained global duality** (tex 4400–4406, 4443–4451: "Retained homotopy
inverses remain homotopy inverses"): the assembled reverse map and homotopies, with the chain-map
property and both homotopy-inverse identities modulo the stage ideals on the set in `U`. Kind:
definition. -/
def assembledDuality : RetainedGlobalDualityStages (assembledPairing r₀ r S U lo hi hbdd₀ hr) where
  rev a i := assembledRev r₀ r S i a
  srcHom a b hab i := assembledSrc r₀ r S i a b hab
  tgtHom a b hab i := assembledTgt r₀ r S i a b hab
  chain a := hr.mono fun _ h => assembled_chain_at h a
  src a := hr.mono fun _ h => assembled_src_at h a
  tgt a := hr.mono fun _ h => assembled_tgt_at h a

end Retained

/-- **The stage-to-`Λ` ultralimit diagram** (Lemma `ex:limits-inner-limit`, tex 4400–4406 and
4443–4451): given, at every coefficient stage `A_i`, a stagewise matrix diagram `S i` with exact
identities, of model ranks `r i` vanishing outside `[lo, hi]` and bounded by `B`, there are a rank
function `r₀` (bounded by `B`) equal to `r i` on a set in `U`, a retained global model `C` of ranks
`r₀` in the window `[lo, hi]`, retained pairing data `D` and a retained global duality `E` over `Λ`
(all identities modulo the stage ideals on a set in `U`), whose matrices are, on a set in `U`,
lifts along `Λ → A_i` of the matrices of `S i` (transported along `r i = C.rank`). The assembly
uses only that `U` is an ultrafilter; nonprincipality (`_hU`) is needed only later, for the
limits. Kind: PROVED. -/
theorem exists_retained_of_stageDiagrams (U : Ultrafilter ℕ)
    (_hU : (U : Filter ℕ) ≤ Filter.cofinite)
    (r : ℕ → ℤ → ℕ) (S : ∀ i, StageMatrixDiagram (StageA i) (r i)) (lo hi : ℤ) (B : ℕ)
    (hbdd : ∀ i n, n < lo ∨ hi < n → r i n = 0) (hB : ∀ i n, r i n ≤ B) :
    ∃ (r₀ : ℤ → ℕ) (C : ComplexStages (R := Lambda) stageIdeal U)
      (D : RetainedLimitPairingStages U C) (E : RetainedGlobalDualityStages D),
      C.rank = r₀ ∧ C.low = lo ∧ C.high = hi ∧ (∀ n, r₀ n ≤ B) ∧
      (∀ᶠ i in (U : Filter ℕ), r i = r₀) ∧
      (∀ i a b, (D.loc a b i).map (stageMap i) = (S i).loc a b) ∧
      ∀ᶠ i in (U : Filter ℕ), ∃ h : r i = C.rank,
        (∀ a b hab, (C.d i a b hab).map (stageMap i) = ((S i).cast h).dC a b hab) ∧
        (∀ n, (D.res n i).map (stageMap i) = ((S i).cast h).res n) ∧
        (∀ a b hab, (D.glob a b hab i).map (stageMap i) = ((S i).cast h).glob a b hab) ∧
        (∀ a, (E.rev a i).map (stageMap i) = ((S i).cast h).rev a) ∧
        (∀ a b hab, (E.srcHom a b hab i).map (stageMap i) = ((S i).cast h).srcHom a b hab) ∧
        (∀ a b hab, (E.tgtHom a b hab i).map (stageMap i) = ((S i).cast h).tgtHom a b hab) := by
  obtain ⟨r₀, hr₀B, hbdd₀, hr⟩ := exists_eventually_rank_eq U r lo hi B hbdd hB
  refine ⟨r₀, assembledComplex r₀ r S U lo hi hbdd₀ hr, assembledPairing r₀ r S U lo hi hbdd₀ hr,
    assembledDuality r₀ r S U lo hi hbdd₀ hr, rfl, rfl, rfl, hr₀B, hr,
    fun i a b => map_assembledLoc i a b, ?_⟩
  refine hr.mono fun i h => ⟨h, ?_⟩
  exact ⟨fun a b hab => map_assembledD h a b hab, fun n => map_assembledRes h n,
    fun a b hab => map_assembledGlob h a b hab, fun a => map_assembledRev h a,
    fun a b hab => map_assembledSrc h a b hab, fun a b hab => map_assembledTgt h a b hab⟩

end ZInQ.Manuscript.RC.FibreDuality
