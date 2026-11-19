import ZInQKernel.Contrib.OneProof.RC.FibreDuality.LimitTransport

/-!
# Lane RC31, round 2, part 5: the retained stage data of the paired limit diagram

Manuscript `diophantine_zq.tex`, Lemma `ex:limits-inner-limit` (tex 4391–4451): finite free
models at the coefficient stages `A_i = Λ/(2^i, t^i)`, with "every fixed finite diagram of maps
and homotopies, including the duality and local-condition data used here", transported to them;
"One fixed nonprincipal ultrafilter gives a diagram over `Λ` at all coefficient precisions,
preserving its matrix identities and retained homotopy inverses"; "Mere stagewise
quasi-isomorphisms without those maps would not justify a nonflat coefficient change". And tex
4385–4388: "The same retained data include the integral duality maps, their homotopy inverses, and
the homotopies expressing compatibility of duality with localization."

This file records, for a retained global model `C` (lifted stage matrices over `Λ`, identities
modulo the stage ideals on one ultrafilter-large set), the retained localization at the derivative
label, the retained global trace pairing and the retained local pairing, with chain-level
reciprocity at every stage (`RetainedLimitPairingStages`), and proves that after the inner limit and
the specialization to `k(𝔭)` they give the matrix data of `LimitMatrices.lean` with exact
identities (`resLimit`, `reciprocity_limit`).

Kinds: definitions (the retained data, ELLIOT: Lemma `ex:limits-inner-limit` supplies them for the
realized diagram) and PROVED (their limits).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open Filter Matrix
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.RC53Assist.InnerLimit
open ZInQ.Manuscript.RC.Limits (ulimMat ulimMat_mul ulimMat_add ulimMat_sub ulimMat_eq_zero_of_mem
  stageIdeal stageIdeal_tendsToZero)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open scoped PowerSeries.WithPiTopology

/-! ### Ultralimits of matrix formulas -/

section Ulim

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R]

omit [CommRing R] [IsTopologicalRing R] in
/-- Transposition commutes with the entrywise ultralimit. Kind: PROVED. -/
theorem ulimMat_transpose {R : Type} [TopologicalSpace R] [CompactSpace R] [T2Space R]
    {m n : Type} (U : Ultrafilter ℕ) (M : ℕ → Matrix m n R) :
    ulimMat U (fun i => (M i)ᵀ) = (ulimMat U M)ᵀ :=
  rfl

/-- Integer multiples commute with the entrywise ultralimit. Kind: PROVED. -/
theorem ulimMat_zsmul {m n : Type} (U : Ultrafilter ℕ) (z : ℤ) (M : ℕ → Matrix m n R) :
    ulimMat U (fun i => z • M i) = z • ulimMat U M := by
  ext a b
  change ZInQ.Manuscript.RC.Limits.ulim U (fun i => z • M i a b) =
    z • ZInQ.Manuscript.RC.Limits.ulim U (fun i => M i a b)
  simp only [zsmul_eq_mul]
  rw [ZInQ.Manuscript.RC.Limits.ulim_mul, ZInQ.Manuscript.RC.Limits.ulim_intCast]

end Ulim

/-- A ring homomorphism commutes with the matrix formula of reciprocity. Kind: PROVED. -/
theorem map_recip_formula {S T : Type} [CommRing S] [CommRing T] (f : S →+* T)
    {m n p q l l' : Type} [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype l] [Fintype l']
    (A : Matrix m n S) (B : Matrix m p S) (z : ℤ) (C' : Matrix n q S) (D' : Matrix q p S)
    (E : Matrix l n S) (F : Matrix l l' S) (G : Matrix l' p S) :
    (Aᵀ * B + z • (C' * D') + Eᵀ * F * G).map f =
      (A.map f)ᵀ * B.map f + z • (C'.map f * D'.map f) + (E.map f)ᵀ * F.map f * G.map f := by
  ext x y
  simp [Matrix.mul_apply, map_sum, map_mul, map_add]


/-! ### The retained pairing data at the stages -/

variable (U : Ultrafilter ℕ) (C : ComplexStages (R := Lambda) stageIdeal U)

/-- **The retained pairing data of the limit diagram at the coefficient stages** (ELLIOT, Lemma
`ex:limits-inner-limit`, tex 4391–4451, for the realized diagram): lifted stage matrices over `Λ`
of the localization at the derivative label (`res`, in the coordinates `lIdx` of the split model),
of the global trace pairing (`glob`: the trace of the retained global cup product) and of the
local pairing (`loc`), with the chain-map property of the localization (`res_comm`) and chain-level
reciprocity (`recip`: the trace of the retained Leibniz rule and compatibility of the cup product)
modulo the stage ideals on one ultrafilter-large set. Kind: definition (hypothesis structure). -/
structure RetainedLimitPairingStages where
  /-- The retained localization at the derivative label. -/
  res : ∀ n : ℤ, ℕ → Matrix (lIdx n) (Fin (C.rank n)) Lambda
  /-- It is a chain map at the retained precision (the split model has zero differential). -/
  res_comm : ∀ n : ℤ, ∀ᶠ i in (U : Filter ℕ), ∀ x y,
    (res (n + 1) i * C.d i n (n + 1) rfl) x y ∈ stageIdeal i
  /-- The retained global trace pairing `G^a × G^b → Λ`, `a + b = 3`. -/
  glob : ∀ a b : ℤ, a + b = 3 → ℕ → Matrix (Fin (C.rank a)) (Fin (C.rank b)) Lambda
  /-- The retained local pairing of the split model. -/
  loc : ∀ a b : ℤ, ℕ → Matrix (lIdx a) (lIdx b) Lambda
  /-- Chain-level reciprocity at the retained precision. -/
  recip : ∀ (a b : ℤ) (h : a + b = 2), ∀ᶠ i in (U : Filter ℕ), ∀ x y,
    ((C.d i a (a + 1) rfl)ᵀ * glob (a + 1) b (by omega) i +
        sgn a • (glob a (b + 1) (by omega) i * C.d i b (b + 1) rfl) +
        (res a i)ᵀ * loc a b i * res b i) x y ∈ stageIdeal i

variable {U C} (hU : (U : Filter ℕ) ≤ Filter.cofinite) (D : RetainedLimitPairingStages U C)
  (P : Ideal Lambda) [P.IsPrime]

/-- The localization matrices after the inner limit, at `k(𝔭)`. Kind: definition. -/
abbrev RetainedLimitPairingStages.resK (n : ℤ) : Matrix (lIdx n) (Fin (C.rank n)) (ResAt P) :=
  (ulimMat U (D.res n)).map (algebraMap Lambda (ResAt P))

/-- The global trace pairing matrices after the inner limit, at `k(𝔭)`. Kind: definition. -/
abbrev RetainedLimitPairingStages.globK (a b : ℤ) (h : a + b = 3) :
    Matrix (Fin (C.rank a)) (Fin (C.rank b)) (ResAt P) :=
  (ulimMat U (D.glob a b h)).map (algebraMap Lambda (ResAt P))

/-- The local pairing matrices after the inner limit, at `k(𝔭)`. Kind: definition. -/
abbrev RetainedLimitPairingStages.locK (a b : ℤ) : Matrix (lIdx a) (lIdx b) (ResAt P) :=
  (ulimMat U (D.loc a b)).map (algebraMap Lambda (ResAt P))

include hU in
/-- **The limit localization is a chain map**: `R(n + 1) ⋅ d = 0` exactly at `k(𝔭)`. Kind:
PROVED. -/
theorem RetainedLimitPairingStages.resK_comm (n : ℤ) :
    D.resK P (n + 1) * specDiff (algebraMap Lambda (ResAt P)) C n (n + 1) rfl = 0 := by
  have h := ulimMat_eq_zero_of_mem stageIdeal_tendsToZero hU (D.res_comm n)
  rw [ulimMat_mul] at h
  unfold RetainedLimitPairingStages.resK specDiff
  rw [← Matrix.map_mul, h, Matrix.map_zero _ (map_zero _)]

/-- **The localization of the realized limit diagram at the derivative label**, at `k(𝔭)`: the
chain map `fibreLimitGlobal → splitLocalComplex` of the retained localization. Kind:
definition. -/
def RetainedLimitPairingStages.resLimit :
    GHom (fibreLimitGlobal U hU P C) (splitLocalComplex (ResAt P)) :=
  resOfMat stageIdeal_tendsToZero hU (algebraMap Lambda (ResAt P)) C (D.resK P) (D.resK_comm hU P)

include hU in
/-- **Chain-level reciprocity survives the inner limit** (Lemma `ex:limits-inner-limit`: "Every
polynomial identity between the matrices survives"). Kind: PROVED. -/
theorem RetainedLimitPairingStages.matReciprocity :
    MatReciprocity (algebraMap Lambda (ResAt P)) C (D.resK P) (D.globK P) (D.locK P) := by
  intro a b h
  have e := ulimMat_eq_zero_of_mem stageIdeal_tendsToZero hU (D.recip a b h)
  rw [ulimMat_add, ulimMat_add, ulimMat_mul, ulimMat_transpose, ulimMat_zsmul, ulimMat_mul,
    ulimMat_mul, ulimMat_mul, ulimMat_transpose] at e
  have e' := congrArg (fun M => M.map (algebraMap Lambda (ResAt P))) e
  simp only [Matrix.map_zero _ (map_zero _)] at e'
  rw [map_recip_formula] at e'
  exact e'

end ZInQ.Manuscript.RC.FibreDuality
