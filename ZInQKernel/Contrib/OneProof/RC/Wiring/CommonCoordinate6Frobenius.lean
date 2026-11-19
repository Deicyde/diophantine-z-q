import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate5Objects
import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.Conjugation
import ZInQKernel.Contrib.OneProof.RC.GlueSweep.TatePrecision
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Frobenius

/-!
# Theorem 5.3, Lane RC32 round 2: the actual Frobenius matrix at a graph prime

Lemma `ex:arith-common-coordinate` (tex 4209–4213): at an unused good split prime `q`, "the
Frobenius at `q` has trace `a_q` and determinant `q`" on `T = T₂E` (tex 2836–2838: `T₂E` with its
`G_{K,S}`-action `ρ_T`). The round-one leaf (`CommonCoordinate5.lean`) took a free `ℤ₂`-matrix
with these trace and determinant. Here the matrix is the actual one:

* `frobQ q`: an arithmetic Frobenius element at `q` in `G_ℚ` (a choice; it exists at every prime,
  lane RC24's `AddressGenuine.frobeniusExists`, PROVED from the surjectivity of the decomposition
  group onto the residue automorphisms); `isFrobAt_frobQ`, and `isFrobAtC10_frobQ` in the form the
  Chebotarev files and the GLUE `FrobeniusTrace` use;
* `TateCoef E`: the coefficient datum of `𝕋` — a number field `K`, a set `S` of its primes, an
  identification `K̄ ≃ ℚ̄`, and `E[2^∞] ⊆ E(K_S)` (lane RC28's `HasFullTwoTorsion`) — so that lane
  RC28's `tateBasis` is a `ℤ₂`-basis of `T₂E` over `K_S`;
* `frobMat C q`: the matrix of `ρ_T(Fr_q)` in that basis (the transported action `rhoKMatrix` of
  `InnerLimitArith/Conjugation.lean`); when `Fr_q` fixes `K` (the text's split primes) it is the
  matrix of the native `G_{K,S}`-action of the Frobenius on lane RC28's `T₂E` over `K_S`
  (`frobMat_eq_native`);
* `det_frobMat`: `det = q` for every odd prime `q`, PROVED (the determinant of `ρ_T` is the
  `2`-adic cyclotomic character, batch 3's `detTateTwoEqCyclotomic` through
  `det_tateMatrix_eq_of_frob`; the Frobenius acts on `μ_{2^∞}` by `ζ ↦ ζ^q`,
  `apply_eq_pow_of_isFrobAt`);
* `trace_frobMat`: `tr = a_q` (Mathlib's coefficient of `L(E, s)`) at every odd prime of good
  reduction, PROVED from the GLUE `FrobeniusTrace E` (lane RC17's named input, printed in Silverman,
  AEC, 2nd ed., Prop. VII.3.1(b) p. 192, Prop. VII.4.1 p. 195, Thm. V.2.3.1 p. 142 and Remark V.2.6
  p. 144: Eichler–Shimura for elliptic curves over finite fields); the tree has no proof of it;
* `TateCoef.rat`: the datum `K = ℚ`, `S` all primes (`K_S = ℚ̄`), `e = id`, available for every
  elliptic `E` (non-vacuity).

Kinds: definitions, PROVED, and the GLUE `FrobeniusTrace` (a hypothesis, never assumed).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar TateMod tateRep)
open ZInQ.Manuscript.RC.LambdaCoef (TateS HasFullTwoTorsion hasFullTwoTorsion_univ)
open ZInQ.Contrib.RC53Assist.InnerLimitArith (rhoK rhoKMatrix basisK tateSEquiv gksOfQ
  gksOfQ_smul_eq_rhoK det_rhoKMatrix)
open ZInQ.Manuscript.RC.TateWiring (tateMatrix FrobeniusTrace trace_tateMatrix)
open scoped WeierstrassCurve

/-! ## An arithmetic Frobenius element at `q` -/

/-- **An arithmetic Frobenius element `Fr_q ∈ G_ℚ` at `q`** (definition, a choice; tex
4209–4213, 9936–9942): at a prime `q`, an element with `σ x ≡ x^q` modulo a maximal ideal of `ℤ̄`
over `q` (lane RC24's `AddressGenuine.IsFrobAt`, Mathlib's `IsArithFrobAt`). -/
def frobQ (q : ℕ) : GalQ :=
  Classical.epsilon fun σ : GalQ => AddressGenuine.IsFrobAt σ q

/-- `frobQ q` is an arithmetic Frobenius element at the prime `q` (PROVED from lane RC24's
`frobeniusExists`). -/
theorem isFrobAt_frobQ {q : ℕ} (hq : q.Prime) : AddressGenuine.IsFrobAt (frobQ q) q :=
  Classical.epsilon_spec (AddressGenuine.frobeniusExists q hq)

/-- `frobQ q` is a Frobenius element at `q` in the form of the Chebotarev files and of the GLUE
`FrobeniusTrace` (PROVED). -/
theorem isFrobAtC10_frobQ {q : ℕ} (hq : q.Prime) :
    ZInQ.Contrib.ChebFD.C10.IsFrobAt (frobQ q) q := by
  obtain ⟨Q, hQ, hqQ, hF⟩ := (isFrobAt_frobQ hq).exists_congr hq
  refine ⟨Q, hQ.isPrime, AddressGenuine.under_eq_span_of_isMaximal hQ hq hqQ, fun x y hy => ?_⟩
  have hyx : y = frobQ q • x - x ^ q := by
    apply Subtype.ext
    rw [hy]
    push_cast
    rw [AddressGenuine.coe_smul_Zbar]
  rw [hyx]
  exact hF x

/-! ## The coefficient datum and the Frobenius matrix -/

/-- **The coefficient datum of `𝕋 = T₂E ⊗ Λ(α)`** (definition; tex 2747–2781): a number field `K`,
a set `S` of its primes, an identification `K̄ ≃ ℚ̄` over `ℚ`, and `E[2^∞] ⊆ E(K_S)` (lane RC28's
`HasFullTwoTorsion`; for the text's `K` and `S` it is the GLUE input Néron–Ogg–Shafarevich,
Silverman AEC VII.7.1), so that lane RC28's `tateBasis` is a `ℤ₂`-basis of `T₂E` over `K_S`. -/
structure TateCoef (E : WeierstrassCurve ℚ) : Type 1 where
  /-- the number field `K` -/
  K : Type
  [field : Field K]
  [numberField : NumberField K]
  /-- the set `S` of primes of `K` -/
  S : Set (HeightOneSpectrum (𝓞 K))
  /-- an identification `K̄ ≃ ℚ̄` over `ℚ` -/
  e : AlgebraicClosure K ≃ₐ[ℚ] Qbar
  [full : HasFullTwoTorsion K S (E⁄K)]

attribute [instance] TateCoef.field TateCoef.numberField TateCoef.full

variable {E : WeierstrassCurve ℚ} [E.IsElliptic]

/-- **The matrix of `ρ_T(Fr_q)` on `T₂E` in lane RC28's basis `tateBasis` over `K_S`**
(definition; tex 2836–2838, 4209–4213): the transported action `rhoKMatrix` of `frobQ q`. -/
def frobMat (C : TateCoef E) (q : ℕ) : Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  rhoKMatrix C.S E C.e (frobQ q)

/-- The trace of the transported matrix is the trace of `ρ_T` (PROVED). -/
theorem trace_rhoKMatrix (C : TateCoef E) (g : GalQ) :
    (rhoKMatrix C.S E C.e g).trace = (tateMatrix E g).trace := by
  rw [rhoKMatrix, ← LinearMap.trace_eq_matrix_trace, trace_tateMatrix, rhoK]
  have h := LinearMap.trace_conj' (tateRep E 2 g) (tateSEquiv C.S E C.e).symm
  rw [LinearEquiv.conj_apply, LinearEquiv.symm_symm] at h
  exact h

/-- **`det ρ_T(Fr_q) = q`** at every odd prime `q` (tex 4213; "the determinant is the cyclotomic
character by the Weil pairing", tex 3091–3096). PROVED: batch 3's `detTateTwoEqCyclotomic` (through
lane RC22's `det_tateMatrix_eq_of_frob`) and the action of the Frobenius on `μ_{2^∞}`
(`apply_eq_pow_of_isFrobAt`). -/
theorem det_frobMat (C : TateCoef E) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    (frobMat C q).det = (q : ℤ_[2]) := by
  rw [frobMat, det_rhoKMatrix]
  exact GlueSweep.Tate.det_tateMatrix_eq_of_frob E (frobQ q) fun _ ζ hζ =>
    GlueSweep.Tate.apply_eq_pow_of_isFrobAt hq2 (isFrobAtC10_frobQ hq) ζ hζ

/-- **`tr ρ_T(Fr_q) = a_q`** at every odd prime of good reduction (tex 4213; `a_q` Mathlib's
coefficient of `L(E, s)`). PROVED from the GLUE `FrobeniusTrace E` (Eichler–Shimura over `𝔽_q`:
Silverman AEC, 2nd ed., Prop. VII.3.1(b) p. 192, Prop. VII.4.1 p. 195, Thm. V.2.3.1 p. 142,
Remark V.2.6 p. 144). -/
theorem trace_frobMat (C : TateCoef E) (hT : FrobeniusTrace E) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hgood : Nonvanishing.GoodAt E q) :
    (frobMat C q).trace = ((E.LFunction q : ℤ) : ℤ_[2]) := by
  rw [frobMat, trace_rhoKMatrix, trace_tateMatrix]
  exact hT q hq hq2 hgood (frobQ q) (isFrobAtC10_frobQ hq)

/-- **The native Galois action** (tex 2836–2838): when `Fr_q` fixes (the image of) `K`, as at the
text's split primes, `frobMat C q` is the matrix of the native action of the Frobenius
`e⁻¹ Fr_q e ∈ G_{K,S}` (`gksOfQ`) on lane RC28's `T₂E` over `K_S`, in `tateBasis`. PROVED
(`gksOfQ_smul_eq_rhoK`). -/
theorem frobMat_eq_native (C : TateCoef E) (q : ℕ)
    (hfix : ∀ x : C.K, frobQ q (C.e (algebraMap C.K (AlgebraicClosure C.K) x)) =
      C.e (algebraMap C.K (AlgebraicClosure C.K) x)) :
    frobMat C q = LinearMap.toMatrix (basisK C.S E) (basisK C.S E)
      (DistribSMul.toLinearMap ℤ_[2] (TateS C.K C.S (E⁄C.K))
        (gksOfQ C.S C.e (frobQ q) hfix)) := by
  rw [frobMat, rhoKMatrix]
  congr 1
  refine LinearMap.ext fun P => ?_
  exact (gksOfQ_smul_eq_rhoK C.S C.e E (frobQ q) hfix P).symm

variable (E) in
/-- **The coefficient datum `K = ℚ`, `S` = all primes** (`K_S = ℚ̄`), `e = id` (definition;
non-vacuity): `E[2^∞] ⊆ E(ℚ̄)` is lane RC28's `hasFullTwoTorsion_univ`. -/
def TateCoef.rat : TateCoef E where
  K := ℚ
  S := Set.univ
  e := AlgEquiv.refl
  full := hasFullTwoTorsion_univ

end ZInQ.Manuscript.RC.Wiring
