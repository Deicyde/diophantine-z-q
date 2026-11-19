import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate6Frobenius
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate5Wiring

/-!
# Theorem 5.3, Lane RC32 round 2: the common-coordinate leaf with the actual Frobenius

Lemma `ex:arith-common-coordinate` (tex 4142–4328) over the text's objects, as in round one
(`CommonCoordinate5.lean`), with the Frobenius matrix pinned: the matrix in each relaxation step is
`frobMat C p`, the matrix of `ρ_T(Fr_p)` on `T₂E` in lane RC28's basis over `K_S`
(`CommonCoordinate6Frobenius.lean`), no longer a free matrix with the right trace and determinant.

Each field or datum: text; tex lines; kind.

* `(Ecurve ℓ).IsElliptic`: `E_ℓ` is an elliptic curve; tex 1779–1784; definition (PROVED for
  `ℓ ≠ 0`).
* `C : TateCoef (Ecurve ℓ)`: `K`, `S`, `K̄ ≃ ℚ̄`, `E[2^∞] ⊆ E(K_S)`; tex 2747–2781; definition +
  GLUE (NOS, AEC VII.7.1).
* `FrobeniusTrace (Ecurve ℓ)`: `tr ρ_T(Fr_q) = a_q` at good odd `q`; tex 4213; GLUE
  (Eichler–Shimura; AEC V.2.3.1, VII.3.1(b), VII.4.1).
* `hgood`: the graph primes are good; tex 4143, 2678–2680; definition (from the support).
* `u`: relaxed coordinates; tex 3877–3892, 4159–4188; existential (any coordinates; not tied to
  the actual complexes).
* `hprim`: `u_{prim,x}` regular; tex 4153; definition + ELLIOT.
* `eps`, `hstep`: (4.7) at each step as an existential triangular model (met by
  `naturalStep_relaxedCoord` for any coordinates with `δ u' = c e² u`), with `frobMat` in its
  two-place block; tex 4157–4194, 4325–4327; ELLIOT; DEPARTURE (one prime at a time).
* `htilde`: `η_x u_{rel,x}` regular, expansion `ũ_x`; tex 4150–4151, 4224–4231; definition.

PROVED: `det(frobMat C q) = q` at every odd prime (no hypothesis), `tr(frobMat C q) = a_q` from the
GLUE at good primes; hence the round-one leaf (`commonCoordinateInputsL_of_LF`, with
`Fr := frobMat C`), (4.7) (`commonCoordinateTarget_of_LF`) and the base-zero step
(`baseZeroTarget_of_LF`).

DEPARTURE (form): the coefficient datum `C` is existential (one datum for all families); the text
fixes `K = ℚ(√k)` and its `S`. Only `tr` and `det` of the Frobenius enter (4.7), and they do not
depend on `C` (`det_frobMat`, `trace_frobMat`). Other departures as in round one (scope of `hprim`,
Branch 1, one prime at a time).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open Matrix ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central
  ZInQ.Manuscript.RC.Uniform ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CommonCoordinate
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)

/-- **The data of Lemma `ex:arith-common-coordinate` at one address, with the actual Frobenius**
(tex 4142–4328): as `CommonCoordinateTrianglesL`, with the Frobenius matrix `frobMat C p` of
`ρ_T(Fr_p)` in lane RC28's basis in place of a free matrix. -/
structure CommonCoordinateTrianglesLF {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ))
    (D : RCData ℓ) (Fam : Family) (x : Addr Fam.b) : Type where
  /-- the graph primes are primes of good reduction of `E_ℓ` (definition: they lie outside the
  support, which contains the primes of `6ℓ`; tex 4143 "unused good split prime", 2678–2680) -/
  hgood : ∀ q ∈ Fam.Q, Nonvanishing.GoodAt (Ecurve ℓ) q
  /-- the class-functional coordinates in `F` relaxed at `T ⊆ U` (existential: any coordinates;
  the text's are those of `[z] ⊗ [λ]`; tex 3877–3892, 4159–4188) -/
  u : Finset ℕ → FracLam
  /-- the primitive coordinate `u ∅` is regular at `t = 0` with `t`-expansion `u_{prim,x}`
  (definition + ELLIOT regularity; DEPARTURE of scope as `RCData.uPrim`; tex 4153, 4334–4336) -/
  hprim : IsTExpansion (u ∅) (D.uPrim Fam x)
  /-- the step units `ε` of (4.7) (existential; tex 4187–4193) -/
  eps : Finset ℕ → ℕ → FracLam
  /-- each relaxation `T → T ∪ {p}` at an unused prime is (4.7) at the step as an existential
  triangular model over `F` (batch 3's `NaturalStep`, met by `naturalStep_relaxedCoord`), with
  the actual Frobenius `frobMat C p` in its two-place block (ELLIOT; DEPARTURE: one prime at a
  time; tex 4157–4194, 4325–4327) -/
  hstep : ∀ T ⊆ unusedAt Fam x, ∀ p ∈ unusedAt Fam x, p ∉ T →
    NaturalStep ((frobMat C p).map zTwoToF) (p : FracLam) (p : FracLam)⁻¹ (apE ℓ p : FracLam)
      (lamToF (zAt Fam x p : Lambda)) (lamToF ((zAt Fam x p)⁻¹ : Lambdaˣ)) (u T) (u (insert p T))
      (eps T p) LamUnitF LamUnitF
  /-- the corrected coordinate `η_x u_{rel,x}` is regular with `t`-expansion `ũ_x` (definition;
  tex 4150–4151, 4224–4231) -/
  htilde : IsTExpansion (etaF ℓ Fam x * u (unusedAt Fam x)) (D.uTilde Fam x)

/-- **The inputs of (4.7) with the actual Frobenius** (tex 4142–4328): `E_ℓ` is elliptic, a
coefficient datum `C` (one for all families), the GLUE `FrobeniusTrace (E_ℓ)`, and at every address
of every final family one `CommonCoordinateTrianglesLF`. -/
def CommonCoordinateInputsLF {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)), FrobeniusTrace (Ecurve ℓ) ∧
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      Nonempty (@CommonCoordinateTrianglesLF ℓ hE C D F x)

/-! ## The actual Frobenius has the round-one leaf's trace and determinant -/

/-- **The actual Frobenius at the graph primes**: `tr = a_q` (from the GLUE) and `det = q`
(PROVED) for odd primes of good reduction. -/
theorem trace_det_frobMat {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] (C : TateCoef (Ecurve ℓ))
    (hT : FrobeniusTrace (Ecurve ℓ)) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hgood : Nonvanishing.GoodAt (Ecurve ℓ) q) :
    (frobMat C q).trace = (apE ℓ q : ℤ_[2]) ∧ (frobMat C q).det = (q : ℤ_[2]) :=
  ⟨trace_frobMat C hT hq hq2 hgood, det_frobMat C hq hq2⟩

/-- **The round-one leaf from the leaf with the actual Frobenius** (PROVED): `Fr := frobMat C`,
with `tr Fr_q = a_q` and `det Fr_q = q` at the graph primes. -/
def CommonCoordinateTrianglesLF.toL {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {C : TateCoef (Ecurve ℓ)}
    {D : RCData ℓ} {Fam : Family} {x : Addr Fam.b} (M : CommonCoordinateTrianglesLF C D Fam x)
    (hT : FrobeniusTrace (Ecurve ℓ)) (hQ : ∀ q ∈ Fam.Q, q.Prime ∧ q ≠ 2) :
    CommonCoordinateTrianglesL D Fam x where
  Fr := frobMat C
  hFtr q hq := (trace_det_frobMat C hT (hQ q hq).1 (hQ q hq).2 (M.hgood q hq)).1
  hFdet q hq := det_frobMat C (hQ q hq).1 (hQ q hq).2
  u := M.u
  hprim := M.hprim
  eps := M.eps
  hstep := M.hstep
  htilde := M.htilde

/-- **The comparison `LF ⇒ L`** (PROVED). -/
theorem commonCoordinateInputsL_of_LF {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsLF D) :
    CommonCoordinateInputsL D := by
  obtain ⟨hE, C, hT, h⟩ := h
  intro Co Ce F hF x
  obtain ⟨M⟩ := h Co Ce F hF x
  exact ⟨M.toL hT fun q hq => ⟨(hF.1 q hq).1, (hF.1 q hq).2.1⟩⟩

/-- **(4.7) from the leaf with the actual Frobenius** (`RCSteps.common_coordinate`; PROVED). -/
theorem commonCoordinateTarget_of_LF {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsLF D) :
    CommonCoordinateTarget D :=
  commonCoordinateTarget_of_L (commonCoordinateInputsL_of_LF h)

/-- **`RCSteps.base_zero` with the leaf with the actual Frobenius** (tex 4330–4376; PROVED, as
`baseZeroTarget_of_L`). -/
theorem baseZeroTarget_of_LF {ℓ : ℕ} {D : RCData ℓ} (P : Prints) (hcc : CommonCoordinateInputsLF D)
    (hpr : PrimRegularityInputs D) (h : BaseZeroAssembly.BaseZeroLeafInputs D) :
    BaseZeroTarget D :=
  baseZeroTarget_of_L P (commonCoordinateInputsL_of_LF hcc) hpr h

end ZInQ.Manuscript.RC.Wiring
