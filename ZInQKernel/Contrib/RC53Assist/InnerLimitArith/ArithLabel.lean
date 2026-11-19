import ZInQKernel.Contrib.RC53Assist.InnerLimitArith.Conjugation

/-!
# One compatible arithmetic label

The realized derivative stages of the inner limit come from one arithmetic label: an elliptic
curve `E` over `ℚ` with its base change `E_K` to the companion field `K`, an actual complex
conjugation, actual derivative primes `ℓ_i` with arithmetic Frobenius elements `Fr_i` selected by
finite Chebotarev, the stage primes `q_i` of `K` above `ℓ_i`, inert with residue size `ℓ_i²`, the
match of the Frobenius of `q_i` with the square of `Fr_i`, and the character constraint, all at
the same stages. This file bundles these data and derives from them, rather than assuming, the
twisted derivative congruence of the label and the realized derivative matrices with conjugation
`J = ρ_T(τ)` in the coefficient basis.

The remaining inputs in the bundle are `frobMatch` (the local–global Frobenius compatibility at
the decomposition embedding) and `character` (the character constraint in the finite quotient of
the Chebotarev selection); the residue degree and the incidence of the primes are recorded.

Sources: the selection of derivative primes and (5.4), manuscript lines 4809–4830; (H12), lines
3088–3100; the conjugation, lines 2761–2808; the local planes at a derivative prime, lines
5027–5037.
-/

set_option maxHeartbeats 400000
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.InnerLimitArith

open Filter NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules (ActualConj)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.Limits hiding Lambda
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Contrib.RC53Assist.InnerLimit
open scoped WeierstrassCurve PowerSeries.WithPiTopology

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (𝓞 K))) [HasFullTwoTorsion K S (E⁄K)] (α : GKS K S →* Lambdaˣ)

/-- **One compatible arithmetic label** for the curve `E`, its base change to `K`, the set `S`
and the character `α`: the conjugation, the derivative primes and their Frobenius elements, the
stage primes of `K` above them with residue size `ℓ_i²`, and the match of the two Frobenius
families, at the same stages. -/
structure CompatibleArithmeticLabel where
  /-- The identification `K̄ ≃ ℚ̄` realizing `G_K ⊂ G_ℚ`. -/
  e : AlgebraicClosure K ≃ₐ[ℚ] Qbar
  /-- The actual complex conjugation. -/
  C : ActualConj K S
  /-- The kernel representatives at the stages. -/
  h : ℕ → GalQ
  /-- The stage fields of the Chebotarev selection. -/
  F : ℕ → IntermediateField ℚ Qbar
  /-- The previously used primes. -/
  excl : ℕ → Finset ℕ
  /-- The derivative primes, with Frobenius elements realizing `τ h_i` on the stage fields. -/
  primes : DerivativePrimes E (tateConjQ e C) h F excl
  /-- The representatives fix the `2^i`-torsion field of `E`. -/
  hh : ∀ i, ∀ x ∈ ZInQ.Manuscript.RC.GlueSweep.Tate.torsField E i, h i x = x
  /-- The squares of the rational Frobenius elements fix `K`. -/
  hK : ∀ i (x : K), (primes.frob i * primes.frob i) (e (algebraMap K (AlgebraicClosure K) x)) =
    e (algebraMap K (AlgebraicClosure K) x)
  /-- The stage primes of `K`. -/
  label : MovingLabel K S
  /-- The stage prime lies above the rational derivative prime. -/
  above : ∀ i, ((primes.ell i : ℕ) : 𝓞 K) ∈ (label.q i).asIdeal
  /-- The stage prime is inert: its residue field has `ℓ_i²` elements. -/
  inert : ∀ i, Nat.card (𝓞 K ⧸ (label.q i).asIdeal) = primes.ell i ^ 2
  /-- The Frobenius of the stage prime is conjugate to the square of the rational Frobenius. -/
  frobMatch : FrobeniusMatchesLabel E e C primes hK label
  /-- The character constraint at the stages. -/
  character : ∀ i, ((α (ratSqFrob E e C primes hK i) : Lambdaˣ) : Lambda) - 1 ∈ lamIdeal i

namespace CompatibleArithmeticLabel

variable {E K S α} (X : CompatibleArithmeticLabel E K S α)

/-- **The twisted derivative congruence of the label, derived**: the Frobenius of the stage prime
acts trivially on `𝕋 / I_i 𝕋` at every stage. -/
theorem htriv (i : ℕ) (x : TLam K S (E⁄K) α) :
    X.label.frob i • x - x ∈ tlamNbhd K S (E⁄K) α i :=
  htriv_of_match E X.e X.C X.primes X.hK X.hh X.character X.label X.frobMatch i x

/-- **The realized derivative matrices of the label**, in the coefficient basis. -/
def derivative (U : Ultrafilter ℕ) : DerivativeMatrices (R := Lambda) stageIdeal U :=
  realizedDerivativeK_of_match E X.e X.C X.primes X.hK X.hh X.character X.label X.frobMatch U

/-- The residue characteristics of the label are its actual derivative primes. -/
theorem derivative_ell (U : Ultrafilter ℕ) (i : ℕ) :
    (X.derivative U).ell i = ((X.primes.ell i : ℕ) : Lambda) ∧ (X.primes.ell i).Prime ∧
      X.primes.ell i ≠ 2 ∧ X.primes.ell i ∉ X.excl i :=
  ⟨rfl, X.primes.prime i, X.primes.odd i, X.primes.avoid i⟩

omit [HasFullTwoTorsion K S (E⁄K)] in
/-- The stage primes lie above the derivative primes with residue size `ℓ_i²`. -/
theorem residue_size (i : ℕ) :
    ((X.primes.ell i : ℕ) : 𝓞 K) ∈ (X.label.q i).asIdeal ∧
      Nat.card (𝓞 K ⧸ (X.label.q i).asIdeal) = X.primes.ell i ^ 2 :=
  ⟨X.above i, X.inert i⟩

/-- The conjugation of the realized stages is `ρ_T(τ)` in the coefficient basis. -/
theorem derivative_J (U : Ultrafilter ℕ) :
    (X.derivative U).J = (conjMatrixK E X.C).map (algebraMap ℤ_[2] Lambda) :=
  rfl

/-- **Read at a fibre, the conjugation of the label is the fibre duality's `conjMatrix`.** -/
theorem derivative_J_fibre (U : Ultrafilter ℕ) (P : Ideal Lambda) [P.IsPrime] :
    (X.derivative U).J.map (algebraMap Lambda (ResAt P)) =
      ZInQ.Manuscript.RC.FibreDuality.conjMatrix X.C (E⁄K) (tate_baseChange_map_kappa E X.C) P :=
  realizedDerivativeK_J_fibre E X.e X.C X.label X.primes X.hh (X.htriv) U
    (tate_baseChange_map_kappa E X.C) P

/-- **The inner limits of the label**: `ℓ → −1`, `q → 1`, `Φ → 1`, the rational Frobenius
matrices tend to `ρ_T(τ)` in the coefficient basis, and `det J = −1`. -/
theorem derivative_limits (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ cofinite) :
    ulim U (X.derivative U).ell = -1 ∧
      ulim U (fun i => (X.derivative U).ell i ^ 2) = 1 ∧
      ulimMat U (X.derivative U).phi = 1 ∧
      ulimMat U (X.derivative U).rationalFrob =
        (conjMatrixK E X.C).map (algebraMap ℤ_[2] Lambda) ∧
      (X.derivative U).J.det = -1 :=
  realizedDerivativeK_limits E X.e X.C X.label X.primes X.hh (X.htriv) U hU

end CompatibleArithmeticLabel

end ZInQ.Contrib.RC53Assist.InnerLimitArith
