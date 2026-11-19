import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate8Decomposition
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate8Valuation

/-!
# Theorem 5.3, Lane RC32 round 5: `FrobeniusTrace` rests on (R) and (D) only

The round-four input `DecompositionFrobeniusQ r hr` (a global Frobenius element at `r` extends
along an embedding `ℚ̄ → ℚ̄_r` to a local arithmetic Frobenius) is PROVED for every prime `r`:

* `invariantResidueValuation`: the spectral valuation of `ℚ̄_r` over `ℚ_r`
  (`CommonCoordinate8Valuation.lean`) is a `Gal(ℚ̄_r/ℚ_r)`-invariant extension of `v_r` whose
  residues are reached from `ℤ̄` along every embedding;
* `localGaloisDecomposition_proof`: with the lift of the decomposition group
  (`CommonCoordinate8Decomposition.lean`: Neukirch ANT II.9.6, proved through the density of `ℚ` in
  `ℚ_r`, the valuation ring `ℤ̄_P` and the infinite Galois correspondence);
* `decompositionFrobeniusQ_proof`, `localGlobalFrobenius_proof`;
* **`frobeniusTrace_of_RD_only (hR : TateReductionComparison) (hD : DetEqDegree) E :
  FrobeniusTrace E`** for every elliptic `E/ℚ`.

The leaf with the actual Frobenius then needs only the RC53 group's (R) and (D):
`CommonCoordinateInputsRD` (`CommonCoordinateInputsLF` with `FrobeniusTrace (E_ℓ)` replaced by
`TateReductionComparison ∧ DetEqDegree`), with `commonCoordinateInputsLF_of_RD`,
`commonCoordinateTarget_of_RD`, `baseZeroTarget_of_RD`, the exact content
`commonCoordinateInputsRD_iff_exact` and, for a support containing `S₀`,
`commonCoordinateInputsRD_iff_of_support`; not implied by (4.7)
(`commonCoordinateInputsRD_not_of_target`); non-vacuity given (R) and (D)
(`commonCoordinateInputsRD_goodData`); and the non-vacuity of the proved input:
`exists_frobenius_with_local_lift` (a global Frobenius at every prime, with its local lift).

Kinds: definitions and PROVED; (R) and (D) are the RC53 group's named inputs (hypotheses).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)
open ZInQ.Contrib.RC53Assist.NewformPeriodsDictionary (primeIdealQ IsArithmeticFrobeniusOnClosureQ)
open ZInQ.Contrib.CloudB3RC53.ModularWeil (TateReductionComparison DetEqDegree)
open scoped WithZero

/-! ## The proved local-global input -/

/-- **An invariant valuation of `ℚ̄_r` extending `v_r`, with residues from `ℤ̄`** (PROVED: the
spectral valuation). -/
theorem invariantResidueValuation (r : ℕ) (hr : r.Prime) : InvariantResidueValuation r hr :=
  exists_invariant_extension r hr

/-- **The local Galois decomposition at every prime** (PROVED). -/
theorem localGaloisDecomposition_proof (r : ℕ) (hr : r.Prime) : LocalGaloisDecomposition r hr :=
  localGaloisDecomposition_of_valuation (invariantResidueValuation r hr)

/-- **Every global Frobenius element at `r` extends to a local arithmetic Frobenius** (PROVED; the
round-four input `DecompositionFrobeniusQ`). -/
theorem decompositionFrobeniusQ_proof (r : ℕ) (hr : r.Prime) : DecompositionFrobeniusQ r hr :=
  decompositionFrobeniusQ_of_local (localGaloisDecomposition_proof r hr)

/-- **The local-global comparison for every elliptic `E/ℚ`** (PROVED; the round-four input
`LocalGlobalFrobenius E`). -/
theorem localGlobalFrobenius_proof (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    LocalGlobalFrobenius E :=
  localGlobalFrobenius_of_decomposition E fun r hr _ => decompositionFrobeniusQ_proof r hr

/-- **`FrobeniusTrace` from (R) and (D) alone** (PROVED, for every elliptic `E/ℚ`): the RC53
group's dictionary from `TateReductionComparison` and `DetEqDegree`, and the proved local-global
comparison. -/
theorem frobeniusTrace_of_RD_only (hR : TateReductionComparison) (hD : DetEqDegree)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] : FrobeniusTrace E :=
  frobeniusTrace_of_RD_decomposition hR hD (fun r hr _ => decompositionFrobeniusQ_proof r hr) E

/-- **Non-vacuity of the proved input** (PROVED): at every prime `r` there is a global Frobenius
element (`frobQ r`), and it has a local lift: an embedding `ι`, a valuation `w` extending `v_r` and
an arithmetic Frobenius `σ` for `w` with `σ ∘ ι = ι ∘ frobQ r`. -/
theorem exists_frobenius_with_local_lift (r : ℕ) (hr : r.Prime) :
    ZInQ.Contrib.ChebFD.C10.IsFrobAt (frobQ r) r ∧
      ∃ (ι : Qbar →ₐ[ℚ] Qrbar r hr) (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ)
        (w : Valuation (Qrbar r hr) Γ),
        (w.comap (algebraMap (Qr r hr) (Qrbar r hr))).IsEquiv
          (Valued.v : Valuation (Qr r hr) ℤᵐ⁰) ∧
        ∃ σ : Qrbar r hr ≃ₐ[Qr r hr] Qrbar r hr,
          IsArithmeticFrobeniusOnClosureQ (primeIdealQ r hr) Γ w σ ∧
            ∀ x : Qbar, σ (ι x) = ι (frobQ r x) :=
  ⟨isFrobAtC10_frobQ hr, decompositionFrobeniusQ_proof r hr _ (isFrobAtC10_frobQ hr)⟩

/-! ## The leaf with the actual Frobenius over (R) and (D) -/

/-- **The inputs of (4.7) with the actual Frobenius, over (R) and (D) only** (tex 4142–4328):
`E_ℓ` elliptic, a coefficient datum `C`, the RC53 group's inputs (R) `TateReductionComparison` and
(D) `DetEqDegree`, and at every address of every final family one `CommonCoordinateTrianglesLF`. -/
def CommonCoordinateInputsRD {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
    TateReductionComparison ∧ DetEqDegree ∧
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      Nonempty (@CommonCoordinateTrianglesLF ℓ hE C D F x)

/-- **The leaf over (R) and (D) gives the leaf with `FrobeniusTrace`** (PROVED). -/
theorem commonCoordinateInputsLF_of_RD {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsRD D) :
    CommonCoordinateInputsLF D := by
  obtain ⟨hE, C, hR, hD, hT⟩ := h
  exact ⟨hE, C, @frobeniusTrace_of_RD_only hR hD (Ecurve ℓ) hE, hT⟩

/-- **(4.7) from the leaf over (R) and (D)** (`RCSteps.common_coordinate`; PROVED). -/
theorem commonCoordinateTarget_of_RD {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsRD D) :
    CommonCoordinateTarget D :=
  commonCoordinateTarget_of_LF (commonCoordinateInputsLF_of_RD h)

/-- **`RCSteps.base_zero` with the leaf over (R) and (D)** (PROVED). -/
theorem baseZeroTarget_of_RD {ℓ : ℕ} {D : RCData ℓ} (P : Prints)
    (hcc : CommonCoordinateInputsRD D) (hpr : PrimRegularityInputs D)
    (h : BaseZeroAssembly.BaseZeroLeafInputs D) : BaseZeroTarget D :=
  baseZeroTarget_of_LF P (commonCoordinateInputsLF_of_RD hcc) hpr h

/-- **The exact content of the leaf over (R) and (D)** (PROVED): (R), (D), `E_ℓ` elliptic, good
graph primes, and the round-one leaf. -/
theorem commonCoordinateInputsRD_iff_exact {ℓ : ℕ} (D : RCData ℓ) :
    CommonCoordinateInputsRD D ↔
      TateReductionComparison ∧ DetEqDegree ∧ (Ecurve ℓ).IsElliptic ∧
      (∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ q ∈ F.Q,
        Nonvanishing.GoodAt (Ecurve ℓ) q) ∧
      CommonCoordinateInputsL D := by
  constructor
  · intro h
    obtain ⟨hE, C, hR, hD, hT⟩ := h
    obtain ⟨-, -, hgood, hL⟩ := (commonCoordinateInputsLF_iff_exact D).mp
      (commonCoordinateInputsLF_of_RD ⟨hE, C, hR, hD, hT⟩)
    exact ⟨hR, hD, hE, hgood, hL⟩
  · rintro ⟨hR, hD, hE, hgood, hL⟩
    obtain ⟨hE', C, -, hT⟩ := (commonCoordinateInputsLF_iff_exact D).mpr
      ⟨hE, @frobeniusTrace_of_RD_only hR hD (Ecurve ℓ) hE, hgood, hL⟩
    exact ⟨hE', C, hR, hD, hT⟩

/-- **The exact content for a support containing `S₀`** (PROVED): for `ℓ > 0`, (R) and (D) together
with the round-one leaf (whose exact content is `commonCoordinateInputsL_iff_exact`). -/
theorem commonCoordinateInputsRD_iff_of_support {ℓ : ℕ} (hℓ : 0 < ℓ) (D : RCData ℓ)
    (hS : S0 ℓ ⊆ D.S) :
    CommonCoordinateInputsRD D ↔
      TateReductionComparison ∧ DetEqDegree ∧ CommonCoordinateInputsL D := by
  rw [commonCoordinateInputsRD_iff_exact]
  constructor
  · rintro ⟨hR, hD, -, -, hL⟩
    exact ⟨hR, hD, hL⟩
  · rintro ⟨hR, hD, hL⟩
    exact ⟨hR, hD, isElliptic_Ecurve hℓ, goodAt_of_support hℓ D hS, hL⟩

/-- **The leaf over (R) and (D) is not implied by (4.7)** (PROVED; through `ε_x = 1` at the empty
family). -/
theorem commonCoordinateInputsRD_not_of_target :
    ∃ D : RCData 1, CommonCoordinateTarget D ∧ ¬ CommonCoordinateInputsRD D := by
  obtain ⟨D, h1, h2⟩ := commonCoordinateInputsLF_not_of_target
  exact ⟨D, h1, fun h => h2 (commonCoordinateInputsLF_of_RD h)⟩

/-- **Non-vacuity, conditional on (R) and (D)** (PROVED): for `ℓ > 0` the leaf over (R) and (D)
holds for `goodData ℓ`, with the actual Frobenius in every relaxation step. -/
theorem commonCoordinateInputsRD_goodData {ℓ : ℕ} (hℓ : 0 < ℓ) (hR : TateReductionComparison)
    (hD : DetEqDegree) : CommonCoordinateInputsRD (goodData ℓ) := by
  have hE := isElliptic_Ecurve hℓ
  obtain ⟨hE', C, -, hT⟩ := commonCoordinateInputsLF_goodData hℓ
    (@frobeniusTrace_of_RD_only hR hD (Ecurve ℓ) hE)
  exact ⟨hE', C, hR, hD, hT⟩

end ZInQ.Manuscript.RC.Wiring
