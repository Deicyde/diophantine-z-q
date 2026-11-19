import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate7LocalGlobal
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate6Exact

/-!
# Theorem 5.3, Lane RC32 round 4: the leaf with the narrowed Frobenius GLUE

`CommonCoordinateInputsLRD` is `CommonCoordinateInputsLF` (`CommonCoordinate6.lean`) with the GLUE
conjunct `FrobeniusTrace (E_ℓ)` replaced by its three narrower inputs:

Each conjunct: statement; kind.

* `TateReductionComparison`: (R), at good reduction an arithmetic Frobenius of `ℚ_p` acts on
  `T_ℓ(E/ℚ̄_p)` as the `p`-power Frobenius on `T_ℓ` of the reduction; GLUE (RC53 group; Silverman
  AEC VII.3.1, VII.7.1).
* `DetEqDegree`: (D), `det` on `T_ℓ` of an endomorphism of a curve over `𝔽̄_p` is its degree; GLUE
  (RC53 group; Silverman AEC III.8.6).
* `DecompositionFrobeniusQ`: a global Frobenius at `r` extends to a local arithmetic Frobenius
  along an embedding `ℚ̄ → ℚ̄_r`; GLUE (Neukirch ANT II.8–9), about Galois groups only.

The rest of the leaf is unchanged (the triangles `CommonCoordinateTrianglesLF` with the actual
Frobenius matrix). PROVED:
* `commonCoordinateInputsLF_of_LRD`, through `frobeniusTrace_of_RD_decomposition` (the RC53
  group's dictionary from (R) and (D), the Tate-module comparison along `ι`, the good-reduction and
  coefficient bridges); hence `commonCoordinateTarget_of_LRD` ((4.7)) and `baseZeroTarget_of_LRD`;
* the conjuncts are exactly separated (`commonCoordinateInputsLRD_iff`);
* the exact content: `commonCoordinateInputsLRD_iff_exact`, and for `ℓ > 0` and a support
  containing `S₀` `commonCoordinateInputsLRD_iff_of_support` (the three inputs together with the
  round-one leaf, whose exact content is `commonCoordinateInputsL_iff_exact`);
* not implied by (4.7) alone (`commonCoordinateInputsLRD_not_of_target`);
* non-vacuity conditional on the three inputs (`commonCoordinateInputsLRD_goodData`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)
open ZInQ.Contrib.CloudB3RC53.ModularWeil (TateReductionComparison DetEqDegree)

/-- **The inputs of (4.7) with the actual Frobenius and the narrowed GLUE** (tex 4142–4328):
`E_ℓ` elliptic, a coefficient datum `C`, the GLUE inputs (R) `TateReductionComparison`, (D)
`DetEqDegree` and `DecompositionFrobeniusQ` at the odd primes, and at every address of every final
family one `CommonCoordinateTrianglesLF`. -/
def CommonCoordinateInputsLRD {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
    TateReductionComparison ∧ DetEqDegree ∧
    (∀ (r : ℕ) (hr : r.Prime), r ≠ 2 → DecompositionFrobeniusQ r hr) ∧
    ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
      Nonempty (@CommonCoordinateTrianglesLF ℓ hE C D F x)

/-- **The narrowed leaf gives the leaf with `FrobeniusTrace`** (PROVED). -/
theorem commonCoordinateInputsLF_of_LRD {ℓ : ℕ} {D : RCData ℓ}
    (h : CommonCoordinateInputsLRD D) : CommonCoordinateInputsLF D := by
  obtain ⟨hE, C, hR, hD, hDec, hT⟩ := h
  exact ⟨hE, C, @frobeniusTrace_of_RD_decomposition hR hD hDec (Ecurve ℓ) hE, hT⟩

/-- **(4.7) from the narrowed leaf** (`RCSteps.common_coordinate`; PROVED). -/
theorem commonCoordinateTarget_of_LRD {ℓ : ℕ} {D : RCData ℓ} (h : CommonCoordinateInputsLRD D) :
    CommonCoordinateTarget D :=
  commonCoordinateTarget_of_LF (commonCoordinateInputsLF_of_LRD h)

/-- **`RCSteps.base_zero` with the narrowed leaf** (PROVED, as `baseZeroTarget_of_LF`). -/
theorem baseZeroTarget_of_LRD {ℓ : ℕ} {D : RCData ℓ} (P : Prints)
    (hcc : CommonCoordinateInputsLRD D) (hpr : PrimRegularityInputs D)
    (h : BaseZeroAssembly.BaseZeroLeafInputs D) : BaseZeroTarget D :=
  baseZeroTarget_of_LF P (commonCoordinateInputsLF_of_LRD hcc) hpr h

/-- **The conjuncts are separated** (PROVED): the narrowed leaf is the three GLUE inputs together
with the triangles of the leaf with the actual Frobenius. -/
theorem commonCoordinateInputsLRD_iff {ℓ : ℕ} (D : RCData ℓ) :
    CommonCoordinateInputsLRD D ↔
      TateReductionComparison ∧ DetEqDegree ∧
      (∀ (r : ℕ) (hr : r.Prime), r ≠ 2 → DecompositionFrobeniusQ r hr) ∧
      ∃ (hE : (Ecurve ℓ).IsElliptic) (C : TateCoef (Ecurve ℓ)),
        ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ x : Addr F.b,
          Nonempty (@CommonCoordinateTrianglesLF ℓ hE C D F x) := by
  constructor
  · rintro ⟨hE, C, hR, hD, hDec, hT⟩
    exact ⟨hR, hD, hDec, hE, C, hT⟩
  · rintro ⟨hR, hD, hDec, hE, C, hT⟩
    exact ⟨hE, C, hR, hD, hDec, hT⟩

/-- **Non-vacuity, conditional on the three GLUE inputs** (PROVED): for `ℓ > 0` the narrowed leaf
holds for `goodData ℓ` (support the primes of `6ℓ`, `u_prim = ũ = 1`), with the actual Frobenius
in every relaxation step. -/
theorem commonCoordinateInputsLRD_goodData {ℓ : ℕ} (hℓ : 0 < ℓ) (hR : TateReductionComparison)
    (hD : DetEqDegree) (hDec : ∀ (r : ℕ) (hr : r.Prime), r ≠ 2 → DecompositionFrobeniusQ r hr) :
    CommonCoordinateInputsLRD (goodData ℓ) := by
  have hE := isElliptic_Ecurve hℓ
  obtain ⟨hE', C, -, hT⟩ := commonCoordinateInputsLF_goodData hℓ
    (@frobeniusTrace_of_RD_decomposition hR hD hDec (Ecurve ℓ) hE)
  exact ⟨hE', C, hR, hD, hDec, hT⟩

/-- **The exact content of the narrowed leaf** (PROVED): the three GLUE inputs, `E_ℓ` elliptic,
good graph primes, and the round-one leaf. -/
theorem commonCoordinateInputsLRD_iff_exact {ℓ : ℕ} (D : RCData ℓ) :
    CommonCoordinateInputsLRD D ↔
      TateReductionComparison ∧ DetEqDegree ∧
      (∀ (r : ℕ) (hr : r.Prime), r ≠ 2 → DecompositionFrobeniusQ r hr) ∧
      (Ecurve ℓ).IsElliptic ∧
      (∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ q ∈ F.Q,
        Nonvanishing.GoodAt (Ecurve ℓ) q) ∧
      CommonCoordinateInputsL D := by
  constructor
  · intro h
    obtain ⟨hE, C, hR, hD, hDec, hT⟩ := h
    obtain ⟨-, -, hgood, hL⟩ := (commonCoordinateInputsLF_iff_exact D).mp
      (commonCoordinateInputsLF_of_LRD ⟨hE, C, hR, hD, hDec, hT⟩)
    exact ⟨hR, hD, hDec, hE, hgood, hL⟩
  · rintro ⟨hR, hD, hDec, hE, hgood, hL⟩
    obtain ⟨hE', C, -, hT⟩ := (commonCoordinateInputsLF_iff_exact D).mpr
      ⟨hE, @frobeniusTrace_of_RD_decomposition hR hD hDec (Ecurve ℓ) hE, hgood, hL⟩
    exact ⟨hE', C, hR, hD, hDec, hT⟩

/-- **The exact content for a support containing `S₀`** (PROVED): for `ℓ > 0`, the narrowed leaf
is the three GLUE inputs together with the round-one leaf (whose own exact content is
`commonCoordinateInputsL_iff_exact`). -/
theorem commonCoordinateInputsLRD_iff_of_support {ℓ : ℕ} (hℓ : 0 < ℓ) (D : RCData ℓ)
    (hS : S0 ℓ ⊆ D.S) :
    CommonCoordinateInputsLRD D ↔
      TateReductionComparison ∧ DetEqDegree ∧
      (∀ (r : ℕ) (hr : r.Prime), r ≠ 2 → DecompositionFrobeniusQ r hr) ∧
      CommonCoordinateInputsL D := by
  rw [commonCoordinateInputsLRD_iff_exact]
  constructor
  · rintro ⟨hR, hD, hDec, -, -, hL⟩
    exact ⟨hR, hD, hDec, hL⟩
  · rintro ⟨hR, hD, hDec, hL⟩
    exact ⟨hR, hD, hDec, isElliptic_Ecurve hℓ, goodAt_of_support hℓ D hS, hL⟩

/-- **The narrowed leaf is not implied by (4.7)** (PROVED; as for the leaf with `FrobeniusTrace`,
through `ε_x = 1` at the empty family). -/
theorem commonCoordinateInputsLRD_not_of_target :
    ∃ D : RCData 1, CommonCoordinateTarget D ∧ ¬ CommonCoordinateInputsLRD D := by
  obtain ⟨D, h1, h2⟩ := commonCoordinateInputsLF_not_of_target
  exact ⟨D, h1, fun h => h2 (commonCoordinateInputsLF_of_LRD h)⟩

end ZInQ.Manuscript.RC.Wiring
