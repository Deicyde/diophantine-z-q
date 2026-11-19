import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate6NonVacuity
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate5Bridge

/-!
# Theorem 5.3, Lane RC32 round 2: the leaf with the actual Frobenius against its target

* `commonCoordinateInputsLF_not_of_target`: the leaf is not implied by (4.7) (round one's
  counterexample: `u_prim ≡ 1`, `ũ ≡ −1`, the empty family; the leaf implies the round-one leaf);
* `commonCoordinateInputsLF_iff`: for `ℓ > 0`, given the GLUE `FrobeniusTrace (E_ℓ)`, good graph
  primes (for a support containing `S₀`, PROVED, `PreDataSpec.support_base`) and primitive
  coordinates from `F`, the leaf holds exactly when (4.7) holds with `ε_x = 1` where no graph
  prime is unused. So the leaf is equivalent to the GLUE `FrobeniusTrace (E_ℓ)` together with
  (4.7), `ε_x = 1` where no graph prime is unused, and `u_{prim,x} ∈ F` (the GLUE is a conjunct of
  the leaf, not a hypothesis; the pinned Frobenius adds nothing else): pinning the Frobenius
  matrix does not constrain the existential step models.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53
open ZInQ.Manuscript.RC.TateWiring (FrobeniusTrace)

/-- **The leaf with the actual Frobenius is not implied by the target** (PROVED). -/
theorem commonCoordinateInputsLF_not_of_target :
    ∃ D : RCData 1, CommonCoordinateTarget D ∧ ¬ CommonCoordinateInputsLF D := by
  obtain ⟨D, h1, h2⟩ := commonCoordinateInputsL_not_of_target
  exact ⟨D, h1, fun h => h2 (commonCoordinateInputsL_of_LF h)⟩

/-- **The leaf with the actual Frobenius against the target** (PROVED): for `ℓ > 0`, under the
GLUE `FrobeniusTrace (E_ℓ)`, with good graph primes in the final families and primitive
coordinates that are `t`-expansions of elements of `F`, `CommonCoordinateInputsLF D` holds exactly
when (4.7) holds at every address of every final family with `ε_x = 1` where no graph prime is
unused. -/
theorem commonCoordinateInputsLF_iff {ℓ : ℕ} (D : RCData ℓ) (hℓ : 0 < ℓ)
    (hT : FrobeniusTrace (Ecurve ℓ))
    (hgood : ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F → ∀ q ∈ F.Q,
      Nonvanishing.GoodAt (Ecurve ℓ) q)
    (hfrac : ∀ F : Family, ∀ x : Addr F.b, ∃ u : FracLam, IsTExpansion u (D.uPrim F x)) :
    CommonCoordinateInputsLF D ↔ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
      ∀ x : Addr F.b, ∃ ε : PowerSeries ℚ_[2], LamUnit ε ∧ D.uTilde F x = ε * D.uPrim F x ∧
        (unusedAt F x = ∅ → D.uTilde F x = D.uPrim F x) := by
  constructor
  · intro h
    exact (commonCoordinateInputsL_iff D hfrac).mp (commonCoordinateInputsL_of_LF h)
  · intro h
    have hE := isElliptic_Ecurve hℓ
    refine ⟨hE, TateCoef.rat (Ecurve ℓ), hT, fun Co Ce F hF x => ?_⟩
    obtain ⟨ε, ⟨e, rfl⟩, h47, hone⟩ := h Co Ce F hF x
    obtain ⟨u, hu⟩ := hfrac F x
    exact ⟨trianglesLF_of_eq _ hT D F x (fun q hq => ⟨(hF.1 q hq).1, (hF.1 q hq).2.1⟩)
      (hgood Co Ce F hF) u hu e h47 hone⟩

end ZInQ.Manuscript.RC.Wiring
