import ZInQKernel.Contrib.G15.Transport
import ZInQKernel.Contrib.G15.LadicBridge
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.LocalGlobal.RamificationGroup

/-!
# G15: the three readings of the lower filtration agree

For a Galois number field `L` and `j : L →+* ℚ̄_p`, with `P = primeOf j`, `w = P` as a place of
`L`, `v` the place of `ℚ` below it, and `F = Lj j = ℚ_p(j L)`:

  `LadicCond.ramCard F i = GlueConductor.ramCard L P i = |G_i(L_w/ℚ_v)|` (Tau Ceti),

and `[F : ℚ_p] = |D_P| = [L_w : ℚ_v]`.

No `sorry`, no `axiom`.
-/

open NumberField IsDedekindDomain
open scoped Pointwise AdicCompletionExtension

noncomputable section

namespace ZInQ.Contrib.G15.Ladic

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  (j : L →+* PadicAlgCl p)

/-- **`[ℚ_p(j L) : ℚ_p] = |D_P|`.** -/
theorem finrank_Lj :
    Module.finrank ℚ_[p] (Lj j) = Nat.card (MulAction.stabilizer Gal(L/ℚ) (primeOf j).asIdeal) := by
  have := finiteDimensional_Lj j
  have := (isFinGal_Lj j).2
  rw [← IsGalois.card_aut_eq_finrank]
  exact Nat.card_congr (decompEquivLj j).toEquiv

/-- The place of `ℚ` below `primeOf j`. -/
abbrev placeBelow : HeightOneSpectrum (𝓞 ℚ) := (primeOf j).under (𝓞 ℚ)

instance : (primeOf j).asIdeal.LiesOver (placeBelow j).asIdeal := ⟨rfl⟩

/-- **`g_i(ℚ_p(j L)/ℚ_p) = |G_i(L_w/ℚ_v)|`** (LadicCond's local field vs Tau Ceti's completion). -/
theorem ramCard_Lj_eq_card_localRam (i : ℕ) :
    LadicCond.ramCard (Lj j) i = Nat.card (localRam (placeBelow j) (primeOf j) i) := by
  rw [ramCard_Lj_eq, ramCard_eq_card_localRam (placeBelow j) (primeOf j)]

/-- **`[ℚ_p(j L) : ℚ_p] = [L_w : ℚ_v]`.** -/
theorem finrank_Lj_eq_finrank_adicCompletion :
    Module.finrank ℚ_[p] (Lj j) =
      Module.finrank ((placeBelow j).adicCompletion ℚ) ((primeOf j).adicCompletion L) := by
  rw [finrank_Lj, ← card_decompGroup_eq_finrank (placeBelow j) (primeOf j)]

/-- If `G_i(P) = 1`, every `σ ∈ LadicCond.ramSet (Lj j) i` fixes `j L` pointwise. -/
theorem apply_j_eq_of_mem_ramSet {i : ℕ} (h : GlueConductor.ramGroup L (primeOf j).asIdeal i = ⊥)
    {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : σ ∈ LadicCond.ramSet (Lj j) i) (x : L) :
    σ (j x) = j x := by
  have h1 := (mem_ramSet_iff (tauOf_spec j σ) i).mp hσ
  rw [h, Subgroup.mem_bot] at h1
  rw [← tauOf_spec, h1]
  rfl

/-- **Tame criterion** (Tau Ceti's `ramificationGroup_one_eq_bot_iff_natCast_ramificationIdx_ne_zero`):
`G_1(P) = 1` iff `e(P | v)` is nonzero in the residue field of `v`. -/
theorem ramGroup_one_eq_bot_iff :
    GlueConductor.ramGroup L (primeOf j).asIdeal 1 = ⊥ ↔
      (((primeOf j).asIdeal.ramificationIdx (𝓞 ℚ) : ℕ) : 𝓞 ℚ ⧸ (placeBelow j).asIdeal) ≠ 0 := by
  rw [ramGroup_eq_ramificationGroup]
  exact HeightOneSpectrum.ramificationGroup_one_eq_bot_iff_natCast_ramificationIdx_ne_zero
    (placeBelow j) (primeOf j)

end ZInQ.Contrib.G15.Ladic

end
