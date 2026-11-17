import ZInQKernel.Contrib.OneProof.CdOptimal.Level32

/-!
# cd-optimal: `CdOptimal` from the eta-quotient transformation law and one non-divisibility

Task cd-optimal (2026-11-16). Report: `docs/research/cd-optimal.md`; scratch and log:
`scratch/cd-optimal/`.

gz-optimal's `ZInQ.GZOptimal.CdOptimal` says that for `d ≡ 5 (mod 8)` squarefree, every period lattice
`L` of `C_d : y² = x³ − d²x` is `c₀ Λ_f` with `c₀ ∈ ℚ`, `Λ_f` the period lattice of the newform `f`
of `C_d`. Proved here (`cdOptimal_of`) from

* **`EtaW32Character`** (printed leaf; the Newman / Gordon–Hughes transformation law of eta
  quotients, for `v = η(8τ)η(32τ)²/η(16τ)³` on `Γ₀(32)`, character `(2/d)`), and
* **`CdTwistedPeriodOdd`** (glue; some period of `f` is not in `(1 + i) L`).

The proof (files in `CdOptimal/`):

1. `Unif.lean`: gz-weil's uniformization argument in general form, and **uniqueness of the period
   lattice** (`lattice_eq_of_g₂_g₃`).
2. `Structure.lean`: `Λ_f = Λ_d` is stable under `i` (`Φ_d(τ + 1/4) = iΦ_d(τ)`) and under complex
   conjugation (real coefficients); so is every lattice `L` of `C_d` (uniqueness); Gaussian rounding
   and units of `ℤ[i]` give `Λ_d = n L` or `n (1 + i) L` once `Λ_d ⊆ L`
   (`lattice_eq_of_periods`).
3. `Level32.lean`: on x0-32's eta model of `X₀(32) = 32a1`, `x₁ = (x − y/w)/2` is a coordinate of
   `C₁ = 32a2` with `dx₁/2y₁ = 2πi f₁ dτ`, invariant under `Γ₀(32) ∩ {(2/d) = 1}` by the leaf; the
   periods of `Φ₁` over that group lie in every lattice of `C₁` (`period_mem_C1`); the twist
   `Φ_d = g⁻¹ Σ_a χ_d(a) Φ₁(τ + a/d)` then gives **`Λ_d ⊆ L`** (`LamCd_le_of_etaW32`), sharpening
   gz-weil's `2 Λ_d ⊆ L`.

With gz-optimal's route A: `GZHL3.GrossZagierFormulaCd` from `GrossZagierModuliOptCd`,
`EtaW32Character` and `CdTwistedPeriodOdd` (`grossZagierFormulaCd_of_cdLeaves`). No `sorry`, no
`axiom`.
-/

noncomputable section

open Complex CongruenceSubgroup
open scoped UpperHalfPlane MatrixGroups
open ZInQ.GZWeil (eichlerCd)

namespace ZInQ.CdOpt

/-- **(GLUE) A period of the twisted newform outside `(1 + i) L`.** For `d ≡ 5 (mod 8)` squarefree
and every period lattice `L` of `C_d : y² = x³ − d²x`, some period `Φ_d(γτ) − Φ_d(τ)`, `γ ∈ Γ₀(32 d²)`,
of gz-weil's Eichler integral `Φ_d(τ) = Σ_{n ≥ 1} aₙ(C_d)/n · qⁿ` does not lie in `(1 + i) L`.

Given `Λ_d ⊆ L` (`LamCd_le_of_etaW32`), this is exactly what separates `Λ_d = n L` (`C_d` optimal)
from `Λ_d = n (1 + i) L` (the optimal curve would be the 2-isogenous `y² = x³ + 4d²x`); it is the
non-congruence part of the computation: the classes of the periods of `Φ₁` modulo `(1 + i)` times a
lattice of `C₁` are not a congruence character of `Γ₀(32)` (`scratch/cd-optimal/log.md`). Checked
numerically for the 18 values `d = 5, …, 165` of gz-optimal (`Λ_d = L` there). Not known to be
printed (SPECULATIVE): it is the statement that `C_d` is the `X₀(32d²)`-optimal curve of its class up
to the factor `n`; a reduction modulo 2 turns it into a statement about the degeneracy maps
`X₀(32 d²) → X₀(32)` (report, §4). -/
def CdTwistedPeriodOdd : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ L : PeriodPair,
    ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L →
    ∃ γ ∈ Gamma0 (32 * d ^ 2), ∃ τ : ℍ,
      eichlerCd d ((γ • τ : ℍ) : ℂ) - eichlerCd d (τ : ℂ) ∉
        L.lattice.map (LinearMap.mulLeft ℤ (1 + I))

/-- **`CdOptimal` from the eta-quotient transformation law and `CdTwistedPeriodOdd`.** -/
theorem cdOptimal_of (hW : EtaW32Character) (hT : CdTwistedPeriodOdd) :
    ZInQ.GZOptimal.CdOptimal := by
  intro d hd8 hsq N _ f hχ hf L hL
  have hd4 : d % 4 = 1 := by omega
  have hd1 : 1 < d := by omega
  rw [periodLattice_eq_LamCd hd4 hsq f hχ hf]
  obtain ⟨γ, hγ, τ, hnot⟩ := hT d hd8 hsq L hL
  exact lattice_eq_of_periods hd4 hsq hL (LamCd_le_of_etaW32 hW hd4 hd1 hsq hL)
    ⟨_, Submodule.subset_span ⟨γ, hγ, τ, rfl⟩, hnot⟩

/-- **`Λ_f ⊆ L`** for the newform `f` of `C_d` and every period lattice `L` of `C_d` (`d ≡ 1 mod 4`
squarefree, `d > 1`), from the eta-quotient transformation law: the inclusion half of `CdOptimal`
with `c₀ = 1`. -/
theorem periodLattice_le_of_etaW32 (hW : EtaW32Character) {d : ℕ} (hd4 : d % 4 = 1) (hd1 : 1 < d)
    (hsq : Squarefree d) {N : ℕ} [NeZero N] (f : HeckeRing.GL2.Newform N 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, n ≠ 0 → ZInQ.GZDecomp.coeff f n = ((shortCurve (-(d : ℚ) ^ 2)).LFunction n : ℂ))
    {L : PeriodPair} (hL : ZInQ.GZHL3.IsPeriodLattice (shortCurve (-(d : ℚ) ^ 2)) L) :
    ZInQ.GZOptimal.periodLattice f ≤ L.lattice := by
  rw [periodLattice_eq_LamCd hd4 hsq f hχ hf]
  exact LamCd_le_of_etaW32 hW hd4 hd1 hsq hL

/-- **`GZHL3.GrossZagierFormulaCd` from the optimal-parametrization leaf, the eta-quotient
transformation law and `CdTwistedPeriodOdd`** (gz-optimal's route A with `CdOptimal` proved). -/
theorem grossZagierFormulaCd_of_cdLeaves (hGZ : ZInQ.GZOptimal.GrossZagierModuliOptCd)
    (hW : EtaW32Character) (hT : CdTwistedPeriodOdd) : ZInQ.GZHL3.GrossZagierFormulaCd :=
  ZInQ.GZOptimal.grossZagierFormulaCd_of_selfOptimal hGZ (cdOptimal_of hW hT)

end ZInQ.CdOpt
