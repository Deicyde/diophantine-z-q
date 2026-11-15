import ZInQKernel.OneProof.H.TailJ

/-! # linyang-printed: `LinYangThetaCurve` from Lin–Yang's printed Example 29 and Igusa's theta expressions

Task linyang-printed (2026-11-14/15), base b5ff0474 (w63). Report: docs/research/linyang-printed.md.

* §0 verbatim copies of theta-glue's definitions `psi4Th`, `psi6Th`, `chi10Th`, `chi12Th` and of the composite
  leaf `LinYangThetaCurve` (origin/wip/theta-glue, scratch/theta-glue/ThetaGlue.lean §4-§5), in theta-glue's
  namespace so the names coincide.
* §1 genuine definitions: the degree-2 Siegel Eisenstein series `ψ_k` (sum over `Γ_∞\Sp₄(ℤ)`), Igusa's 1962 cusp
  forms `χ₁₀`, `χ₁₂` (linear combinations of Eisenstein series), Lin–Yang's normalized generators `s₂, s₃, s₅, s₆`.
* §2 two LEAVES in printed form: `IgusaThetaExpressions` (Igusa) and `LinYangEx29` (Lin–Yang, Example 29).
* §3 glue (proved): continuity of theta constants along `Ω(τ)`, countability of `Γ*`-orbits, density.
* §4 `linYangThetaCurve_of_printed : IgusaThetaExpressions → LinYangEx29 → LinYangThetaCurve` (proved).
* §5 `qmHauptmodul_of_printed : IgusaThetaExpressions → LinYangEx29 → PkgI1.QMHauptmodul` (proved).

Check: `lake env lean scratch/linyang-printed/LinYangPrinted.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.HSyn.G0Split.ThetaPt.ThetaGlue

open Complex Matrix
open _root_.ZInQ.LeafPush2 (IsSiegel)

/-! ## 0. Verbatim copies (theta-glue, scratch/theta-glue/ThetaGlue.lean l.392-470, 534-551, 578-597) -/

/-! ## 4. Igusa's theta expressions (Igusa, Amer. J. Math. 89 (1967); locators UNVERIFIED)

`ψ₄ = 2⁻² Σ_m θ_m⁸`, `ψ₆ = 2⁻² Σ_{syzygous {m₁,m₂,m₃}} ±(θ_{m₁}θ_{m₂}θ_{m₃})⁴` (60 triples),
`χ₁₀ = −2⁻¹⁴ ∏_m θ_m²`, `χ₁₂ = 2⁻¹⁷3⁻¹ Σ_{Göpel quadruples Q} ∏_{m ∉ Q} θ_m⁴` (15 quadruples).
The signs in `ψ₆` are the ones forced by `Sp₄(ℤ)`-modularity (scratch/theta-glue/py/signs.py: the ten
`θ_m⁴` are permuted with signs by generators of `Sp₄(ℤ)`, which act transitively on the 60 syzygous
triples); with them the expression is exactly the weight-6 Siegel modular form with constant term 1
and restriction `E₆⊗E₆` to `diag(τ₁, τ₂)`. The `χ₁₂` expression is exactly the weight-12 cusp form with
restriction `Δ⊗Δ` (py/igusa2.py, exact). -/

/-- Igusa's `ψ₄ = 2⁻² Σ_{m even} θ_m⁸`. -/
def psi4Th (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := PkgI1.thetaSum8 Ω / 4

/-- Igusa's `χ₁₀ = −2⁻¹⁴ ∏_{m even} θ_m²`. -/
def chi10Th (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := -PkgI1.thetaProd2 Ω / 2 ^ 14

/-- Igusa's `ψ₆ = 2⁻² Σ_{syzygous} ±(θ_{m₁}θ_{m₂}θ_{m₃})⁴`. -/
def psi6Th (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (1 / 4) * ((PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     - (PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4)

/-- Igusa's `χ₁₂ = 2⁻¹⁷3⁻¹ Σ_{Göpel Q} ∏_{m∉Q} θ_m⁴`. -/
def chi12Th (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (1 / (2 ^ 17 * 3)) * ((PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 1]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![1, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 1]) Ω * PkgI1.thetaConst (![1, 1], ![0, 0]) Ω) ^ 4
     + (PkgI1.thetaConst (![0, 0], ![0, 0]) Ω * PkgI1.thetaConst (![0, 0], ![0, 1]) Ω * PkgI1.thetaConst (![0, 0], ![1, 0]) Ω * PkgI1.thetaConst (![0, 1], ![0, 0]) Ω * PkgI1.thetaConst (![1, 0], ![0, 0]) Ω * PkgI1.thetaConst (![1, 1], ![1, 1]) Ω) ^ 4)

/-- **LEAF, COMPOSITE (Lin–Yang's Igusa vector on the QM curve, in Igusa's theta expressions, along
the explicit curve `τ ↦ Ω(τ)`).** For `τ` in the upper half-plane, at `Ω = Ω(τ)` (pkg-I1's period
matrix of the principally polarized QM surface `ℂ²/ι(𝒪)(τ,1)ᵀ`, `𝒪` the maximal order of the
quaternion algebra of discriminant 6):
`ψ₄ψ₆ = 2¹²3⁵χ₁₀` and `ψ₄³ + ψ₆² = 2¹²3⁶χ₁₂`.

Sources: Lin–Yang, *Quaternionic loci in Siegel's modular threefold*, Math. Z. 295 (2020); arXiv
1807.00466v1, Example 29 with eqs. (13)-(14): along the curve `s₃²/s₂³ = c₁j`, `s₅/(s₂s₃) = c₂`,
`s₆/s₂³ = c₃j + c₄` for Igusa's `s₂ = ψ₄, s₃ = ψ₆, s₅ = 2¹²3⁵χ₁₀, s₆ = 2¹²3⁶χ₁₂`, with
`c₁ = c₂ = c₃ = c₄ = 1` in the normalization of `j` fixed at the CM points of discriminants −4, −24
(as restated in scratch/h-v14/igusa_check.py; locators UNVERIFIED here); eliminating `j` gives the two
relations, so the statement is weaker than the printed one. Igusa, *Modular forms and projective
invariants*, Amer. J. Math. 89 (1967) for the theta expressions (§4). Faithfulness: the same
identification of `Ω(τ)` with the QM locus as `PkgI1.QMHauptmodul` (pkg-I1 §4). Numerically VERIFIED
(py/curve_check.py, 80 digits, 12 random `τ`: relative residuals ≤ 9e-78 and ≤ 5e-75). -/
def LinYangThetaCurve : Prop :=
  ∀ τ : ℂ, 0 < τ.im →
    psi4Th (PkgI1.Omega τ) * psi6Th (PkgI1.Omega τ) = 2 ^ 12 * 3 ^ 5 * chi10Th (PkgI1.Omega τ) ∧
    psi4Th (PkgI1.Omega τ) ^ 3 + psi6Th (PkgI1.Omega τ) ^ 2 = 2 ^ 12 * 3 ^ 6 * chi12Th (PkgI1.Omega τ)


end HDec.HSyn.G0Split.ThetaPt.ThetaGlue

namespace HDec.HSyn.G0Split.ThetaPt.LinYangPrinted

open Complex Matrix Filter Topology
open ThetaGlue (psi4Th psi6Th chi10Th chi12Th LinYangThetaCurve)
open HSyn.G0Split.FibreQM.PeriodMap (U isOpen_U thTerm qf quad_lower differentiableAt_omega summable_gb2
  norm_thTerm_le omegaSiegel_proof)

/-! ## 1. Genuine definitions: Siegel Eisenstein series, Igusa's `χ₁₀`, `χ₁₂`, Lin–Yang's `s_k` -/

/-- Integer `4 × 4` matrices in block form. -/
abbrev SpMat := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ

/-- Same coset of the Siegel parabolic `Γ_∞ = {M ∈ Sp₄(ℤ) : C = 0}`: the bottom block rows satisfy
`(C_N, D_N) = U·(C_M, D_M)` for some `U ∈ GL₂(ℤ)`. -/
def botRel (M N : Matrix.symplecticGroup (Fin 2) ℤ) : Prop :=
  ∃ U : GL (Fin 2) ℤ,
    (N : SpMat).toBlocks₂₁ = (U : Matrix (Fin 2) (Fin 2) ℤ) * (M : SpMat).toBlocks₂₁ ∧
    (N : SpMat).toBlocks₂₂ = (U : Matrix (Fin 2) (Fin 2) ℤ) * (M : SpMat).toBlocks₂₂

theorem botRel_equiv : Equivalence botRel where
  refl M := ⟨1, by simp, by simp⟩
  symm := by
    rintro M N ⟨U, h1, h2⟩
    refine ⟨U⁻¹, ?_, ?_⟩
    · rw [h1, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    · rw [h2, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  trans := by
    rintro M N P ⟨U, h1, h2⟩ ⟨V, h3, h4⟩
    refine ⟨V * U, ?_, ?_⟩
    · rw [h3, h1, Units.val_mul, Matrix.mul_assoc]
    · rw [h4, h2, Units.val_mul, Matrix.mul_assoc]

/-- The coset relation as a setoid on `Sp₄(ℤ)`. -/
def botSetoid : Setoid (Matrix.symplecticGroup (Fin 2) ℤ) := ⟨botRel, botRel_equiv⟩

/-- `Γ_∞\Sp₄(ℤ)`, i.e. the classes of coprime symmetric pairs `(C, D)` modulo `GL₂(ℤ)`. -/
abbrev SiegelCosets := Quotient botSetoid

/-- **The Siegel Eisenstein series of degree 2 and weight `k`** (Igusa, Amer. J. Math. 84 (1962), the forms
`ψ_k`; the standard definition, e.g. Klingen, *Introductory lectures on Siegel modular forms*, §5):
`ψ_k(Ω) = Σ_{M ∈ Γ_∞\Sp₄(ℤ)} det(CΩ + D)^{-k}`, one representative per coset. For even `k` the summand does not
depend on the representative (`det U = ±1`); for `k ≥ 4` the series converges absolutely on `𝔥₂`, so the `tsum`
is the classical value. -/
def siegelEis (k : ℕ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑' c : SiegelCosets,
    (PkgI1.spFactor ((Quotient.out c : Matrix.symplecticGroup (Fin 2) ℤ) : SpMat) Ω)⁻¹ ^ k

/-- **Igusa's cusp form `χ₁₀`** (Igusa 1962, as a combination of Eisenstein series; constants recalled,
UNVERIFIED as a citation, VERIFIED against the theta expression on 76 Fourier coefficients, py/fourier.py):
`χ₁₀ = −43867·2⁻¹²3⁻⁵5⁻²7⁻¹53⁻¹ (ψ₄ψ₆ − ψ₁₀)`. -/
def igusaChi10E (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (-43867 / (2 ^ 12 * 3 ^ 5 * 5 ^ 2 * 7 * 53) : ℂ) * (siegelEis 4 Ω * siegelEis 6 Ω - siegelEis 10 Ω)

/-- **Igusa's cusp form `χ₁₂`** (Igusa 1962; same status as `igusaChi10E`):
`χ₁₂ = 131·593·2⁻¹³3⁻⁷5⁻³7⁻²337⁻¹ (3²7²ψ₄³ + 2·5³ψ₆² − 691ψ₁₂)`. -/
def igusaChi12E (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  (131 * 593 / (2 ^ 13 * 3 ^ 7 * 5 ^ 3 * 7 ^ 2 * 337) : ℂ) *
    (3 ^ 2 * 7 ^ 2 * siegelEis 4 Ω ^ 3 + 2 * 5 ^ 3 * siegelEis 6 Ω ^ 2 - 691 * siegelEis 12 Ω)

/-- Lin–Yang's normalized generators (arXiv:1807.00466v1 §2, as restated in scratch/h-v14/igusa_check.py):
`s₂ = ψ₄`. -/
def lyS2 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := siegelEis 4 Ω
/-- `s₃ = ψ₆`. -/
def lyS3 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := siegelEis 6 Ω
/-- `s₅ = 2¹²3⁵χ₁₀`. -/
def lyS5 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 2 ^ 12 * 3 ^ 5 * igusaChi10E Ω
/-- `s₆ = 2¹²3⁶χ₁₂`. -/
def lyS6 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := 2 ^ 12 * 3 ^ 6 * igusaChi12E Ω

/-! ## 2. The two leaves, in printed form -/

/-- **LEAF (Igusa: the theta expressions of the generators).** On the Siegel upper half-space `𝔥₂`, the Eisenstein
series `ψ₄`, `ψ₆` and Igusa's cusp forms `χ₁₀`, `χ₁₂` equal their theta expressions:
`ψ₄ = 2⁻² Σ_m θ_m⁸`, `ψ₆ = 2⁻² Σ_{syzygous} ±(θ_{m₁}θ_{m₂}θ_{m₃})⁴`, `χ₁₀ = −2⁻¹⁴ ∏_m θ_m²`,
`χ₁₂ = 2⁻¹⁷3⁻¹ Σ_{Göpel Q} ∏_{m ∉ Q} θ_m⁴` (theta-glue's `psi4Th`, `psi6Th`, `chi10Th`, `chi12Th`).

Sources: J.-I. Igusa, *On Siegel modular forms of genus two (II)*, Amer. J. Math. 86 (1964), and *Modular forms and
projective invariants*, Amer. J. Math. 89 (1967), p. 848 (locators UNVERIFIED, no network; the printed sign rule of
`ψ₆` was not read). Evidence (VERIFIED, exact, py/fourier.py): all 76 Fourier coefficients at half-integral
`T = (n, r, m)`, `n, m ≤ 2`, agree on both sides; since `dim M_k(Sp₄(ℤ)) = 1, 1, 2, 3` for `k = 4, 6, 10, 12` and
the theta expressions are modular (theta-glue py/invariants.py), this pins the identities, including the sign
choice in `ψ₆` and Igusa's 1962 constants in `igusaChi10E`, `igusaChi12E`. Form: printed (the theta expressions as
theorems about Igusa's forms). -/
def IgusaThetaExpressions : Prop :=
  ∀ Ω ∈ PkgI1.SiegelH2,
    siegelEis 4 Ω = psi4Th Ω ∧ siegelEis 6 Ω = psi6Th Ω ∧
      igusaChi10E Ω = chi10Th Ω ∧ igusaChi12E Ω = chi12Th Ω

/-- **LEAF (Lin–Yang 2020, Example 29: the quaternionic locus of discriminant 6 in Igusa's generators, as functions
of the Hauptmodul `j₆`).** There is a Hauptmodul `j₆ : Γ*\ℍ = X₆/W → P¹` (continuous on `ℍ`, fibres exactly the
`Γ*`-orbits, surjective) with `j₆ = 0, ∞, −16/27` at the CM points of discriminants `−4, −3, −24`, such that along the
modular embedding `τ ↦ Ω(τ)` of the QM surfaces, wherever `j₆(τ) = z ≠ ∞`,
`s₃² = z·s₂³`, `s₅ = s₂s₃`, `s₆ = (z + 1)·s₂³`,
i.e. Lin–Yang's printed `s₃²/s₂³ = j₆`, `s₅/(s₂s₃) = 1`, `s₆/s₂³ = j₆ + 1` with denominators cleared.

Sources: Y.-H. Lin, Y. Yang, *Quaternionic loci in Siegel's modular threefold*, Math. Z. 295 (2020), 775-819;
arXiv:1807.00466v1, Example 29 (pp. 20-21, discriminant 6; the Hauptmodul `j₆` of `X₀⁶(1)/W₆` defined by its values
at the CM points of discriminants `−4, −3, −24`, VERIFIED in arXiv v1 by h-v14 row L719), with the normalization
`s₂ = ψ₄, s₃ = ψ₆, s₅ = 2¹²3⁵χ₁₀, s₆ = 2¹²3⁶χ₁₂` and the constants `c₁ = c₂ = c₃ = c₄ = 1` (h-v14 §5.3,
scratch/h-v14/igusa_check.py, from the arXiv text: Lin–Yang fix them at discriminant `−19`, `j₆ = 81/64`; the
display itself was not re-read here: UNVERIFIED). Form: consequence of the printed statement (an identity of
meromorphic functions on `X₆/W`, evaluated where `j₆` is finite), never stronger. Faithfulness: as for
`PkgI1.QMHauptmodul`, `Ω(τ)` is pkg-I1's period matrix of the principally polarized QM surface at `τ` (pkg-I1 §4);
the ratios are `Sp₄(ℤ)`-invariant, so the choice of symplectic basis does not matter. The CM clauses are verbatim
those of `PkgI1.QMHauptmodul`. Numerically consistent: with Igusa's theta expressions this is theta-glue's
80-digit check of `LinYangThetaCurve` together with pkg-I1's values of `j_θ = s₃²/s₂³ ∘ Ω`. -/
def LinYangEx29 : Prop :=
  ∃ j6 : UpperHalfPlane → OnePoint ℂ, Continuous j6 ∧
    (∀ τ τ' : UpperHalfPlane, j6 τ = j6 τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ') ∧
    Function.Surjective j6 ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -1 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = ((0 : ℂ) : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x - x + 1 = 0 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = (OnePoint.infty : OnePoint ℂ)) ∧
    (∀ x : PkgI1.B, PkgI1.InO x → x * x = -6 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = ((-16/27 : ℂ) : OnePoint ℂ)) ∧
    ∀ τ : UpperHalfPlane, ∀ z : ℂ, j6 τ = (z : OnePoint ℂ) →
      lyS3 (PkgI1.Omega τ) ^ 2 = z * lyS2 (PkgI1.Omega τ) ^ 3 ∧
      lyS5 (PkgI1.Omega τ) = lyS2 (PkgI1.Omega τ) * lyS3 (PkgI1.Omega τ) ∧
      lyS6 (PkgI1.Omega τ) = (z + 1) * lyS2 (PkgI1.Omega τ) ^ 3

/-! ## 3. Glue (proved): continuity along `Ω(τ)`, countable orbits, density -/

/-- Each theta constant along `Ω` is analytic on `ℍ` (copy of the inner step of period-map's
`thetaOmegaAnalytic_of`, TailJ). -/
theorem thetaConst_omega_analyticAt {τ₀ : ℂ} (hτ₀ : τ₀ ∈ U) (m : PkgI1.Char2) :
    AnalyticAt ℂ (fun τ => PkgI1.thetaConst m (PkgI1.Omega τ)) τ₀ := by
  have hS := omegaSiegel_proof
  have hτ₀' : (0 : ℝ) < τ₀.im := hτ₀
  obtain ⟨hsym, hpd⟩ := hS τ₀ hτ₀'
  set p : ℂ → ℝ := fun τ => (PkgI1.Omega τ 0 0).im with hp
  set q : ℂ → ℝ := fun τ => ((PkgI1.Omega τ 0 1).im + (PkgI1.Omega τ 1 0).im) / 2 with hq
  set r : ℂ → ℝ := fun τ => (PkgI1.Omega τ 1 1).im with hr
  have hcont : ∀ i j, ContinuousAt (fun τ => (PkgI1.Omega τ i j).im) τ₀ := fun i j =>
    Complex.continuous_im.continuousAt.comp (differentiableAt_omega hτ₀'.ne' i j).continuousAt
  have hp0 : 0 < p τ₀ := by
    have := hpd.diag_pos (i := 0); simpa [hp] using this
  have hr0 : 0 < r τ₀ := by
    have := hpd.diag_pos (i := 1); simpa [hr] using this
  have hsym01 : PkgI1.Omega τ₀ 1 0 = PkgI1.Omega τ₀ 0 1 := by
    have := congrFun (congrFun hsym 0) 1; simpa using this
  have hdet0 : 0 < p τ₀ * r τ₀ - q τ₀ ^ 2 := by
    have := hpd.det_pos
    rw [Matrix.det_fin_two] at this
    simp only [Matrix.map_apply] at this
    rw [hsym01] at this
    simp only [hp, hq, hr, hsym01]
    nlinarith [this]
  set g : ℂ → ℝ := fun τ => (p τ * r τ - q τ ^ 2) / (p τ + r τ) with hg
  have hg0 : 0 < g τ₀ := div_pos hdet0 (add_pos hp0 hr0)
  have hpc : ContinuousAt p τ₀ := hcont 0 0
  have hrc : ContinuousAt r τ₀ := hcont 1 1
  have hqc : ContinuousAt q τ₀ := ((hcont 0 1).add (hcont 1 0)).div_const 2
  have hgc : ContinuousAt g τ₀ :=
    ((hpc.mul hrc).sub (hqc.pow 2)).div (hpc.add hrc) (add_pos hp0 hr0).ne'
  have hev : ∀ᶠ τ in 𝓝 τ₀, τ ∈ U ∧ 0 < p τ + r τ ∧ g τ₀ / 2 < g τ := by
    refine (show ∀ᶠ τ in 𝓝 τ₀, τ ∈ U from isOpen_U.mem_nhds hτ₀).and ((?_ : ∀ᶠ τ in 𝓝 τ₀, 0 < p τ + r τ).and ?_)
    · exact (hpc.add hrc).eventually (lt_mem_nhds (add_pos hp0 hr0))
    · exact hgc.eventually (lt_mem_nhds (half_lt_self hg0))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set c := g τ₀ / 2 with hcdef
  have hc : 0 < c := half_pos hg0
  have hq_ball : ∀ τ ∈ Metric.ball τ₀ ε, ∀ w : Fin 2 → ℝ, c * (w 0 ^ 2 + w 1 ^ 2) ≤ qf τ w := by
    intro τ hτ w
    obtain ⟨-, hpr, hgt⟩ := hball τ hτ
    have hl := quad_lower (p τ) (q τ) (r τ) (w 0) (w 1) hpr
    have hw : 0 ≤ w 0 ^ 2 + w 1 ^ 2 := by positivity
    calc c * (w 0 ^ 2 + w 1 ^ 2) ≤ g τ * (w 0 ^ 2 + w 1 ^ 2) :=
          mul_le_mul_of_nonneg_right hgt.le hw
      _ ≤ _ := by
        refine hl.trans (le_of_eq ?_)
        simp only [qf, hp, hq, hr]
        ring
  have hdiff : ∀ n, DifferentiableOn ℂ (thTerm m n) (Metric.ball τ₀ ε) := by
    intro n σ hσ
    have hσU : (0 : ℝ) < σ.im := (hball σ hσ).1
    have hΩ := fun i j => differentiableAt_omega hσU.ne' i j
    apply DifferentiableAt.differentiableWithinAt
    set V : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2 with hV
    set Bv : Fin 2 → ℂ := fun k => ((m.2 k : ℕ) : ℂ) with hBv
    have key : thTerm m n = fun τ => Complex.exp (Real.pi * I * (V ⬝ᵥ (PkgI1.Omega τ *ᵥ V)) +
        Real.pi * I * (V ⬝ᵥ Bv)) := rfl
    have hq : DifferentiableAt ℂ (fun τ => V ⬝ᵥ (PkgI1.Omega τ *ᵥ V)) σ := by
      simp only [dotProduct, Matrix.mulVec]
      refine DifferentiableAt.fun_sum fun i _ => ?_
      refine DifferentiableAt.const_mul (DifferentiableAt.fun_sum fun j _ => ?_) _
      exact (hΩ i j).mul_const _
    rw [key]
    exact ((hq.const_mul _).add_const _).cexp
  have hdon : DifferentiableOn ℂ (fun τ => PkgI1.thetaConst m (PkgI1.Omega τ))
      (Metric.ball τ₀ ε) :=
    differentiableOn_tsum_of_summable_norm (summable_gb2 hc) hdiff Metric.isOpen_ball
      (fun n τ hτ => norm_thTerm_le hc m n τ (hq_ball τ hτ))
  exact hdon.analyticAt (Metric.ball_mem_nhds τ₀ hε)

/-- The ten theta constants along `Ω` are continuous on `ℍ`. -/
theorem thetaVec_continuousOn :
    ContinuousOn (fun τ : ℂ => fun m : PkgI1.Char2 => PkgI1.thetaConst m (PkgI1.Omega τ)) U :=
  continuousOn_pi.mpr fun m _ hτ => (thetaConst_omega_analyticAt hτ m).continuousAt.continuousWithinAt

/-- `ψ₄` as a polynomial in the theta constants. -/
def Q4 (t : PkgI1.Char2 → ℂ) : ℂ := (∑ m ∈ PkgI1.evenChars, t m ^ 8) / 4
/-- `χ₁₀` as a polynomial in the theta constants. -/
def Q10 (t : PkgI1.Char2 → ℂ) : ℂ := -(∏ m ∈ PkgI1.evenChars, t m ^ 2) / 2 ^ 14
def Q6 (t : PkgI1.Char2 → ℂ) : ℂ :=
  (1 / 4) * ((t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0])) ^ 4
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 1])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0])) ^ 4
     + (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     - (t (![0, 0], ![1, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4)

def Q12 (t : PkgI1.Char2 → ℂ) : ℂ :=
  (1 / (2 ^ 17 * 3)) * ((t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![1, 0]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 1], ![0, 0]) * t (![0, 1], ![1, 0]) * t (![1, 1], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 1]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![1, 1])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![1, 0]) * t (![1, 0], ![0, 1]) * t (![1, 1], ![0, 0])) ^ 4
     + (t (![0, 0], ![0, 0]) * t (![0, 0], ![0, 1]) * t (![0, 0], ![1, 0]) * t (![0, 1], ![0, 0]) * t (![1, 0], ![0, 0]) * t (![1, 1], ![1, 1])) ^ 4)

theorem psi4Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) : psi4Th Ω = Q4 (fun m => PkgI1.thetaConst m Ω) := rfl
set_option maxRecDepth 100000 in
theorem psi6Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) : psi6Th Ω = Q6 (fun m => PkgI1.thetaConst m Ω) := rfl
theorem chi10Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) : chi10Th Ω = Q10 (fun m => PkgI1.thetaConst m Ω) := rfl
set_option maxRecDepth 100000 in
theorem chi12Th_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) : chi12Th Ω = Q12 (fun m => PkgI1.thetaConst m Ω) := rfl

theorem continuous_Q4 : Continuous Q4 :=
  (continuous_finset_sum _ fun m _ => (continuous_apply m).pow 8).div_const 4
theorem continuous_Q10 : Continuous Q10 :=
  (continuous_finset_prod _ fun m _ => (continuous_apply m).pow 2).neg.div_const _
theorem continuous_Q6 : Continuous Q6 := by unfold Q6; fun_prop
theorem continuous_Q12 : Continuous Q12 := by unfold Q12; fun_prop

theorem contOn_comp {Q : (PkgI1.Char2 → ℂ) → ℂ} (hQ : Continuous Q) :
    ContinuousOn (fun τ : ℂ => Q (fun m => PkgI1.thetaConst m (PkgI1.Omega τ))) U :=
  hQ.comp_continuousOn thetaVec_continuousOn

theorem psi4_contOn : ContinuousOn (fun τ : ℂ => psi4Th (PkgI1.Omega τ)) U := contOn_comp continuous_Q4
theorem psi6_contOn : ContinuousOn (fun τ : ℂ => psi6Th (PkgI1.Omega τ)) U := by
  rw [show (fun τ : ℂ => psi6Th (PkgI1.Omega τ)) = fun τ => Q6 (fun m => PkgI1.thetaConst m (PkgI1.Omega τ)) from
    funext fun τ => psi6Th_eq _]
  exact contOn_comp continuous_Q6
theorem chi10_contOn : ContinuousOn (fun τ : ℂ => chi10Th (PkgI1.Omega τ)) U := contOn_comp continuous_Q10
theorem chi12_contOn : ContinuousOn (fun τ : ℂ => chi12Th (PkgI1.Omega τ)) U := by
  rw [show (fun τ : ℂ => chi12Th (PkgI1.Omega τ)) = fun τ => Q12 (fun m => PkgI1.thetaConst m (PkgI1.Omega τ)) from
    funext fun τ => chi12Th_eq _]
  exact contOn_comp continuous_Q12

instance countable_B : Countable PkgI1.B :=
  (QuaternionAlgebra.equivTuple (2 : ℚ) 0 (-3)).injective.countable

/-- `Γ*` is countable (its elements are `ι(x)`, `x ∈ B`). -/
theorem gammaStar_countable : PkgI1.GammaStar.Countable := by
  have h : PkgI1.GammaStar ⊆
      (fun γ : GL (Fin 2) ℝ => (γ : Matrix (Fin 2) (Fin 2) ℝ)) ⁻¹' Set.range PkgI1.iota := by
    rintro γ ⟨x, -, hx, -⟩
    exact ⟨x, hx.symm⟩
  exact ((Set.countable_range _).preimage (fun a b hab => Units.ext hab)).mono h

/-- If the fibres of `j₆` are `Γ*`-orbits, every fibre is countable. -/
theorem fibre_countable {j6 : UpperHalfPlane → OnePoint ℂ}
    (hfib : ∀ τ τ' : UpperHalfPlane, j6 τ = j6 τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ')
    (w : OnePoint ℂ) : {τ | j6 τ = w}.Countable := by
  rcases Set.eq_empty_or_nonempty {τ | j6 τ = w} with h | ⟨τ₀, hτ₀⟩
  · rw [h]; exact Set.countable_empty
  · refine (gammaStar_countable.image (fun γ => γ • τ₀)).mono ?_
    intro τ hτ
    have e : j6 τ₀ = j6 τ := (show j6 τ₀ = w from hτ₀).trans (show j6 τ = w from hτ).symm
    obtain ⟨γ, hγ, hγτ⟩ := (hfib τ₀ τ).1 e
    exact ⟨γ, hγ, hγτ⟩

/-- Two continuous functions on an open `V ⊆ ℂ` that agree off a countable set agree on `V`. -/
theorem eqOn_of_countable {X : Type*} [TopologicalSpace X] [T2Space X] {V : Set ℂ} (hV : IsOpen V)
    {f g : ℂ → X} {S : Set ℂ} (hS : S.Countable) (hf : ContinuousOn f V) (hg : ContinuousOn g V)
    (h : ∀ z ∈ V, z ∉ S → f z = g z) : Set.EqOn f g V :=
  Set.EqOn.of_subset_closure (s := V ∩ Sᶜ) (fun z hz => h z hz.1 hz.2) hf hg Set.inter_subset_left
    ((hS.dense_compl ℂ).open_subset_closure_inter hV)

/-! ## 4. `LinYangThetaCurve` from the printed leaves (eliminating `j₆`) -/

/-- **`LinYangThetaCurve` from Igusa's theta expressions and Lin–Yang's Example 29 (proved).** Where `j₆ = z` is
finite, `s₅ = s₂s₃` and `s₆ = (z+1)s₂³ = s₂³ + s₃²`; the points where `j₆ = ∞` form one `Γ*`-orbit, which is countable,
and both sides are continuous on `ℍ`. -/
theorem linYangThetaCurve_of_printed (hI : IgusaThetaExpressions) (hL : LinYangEx29) :
    LinYangThetaCurve := by
  obtain ⟨j6, -, hfib, -, -, -, -, hrel⟩ := hL
  set S : Set ℂ := (fun τ : UpperHalfPlane => (τ : ℂ)) '' {τ | j6 τ = OnePoint.infty} with hSdef
  have hS : S.Countable := (fibre_countable hfib _).image _
  have hoff : ∀ z ∈ U, z ∉ S →
      psi4Th (PkgI1.Omega z) * psi6Th (PkgI1.Omega z) = 2 ^ 12 * 3 ^ 5 * chi10Th (PkgI1.Omega z) ∧
      psi4Th (PkgI1.Omega z) ^ 3 + psi6Th (PkgI1.Omega z) ^ 2 =
        2 ^ 12 * 3 ^ 6 * chi12Th (PkgI1.Omega z) := by
    intro z hz hzS
    let τ : UpperHalfPlane := ⟨z, hz⟩
    have hne : j6 τ ≠ OnePoint.infty := fun h => hzS ⟨τ, h, rfl⟩
    obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hne
    obtain ⟨h1, h2, h3⟩ := hrel τ w hw.symm
    obtain ⟨e4, e6, e10, e12⟩ := hI _ (omegaSiegel_proof z hz)
    have hτz : ((τ : UpperHalfPlane) : ℂ) = z := rfl
    rw [hτz] at h1 h2 h3
    simp only [lyS2, lyS3, lyS5, lyS6] at h1 h2 h3
    rw [e4, e6] at h1
    rw [e4, e6, e10] at h2
    rw [e4, e12] at h3
    exact ⟨by linear_combination (-1 : ℂ) * h2, by linear_combination h1 - h3⟩
  intro z hz
  have hzU : z ∈ U := hz
  refine ⟨?_, ?_⟩
  · exact eqOn_of_countable isOpen_U hS (psi4_contOn.mul psi6_contOn)
      (continuousOn_const.mul chi10_contOn) (fun z hz hzS => (hoff z hz hzS).1) hzU
  · exact eqOn_of_countable isOpen_U hS ((psi4_contOn.pow 3).add (psi6_contOn.pow 2))
      (continuousOn_const.mul chi12_contOn) (fun z hz hzS => (hoff z hz hzS).2) hzU

/-! ## 5. `PkgI1.QMHauptmodul` from the same two leaves -/

/-- `j₆` read on `ℂ` through Mathlib's section `ofComplex : ℂ → ℍ`. -/
def onC (j6 : UpperHalfPlane → OnePoint ℂ) : ℂ → OnePoint ℂ := j6 ∘ UpperHalfPlane.ofComplex

theorem ofComplex_continuousAt {z : ℂ} (hz : 0 < z.im) : ContinuousAt UpperHalfPlane.ofComplex z :=
  UpperHalfPlane.isEmbedding_coe.isInducing.continuousAt_iff.mpr
    (continuousAt_id.congr (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex hz).symm)

theorem onC_contOn {j6 : UpperHalfPlane → OnePoint ℂ} (hc : Continuous j6) : ContinuousOn (onC j6) U :=
  fun z hz => (hc.continuousAt.comp (ofComplex_continuousAt hz)).continuousWithinAt

theorem onC_of_pos (j6 : UpperHalfPlane → OnePoint ℂ) {z : ℂ} (hz : 0 < z.im) : onC j6 z = j6 ⟨z, hz⟩ := by
  simp only [onC, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem onC_coe (j6 : UpperHalfPlane → OnePoint ℂ) (τ : UpperHalfPlane) : onC j6 τ = j6 τ := by
  simp only [onC, Function.comp_apply, UpperHalfPlane.ofComplex_apply]

/-- **`PkgI1.QMHauptmodul` from Igusa's theta expressions and Lin–Yang's Example 29 (proved).** Take `f = j₆`.
Where `j₆ = z` is finite and `ψ₄ ≠ 0`, `z = s₃²/s₂³ = 16·144⁵χ₁₀²/ψ₄⁵ = jNum/jDen` (using `s₅ = s₂s₃`). If `j₆ = ∞` at
a point with `ψ₄ ≠ 0`, then near it `j₆ = s₃²/s₂³` off a countable set, so by continuity `j₆` is finite there:
impossible. -/
theorem qmHauptmodul_of_printed (hI : IgusaThetaExpressions) (hL : LinYangEx29) : PkgI1.QMHauptmodul := by
  obtain ⟨j6, hc, hfib, hsurj, h4, h3, h24, hrel⟩ := hL
  refine ⟨j6, hc, ?_, hfib, hsurj, h4, h3, h24⟩
  -- the value of `j₆` where it is finite and `ψ₄ ≠ 0`
  have hval : ∀ (τ : UpperHalfPlane) (w : ℂ), j6 τ = (w : OnePoint ℂ) →
      psi4Th (PkgI1.Omega τ) ≠ 0 → w = psi6Th (PkgI1.Omega τ) ^ 2 / psi4Th (PkgI1.Omega τ) ^ 3 := by
    intro τ w hw hp
    obtain ⟨h1, -, -⟩ := hrel τ w hw
    obtain ⟨e4, e6, -, -⟩ := hI _ (omegaSiegel_proof τ τ.im_pos)
    simp only [lyS2, lyS3] at h1
    rw [e4, e6] at h1
    rw [eq_div_iff (pow_ne_zero 3 hp)]
    exact h1.symm
  intro τ hD
  have hS8 : PkgI1.thetaSum8 (PkgI1.Omega τ) ≠ 0 := fun h => hD (by rw [PkgI1.jDen, h]; ring)
  have hp4 : psi4Th (PkgI1.Omega τ) ≠ 0 := by
    unfold ThetaGlue.psi4Th; exact div_ne_zero hS8 (by norm_num)
  by_cases hinf : j6 τ = OnePoint.infty
  · exfalso
    set V : Set ℂ := U ∩ (fun z => psi4Th (PkgI1.Omega z)) ⁻¹' {0}ᶜ with hV
    have hVo : IsOpen V := psi4_contOn.isOpen_inter_preimage isOpen_U isOpen_compl_singleton
    set S : Set ℂ := (fun τ : UpperHalfPlane => (τ : ℂ)) '' {τ | j6 τ = OnePoint.infty} with hSdef
    have hS : S.Countable := (fibre_countable hfib _).image _
    have hG : ContinuousOn
        (fun z => ((psi6Th (PkgI1.Omega z) ^ 2 / psi4Th (PkgI1.Omega z) ^ 3 : ℂ) : OnePoint ℂ)) V :=
      OnePoint.continuous_coe.comp_continuousOn
        (((psi6_contOn.pow 2).mono Set.inter_subset_left).div ((psi4_contOn.pow 3).mono Set.inter_subset_left)
          (fun z hz => pow_ne_zero 3 hz.2))
    have hEq := eqOn_of_countable hVo hS ((onC_contOn hc).mono Set.inter_subset_left) hG
      (fun z hz hzS => by
        have hzU : 0 < z.im := hz.1
        let σ : UpperHalfPlane := ⟨z, hzU⟩
        have hne : j6 σ ≠ OnePoint.infty := fun h => hzS ⟨σ, h, rfl⟩
        obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hne
        have hwv := hval σ w hw.symm hz.2
        show onC j6 z = _
        rw [onC_of_pos j6 hzU]
        show j6 σ = _
        rw [← hw, hwv])
    have hτV : (τ : ℂ) ∈ V := ⟨τ.im_pos, hp4⟩
    have := hEq hτV
    rw [onC_coe, hinf] at this
    exact OnePoint.coe_ne_infty _ this.symm
  · obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hinf
    rw [← hw]
    congr 1
    obtain ⟨-, h2, -⟩ := hrel τ w hw.symm
    obtain ⟨e4, e6, e10, -⟩ := hI _ (omegaSiegel_proof τ τ.im_pos)
    simp only [lyS2, lyS3, lyS5] at h2
    rw [e4, e6, e10] at h2
    rw [hval τ w hw.symm hp4]
    have hP : PkgI1.thetaProd2 (PkgI1.Omega τ) = -2 ^ 14 * chi10Th (PkgI1.Omega τ) := by
      unfold ThetaGlue.chi10Th; ring
    have hSum : PkgI1.thetaSum8 (PkgI1.Omega τ) = 4 * psi4Th (PkgI1.Omega τ) := by
      unfold ThetaGlue.psi4Th; ring
    rw [PkgI1.jNum, PkgI1.jDen, hP, hSum]
    have hc10 : chi10Th (PkgI1.Omega τ) =
        psi4Th (PkgI1.Omega τ) * psi6Th (PkgI1.Omega τ) / (2 ^ 12 * 3 ^ 5) := by
      rw [← h2]; ring
    rw [hc10]
    generalize psi4Th (PkgI1.Omega τ) = p at hp4 ⊢
    generalize psi6Th (PkgI1.Omega τ) = q
    field_simp
    ring

end HDec.HSyn.G0Split.ThetaPt.LinYangPrinted

end

#print axioms HDec.HSyn.G0Split.ThetaPt.LinYangPrinted.linYangThetaCurve_of_printed
#print axioms HDec.HSyn.G0Split.ThetaPt.LinYangPrinted.qmHauptmodul_of_printed
