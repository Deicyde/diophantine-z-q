import TailK

/-!
# qm-split, row H-2: `PkgI1.ThetaModularity` split into Igusa's two printed statements

The row (`HDec.PkgI1.ThetaModularity`, leaf-fold4 chain `LPrefix.lean` l.295; imported) is the conjunction
of two transformation laws. Igusa prints them as the modularity of two Siegel modular forms of degree 2 with
their theta expressions: `ψ₄ = 2⁻² Σ_{m even} θ_m⁸` (weight 4) and `χ₁₀ = −2⁻¹⁴ ∏_{m even} θ_m²` (weight 10),
both for `Γ₂ = Sp₄(ℤ)` with trivial character. The two leaves below are those statements in Igusa's
normalization; the row follows by clearing the constants.

Check: `scratch/qm-split/chk.sh scratch/qm-split/ThetaSplit.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.QMSplit.Theta

open HDec.PkgI1

/-- `ψ₄ = 2⁻² Σ_{m even} θ_m⁸` (Igusa's normalization). -/
def psi4 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := (1 / 4 : ℂ) * thetaSum8 Ω

/-- `χ₁₀ = −2⁻¹⁴ ∏_{m even} θ_m²` (Igusa's normalization). -/
def chi10 (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ := (-1 / 2 ^ 14 : ℂ) * thetaProd2 Ω

/-- **LEAF (Igusa: `ψ₄` is a Siegel modular form of weight 4 for `Sp₄(ℤ)`, with its theta expression).**
`ψ₄(Ω) = 2⁻² Σ_{m even} θ_m(Ω)⁸` satisfies `ψ₄(M·Ω) = det(CΩ + D)⁴ ψ₄(Ω)` for `M = [[A,B],[C,D]] ∈ Sp₄(ℤ)`
and `Ω` in the Siegel upper half-space of degree 2.

Source: J.-I. Igusa, *On Siegel modular forms of genus two*, Amer. J. Math. 84 (1962), 175-200, and
*On Siegel modular forms of genus two (II)*, Amer. J. Math. 86 (1964), 392-412 (the Eisenstein series
`ψ₄` and its expression `2⁻² Σ θ_m⁸`); *Modular forms and projective invariants*, Amer. J. Math. 89
(1967), 817-855, pp. 833-834, 848 (the row's locators; page numbers UNVERIFIED, no network). The sign
conventions of `spAct`/`spFactor` and Mathlib's `symplecticGroup` (`J = [[0, −1], [1, 0]]`, the same
group as `[[0, 1], [−1, 0]]`) were checked numerically by leaf-review-a (`theta_mod_check.py`).
Form: the printed modularity of `ψ₄` with its theta expression (published form, with the caveat that
Igusa defines `ψ₄` as an Eisenstein series and prints the theta expression as a theorem; the
transformation law of the theta expression is then the conjunction, read off the same text). -/
def IgusaPsi4 : Prop :=
  ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
    psi4 (spAct M Ω) = spFactor M Ω ^ 4 * psi4 Ω

/-- **LEAF (Igusa: `χ₁₀` is a Siegel cusp form of weight 10 for `Sp₄(ℤ)`, with its theta expression).**
`χ₁₀(Ω) = −2⁻¹⁴ ∏_{m even} θ_m(Ω)²` satisfies `χ₁₀(M·Ω) = det(CΩ + D)¹⁰ χ₁₀(Ω)` for `M ∈ Sp₄(ℤ)`
(trivial character).

Source: Igusa, Amer. J. Math. 84 (1962) (the cusp form `χ₁₀` and `χ₁₀ = −2⁻¹⁴ ∏ θ_m²`); Amer. J. Math. 89
(1967), p. 848 (page UNVERIFIED). Form: as for `IgusaPsi4`. -/
def IgusaChi10 : Prop :=
  ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
    chi10 (spAct M Ω) = spFactor M Ω ^ 10 * chi10 Ω

/-- **Row H-2 from the two printed statements** (clear the constants `2⁻²`, `−2⁻¹⁴`). -/
theorem thetaModularity_of (h4 : IgusaPsi4) (h10 : IgusaChi10) : ThetaModularity := by
  intro M hM Ω hΩ
  have a := h4 M hM Ω hΩ
  have b := h10 M hM Ω hΩ
  simp only [psi4, chi10] at a b
  constructor
  · linear_combination 4 * a
  · linear_combination (-(2 : ℂ) ^ 14) * b

end HDec.QMSplit.Theta

#print axioms HDec.QMSplit.Theta.thetaModularity_of

example : HDec.QMSplit.Theta.IgusaPsi4 → HDec.QMSplit.Theta.IgusaChi10 → HDec.PkgI1.ThetaModularity :=
  HDec.QMSplit.Theta.thetaModularity_of
