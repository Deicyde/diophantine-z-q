# x0-32 results log

## 2026-11-13 06:40 start (fresh; no earlier log)

- VERIFIED (computed, `eta.py`, exact integer q-series to q^79): the Γ₀(32) eta quotients (Ligozat
  conditions) with poles only at ∞ and order ≤ 3 there: X = η(2τ)²η(16τ)/(η(4τ)η(32τ)²) (order −2),
  Y1 = η(8τ)⁴η(16τ)²/(η(4τ)²η(32τ)⁴) and Y2 = η(τ)²η(16τ)⁴/(η(2τ)η(8τ)η(32τ)⁴) (order −3); none of order −1
  (genus 1).
- VERIFIED (`fit.py`): x = X + 2, y = ±Y1 satisfy y² = x³ + 4x to O(q³⁴) (window of 40 coefficients).
- VERIFIED (`newf.py`): f = η(4τ)²η(8τ)² = Σ aₙ qⁿ with aₙ from the Euler product of point counts of
  y² = x³+4x (a₂ = 0), n < 80. q dx/dq = −2·Y1·f exactly to q^77, so with y = −Y1: dx/(2y) = 2πi f dτ.
- VERIFIED (`cusps.py`, floating point, τ = r + 10⁻³ i): cusp images [0]↦(2,−4), [1/2]↦(2,4),
  [1/4]↦(−2,−4i), [−1/4]↦(−2,4i), [1/8]↦(−2i,0), [−1/8]↦(2i,0), [1/16]↦(0,0); agrees with
  rv-tyz-inputs §1.5a (PARI modular symbols).
- Tools: no cypari2/sympy/mpmath on this host (~/pyenv absent; uv would need network) — all computations
  in plain Python (fractions, cmath).
- COMPILED: ZInQKernel/Contrib/TYZGenus/X0.lean skeleton (defs + leaves X0-EQ, X0-INV, X0-BIJ, X0-DIFF,
  X0-NEWFORM, X0-CUSP, X0-DICT; `lake env lean`, no errors).

## 07:20 algebraic part proved (X0.lean §4–§10), all axioms = [propext, Classical.choice, Quot.sound]

- COMPILED (`lake build ZInQKernel.Contrib.TYZGenus.X0`; audit `scratch/x0-32/Audit.lean`):
  `scalePt_add` (generic `(x,y) ↦ (w²x, w³y)` between short curves is additive),
  `iotaInv_iota`, `iota_iotaInv` (`ι : A ≅ C₁` over ℚ(i), w = (1+i)/2),
  `psi_phi : psi (phi P) = 2 • P`, `phi_psi : phi (psi Q) = 2 • Q` (φ = ι∘(1+[i]), ψ = (1−[i])∘ι⁻¹),
  `phi_some` (φ(x,y) = (y²/4x², y(x²−4)/8x²), x ≠ 0), `psi_some` (ψ(x,y) = (y²/x², y(x²+1)/x²)),
  `phi_map`, `psi_map` (commute with every σ : ℚ̄ →ₐ[ℚ] ℚ̄),
  `two_nsmul_add_iPt_eq_zero_iff` (A[(1+i)³] = {O,(0,0),(2,±4),(−2,±4i),(±2i,0)}),
  `lemma316_mpr` (A[(1+i)³] ⊆ A(ℚ(i))), `tyzLemma316_iff` (TYZLemma316 ↔ A(ℚ(i)) ⊆ A[(1+i)³]),
  `curveX0_j = 1728`, `curveC1_j = 1728`, `curve32a3_j = curve32a4_j = 287496`, Δ = −4096, 64, 512, 512,
  `not_exists_variableChange_X0_C1` (no ℚ-isomorphism y²=x³+4x → y²=x³−x; c₄ ratio −1/4 < 0),
  `isoVC_smul` (explicit VariableChange over ℚ̄, u = 1 − i, maps A to C₁),
  `isCuspImage_toC` (cusp-image set over ℂ = image of A[(1+i)³] under a fixed ℚ̄ → ℂ).
- Finding: proving additivity of the 2-isogeny by brute-force formulas was avoided: φ = ι∘(1+[i]) reduces it
  to additivity of linear scalings plus CurveA's `iPt_add`.

## 08:00–08:40

- COMPILED: `X0Newform.lean` (leaf `NewformTC32` over Tau Ceti's `HeckeRing.GL2.Newform 32 2`).
- COMPILED: leaves `EtaModelWeierstrass` (eta model = ℘_L ∘ Eichler integral for any L with g₂=−16, g₃=0)
  and `EtaModelFricke`; `X0AnalyticModel` = conjunction of 9 leaves.
- VERIFIED (`fricke.py`): φ(−1/(32τ)) + φ(τ) = (2,−4) at 3 points (12 digits); x(W₃₂τ) =
  2 + 8η(2τ)η(16τ)²/(η(τ)²η(8τ)).
- COMPILED: holomorphy of x, y, f on ℍ; f, y nonvanishing; `phiC_eq_some`, `phiC_ne_zero` (under
  EtaModelEquation); `eta_add_nat`; `xC_yC_fC_T_smul` (T-invariance). Audit: 28 declarations, all
  [propext, Classical.choice, Quot.sound].
- VERIFIED (`ModParamRfl.lean`): cm-points' `CM.modParam` (verbatim copy) is `rfl`-equal to `X0.modParamF`.
- Merged origin/main (6c225515) once (STATUS.md only).
- Report docs/research/x0-32.md written.

## 09:00–09:40

- COMPILED: `phi_iPt` (φ is ℤ[i]-linear), §13 `eta_neg_conj`, `xC/yC/fC_neg_conj`, `phiC_neg_conj`.
- Merged origin/wip/cm-points (ba214e17, includes ring-class) to import CM.lean.
- COMPILED: `ZInQKernel/Contrib/TYZGenus/X0CM.lean`: `cmComplexConj : CM.CMComplexConj` (cm-points' leaf
  CM-4 proved), `tauH_conj`, `toC_galPt`; axioms [propext, Classical.choice, Quot.sound]
  (`scratch/x0-32/AuditCM.lean`).
- COMPILED: `ZInQKernel/Contrib/TYZGenus/X0Pkg.lean` (imports Package.lean; Package build incl. ring-class
  vendored TC took 3 min): `tauG_range_iff` (range of cm-points' tauG = IsTorsI3 = A[(1+i)³]),
  `lemma318_iff` (Package.Lemma318 ↔ torsion of A(ℍ'_n) ⊆ A[(1+i)³], no τ), `two_nsmul_add_iPt_tauG`;
  axioms standard (`scratch/x0-32/AuditPkg.lean`).
