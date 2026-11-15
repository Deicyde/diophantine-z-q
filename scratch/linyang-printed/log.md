# linyang-printed results log

- Base b5ff0474 (w63). theta-glue (origin/wip/theta-glue) and igusa-alg (origin/wip/igusa-alg c9360203) read via
  `git show`; not merged. Olean tree: `.lake/build` and `lean/.lake/build` copied from ~/dzq-check2 (HEAD 29885092;
  `git diff --stat b5ff0474 29885092 -- ZInQKernel/` touches only TailY, TailZ7, TailZ14, TailZ15, TailZ20-22,
  Discharges, Main, so TailA..TailX oleans are valid for this base).
- py/fourier.py (VERIFIED, exact, sympy 1.14 via `uv --offline`): Fourier coefficients at every half-integral
  semidefinite T = (n, r, m) with n, m <= 2 (fourier2.out; n, m <= 1 in fourier1.out) of
  * theta-glue's Lean theta expressions psi4Th, psi6Th (60 signed syzygous terms parsed from the Lean text),
    chi10Th, chi12Th (15 Goepel terms parsed from the Lean text), and
  * the degree-2 Siegel Eisenstein series psi_4, psi_6, psi_10, psi_12 (Maass/Cohen coefficient formula:
    rank 2: 2/(zeta(1-k) zeta(3-2k)) sum_{d | e(T)} d^{k-1} H(k-1, det(2T)/d^2); rank 1: genus-1 coefficient;
    formula recalled, UNVERIFIED as a citation, but self-checked: psi_4 and psi_6 are forced by dim M_4 = dim M_6 = 1),
    with Igusa's 1962 cusp forms chi10 = -43867 2^-12 3^-5 5^-2 7^-1 53^-1 (psi4 psi6 - psi10),
    chi12 = 131.593 2^-13 3^-7 5^-3 7^-2 337^-1 (3^2 7^2 psi4^3 + 2.5^3 psi6^2 - 691 psi12) (constants recalled,
    UNVERIFIED as citations)
  agree exactly: 76 of 76 coefficients (e.g. psi4: 1, 240, 30240, 13440; psi6: 1, -504, 166320, 44352;
  chi10: a(1,0,1) = 1/2, a(1,1,1) = -1/4; chi12: a(1,0,1) = 5/6, a(1,1,1) = 1/12).
  Since dim M_4, M_6, M_10, M_12 = 1, 1, 2, 3 and theta-glue VERIFIED the theta expressions are Sp4(Z)-invariant
  (py/invariants.py there), this pins Igusa's printed normalizations: Eisenstein psi4 = 2^-2 sum theta^8,
  Eisenstein psi6 = theta-glue's signed syzygous sum, Igusa's chi10 = -2^-14 prod theta^2, chi12 = 2^-17 3^-1 sum_Goepel.
  In particular theta-glue's psi6 sign choice is the Eisenstein one (it equals psi_6, not -psi_6).
- LinYangPrinted.lean (imports ZInQKernel.OneProof.H.TailJ) COMPILES (VERIFIED, `lake env lean`, 23 s, no errors,
  no sorry). `#print axioms` = [propext, Classical.choice, Quot.sound] for
  `LinYangPrinted.linYangThetaCurve_of_printed : IgusaThetaExpressions → LinYangEx29 → ThetaGlue.LinYangThetaCurve`
  and `LinYangPrinted.qmHauptmodul_of_printed : IgusaThetaExpressions → LinYangEx29 → PkgI1.QMHauptmodul`.
  §0 = theta-glue ThetaGlue.lean l.392-470, 534-551, 578-597 copied by `sed -n` (byte-identical), same namespace.
  Glue proved in the file: analyticity of each θ_m∘Ω on ℍ (copy of TailJ's inner step), countability of Γ*
  (B ≃ ℚ⁴), countable fibres of a Hauptmodul with orbit fibres, eqOn off a countable set (Set.Countable.dense_compl).
