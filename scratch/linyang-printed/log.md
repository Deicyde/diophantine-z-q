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
- EisDev.lean (imports LPrefix only; development copy of §6) COMPILES (VERIFIED): `spFactor_ne_zero`
  (det(CΩ+D) ≠ 0 on 𝔥₂, from ω((Wv,Xv),(Wv,Xv)) = 2i·v̄ᵀ(Im Ω)v), `spAct_mem` (Sp4(ℤ) preserves 𝔥₂: symmetry from
  the bilinear invariance, Im(MΩ) > 0 from the hermitian one), `spFactor_mul` (cocycle), `rightEquiv`
  (c ↦ c·M on Γ∞\Sp4(ℤ)), `spFactor_botRel` (summand independent of the representative, even k),
  `siegelEis_modular` (ψ_k(MΩ) = det(CΩ+D)^k ψ_k(Ω), even k; tsum reindexing, no convergence needed).
  Axioms [propext, Classical.choice, Quot.sound].
- LinYangPrinted.lean now imports TailU and uses the kernel's `QMSplit.Theta.IgusaPsi4`, `IgusaChi10` directly.
  COMPILES (VERIFIED, 12 s; LinYangPrinted.out): all of the above plus §8
  `igusaPsi4_of_printed : IgusaThetaExpressions → QMSplit.Theta.IgusaPsi4`,
  `igusaChi10_of_printed : IgusaThetaExpressions → QMSplit.Theta.IgusaChi10`,
  `thetaModularity_of_printed : IgusaThetaExpressions → PkgI1.ThetaModularity`; 7 `#print axioms` lines standard.
- LinYangPrintedChain.lean (= LinYangPrinted.lean with import TailZ19 and §9) COMPILES (VERIFIED, 13 s;
  LinYangPrintedChain.out): `HDec.HSyn.OpenResearchLeaves12P` (31 fields: leaf-fold12's 32 with igusaPsi4,
  igusaChi10 replaced by igusaThetaExpressions, text otherwise verbatim from TailZ19),
  `researchLeaves12_of_P : OpenResearchLeaves12P → OpenResearchLeaves12`,
  `sixContactMin_of_open15P : OpenResearchLeaves12P → OpenTextbookLeaves10 → OpenAddedLeaves11 → OpenGlue7 →
  ZInQ.SixContactMin`, standard axioms. Caveat: compiled with `lake env lean` against the olean tree copied from
  ~/dzq-check2 (29885092); its TailY, TailZ7, TailZ14, TailZ15 differ from b5ff0474 only in docstrings
  (VERIFIED by `git diff`: no def/theorem/structure/field line changed), TailZ19 and every bundle file identical.
- gap-triage's note (VERIFIED by reading TailJ/TailO/TailZ2/TailK/TailZ4/TailO): the fields igusaPsi4, igusaChi10
  enter only through `QMSplit.Theta.thetaModularity_of` (r4 = ThetaModularity), and r4 is used only by
  `s8WeightExact_of` / `s20WeightExact_of` (via `g8Auto_g4/g6`, `g20Auto_g4/g6`: `g8Auto_gen hT g _ M4 ...`,
  `... M6 ...`), whose callers are `qmDenZeroCM3_of_leaves4` (TailK l.317), `base2_of_base3` (TailO l.2779, 2967)
  and `qmHauptmodulBase3_of_leaves` (TailZ4 l.235, through TailZ2's auto8/auto20). So: only at M4, M6, along Ω(z).
  Route 1 as theta-split/igusa-alg stated it (LinYangThetaCurve) does NOT remove them (FibreQMPeriod still needs
  qmHauptmodul and qmDenZeroCM3, which use r4). With the printed leaves they become theorems
  (igusaPsi4_of_printed, igusaChi10_of_printed), for all M ∈ Sp4(ℤ), not just M4, M6.
- jTuple_of_sForm (s-form relations + Igusa/Lin-Yang conversion (13)-(14) ⇒ R3's LinYangTuple J-tuple with t = −s3/(12 j s2), j ≠ 0, s2 ≠ 0) PROVED in both files (VERIFIED compile: LinYangPrinted.out 8 axiom lines, LinYangPrintedChain.out 10, all standard).
- LinYangPrintedFull.lean = igusa-alg's IgusaAlg.lean (c9360203, verbatim, import raised TailA → TailZ19) +
  LinYangPrintedChain.lean minus its §0 (theta-glue's definitions are in igusa-alg's verbatim ThetaGlue body) + §10.
  COMPILES (VERIFIED, `lake env lean`, 1 min 45 s, peak 13.4 GB, 0 errors, no sorry; 16 `#print axioms` lines all
  [propext, Classical.choice, Quot.sound]; LinYangPrintedFull.out):
  `IgusaAlgFinal.thetaRatiosAtQM_of_printed : IgusaThetaExpressions → LinYangEx29 → ThetaRatiosAtQM`,
  `IgusaAlgFinal.thetaPointOfFibre_of_printed : FibreQMPeriod → IgusaThetaExpressions → LinYangEx29 → ThetaPointOfFibre`,
  `IgusaAlgFinal.thetaPointOfFibre_of_printedAll : FibreQMPeriod → PkgI1.QMHauptmodul → IgusaThetaExpressions →
  LinYangEx29All → ThetaPointOfFibre`, plus everything of LinYangPrintedChain.lean.
- Strict variant: `LinYangEx29All` (∀ Hauptmodul j6 with the clauses → relations; no existence claim);
  `linYangEx29_of_all : LinYangEx29All → PkgI1.QMHauptmodul → LinYangEx29`,
  `linYangThetaCurve_of_printedAll : IgusaThetaExpressions → LinYangEx29All → QMHauptmodul → LinYangThetaCurve`
  (VERIFIED compile in all three files: 9, 11, 16 axiom lines, all standard).
