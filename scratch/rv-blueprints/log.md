# rv-blueprints results log

## 18:15-18:20 Compile audit (VERIFIED, compiled)
Each blueprint Lean file copied to `Audit_<name>.lean` with `audit_tail.lean` appended (an `elab`
command that runs `Lean.collectAxioms` on every declaration added by the file and reports any
axiom other than propext, Classical.choice, Quot.sound). Runner `run_audit.sh` (sequential, one
Lean process). Outputs in `audit_out/`.

| file | exit | errors | warnings | sorry | declarations audited | non-standard axioms |
| --- | --- | --- | --- | --- | --- | --- |
| bp-faltings/Hodge | 0 | 0 | 0 | 0 | 125 | none |
| bp-faltings/Models | 0 | 0 | 0 | 0 | 40 | none |
| bp-modcurves/Gamma1Genus | 0 | 0 | 0 | 0 | 44 | none |
| bp-modcurves/TateNormalForm | 0 | 0 | 0 | 0 | 12 | none |
| bp-modcurves/Jacobian | 0 | 0 | 0 | 0 | 38 | none |
| bp-modcurves/ModularCurveDefs | 0 | 0 | 0 | 0 | 20 | none |
| bp-modcurves/AnalyticModuli | 0 | 0 | 0 | 0 | 16 | none |
| bp-modcurves/PointTransport | 0 | 0 | 0 | 0 | 70 | none |
| bp-qmmoduli/QMOrder | 0 | 0 | 21 (linter) | 0 | 81 | none |
| bp-qmmoduli/Units72 | 0 | 0 | 0 | 0 | 7 | none |
| bp-qmmoduli/QMAbVar (imports ZInQKernel.HDecomp.A6.A6, prebuilt) | 0 | 0 | 9 (linter) | 0 | 176 | none |

Warnings are unused-tactic / deprecated `push_neg` linter warnings only.
(First run failed only in the appended audit command: a `MessageData` numeral typing slip,
fixed by `let mut n : Nat := 0`; the blueprint files themselves compiled in that run too.)

## 18:40 AT3 normalization check (VERIFIED, computed: at3_check.py, at3_check.out)
faltingsHeightEC(y^2 = x^3 + 1) by direct 2-d integration = -1.3211174284280; the eta-product
form -(1/12)log(|eta(rho)|^24 (Im rho)^6) - log 2pi gives the same to 19 digits. Deligne's
recalled minimum -0.74875248 (STANDARD, locator UNVERIFIED) minus (1/2)log pi = -1.3211174229
(agrees to the 8 digits of the recalled constant). So faltingsHeightEC is Faltings-normalized
and h_D = h_F + (1/2) log pi at g = 1.
