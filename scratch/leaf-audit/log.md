# leaf-audit log (results only)

## Setup (2026-11-15 06:20-06:30)
- Worktree at 43513d87 (leaf-fold25). Merged origin/wip/{theta-fold, elkies-coord, r17-bypass, h29-ne3, qmrec-printed,
  pb-bypass, faltings-cm, sir-printed, gz-heegner, gz-weil}. Only conflicts: theta-fold vs leaf-fold25 in
  ZInQKernel/OneProof/Main.lean and generated docs (STATUS.md, docs/one-proof/*, scratch/contrib-kit/DischargesTest-output.txt);
  resolved to leaf-fold25's side (Main.lean still imports TailZ35, not theta-fold's TailZ41). The integrator must redo
  theta-fold's Main edit on top of leaf-fold25. MumfordGroupLaw (leaf-fold23) is already in the base.
- Build tree copied from ~/dzq-check2 (bc90deac). h29-ne3's leaves exist only in scratch/h29-ne3/TYZLemma29Mod2.lean
  (drop-in for the Contrib file): copied verbatim to ZInQKernel/Contrib/OneProof/LeafAudit1115H29.lean (helper module).

## Leaf statements read (definitions located)
| leaf | file:line |
|---|---|
| ElkiesX6StarFunctionField | ZInQKernel/Contrib/OneProof/ElkiesX6StarPrinted.lean:814 |
| IgusaThetaExpressions | ZInQKernel/Contrib/OneProof/LinYangPrinted.lean:96 |
| LinYangEx29All | ZInQKernel/Contrib/OneProof/LinYangPrinted.lean:397 |
| MumfordGroupLaw | ZInQKernel/Contrib/OneProof/MumfordRigidity.lean:82 |
| NewformRepConductor | ZInQKernel/Contrib/OneProof/CarayolLevel.lean:230 |
| TYZLemma29PrintedNe3, TYZThm21At31 | scratch/h29-ne3/TYZLemma29Mod2.lean:455,474 |
| MainTheoremCM | ZInQKernel/Contrib/OneProof/QMRecPrinted.lean:135 |
| PanPrinted, BergerPrinted | ZInQKernel/Contrib/OneProof/PanBerger.lean:478,489 |
| FaltingsTateSurj | ZInQKernel/Contrib/OneProof/FaltingsTateSurj.lean:37 |
| ShimuraIntegralModelUsed | ZInQKernel/Contrib/OneProof/ShimuraIntegralModelUsed.lean:78 |
| X0ModuliGaloisMero | ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Heegner.lean:503 |
| GrossZagierFormulaCd, GrossConjugationCd | ZInQKernel/Contrib/OneProof/GrossZagierHeegner/Cd.lean:39,43 |

## Finding 1: LinYangEx29All is false (SPECULATIVE until the Lean lemma compiles; numerics VERIFIED)
- Its premises on j6 (continuous, fibres = Gamma*-orbits, surjective, values 0, infty, -16/27 at the CM points) are
  invariant under j6 |-> conj o j6 (complex conjugation on the Riemann sphere fixes 0, infty, -16/27), but its conclusion
  s3^2 = z s2^3 is not. Applying the leaf to j6 and to conj o j6 gives (z - conj z) s2(Omega tau)^3 = 0.
- With IgusaThetaExpressions (s2 = psi4Th = thetaSum8/4) and QMHauptmodul (f = jNum/jDen o Omega where jDen != 0):
  j_theta(tau) = jNum/jDen(Omega tau) would be real wherever jDen(Omega tau) != 0.
- Numerics (scratch/leaf-audit/py/jtheta_nonreal.py, mpmath 40 digits, Lean definitions transcribed; VERIFIED):
  j_theta(0.3+1.1i) = 4.27317158561753 - 0.683139858455891 i, |jDen| = 3.1e5; j_theta(0.1+0.9i) = -0.8183 + 0.7624 i;
  j_theta(-0.4+1.3i) = -10.628 + 16.718 i. Validation: j_theta(sqrt2+i) = 0 (1e-162), j_theta(i sqrt(9+6 sqrt2)) =
  -0.592592592592593 = -16/27, pole at i sqrt3 (|jDen| = 3e-197), matching pkg-I1's values.
- COMPILED (scratch/leaf-audit/T1.lean, lake env lean, standard axioms):
  `linYangEx29All_conj` (leaf applied to j6 and conjOP ∘ j6 gives (z - conj z) * lyS2(Ω τ)^3 = 0),
  `jtheta_real_of_leaves : IgusaThetaExpressions → LinYangEx29All → QMHauptmodul → ∀ τ, jDen(Ωτ) ≠ 0 → im(jNum/jDen) = 0`,
  `not_linYangEx29All : IgusaThetaExpressions → QMHauptmodul → (∃ τ, jDen ≠ 0 ∧ im(jNum/jDen) ≠ 0) → ¬ LinYangEx29All`.
  The existential `LinYangEx29` feeds the consumer directly: `IgusaAlgFinal.thetaRatiosAtQM_of_printed hI hL` (checked).
  VERDICT LinYangEx29All: FALSE as stated (missing holomorphy of j6). Correction: use the existential `LinYangEx29`
  (theta-fold's own def) or add a premise pinning j6 (e.g. holomorphy where finite).

## Audit module (VERIFIED: compiled)
- `ZInQKernel/Contrib/OneProof/LeafAudit1115.lean` builds (`lake build ZInQKernel.Contrib.OneProof.LeafAudit1115`,
  12964 jobs; output scratch/leaf-audit/build-LeafAudit1115-output.txt); all new theorems use [propext, Classical.choice, Quot.sound].
  Contents: LinYang refutation; Elkies ff-premises from charts; MumfordGroupLaw premises + conclusion at the trivial
  family Spec Q -> Spec Q (zero abelian variety fibres); FaltingsTateSurj at A = B = 0; TYZ premises from sibling
  leaves (n = 3, 11) and `printed_iff : TYZLemma29Printed ↔ TYZLemma29PrintedNe3 ∧ TYZThm21At31`;
  X0ModuliGaloisMero premises at N = 1, g = 1, tau = tau' = i (j(i) = 1728 algebraic, via gz-weil's squarePP g3 = 0);
  examples pinning every old/new implication (Elkies, Mumford, Faltings, Carayol, QMRec, PanBerger, SIR, X0, GZ).
- Corrected theta-fold top compiles: scratch/leaf-audit/FoldFix.lean `sixContactMin_of_open29_fixed` (field
  `LinYangEx29` instead of `LinYangEx29All`; hθ := fun _ => thetaRatiosAtQM_of_printed hI hL), standard axioms.
- Integration finding (VERIFIED): with theta-fold merged onto leaf-fold25, `ZInQKernel/OneProof/H/TailZ35.lean` fails
  (line 117: type mismatch; `sixContactMin_of_open28` now takes `hθ`). Main of leaf-fold25 does not build with theta-fold.
- `#discharges` (scratch/leaf-audit/Discharges.lean, output discharges-output.txt) run against a temporary Main =
  theta-fold's Main + leaf-fold25's hFH edit (working tree only, restored afterwards): 64 open hypotheses, 3499
  theorems, 17 discharge one; the audit module adds no discharge (expected). r17, r11r12, elkiesX6StarPrinted, r9b,
  mumfordGroupLaw, h29, hL3, hX discharges by the 11-15 tasks' theorems are listed. `linYangEx29All` is an open
  hypothesis of that frozenTarget (and an open LEAF row in theta-fold's OPEN.md, elliotglazer #86).
- TYZ sanity: h29-fix's brandt.py re-run (pure Python): n = 3: Q(3) = f_3(1) = ±3 for all 8 tau, values {−3, 1};
  n = 11, 19: Q = ±1; matches 𝓛(3)^2 = 𝓛(11)^2 = 𝓛(19)^2 = 1 (lcalSq doc) with w_K(3) = 3, pairIdx 11 = pairIdx 19 = {1}.
- Corrected LinYangEx29 numerics (scratch/leaf-audit/py/linyang_check.py, psi6Th (60 terms) and chi12Th (15 terms)
  parsed from LinYangGlue.lean; VERIFIED): with j6 = j_theta, s3^2 = j s2^3, s5 = s2 s3, s6 = (j+1) s2^3 hold to
  relative error < 2e-39 at tau = 0.3+1.1i, 0.1+0.9i, -0.4+1.3i (at the D = -4 point sqrt2+i, s3 = 0, degenerate).
- GZ sanity (scratch/leaf-audit/py/gz_check.py, PARI 2.2.4 cypari2; VERIFIED): C_5 conductor 800, root number -1,
  D = -31 (2, 5 split; fundamental): L'(C_5,1) = 2.22737, L(C_5^D,1) = 3.36974, L'(E/K,1) = 7.50566 > 0; PARI's
  Heegner point [25/4, 75/8] in E(Q), height 1.89948 > 0: consistent with GrossZagierFormulaCd (kappa > 0) and
  GrossConjugationCd (epsilon = -1: sigma y - y torsion, y in E(Q) up to torsion).
- Elkies orientation (by hand, VERIFIED algebra): the chart cover {s^2 = -t, r^2 = 3(t-1)} is invariant under
  t' = 1/t (s' = s/t, r' = rs/t: s'^2 = -t', r'^2 = 3(t'-1)), which swaps t = 0 and t = infinity and fixes t = 1. So
  the leaf's truth does not depend on whether D = -24 or D = -3 sits at 0 (the unread 0/infinity orientation).
  Fibre fields: t = 1 gives Q(i) (only D = -4 fits), t = 0 and t = infinity give Q(sqrt -3) (D = -24: field of
  definition is the quadratic subfield of H_{-24} = Q(sqrt2, sqrt -3) other than K and Q(sqrt2); D = -3: Q(sqrt -3)).
- IgusaThetaExpressions, theta side on the diagonal (scratch/leaf-audit/py/igusa_diag_check.py; VERIFIED): at
  diag(0.1+1.2i, -0.3+0.9i) and diag(0.25+i, 0.4+1.5i): psi4Th = E4⊗E4 and psi6Th = E6⊗E6 (rel. err < 3e-30),
  chi10Th = 0 (< 5e-69), chi12Th = Δ⊗Δ (< 1e-29). With theta-glue's modularity of the theta expressions and the
  injectivity of the diagonal restriction on M_4, M_6, M_12 this pins psi4Th, psi6Th (sign pattern) and chi12Th;
  chi10Th's constant is pinned only by theta-fold's Fourier check (script not in the repository; not re-run).

## Final (2026-11-15)
- Report docs/research/leaf-audit.md, fleet note .fleet/leaf-audit.md. Deliverables committed.
