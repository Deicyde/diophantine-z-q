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
