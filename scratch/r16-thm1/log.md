# r16-thm1 results log (round 2 of r16-shimura73)

## Setup (10:45)
- Base: this worktree (wip/r16-shimura73, round 1 at 7544856cf; base bf691da22 leaf-fold33b, TailZ74). VERIFIED.
- heckeJ1DS, afShimura, afCharpolyDS965, igusaGL2DSGalSome are top fields of OpenResearchLeaves48 (TailZ74). VERIFIED (grep).
- AfShimura (AfTateLambda.lean:~640) asks IsAfQuotient (surjective, kills I_f J, universal) and IsAfAction
  (theta(a_p) = 1 (x) e_p, theta(chi(d)) = 1 (x) e_d). AfCharpolyDS965 takes IsAfQuotient/IsAfAction as hypotheses,
  so replacing afShimura must yield the full AfShimura statement. VERIFIED (read).

## Lean (VERIFIED, compiled 10:57)
- ZInQKernel/Contrib/OneProof/R16Thm1.lean: no errors, no warnings. lake build of the module: success.
- Axioms (scratch/r16-thm1/Axioms-output.txt): afShimura_of_shimura73, heckeJ1DS_of_bSh, euler_of_shimura73_li,
  r16CoreY_of_shimura73, isAfAction_of: [propext, Classical.choice, Quot.sound].
- New Props: ShimuraThm1Printed (LEAF, printed form as read; (iv), uniqueness, Gamma0 branch dropped),
  BShStandardModel (ON THE SPOT; = HeckeJ1DS statement), ShimuraQuotientIsAf (GLUE: Shimura's A is DS's J/I_f J).
- Proved: heckeJ1DS_of_bSh (by `h`), isAfAction_of (T_p from (ii) at n = p; <d> from (ii) at n = p^2 with
  xi_{p^2} = T_p^2 - p<p>, Dirichlet prime p = d mod N, a_p^2 - a_{p^2} = chi(p) p), afShimura_of_shimura73,
  euler_of_shimura73_li (Li + ConjNewform discharge the Fricke proviso), r16CoreY_of_shimura73.

## Finding: the read's (i)-(iii) do not give DS's J/I_f J
- (ii)-(iv) are invariant under composing nu with an isogeny, so (A, nu) is pinned only if "quotient" means
  connected kernel (rendered KerConnected). Even then IsAfQuotient needs ker nu = I_f J, i.e.
  dim J/I_f J <= [K_f : Q] (multiplicity one). Named as glue ShimuraQuotientIsAf. SPECULATIVE whether the
  printed uniqueness clause states A = J/I_f J (not in the read note).

## Fold (VERIFIED, 11:10)
- scratch/r16-thm1/autofold.json: discharges heckeJ1DS (heckeJ1DS_of_bSh; leaf bShStandardModel) and afShimura
  (afShimura_of_shimura73; leaves shimuraThm1Printed, shimuraQuotientIsAf). No generation step (both are top fields).
- Dry run (in the worktree; --dry-run writes nothing, git status clean outside scratch):
  `strict count: 4/27 on 31 -> 4/28 on 32; strictest 4/27 -> 4/28` (needs --allow-rise; +1 GLUE).
- FoldCheck.lean (dry-run module, line 1 stripped): compiles; sixContactMin_of_open68 standard axioms.
- #discharges (DischargesCheck-output.txt): afShimura by R16Thm1.afShimura_of_shimura73 (still assumes
  ShimuraThm1Printed, ShimuraQuotientIsAf); heckeJ1DS by R16Thm1.heckeJ1DS_of_bSh (still assumes BShStandardModel).

## kinds rows (VERIFIED, 11:15): real autofold on a git-archive copy in /tmp (worktree untouched); diff in
  kinds-diff.txt: -afShimura, -heckeJ1DS, +bShStandardModel, +shimuraQuotientIsAf, +shimuraThm1Printed (all GLUE).
  render_open --check there: only "OpenStatements not regenerated" (needs Lean build).
## Report docs/research/r16-thm1.md written (Manuscript check, Known issues incl. Shimura misprint a_n^sigma f).
