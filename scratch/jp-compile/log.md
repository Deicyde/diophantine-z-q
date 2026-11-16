# jp-compile results log

Base: origin/work/h10-jones-pall-40944c0a a9bc2e35 (draft fork PR #38), origin/main 0caafe66 merged (STATUS.md only;
Main.lean unchanged from 2880fef1). Toolchain Lean 4.35.0, Mathlib v4.35.0.

## Target
`hJP : ZInQ.Contrib.TYZDecomp.H29Split.JonesPallX2Y2Z16` (ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean:610):
`∀ n : ℕ, Squarefree n → n % 8 = 1 → ∃ x y z : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 + 16 * z ^ 2`.
Claimed proof: `ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof` (ZInQKernel/Contrib/OneProof/JonesPall.lean).

## Outcomes (all VERIFIED, compiled 2026-11-16)
1. `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.JonesPall`:
   success, 13704 jobs; PR modules Atlas 18 s, Quaternion 20 s, Descent 4.6 s, Parity 6.7 s, Representation 12 s,
   JonesPall 36 s. Only warnings: Mathlib "designed for the module system" import notices. No technical fix needed;
   no file under ZInQKernel/ changed by this task. (build-excerpt.txt)
2. `#discharges` (Discharges.lean, output Discharges-output.txt):
   `DISCHARGES [hJP] by ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof / still assumes: [] /
   axioms: [propext, Classical.choice, Quot.sound]`; 56 open hypotheses, 3047 theorems checked.
3. Type vs binder: MetaM check on `frozenTarget`'s binder `hJP`: syntactically equal (`==`) and defeq to the
   proof's type; `rfl` example and the named-argument application `frozenTarget r t l g (hJP := jonesPall_proof)`
   elaborate.
4. `#print axioms` jonesPall_proof, jonesPall_representation: [propext, Classical.choice, Quot.sound]
   (no Lean.ofReduceBool, so no native_decide anywhere in the closure).
5. FoldCheck.lean (main's Main.lean body, binder hJP dropped, proof passed): compiles; `frozenTarget` standard
   axioms; `#check` shows the signature without `JonesPallX2Y2Z16` (FoldCheck-output.txt).
6. autofold.py --dry-run on autofold.json: `autofold: not a field of the current bundles: ['hJP']` (expected:
   autofold folds bundle fields only; the fold of a frozenTarget argument is manual = FoldCheck.lean).
7. Source scan of the 6 PR .lean files: no #eval/run_cmd/initialize/syntax/notation/macro/elab/axiom/sorry/
   native_decide/implemented_by/extern/set_option; `decide` only on small closed residue goals.
   Atlas.lean uses `module`/`public import`/`@[expose] public section` (module system, no build-time code).
8. Diff vs origin/main: additions only (10 files under ZInQKernel/Contrib/OneProof/{JonesPall,LegendreThreeSquares}).
9. LegendreThreeSquares/{Atlas.lean,LICENSE,NOTICE.md} blobs equal those at PR #36 head 47ca4df2 and on
   origin/wip/leaf-fold32b (b0355816, 010649b7, 2960f767). TYZLemma29Mod2.lean blob identical on leaf-fold32b.
   leaf-fold32b's Main keeps binder `hJP` with the same type. A fold over leaf-fold32b's Main: UNCHECKED (no built
   tree of that branch; the change is the same one-line substitution plus the import).

## New leaves
None. The proof uses Mathlib and the in-PR port of atlas-lean's Legendre three-square proof only.
