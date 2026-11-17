# nv-local (2026-11-15, final)

**Verdict.** `SGRDirect.NVLocalInertia` (sgr-direct's one open Prop of route NV) is not proved outright. It is
proved in Lean, with standard axioms, from one strictly smaller GLUE Prop, `SGRDirect.NVLocal.TameBranchNormal`.
That Prop is general commutative algebra with no project definitions:
- *Hypotheses.* `R_m` is a regular local ring of dimension 2 with `m = (f, g)` and residue characteristic `p`.
  `L/Frac R` is Galois of degree `< p` and unramified off `fg = 0` near `m`.
- *Conclusion.* At every closed point of the normalization, the branch of `f = 0` is unique and normal.

`NVLocalInertia` is true as stated; no statement changed.

**What compiles** (`ZInQKernel/Contrib/OneProof/SGRDirectNVLocal.lean`, about 1000 lines; `lake build` OK;
`#discharges`: 63 open, 1923 checked, 7 discharge one, none from this file, as expected):
- `nvLocalInertia_of_branchRegular`: the Galois and arithmetic half of h-b1 step 3. It covers going up to a closed
  point, the unique branch, `τ` acting on the residue number field inside the inertia of an unramified prime, and
  hence `τ ∈ I_Q`.
- `branchRegular_of_tame`: the translation from `ℤ[X]`. It covers Gauss's lemma, `m = (dX − a, p)`, `B` as a
  localization of `C`, the transport of the ramification index, and unramifiedness from `BranchData`.
- `exists_branch`: going down.
- `heckeVertWitness_of_tame`: `HeckeVertWitness` from the bundle fields `r1r2`, `t5`, `qmAutCard`,
  `serreRigidity3`, `alFixedPoints`, `elkiesX6StarPrinted` plus `TameBranchNormal`.

**Fold** (`scratch/nv-local/autofold.json`, not executed): as sgr-direct's bypass, with the new field
`tameBranchNormal` (project glue, GLUE) in place of `nvLocalInertia`. GLUE −1, the same as sgr-direct's plan.

**What remains.** `TameBranchNormal`, via Abhyankar's lemma in dimension 2: a Kummer base change, T2 at both
divisors, purity (proved), specialization to a DVR, and descent by going down and the Reynolds operator. The
paper proof is in `docs/research/nv-local.md` §2.3; the Lean is estimated at several thousand lines.
Report: `docs/research/nv-local.md`.
