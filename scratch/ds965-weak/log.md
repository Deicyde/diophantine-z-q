# ds965-weak results log

## Statements
- Target: `ZInQ.Contrib.HodgeSplit.DSThm965` (ZInQKernel/OneProof/H/TailS.lean l.1110), bundle field
  `HDec.HSyn.OpenResearchLeaves22.dsThm965`. Verbatim copy `DSThm965Copy` in Check.lean,
  `DSThm965Copy = DSThm965 := rfl` compiles (VERIFIED).
- New leaf `DS965Weak.DSThm965Weak`: DSThm965 with conclusion `aeval (ρ.mat σ) (X^2 - C(ιL α) X + C(ιL β)) = 0`
  ("ρ(Frob) satisfies the polynomial") in place of `charpoly = ...`.

## Compile outcomes (11-15)
- 23:10 scratch/ds965-weak/DSThm965Weak.lean: compiles, no errors (lake env lean, ~1.5 min). VERIFIED.
- 23:14 scratch/ds965-weak/Check.lean (same + verbatim copy + #print axioms): `dsThm965_of_weak` and
  `dsThm965Weak_of_dsThm965` depend on [propext, Classical.choice, Quot.sound]. VERIFIED.

## Findings
- `dsThm965_of_weak : DSThm965Weak → DSThm965` proved with no further leaf; glue = kernel T18
  (`frobeniusDense_C9`), hodge-split's `eps0`/`cycQ` (Mathlib cyclotomic characters), new inertia lemmas
  (`eps0_inertia`, `cycQ_inertia`). VERIFIED (compiled).
- `dsThm965Weak_of_dsThm965 : DSThm965 → DSThm965Weak` (Cayley–Hamilton): the weak leaf is never stronger. VERIFIED.
- Math: the scalar case (every ρ(σ) scalar) is handled by replacing ρ with diag(ψ₀, ε₀χ_ℓ^{k−1}ψ₀⁻¹); no
  determinant leaf needed. Non-scalar case: det ρ = ε₀χ_ℓ^{k−1} by Chebotarev on the open non-scalar locus.
- 23:11 `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.DSThm965Weak`:
  success, 0 errors (build tree copied from ~/dzq-wt/unif-printed, partial rebuild). VERIFIED.
- 23:12 #discharges (scratch/ds965-weak/Discharges.lean, output discharges.out):
  `DISCHARGES [OpenResearchLeaves22.dsThm965] by DS965Weak.dsThm965_of_weak`
  `still assumes: [DS965Weak.DSThm965Weak]`, `axioms: [propext, Classical.choice, Quot.sound]`;
  "#discharges: 62 open hypotheses, 2165 theorems checked, 8 discharge one". VERIFIED.
- autofold dry run (scratch/ds965-weak/autofold.json): "strict count: 45/11 on 56 -> 45/11 on 56; strictest 43/13 -> 44/12".
  Output minus line 1 = FoldDryRun.lean compiles; `HDec.HSyn.sixContactMin_of_open30` axioms standard. VERIFIED.
- R16Used.AfTateCharPoly: steps 1-3 transfer componentwise (SPECULATIVE, not formalized); scalar case does not
  (the representation is the Tate module of the existential A, cannot be replaced). Residual reading risk remains.
