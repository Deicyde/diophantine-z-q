# local-data results log

## Step 1 (2026-11-13 05:50-06:30 PST): statements and findings
- Target: `G15Ram.LocalData p r` (scratch/g15-ram/G15Ram.lean l.177), with `SmallPrimeData`,
  `LargePrimeData`, `TwistShape`, `TwistUpper`, `TwistTame`, `U0`, `ModData`.
  Copied verbatim (whole lines 8-718 of G15Ram.lean, via `build.sh`) into
  `scratch/local-data/LocalData.lean`.
- Finding F1 (logical; VERIFIED by reading the definitions): `LocalData p r` is a predicate on a
  bare `r : GaloisRep ℓ 2`. At `p > D` it is equivalent to "r is trivial on wild inertia"
  (to be compiled: `largePrimeData_iff`), so it fails for `r = ψ ⊕ 1` with `ψ` a Dirichlet
  character of conductor `p²` (wildly ramified at `p`; STANDARD, Serre *Local Fields* IV §4,
  cyclotomic ramification groups; not formalized). Not provable as a closed statement.
- Finding F2 (VERIFIED, read): G8's construction of `r` IS a Lean object:
  `G0Galois.G8Out A ℓ ρ r` (scratch/g0-mod-galois/part_galois.lean l.147) with
  `ρ = GlueDescent.rho Tm a β` (ZInQKernel/HDecomp/Descent/ProjRep.lean l.102) from
  `G0Galois.G7Out` (l.121). g15-ram §3 ("G8's construction of `r_ℓ` is not a Lean object") is
  superseded: `TwistShape` can be moved from `r` to G7's data.
- Finding F3 (VERIFIED, read): g0-mod-field's interface `G7Data`/`AfterG7`
  (scratch/g0-mod-field/ModField.lean l.611, 812) does not carry `[L:ℚ] ≤ D` (only `G4Out`
  does). G15 at `p ≤ D` needs `[L_v:ℚ_p] ≤ D` for `e(F) ≤ (DG₀)!`; it can be recovered from
  `IsQMModel` (A is a base change from the fibre field `K`, `[K:ℚ] ≤ 324!`) only if the
  local Galois-closure bound is redone over `K` (SPECULATIVE). To be reported.
- `lake build` of the 7 kernel modules needed (HDecomp not prebuilt in this worktree): started.
