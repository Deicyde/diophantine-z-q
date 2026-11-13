# local-data results log

## Step 1 (2026-11-13 05:50-05:58 PST): statements and findings
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

## Step 2 (05:58-06:04 PST): reduction compiled
- `LocalData.lean` = verbatim G15Ram.lean 8-1384 + verbatim part_galois defs (`resQ`, `Vb`, `tate`,
  `Intertwines`, `G7Out`, `G8Out`) + `part_local.lean` (§4, new). Needed a one-time
  `lake build` of 7 HDecomp modules and `ZInQKernel.Multiplication.Certificate.Constants`
  (builds the upstream `lean/` package `z_in_q`).
- Compile (VERIFIED): `lake env lean scratch/local-data/LocalData.lean` exit 0, 0 errors, no
  sorry, ~55 s; `#print axioms` = [propext, Classical.choice, Quot.sound] for
  `largePrimeData_iff`, `localData_large_iff`, `mat_eq_scalar_of_intertwines`,
  `twistShape_of_g8`, `localData_of_g8`, `betaTame_of_odd`, `g15RamG_of_g8`,
  `betaOpen_of_isLocallyConstant`, `g7LocalData_of_odd` (output: compile.out).
- Statements proved:
  * `largePrimeData_iff r : LargePrimeData p r ↔ ∀ σ ∈ wildSet, r.restrictLocal p σ = 1`;
    `localData_large_iff` (p > D): `LocalData p r ↔` the same. (F1 made precise.)
  * `localData_of_g8 : G8Out A ℓ (rho Tm a β) r → G7LocalData p Tm a β → LocalData p r`.
  * `g15RamG_of_g8`: `G15RamG D u` from G8Out for `D.r5`, `D.r3`, `G7LocalData` at every
    `p ≠ 5` (ℓ = 5) and at `p = 5` (ℓ = 3), and G11Out.
  * `betaTame_of_odd (p ≠ 2) : BetaCharOn β F → BetaSqWild β F → BetaOpen β → BetaTame β F`
    (wild σ: σ^{p^a} fixes F' via `fix_of_wild_pow`; β(σ)^{p^a} = 1 = β(σ)²).
  * `betaOpen_of_isLocallyConstant : IsLocallyConstant β → β 1 = 1 → BetaOpen β`
    (continuity of `Field.absoluteGaloisGroup.map`, `krullTopology_mem_nhds_one_iff`,
    normal closure).
  * `g7LocalData_of_odd (p ≠ 2) : IsLocallyConstant β → β 1 ≠ 0 → G7LocalDataOdd p Tm a β →
    G7LocalData p Tm a β`.
- Named glue Props left: `TateWildTrivial` (G4/G7 descent on G_L + R6 + D2; G3 + NOS at p > D),
  `BetaUpper` at p = 2 (T16 + D3), `BetaCharOn` (∂β = ε, ε inflated from Gal(L/ℚ)),
  `BetaSqWild` (β² = χ, χ tame at odd p), the e-bound / tameness of F (field degrees).

## Step 3 (06:05-06:20 PST): β² = χ is trivial on wild inertia at odd p
- New imports `ZInQKernel.HDecomp.Descent.B2Glue`, `…Chi` (lake build of both, once).
- Proved (VERIFIED, compiled, axioms standard): `wild_fix_root` (σ ∈ wildSet, ζⁿ = 1,
  p² ∤ n ⇒ σζ = ζ; via `wild_fix_prime_to_p`: m = ∑(1 − ηⁱ) has norm < 1 if η ≠ 1, and
  `wild_fix_p_root`: x = ζ − 1 and ζ = ηⁱ); `decomp_spec` (embP ∘ decomp σ = σ ∘ embP);
  `cyc_decomp_wild` (`GlueDescent.B2Q.cyc N (decomp p σ) = 1` for p² ∤ N);
  `galChar_decomp_wild`; `not_sq_dvd_chiLevel` (p odd, T₋ primes ⇒ p² ∤ chiLevel T₋);
  `betaSqWild_of_chi` (BetaSqWild from β² = ι ∘ galChar χ on G_F, χ mod chiLevel T₋).
- Compile: exit 0, 0 errors, no sorry (~60 s).
