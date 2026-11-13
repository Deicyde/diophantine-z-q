# g0-mod-newform results log

Base: 883c4ddf (wip/integrate-w35c). Split.lean's `ModularConstituent` read from
origin/wip/g0-split (c20fa62b), `scratch/g0-split/part_split.lean`, not merged.

## Files
- `part_c9_src.lean`, `part_e1_src.lean`: verbatim copies of scratch/c9-rhof/C9.lean and
  scratch/e1-sub/E1Sub.lean.
- `part_new.lean`: the new section (namespace `G0ModNewform`, ~700 lines).
- `build.sh`: assembles `NewForm.lean` = kernel imports + C9 body + E1Sub body + part_new.
- `compile.out`: last compiler output.

## Compile outcomes (`lake env lean scratch/g0-mod-newform/NewForm.lean`)
- run1 02:01: kernel oleans missing; `lake build` of the 7 imported modules (6m41s, OK).
- run2: 13 errors, `GQp` unknown under `open LadicCond` (fixed: `open PkgI4 (GQp)`).
- run3 02:04: 0 errors; 11 `#print axioms` all `[propext, Classical.choice, Quot.sound]`.
- run4-7: §7b (G15 from ramification). Errors: `heightD_pos` not imported; `maxRecDepth` from
  `nlinarith`/`norm_cast` on the cast of `10 * x^2` (fixed with `Nat.cast_mul, Nat.cast_pow; rfl`).
- run8 02:1x: exit 0, no error, no `sorry`; 14 `#print axioms` all
  `[propext, Classical.choice, Quot.sound]` (VERIFIED). ~30 s per run.

## Statements (all VERIFIED compiled)
- `G12Spec D` (interface with g0-mod-galois): `r₅`, `r₃` irreducible; constituents of `V₅(A)`,
  `V₃(A)` on `G_{L'}` (`IsConstituentOf`); `PanOutput` for `r₅` (weight-2 eigenform up to a
  Dirichlet twist at Frobenius).
- `g13`: `G12Spec D` → newform `f`, level `N > 0`, `r₅` attached to `f` outside a finite set,
  and `∀ J, IsJ1 N J → CommonConstituent A (J_{L'})`. Leaves: T24, T25, R16, R9a, R9b, I3.M0,
  T18, T19.
- `g14`: + `G14TraceCompat D` (open) → `r₅`, `r₃` equivariantly isomorphic to R14's semisimple
  `ρ` attached to `f` (`AttachedTo`). Leaves: R14, T18, T19.
- `g15`: + `G15LocalBounds D u` → exponents of `N`. Leaf R17 (`CarayolR17'`), glue
  `SwanIndependent`. Uses proved invariance of `condAt` and adaptedness under isomorphism.
- `g15LocalBounds_of_ram`: `G15Ram D u` (open; ramification form) → `G15LocalBounds D u`, from
  glue `SwanIntegral` (L8) and `AdaptedExists`; `2(1+U₀) ≤ E₀` proved.
- `g16`: `N ≤ Q_D M²` (`GlueConductor.level_le`, `Mult.le_heightD_of_mem_S_mul`).
- `g13_g16`, `g13_g16_ram`, `modularConstituent_tail` (+ T33 `JacobianExists`, glue target
  `X1ModelExists` for a `J₁(N)`).

## Findings
- F1 (VERIFIED, logical): a constituent `U ⊆ V_ℓ(A)` determines `r_ℓ` only on `G_{L'}`; so the
  compatibility of `r₃`, `r₅` (G14) and their local ramification (G15) are statements about the
  `r_ℓ` *constructed* in G8 from G7's descent data, not about arbitrary constituents. Stated
  universally over constituents they would be false (twist by a character of `Gal(L'/ℚ)`).
  Hence `G14TraceCompat D`, `G15Ram D u` are hypotheses on the same data `D` as `G12Spec D`.
- F2 (VERIFIED): `GlueAssembly.one_le_heightD_real`, `ZInQ.Mult.le_heightD_of_mem_S_mul` give
  `GlueConductor.level_le`'s side conditions for `R = D`, `S = S_mul`.
- F3 (VERIFIED): `PkgI4.decomp p` is continuous (`Field.absoluteGaloisGroup.map` is `→ₜ*`), so
  `r.restrictLocal p` is continuous with no new hypothesis.
- F4 (VERIFIED): the twist bookkeeping of `C9Rhof.c9_r5` and the `A_f` of R16 must be taken from
  one application of R16 (c9 and E1Sub each obtain their own `A_f`); `commonConstituent_of_attached`
  uses one `A_f` for both the Brauer–Nesbitt isomorphism (`c9_core`) and the `J`-side (`jSide`).
