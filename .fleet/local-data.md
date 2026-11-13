# local-data (2026-11-13)

**Verdict.** `G15Ram.LocalData p r` (scratch/g15-ram), copied verbatim, is a predicate on a
bare `r : GaloisRep ℓ 2`, so it cannot be proved for arbitrary `r`. Compiled:
`localData_large_iff` shows that at `p > D` it is equivalent to "`r` kills wild inertia", which
fails for `ψ ⊕ 1` with `ψ` of conductor `p²` (STANDARD). The corrected statement is about G8's
`r`, which is a Lean object (`G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r`).

**Main result (compiled, no sorry, standard axioms).**
- `G15Ram.localData_of_g7 : G8Out A ℓ (rho Tm a β) r → G7Clauses β ε L → LocalGlue p Tm a β L →
  LocalData p r`, for every prime `p`.
- `g15RamG_of_g7` composes it into g15-ram's `G15RamG D u`.

**What remains: four named glue Props, none a leaf.**
- `G7Clauses`: G4/G7 clauses moved from g0-mod-field's `ℂ^×`-valued data to g0-mod-galois's
  `ℚ̄_ℓ` data.
- `TorsionFieldWild` (`p ≤ D`): R6 + D2 + `A[m] ≅ (ℤ/m)⁴` + the descent datum on `G_L`.
- `TateWildTrivialL` (`p > D`): G3 + Néron–Ogg–Shafarevich + the descent datum.
- `BetaUpper` at `p = 2`: T16 + D3 + Herbrand.

**What the `β`-side and the field theory now need.**
- At odd `p`, the whole `β`-side is proved: `β² = χ` is trivial on wild inertia, because wild
  inertia fixes `μ_n` for `p² ∤ n`.
- The field-degree facts are proved:
  - `[L_v:ℚ_p] ≤ [L:ℚ]`;
  - wild inertia fixes any `E` with `[E:ℚ_p] < p`;
  - the Galois closure of `E` has `e ≤ [E:ℚ_p]!`.

**Findings.**
- F2: g15-ram §3's claim that G8's `r` is not in Lean is superseded.
- F3: g0-mod-field's `G7Data`/`AfterG7` drop `[L:ℚ] ≤ D`, which G15 needs; it is a one-line fix
  in `g7OutUnr_of_g4Out`.
- F4: the Tate glue is false at `p = ℓ` and is used only at `p ≠ ℓ`.
- F5: the two `β`'s (`ℂ^×` and `ℚ̄_ℓ`) are not connected in Lean.

**Tail (compiled).** `scratch/local-data/Tail.lean` proves `G0ModNewform.modularConstituent_tail_L`:
g0-mod-newform's tail with `G15RamG D u` replaced by "`D.r5` and `D.r3` come from G8 on G7's data,
with the glue at each prime" (`G8LocalPack`) together with G11's output. It has no sorry and only
the standard axioms.

**Files.** `scratch/local-data/LocalData.lean`, built by `build.sh`; check with
`lake env lean scratch/local-data/LocalData.lean`. 27 declarations, all
`[propext, Classical.choice, Quot.sound]`. Report: `docs/research/local-data.md`. Log:
`scratch/local-data/log.md`.
