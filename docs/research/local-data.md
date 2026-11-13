# local-data: `LocalData p r` (g15-ram) on G8's representation

Task local-data, 2026-11-13. Lean: `scratch/local-data/LocalData.lean` (2536 lines). It is
assembled by `scratch/local-data/build.sh` from three pieces: a verbatim copy of
`scratch/g15-ram/G15Ram.lean` lines 8-1384, verbatim definitions from
`scratch/g0-mod-galois/part_galois.lean`, and the new part `scratch/local-data/part_local.lean`.
Log: `scratch/local-data/log.md`. Compiler output: `scratch/local-data/compile.out`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

**Verdict.** `LocalData p r`, copied verbatim from g15-ram, is a predicate on a bare
`r : GaloisRep ℓ 2`. It is false for general `r`, so it cannot be proved as a closed statement.
This is made precise and proved in Lean (VERIFIED):

```
theorem G15Ram.localData_large_iff (r : GaloisRep ℓ 2) (hp : (heightD : ℝ) < p) :
    LocalData p r ↔ ∀ σ ∈ wildSet, r.restrictLocal p σ = 1
```

So at `p > D`, `LocalData p r` says exactly that `r` kills wild inertia. It therefore fails for
`r = ψ ⊕ 1` whenever `ψ` is a Dirichlet character of conductor `p²` and order `p`. Such a `ψ` is
wildly ramified at `p`, since wild inertia maps onto `Gal(ℚ_p(ζ_{p²})/ℚ_p(ζ_p))` (STANDARD: Serre,
*Local Fields*, IV §4, cyclotomic extensions; the counterexample itself is not formalized).

**Corrected statement and main result (VERIFIED, compiled, standard axioms).** The `r` that G8
builds is a Lean object. It is `r` with `G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r`, where
the inputs `(Tm, a, β, ε)` are G7's data (`G0Galois.G7Out`). For this `r`, `LocalData p r` holds
at every prime `p`, given two named Props on G7's data:

```
theorem G15Ram.localData_of_g7 {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm : GQ → Module.End (PadicAlgCl ℓ) (G0Galois.Vb A ℓ)} {a β : GQ → PadicAlgCl ℓ}
    {ε : GQ → GQ → PadicAlgCl ℓ} {r : GaloisRep ℓ 2} {L : IntermediateField ℚ Qbar}
    (hG8 : G0Galois.G8Out A ℓ (GlueDescent.rho Tm a β) r)   -- G8's output (g0-mod-galois `g8`)
    (hC : G7Clauses β ε L)                                     -- clauses of G4/G7
    (hG : LocalGlue (p := p) Tm a β L) :                       -- the local glue at p
    LocalData p r

theorem G15Ram.g15RamG_of_g7 (D : ModData L A) (u : ℚ)
    (hG8₅ : G8Out A₅ 5 (rho Tm₅ a₅ β₅) D.r5) (hC₅ : G7Clauses β₅ ε₅ L₅)
    (hG₅ : ∀ p (hp : p.Prime), p ≠ 5 → @LocalGlue p ⟨hp⟩ 5 _ _ _ _ Tm₅ a₅ β₅ L₅)
    (hG8₃ : G8Out A₃ 3 (rho Tm₃ a₃ β₃) D.r3) (hC₃ : G7Clauses β₃ ε₃ L₃)
    (hG₃ : LocalGlue (p := 5) Tm₃ a₃ β₃ L₃)
    (h11₅ : G11Out T D.r5) (h11₃ : G11Out T D.r3) : G15RamG D u
```

`g15RamG_of_g7` composes `localData_of_g7` with g15-ram's `g15RamG_of_localData`. Its hypotheses
are therefore everything that G15 (clauses (i)-(iii)) still needs.

### The remaining named Props

Each is a `def … : Prop` in `part_local.lean` with a docstring naming its step and its source.
**None is a leaf.** The published inputs they rest on are leaves already in the bundles.

| Prop | where used | content | glue on (leaves in **bold**) |
|---|---|---|---|
| `G7Clauses β ε L` | all `p` | `L ⊆ ℚ̄` finite, `[L:ℚ] ≤ D`; `∂β = ε`; `β ≠ 0`; `β` locally constant; `β² = ι∘galChar χ` for a Dirichlet `χ` mod `chiLevel T₋`, `T₋` a set of primes; `ε = 1` on `G_L × G_L` | transport of g0-mod-field's `G4Out`/`G7Data`/`DescentDatum` (`ℂ^×`-valued) to g0-mod-galois's `ℚ̄_ℓ`-valued `G7Out`; no new mathematics |
| `TorsionFieldWild p Tm a L` | `p ≤ D` | some finite `E ⊇ L_v` with `[E:ℚ_p] ≤ G₀·[L_v:ℚ_p]` on which `a_σ·Tm σ = 1` for wild `σ ∈ G_E` | descent datum on `G_L` (`a_σμ_σ = 1`); `E = L_v(A[3])` (`A[5]` if `p = 3`); `A[m] ≅ (ℤ/m)⁴` (**I2-Tors** `PkgI2.TorsionStructure`), `|GL₄(𝔽₅)| = G₀`; **R6** `PkgI2.RaynaudCriterion`; D2 `PkgI2.D2_fixed_of_raynaud` (proved from R6); N5 L813-818 |
| `TateWildTrivialL p Tm a L` | `p > D` | `a_σ·Tm σ = 1` for wild `σ` with `decomp σ ∈ G_L` | descent datum on `G_L`; G3 (good reduction away from 3); **NOS** `PkgI2.NeronOggShafarevich` via `PkgI2.inertiaTrivial_of_goodReduction`; N5 L848-851 |
| `BetaUpper β (Lv L) U₀` | `p = 2` | `β = 1` on `G_{ℚ_2}^t ∩ G_{L_v}` for `t > U₀` | **T16** `PkgI6.LocalReciprocityUpper`; D3 `GlueConductor.fourth_pow_mem` (proved); Herbrand's `ψ ≥ id`; the 2-part of `χ` has conductor 4; N5 L826-844 |

`LocalGlue p Tm a β L` bundles the last three: `TorsionFieldWild` if `p ≤ D`, `TateWildTrivialL`
if `p > D`, and `BetaUpper` if `p = 2`. Both `G7Clauses` and `LocalGlue` are satisfiable:
`g7Clauses_triv` and `localGlue_triv` prove them for trivial data (VERIFIED). So the hypotheses
of `localData_of_g7` are not contradictory.

**Only the abelian-variety content of G15, and the 2-adic class field theory, remain.**

- At odd `p`, the whole `β`-side of g15-ram's `TwistUpper`/`TwistTame` is now proved from
  `G7Clauses`: `β` is a character on `G_F`, and `β² = χ` is trivial on wild inertia, so `β` is
  trivial there.
- The field-degree facts are now proved:
  - `[L_v:ℚ_p] ≤ [L:ℚ]`;
  - a field of degree `< p` is fixed by wild inertia, so no tameness of a Galois closure is needed;
  - the Galois closure of `E` has `e ≤ [E:ℚ_p]!`.

## 2. What is proved

All rows are VERIFIED: `lake env lean scratch/local-data/LocalData.lean` exits 0 with 0 errors and
no `sorry`, and `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all 27 printed
declarations.

| Lean (namespace `G15Ram`) | statement | proof idea |
|---|---|---|
| `largePrimeData_iff`, `localData_large_iff` | at `p > D`: `LocalData p r ↔ r = 1` on `wildSet` | tame `F` is fixed by wild inertia (g15-ram `wildFixTame`); conversely `F = ℚ_p` |
| `mat_eq_scalar_of_intertwines` | if `e` intertwines `ρ` with `m ⊕ m` and `ρ(g) = c`, then `m(g) = c·I` | evaluate at `e⁻¹(x, x)` |
| `twistShape_of_g8` | `G8Out (rho Tm a β) r` and `TateWildTrivial Tm a F` give `TwistShape p r F (β∘decomp)⁻¹` | `rho = β⁻¹ a Tm` |
| `localData_of_g8` | `G8Out` and `G7LocalData p Tm a β` give `LocalData p r` | — |
| `exists_pow_fix_of_wild` | for wild `σ` and finite Galois `F'`, some `σ^{p^a}` fixes `F'` | the order of `σ|_{F'}` is `p^a m`; `fix_of_wild_pow` (g15-ram) |
| `betaTame_of_odd` | at odd `p`, `BetaCharOn`, `BetaSqWild`, `BetaOpen` give `BetaTame` | `β(σ)^{p^a} = 1 = β(σ)²` |
| `betaOpen_of_isLocallyConstant` | `β` locally constant and `β 1 = 1` give `β∘decomp = 1` on some `G_{F'}` | `decomp` is continuous; `krullTopology_mem_nhds_one_iff`; normal closure |
| `betaUpper_of_betaTame` | `BetaTame` gives `BetaUpper` (any `U ≥ 0`) | g15-ram's `upperWild` |
| `wild_fix_root` | wild `σ` fixes every `ζ` with `ζⁿ = 1`, `p² ∤ n` | prime-to-`p` part: `m = ∑(1 − ηⁱ)` has norm `< 1` unless `η = 1`; `p`-part: wildness at `x = ζ − 1` together with `ζ = ηⁱ`; Bezout |
| `decomp_spec` | `embP ∘ decomp σ = σ ∘ embP` | `restrictNormal_commutes` |
| `cyc_decomp_wild`, `galChar_decomp_wild` | the cyclotomic character mod `N` and every Dirichlet character mod `N` are trivial on `decomp(P_p)` when `p² ∤ N` | `modularCyclotomicCharacter.unique` |
| `not_sq_dvd_chiLevel` | `p` odd, `T₋` primes ⟹ `p² ∤ chiLevel T₋` | `lev q ∈ {q, 4}` |
| `betaSqWild_of_chi` | `β² = ι∘galChar χ` on `G_F` gives `BetaSqWild` (odd `p`) | — |
| `betaCharOn_of_cocycle` | `∂β = ε`, `ε = 1` on `G_L²` and `F ⊇ embP(L)` give `BetaCharOn` | `decomp_fix_of_le` |
| `wild_fix_small_degree` | `[E:ℚ_p] < p` ⟹ `wildSet ⊆ fixSet E` | the `σ`-orbit of `x` has `p`-power size and at most `deg minpoly(x) < p` elements (`minimalPeriod`) |
| `localData_large_of_g8` | `p > D`, `[E:ℚ_p] < p`, `TateWildTrivial`/`BetaTame` on `E` ⟹ `LocalData p r` | — |
| `ramCard_zero_le_finrank`, `exists_finGal_ramCard_le` | `[E:ℚ_p] ≤ n` ⟹ some finite Galois `F ⊇ E` has `e(F) ≤ n!` | splitting field of the minimal polynomial of a primitive element; `Gal` acts on `≤ n` roots |
| `localData_small_of_g8` | `[E:ℚ_p] ≤ DG₀`, `TateWildTrivial`/`BetaUpper` on `E` ⟹ `SmallPrimeData p r` | — |
| `localData_of_g7_odd` | odd `p`: G7's clauses plus `TateWildTrivial` on a suitable `E ⊇ embP(L)` ⟹ `LocalData p r` | — |
| `exists_local_field_le`, `Lv_fin` | `[ℚ_p·embP(L) : ℚ_p] ≤ [L:ℚ]` | the minimal polynomial over `ℚ_p` divides the image of the one over `ℚ` |
| `localData_of_g7_large` | `p > D`: G7's clauses, `[L:ℚ] ≤ D` and `TateWildTrivialL` ⟹ `LocalData p r` | — |
| `localData_of_g7`, `g15RamG_of_g7` | main result (§1) | — |
| `g7LocalData_triv`, `g7Clauses_triv`, `localGlue_triv` | non-vacuity | trivial data |

## 3. Findings

- **F1 (VERIFIED, compiled).** `LocalData p r` is not provable for arbitrary `r`
  (`localData_large_iff`; example in §1). It is a claim about G8's `r`. The corrected form is
  `localData_of_g7`.
- **F2 (VERIFIED, read).** g15-ram §3 said that G8's construction of `r_ℓ` is not a Lean object,
  so `TwistShape` could not be stated on `(μ_σ, a_σ, β)`. That is superseded:
  - `G0Galois.G8Out` and `GlueDescent.rho` (`ZInQKernel/HDecomp/Descent/ProjRep.lean`) are that
    construction;
  - `twistShape_of_g8` moves `TwistShape` from `r` to G7's data.
- **F3 (VERIFIED, read). Interface gap.** g0-mod-field's `G7Data` does not carry `[L:ℚ] ≤ D`,
  and neither does `AfterG7`, which is quantified over all `G7Data`
  (`scratch/g0-mod-field/ModField.lean` l.611 and l.823); only `G4Out` carries it. G15 needs
  `[L_v:ℚ_p] ≤ D` (Glazer's degree bound at `p ≤ D` and tameness at `p > D`).
  - The fix is mechanical: `g7OutUnr_of_g4Out` (l.634) already has `hLD : finrank ℚ L ≤ heightD`
    in scope from `G4Out` (it uses it for the bound on `[L':ℚ]`) but does not store it, so adding
    that clause to `G7Data` costs one line.
  - Until then, `G7Clauses` asks for it.
  - Without the bound, Glazer's proof does not apply as written (SPECULATIVE whether the
    conclusion survives).
- **F4 (VERIFIED, logical).** `TateWildTrivial` (and so `TorsionFieldWild`, `TateWildTrivialL`)
  is false in general at `p = ℓ`. Wild inertia does not act trivially on `V_p` of a semistable
  abelian variety at `p` (STANDARD). It is only claimed, and `g15RamG_of_g7` only uses it, at
  `p ≠ ℓ` (`r₅` at `p ≠ 5`, `r₃` at `p = 5`).
- **F5 (VERIFIED, read). Two copies of `β`.** g0-mod-galois's `G7Out` has `β : G_ℚ → ℚ̄_ℓ` with
  `∂β = ε` and `β ≠ 0`, but no local constancy and no `β² = χ`. Those clauses live in
  g0-mod-field's `G7Data`, for `β : G_ℚ → ℂ^×`. Nothing in the repository connects the two copies
  yet. `G7Clauses` names that transport. The transport needs:
  - `ι : ℂ^× →* ℚ̄_ℓ^×`, which exists because `μ_∞(ℂ)` is a divisible subgroup, hence a direct
    summand, of `ℂ^×` (STANDARD);
  - `β_ℓ = ι ∘ β_ℂ`.
- **F6 (SPECULATIVE).** Truth on Glazer's construction is direct from N5 L813-851. One point
  goes beyond what g0-mod-galois's `G7Out` records:
  - `TorsionFieldWild` and `TateWildTrivialL` use that `a_σ · Tm σ` is the Tate action of `A/L`
    for `σ ∈ G_L`;
  - `G7Out` records the Tate action only on `G_{L'}`;
  - g0-mod-field's `DescentDatum` has it on points (`a = 1` and `m_σ` = Galois action on `G_L`).
- **Kernel pitfall (VERIFIED).** `mul_comm` on `heightG0 * heightD` made the kernel evaluate
  `Nat.pow` on `heightD`'s body. `Nat.mul_comm` avoids it.

## 4. What remains

1. `TorsionFieldWild` (`p ≤ D`) and `TateWildTrivialL` (`p > D`). Both need:
   - a Lean bridge from g0-mod-galois's `Vb A ℓ` (Tate module of `A/L'`, `PkgI3.AbVar`) to
     PkgI2's torsion action at a DVR place of `L_v`, for R6/D2/NOS;
   - the descent datum on `G_L`.
2. `BetaUpper` at `p = 2`. It needs the relative upper numbering of `G_{L_v}` and Herbrand's
   `G_{ℚ_2}^u ∩ G_F = G_F^{ψ(u)}`. Neither is defined over `LadicCond` (only the absolute
   `upperAbs` is), and T16 is stated over DVR models (`PkgI6`). g15-ram's `ladicDVRModelZp` is
   the natural bridge.
3. `G7Clauses`: the transport in F5 and the interface clause in F3.

## 5. Compile record

`lake env lean scratch/local-data/LocalData.lean`, 2026-11-13, about 60 s. VERIFIED: exit 0,
0 errors, no `sorry`, all 27 `#print axioms` lines `[propext, Classical.choice, Quot.sound]`
(`scratch/local-data/compile.out`).

Building first required, once:
- `lake build` of `ZInQKernel.HDecomp.{Conductor.LadicCond, Conductor.Breaks, Textbook.Different,
  Objects, Descent.Constants, I3Linalg.C2, Descent.ProjRep, Descent.B2Glue, Descent.Chi}`;
- `lake build ZInQKernel.Multiplication.Certificate.Constants`, which builds the upstream `lean/`
  package `z_in_q`.

The verbatim copies were checked with a python substring test (log step 6):
- `scratch/g15-ram/G15Ram.lean` lines 8-1384;
- `scratch/g0-mod-galois/part_galois.lean` lines 23-40, 66-73, 83-88, 110-133, 142-153.

## 6. Integration

**Compiled tail (VERIFIED).** `scratch/local-data/Tail.lean` is assembled by `build_tail.sh`. It
consists of verbatim `scratch/g0-mod-newform/NewForm.lean`, then g15-ram's pieces as in its
`build_tail.sh`, then this task's §3'-§4, then `tail_part.lean`. It proves
`G0ModNewform.modularConstituent_tail_L`, which is g0-mod-newform's tail (the conclusion of
G13-G16) with `G15RamG D u` replaced by

```
G8LocalPack 5 D.r5 (· ≠ 5) ∧ G8LocalPack 3 D.r3 (· = 5) ∧ G11Out T D.r5 ∧ G11Out T D.r3
```

Here `G8LocalPack ℓ r P` asks for a model and G7 data with three properties: `G8Out (rho Tm a β) r`,
`G7Clauses β ε L`, and `LocalGlue` at every prime in `P`. `lake env lean
scratch/local-data/Tail.lean` exits 0 with 0 errors and no `sorry` in about 90 s, and the axioms
are standard (`scratch/local-data/tail_compile.out`).


- `localData_of_g7` and `g15RamG_of_g7` give the newform tail the following replacement for its
  hypothesis on `D`: `D.r5` and `D.r3` come from G8 (`G8Out` on `rho Tm a β`), together with
  `G7Clauses` and `LocalGlue`. This is how `ModData` should be filled in (the tail of
  g0-mod-newform as patched by g15-ram's `modularConstituent_tail_R`).
- The local-field lemmas involve only `LadicCond` and Mathlib. They belong next to
  `ZInQKernel/HDecomp/Conductor/LadicCond.lean`, with g15-ram's `wildFixTame` and `upperWild`:
  - `wild_fix_root`;
  - `wild_fix_small_degree`;
  - `exists_finGal_ramCard_le`;
  - `exists_local_field_le`;
  - `cyc_decomp_wild`.
