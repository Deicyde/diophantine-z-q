# kerwild-fix: `LocalGlue` at every `ℓ` with all of `G7Clauses` discharged

Task kerwild-fix, 2026-11-13. Base `wip/kerwild-fix` (88dc9bd4) with origin/wip/rv-fast merged.
Files: `scratch/kerwild-fix/` (`build.sh`, `mk_fix.py`, `part_fix_head.lean`, `part_fix_defs.lean`,
`part_fix_final.lean`, the assembled `KerWildFix.lean`, `compile.out`, results log `log.md`).
This is model work. No human has checked it.

Marks: **VERIFIED** means compiled, computed, or read in a file here. **STANDARD** means published,
with a reference. **SPECULATIVE** means my judgement. Theorem numbers recalled without a source are
**UNVERIFIED** (no network).

## 0. Result

**The defect rv-fast found is fixed (VERIFIED, compiled).**

- The every-`ℓ` theorem no longer has a hypothesis about hidden data.
- `KWFix.exists_localGlue_of_leaves'` proves that for every coefficient prime `ℓ` there are
  operator data satisfying `G7Out` at `ℓ`. On these data it proves, for every `p ≠ ℓ`:
  - `G7Clauses`,
  - `KerWild`,
  - local-glue's `LocalGlue p`.
- The leaves used are I3.M0 (`PkgI3.TateModuleFree`, T26), R6 (`ObjBridge.RaynaudCriterion`) and
  I2-Tors (`ObjBridge.TorsionStructure`, T5).
- The other hypotheses are properties of the visible input:
  - `G7Data u P L A ε N χ β L' hLL'`;
  - `[L:ℚ] ≤ D`;
  - `rank_ℤ End(A_{L'}) = 4`.
- `UnramRoots` is no longer a hypothesis. It is unram-roots' theorem, which is spliced in.
- `dim A_{L'} = 2` is now proved from `G7Data`.

**The fix is a change of normalization.**

- unram-tate's witness put the real descent factor into `ε'` (`a' = 1`, `ε' = c = n/d`). Glazer and
  `G7Clauses` put it into `a`.
- The new bridge `KWFix.TateBridgeE` has the following output, for a field isomorphism
  `Φ : ℂ ≃+* ℚ̄_ℓ` (Steinitz, from g8-tate):
  - `β' = Φ ∘ β` and `ε' = Φ ∘ ε`, with `β`, `ε` G7Data's cochain and sign cocycle;
  - `a` carries the real factor: `a_g a_h c(g,h) = ε'(g,h) a_{gh}`, with `c = n/d`.
- `c_eq_of_a_one` is proved: `a ≡ 1` forces `c = ε'`, so `c` is a sign.
- `KWFix.tateBridgeE_of_tateModuleFree : PkgI3.TateModuleFree → TateBridgeE` is proved. The proof
  is frob-trace's construction with the embedding `j := Φ ∘ ι_ℂ`.
- `TateBridgeE` implies `TateBridge` (`tateBridge_of_E`).

**Coefficient primes `ℓ = 5, 3` with `FrobTraceLink` (the form g14-trace and the assembly use).**

- `KWFix.TateBridge35E` is `TateBridge35` with `j_ℓ = Φ_ℓ ∘ ι_ℂ`.
- `tateBridge35E_of_algFrobLink : TateModuleFree → AlgFrobLink → TateBridge35E` is proved, and so is
  `tateBridge35_of_E : TateBridge35E → TateBridge35`.
- `exists_localGlue35_of_algFrobRed` gives `FrobTraceLink` and `LocalGlue` at every `p ≠ 5`
  (resp. `p ≠ 3`). Its inputs are I3.M0, frob-trace's glue `AlgFrobRed`, R6 and I2-Tors.
- rv-fast listed two missing inputs on this route. Both are now settled:
  - `ε₅ = 1` on `G_L × G_L` is now a theorem: `ε₅ = Φ₅ ∘ ε`, and `ε` is inflated and normalized.
  - `[L:ℚ] ≤ D` is a hypothesis on `L`. `G4Out` supplies it through the new
    `g7OutUnrD_of_g4Out`.

**Rebuild.** lg-kerwild's three parts rebuild against the current local-glue source with no
change (VERIFIED). The conflict was a second splice of g0-dim, which `LocalGlue.lean` now already
contains. `scratch/kerwild-fix/build.sh` no longer splices it.

## 1. What compiles

`lake env lean scratch/kerwild-fix/KerWildFix.lean`:
- exit 0, 0 errors, about 73 s (`compile.out`);
- 22 `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]`;
- no `sorry`, no `axiom`.

All VERIFIED.

The file is assembled by `build.sh` from these pieces:
1. **local-glue, current source.** `scratch/local-glue/LocalGlue.lean` verbatim. Since b582bf03 it
   contains g0-dim's `DimBlock` and `localGlue_of_baseChange'`.
2. **frob-trace.** `scratch/frob-trace/FrobTrace.lean` verbatim, minus l.1632-1754. These lines
   are unram-tate's BCPoints block, already in `LocalGlue.lean` (as lg-kerwild did).
3. **lg-kerwild.** `scratch/lg-kerwild/part_kerwild.lean`, `part_tbk.lean`, `part_final.lean`,
   verbatim and read-only. `compile0.out` is the check of pieces 1-3 alone: 0 errors.
4. **unram-roots.** `scratch/unram-roots/UnramRoots.lean` l.53-end, verbatim.
   - Its l.21-52 are dropped: they hold its copy of `G15Ram.UnramRoots`, already in local-glue
     (byte-identical, rv-fast §3).
   - A script checked all of its declaration names against the rest of the file. This copy was
     the only clash.
   - Its Tau Ceti imports are added.
5. **New part.** `part_fix.lean`, made by `mk_fix.py`:
   - §0 verbatim copies from g8-tate: `padic_card_le`, `padicAlgCl_card`, `exists_complex_equiv`
     (part_tools l.20-61); `T_prime`, `g7Clauses_of_g7Data` (part_local l.28-63).
   - §1 the new definitions and small lemmas.
   - §2 three edited copies of g0-mod-field / frob-trace proofs (list below).
   - §3 the results.

The three copies in §2:
- **Copy A.** `tateBridge35_of_algFrobLink` (FrobTrace.lean l.2562-2753) becomes
  `tateBridgeE_of_tateModuleFree`. It drops the `FrobTraceLink` part, so it does not use
  `AlgFrobLink`.
- **Copy B.** The same proof becomes `tateBridge35E_of_algFrobLink`.
- **Copy C.** `g7OutUnr_of_g4Out` (l.636-662) becomes `g7OutUnrD_of_g4Out`, which keeps `hLD`.

The edits are only the header and the last lines, listed with assertions in `mk_fix.py`.

### Statements (all VERIFIED by compile)

| name | statement (abbreviated) |
|---|---|
| `KWFix.TateBridgeE` (def, GLUE) | ∀ G7Data, `dim A_{L'} = 2`, `rank End A_{L'} = 4`, ∀ ℓ, ∃ `Φ : ℂ ≃+* ℚ̄_ℓ`, `Tm c a uu`, `G7Out A_{L'} ℓ Tm c (Φ∘ε) a (Φ∘β) uu` |
| `tateBridge_of_E` | `TateBridgeE → TateBridge` |
| `tateBridgeE_of_tateModuleFree` | `PkgI3.TateModuleFree → TateBridgeE` |
| `KWFix.TateBridge35E` (def, GLUE) | `TateBridge35`'s data with `β'_ℓ = Φ_ℓ∘β`, `ε'_ℓ = Φ_ℓ∘ε`, `a_ℓ = Φ_ℓ∘ι_ℂ∘aQ`, `ι_ℂ∘βQ = β`, `FrobTraceLink Tm₅ Tm₃` |
| `tateBridge35E_of_algFrobLink` | `TateModuleFree → AlgFrobLink → TateBridge35E` |
| `tateBridge35_of_E` | `TateBridge35E → G14Bridge.TateBridge35` |
| `g7Out_eps_congr`, `g7Out_beta_congr`, `cocycle_map` | `G7Out`'s `ε` is `∂β`; pointwise congruence in `β`; `∂(Φ∘β) = Φ∘∂β` |
| `c_eq_of_a_one` | `G7Out … c ε' a β' …`, `a ≡ 1` ⟹ `c = ε'` |
| `dim_bc_of_g7Data` | `G7Data … → dim A_{L'} = 2` (g8-tate's argument via `IsQMModel`, `PK.surface`, g0-dim) |
| `kerWild_of_equiv` | `G7Data … → KerWild L' (Φ∘β) L` |
| `localGlue_of_E` | G7Data, `[L:ℚ] ≤ D`, `G7Out` with `(Φ∘ε, Φ∘β)`, `p ≠ ℓ`, R6, I2-Tors, `UnramRoots p ℓ` ⟹ `LocalGlue p Tm a (Φ∘β) L` |
| `exists_localGlue_of_tateBridgeE` | `TateBridgeE` + R6 + I2-Tors + `UnramRoots` + G7Data + dim + rank + `[L:ℚ] ≤ D` ⟹ ∀ ℓ, ∃ `Φ Tm c a uu`, `G7Out ∧ G7Clauses (Φ∘β) (Φ∘ε) L ∧ KerWild ∧ ∀ p ≠ ℓ, LocalGlue p` |
| `exists_localGlue_of_leaves` | the same, with I3.M0 in place of `TateBridgeE` |
| **`exists_localGlue_of_leaves'`** | the same, without `UnramRoots` (I3.M0, R6, I2-Tors only) |
| `UnramRootsTask.unramRoots_all` | (unram-roots, spliced) `∀ p ℓ, G15Ram.UnramRoots p ℓ` |
| `KWFix.G7OutUnrD` (def), `g7OutUnr_of_D` | `G7OutUnr` plus `[L:ℚ] ≤ D`; it implies `G7OutUnr` |
| `g7OutUnrD_of_g4Out` | `LeafHasse → LeafLocalTwo → LeafSqrtCrit → LeafUnramified → G4Out u P → G7OutUnrD u P` |
| `exists_localGlue_of_g4Out` | `G4Out` + the 4 B2 leaves + I3.M0 + R6 + I2-Tors ⟹ ∃ G7 data with `[L:ℚ] ≤ D`, and (`rank End A_{L'} = 4` →) ∀ ℓ the conclusion of `exists_localGlue_of_leaves'` |
| `exists_localData_of_leaves` | the data of `exists_localGlue_of_leaves'`, and ∀ `r` with `G8Out A_{L'} ℓ (rho Tm a (Φ∘β)) r`: G15's `LocalData p r` for every `p ≠ ℓ` |
| `exists_g15RamG_of_leaves` | data at `ℓ = 5, 3`; ∀ `D : ModData` with `G8Out` (these data, `D.r₅`, `D.r₃`) and `G11Out`: `G15RamG D u` |
| `exists_localGlue35_of_tateBridge35E` | `TateBridge35E` + R6 + I2-Tors + `UnramRoots` + G7Data + dim + rank + `[L:ℚ] ≤ D` ⟹ `G7Clauses` at 5 and 3, `LocalGlue` at every `p ≠ 5` (`Tm₅`) and `p ≠ 3` (`Tm₃`) |
| `exists_localGlue35_of_algFrobRed` | `TateBridge35E` and the previous conclusion, from I3.M0, `AlgFrobRed`, R6, I2-Tors |

## 2. Why the normalization fixes it (VERIFIED by reading and compile)

**Where the old witness failed.** `G7Clauses β' ε' L` has three relevant clauses:
- `β'² = ι ∘ χ` for a Dirichlet character `χ` and a hom `ι : ℂ^× → ℚ̄_ℓ^×`;
- `∂β' = ε'`;
- `ε' = 1` on `G_L × G_L`.

`∂(β'²) = 1` then forces `ε'² = 1` (rv-fast `rvf_g7Clauses_eps_sq`). The old witness had
`ε' = n/d`, which is not a sign in general.

**How frob-trace's construction works.** frob-trace's `key` (inside `tateBridge35_of_algFrobLink`)
holds for every `j : ℚ̄ →ₐ[ℚ] ℚ̄_ℓ`. It rescales unram-tate's witness by
`φ(g) = j(βQ g)/γ(hgh⁻¹)` (`g7Out_rescale`). The result is `G7Out` with:
- `β' = j ∘ βQ`, where `ι_ℂ ∘ βQ = β` (`scalarsQbar`);
- `a = j(βQ g / γQ(hgh⁻¹))`.

**The choice of `j`.** Take `j := Φ ∘ ι_ℂ` for `Φ : ℂ ≃+* ℚ̄_ℓ`. Then:
- `β' = Φ ∘ β`;
- `ε' = ∂β' = Φ ∘ ε`, a sign (`g7Out_eps_congr` with `cocycle_map`);
- every clause of `G7Clauses` is transported from `G7Data` along `Φ`. g8-tate's
  `g7Clauses_of_g7Data` does this with `ι = Units.map Φ`.

**`KerWild` and `DescentPts`.**
- `KerWild` follows because `Φ` is injective, with G7Data's clause `G_{L'} = G_L ∩ ker β` (local-glue's
  `kerWild_of_g7Data`).
- `DescentPts` is lg-kerwild's `descentPts_of_g7`.

**What `a` is.** I read this off `scalarsQbar`; it is not exported as a Lean statement.
- `ι_ℂ(γQ σ) = β(σ)/a_σ`.
- Hence `ι_ℂ(a-value at g) = a_{hgh⁻¹} · β(g)/β(hgh⁻¹)`. This is Glazer's real factor at `hgh⁻¹`,
  times a ratio of values of `β` that is `1` on `G_L`.
- So `ρ = β'⁻¹ a Tm` is Glazer's `ρ_ℓ` at `hgh⁻¹`, transported by `Φ`.

## 3. Findings

1. **rv-fast's concern is resolved by a different bridge, not by a weaker conclusion.**
   - `TateBridgeE` implies `TateBridge`.
   - Its proof uses no new leaf or glue: I3.M0 only, as unram-tate's `tateBridge_of_tateModuleFree`
     did.
   - lg-kerwild's `TateBridgeK`, `exists_localGlue_of_tateBridgeK` and
     `exists_localGlue_of_tateModuleFree` still compile, but they are superseded. Integration should
     use `exists_localGlue_of_leaves'` (or `…35_of_algFrobRed`) and drop the old every-`ℓ`
     theorem, whose `G7Clauses` premise is vacuous for its own witness.
2. **`[L:ℚ] ≤ D` is a premise on the input `L`, and it is dischargeable.**
   - g0-mod-field's `G7OutUnr` drops it, although `g7OutUnr_of_g4Out` keeps G4's `L`.
   - `G7OutUnrD` with `g7OutUnrD_of_g4Out` restores it from `G4Out` with the same four leaves.
3. **Integration pitfall: retyping data over `bcL'`.** Retyping our data over local-glue's `bcL'`
   (`incAlgL`, the same text as `incAlg`) to state `G7LocalPackBC` timed out in elaboration
   (`whnf`, still at 1.6M heartbeats). Sorry-bisection placed it in the first steps of the proof, where `L, L', A` and `Tm` are supplied
   (a `sorry` right after the outer `refine` compiles; one right after `refine ⟨Tm, ?_⟩` still times
   out).
   `exists_g15RamG_of_leaves` reaches G15 through `g15RamG_of_g7` instead, which is generic in
   `K` and `A`.
4. **The Tau Ceti imports are safe here.** Adding them (for unram-roots) to the whole assembled file
   broke none of the earlier verbatim parts (VERIFIED, same compile).

## 4. What remains (unproved or not done)

- **The hypothesis `rank_ℤ End(A_{L'}) = 4`.** It is g8-tate's glue `EndRank4`; linked-tate
  derives it from `FibreSimple` and `QMEndRank`. Not re-checked here.
- **The `G8Out` premise.** In `exists_localData_of_leaves` and `exists_g15RamG_of_leaves`, the
  link from these operator data to G8's `r_ℓ` is not made here. g8-object makes `r_ℓ` a Lean
  object.
- **`FrobTraceLink` at `ℓ = 5, 3`.** It still needs frob-trace's glue `AlgFrobRed` (alg-frob-red
  reduced it). The every-`ℓ` result needs no Frobenius link.
- **Not wired into g0-assemble2.** `GluePieces3`, e.g. field 39 `LinkedTateLocal`, is not
  connected here.
- **Duplicated proofs.** frob-trace's 190-line proof is duplicated (copies A and B). At integration
  its `key` should become one lemma.
- **Review.** This is model review only.
