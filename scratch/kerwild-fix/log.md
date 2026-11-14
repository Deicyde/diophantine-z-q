# kerwild-fix results log

## Step 0 (11:58-12:05 PST): setup
- Merged origin/wip/rv-fast. Read (VERIFIED) rv-fast §1: `exists_localGlue_of_tateModuleFree` keeps
  `G7Clauses β' ε' L` about TateBridgeK's hidden data; for unram-tate's witness (`a' = 1`,
  `ε' = c = n/d`) G7Clauses forces `c² = 1` (rv-fast `rvf_c_sq_of_a_one`).
- Read (VERIFIED): frob-trace's `tateBridge35_of_algFrobLink` (FrobTrace.lean) contains a `have key`
  proving, for every `ℓ` and every `j : ℚ̄ →ₐ[ℚ] ℚ̄_ℓ`, `G7Out` at `ℓ` with `a = j ∘ (βQ / γQ(h·h⁻¹))`,
  `β' = j ∘ βQ`, `ιC ∘ βQ = β` (scalars rescaled by `g7Out_rescale`); it uses only I3.M0
  (`tateCont_of_tateModuleFree`), `tatePoints`, `endBaseChange`, `resQEmbedding`, `scalarsQbar`.
  AlgFrobLink is used only for `FrobTraceLink`.
- Read (VERIFIED): g8-tate's `G8Tate.exists_complex_equiv : Nonempty (ℂ ≃+* PadicAlgCl ℓ)` and
  `G8Tate.g7Clauses_of_g7Data (Φ) (hD : G7Data …) (hLD : [L:ℚ] ≤ D) :
  G7Clauses (Φ ∘ β) (Φ ∘ ε) L` (scratch/g8-tate/part_tools.lean, part_local.lean).
- Plan: choose `j := Φ ∘ ιC`; then `β' = Φ ∘ β`, `ε' = ∂β' = Φ ∘ ε` (sign cocycle: Glazer's
  normalization, the real factor stays in `a`), and G7Clauses, KerWild hold for the witness.
- build.sh: KerWildFix.lean = current LocalGlue.lean + FrobTrace.lean (minus BCPoints l.1632-1754)
  + lg-kerwild's part_kerwild/part_tbk/part_final verbatim (no g0-dim slice: LocalGlue.lean now has
  it, `diff` identical) + part_fix.lean (new).
- `lake build` of the 25 imported ZInQKernel modules: success.

## Step 1 (12:08 PST): rebuild of lg-kerwild on the current local-glue source
- `lake env lean scratch/kerwild-fix/KerWildFix.lean` (no part_fix yet): exit 0, 0 errors, ~61 s
  (compile0.out). The rv-fast integration conflict (duplicate `G0Dim`) is resolved by not splicing
  g0-dim again; lg-kerwild's three parts compile unchanged against LocalGlue.lean's DimBlock.

## Step 2 (12:20-12:40 PST): part_fix.lean (§0-§3), compiled
- New defs: `KWFix.TateBridgeE` (TateBridge with output `β' = Φ ∘ β`, `ε' = Φ ∘ ε`,
  `Φ : ℂ ≃+* ℚ̄_ℓ`), `KWFix.TateBridge35E` (TateBridge35 with `j_ℓ = Φ_ℓ ∘ ι_ℂ`, same output form),
  `KWFix.jOf`.
- Proved (VERIFIED, `lake env lean scratch/kerwild-fix/KerWildFix.lean`: exit 0, 0 errors, ~71 s,
  compile1.out; 12 `#print axioms` all `[propext, Classical.choice, Quot.sound]`):
  `tateBridge_of_E : TateBridgeE → TateBridge`, `tateBridge35_of_E : TateBridge35E → TateBridge35`,
  `g7Out_eps_congr`, `g7Out_beta_congr`, `cocycle_map`,
  **`tateBridgeE_of_tateModuleFree : PkgI3.TateModuleFree → TateBridgeE`** (copy A of frob-trace's
  proof, `j := Φ ∘ ι_ℂ`), **`tateBridge35E_of_algFrobLink : TateModuleFree → AlgFrobLink →
  TateBridge35E`** (copy B), `kerWild_of_equiv`, `localGlue_of_E`,
  `exists_localGlue_of_tateBridgeE`, **`exists_localGlue_of_leaves`** (every ℓ: ∃ Φ Tm c a uu,
  G7Out ∧ G7Clauses ∧ KerWild ∧ ∀ p ≠ ℓ, LocalGlue; hypotheses I3.M0, R6, I2-Tors, UnramRoots,
  G7Data, dim A_{L'} = 2, rank End A_{L'} = 4, [L:ℚ] ≤ D), `exists_localGlue35_of_tateBridge35E`.
- Copied verbatim (VERIFIED compile): g8-tate `padic_card_le`, `padicAlgCl_card`,
  `exists_complex_equiv`, `T_prime`, `g7Clauses_of_g7Data`.
- Pitfalls hit: FrobTrace.lean's file-level `open … GlueDescent.B3Q` (l.53-54) is needed for `GQL`
  in the copies; `rw` of lambdas `fun g => Φ (β g)` fails (GQ vs PkgI4.GQ binder types), replaced
  by `g7Out_beta_congr` with pointwise proofs.

## Step 3 (12:45-13:05 PST): leaves-only forms, compiled
- build.sh now also splices scratch/unram-roots/UnramRoots.lean l.53-end (its l.21-52 copy of
  `G15Ram.UnramRoots` dropped: the only name clash with the rest of the file, checked by script;
  two `end` close its unclosed `noncomputable section`s) and adds its Tau Ceti imports and
  g8-tate's three cardinality imports. `lake build` of the 5 Tau Ceti modules: success.
- New (VERIFIED, compile.out: exit 0, 0 errors, ~72 s; 21 `#print axioms`, all
  `[propext, Classical.choice, Quot.sound]`):
  - `KWFix.G7OutUnrD` (G7OutUnr + `[L:ℚ] ≤ D`), `g7OutUnr_of_D`, `g7OutUnrD_of_g4Out` (copy C of
    g0-mod-field's `g7OutUnr_of_g4Out`, FrobTrace.lean l.636-662, with `hLD` kept);
  - `dim_bc_of_g7Data` (`dim A_{L'} = 2` from G7Data, g8-tate's argument);
  - `c_eq_of_a_one` (`a ≡ 1` ⟹ `c = ε'`);
  - `exists_localGlue_of_leaves'` (no `UnramRoots` hypothesis: `UnramRootsTask.unramRoots_all`);
  - `exists_localGlue_of_g4Out` (G4Out + 4 B2 leaves + I3.M0 + R6 + I2-Tors ⟹ G7 data with
    `[L:ℚ] ≤ D`, and, given `rank End A_{L'} = 4`, LocalGlue at every ℓ, p ≠ ℓ);
  - `exists_localData_of_leaves` (G15's `LocalData p r` at every p ≠ ℓ for every r with
    `G8Out A_{L'} ℓ (rho Tm a (Φ ∘ β)) r`; hypotheses G7Data, `[L:ℚ] ≤ D`, rank 4);
  - `exists_localGlue35_of_algFrobRed` (TateBridge35E, and at ℓ = 5, 3 FrobTraceLink + LocalGlue,
    from I3.M0, AlgFrobRed, R6, I2-Tors).
- compile0.out: the rebuild check of step 1 (lg-kerwild parts only).

## Step 4 (13:10-13:35 PST): G15 corollary, compiled
- Attempted `exists_g7LocalPackBC_of_leaves` (local-glue's `G7LocalPackBC ℓ r` for our data):
  `(deterministic) timeout at whnf` (also at 1.6M heartbeats), located (by sorry-bisection) in the
  steps supplying `L, L', A, Tm` (likely retyping `Tm` from `GaloisCopy.Vb (A.baseChange L' via incAlg)` to `G0Galois.Vb (bcL' hLL' A)`
  (`incAlgL`, same text as `incAlg`); SPECULATIVE as to the exact cause). Dropped (FINDING for integration: avoid the `bcL'` retyping).
- Instead proved (VERIFIED, compile.out: exit 0, 0 errors, ~73 s; 22 `#print axioms`, all
  `[propext, Classical.choice, Quot.sound]`): `exists_g15RamG_of_leaves` — operator data at ℓ = 5
  and ℓ = 3 (Glazer's normalization) and, for every `D : ModData` whose `r₅`, `r₃` satisfy G8Out for
  these data and G11Out, `G15RamG D u` (local-glue's `g15RamG_of_g7` with G7Clauses and LocalGlue
  discharged). Hypotheses: I3.M0, R6, I2-Tors, G7Data, `[L:ℚ] ≤ D`, `rank End A_{L'} = 4`.
