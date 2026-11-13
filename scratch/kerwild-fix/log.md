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
