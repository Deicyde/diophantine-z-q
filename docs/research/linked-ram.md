# linked-ram: `LinkedRam` now rests on one textbook leaf and one glue Prop (the sign of `β` at 2)

Task linked-ram, 2026-11-13. Lean: `scratch/linked-ram/` (results log `log.md`). Merged before starting:
`origin/wip/linked-tate` (already on the base), `origin/wip/lt-goodred`, `origin/wip/g0-assemble3`.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = model judgement. **UNVERIFIED** = theorem number recalled without a source (no network).
Model work only; no human review.

## 0. Main result

**Both glue fields that g0-assemble3 left for `LinkedRam` are removed.**

- `kernelFieldBreaks` (field 45 of `GluePieces4`) is reduced to:
  - **`UpperBreakBound`**, a textbook leaf candidate;
  - **`BetaSignAtTwo`**, one glue Prop: the sign of `β` on high upper groups at the prime 2.
- `tateRamAtThree` (field 46) is first **corrected** (finding F1), then **proved** from leaves already in the bundles:
  - R6, Raynaud's criterion (`r.r6`);
  - T5, the torsion structure (`t.t5`);
  - `UpperBreakBound`.
- Everything else in linked-tate's reduction of `LinkedRam` is now proved.

```lean
-- proved outright (no hypotheses):
theorem UnramTate.kernelFieldBreaksHigh : UnramTate.KernelFieldBreaksHigh   -- KernelFieldBreaks (ii), p > D
theorem UnramTate.upperAbsWild : UnramTate.UpperAbsWild                     -- G_{ℚ_p}^u ⊆ P_p for u > 0
-- proved from leaves:
theorem UnramTate.torsionFieldFive_of (hTors : PkgI2.TorsionStructure.{0}) : TorsionFieldFive
theorem UnramTate.tateRamAtThreeD_of_leaves (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hB : UpperBreakBound) : TateRamAtThreeD
-- reductions:
theorem UnramTate.betaTrivialAtTwo_of_sign (hB : UpperBreakBound) (h : BetaSignAtTwo) : BetaTrivialAtTwo
theorem UnramTate.kernelFieldBreaks_of' (hB : UpperBreakBound) (h2 : BetaTrivialAtTwo) : KernelFieldBreaks
theorem UnramTate.linkedRam_of' (hG3 : HSyn.LinkedTate.QMModelG3) (hK : KernelFieldBreaks)
    (hLI : LocalInertiaGlobal) (hUI : UpperAbsInertia) (h3 : TateRamAtThreeD) : LinkedRam
-- end to end:
theorem HSyn.sixContactMin_of_leaves5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) :
    ZInQ.SixContactMin
```

### Finding F1: g0-assemble3's field 46 has no degree bound

g0-assemble3 added `[L:ℚ] ≤ D` to `G7Data`, so that linked-tate's `KernelFieldBreaks` and `TateRamAtThree` would become
usable.
- **The gap.** `TateRamAtThree` is not quantified over `G7Data`. It ranges over every `K ≤ L ≤ L'` and every `QML3 K`,
  with no degree bound (part c12, L107-118; VERIFIED by reading). So the fix does not reach `GluePieces4.tateRamAtThree`.
- **Why that matters.** The manuscript's argument needs `[L:ℚ] ≤ D`. For unbounded `K`, the Prop is SPECULATIVELY false:
  the field that cuts out the inertia image at 3 can have upper breaks above `U₀`. No counterexample was constructed.
- **The fix.**
  - `TateRamAtThreeD` is the same statement with the hypothesis `Module.finrank ℚ L ≤ heightD`.
  - `linkedRam_of'` re-proves linked-tate's reduction, reading the bound from `G7Data`'s last clause.
  - The old Prop implies the new one (`tateRamAtThreeD_of`).
- **The corrected Prop is then proved** (`tateRamAtThreeD_of_leaves`, §4).

### `GluePieces5`: 44 fields = 14 LEAF + 4 LEAF? + 26 GLUE

g0-assemble3's `GluePieces4` has 46 fields = 14 + 3 + 29. Against it:
- **Removed:**
  - `goodRedTorsion`, `qmEndRank`: lt-goodred's proofs, which compile verbatim on g0-assemble3's olean chain (VERIFIED);
  - `kernelFieldBreaks`, `tateRamAtThree`: this task.
- **Added:**
  - `upperBreakBound` (LEAF?);
  - `betaSignAtTwo` (GLUE).

**Verification.** VERIFIED in Lean 4.35.0 with Mathlib v4.35.0, on two builds:
- the olean tail `scratch/linked-ram/olean/Tail.lean`;
- the flat file of g0-assemble3 plus lt-goodred plus this task (§6).

Both have 0 errors and no `sorry`. Every axiom report is `[propext, Classical.choice, Quot.sound]`.

## 1. The statements

All of these Props are in `namespace UnramTate`. The following definitions are unchanged:
- linked-tate's `KernelFieldBreaks`, `TateRamAtThree`, `LinkedRam`;
- g0-assemble3's `G7Data`;
- `LadicCond`'s `upperAbs` (`G_{ℚ_p}^u`, Serre IV §3) and `wildSet` (`P_p`, defined by `‖σx − x‖ < ‖x‖`);
- `PkgI4.decomp`, the restriction along `embP p : ℚ̄ → ℚ̄_p`.

| Prop | kind | content |
|---|---|---|
| `KernelFieldBreaksHigh` | **proved** | G7 data, `p > D`, `σ ∈ P_p` ⇒ `decomp_p σ ∈ G_{L'}` (clause (ii)) |
| `KernelFieldBreaksLow` | reduced | G7 data, `p ≤ D`, `t > U₀`, `σ ∈ G_{ℚ_p}^t` ⇒ `decomp_p σ ∈ G_{L'}` (clause (i)) |
| `UpperBreakBound` | **LEAF?** | `F/ℚ_p` of degree `a`, `u > 4a²`, `σ ∈ G_{ℚ_p}^u` ⇒ `σ` fixes `F` pointwise |
| `UpperAbsWild` | **proved** | `u > 0` ⇒ `G_{ℚ_p}^u ⊆ P_p` |
| `BetaTrivialAtTwo` | reduced | G7 data, `t > U₀`, `σ ∈ G_{ℚ_2}^t`, `g = decomp₂ σ ∈ G_L` ⇒ `β(g) = 1` |
| `BetaSignAtTwo` | **GLUE** | the same with the extra hypothesis `β(g)² = 1` |
| `TateRamAtThreeD` | **proved from leaves** | `TateRamAtThree` with `finrank ℚ L ≤ D` |
| `TorsionFieldFive` | **proved from T5** | `QML3` over `K`: some `K₁/K` with `[K₁:K] ≤ G₀` has `G_{K₁}` fixing `A(K̄)[5]` |
| `RaynaudAtThree` | **proved from R6, `UpperBreakBound`, `TorsionFieldFive`** | `σK ∈ G_K` matching `σ ∈ G_{ℚ_3}^t`, `t > U₀`, `[K:ℚ] ≤ D` ⇒ `(σK − 1)² = 0` on `A(K̄)[5ⁿ]` |
| `TateRamCore` | **proved from `RaynaudAtThree`** | the same `σK` fixes `A(K̄)[5ⁿ]` |

### About the leaf `UpperBreakBound`

- **Source.** It is the bound in the manuscript at L796-811. The manuscript derives it from Serre, *Local Fields*:
  - Ch. III §6, the different bound `δ ≤ e − 1 + e·v_p(e)`;
  - Ch. IV §1-§3, Hilbert's formula `δ = Σ_{i≥0}(|G_i| − 1)` and Herbrand's change of variables.

  The section numbers are the manuscript's; proposition numbers are UNVERIFIED.
- **The argument.** The normal closure of a degree-`a` extension has degree `≤ a!`. Its last upper break `u*` satisfies
  `u*/2 ≤ δ/e < 1 + v_p(e) ≤ 1 + log₂ a!`, so `u* < 4a²`. Upper numbering passes to quotients, so `G^u ⊆ G_F` for
  `u > 4a²`.
- **Why the encoding is faithful.** It is stated over `LadicCond`'s definitions, which encode Serre's:
  - `ramSet` is `G_i`;
  - `ramSetR` is `G_u = G_{⌈u⌉}`;
  - `phiAt` is Herbrand's function `φ`;
  - `upperSet` is `G^v = G_{ψ(v)}`, with `ψ(v) = inf{u ≥ −1 | φ(u) ≥ v}`;
  - `upperAbs` asks this at every finite Galois level.

  The facts used here (`φ(u) ≤ u`, `ψ(u) ≥ u`, the integrand antitone) are proved in §3 and behave as in Serre.
- **Kind.** LEAF? (a textbook composite), not a single printed theorem. Formalizing it needs Hilbert's formula and the
  different bound, which Mathlib 4.35 lacks.

## 2. `KernelFieldBreaksHigh`, proved

### Local lemmas on wild elements

They are in `scratch/linked-ram/test/Wild.lean`, which imports only Mathlib (VERIFIED), and are copied into
`Tail.lean` §1. Let `σ` be a wild element of `G_{ℚ_p}`.
- **W0** (`eq_one_of_pow_eq_one`). If `ξ^k = 1`, `p ∤ k` and `‖ξ − 1‖ < 1`, then `ξ = 1`. Proof: `k = Σ_{i<k}(1 − ξ^i)`
  and every term has norm `< 1`.
- **W1** (`wild_fix_root`). `σ` fixes the roots of unity of order prime to `p`.
- **W2** (`wild_fix_of_pow`). If `σ^k y = y` with `p ∤ k`, then `σ y = y`. Proof:
  - over the fixed field of `σ`, `X^k − 1 = ∏_c (X − c)`;
  - for `c ≠ 1`, the `F`-linear map `σ − c` is injective, because `σv = cv` would give `‖σv − v‖ = ‖c − 1‖‖v‖ ≥ ‖v‖`.
- **W4** (`wild_fix_of_aeval`). The roots of a nonzero `ℚ`-polynomial of degree `< p` are fixed. Proof: pigeonhole,
  then W2.
- **W5** (`wild_fix_of_pow_eq_one`). If `y^N = 1` and `p² ∤ N`, then `y` is fixed.
- **Transfer to `G_ℚ`.** Along `e : ℚ̄ → ℚ̄_p` with `e ∘ g = σ ∘ e`:
  - `fix_of_finrank`: if `[L:ℚ] < p`, then `g ∈ G_L`;
  - `fix_of_pow_eq_one`: the same for roots of unity, as in W5;
  - `pow_mem_fixing`: if `L'` is finite and normal, then `g^{p^a} ∈ G_{L'}` for some `a`.

### The β-step

`mem_GQL'_of_wild`: take G7 data, `p` odd, `σ` wild, and `g = decomp_p σ ∈ G_L`.
1. `ε = 1` on `G_L × G_L` (from `InflatedFrom` and `ε 1 1 = 1`), so `β` is multiplicative on `G_L`.
2. `N = chiLevel Tm` with `Tm` a set of primes, so `p² ∤ N` (`not_sq_dvd_chiLevel`).
3. `g` fixes `μ_N`, so `cyc N g = 1` (Mathlib's `modularCyclotomicCharacter.unique`). Hence `β(g)² = χ(g) = 1`.
4. `g^{p^a} ∈ G_{L'} = G_L ∩ ker β` (from `pow_mem_fixing`), so `β(g)^{p^a} = 1`.
5. `p` is odd, so `β(g) = 1`.

### The proof of `KernelFieldBreaksHigh`

For `p > D ≥ 3`:
- `p` is odd;
- `[L:ℚ] ≤ D < p`, so `g ∈ G_L` by W4;
- the β-step then gives `g ∈ G_{L'}`.

## 3. `KernelFieldBreaksLow` and `UpperAbsWild`

**`decomp_mem_GQL_of_breaks`.** For `[L:ℚ] ≤ D` and `t > U₀`, `decomp_p(G_{ℚ_p}^t) ⊆ G_L`. Proof:
- for `x ∈ L`, `ℚ_p(embP x)` has degree `≤ deg minpoly_ℚ x ≤ D`;
- `4D² < U₀ = 4(DG₀)²` (`four_D_sq_lt_U0`).

**`kernelFieldBreaksLow_of`.**
- At odd `p ≤ D`: `UpperAbsWild` and the β-step.
- At `p = 2`: `BetaTrivialAtTwo`.

**`UpperAbsWild`, proved** (`upperSet_wild`, `upperAbsWild`). For `x ≠ 0`, let `M` be the normal closure of
`ℚ_p(x)`.
- Write `g_t = |G_t|`. The integrand `g_t/g_0` of `φ_M` is antitone, so it is interval integrable.
- On `[0, ∞)` the integrand lies in `[1/g_0, 1]`. The identity lies in every `G_i`, and the restriction images are
  finite (`restr_image_finite`).
- Hence `v/g_0 ≤ φ_M(v) ≤ v`, so `ψ(u) ≥ u > 0` and `G^u(M) ⊆ G_1(M)`.
- `G_1(M)` acts wildly on `M^×` (`wild_on_of_ramSet`):
  - the value group of `M` is `‖ϖ‖^ℤ` (`norm_eq_zpow`, from the maximality in `IsUnif`);
  - write `x = wϖ^k` with `‖w‖ = 1`;
  - then `σx/x = (σw/w)(σϖ/ϖ)^k` lies in the group `{‖z − 1‖ < 1}`.

**`betaTrivialAtTwo_of_sign`.** At `2`, write `N = 2^b N'` with `b ≤ 2` (`not_eight_dvd_chiLevel`) and `N'` odd.
- `y^{N'}` is a 4th root of unity. It has degree `≤ 4`, so `UpperBreakBound` fixes it (`64 < U₀`).
- The odd part is fixed by wildness and W0.
- So `χ(g) = 1` and `β(g)² = 1`. What remains is exactly `BetaSignAtTwo`.

## 4. `TateRamAtThreeD`, proved from R6, T5 and `UpperBreakBound`

This is the manuscript's argument at L814-821, done in Lean.

1. **`TorsionFieldFive` from T5** (`torsionFieldFive_of`).
   - `A(K̄)[5] ≅ 𝔽₅⁴` by T5, so it is finite.
   - Point stabilizers are open (`PkgI3.RhoCont.exists_openSubgroup_galAct_eq`), so the stabilizer `S` of `A[5]` is
     open.
   - Set `K₁ = K̄^S`. Then `[K₁:K] = [G_K:S]` (`IntermediateField.finrank_eq_fixingSubgroup_index`, and
     `InfiniteGalois.fixingSubgroup_fixedField`).
   - `G_K/S` embeds in `Aut(𝔽₅⁴)`, whose order is `|GL₄(𝔽₅)| = 624·620·600·500 = G₀` (`card_GL4_F5`, by
     `Matrix.card_GL_field`).
2. **`RaynaudAtThree`** (`raynaudAtThree_of`).
   - Every `y ∈ K₁` has degree `≤ [K:ℚ][K₁:K] ≤ D G₀` over `ℚ`. So `σK` fixes `K₁`, by `UpperBreakBound` and
     `4(DG₀)² = U₀ < t`.
   - `σK` lies in the inertia group of `ψ^*(v)`, by `upperAbsInertia` and `localInertiaGlobal` (linked-tate's proofs).
   - Apply R6 over `K₁` with `m = 5`. `K₁` is a number field, and `O₁ = w₁ ∩ K₁` is a DVR (neron-lg's classification,
     as copied by lt-goodred).
   - Transport the result along `A_{K₁}(\bar{K₁}) ≅ A(K̄)` (unram-tate's `trPt` and `bcPt`).
3. **`TateRamCore`** (`tateRamCore_of`).
   - Set `y = σK x · x⁻¹`. Unipotence makes `y` fixed, so `σK^m x = y^m x`, and `y^{5ⁿ} = 1`. Hence `σK^{5ⁿ} x = x`.
   - `σ` is wild (`upperAbsWild`) and `3 ∤ 5ⁿ`, so `σK x = x` by `fix_of_pow_fix`.
   - `fix_of_pow_fix`: the stabilizer of a point is open, hence closed, hence equal to `G_{K̄^S}`; W2 moves the fixing
     from `σK^k` to `σK`.
4. **`TateRamAtThreeD`** (`tateRamAtThreeD_of_core`). Transport along `\bar{L'} ≅ K̄` and
   `A_{L,L'}(\bar{L'}) ≅ A(K̄)`, exactly as lt-goodred's `goodRedTorsion` does. Then apply linked-tate's
   `tate_eq_one_of_torsion`.

## 5. Findings

- **F1** (§0). Field 46 of `GluePieces4` lacks the degree bound. Corrected, and the corrected form is proved.
- **F2.** `UpperBreakBound`, stated for any finite `F/ℚ_p` (not only Galois ones), is the only local-field input needed
  for clause (i) at odd `p` and for the prime 3. No Galois-closure bookkeeping is needed in Lean.
- **F3.** At `2`, the only content beyond `UpperBreakBound` and the definitions is the sign: `β(g) ≠ −1`. That needs
  local class field theory, which Mathlib 4.35 lacks.
- **Pitfalls** (recorded in `log.md`):
  - `ι` is notation for `GrpObj.inv` under `open MonObj`;
  - `AddAut` is an additive group in Mathlib 4.35, so use `Multiplicative`;
  - `PkgI2.Pts` and `PkgI3`'s `Pt` agree only up to definitional unfolding: bridge them with `exact`, not `rw`;
  - `nlinarith` on goals that contain `(heightD : ℝ)` hits the maximum recursion depth.

## 6. What compiles

- **`scratch/linked-ram/test/Wild.lean`** (imports Mathlib only): 0 errors. VERIFIED.
- **The olean chain in `scratch/linked-ram/olean/`.**
  - The prefix is g0-assemble3's olean chain, copied from the g0-assemble3 worktree (gitignored).
  - `TailD.olean` is built here from g0-assemble3's committed `TailD.lean`.
  - `GoodRedLR.lean` is `import TailD` followed by lt-goodred's `integ/99d_proofs.lean`, verbatim.
  - `Tail.lean` is `import GoodRedLR` followed by this task's parts. Build with `ctail.sh Tail.lean`: 0 errors, about
    35 s.
  - All 15 axiom reports are standard. They include `kernelFieldBreaksHigh`, `upperAbsWild`, `kernelFieldBreaks_of'`,
    `betaTrivialAtTwo_of_sign`, `torsionFieldFive_of`, `raynaudAtThree_of`, `tateRamAtThreeD_of_leaves`,
    `linkedRam_of'`, `HSyn.gluePieces_of_gluePieces5` and `HSyn.sixContactMin_of_leaves5`.
- **The flat file.** `assemble.sh` builds `LinkedRam.lean` (not committed) from three pieces:
  - g0-assemble3's `G0Assemble3.lean`;
  - lt-goodred's `99d_proofs.lean`;
  - `Tail.lean` without its import line.

  The result of `lake env lean` is in `flat_summary.txt`:
  - the run before the TateRam and sign additions: exit 0 in 922 s, 0 errors, 237 standard axiom reports (VERIFIED);
  - the final run: see `flat_summary.txt` and `log.md`.
- **Setup for a fresh worktree.** Run `lake build ZInQKernel.Hypotheses.JHeight` (and the prefix's other imports) before
  the prefix oleans load. Otherwise Lean reports "unknown module prefix 'ZInQ'".

## 7. What remains

- **`BetaSignAtTwo`** (GLUE). It says `β(decomp₂ σ) ≠ −1` on `G_{ℚ_2}^t ∩ G_L`, `t > U₀`, given `β² = 1` there. The
  manuscript's route:
  - local reciprocity at 2;
  - the 2-primary factor of `χ` has conductor `≤ 4`;
  - the logarithm identifies `U_F^{e+1}` with `𝔪_F^{e+1}`;
  - `ψ_{F/ℚ_2}(u) ≥ u`.

  Truth: STANDARD route.
- **`UpperBreakBound`** (LEAF?). A candidate for the literature list: a textbook composite from Serre.
- **`LinkedFrob`**: untouched (assigned to another host).
- **Integration.** `GluePieces5` and `sixContactMin_of_leaves5` are in `Tail.lean` §LinkedRamBundle. They are built from
  g0-assemble3's `GluePieces4` (part z95) by removing four fields and adding two. No Prop of another task was changed;
  `TateRamAtThreeD` is a new, corrected Prop that sits beside the old one.
