# linked-ram: `KernelFieldBreaks` reduced to one textbook leaf and one glue Prop at `p = 2`; `TateRamAtThree` corrected

Task linked-ram, 2026-11-13. Lean: `scratch/linked-ram/` (results log `log.md`). Merged before starting:
`origin/wip/linked-tate` (already on the base), `origin/wip/lt-goodred`, `origin/wip/g0-assemble3`.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = model judgement. **UNVERIFIED** = theorem number recalled without a source (no network).
Model work only; no human review.

## 0. Main result

**`LinkedRam` now rests on G3 (proved), one textbook leaf candidate and two glue Props, all stated over the
project's genuine definitions; two of the four pieces of linked-tate's reduction are proved outright.**

```lean
-- proved, no hypotheses (standard axioms):
theorem UnramTate.kernelFieldBreaksHigh : UnramTate.KernelFieldBreaksHigh   -- KernelFieldBreaks (ii), p > D
theorem UnramTate.upperAbsWild : UnramTate.UpperAbsWild                     -- G_{ℚ_p}^u ⊆ P_p for u > 0
-- reductions:
theorem UnramTate.kernelFieldBreaks_of' (hB : UpperBreakBound) (h2 : BetaTrivialAtTwo) : KernelFieldBreaks
theorem UnramTate.linkedRam_of' (hG3 : HSyn.LinkedTate.QMModelG3) (hK : KernelFieldBreaks)
    (hLI : LocalInertiaGlobal) (hUI : UpperAbsInertia) (h3 : TateRamAtThreeD) : LinkedRam
-- end to end:
theorem HSyn.sixContactMin_of_leaves5 (r : ResearchLeaves4) (t : TextbookLeaves) (gp : GluePieces5) :
    ZInQ.SixContactMin
```

- **Finding F1 (statement of g0-assemble3's field 46).** g0-assemble3 added `[L:ℚ] ≤ D` to `G7Data` so that
  linked-tate's `KernelFieldBreaks` and `TateRamAtThree` become usable. But `TateRamAtThree` is **not quantified over
  `G7Data`**: it ranges over every `K ≤ L ≤ L'` and every `QML3 K`, with no degree bound (part c12, L107-118,
  VERIFIED by reading). So the fix does not reach it, and linked-tate's caveat ("justified only for small `K`") still
  applies to `GluePieces4.tateRamAtThree`. I replace it by **`TateRamAtThreeD`**, the same statement with the hypothesis
  `Module.finrank ℚ L ≤ heightD`, and re-prove linked-tate's reduction as `linkedRam_of'`, reading the bound from
  `G7Data`'s last clause. The old Prop implies the new one (`tateRamAtThreeD_of`). Truth of the old form for unbounded
  `K`: SPECULATIVE (likely false; see §4).
- **`KernelFieldBreaks` (field 45) is split** into its two clauses. Clause (ii) (`p > D`, wild inertia) is **proved**
  from the definitions, by an elementary argument about wild elements of `G_{ℚ_p}` (§2). Clause (i) (`p ≤ D`,
  `t > U₀`) is reduced to:
  - **`UpperBreakBound`** (LEAF?, a textbook composite): for a finite extension `F/ℚ_p` of degree `a` inside `ℚ̄_p`,
    `G_{ℚ_p}^u` fixes `F` for `u > 4a²`. This is exactly the bound of the manuscript L796-811, derived there from
    Serre, *Local Fields*, Ch. III §6 (the different bound `δ ≤ e − 1 + e v_p(e)`) and Ch. IV §1-§3 (Hilbert's formula,
    Herbrand's function) [section numbers as cited by the manuscript; proposition numbers UNVERIFIED];
  - **`UpperAbsWild`** (glue, definitions): **proved** (§3);
  - **`BetaTrivialAtTwo`** (GLUE): at `p = 2`, `β(decomp₂ σ) = 1` for `σ ∈ G_{ℚ_2}^t ∩ decomp⁻¹(G_L)`, `t > U₀`.
    This is the manuscript's local-reciprocity argument (L826-843); at odd `p` the same step is proved here.
- **lt-goodred folded.** lt-goodred's proofs of `GoodRedTorsion` and `QMEndRank` (merged here) compile verbatim on
  g0-assemble3's olean chain (VERIFIED). `GluePieces5` drops those two fields as well.

**`GluePieces5`: 45 fields = 14 LEAF + 4 LEAF? + 27 GLUE** (g0-assemble3's `GluePieces4`: 46 = 14 + 3 + 29). Against
`GluePieces4`:
- removed: `goodRedTorsion`, `qmEndRank` (proved by lt-goodred), `kernelFieldBreaks`, `tateRamAtThree`;
- added: `upperBreakBound` (LEAF?), `betaTrivialAtTwo` (GLUE), `tateRamAtThreeD` (GLUE, the corrected field 46).

VERIFIED (Lean 4.35.0, Mathlib v4.35.0): `scratch/linked-ram/olean/Tail.lean` compiles with 0 errors and no `sorry`
against g0-assemble3's olean chain plus lt-goodred's proofs; every `#print axioms` (including
`HSyn.sixContactMin_of_leaves5` and `HSyn.gluePieces_of_gluePieces5`) is `[propext, Classical.choice, Quot.sound]` (§5).

## 1. The statements

All Props are in `namespace UnramTate` (`scratch/linked-ram/olean/Tail.lean`). `KernelFieldBreaks`, `TateRamAtThree`,
`LinkedRam`, `G7Data` are linked-tate's and g0-assemble3's definitions, unchanged.

| Prop | kind | content |
|---|---|---|
| `KernelFieldBreaksHigh` | **proved** | for G7 data, `p > D`, `σ ∈ P_p` (wild set): `decomp_p σ ∈ G_{L'}` (clause (ii) of `KernelFieldBreaks`) |
| `KernelFieldBreaksLow` | reduced | for G7 data, `p ≤ D`, `t > U₀`, `σ ∈ G_{ℚ_p}^t`: `decomp_p σ ∈ G_{L'}` (clause (i)) |
| `UpperBreakBound` | LEAF? | `F/ℚ_p` of degree `a`, `u > 4a²`, `σ ∈ G_{ℚ_p}^u` ⇒ `σ` fixes `F` pointwise |
| `UpperAbsWild` | **proved** | `u > 0` ⇒ `G_{ℚ_p}^u ⊆ P_p` |
| `BetaTrivialAtTwo` | GLUE | G7 data, `t > U₀`, `σ ∈ G_{ℚ_2}^t`, `decomp₂ σ ∈ G_L` ⇒ `β(decomp₂ σ) = 1` |
| `TateRamAtThreeD` | GLUE | `TateRamAtThree` with `finrank ℚ L ≤ D` |

`G_{ℚ_p}^u` is `LadicCond.upperAbs p u` (Serre IV §3, through `upperSet`, `phiAt`, `ramSetR`, `ramSet`); `P_p` is
`LadicCond.wildSet` (`‖σx − x‖ < ‖x‖` for `x ≠ 0`); `decomp_p` is `PkgI4.decomp p`, restriction along
`embP p : ℚ̄ → ℚ̄_p` (linked-tate's `embP_decomp`).

## 2. `KernelFieldBreaksHigh`, proved

Local lemmas (`scratch/linked-ram/test/Wild.lean`, Mathlib only, VERIFIED; copied into `Tail.lean` §1), for `σ` wild
in `G_{ℚ_p}`:
- **W0** `‖k‖ = 1` in `ℚ̄_p` for `p ∤ k`; `ξ^k = 1`, `p ∤ k`, `‖ξ − 1‖ < 1` ⇒ `ξ = 1` (`eq_one_of_pow_eq_one`:
  `k = Σ_{i<k}(1 − ξ^i)` and every term has norm `< 1`).
- **W1** `σ` fixes roots of unity of order prime to `p` (`wild_fix_root`).
- **W2** `σ^k y = y` with `p ∤ k` ⇒ `σ y = y` (`wild_fix_of_pow`). Over the fixed field `F` of `σ` (which contains a
  primitive `k`-th root of unity by W1), `X^k − 1 = ∏_c (X − c)`; evaluated at the `F`-linear map `σ`, every factor
  `σ − c` with `c ≠ 1` is injective, because `σ v = c v` would give `‖σv − v‖ = ‖c − 1‖‖v‖ ≥ ‖v‖`.
- **W4** roots of a nonzero `ℚ`-polynomial of degree `< p` are fixed (`wild_fix_of_aeval`: pigeonhole on
  `σ^i y`, `i ≤ deg`, then W2).
- **W5** `y^N = 1` with `p² ∤ N` ⇒ `σ y = y` (`wild_fix_of_pow_eq_one`: `y^{N'}` is a root of `1 + X + … + X^{p−1}`,
  then W0 for `σy/y`).
- Transfer to `G_ℚ` along `e : ℚ̄ → ℚ̄_p` with `e ∘ g = σ ∘ e`: `fix_of_finrank` (`[L:ℚ] < p` ⇒ `g ∈ G_L`),
  `fix_of_pow_eq_one`, `pow_mem_fixing` (`L'` finite normal ⇒ `g^{p^a} ∈ G_{L'}` for some `a`: write the order of
  `g|_{L'}` as `p^a m'` and apply W2 to the wild `σ^{p^a}`).

The proof (`kernelFieldBreaksHigh`, via `mem_GQL'_of_wild`): let `g = decomp_p σ`, `p > D`.
1. `p` is odd (`D ≥ 3`) and `[L:ℚ] ≤ D < p`, so `g ∈ G_L` (W4 through `minpoly`).
2. `ε = 1` on `G_L × G_L` (`InflatedFrom`, `ε 1 1 = 1`), so `β` is multiplicative on `G_L` and `β(1) = 1`.
3. `N = chiLevel Tm` with `Tm ⊆ T u` primes and `lev q ∈ {q, 4}`, so `p² ∤ N` (`not_sq_dvd_chiLevel`); by W5 `g` fixes
   `μ_N`, so `cyc N g = 1` (`cyc_decomp_eq_one`, Mathlib's `modularCyclotomicCharacter.unique`) and
   `β(g)² = χ(g) = 1`.
4. `g^{p^a} ∈ G_{L'}` (`pow_mem_fixing`), so `β(g)^{p^a} = β(g^{p^a}) = 1` (`G7Data`'s clause
   `G_{L'} = G_L ∩ ker β`). With `p` odd, `β(g) = 1`, so `g ∈ G_{L'}`.

The same `β`-step (`mem_GQL'_of_wild`) proves clause (i) at every odd `p ≤ D` once `g ∈ G_L` and `σ` is wild.

## 3. `KernelFieldBreaksLow` and `UpperAbsWild`

**`decomp_mem_GQL_of_breaks`** (from `UpperBreakBound`): for `[L:ℚ] ≤ D` and `t > U₀`, `decomp_p(G_{ℚ_p}^t) ⊆ G_L`.
For `x ∈ L`, `F = ℚ_p(embP x)` has degree `deg minpoly_{ℚ_p}(embP x) ≤ deg minpoly_ℚ x ≤ [L:ℚ] ≤ D`
(`IntermediateField.adjoin.finrank`, `minpoly.dvd`), and `4D² < U₀ = 4(DG₀)²` (`four_D_sq_lt_U0`). No Galois closure
is needed: the leaf is stated for any finite `F`.

**`kernelFieldBreaksLow_of`**: at `p = 2`, `BetaTrivialAtTwo`; at odd `p ≤ D`, `UpperAbsWild` (`t > U₀ ≥ 0`) and
`mem_GQL'_of_wild`.

**`UpperAbsWild`, proved** (`upperSet_wild`, `upperAbsWild`). For `x ≠ 0` take `M` = the normal closure of
`ℚ_p(x)` (as linked-tate's `upperAbsInertia`). `σ ∈ upperSet M u = G_{ψ(u)}(M)`:
- the identity lies in every `ramSet M i` once a uniformizer exists, which `σ ∈ upperSet M u` itself provides; the
  restriction images are finite (`restr_image_finite`, via `M →ₐ[ℚ_p] ℚ̄_p`);
- the integrand `g_t/g_0` of `φ_M` is antitone, hence interval integrable, and lies in `[1/g_0, 1]` on `[0, ∞)`, so
  `v/g_0 ≤ φ_M(v) ≤ v` for `v ≥ 0` (`le_phiAt`, `phiAt_le_self`) and `φ_M ≤ 0` on `v ≤ 0` (linked-tate);
- hence the set `{v ≥ −1 | u ≤ φ_M(v)}` is nonempty and bounded below by `u`, so `ψ(u) ≥ u > 0` and `σ ∈ G_1(M)`;
- `G_1(M)` acts wildly on `M^×` (`wild_on_of_ramSet`): the value group of `M` is `‖ϖ‖^ℤ` (`norm_eq_zpow`, from the
  maximality in `IsUnif`), `x = w ϖ^k` with `‖w‖ = 1`, and `σx/x = (σw/w)(σϖ/ϖ)^k` with both factors in the group
  `{‖z − 1‖ < 1}`.

## 4. `TateRamAtThree` and the corrected `TateRamAtThreeD`

linked-tate's `TateRamAtThree` quantifies over `K ≤ L ≤ L'` with only `L'/ℚ` finite Galois. Its own docstring and
caveat say it is "only justified for small `K`". The manuscript's argument (L814-821) needs `[L:ℚ] ≤ D`: over
`F = L_v(A[5])`, of degree `≤ D·|GL₄(𝔽₅)| = D G₀` (`G₀ = 116064000000 = |GL₄(𝔽₅)|`, VERIFIED arithmetic:
`624·620·600·500`), Raynaud's criterion gives semistable reduction, wild inertia of `G_F` acts trivially on `V₅`, and
`G_{ℚ_3}^t ⊆ G_F ∩ P_3` for `t > U₀ = 4(DG₀)²` (break bound with `a = DG₀`, and `UpperAbsWild`). For unbounded `K`
the last step fails: the field cutting out the inertia image at 3 can have upper breaks beyond `U₀` (SPECULATIVE; no
counterexample constructed). `TateRamAtThreeD` adds `Module.finrank ℚ L ≤ heightD`; `G7Data` supplies it, and
`linkedRam_of'` uses it. `TateRamAtThreeD` is believed true by the manuscript's argument (STANDARD route: R6 Raynaud,
`UpperBreakBound`, `UpperAbsWild`; the unipotent action of a wild element of 3-power order on a 5-group is trivial).

## 5. What compiles

- `scratch/linked-ram/test/Wild.lean` (`lake env lean`, imports Mathlib only): 0 errors. VERIFIED.
- `scratch/linked-ram/olean/`: g0-assemble3's olean chain (`LPrefix → TailA → TailB → TailC → TailE → TailF`, copied
  from the g0-assemble3 worktree, gitignored), `TailD.olean` built here from g0-assemble3's committed
  `olean/TailD.lean` (0 errors), `GoodRedLR.lean` = `import TailD` + lt-goodred's `integ/99d_proofs.lean` verbatim
  (0 errors, 31 s), and `Tail.lean` = `import GoodRedLR` + this task's parts (0 errors, about 10 s;
  `ctail.sh Tail.lean`). Axiom reports, all `[propext, Classical.choice, Quot.sound]`: `kernelFieldBreaksHigh`,
  `kernelFieldBreaks_of_halves`, `kernelFieldBreaks_of`, `kernelFieldBreaks_of'`, `upperAbsWild`, `linkedRam_of'`,
  `HSyn.gluePieces_of_gluePieces5`, `HSyn.sixContactMin_of_leaves5`. VERIFIED.
- Setup note: a fresh worktree needs `lake build ZInQKernel.Hypotheses.JHeight` (and the other prefix imports) before
  the prefix oleans load ("unknown module prefix 'ZInQ'").

## 6. What remains

- **`BetaTrivialAtTwo`** (GLUE). Needs local class field theory at 2 (the manuscript: local reciprocity, the logarithm
  on `U_F^{e+1}`, and `ψ_{F/ℚ_2}(u) ≥ u`). What is cheap here: `χ(decomp₂ σ) = 1` follows from W1 (odd part of `N`)
  and `UpperBreakBound` for `ℚ_2(i)`, so only the sign `β = ±1` is the genuine content (not compiled).
- **`TateRamAtThreeD`** (GLUE). Route: the 5-torsion field `K₁ = K(A[5])` (open stabilizers: `PkgI3.RhoCont`'s
  `exists_openSubgroup_galAct_eq`; `[K₁:K] ≤ |GL₄(𝔽₅)|` from T5), the break bound for `K₁L`, Raynaud (R6) at the place
  above 3 transported as in lt-goodred's `goodRedTorsion`, and "unipotent of 3-power order on a 5-group ⇒ trivial"
  (W2 applied to the torsion field). Not compiled.
- **`UpperBreakBound`** (LEAF?). A textbook composite (Serre III §6, IV §1-§3, plus `[normal closure : ℚ_p] ≤ a!`);
  formalizing it needs Hilbert's different formula and the different bound, which Mathlib 4.35 lacks.
- **`LinkedFrob`**: untouched (assigned elsewhere).
