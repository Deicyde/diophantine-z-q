# local-glue: `LocalGlue p Tm a β L` (local-data) on G7's data

Task local-glue, 2026-11-13.

Lean: `scratch/local-glue/LocalGlue.lean`, assembled by `scratch/local-glue/build.sh` from:
- a verbatim copy of `scratch/local-data/LocalData.lean`, which contains `LocalGlue` and
  everything it depends on;
- the new parts `scratch/local-glue/part_glue.lean` (§6-§7) and `part_pack.lean` (§8).

Integration file: `scratch/local-glue/TailK.lean` (`build_tail.sh`), which is local-data's
`Tail.lean` plus the same parts plus `tail_glue.lean` (§9).

Log: `scratch/local-glue/log.md`. Compiler output: `compile.out` and `tail_compile.out`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

**Verdict.** `LocalGlue p Tm a β L`, copied verbatim from local-data, is a predicate on
arbitrary operators `Tm`, scalars `a`, `β` and a field `L`. It is not a closed theorem:
`not_localGlue_zero` proves it false for `Tm = 0` at every `p > D` (VERIFIED). It is a claim about
the data that G7 builds. The corrected statement is a theorem on G7's data.

**Main result (VERIFIED, compiled, standard axioms).** On G7's data (`G0Galois.G7Out`, with
local-data's clauses `G7Clauses`), `LocalGlue` follows from Props that mention only:
- the abelian surface `A/K` (`K = L'`, the kernel field);
- the Hom field `L`;
- `β`.

No `Tm` and no `a` remain:

```
theorem G15Ram.localGlue_of_g7 {K} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm c ε a β u} (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hW : 7 ≤ p → TateWildK (p := p) A ℓ) (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L)
    (hB : p = 2 → BetaUpper β (Lv (p := p) L) U0) :
    LocalGlue (p := p) Tm a β L
```

At `p ≥ 7`, `p ≠ ℓ`, the Tate-module Prop `TateWildK` is in turn proved from:
- the leaf **I2-Tors** (`ObjBridge.TorsionStructure`);
- `dim A = 2` (a clause of `G7Out`);
- one Mathlib-level glue Prop `PtFinite A` (`K̄`-points are defined over finite extensions);
- the instance `RaynaudPlace` of the leaf **R6** (Raynaud's criterion) at the place of `embP`.

```
theorem G15Ram.tateWildK_of_leaves' (hℓp : ℓ ≠ p) (h7 : 7 ≤ p)
    (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2) (hPt : PtFinite A)
    (hR3 : RaynaudPlace (p := p) A 3) (hR7 : RaynaudPlace (p := p) A 7) :
    TateWildK (p := p) A ℓ
```

The proof uses `m = 3`, or `m = 7` when `p = 13`. Then `p ∤ |GL₄(𝔽_m)|` (computed in Lean from
Mathlib's `Matrix.card_GL_field`), so a wild `σ'` acts trivially on `A[m] ≅ (ℤ/m)⁴`. Raynaud then
gives `(σ' − 1)² = 0` on `A[ℓⁿ]`, and with a `p`-power period this forces `σ' = 1` there (D2).
Finally `tate_eq_one_of_torsFix` passes from torsion points to `ℚ̄_ℓ ⊗ V_ℓ(A)`.

**Packs and tail (VERIFIED).**
- `G0ModNewform.G8LocalPack` is the hypothesis of local-data's tail `modularConstituent_tail_L`;
  it is copied verbatim here.
- `g8LocalPack_of_K` proves it from `G7LocalPackK`, which consists of:
  - G7's data (`G7Out`) and G8's output;
  - `G7Clauses` and `KerWild`;
  - at the primes in question, `TorsFixWild` (`p ≥ 7`), `TorsFixWildE` (`p ≤ 5`) and `BetaUpper`
    (`p = 2`).
- `g15RamG_of_packK` gives g15-ram's `G15RamG D u`.
- `modularConstituent_tail_K` (in `TailK.lean`) is g0-mod-newform's tail (G13-G16) with this
  hypothesis.

### The remaining named Props

Each is a `def … : Prop` in `part_glue.lean` with a docstring naming its step and source. None
is a leaf. The leaves they rest on (in **bold**) are in the bundles already.

| Prop | primes | content | status |
|---|---|---|---|
| `KerWild K β L` | all | `g ∈ G_L`, `β(g) = 1` ⟹ `g ∈ G_K` | GLUE: g0-mod-field's `G7Data` clause `σ ∈ G_{L'} ↔ σ ∈ G_L ∧ β σ = 1`, transported to `G7Out`'s `K` and `ℚ̄_ℓ`-valued `β` (with local-data's F3/F5) |
| `PtFinite A` | `p ≥ 7` | every `P ∈ A(K̄)` is fixed by `G_F` for a finite `F/K` | GLUE, Mathlib-level: a `K̄`-point of a finite-type `K`-scheme factors through a finite extension |
| `RaynaudPlace p A m` (`m = 3, 7`) | `p ≥ 7`, `p ≠ ℓ` | a wild `σ' ∈ G_K` fixing `A(K̄)[m]` has `(σ'−1)² = 0` on `A(K̄)[ℓⁿ]` | GLUE on **R6** (`PkgI2.RaynaudCriterion`): the bridge from `(K, embP)` to a DVR of `K(A[m])` and a valuation ring of `K̄` over it, and the base change of `A` to `K(A[m])` |
| `TorsFixWildE p A ℓ β L` | `p ∈ {2,3,5}`, `p ≠ ℓ` | some `E ⊇ L_v`, `[E:ℚ_p] ≤ G₀[L_v:ℚ_p]`: wild `σ ∈ G_E` has `β(σ) = 1` and fixes `A(K̄)[ℓⁿ]` | GLUE on **R6**, **I2-Tors** and the descent `A = (A_L)_{L'}` (finding G3) |
| `BetaUpper β L_v U₀` | `p = 2` | unchanged from local-data | GLUE on **T16** (`ZInQ.Contrib.localKroneckerWeber`), D3 and Herbrand (local-data §4.2) |

`TorsFixWild` (`p ≥ 7`) and `WildIter` are no longer open. They are proved from the rows above
(`torsFixWild_of_raynaud`, `wildIter_of_ptFinite`).

## 2. What is proved

All rows are VERIFIED: `lake env lean scratch/local-glue/LocalGlue.lean` exits 0 with 0 errors
and no `sorry`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every printed
declaration.

| Lean (`G15Ram` unless noted) | statement | proof idea |
|---|---|---|
| `not_localGlue_zero` | `D < p` ⟹ `¬ LocalGlue (Tm := 0) (a := 1) (β := 1) L` | `σ = 1` is wild and fixes `L` |
| `fixSet_Lv_of_fix`, `fixSet_Lv_iff` | `σ ∈ G_{L_v}` ⟺ `decomp σ ∈ G_L` | `decomp_spec`; `L_v ≤ fixedField(zpowers σ)` via the stabilizer |
| `beta_wild_of_clauses` | odd `p`, `G7Clauses` ⟹ `β = 1` on wild `σ` with `decomp σ ∈ G_L` | local-data's `betaTame_of_odd` on `F = L_v` |
| `aTm_eq_one_of_kerWild` | `g ∈ G_L`, `β g = 1`, Tate trivial over `g` ⟹ `a_g Tm g = 1` | `KerWild` puts `g` in `G_K`, where `G7Out` has `Tm = tate`, `a = 1` |
| `localGlue_of_g7` | main result (§1) | at `p ≥ 7` the field of `TorsionFieldWild` is `L_v` itself; `p > D ≥ 10¹²` gives `p ≥ 7` |
| `tate_eq_one_of_torsFix` | fixing every `ℓⁿ`-torsion point ⟹ trivial on `ℚ̄_ℓ ⊗ V_ℓ(A)` | `T_ℓ` = compatible sequences of `ℓⁿ`-torsion points |
| `tateWildK_of_torsFixWild`, `tateWildKE_of_torsFixWildE` | — | `tate_eq_one_of_torsFix` |
| `iterate_card_GL_fix` | `φ` injective, `φ(S) ⊆ S`, `S ≅ (ℤ/q)ⁿ` as groups ⟹ `φ^[‖GLₙ(𝔽_q)‖] = id` on `S` | `φ` induces an element of `GLₙ(𝔽_q)` (`Matrix.GeneralLinearGroup.toLin`, `pow_card_eq_one'`) |
| `card_GL4_three`, `card_GL4_seven`, `coprime_card_GL4_three`, `coprime_card_GL4_seven` | `‖GL₄(𝔽₃)‖ = 24261120 = 2⁹3⁶·5·13`; `13 ∤ ‖GL₄(𝔽₇)‖` | `Matrix.card_GL_field`, `norm_num` |
| `fixed_of_unipSq_of_iterate'` | `(σ−1)²x = 0`, `ℓⁿx = 0`, `σ^{qᵃ}x = x`, `(qᵃ, ℓⁿ) = 1` ⟹ `σx = x` | D2's core, as `PkgI2.fixed_of_unipSq_of_iterate`, on PkgI3 points |
| `torsGL_of_leaf` | I2-Tors and `dim A = 2` ⟹ `A(K̄)[m] ≅ (ℤ/m)⁴` | the leaf applied to `ObjBridge.toGrp A` (its torsion set is defeq to PkgI3's) |
| `fix_torsion_of_coprime` | `WildIter`, `TorsGL A m`, `p ∤ ‖GL₄(𝔽_m)‖` ⟹ wild `σ'` fixes `A[m]` | periods `pᵃ` and `‖GL₄‖` are coprime (`IsPeriodicPt.gcd`) |
| `torsFixWild_of_raynaud`, `tateWildK_of_leaves` | §1 | — |
| `qEmbRing_surjective` | `ℚ̄ → K̄` is onto | `K̄` integral over `ℚ̄` (`IsAlgClosed.ringHom_bijective_of_isIntegral`) |
| `wild_pow_fix_elem`, `wild_pow_fix_field` | a wild `σ'` has `p`-power period on each `x ∈ K̄` and on each finite `F/K` | `exists_pow_fix_of_wild` on the normal closure of `ℚ_p(embP y)`; a basis of `F` |
| `wildIter_of_ptFinite`, `tateWildK_of_leaves'` | §1 | — |
| `G0ModNewform.g8LocalPack_of_K`, `g15RamG_of_packK` | packs (§1) | `localGlue_of_g7`; local-data's `g15RamG_of_g7` |
| `G0ModNewform.modularConstituent_tail_K` (`TailK.lean`) | the tail of G13-G16 on `G7LocalPackK` | local-data's `modularConstituent_tail_L` |

## 3. Findings

- **G1 (VERIFIED, compiled).** `LocalGlue` is false for some data (`not_localGlue_zero`), so it
  cannot be proved as stated with free `Tm, a, β, L`.
- **G1' (SPECULATIVE, not formalized).** `LocalGlue` is not implied by `G7Out ∧ G8Out ∧ G7Clauses`
  either. These tie `a·Tm` to an abelian variety only on `G_K`, and nothing in them relates `K`
  to `L`.
  - Example: `L = ℚ`, and `A = E²` over a cyclic degree-`p` subfield `K ⊆ ℚ(ζ_{p²})`.
  - Take `Tm = ψ ⊗ (Tate action of E²)`, with `ψ` of order `p` and conductor `p²`, trivial
    on `G_K`.
  - Then `a·Tm(σ) = ψ(σ) ≠ 1` for some wild `σ`.

  The missing link is `KerWild` (G7Data's kernel field clause).
- **G2 (VERIFIED, read).** g0-mod-field's `G7Data` (`scratch/g0-mod-field/ModField.lean`
  l.611-631) has the clause `σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`. g0-mod-galois's `G7Out`
  (`scratch/g0-mod-galois/part_galois.lean` l.121-133) does not. With that clause:
  - at odd `p`, every wild inertia element of `G_L` lies in `G_{L'}`, since `β` is tame there
    (`beta_wild_of_clauses`);
  - so at every `p ≥ 7` the local glue is a statement about `A/L'` alone, and the descent datum
    on `G_L \ G_{L'}` is not needed.
- **G3 (VERIFIED, arithmetic).** At `p ∈ {2,3,5}` this argument cannot avoid the descent of `A`
  to `L`. For every `m ≥ 3`, `|GL₄(ℤ/m)|` is divisible by `2`, `3` and `5`: for a prime `q ∣ m`,
  `|GL₄(𝔽_q)| = q⁶(q⁴−1)(q³−1)(q²−1)(q−1)`. So the argument cannot make
  `[L'_w(A[m]) : L'_w]` prime to `p`. Moreover `[L'_w : L_v]` is not bounded by `G₀`.
  - So `TorsFixWildE` needs a model `A_L` with `A = (A_L)_{L'}` and `E = L_v'(A_L[m])`, as in
    Glazer (N5 L813-818).
  - At `p = 2` it also needs the extension `L_v'/L_v` of degree `≤ 4` killing `β` on wild
    inertia.
- **G4 (VERIFIED, compiled).** At `p ≥ 7`, `m = 3` (`p ≠ 13`) or `m = 7` (`p = 13`) has
  `p ∤ |GL₄(𝔽_m)|`. So `TateWildK` needs no degree bound and no descent: Glazer's `L_v(A[3])` of
  degree `≤ DG₀` can be replaced by `L_v` itself at those primes.
- **G5 (VERIFIED, compiled).** The PkgI2 leaf I2-Tors applies directly to the PkgI3 abelian
  variety through `ObjBridge.toGrp`. The torsion subset and the group law agree definitionally
  (`torsGL_of_leaf` is `⟨e, he⟩` from the leaf), so no transport is needed for torsion. R6 is
  different: it needs a base change and a change of valuation-theoretic setting.

## 4. What remains

1. `RaynaudPlace p A m` (`p ≥ 7`): apply R6 to `K' = K(A[m])`. This needs:
   - the valuation subring of `K'` at the place of `embP` (a DVR);
   - a valuation ring `w` of `K̄' ≅ K̄` over it, with wild `σ'` in its inertia group;
   - `A_{K'}` (`PkgI2.baseChange`) and an equivariant identification of its torsion points
     with those of `A`.
2. `PtFinite A`: a `K̄`-point of a scheme of finite type over `K` factors through `Spec F` with
   `F/K` finite (Mathlib-level scheme glue).
3. `TorsFixWildE` (`p ∈ {2,3,5}`): items 1-2, plus the model `A_L` and its descent datum on
   `G_L` (`DescentDatum` of g0-mod-field, transported to `ℚ̄_ℓ ⊗ V_ℓ`), plus the degree bound on
   `L_v'(A_L[m])`.
4. `KerWild`: the transport of G7Data to G7Out (also local-data's F3/F5).
5. `BetaUpper` at `p = 2`: as in local-data §4.2 (relative upper numbering and Herbrand's
   `ψ ≥ id` over `LadicCond`; T16 is now `ZInQ.Contrib.localKroneckerWeber`).

## 5. Compile record

- `lake env lean scratch/local-glue/LocalGlue.lean`: exit 0, 0 errors, no `sorry`; every
  `#print axioms` line `[propext, Classical.choice, Quot.sound]` (`compile.out`).
- `lake env lean scratch/local-glue/TailK.lean`: see `tail_compile.out` and the log.
- Building first required `lake build` of the imports of `LocalData.lean` and of local-data's
  `Tail.lean`.
