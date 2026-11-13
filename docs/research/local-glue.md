# local-glue: `LocalGlue p Tm a β L` (local-data) on G7's data

Task local-glue, 2026-11-13. Lean: `scratch/local-glue/LocalGlue.lean`, assembled by
`scratch/local-glue/build.sh` from a verbatim copy of `scratch/local-data/LocalData.lean` (which
contains `LocalGlue` and everything it depends on) and the new part
`scratch/local-glue/part_glue.lean`. Log: `scratch/local-glue/log.md`. Compiler output:
`scratch/local-glue/compile.out`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

**Verdict.** `LocalGlue p Tm a β L`, copied verbatim from local-data, is a predicate on
arbitrary operators `Tm`, scalars `a`, `β` and a field `L`. It is not a closed theorem:
`not_localGlue_zero` proves it false for `Tm = 0` at every `p > D` (VERIFIED). It is a claim about
the data that G7 builds, and the corrected statement is a theorem on G7's data.

**Main result (VERIFIED, compiled, standard axioms).** On G7's data (`G0Galois.G7Out`, with the
clauses `G7Clauses` of local-data), `LocalGlue` follows from Props that mention only the abelian
surface `A/K` (`K = L'`), the Hom field `L` and `β`. No `Tm` and no `a` remain:

```
theorem G15Ram.localGlue_of_g7 {K} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm c ε a β u} (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hW : 7 ≤ p → TateWildK (p := p) A ℓ) (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L)
    (hB : p = 2 → BetaUpper β (Lv (p := p) L) U0) :
    LocalGlue (p := p) Tm a β L

theorem G15Ram.tate_eq_one_of_torsFix (A : PkgI3.AbVar K) (ℓ) (σ : G_K)
    (h : ∀ n (P : A.Pt K̄), P ^ (ℓ ^ n) = 1 → A.galAct σ P = P) : G0Galois.tate A ℓ σ = 1
```

`tate_eq_one_of_torsFix` turns `TateWildK` and `TateWildKE` into the torsion-point Props
`TorsFixWild` and `TorsFixWildE`. That is the form in which PkgI2's leaves R6
(`PkgI2.RaynaudCriterion`) and D2 (`PkgI2.D2_fixed_of_raynaud`) are stated.

**Packs (VERIFIED).** `G0ModNewform.G8LocalPack` is the hypothesis of local-data's tail
`modularConstituent_tail_L`; it is copied verbatim here. `g8LocalPack_of_K` proves it from
`G7LocalPackK`, which consists of G7's data (`G7Out`), G8's output, `G7Clauses`, `KerWild` and
the torsion-point Props at the primes in question. `g15RamG_of_packK` then gives g15-ram's
`G15RamG D u`.

### The remaining named Props

Each is a `def … : Prop` in `part_glue.lean` with a docstring naming its step and source.

| Prop | primes | content | status |
|---|---|---|---|
| `KerWild K β L` | all | `g ∈ G_L`, `β(g) = 1` ⟹ `g ∈ G_K` | GLUE: g0-mod-field's `G7Data` clause `σ ∈ G_{L'} ↔ σ ∈ G_L ∧ β σ = 1`, transported to `G7Out`'s `K` and `ℚ̄_ℓ`-valued `β` |
| `TorsFixWild p A ℓ` ⟹ `TateWildK` | `p ≥ 7`, `p ≠ ℓ` | wild inertia at `p` in `G_K` fixes `A(K̄)[ℓⁿ]` | GLUE on the leaves **R6**, **I2-Tors** (and D2, proved from R6) |
| `TorsFixWildE p A ℓ β L` ⟹ `TateWildKE` | `p ∈ {2,3,5}`, `p ≠ ℓ` | some `E ⊇ L_v` with `[E:ℚ_p] ≤ G₀[L_v:ℚ_p]`: wild `σ ∈ G_E` has `β(σ) = 1` and fixes `A(K̄)[ℓⁿ]` | GLUE on **R6**, **I2-Tors** and the descent of `A` to `L` |
| `BetaUpper β L_v U₀` | `p = 2` | unchanged from local-data | GLUE on **T16** (`ZInQ.Contrib.localKroneckerWeber`), D3 and Herbrand |

None of these is a leaf. The leaves they rest on are in the bundles already.

## 2. What is proved

All rows are VERIFIED: `lake env lean scratch/local-glue/LocalGlue.lean` exits 0 with 0 errors
and no `sorry`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every printed
declaration.

| Lean | statement | proof idea |
|---|---|---|
| `not_localGlue_zero` | `D < p` ⟹ `¬ LocalGlue (Tm := 0) (a := 1) (β := 1) L` | `σ = 1` is wild and fixes `L` |
| `fixSet_Lv_of_fix`, `fixSet_Lv_iff` | `σ ∈ G_{L_v}` ⟺ `decomp σ ∈ G_L` | `decomp_spec`; `L_v ≤ fixedField(zpowers σ)`, via the stabilizer |
| `beta_wild_of_clauses` | odd `p`, `G7Clauses` ⟹ `β = 1` on wild `σ` with `decomp σ ∈ G_L` | local-data's `betaTame_of_odd` on `F = L_v` with `betaCharOn_of_cocycle`, `betaSqWild_of_chi`, `betaOpen_of_isLocallyConstant` |
| `aTm_eq_one_of_kerWild` | `g ∈ G_L`, `β g = 1`, Tate trivial on the preimage ⟹ `a_g Tm g = 1` | `KerWild` puts `g` in `G_K`, where `G7Out` has `Tm = tate`, `a = 1` |
| `localGlue_of_g7` | main result (§1) | at `p ≥ 7` the field of `TorsionFieldWild` is `L_v` itself; at `p > D ≥ 10¹²`, `p ≥ 7` |
| `tate_eq_one_of_torsFix` | fixing every `ℓⁿ`-torsion point ⟹ trivial on `ℚ̄_ℓ ⊗ V_ℓ(A)` | `T_ℓ` = compatible sequences of `ℓⁿ`-torsion points (`PkgI3.Tate.pow_smul_eq_zero`) |
| `tateWildK_of_torsFixWild`, `tateWildKE_of_torsFixWildE` | — | `tate_eq_one_of_torsFix` |
| `g8LocalPack_of_K`, `g15RamG_of_packK` | packs (§1) | `localGlue_of_g7`; local-data's `g15RamG_of_g7` |

## 3. Findings

- **G1 (VERIFIED, compiled).** `LocalGlue` is false for some data (`not_localGlue_zero`), so it
  cannot be proved as stated with free `Tm, a, β, L`.
- **G1' (SPECULATIVE, not formalized).** `LocalGlue` is not implied by `G7Out ∧ G8Out ∧ G7Clauses`
  either. These tie `a·Tm` to an abelian variety only on `G_K`, and nothing in them relates `K`
  to `L`. Example: `L = ℚ`, `A = E²` over a cyclic degree-`p` subfield `K ⊆ ℚ(ζ_{p²})`,
  `Tm = ψ ⊗ (Tate action of E²)` with `ψ` of order `p` and conductor `p²`, trivial on `G_K`. Then
  `a·Tm(σ) = ψ(σ) ≠ 1` for some wild `σ`. The missing link is `KerWild` (G7Data's kernel field
  clause).
- **G2 (VERIFIED, read).** g0-mod-field's `G7Data` (`scratch/g0-mod-field/ModField.lean`
  l.611-631) has the clause `σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1`. g0-mod-galois's `G7Out`
  (`scratch/g0-mod-galois/part_galois.lean` l.121-133) does not. With that clause:
  - at odd `p`, every wild inertia element of `G_L` lies in `G_{L'}`, since `β` is tame there
    (`beta_wild_of_clauses`);
  - so at every `p ≥ 7` the local glue is a statement about `A/L'` alone, and the descent datum
    on `G_L \ G_{L'}` is not needed.
- **G3 (VERIFIED, arithmetic).** At `p ∈ {2,3,5}` the descent datum of `A` to `L` cannot be
  avoided by this argument. For every `m ≥ 3`, `|GL₄(ℤ/m)|` is divisible by `2`, `3` and `5`
  (`q⁴ ≡ 1 mod 5` for `q ≠ 5`, and `GL₄(𝔽₅)` contains `5`-elements). So the argument cannot make
  `[L'_w(A[m]) : L'_w]` prime to `p`. Moreover `[L'_w : L_v]` is not bounded by `G₀`.
  Hence `TorsFixWildE` needs `A_L` with `A = (A_L)_{L'}`, as in Glazer (N5 L813-818).
- **G4 (VERIFIED, arithmetic).** At `p ≥ 7` a suitable `m` exists:
  - `m = 3`: `|GL₄(𝔽₃)| = 80·78·72·54 = 2⁹·3⁶·5·13`;
  - `m = 7` for `p = 13`: `|GL₄(𝔽₇)| = 2400·2394·2352·2058`, whose prime factors are
    `{2, 3, 5, 7, 19}`.

  So `TorsFixWild` needs no degree bound and no descent. Glazer's argument at `p ≤ D` uses
  `L_v(A[3])` of degree `≤ DG₀`; at `p ≥ 7` the field `L_v` itself suffices.

## 4. What remains

1. `TorsFixWild` (`p ≥ 7`), on R6 and I2-Tors. The steps are:
   - the bridge from the number field `K` at the place of `embP` (`resQ`, `decomp`, `wildSet`) to
     PkgI2's valuation-ring setting (a DVR of `K(A[m])` and a valuation ring of `K̄` over it);
   - the base change of `A` to `K(A[m])`;
   - `K̄`-points have open stabilizers.
2. `TorsFixWildE` (`p ∈ {2,3,5}`): the same as item 1, plus a model `A_L` with `A = (A_L)_{L'}`
   and the degree bound on `L_v(A_L[m])`.
3. `KerWild`: the transport of G7Data to G7Out (also local-data's F3/F5).
4. `BetaUpper` at `p = 2`: as in local-data §4.2.
