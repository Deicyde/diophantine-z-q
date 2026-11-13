# local-glue: `LocalGlue p Tm a β L` (local-data) on G7's data

Task local-glue, 2026-11-13.

Lean: `scratch/local-glue/LocalGlue.lean`, assembled by `scratch/local-glue/build.sh` from:
- a verbatim copy of `scratch/local-data/LocalData.lean`, which contains `LocalGlue` and
  everything it depends on;
- a verbatim block of `scratch/g0-mod-galois/part_galois.lean` (`galois_block.lean`);
- the new parts `part_glue.lean` (§6-§7), `part_ptfinite.lean` (§7b) and `part_pack.lean` (§8).

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
theorem G15Ram.localGlue_of_g7_twist {K} [Field K] [NumberField K] {A : PkgI3.AbVar K}
    {Tm c ε a β u} (h7 : G0Galois.G7Out A ℓ Tm c ε a β u) {L : IntermediateField ℚ Qbar}
    (hC : G7Clauses β ε L) (hK : KerWild K β L)
    (hW : 7 ≤ p → TateWildK (p := p) A ℓ) (hE : p ≤ 5 → TateWildKE (p := p) A ℓ β L)
    (hB : p = 2 → BetaTwist2 (p := p) β L) :
    LocalGlue (p := p) Tm a β L
```

(`localGlue_of_g7` is the same with local-data's `BetaUpper` in place of `BetaTwist2`.)

**At every `p ≥ 7`, `p ≠ ℓ`, the local glue rests on the leaves alone, through one bridge Prop
(VERIFIED):**

```
theorem G15Ram.tateWildK_of_raynaud (hℓp : ℓ ≠ p) (h7 : 7 ≤ p)
    (hTors : ObjBridge.TorsionStructure) (hdim : A.dim = 2)
    (hR3 : p ≠ 13 → RaynaudPlace (p := p) A 3) (hR7 : p = 13 → RaynaudPlace (p := p) A 7) :
    TateWildK (p := p) A ℓ
```

Here `ObjBridge.TorsionStructure` is the leaf **I2-Tors**, `dim A = 2` is a clause of `G7Out`,
and `RaynaudPlace` is the instance of the leaf **R6** (Raynaud's criterion) at the place of
`embP`. The proof:
- take `m = 3`, or `m = 7` when `p = 13`; then `p ∤ |GL₄(𝔽_m)|`, computed in Lean from Mathlib's
  `Matrix.card_GL_field`;
- a wild `σ'` has `p`-power period on every point of `A(K̄)` (`wildIter`). This is proved from
  `ptFinite`: `K̄`-points are defined over finite extensions, by Mathlib's Stacks 01ZC;
- so `σ'` acts trivially on `A[m] ≅ (ℤ/m)⁴`;
- Raynaud gives `(σ'−1)² = 0` on `A[ℓⁿ]`, and with a `p`-power period this forces `σ' = 1` (D2);
- `tate_eq_one_of_torsFix` passes from torsion points to `ℚ̄_ℓ ⊗ V_ℓ(A)`.

**At `p = 2`, T16 is not needed (VERIFIED, finding G6).** `betaUpper_of_twist` proves
local-data's `BetaUpper` from a small field-theoretic Prop `BetaTwist2`: some `M ⊇ L_v` with
`[M:L_v] ≤ 4` has `β = 1` on wild inertia of `G_M`. The proof uses the degree-based break bound
already proved for G15 (`UpperBreakFix`, from T20 + T21); it uses no local reciprocity, no D3 and
no Herbrand function.

**Packs and tail (VERIFIED).**
- `G0ModNewform.G8LocalPack` is the hypothesis of local-data's tail `modularConstituent_tail_L`;
  it is copied verbatim here.
- `g8LocalPack_of_K` proves it from `G7LocalPackK`, which consists of:
  - G7's data (`G7Out`) and G8's output;
  - `G7Clauses` and `KerWild`;
  - at the primes in question, `TorsFixWild` (`p ≥ 7`), `TorsFixWildE` (`p ≤ 5`) and `BetaUpper`
    (`p = 2`).
- `G7LocalPackR` is the leaf-and-bridge form. Its local clauses are:
  - at `p ≥ 7`: `RaynaudPlace A 3` (`p ≠ 13`), resp. `RaynaudPlace A 7` (`p = 13`);
  - at `p ∈ {3,5}`: `TorsFixWildOdd`;
  - at `p = 2`: `TorsFixWildE` and `BetaTwist2`.
- `g7LocalPackK_of_R` turns `G7LocalPackR` into `G7LocalPackK`, given the leaf I2-Tors and
  `p ≠ ℓ`.
- `g15RamG_of_packK` and `g15RamG_of_packR` give g15-ram's `G15RamG D u`.
- In `TailK.lean`, `modularConstituent_tail_K` and `modularConstituent_tail_R` are
  g0-mod-newform's tail (G13-G16) on these packs.

### The remaining named Props

Each is a `def … : Prop` in `part_glue.lean` with a docstring naming its step and source. None
is a leaf. The leaves they rest on (in **bold**) are in the bundles already.

| Prop | primes | content | status |
|---|---|---|---|
| `KerWild K β L` | all | `g ∈ G_L`, `β(g) = 1` ⟹ `g ∈ G_K` | GLUE: g0-mod-field's `G7Data` clause `σ ∈ G_{L'} ↔ σ ∈ G_L ∧ β σ = 1`, transported to `G7Out`'s `K` and `ℚ̄_ℓ`-valued `β` (with local-data's F3/F5) |
| `RaynaudPlace p A m` (`m = 3`, `p ≠ 13`; `m = 7`, `p = 13`) | `p ≥ 7` | a wild `σ' ∈ G_K` fixing `A(K̄)[m]` has `(σ'−1)² = 0` on `A(K̄)[ℓⁿ]`, `ℓ ≠ p` | GLUE on **R6** (`PkgI2.RaynaudCriterion`). Needed: R6 at a DVR of `K(A[m])` and a valuation ring of `K̄` over it, and the base change of `A` to `K(A[m])` |
| `TorsFixWildOdd p A ℓ L` | `p ∈ {3,5}`, `p ≠ ℓ` | some `E ⊇ L_v`, `[E:ℚ_p] ≤ G₀[L_v:ℚ_p]`: wild `σ ∈ G_E` fixes `A(K̄)[ℓⁿ]` | GLUE on **R6**, **I2-Tors** and the descent `A = (A_L)_{L'}` (finding G3) |
| `TorsFixWildE p A ℓ β L` | `p = 2`, `ℓ ≠ 2` | the same, and `β(σ) = 1` | as above |
| `BetaTwist2 β L` (⟹ `BetaUpper`) | `p = 2` | some `M ⊇ L_v`, `[M:ℚ_2] ≤ 4[L_v:ℚ_2]`, with `β = 1` on wild `σ ∈ G_M` | GLUE with no leaf (see below) |

How `BetaTwist2` is proved:
- `β⁴ = χ²` is unramified at `2`;
- an unramified `η` with `η⁴ = β⁴` exists, because `G_{L_v}/I` is procyclic;
- `M` is the kernel field of `βη⁻¹`.

Proved and no longer open:
- `PtFinite` and `WildIter` (`ptFinite`, `wildIter`);
- `TorsFixWild` and `TateWildK` at `p ≥ 7`, from I2-Tors and `RaynaudPlace`;
- `TorsGL`, from I2-Tors;
- `BetaUpper` at `p = 2`, from `BetaTwist2`.

## 2. What is proved

All rows are VERIFIED: `lake env lean scratch/local-glue/LocalGlue.lean` exits 0 with 0 errors
and no `sorry`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all 52 printed
declarations (27 from `LocalData.lean`, 25 new).

| Lean (`G15Ram` unless noted) | statement | proof idea |
|---|---|---|
| `not_localGlue_zero` | `D < p` ⟹ `¬ LocalGlue (Tm := 0) (a := 1) (β := 1) L` | `σ = 1` is wild and fixes `L` |
| `fixSet_Lv_of_fix`, `fixSet_Lv_iff` | `σ ∈ G_{L_v}` ⟺ `decomp σ ∈ G_L` | `decomp_spec`; `L_v ≤ fixedField(zpowers σ)` via the stabilizer |
| `beta_wild_of_clauses` | odd `p`, `G7Clauses` ⟹ `β = 1` on wild `σ` with `decomp σ ∈ G_L` | local-data's `betaTame_of_odd` on `F = L_v` |
| `aTm_eq_one_of_kerWild` | `g ∈ G_L`, `β g = 1`, Tate trivial over `g` ⟹ `a_g Tm g = 1` | `KerWild` puts `g` in `G_K`, where `G7Out` has `Tm = tate`, `a = 1` |
| `localGlue_of_g7`, `localGlue_of_g7_twist` | main result (§1) | at `p ≥ 7` the field of `TorsionFieldWild` is `L_v` itself; `p > D ≥ 10¹²` gives `p ≥ 7` |
| `tate_eq_one_of_torsFix` | fixing every `ℓⁿ`-torsion point ⟹ trivial on `ℚ̄_ℓ ⊗ V_ℓ(A)` | `T_ℓ` = compatible sequences of `ℓⁿ`-torsion points |
| `tateWildK_of_torsFixWild`, `tateWildKE_of_torsFixWildE`, `torsFixWildE_of_odd` | — | `tate_eq_one_of_torsFix`; `beta_wild_of_clauses` |
| `iterate_card_GL_fix` | `φ` injective, `φ(S) ⊆ S`, `S ≅ (ℤ/q)ⁿ` as groups ⟹ `φ^[‖GLₙ(𝔽_q)‖] = id` on `S` | `Matrix.GeneralLinearGroup.toLin`, `pow_card_eq_one'` |
| `card_GL4_three`, `card_GL4_seven`, `coprime_card_GL4_three`, `coprime_card_GL4_seven` | `‖GL₄(𝔽₃)‖ = 24261120 = 2⁹3⁶·5·13`; `13 ∤ ‖GL₄(𝔽₇)‖` | `Matrix.card_GL_field`, `norm_num` |
| `fixed_of_unipSq_of_iterate'` | `(σ−1)²x = 0`, `ℓⁿx = 0`, `σ^{qᵃ}x = x`, `(qᵃ, ℓⁿ) = 1` ⟹ `σx = x` | D2's core, as `PkgI2.fixed_of_unipSq_of_iterate`, on PkgI3 points |
| `torsGL_of_leaf` | I2-Tors and `dim A = 2` ⟹ `A(K̄)[m] ≅ (ℤ/m)⁴` | the leaf applied to `ObjBridge.toGrp A`; its torsion set is defeq to PkgI3's |
| `fix_torsion_of_coprime`, `torsFixWild_of_raynaud`, `tateWildK_of_leaves(')` | §1 | periods `pᵃ` and `‖GL₄‖` are coprime (`IsPeriodicPt.gcd`) |
| `qEmbRing_surjective` | `ℚ̄ → K̄` is onto | `IsAlgClosed.ringHom_bijective_of_isIntegral` |
| `wild_pow_fix_elem`, `wild_pow_fix_field`, `wildIter_of_ptFinite` | a wild `σ'` has `p`-power period on each `x ∈ K̄`, on each finite `F/K`, on each point | `exists_pow_fix_of_wild` on the normal closure of `ℚ_p(embP y)`; a basis of `F` |
| `fRingCoconeIsColimit`, `fSpecConeIsLimit`, **`ptFinite`**, `wildIter`, `tateWildK_of_raynaud` | `K̄ = colim F`; `Spec K̄ = lim Spec F`; every `P ∈ A(K̄)` is fixed by `G_F`, `F/K` finite | Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation` (Stacks 01ZC); construction as in scratch/morph-descend |
| `betaUpper_of_twist` | `G7Clauses`, `BetaTwist2` ⟹ `BetaUpper β L_v U₀` | `exists_finGal_ramCard_le`, `UpperBreakFix` (proved), `upperWild` |
| `G0ModNewform.g8LocalPack_of_K`, `g15RamG_of_packK`, `g7LocalPackK_of_R`, `g15RamG_of_packR` | packs (§1) | the above |
| `G0ModNewform.modularConstituent_tail_K`, `modularConstituent_tail_R` (`TailK.lean`) | the tail of G13-G16 on `G7LocalPackK`, resp. `G7LocalPackR` with I2-Tors | local-data's `modularConstituent_tail_L` |

## 3. Findings

- **G1 (VERIFIED, compiled).** `LocalGlue` is false for some data (`not_localGlue_zero`), so it
  cannot be proved as stated with free `Tm, a, β, L`.
- **G1' (SPECULATIVE, not formalized).** `LocalGlue` is not implied by `G7Out ∧ G8Out ∧ G7Clauses`
  either. These tie `a·Tm` to an abelian variety only on `G_K`, and nothing in them relates `K`
  to `L`.
  - Example: `L = ℚ`, `A = E²` over a cyclic degree-`p` field `K ⊆ ℚ(ζ_{p²})`, with `E/ℚ` without
    CM and of good reduction at `p > D`.
  - Take `Tm = ψ ⊗ (Tate action of E²)`, with `ψ` of order `p` and conductor `p²`, trivial on
    `G_K`; `a = β = 1`, `ε = 1`.
  - Then `a·Tm(σ) = ψ(σ) ≠ 1` for some wild `σ`.

  The missing link is `KerWild` (G7Data's kernel field clause), which fails in this example.
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
  - So `TorsFixWildOdd` and `TorsFixWildE` need a model `A_L` with `A = (A_L)_{L'}` and
    `E = L_v(A_L[m])`, as in Glazer (N5 L813-818).
  - At `p = 2`, `E` must also contain `BetaTwist2`'s `M`.
- **G4 (VERIFIED, compiled).** At `p ≥ 7`, `m = 3` (`p ≠ 13`) or `m = 7` (`p = 13`) has
  `p ∤ |GL₄(𝔽_m)|`. So `TateWildK` needs no degree bound and no descent: Glazer's `L_v(A[3])` of
  degree `≤ DG₀` can be replaced by `L_v` itself at those primes.
- **G5 (VERIFIED, compiled).** The PkgI2 leaf I2-Tors applies directly to the PkgI3 abelian
  variety through `ObjBridge.toGrp`. The torsion subset and the group law agree definitionally
  (`torsGL_of_leaf` is `⟨e, he⟩` from the leaf), so no transport is needed for torsion. R6 is
  different: it needs a base change and a change of valuation-theoretic setting.
- **G6 (VERIFIED, compiled). T16 is not needed for G15 at `p = 2`.** local-data's `BetaUpper`
  (Glazer's route) bounds the conductor of `β|G_F` by local reciprocity: T16, D3
  `(U^{e+1})⁴ = U^{3e+1}`, then Herbrand's `ψ ≥ id`. Instead, `betaUpper_of_twist` uses:
  - the degree-`≤ 4` field `M` of `BetaTwist2`;
  - the degree-based break bound already proved for G15 (`UpperBreakFix`, from T20 + T21 through
    `hilbertSerre_of_model` and `ladicDVRModelZp`), applied to the Galois closure of `M`
    (`[M:ℚ_2] ≤ 4D ≤ DG₀`, so `e ≤ (DG₀)!` and `G^t ⊆ G_M` for `t > U₀`);
  - `upperWild`.

  The bound `U₀ = 4(DG₀)²` is unchanged. The mathematics of `BetaTwist2` is standard: unramified
  characters factor through the procyclic `G_F/I_F` (Serre, *Local Fields*).
- **G7 (VERIFIED, logical; fixed).** A first version of `G7LocalPackR` required
  `RaynaudPlace A 7` at every `p ≥ 7`, including `p = 7`. There `m = p` and Raynaud's criterion does
  not apply, so the pack could have been unsatisfiable. It now requires `m = 3` for `p ≠ 13` and
  `m = 7` only for `p = 13`. The docstring of `RaynaudPlace` restricts the claim to `m` prime to
  `p`.

## 4. What remains

1. `RaynaudPlace p A m` (`p ≥ 7`): apply R6 to `K' = K(A[m])` (finite over `K` by `ptFinite`
   and I2-Tors). This needs:
   - the valuation subring of `K'` at the place of `embP` (a DVR);
   - a valuation ring `w` of `AlgebraicClosure K' ≅ K̄` over it, with the wild `σ'` in its inertia
     group (LadicCond's `wildSet_subset_inertiaSet`, transported);
   - `A_{K'}` (`PkgI2.baseChange`) and an equivariant identification of its torsion points with
     those of `A`.
2. `TorsFixWildOdd`, `TorsFixWildE` (`p ∈ {2,3,5}`): item 1 for a model `A_L` over `L`, plus:
   - the descent datum on `G_L` (g0-mod-field's `DescentDatum`, transported to `ℚ̄_ℓ ⊗ V_ℓ`);
   - the degree bound `[L_v(A_L[m]) : L_v] ≤ |GL₄(𝔽_m)|`.
3. `KerWild`: the transport of G7Data to G7Out (also local-data's F3/F5).
4. `BetaTwist2` at `p = 2`:
   - inertia at `2` fixes the roots of unity of odd order (local-data's `wild_fix_root` covers
     wild inertia only), so `χ²` is unramified;
   - unramified characters of `G_{L_v}` factor through `G_{L_v}/I` and have 4th roots;
   - the kernel field of a character of order dividing 4 has degree `≤ 4`.

## 5. Compile record

- `lake env lean scratch/local-glue/LocalGlue.lean`: exit 0, 0 errors, no `sorry`, about 25 s.
  All 52 `#print axioms` lines are `[propext, Classical.choice, Quot.sound]` (`compile.out`).
- `lake env lean scratch/local-glue/TailK.lean`: exit 0, 0 errors, no `sorry`, about 50 s.
  `modularConstituent_tail_K` and `modularConstituent_tail_R` have axioms
  `[propext, Classical.choice, Quot.sound]` (`tail_compile.out`).
- Building first required `lake build` of the imports of `LocalData.lean` and of local-data's
  `Tail.lean`. Both files also import `Mathlib.AlgebraicGeometry.AffineTransitionLimit` (added
  first by the build scripts).
- Verbatim copies (VERIFIED by construction: `cat`/`sed -n` in the build scripts):
  - `scratch/local-data/LocalData.lean` (whole) and `Tail.lean` (whole);
  - `scratch/g0-mod-galois/part_galois.lean` l.40-58;
  - `G8LocalPack` from `scratch/local-data/tail_part.lean`, between the `BEGIN`/`END verbatim
    copy` markers of `part_pack.lean`.
