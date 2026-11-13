# linked-tate: `ModelG3G6` and `LinkedTateData` reduced; the linked Tate data are constructed

Task linked-tate, 2026-11-13. Lean: `scratch/linked-tate/` (results log `log.md`). The flat file
`LinkedTate.lean` is assembled by `assemble.sh` from three pieces:
- `Leaves.lean`, a byte-identical copy of the pin-applied `scratch/h-decomposition/Leaves.lean`;
- the three non-HDecomp kernel imports in `imports_extra.txt`;
- the parts in `scratch/linked-tate/parts/`.

The iteration file `olean/Tail.lean` compiles against an olean of that prefix
(`build_prefix.sh`, `ctail.sh`), as g0-assemble did.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = model judgement. **UNVERIFIED** = theorem number recalled without a source (no
network). Model work only; no human review.

## 0. Main result

**Both joint glue Props of g0-assemble are proved from strictly smaller named Props, over
`Leaves.lean`'s definitions. Neither statement is changed.**

- `ModelG3G6` (copied verbatim from `scratch/g0-assemble/parts/87_afterg7.lean`) is proved from:
  - `FibreSimple` (already a `GluePieces` field);
  - one new glue Prop, `GoodRedG3Bridge`;
  - the leaves R6, R7a and T5.

  The noncommutativity half of G6 needs no input.
- `LinkedTateData` (copied verbatim from the same part) is proved from:
  - the leaves T7 and I3.M0 (= T26);
  - `FibreSimple`;
  - three new glue Props, `QMEndRank`, `LinkedFrob` and `LinkedRam`.

  The ℓ = 5 and ℓ = 3 operator data are constructed. They are unram-tate's Tate-functor
  construction, run once with one scalar function `γ₀ : G_ℚ → ℚ̄`. So the scalar link that
  g14-trace found missing (its finding F1) now holds by construction, and it is no longer glue.

```lean
theorem HSyn.LinkedTate.modelG3G6_of (hFS : HSyn.G0Split.FibreSimple) (hG3 : QMModelG3) :
    HSyn.G0AssembleMod.ModelG3G6
theorem HSyn.LinkedTate.qmModelG3_of (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : PkgI2.RaynaudCriterion.{0}) (hTors : PkgI2.TorsionStructure.{0})
    (hB : GoodRedG3Bridge) : QMModelG3
theorem HSyn.LinkedTate.linkedTateData_of_frobRam (hM : PkgI3.CharPolyIndepOfEll)
    (hT : PkgI3.TateModuleFree) (hFS : HSyn.G0Split.FibreSimple) (hR : QMEndRank)
    (hFR : UnramTate.LinkedFrobRam) : HSyn.G0AssembleMod.LinkedTateData
theorem UnramTate.linkedFrobRam_of (hF : LinkedFrob) (hR : LinkedRam) : LinkedFrobRam
theorem HSyn.LinkedTate.afterG7_of_final (r t m hDF hCar hSw hL8 hAd)
    (hFS : FibreSimple) (hB : GoodRedG3Bridge) (hR : QMEndRank)
    (hF : UnramTate.LinkedFrob) (hRam : UnramTate.LinkedRam) : G0ModField.AfterG7
```

The last theorem is g0-assemble's `afterG7_of` with its two fields `modelG3G6` and
`linkedTateData` replaced by the five glue Props above. The leaves come from the bundles: R6,
R7a and T5 for G3, and T7 and T26 for G14 and the Tate data.

**VERIFIED** (Lean 4.35.0, Mathlib v4.35.0):
- `olean/Tail.lean` against the prefix olean gives 0 errors and no `sorry`. Every `#print axioms`
  of a new declaration gives `[propext, Classical.choice, Quot.sound]`, as does the copied
  `G0AssembleMod.afterG7_of` and `UnramTate.tateBridge_of_tateModuleFree`.
- The flat file is reported in §6.

## 1. The statements (copied, unchanged)

`ModelG3G6`: for every fibre context `FibreCtx Y Φ π u P` and all G7 data
`G7Data u P L A ε N χ β L' hLL'`, the model `A' = A_{L'}` satisfies three things:
- `G0Galois.G6Out A'`: `EndDivision A'`, and `End(A')` is not commutative;
- `G0Galois.G3Out A' 5 (T u)`;
- `G0Galois.G3Out A' 3 (T u)`.

`LinkedTateData`: for the same data there exist operator data
`(Tm_ℓ, c_ℓ, ε_ℓ, a_ℓ, β_ℓ, u_ℓ)` at `ℓ = 5` and `ℓ = 3`. They satisfy `G0Galois.G7Out` at both
primes. Moreover, for all `r₅`, `r₃` with G8's output `G8Out … (rho Tm_ℓ a_ℓ β_ℓ) r_ℓ`, and all
`i`, `ι_ℂ`, `ι₅`, some `ι₃` gives `G14TraceCompat ⟨i, ι_ℂ, ι₅, ι₃, r₅, r₃⟩` and `G15RamWild` of
the same data.

Both are read over the pin-applied `Leaves.lean`. There `FibreCtx` contains `R1fpProps`, which
pin-apply strengthened by `R1famProps` and `R1univProps`.

## 2. Named Props: leaf or glue

| Prop | kind | content | used for |
|---|---|---|---|
| `PkgI2.NeronOggShafarevich` (R7a), `PkgI2.RaynaudCriterion` (R6), `PkgI2.TorsionStructure` (T5) | **leaf** (bundle fields `r.r7a`, `r.r6`, `t.t5`) | Serre–Tate 1968 Thm 1; Raynaud's criterion; Mumford §4 | G3, through `LeafQM.AV.QML3.goodReduction` (proved in `Leaves.lean`) |
| `PkgI3.CharPolyIndepOfEll` (T7) | **leaf** (`t.t7`) | Mumford §19 Thm 4 | G14 |
| `PkgI3.TateModuleFree` (I3.M0 = T26) | **leaf** (`t.t26`) | Mumford §18-19 | continuity clause of `G7Out` (unram-tate's `tateCont_of_tateModuleFree`) |
| `HSyn.G0Split.FibreSimple` | glue (existing `GluePieces` field 4; g0-fibresimple reduced it to leaves, FS1b and FS5; pin-apply made it independent of the triple, given `MobiusGlue`) | every number-field model of the fibre over `J(u)` has `EndDivision` | `EndDivision` half of G6, and the hypothesis of `QMEndRank` |
| `HSyn.LinkedTate.GoodRedG3Bridge` | **glue (new)** | Given NOS: if `A/K` has good reduction at every DVR of `K` in which 3 is a unit, then inertia of `G_{L'}` above `p ∉ {3, ℓ}` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A_{L,L'})`. | G3 |
| `HSyn.LinkedTate.QMEndRank` | **glue (new, literature-backed)** | For a `QML3` object over `K ≤ L ≤ L'` with `EndDivision`, `rank_ℤ End(A_{L,L'}) = 4`. | the `rank = 4` conjunct of `G7Out` |
| `UnramTate.LinkedFrob` | **glue (new)** | g14-trace's `FrobTraceLink` for the canonical operators `tmOf … 5`, `tmOf … 3`, for every transport `(Θ, h)` and every points-level descent datum `(m, a, n, d)` | G14 |
| `UnramTate.LinkedRam` | **glue (new)** | `RhoRamWild` (clauses (i)-(ii) of `LocalRam`, for the descended operator `ρ_ℓ` itself) for `ρ₅` at `p ≠ 5` and `ρ₃` at `p = 5`, built from the canonical operators, for every choice of the data | G15 clauses (i)-(ii) |

Intermediate named Props, all proved from the rows above:
- `QMModelG3`: G3 on base changes of `QML3` objects;
- `LinkedTateCore`;
- `LinkedTateCoreDR` (`LinkedTateCore` assuming `dim = 2` and `rank = 4`, as g0-mod-field's
  `TateBridge` does);
- `LinkedFrobRam` (the conjunction of `LinkedFrob` and `LinkedRam`).

No new literature leaf is introduced.

## 3. `ModelG3G6` (proved from `FibreSimple`, `GoodRedG3Bridge`, R6, R7a, T5)

`G7Data`'s `IsQMModel L A P` gives `A = (PK.A)_L` for a `QML3` object `PK` over some `K ≤ L`. So
`A' = (PK.A)_{L,L'}`.

1. **`EndDivision A'`** (`endDivision_of_fibreSimple`). `G7Data`'s last clause, `IsModelOver L' A' P`,
   together with the fibre context, is `FibreOver Y Φ π u ⟨L'⟩ ((abVarEquiv L').symm A')`, using
   the inclusion `L' ⊆ ℚ̄`. `FibreSimple` then gives the result, and `abVarEquiv` is the identity
   on the data. VERIFIED.
2. **`End(A')` is not commutative** (`noncomm_baseChange2`, no input). bp-qmmoduli's `endBC`
   (`Over.pullback` on morphisms) is an injective ring map; injectivity is Mathlib's flat-descent
   faithfulness of `Over.pullback` along `Spec L → Spec K`. The QM structure `ι : 𝒪 → End(PK.A)`
   is also injective. In `𝒪`, `i·(1+j)/2 ≠ (1+j)/2·i`: the `k`-coordinates are `1/2` and
   `−1/2` (`oI_oH_ne`). So the images under `endBC ∘ endBC ∘ ι` do not commute. VERIFIED.
3. **G3.** `3 ∈ T u` because `3 ∈ S_mul`, and `G3Out` is monotone in `T`. So it suffices to have
   `G3Out A' ℓ {3}` (`QMModelG3`). Leaves.lean's proved `LeafQM.AV.QML3.goodReduction` (from R7a,
   R6 and T5) gives good reduction of `PK.A` at every DVR with 3 a unit (`qmModelG3_of`), and
   `GoodRedG3Bridge` converts that into `G3Out`. VERIFIED.

**`GoodRedG3Bridge` is true** (STANDARD route). For a place `v` above `p ≠ 3`, `v ∩ K` is a DVR in
which 3 is a unit. NOS (a) ⇒ (b) over `K` makes inertia trivial on every `A[ℓⁿ](K̄)`. Inertia of
`G_{L'}` restricts into inertia of `G_K`. Triviality on all `A[ℓⁿ]` gives triviality on `T_ℓ`, and
so on `ℚ̄_ℓ ⊗ V_ℓ`. Base change does not change the points over `K̄ = \bar{L'}` (unram-tate's
`bcPt`).

What is open is only the transport between PkgI2's torsion points and valuation rings of `K̄` and
the places and `resQ` of `G0Galois.G3Out`. It needs no new literature.

## 4. `LinkedTateData`

### 4.1 G14 and G15 from the descended operators (proved: `linkedTateData_of`)

Suppose the operator data have scalars `a_ℓ = j_ℓ ∘ a` and `β_ℓ = j_ℓ ∘ β` for one pair
`a, β : G_ℚ → ℚ̄`, and satisfy `FrobTraceLink` and `RhoRamWild`. This is `LinkedTateCore`. Then:
- **G14.** Given `ι₅`, write `ι₅ = j₅ ∘ γ` (g14-trace's `exists_comp_eq`) and set
  `ι₃ := j₃ ∘ γ`. g14-trace's `g14TraceCompat_of_link` (from T7, copied verbatim as part 93, with
  the kernel's `FrobCompare` and `trace_T_of_frobCompare` copied as part 92) gives
  `G14TraceCompat` for every `r₅`, `r₃` with G8's output.
- **G15.** G8's `e` intertwines `ρ_ℓ` with `r_ℓ ⊕ r_ℓ` on all of `G_ℚ`. So `ρ_ℓ(g) = 1` implies
  `r_ℓ(g) = 1` (`toHom_eq_one_of_intertwines`: `M·x = x` for all `x`, hence `M = 1`). This turns
  `RhoRamWild p ρ_ℓ` into `LocalRamWild p r_ℓ` (`localRamWild_of_rho`).

VERIFIED.

### 4.2 `dim` and `rank` (proved: `linkedTateCore_of`)

`G7Out` asks `dim A' = 2` and `rank_ℤ End(A') = 4` without hypotheses, while `TateBridge` assumed
both.
- `dim A' = 2` is proved from `PK.surface` and g0-dim's `pkgI3_dim_baseChange`, applied twice
  (part 10 copied).
- `rank = 4` is `QMEndRank`, applied with `EndDivision A'` from `FibreSimple`.

The rest is `LinkedTateCoreDR`.

**`QMEndRank` is true** (STANDARD route, numbering UNVERIFIED):
- `End(A')` is finitely generated and torsion-free (Mumford §19 Thm 3), so it is free.
- `End⁰(A')` is a division algebra (`EndDivision`) and contains `ι(B)`, `B = (2,−3)`, of
  dimension 4.
- For a simple abelian surface in characteristic 0, `[End⁰ : ℚ]` divides 4 (Albert, Mumford §21).
  So `End⁰ = B` and the rank is 4.

It is literature-backed glue, not a leaf, because Albert's classification is not stated in the
bundle.

### 4.3 The linked data are constructed (proved: `UnramTate.linkedTateCoreDR_of`)

unram-tate proved `TateBridge` separately for each `ℓ`. Its file
(`scratch/unram-tate/TateBridge.lean`, lines 1038-1825) is copied verbatim as part 96 and compiles
over `Leaves.lean`: `UnramTate.tateBridge_of_tateModuleFree`, VERIFIED.

Part 97 runs its assembly once for both primes with the same data:
- unram-tate's transport `(Θ, h)` (`tatePoints`);
- the descent datum `m`, `a`, `n/d` of `G7Data`;
- the canonical operators `tmOf … ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`.

The scalars are `a = 1` and `β' g = γ₀(hgh⁻¹)`, where `γ₀ : G_ℚ → ℚ̄` comes from `scalarTransferQ`.
That is unram-tate's `scalarTransfer` with the target `ℚ̄_ℓ` replaced by `ℚ̄`; the proof is
unchanged. The embeddings are `j_ℓ = IsAlgClosed.lift : ℚ̄ → ℚ̄_ℓ`.

The `G7Out` proof is unram-tate's `tateBridge_of_pieces`, changed in three places only:
- `a' = j ∘ 1`;
- `β' = j ∘ γ₀ ∘ cj`;
- `∂β' = n/d` obtained by applying `j` to `∂γ₀ = n/d`.

The remaining two conjuncts, `FrobTraceLink` and `RhoRamWild`, refer to the constructed operators.
They are therefore stated for the canonical operators and every choice of the data the
construction uses (`LinkedFrob`, `LinkedRam`), and then applied to the choice made. VERIFIED.

**Why `LinkedFrob` and `LinkedRam` are true** (SPECULATIVE in their Lean details).
- **`LinkedFrob`** is g14-trace's argument (N5 L777-786). At a Frobenius `τ` above
  `p ∉ T ∪ {3, 5} ∪ ram(L')`, `m_{hτh⁻¹}` is `μ ∘ (Frobenius)` on points, and it is algebraic
  (`DescentDatum`'s clause `F_σ`). With the Serre–Tate reduction isomorphism, `N·Tm_ℓ(τ)` becomes
  `V_ℓ(α')` for one `α' = N μ̄ ∘ F` on the reduction, the same for `ℓ = 3` and `5`.
- **`LinkedRam`** is Glazer's D1-D4 (N5 L819-852), and it is quantified over every choice of the
  data. Every choice gives Glazer's `ρ_ℓ` up to conjugation and up to a twist by a character of
  `Gal(L'/ℚ)` (derivation below). So `LinkedRam` says: D1-D4 hold for every such twist. Two facts
  about `L'` make that plausible:
  - **Clause (ii), `p > D`.** `L'` is tamely ramified at `p`: `[L:ℚ] ≤ D < p`, and
    `L'/L` is cyclic, cut out by `β|_{G_L}` with `β² = χ`, so `β|_{I_p}` has order dividing
    `2(p−1)`. Hence a character of `Gal(L'/ℚ)` is trivial on wild inertia.
  - **Clause (i), `p ≤ D`.** It needs the upper breaks of `L'` at `p` to be `≤ U₀ = 4(D G₀)²`.
    These breaks come from `L` and `β`, which are exactly what D1 and D3 bound
    (`GlueConductor.D1_genuine`, `fourth_pow_mem`). SPECULATIVE: this is the one point of
    `LinkedRam` to review.

  Derivation of the conjugation-and-twist claim:
  - Changing `(Θ, h)` conjugates `ρ_ℓ`, and `ρ_ℓ(kxk⁻¹) = 1 ⟺ ρ_ℓ(x) = 1`.
  - Two descent data `m, m'` for `ε` satisfy `m' = q·m` with `q : G_ℚ → ℚ^×`. The reason is that
    `m'_σ m_σ⁻¹` commutes with `End⁰ = B`, whose centralizer is `ℚ`. Moreover `q = 1` on `G_L`.
  - Two choices of `γ₀` differ by a function `ψ` with `∂ψ = 1`, `ψ = 1` on `G_{L'}` and `ψ`
    constant on `G_{L'}`-cosets, which is a character of `Gal(L'/ℚ)`.
  - In both cases the ratio of the two `ρ_ℓ` is a character of `G_ℚ` trivial on `G_{L'}`.

## 5. Findings

- **The scalar link is constructible.** g14-trace's F1 (`TateBridge` ties neither the `ℓ = 3`
  data to the `ℓ = 5` data nor either to `β`) is resolved by construction, not by a new glue Prop.
  One `γ₀ : G_ℚ → ℚ̄` and the same `(Θ, h, m)` serve both primes, and every `G7Out` clause is
  proved. VERIFIED.
- **`G7Out` asks more than `TateBridge` provides.** `LinkedTateData` asks `dim A' = 2` and
  `rank_ℤ End(A') = 4` outright, while `TateBridge` assumes them. The rank needs NoCM on the model
  (via `FibreSimple`) and Albert's classification (`QMEndRank`). VERIFIED by reading the
  statements.
- **No statement is false, vacuous or inert.** `ModelG3G6`'s G6 half has real content
  (`EndDivision` is `FibreSimple`'s), and its noncommutativity half is a theorem.
- **The last step of G15 can be stated on `ρ_ℓ`.** `G15RamWild` for every `r_ℓ` with G8's output
  is equivalent to `RhoRamWild` for `ρ_ℓ`; the forward direction is proved here.

## 6. What compiles

- `scratch/linked-tate/olean/Tail.lean` (`import LPrefix` + parts 10, 70, 72, 74, 75, 77, 87, 92,
  93, 95, 96, 97), compiled against the olean of `Leaves.lean` + `imports_extra.txt`: VERIFIED.
  It gives exit 0, 0 errors and no `sorry`. All axiom reports of the new declarations are
  standard. The declarations:
  - `HSyn.LinkedTate`: `oI_oH_ne`, `noncomm_baseChange2`, `endDivision_of_fibreSimple`,
    `qmModelG3_of`, `modelG3G6_of`, `toHom_eq_one_of_intertwines`, `localRamWild_of_rho`,
    `linkedTateCore_of`, `linkedTateData_of`, `afterG7_of_linked`, `afterG7_of_linked'`,
    `linkedTateData_of_frobRam` and `afterG7_of_final`;
  - `UnramTate`: `tateBridge_of_tateModuleFree`, `scalarTransferQ`, `linkedTateCoreDR_of` and
    `linkedFrobRam_of`.
- The flat file `scratch/linked-tate/LinkedTate.lean` (FLAT-RESULT).
- Parts copied:
  - verbatim: g0-assemble's parts 10, 70, 72, 74, 75, 77 and 87; unram-tate lines 1038-1825
    (part 96, plus the file-level `open`s of `ModField.lean`); g14-trace's `part_g14.lean` §2-§5
    (part 93);
  - with one change: kernel `C10/Link.lean` excerpts (part 92). The change is
    `set_option synthInstance.maxHeartbeats 400000 in` before `trace_endE_indep`, because instance
    search for `Module.Free ℚ_[ℓ] (A.V ℓ)` times out at the default limit in this environment.

## 7. What remains

- **`GoodRedG3Bridge`.** The transport from PkgI2's points, torsion and valuation rings of `K̄` to
  `ℚ̄_ℓ ⊗ V_ℓ(A_{L,L'})` and the places of `ℚ̄`. It needs no literature beyond NOS.
- **`QMEndRank`.** Mumford §19 Thm 3 and Albert's classification on PkgI3 objects. Neither is in
  the bundles; either could be added as a leaf.
- **`LinkedFrob`.** Néron models, reduction and Serre–Tate on PkgI3 objects. g14-trace's square
  form `FrobSquaresLink` splits it into the kernel's three squares.
- **`LinkedRam`.** D1-D4 on the canonical `ρ_ℓ`. The bound on the upper breaks of `L'` at `p ≤ D`
  should be checked (§4.3).
- **`FibreSimple`.** Unchanged: g0-fibresimple's FS1b and FS5, plus pin-apply's `MobiusGlue`.
- **Integration.** `GluePieces2`'s fields 27 and 28 can be replaced by the five Props through
  `afterG7_of_final`. This was not done here, because g0-assemble's files belong to another task.
