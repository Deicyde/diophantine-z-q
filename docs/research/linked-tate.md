# linked-tate: `ModelG3G6` and `LinkedTateData` reduced; the linked Tate data are constructed

Task linked-tate, 2026-11-13. Lean: `scratch/linked-tate/` (results log `log.md`).
- **Flat file.** `LinkedTate.lean` is assembled by `assemble.sh` from three pieces:
  - `Leaves.lean`, a byte-identical copy of the pin-applied `scratch/h-decomposition/Leaves.lean`;
  - the three non-HDecomp kernel imports in `imports_extra.txt`;
  - the parts in `parts/`.
- **Iteration file.** `olean/Tail.lean` is compiled against an olean of that prefix
  (`build_prefix.sh`, `ctail.sh`), as g0-assemble did.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = model judgement. **UNVERIFIED** = theorem number recalled without a source (no
network). Model work only; no human review.

## 0. Main result

**Both joint glue Props of g0-assemble are proved from strictly smaller named Props, over
`Leaves.lean`'s definitions. Neither statement is changed.** Both Props are copied verbatim from
`scratch/g0-assemble/parts/87_afterg7.lean`.

- **`ModelG3G6`** follows from:
  - `FibreSimple`, already a `GluePieces` field;
  - one new glue Prop, `GoodRedTorsion`;
  - the leaves R6, R7a and T5.

  The noncommutativity half of G6 is proved outright.
- **`LinkedTateData`** follows from:
  - the leaves T7 and T26 (= I3.M0);
  - `FibreSimple`;
  - three new glue Props: `QMEndRank`, `LinkedFrob` and `LinkedRam`.
- **The `ℓ = 5` and `ℓ = 3` operator data are constructed, not assumed.** They are unram-tate's
  Tate-functor construction, run once with one scalar function `γ₀ : G_ℚ → ℚ̄`. So the scalar link
  that g14-trace found missing (its finding F1) holds by construction.
- **End to end.** `HSyn.sixContactMin_of_leaves3 r t gp3 : ZInQ.SixContactMin`. `GluePieces3` is
  g0-assemble's `GluePieces2` with fields 1-25 copied verbatim and fields 27 (`modelG3G6`) and
  28 (`linkedTateData`) replaced by four smaller Props:
  - `goodRedTorsion`;
  - `qmEndRank`;
  - `linkedFrob`;
  - `linkedRam`.

  That makes 29 fields, against 27.

```lean
theorem HSyn.LinkedTate.modelG3G6_of (hFS : HSyn.G0Split.FibreSimple) (hG3 : QMModelG3) :
    HSyn.G0AssembleMod.ModelG3G6
theorem HSyn.LinkedTate.qmModelG3_of (hNOS : PkgI2.NeronOggShafarevich.{0})
    (hRay : PkgI2.RaynaudCriterion.{0}) (hTors : PkgI2.TorsionStructure.{0})
    (hB : GoodRedG3Bridge) : QMModelG3
theorem HSyn.LinkedTate.goodRedG3Bridge_of_torsion (h : GoodRedTorsion) : GoodRedG3Bridge
theorem HSyn.LinkedTate.linkedTateData_of_frobRam (hM : PkgI3.CharPolyIndepOfEll)
    (hT : PkgI3.TateModuleFree) (hFS : HSyn.G0Split.FibreSimple) (hR : QMEndRank)
    (hFR : UnramTate.LinkedFrobRam) : HSyn.G0AssembleMod.LinkedTateData
theorem UnramTate.linkedFrobRam_of (hF : LinkedFrob) (hR : LinkedRam) : LinkedFrobRam
theorem HSyn.sixContactMin_of_leaves3 (r : ResearchLeaves) (t : TextbookLeaves)
    (gp3 : GluePieces3) : ZInQ.SixContactMin
```

**Also proved: two Mathlib-level glue Props, compiled first in standalone Mathlib files.**
- `UnramTate.localInertiaGlobal`: `decomp p` maps local inertia into the inertia group of a place
  of `ℚ̄` above `p`.
- `UnramTate.upperAbsInertia`: `G_{ℚ_p}^t` lies in inertia for `t > 0`.

They feed a conditional reduction of `LinkedRam` (§4.4).

**One finding changes a statement of mine, not of the task.** g0-mod-field's `G7Data` does not
record `[L:ℚ] ≤ D`. Because of that, `LinkedRam` in its first form, quantified over every scalar
function `γ₀`, was false for an oversized `L`. It now asks `γ₀` to equal `β/a` under an embedding
`ℚ̄ → ℂ`, and the construction supplies such a `γ₀` (§5).

**VERIFIED** (Lean 4.35.0, Mathlib v4.35.0): see §6. The tail and the flat file both give 0 errors
and no `sorry`. Every axiom report is `[propext, Classical.choice, Quot.sound]`.

## 1. The statements (copied, unchanged)

`ModelG3G6`: for every fibre context `FibreCtx Y Φ π u P` and all G7 data
`G7Data u P L A ε N χ β L' hLL'`, the model `A' = A_{L'}` satisfies:
- `G0Galois.G6Out A'`: `EndDivision A'`, and `End(A')` is not commutative;
- `G0Galois.G3Out A' 5 (T u)`;
- `G0Galois.G3Out A' 3 (T u)`.

`LinkedTateData`: for the same data there exist operator data `(Tm_ℓ, c_ℓ, ε_ℓ, a_ℓ, β_ℓ, u_ℓ)`
at `ℓ = 5` and `ℓ = 3`. They satisfy `G0Galois.G7Out` at both primes. Moreover, for all `r₅`, `r₃`
with G8's output on `ρ_ℓ = rho Tm_ℓ a_ℓ β_ℓ`, and all `i`, `ι_ℂ`, `ι₅`, some `ι₃` gives
`G14TraceCompat ⟨i, ι_ℂ, ι₅, ι₃, r₅, r₃⟩` and `G15RamWild` of the same data.

Both are read over the pin-applied `Leaves.lean`. There `FibreCtx` contains `R1fpProps`, which
pin-apply strengthened by `R1famProps` and `R1univProps`.

## 2. Named Props: leaf or glue

| Prop | kind | content | used for |
|---|---|---|---|
| `PkgI2.NeronOggShafarevich` (R7a), `PkgI2.RaynaudCriterion` (R6), `PkgI2.TorsionStructure` (T5) | **leaf** (`r.r7a`, `r.r6`, `t.t5`) | Serre–Tate 1968 Thm 1; Raynaud; Mumford §4 | G3, through `LeafQM.AV.QML3.goodReduction` (proved in `Leaves.lean`) |
| `PkgI3.CharPolyIndepOfEll` (T7) | **leaf** (`t.t7`) | Mumford §19 Thm 4 | G14 |
| `PkgI3.TateModuleFree` (I3.M0) | **leaf** (`t.t26`) | Mumford §18-19 | continuity clause of `G7Out` |
| `HSyn.G0Split.FibreSimple` | glue (existing `GluePieces` field; g0-fibresimple: leaves + FS1b + FS5; pin-apply: independent of the triple given `MobiusGlue`) | every number-field model of the fibre has `EndDivision` | G6, and the hypothesis of `QMEndRank` |
| `HSyn.LinkedTate.GoodRedTorsion` | **glue (new)** | Given NOS: if `A/K` has good reduction at every DVR of `K` with `3` a unit, then inertia of `G_{L'}` above `p ∉ {3, ℓ}` fixes every `ℓⁿ`-torsion point of `A_{L,L'}(\bar{L'})`. | G3 |
| `HSyn.LinkedTate.QMEndRank` | **glue (new, literature-backed)** | A `QML3` object over `K ≤ L ≤ L'` whose model has `EndDivision` has `rank_ℤ End(A_{L,L'}) = 4`. | `rank = 4` in `G7Out` |
| `UnramTate.LinkedFrob` | **glue (new)** | g14-trace's `FrobTraceLink` for the canonical operators `tmOf … 5`, `tmOf … 3`, for every admissible `(Θ, h)` and descent datum `(m, a, n, d)` | G14 |
| `UnramTate.LinkedRam` | **glue (new)** | `RhoRamWild` (clauses (i)-(ii) of `LocalRam` for the descended operator `ρ_ℓ`) for `ρ₅` at `p ≠ 5` and `ρ₃` at `p = 5`; `ρ_ℓ` built from the canonical operators and a `γ₀` equal to `β/a` under an embedding `ℚ̄ → ℂ` | G15 (i)-(ii) |

Intermediate Props, all proved from the rows above:
- `GoodRedG3Bridge`: G3 on base changes;
- `QMModelG3`: G3 for `QML3` objects;
- `LinkedTateCore`, `LinkedTateCoreDR`;
- `LinkedFrobRam`: the conjunction of `LinkedFrob` and `LinkedRam`.

No new literature leaf is introduced.

## 3. `ModelG3G6`

`G7Data`'s `IsQMModel L A P` gives `A = (PK.A)_L` for a `QML3` object `PK` over some `K ≤ L`.
So `A' = (PK.A)_{L,L'}`.

1. **`EndDivision A'`** (`endDivision_of_fibreSimple`). The clause `IsModelOver L' A' P` of
   `G7Data`, together with the fibre context, is `FibreOver Y Φ π u ⟨L'⟩ ((abVarEquiv L').symm A')`.
   `FibreSimple` then gives the result. VERIFIED.
2. **`End(A')` is not commutative** (`noncomm_baseChange2`, no input). bp-qmmoduli's `endBC` is
   an injective ring map: Mathlib's flat-descent faithfulness of `Over.pullback` along
   `Spec L → Spec K`. The QM structure `ι` is also injective. In `𝒪`,
   `i·(1+j)/2 ≠ (1+j)/2·i` (`oI_oH_ne`: the `k`-coordinates are `±1/2`). VERIFIED.
3. **G3.** `3 ∈ T u`, and `G3Out` is monotone in `T`, so `G3Out A' ℓ {3}` suffices (`QMModelG3`).
   Leaves.lean's `QML3.goodReduction` (from R7a, R6 and T5) gives good reduction at every DVR with
   3 a unit (`qmModelG3_of`). `GoodRedG3Bridge` turns that into `G3Out`. VERIFIED.
4. **`GoodRedG3Bridge` from `GoodRedTorsion`** (`goodRedG3Bridge_of_torsion`,
   `tate_eq_one_of_torsion`). The coordinates of `x ∈ T_ℓ(A)` are `ℓⁿ`-torsion. So triviality on
   torsion gives `galT σ = id`, `galRep σ = 1` and `tate σ = 1`. VERIFIED.

**`GoodRedTorsion` is true** (STANDARD route). For `v` above `p ≠ 3`, `v ∩ K` is a DVR with 3 a
unit. NOS (a) ⇒ (b) over `K` makes inertia trivial on `A(K̄)[ℓⁿ]`. Inertia of `G_{L'}` restricts
into it, and base change does not change the points (unram-tate's `bcPt`).

What is open is only the transport of places, `resQ` and points. It needs no literature beyond NOS.

## 4. `LinkedTateData`

### 4.1 G14 and G15 from the descended operators (`linkedTateData_of`)

Given linked data (`LinkedTateCore`): scalars `j_ℓ ∘ a`, `j_ℓ ∘ β` for one pair
`a, β : G_ℚ → ℚ̄`, `FrobTraceLink`, and `RhoRamWild`.
- **G14.** Write `ι₅ = j₅ ∘ γ` (g14-trace's `exists_comp_eq`) and set `ι₃ := j₃ ∘ γ`. g14-trace's
  `g14TraceCompat_of_link` (T7; part 93, with the kernel's `FrobCompare` in part 92) gives
  `G14TraceCompat` for every `r₅`, `r₃` with G8's output.
- **G15.** G8's `e` intertwines `ρ_ℓ` with `r_ℓ ⊕ r_ℓ`, so `ρ_ℓ(g) = 1` implies `r_ℓ(g) = 1`
  (`toHom_eq_one_of_intertwines`). This turns `RhoRamWild` into `LocalRamWild`
  (`localRamWild_of_rho`).

VERIFIED.

### 4.2 `dim` and `rank` (`linkedTateCore_of`)

`G7Out` asks `dim A' = 2` and `rank_ℤ End(A') = 4` outright, while g0-mod-field's `TateBridge`
assumed both.
- `dim A' = 2` is proved: `PK.surface` with g0-dim's `pkgI3_dim_baseChange`, applied twice.
- `rank = 4` is `QMEndRank`, applied with `EndDivision A'` from `FibreSimple`.

**`QMEndRank` is true** (STANDARD route, numbering UNVERIFIED):
- `End(A')` is finitely generated and torsion-free (Mumford §19 Thm 3).
- `End⁰(A')` is a division algebra containing `ι(B)`, of dimension 4.
- For a simple abelian surface in characteristic 0, `[End⁰ : ℚ]` divides 4 (Albert; Mumford §21).
  So `End⁰ = B`.

### 4.3 The linked data are constructed (`UnramTate.linkedTateCoreDR_of`)

unram-tate's `TateBridge.lean` (lines 1038-1825) is copied verbatim as part 96 and compiles over
`Leaves.lean` (`UnramTate.tateBridge_of_tateModuleFree`, VERIFIED).

Part 97 runs its assembly once for both primes with the same data:
- unram-tate's transport `(Θ, h)` (`tatePoints`);
- `G7Data`'s descent datum `m`, `a`, `n/d`;
- the canonical operators `tmOf … ℓ g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`.

The scalars:
- `a = 1`;
- `β' g = γ₀(hgh⁻¹)`.

`γ₀` comes from `scalarTransferQ`. The algebraic values of `β/a` are pulled back along an
embedding `κ : ℚ̄ → ℂ`, so `κ ∘ γ₀ = β/a`, and injectivity of `κ` transfers `∂(β/a) = n/d`.
The embeddings are `j_ℓ = IsAlgClosed.lift`.

The `G7Out` proof is unram-tate's `tateBridge_of_pieces`, with `a' = j ∘ 1` and `β' = j ∘ γ₀ ∘ cj`.
The conjuncts `FrobTraceLink` and `RhoRamWild` refer to the constructed operators. They are
therefore stated for every admissible choice (`LinkedFrob`, `LinkedRam`) and applied to the choice
made. VERIFIED.

**Why `LinkedFrob` and `LinkedRam` are true** (SPECULATIVE).
- **`LinkedFrob`** is g14-trace's argument (N5 L777-786). At a Frobenius `τ` outside a finite
  set, `m_{hτh⁻¹}` is `μ ∘ Frobenius` on points, and it is algebraic (`DescentDatum`'s clause
  `F_σ`). With the Serre–Tate reduction isomorphism, `N·Tm_ℓ(τ)` is `V_ℓ(N μ̄ ∘ F)`, with the
  same endomorphism at both `ℓ`. The other choices change nothing that matters:
  - `(Θ, h)`, or `Θ` composed with a Galois-equivariant additive automorphism, conjugates `Tm_ℓ`
    by an invertible operator;
  - another descent datum `m' = q·m` has `q` rational, absorbed into `N`.
- **`LinkedRam`** is Glazer's D1-D4 (N5 L819-852; read). Above `U₀ = 4(DG₀)²` the absolute upper
  groups lie in `G_L` and act trivially on the Tate module; `β` is trivial on them (on wild
  inertia at odd `p`, and above `max(4D², 3e)` at `2`). The other choices allowed in `LinkedRam`
  change `ρ_ℓ` only by conjugation and by `sgn(q)`, where `m' = q m` and `q ∈ ℚ^×`, because
  `End⁰ = B` has centre `ℚ`. Since `γ₀ = β/a` is tied, `γ₀` itself is not a free choice. A
  quadratic character has conductor exponent `≤ 3` at 2 and is tame at odd `p`, so the bounds
  survive.

### 4.4 A conditional reduction of `LinkedRam` (`UnramTate.linkedRam_of`, part 98b)

On `G_{L'}` the canonical operators are the Tate action (`tmOf_resQ`), and `β' = 1` there. So
`RhoRamWild` follows from four Props, together with G3 (`QMModelG3`):
- **`KernelFieldBreaks`** (field-theoretic): `decomp p (G_{ℚ_p}^t) ⊆ G_{L'}` for `p ≤ D`, `t > U₀`,
  and `decomp p (wild inertia) ⊆ G_{L'}` for `p > D`;
- **`LocalInertiaGlobal`**: **proved** (part 98c, Mathlib). The place is the comap of `‖·‖ ≤ 1`
  along `decomp`'s embedding `ℚ̄ → ℚ̄_p`;
- **`UpperAbsInertia`**: **proved** (part 98d, Mathlib). The lower index of `G^t` is `≥ 0` because
  `φ_L ≤ 0` on `u ≤ 0`, and every `x ∈ ℚ̄_p` lies in a finite Galois `L`;
- **`TateRamAtThree`**: D1-D2 at `p = 3` for `ρ₅`.

VERIFIED (all compiled, standard axioms).

**Caveat: `KernelFieldBreaks` and `TateRamAtThree` are justified only when `[L:ℚ] ≤ D`.**
- **What Glazer proves.** Glazer's argument proves `KernelFieldBreaks` (read, N5 L813-850):
  `G^u ⊆ G_L` above the break bound of `L`, `[L:ℚ] ≤ D`, and `β` trivial there. So
  `G^u ⊆ G_L ∩ ker β = G_{L'}`.
- **What `G7Data` omits.** `G7Data` does not record `[L:ℚ] ≤ D`.
- **The failure.** For an oversized `L ⊇ ℚ(ζ_{2^k})`, `KernelFieldBreaks` (i) fails at 2. Such an
  `L` is allowed when `M_{S_mul}(u)` is large (SPECULATIVE).

Hence `GluePieces3` keeps `LinkedRam` itself as the field. The reduction becomes usable if `G7Data`
is corrected (§5).

## 5. Findings

- **The scalar link is constructible.** g14-trace's F1 is resolved by construction: one
  `γ₀ = β/a` and the same `(Θ, h, m)` serve both primes, and every `G7Out` clause is proved.
  VERIFIED.
- **`G7Out` asks more than `TateBridge` provides.** It asks `dim = 2` and `rank End = 4`. The rank
  needs NoCM on the model (`FibreSimple`) and Albert's classification (`QMEndRank`).
- **`G7Data` forgets `[L:ℚ] ≤ D`.**
  - The fact: g0-mod-field's `G4Out` has the bound and `G7Data` drops it (VERIFIED by reading
    `parts/75_modfield.lean`).
  - The consequence: statements universally quantified over the choices made after G7 can fail for
    an oversized `L`, even when the existential statements they feed survive.

  Two instances here:
  - **`LinkedRam`, first form.** Over every `γ₀`, it fails for an oversized `L`. Twisting `γ₀` by a
    character of `Gal(L'/ℚ)` of conductor `2^k` breaks clause (i). Now repaired by tying `γ₀` to
    `β/a`.
  - **`KernelFieldBreaks` and `TateRamAtThree`.** These are justified only under `[L:ℚ] ≤ D`.

  Recommended correction for the integrators: add `Module.finrank ℚ L ≤ heightD` to `G7Data`.
  `fieldDescentUnr` already has it from `G4Out`. Then `GluePieces3`'s `linkedRam` could be replaced
  by `KernelFieldBreaks` and `TateRamAtThree`, through `linkedRam_of`. `ModelG3G6` and
  `LinkedTateData` themselves are believed true as stated: they are existential in the choices
  (SPECULATIVE).
- **g0-fibresimple's §5 conflicts with the pin, as pin-apply intended.** Its
  `r1fpProps_twistBy` no longer compiles against the pin-applied `R1fpProps`. It is removed from
  this task's copy of part 40, and nothing else uses it (VERIFIED).
- **The last step of G15 can be stated on `ρ_ℓ`.** `G15RamWild` for G8's `r_ℓ` follows from
  `RhoRamWild` for `ρ_ℓ` (proved).

## 6. What compiles

- **`olean/Tail.lean`** = `import LPrefix` + every part. Those are g0-assemble's 05-90, then 92,
  93, 95, 96, 97, 98, 98b, 98c, 98d and 99. VERIFIED: 0 errors and no `sorry`, and every axiom
  report is standard. The declarations (namespaces `HSyn.LinkedTate`, `UnramTate`, `HSyn`):
  - G6 and G3: `oI_oH_ne`, `noncomm_baseChange2`, `endDivision_of_fibreSimple`, `qmModelG3_of`,
    `modelG3G6_of`, `tate_eq_one_of_torsion` and `goodRedG3Bridge_of_torsion`.
  - G14 and G15: `toHom_eq_one_of_intertwines`, `localRamWild_of_rho`, `linkedTateCore_of` and
    `linkedTateData_of`.
  - The composites: `linkedTateData_of_frobRam`, `afterG7_of_linked`, `afterG7_of_linked'`,
    `afterG7_of_final`, `gluePieces2_of_gluePieces3`, `sixContactMin_of_leaves3`, and
    g0-assemble's `sixContactMin_of_leaves2`.
  - The unram-tate port and the construction: `tateBridge_of_tateModuleFree`, `scalarTransferQ`,
    `linkedTateCoreDR_of`, `linkedFrobRam_of` and `tmOf_resQ`.
  - The reduction of `LinkedRam`: `tate_trivial_of_g3`, `linkedRam_of`, `localInertiaGlobal` and
    `upperAbsInertia`.
- **The flat file `LinkedTate.lean`** (FLAT-RESULT).
- **Standalone Mathlib checks:** `test/LocalInertia.lean` and `test/UpperAbs.lean`. Both compile
  with 0 errors.
- **Parts copied verbatim:**
  - g0-assemble's parts 05-90, except part 40 below;
  - unram-tate lines 1038-1825 (part 96, plus `ModField.lean`'s file-level `open`s);
  - g14-trace's `part_g14.lean` §2-§5 (part 93).
- **Parts copied with changes:**
  - **Part 92** (kernel `C10/Link.lean` excerpts). `set_option synthInstance.maxHeartbeats 400000
    in` is added before `trace_endE_indep`, because of an instance timeout in this environment.
  - **Part 40.** Its §5 is removed (§5 above).

## 7. What remains

- **`GoodRedTorsion`.** The point-level transport between places, `resQ` and base change.
- **`QMEndRank`.** Mumford §19 Thm 3 and Albert's classification on PkgI3 objects. It could be
  added as a leaf.
- **`LinkedFrob`.** Néron models, reduction and Serre–Tate on PkgI3 objects. g14-trace's square
  form `FrobSquaresLink` splits it into the kernel's three squares.
- **`LinkedRam`.** Glazer's D1-D4 on the canonical `ρ_ℓ`. With `[L:ℚ] ≤ D` added to `G7Data`, it
  reduces (proved) to `KernelFieldBreaks` and `TateRamAtThree`.
- **`FibreSimple`.** Unchanged: g0-fibresimple's FS1b and FS5, plus pin-apply's `MobiusGlue`.
- **Integration.** `GluePieces3` and `sixContactMin_of_leaves3` are in `parts/99_bundle3.lean`.
  g0-assemble's own files are untouched.
