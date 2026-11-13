# g8-tate: the glue left under G8 is closed, modulo two existing named glue Props

Task g8-tate, 2026-11-13. Lean: `scratch/g8-tate/` (results log `log.md`).
- **Flat check file:** `G8Tate.lean`, written by `build_flat.sh`.
- **Iteration files:** `Prefix.lean` → `Prefix2.lean` → `Tail.lean`, compiled as a chain of oleans
  (`build_prefix.sh`, `build_prefix2.sh`, `assemble.sh`, `ctail.sh`). They are not committed (they
  are gitignored); the scripts regenerate them. The sources are the parts `part_*.lean`.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = model judgement. **UNVERIFIED** = a theorem number recalled without a source
(there is no network). Model work only, no human review.

## 1. Result

**Verdict.** I took g8-object's split form of the restated `GluePieces2` field, `LinkedTateObjS`,
and the same field with T7 applied, `LinkedTateDataD`. Both are copied verbatim, and both carry
the premise `[L:ℚ] ≤ D` that g8-object recommends adding to `G7Data`. Both are now proved from:
- four leaves: R6, I2-Tors, T26 and (for `LinkedTateDataD`) T7;
- local-glue's textbook Prop `UnramRoots 2 5`;
- two glue Props that already existed in substance (§2).

No statement was changed.

The four items assigned to this task are closed in Lean:

| item (g8-object §4) | status |
|---|---|
| `WildTateTrivial` (R6/D2 on `LadicCond`'s `G_{ℚ_p}`) | **proved** from R6 and I2-Tors (`localDataS_of_g7Data`) |
| `BetaUpperC`, `BetaTameC` (T16/D3 on `G7Data`'s `β`) | **proved**. Odd `p` needs nothing; `p = 2` uses `UnramRoots 2 ℓ`. T16 is not needed (local-glue's finding G6) |
| the local field `F`: `e(F) ≤ (DG₀)!` resp. `p ∤ e(F)`, with `F ⊇ L` (`ContainsL`) | **proved** (`exists_finGal_ramCard_le`, and the new `exists_finGal_tame`) |
| `TateBridge35` with `OnL` (the Tate functor on G7's descent datum, `ℓ = 5, 3`) | **proved** in the form `TateBridgeOnL` from T26, `EndRank4` and linked-tate's `LinkedFrob` (`tateBridgeOnL_of`). `TateBridgeOnL` is `TateBridge35`'s conclusion plus `OnL`, for G7 data in a fibre context with `[L:ℚ] ≤ D`. `TateBridge35`'s premises `dim = 2` and `rank End = 4` are discharged by `PK.surface` and `EndRank4`. `OnL` itself is proved outright (`onL_canon`) |

VERIFIED: `lake env lean scratch/g8-tate/G8Tate.lean` (12 858 lines) exits with 0 errors in
3 min 40 s, with no `sorry`. All 147 `#print axioms` reports are
`[propext, Classical.choice, Quot.sound]`.

The main theorems are in namespace `G8Tate`:

```lean
-- G15's local data on G7Data's objects (g8-object's `LocalDataS`, verbatim)
theorem localDataS_of_g7Data (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) {p : ℕ} [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime]
    (hU : p = 2 → G15Ram.UnramRoots p ℓ) (hpℓ : p ≠ ℓ) … (h : G7Data u P L A ε N χ β L' hLL')
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD) (hdim : A.dim = 2) :
    G8Object.LocalDataS p L A ℓ β

-- OnL for unram-tate's canonical operators, for every descent datum, transport and h
theorem onL_canon (hLL' : L ≤ L') (A : PkgI3.AbVar L) (Θ : PtQ L A ≃+ PtA (A_{L'})) (h : GQ)
    (m : GQ → (PtQ L A →+ PtQ L A)) (n d : GQ → GQ → ℤ) (hmL) (hmLL) (hmsf) (hn) (hd) (hnd)
    (ℓ : ℕ) [Fact ℓ.Prime] (aℓ : GQ → ℚ̄_ℓ) (ha : ∀ k ∈ GQL L, aℓ k = 1) :
    ∃ ψ, G8Object.OnL L A (tmOf hLL' A Θ h m ℓ) aℓ ψ

-- the reductions
theorem linkedTateObjS_of_onL (hR6) (hTors) (hU : G15Ram.UnramRoots 2 5) (hB : TateBridgeOnL) :
    G8Object.LinkedTateObjS
theorem tateBridgeOnL_of (hT : PkgI3.TateModuleFree) (hRk : EndRank4)
    (hF : UnramTate.LinkedFrob) : TateBridgeOnL
theorem linkedTateObjS_of_frob (hR6) (hTors) (hU : G15Ram.UnramRoots 2 5)
    (hT : PkgI3.TateModuleFree) (hRk : EndRank4) (hF : UnramTate.LinkedFrob) :
    G8Object.LinkedTateObjS
theorem linkedTateDataD_of_frob (hM : PkgI3.CharPolyIndepOfEll) (hR6) (hTors) (hU) (hT) (hRk) (hF) :
    G8Object.LinkedTateDataD

-- tools
theorem exists_complex_equiv (ℓ : ℕ) [Fact ℓ.Prime] : Nonempty (ℂ ≃+* PadicAlgCl ℓ)
theorem exists_finGal_tame {E : Fld p} [FiniteDimensional ℚ_[p] E]
    (hE : Module.finrank ℚ_[p] E < p) : ∃ F : Fld p, IsFinGal F ∧ E ≤ F ∧ ¬ p ∣ ramCard F 0
```

Here `TateBridgeOnL` is the text of `LinkedTateObjS` with its two `LocalDataS` conjuncts deleted.
It consists of g14-trace's `TateBridge35` data together with `OnL` for `Tm₅` and `Tm₃`.
`G8Object.LinkedTateDataD` is g0-assemble's `LinkedTateData` (the `GluePieces2` field
`linkedTateData`) with the premise `[L:ℚ] ≤ D` added.

## 2. What the hypotheses are

| Prop | kind | content | used for |
|---|---|---|---|
| `ObjBridge.RaynaudCriterion` (R6) | **leaf** (`r.r6`; `raynaudCriterion_iff : … ↔ PkgI2.RaynaudCriterion.{0}` is `Iff.rfl`) | Raynaud's criterion, SGA 7 I Exp. IX | `WildTateTrivial` |
| `ObjBridge.TorsionStructure` (I2-Tors) | **leaf** (`t.t5`, likewise) | `A[n] ≅ (ℤ/n)^{2g}`, Mumford §4 | `WildTateTrivial` (index bound, `p`-power period) |
| `PkgI3.TateModuleFree` (T26 = I3.M0) | **leaf** (`t.t26`) | Mumford §18-19 | continuity clause of `G7Out` (`tateCont_of_tateModuleFree`) |
| `PkgI3.CharPolyIndepOfEll` (T7) | **leaf** (`t.t7`) | Mumford §19 Thm 4 | G14 (only in `linkedTateDataD_of_frob`) |
| `G15Ram.UnramRoots 2 5` | **textbook glue** (local-glue's; a leaf candidate) | an unramified character of `G_F`, `F/ℚ₂` finite, has an unramified 4th root (Serre, *Local Fields* III §5, IV §2; locators UNVERIFIED) | `BetaUpperC` at `p = 2` |
| `G8Tate.EndRank4` | **glue** (new name; the content of linked-tate's `FibreSimple` + `QMEndRank`) | for every fibre context and G7 datum with `[L:ℚ] ≤ D`, `rank_ℤ End(A_{L'}) = 4` (the premise is not used by the truth argument) | the `rank` clause of `G7Out` |
| `UnramTate.LinkedFrob` | **glue** (linked-tate's, copied verbatim) | g14-trace's `FrobTraceLink` for the canonical operators `tmOf … 5`, `tmOf … 3`, for every admissible `(Θ, h)` and descent datum | the `FrobTraceLink` conjunct of `TateBridge35` |

`EndRank4` is stated here because `LinkedTateObjS`, unlike `TateBridge35` and g0-mod-field's
`TateBridge`, does not assume `rank End = 4`. linked-tate proves `rank = 4` from `FibreSimple` (an
existing `GluePieces` field) and its `QMEndRank`, using `endDivision_of_fibreSimple`
(`linkedTateCore_of`). That proof is over `Leaves.lean` and is not re-checked in this environment;
porting it also needs `endDivision_of_fibreSimple`'s bridge `abVarEquiv` from the Leaves layer.
**Why `EndRank4` is true** (STANDARD route, numbering UNVERIFIED):
- `End⁰(A_{L'})` is a division algebra (`FibreSimple`) containing `B`.
- By Albert's classification it equals `B`.
- `End` is finitely generated and torsion-free (Mumford §19 Thm 3).

`dim A_{L'} = 2` is proved (`PK.surface` and the kernel's `PkgI3.AbVar.dim_baseChange`,
`ZInQKernel/Contrib/AbVarBC/Dim.lean`).

## 3. How each item is proved

### 3.1 `LocalDataS` (part 2, `part_local.lean`)

- **Transport of `β`.** `G7Data`'s `β` is `ℂ^×`-valued; local-data's and local-glue's lemmas are
  about `ℚ̄_ℓ`-valued cochains.
  - `exists_complex_equiv` gives a field isomorphism `Φ : ℂ ≅ ℚ̄_ℓ`. It is Steinitz's theorem, via
    Mathlib's `IsAlgClosed.ringEquiv_of_equiv_of_charZero`.
  - The cardinalities: `#ℚ_ℓ ≤ 𝔠` (rational approximations), `#ℚ_ℓ ≥ 𝔠` (Mathlib's perfect-set
    bound for complete fields), and `#ℚ̄_ℓ = #ℚ_ℓ`.
  - `g7Clauses_of_g7Data`: `Φ ∘ β` satisfies local-data's `G7Clauses`, with `[L:ℚ] ≤ D` as the
    premise.
  - `Φ` is injective, so `Φ(β g) = 1 ⇒ β g = 1`.
  - This also supplies the injective `ι : ℂ^× →* ℚ̄_ℓ^×` that local-glue's `kerWild_of_g7Data`
    assumes, as `Units.map Φ`.
- **`p ≤ D`.**
  - `torsFixWildOdd_of_descent` (local-glue: R6 and D2 on the torsion field, `q = 3`, or `q = 5`
    if `p = 3`) gives `E ⊇ L_v` with `[E:ℚ_p] ≤ G₀·[L_v:ℚ_p] ≤ DG₀`. Wild inertia of `G_E` fixes
    every `ℓⁿ`-torsion point of `A/L`.
  - Its `DescentPts A L` input is trivial here (`descentPts_self`: `A` is already over `L`;
    `resQ` is injective).
  - `F` is the Galois closure, so `e(F) ≤ (DG₀)!` (`exists_finGal_ramCard_le`), and `ContainsL`
    holds with `j = embP`.
  - `WildTateTrivial` follows from `tate_eq_one_of_torsFix`.
  - `BetaUpperC`:
    - at odd `p`: upper ramification groups are wild (`upperWild`), and `β` kills wild inertia of
      `G_{L_v}` (`beta_wild_of_clauses`);
    - at `p = 2`: `betaUpper_of_twist` with `betaTwist2_of_unramRoots` (local-glue).
- **`p > D`** (so `p ≥ 7`).
  - `F` is the Galois closure of `L_v`. It is tame because `[L_v:ℚ_p] ≤ D < p` (`exists_finGal_tame`:
    `Gal(F/ℚ_p)` embeds in `S_n`, `n < p`, and inertia is a subgroup).
  - `WildTateTrivial` follows from `tateWildK_of_R6`.
  - `BetaTameC` follows from `beta_wild_of_clauses`.

### 3.2 `OnL` for the canonical operators (part 4, `part_onl.lean`)

unram-tate's operators are `Tm_ℓ(g) = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)` (linked-tate's `tmOf`). On `G_L`,
`m` is the Galois action, so `Tm(resQ σ_L) = opV(Θ ∘ σ(h k₀ h⁻¹) ∘ Θ⁻¹)` with `k₀ = resQ σ_L`.

`onL_canon` takes `ψ⁻¹ = opV(m_x) ∘ V(Θ ∘ trPt φ₁)`, where:
- `φ₁ : L̄ ≅ ℚ̄` is an `L`-isomorphism (`IsAlgClosure.equiv`);
- `g₁ = φ₁ ∘ g₀`, with `g₀ : ℚ̄ → L̄` the embedding chosen by `resQ` (so `trPt φ₁` carries `σ_L`
  to `g₁ k₀ g₁⁻¹`, `resQ_comm'`);
- `x = h g₁⁻¹`.

Two facts make this work:
- `DescentDatum`'s `m(σk) = m σ m k` and `m(kσ) = m k m σ` on `G_L` give
  `m_x ∘ σ(g₁k₀g₁⁻¹) = σ(hk₀h⁻¹) ∘ m_x`.
- `m_x` is invertible on `V_ℓ`, because `m_x m_{x⁻¹} = (n/d)·m_1` and `m_1 = id` (`m_one`:
  `m_1` is idempotent and onto).

New general lemmas:
- `VX`/`VXe`: the Tate functor across two groups of points;
- `opV_conjE`: `opV(Ξ f Ξ⁻¹) = V(Ξ) opV(f) V(Ξ)⁻¹`;
- `exists_equiv_of_quasiInv`.

**Finding (VERIFIED, compiled).** The isogeny `m_x` cannot be dropped. The `h` that `tatePoints`
produces need not fix `L` pointwise (the same embedding mismatch `γ ∈ Gal(L/ℚ)` as local-glue's
finding G9). A points-level transport alone would identify `V_ℓ(A_{L'})` with `V_ℓ` of a
conjugate of `A`. The descent datum's `m_x` (Glazer's `μ`) corrects this, as g8-object predicted
in §4.1 (SPECULATIVE there, now proved).

### 3.3 `TateBridge35`'s data (part 5, `part_tb.lean`)

linked-tate's `linkedTateCoreDR_of` builds `G7Out` at `ℓ = 5, 3` for the canonical operators with
scalars `a = 1` and `β' = γ₀ ∘ conj_h`, where `κ ∘ γ₀ = β/a` (`scalarTransferQ`).
`TateBridge35` asks for something else, `ιC ∘ βQ = β` for `G7Data`'s own `β`, and `OnL` asks for
`aQ = 1` on `G_L`.

`tateBridgeOnL_of` therefore keeps the operators `Tm_ℓ = tmOf … ℓ` and `c` and changes the scalars:
- `βQ = κ⁻¹ ∘ β` (`β`'s values are roots of unity, since `β² = χ`: `beta_pow_eq_one`,
  `exists_preimage`);
- `aQ(g) = βQ(g) / γ₀(hgh⁻¹)`;
- `ε_ℓ = ∂(j_ℓ ∘ βQ)`.

Then:
- `∂aQ · c = ∂βQ`, because `c = ∂γ₀ ∘ conj_h`.
- `aQ = 1` on `G_L`. `β(hkh⁻¹) = β(k)` for `k ∈ G_L` (`beta_conj`: `ε` is `1` as soon as one
  argument is in `G_L`), and `a = 1` on `G_L`.
- `ρ = β'⁻¹ a' Tm` is pointwise linked-tate's `ρ`, so linked-tate's continuity proof applies
  unchanged.

The rest of linked-tate's `key` block (relations, `G_{L'}`-clause, matrix units from `𝒪`,
continuity) is copied with these scalars. `FrobTraceLink` is `LinkedFrob` applied to the same
choice, and `OnL` is `onL_canon`.

## 4. Findings

- **F1 (VERIFIED, compiled).** No T16 and no Herbrand function are needed for G8's `β`-clauses
  (local-glue's G6, now on `G7Data`'s `ℂ^×`-valued `β`). The only input beyond `G7Data` and R6/I2-Tors
  is `UnramRoots` at `p = 2`.
- **F2 (VERIFIED, compiled; one point SPECULATIVE).** linked-tate's data do not supply
  `TateBridge35`'s clause `ιC ∘ βQ = β`, because their `β'` is `γ₀ ∘ conj_h`.
  - Why it would fail (SPECULATIVE): `|ιC(γ₀(hgh⁻¹))| = a(hgh⁻¹)⁻¹`, and this is `≠ 1` when
    `deg μ ≠ 1`, while `β` is a root of unity.
  - The repair (VERIFIED, compiled): rescaling `aQ = βQ / γ₀ ∘ conj_h` gives the clause without
    changing `ρ_ℓ`.
  - So linked-tate's `LinkedRam` and g8-object's `LocalDataS` route are statements about the same
    `ρ_ℓ`.
- **F3 (VERIFIED, compiled).** `OnL` needs the descent isogeny `m_x` in `ψ` (§3.2).
- **F4 (VERIFIED, by reading).** `LinkedTateObjS` (and `LinkedTateObj`) ask `G7Out` for
  `rank End(A_{L'}) = 4` without assuming it. That is why `EndRank4` appears. linked-tate found the
  same about `LinkedTateData`.
- **F5 (VERIFIED, compiled).** `ℂ ≃+* ℚ̄_ℓ` is available (Steinitz). Every transport between
  `G7Data`'s `ℂ^×`-valued data and `ℚ̄_ℓ`-valued data can use it. This removes the injectivity
  hypothesis that local-glue's `kerWild_of_g7Data` left open.
- **F6 (unchanged from g8-object).** The premise `[L:ℚ] ≤ D` is needed. `localDataS_of_g7Data`
  uses it for the bounds on `e(F)`. To feed `LinkedTateDataD` to g0-assemble's `afterG7_of`,
  `G7Data` must carry G4's bound (g0-mod-field's `g7OutUnr_of_g4Out` has it from `G4Out`).

## 5. What remains

1. **`EndRank4`**: linked-tate's `FibreSimple` + `QMEndRank` (Albert's classification). Porting
   linked-tate's `linkedTateCore_of` needs its Leaves-layer `FibreSimple`.
2. **`UnramTate.LinkedFrob`**: reduction of the descent isogenies modulo `p` and Serre–Tate. This is
   G14 content, linked-tate's open Prop, and g14-trace's `FrobSquaresLink` splits it further.
3. **`G15Ram.UnramRoots 2 5`** (textbook): Mathlib lacks unramified extensions of `p`-adic fields
   with Frobenius-generated cyclic Galois group.
4. **Integration**: add `Module.finrank ℚ L ≤ heightD` to `G7Data`. Then `linkedTateDataD_of_frob`
   replaces the `GluePieces3` fields `linkedFrob` and `linkedRam`, or g8-object's
   `LinkedTateObj` field, by `EndRank4` and `LinkedFrob`. `LinkedRam` is no longer needed on this
   route. Not done here, since `G7Data` is another task's text.

## 6. Compile record and copies

- `Prefix.lean` (`build_prefix.sh`) is the sum of three verbatim pieces:
  - `scratch/g8-object/G8Object.lean`;
  - `scratch/local-data/part_local.lean`, inside a `noncomputable section`;
  - local-glue's parts, without `galois_block.lean`, whose text is already in G8Object.lean.

  Compiled to an olean: 2 min 10 s, 0 errors, 133 axiom reports, all standard. No name clashes.
- `Prefix2.lean` (`build_prefix2.sh`) is the sum of two pieces:
  - linked-tate's `parts/96_unramtate.lean`, which is unram-tate's `TateBridge.lean` L1038-1825
    verbatim. Its copy of BCPoints.lean is left out, because local-glue's `bc_block.lean`, already
    in Prefix, is the same text in the same namespace `UnramTate`.
  - linked-tate's `parts/97_linkeddata.lean` L1-445, verbatim, without the two Leaves-layer
    composites at its end.

  Compiled: 1 min 11 s, 0 errors. These Leaves-layer parts compile unchanged over the kernel-layer
  prefix.
- `Tail.lean` (`assemble.sh`) holds parts 1-5 (`part_tools`, `part_local`, `part_link`,
  `part_onl`, `part_tb`). `TateBridgeOnL` is produced from g8-object's `part_split.lean` by a
  string replacement that deletes the two `LocalDataS` conjuncts. linked-tate's `key` block is
  copied with the scalar changes listed in §3.3.
- `G8Tate.lean` (`build_flat.sh`) is all of the above as one file. Compiled with
  `lake env lean`: 0 errors, no `sorry`, 147 axiom reports, all
  `[propext, Classical.choice, Quot.sound]`.
