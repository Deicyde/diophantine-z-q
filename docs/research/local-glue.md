# local-glue: `LocalGlue p Tm a β L` (local-data) on G7's data

Task local-glue, 2026-11-13.

Lean: `scratch/local-glue/LocalGlue.lean`, assembled by `scratch/local-glue/build.sh` from:
- a verbatim copy of `scratch/local-data/LocalData.lean`, which contains `LocalGlue` and
  everything it depends on;
- verbatim blocks of `scratch/g0-mod-galois/part_galois.lean` (`galois_block.lean`),
  `scratch/neron-lg/NeronLG.lean` (`neron_block.lean`), `scratch/unram-tate/BCPoints.lean`
  (`bc_block.lean`), `scratch/g0-assemble/parts/75_modfield.lean` (`resq_block.lean`:
  `resQ_range`) and `scratch/g0-dim/Dim.lean` (`dim_block.lean`);
- the new parts `part_glue.lean` (§6-§7), `part_ptfinite.lean` (§7b), `part_raynaud.lean` (§7c),
  `part_descent.lean` (§7d), `part_twist.lean` (§7e), `part_bcdescent.lean` (§7f) and
  `part_pack.lean` (§8).

Integration file: `scratch/local-glue/TailK.lean` (`build_tail.sh`): local-data's `Tail.lean`
plus the same parts plus `tail_glue.lean` (§9).

Log: `scratch/local-glue/log.md`. Compiler output: `compile.out` and `tail_compile.out`.

Markers: **VERIFIED** = compiled or read here. **STANDARD** = published, with a reference.
**SPECULATIVE** = my judgement. Theorem numbers from memory are **UNVERIFIED** (no network).

## 1. Result

**Verdict.** `LocalGlue p Tm a β L`, copied verbatim from local-data, is a predicate on arbitrary
operators `Tm`, scalars `a`, `β` and a field `L`, so it is not a closed theorem:
`not_localGlue_zero` proves it false for `Tm = 0` at every `p > D` (VERIFIED). It is a claim about
the data that G7 builds.

On g0-mod-field's construction of that data, it is a theorem from two leaves and one textbook
Prop. Besides those it uses only clauses of the construction itself. No local glue Prop is
left.

**Main result (VERIFIED, compiled, standard axioms only).** The general form:

```
theorem G15Ram.localGlue_of_unramRoots (hR6 : ObjBridge.RaynaudCriterion)
    (hTors : ObjBridge.TorsionStructure) (hU : UnramRoots p ℓ) (hpℓ : p ≠ ℓ)
    {A : PkgI3.AbVar K} {Tm c ε a β u} (h7 : G0Galois.G7Out A ℓ Tm c ε a β u)
    {L : IntermediateField ℚ PkgI4.Qbar} [FiniteDimensional ℚ L]
    (hC : G7Clauses β ε L) (hK : KerWild K β L) (hD : p ≤ 5 → DescentPts A L) :
    LocalGlue (p := p) Tm a β L
```

What it rests on:

| input | kind | where it is used |
|---|---|---|
| `ObjBridge.RaynaudCriterion` (R6) | **leaf**, in the bundles | `p ≥ 7` on `A/K`; `p ≤ 5` on the model `A₀/L` |
| `ObjBridge.TorsionStructure` (I2-Tors) | **leaf**, in the bundles | `A[m] ≅ (ℤ/m)⁴`; the index bound |
| `UnramRoots p ℓ` | textbook glue (new) | `p = 2` only |
| `KerWild K β L` | glue: a clause G7 has but `G7Out` dropped | all `p` |
| `DescentPts A L` | glue: `A` is the base change of a model over `L` | `p ≤ 5` only |
| `G7Out`, `G7Clauses` | G7's data (hypotheses of local-data's `localData_of_g7`) | |

- **At `p ≥ 7`** nothing but R6 and I2-Tors is needed (`tateWildK_of_R6`). This includes
  Glazer's `p > D`.
- **At `p ∈ {3, 5}`** add `DescentPts` (`torsFixWildOdd_of_descent`).
- **At `p = 2`** add `DescentPts` and `UnramRoots`. local-data's `BetaUpper`, i.e. T16 + D3 +
  Herbrand, is not used (§3, G6).

**On G7's construction both glue Props are discharged (VERIFIED, compiled).**

```
theorem G15Ram.localGlue_of_baseChange (hLL' : L ≤ L') (hR6) (hTors) (hU : UnramRoots p ℓ)
    (hpℓ : p ≠ ℓ) [IsGalois ℚ L'] (A₀ : PkgI3.AbVar L) (hdim₀ : A₀.dim = 2)
    (h7 : G0Galois.G7Out (bcL' hLL' A₀) ℓ Tm c ε a β u) (hC : G7Clauses β ε L)
    (βC : GQ → ℂˣ) (hker : ∀ σ, σ ∈ L'.fixingSubgroup ↔ σ ∈ L.fixingSubgroup ∧ βC σ = 1)
    (ιC : ℂˣ →* (PadicAlgCl ℓ)ˣ) (hι : Function.Injective ιC) (hβ : ∀ g, β g = ιC (βC g)) :
    LocalGlue (p := p) Tm a β L
```

Here `L ≤ L'` are finite in `ℚ̄`, `L/ℚ` is Galois, and `bcL' hLL' A₀` is `A₀.baseChange L'` along
g0-mod-field's `incAlg`, exactly as in `TateBridge`. The data clauses:
- `dim A₀ = 2` (G4/G5). The primed version `localGlue_of_baseChange'` derives it from `G7Out`'s
  `dim (A₀)_{L'} = 2`, using g0-dim's `G0Dim.pkgI3_dim_baseChange` (copied verbatim,
  `dim_block.lean`);
- `hker` is `G7Data`'s kernel-field clause;
- `β = ι ∘ β_ℂ` with `ι` injective is the transport that `TateBridge` should output (G8).

How the glue Props are discharged:
- `kerWild_of_g7Data` gives `KerWild`;
- `descentPts_baseChange` gives `DescentPts`. It builds the conjugate model `A₀ ×_{L,γ} L`
  (finding G9) and proves `dim` invariance along `Spec γ`.

Pack and tail on this form:
- `G0ModNewform.G7LocalPackBC`: the construction's data, with no local Prop and no `dim` clause;
- `g8LocalPack_of_BC`, `g15RamG_of_packBC`;
- `modularConstituent_tail_BC`.

The packs and the tail of `ModularConstituent` (G13-G16) are restated on these inputs and
compiled (`TailK.lean`):
- `G0ModNewform.G7LocalPackU`: G7's data with `KerWild` and `DescentPts`;
- `g8LocalPack_of_U`: gives local-data's `G8LocalPack`;
- `g15RamG_of_packU`: gives g15-ram's `G15RamG`;
- `modularConstituent_tail_U`: the tail itself.

## 2. The remaining Props

Each is a `def … : Prop` with a docstring naming its step and source.

**`UnramRoots p ℓ`** (`part_twist.lean`). Textbook glue. Statement: for a finite `F/ℚ_p` and a
character `ψ` of `G_F` with values in `ℚ̄_ℓ^×` that is trivial on some open `G_{F''}` and on the
inertia subgroup `G_F ∩ inertiaSet`, there is a character `η` of `G_F` with these properties:
- `η` is trivial on some open `G_{F₁}` and on `G_F ∩ inertiaSet`;
- `η⁴ = ψ`.

Proof sketch (STANDARD; Serre, *Local Fields*, Ch. III §5 and Ch. IV §2, locators UNVERIFIED):
- `ψ` factors through `Gal(F_m/F) ≅ ℤ/m`, `F_m` unramified, generated by Frobenius;
- take `ξ ∈ ℚ̄_ℓ` with `ξ⁴ = ψ(Frob)`, a root of unity of order `d ∣ 4m`;
- set `η(σ) = ξ^k` for `σ|_{F_d} = Frob^k`.

Lean needs the unramified extension of each degree and `Gal(F_d/F)` cyclic, generated by
Frobenius. It is stated over the genuine `fixSet`/`inertiaSet` of `ℚ̄_p`, so it is a leaf candidate
of textbook type.

**`KerWild K β L`** (`part_glue.lean`). Glue; discharged on G7's construction by
`kerWild_of_g7Data`. Statement: `g ∈ G_L` and `β(g) = 1` imply
`g ∈ resQ_K(G_K)`.
- This is g0-mod-field's `G7Data` clause `σ ∈ G_{L'} ↔ σ ∈ G_L ∧ β σ = 1`, transported to
  `G7Out`'s `K` and `ℚ̄_ℓ`-valued `β`.
- g0-assemble's `TateBridge`, which produces `G7Out`, does not output it (§3, G8).
- `kerWild_of_g7Data` (proved) derives it from G7Data's clause, given that the
  `ℚ̄_ℓ`-valued `β` is `ι ∘ β_ℂ` with `ι` injective. So what is missing is only that transport
  clause in `TateBridge`'s output.
- It cannot be removed: without it, `LocalGlue` fails on data satisfying `G7Out ∧ G8Out ∧
  G7Clauses` (G1').

**`DescentPts A L`** (`part_descent.lean`). Glue, used at `p ≤ 5`; proved for the base change
by `descentPts_baseChange` (`part_bcdescent.lean`). Statement:
- `L/ℚ` is Galois;
- there is a model `A₀ : AbVar L` with `dim A₀ = 2`;
- there is a group isomorphism `φ : A₀(L̄) ≃* A(K̄)` with `φ ∘ σ₀ = σ' ∘ φ` whenever
  `resQ_L σ₀ = resQ_K σ'`.

In g0-assemble, `A_{L'}` is literally `A.baseChange L'` for `A : AbVar L` (`TateBridge`). Then `φ`
is `bcPt` composed with a transport along `L̄ ≅ L̄'` (`trPt`).
- Mathlib's choices of embeddings inside `resQ L`, `resQ L'` can differ on `L` by
  `γ ∈ Gal(L/ℚ)`. So the model is the conjugate `A₀ ×_{L,γ} L` (VERIFIED, compiled:
  `descentPts_baseChange`).
- Why it is needed at `p ≤ 5`: finding G3.

**Removed in this run** (each was a named Prop in the first report; now proved or reduced):
- `RaynaudPlace` is proved from R6 and I2-Tors (`raynaudPlace_of_R6`).
- `TorsFixWildOdd` and `TorsFixWildE` are proved from R6, I2-Tors and `DescentPts`.
- `BetaTwist2` is proved from `UnramRoots` and `Beta4Inertia`.
- `Beta4Inertia` is proved from `G7Clauses` at `p = 2`.
- `PtFinite`, `WildIter` and `TorsGL` are proved.

## 3. What is proved

All rows are VERIFIED: `lake env lean scratch/local-glue/LocalGlue.lean` exits 0 with 0 errors and
no `sorry`. All 78 `#print axioms` lines are `[propext, Classical.choice, Quot.sound]`. Names are
in `G15Ram` unless noted.

| Lean | statement | proof idea |
|---|---|---|
| `not_localGlue_zero` | `D < p` ⟹ `¬ LocalGlue (Tm := 0) (a := 1) (β := 1) L` | `σ = 1` is wild and fixes `L` |
| `localGlue_of_g7`, `localGlue_of_g7_twist` | `LocalGlue` from `KerWild`, `TateWildK` (`p ≥ 7`), `TateWildKE` (`p ≤ 5`), `BetaUpper` resp. `BetaTwist2` (`p = 2`) | odd `p`: `β` is tame (`beta_wild_of_clauses`), so wild `σ ∈ G_L` lies in `G_K` |
| `tate_eq_one_of_torsFix` | fixing all `ℓⁿ`-torsion ⟹ trivial on `ℚ̄_ℓ ⊗ V_ℓ(A)` | `T_ℓ` = compatible torsion sequences |
| `iterate_card_GL_fix`, `card_GL4_three`, `card_GL4_five`, `card_GL4_seven` | `φ^{‖GL₄(𝔽_q)‖} = id` on `(ℤ/q)⁴`; `‖GL₄(𝔽₃)‖ = 24261120`, `‖GL₄(𝔽₅)‖ = G₀` | `Matrix.card_GL_field` |
| `torsGL_of_leaf` | I2-Tors, `dim A = 2` ⟹ `A(K̄)[m] ≅ (ℤ/m)⁴` | the leaf on `ObjBridge.toGrp A` (defeq) |
| `ptFinite`, `wildIter` | `K̄`-points are defined over finite `F/K`; wild `σ'` has `p`-power period | Mathlib's Stacks 01ZC (`exists_π_app_comp_eq_of_locallyOfFinitePresentation`) |
| `isInertia_of_wild_gen`, `raynaudPlace_of_R6` | R6 at the place of `embP` for `m ≥ 3`, `p ∤ m` | R6 over `F = K(A[m])` (fixed field of the open stabilizer), `A_F` via `bcPt`, valuation rings `normVS` |
| `tateWildK_of_R6` | `TateWildK` at `p ≥ 7`, `p ≠ ℓ` from R6 + I2-Tors | `m = 3` (`m = 7` at `p = 13`) has `p ∤ ‖GL₄(𝔽_m)‖`; D2 |
| `index_torsStab_le` | `[G_K : Stab(A[q])] ≤ ‖GL₄(𝔽_q)‖` | hom `G_K →* (𝔽_q⁴ ≃ₗ 𝔽_q⁴)`, kernel = stabilizer |
| `RQ.resQ_range` (copied) | `resQ_L(G_L) = Fix(L)` for `L/ℚ` Galois | g0-assemble |
| **`torsFix_of_descent`** | R6 + I2-Tors + `DescentPts`, prime `q ≥ 3`, `q ≠ p`, finite `M ⊇ L_v` ⟹ ∃ `E ⊇ M`, `[E:ℚ_p] ≤ ‖GL₄(𝔽_q)‖[M:ℚ_p]`, wild `σ ∈ G_E` fixes `A(K̄)[ℓⁿ]` | see below |
| `torsFixWildOdd_of_descent`, `torsFixWildE_of_twist`, `tateWildKE_of_descent`, `localGlue_of_descent` | `p ≤ 5` | `q = 3` (`q = 5` at `p = 3`); `4·24261120 ≤ G₀` |
| `betaUpper_of_twist` | `BetaTwist2` ⟹ `BetaUpper β L_v U₀` | degree-based break bound (`UpperBreakFix`, T20 + T21) |
| **`betaTwist2_of_roots`** | `G7Clauses`, `UnramRoots`, `Beta4Inertia` ⟹ `BetaTwist2` | see below |
| `inertia_fix_prime_to_p`, `sq_fix_four`, `chiLevel_dvd_four_mul_odd`, `cyc_decomp_sq_inertia`, **`beta4Inertia_of_clauses`** | `p = 2`: `β⁴ = 1` on inertia of `G_{L_v}` | see below |
| `kerWild_of_g7Data` | `G_{L'} = G_L ∩ ker β_ℂ`, `β = ι ∘ β_ℂ`, `ι` injective ⟹ `KerWild L' β L` | `resQ_range` |
| `localGlue_of_unramRoots` | main result (§1) | the above |
| `γL`, `θL`, `θL_galois`, `conjModel`, `φL`, `φL_galAct`, `dim_conjModel`, **`descentPts_baseChange`** | `DescentPts ((A₀)_{L'}) L` for `dim A₀ = 2`, `L/ℚ` Galois | `γ = jK_L⁻¹ ∘ jL'` (both embeddings have image `L`); `φ = bcPt⁻¹ ∘ trPt θ ∘ bcPt`, `θ = qEmb_{L'} ∘ qEmb_L⁻¹`; `Scheme.Hom.homeomorph` |
| **`localGlue_of_baseChange`**, `localGlue_of_baseChange'` | `LocalGlue` on G7's construction (§1) | the above; `'` with `G0Dim.pkgI3_dim_baseChange` |
| `G0ModNewform.g8LocalPack_of_BC`, `g15RamG_of_packBC`, `modularConstituent_tail_BC` | packs and tail on `G7LocalPackBC` | the above |
| `G0ModNewform.g8LocalPack_of_{K,D,U}`, `g15RamG_of_pack{K,R,D,U}`, `g7LocalPackK_of_R` | packs | the above |
| `G0ModNewform.modularConstituent_tail_{K,R,D,U}` (`TailK.lean`) | G13-G16 on the packs | local-data's `modularConstituent_tail_L` |

Proof of `torsFix_of_descent`:
- `E` is the fixed field of `H = decomp⁻¹(resQ_L(Stab(A₀[q]))) ∩ G_M`.
- `H` is open: it contains `G_{E₀}`, where `E₀` is `M` with the images of a basis of `L(A₀[q])`
  adjoined. `L(A₀[q])` is finite by `ptFinite`.
- `[E:ℚ_p]` equals the index of `H`, by Mathlib's `IntermediateField.finrank_eq_fixingSubgroup_index`.
- That index is `relIndex · [G_{ℚ_p} : G_M]`, and the `relIndex` is at most `[G_L : Stab]`.
- For wild `σ ∈ G_E`, `decomp σ = resQ_L σ₀` with `σ₀ ∈ Stab`. Raynaud on `A₀` and the `p`-power
  period give that `σ₀` fixes `A₀[ℓⁿ]` (D2), and `φ` carries this to `A`.

Proof of `betaTwist2_of_roots`:
- `M` is the fixed field of `U = {σ ∈ G_{L_v} : β(σ) = η(σ)}`.
- `U` is the kernel of `β/η : G_{L_v} → μ₄(ℚ̄_ℓ)`, so its index is at most
  `card(rootsOfUnity 4) ≤ 4`.
- `U` is open: `β` is locally constant (`betaOpen_of_isLocallyConstant`) and `η` is continuous.
- On wild inertia of `G_M`, `β = η = 1`.

Proof of `beta4Inertia_of_clauses` (`p = 2`):
- `chiLevel T₋ ∣ 4M` with `M` odd;
- inertia at `2` fixes the roots of unity of odd order;
- `σ²` fixes `μ₄`;
- so `cyc_N(σ²) = 1`, and `β⁴ = ι(χ(cyc_N σ))² = ι(χ(cyc_N σ²)) = 1`.

## 4. Findings

- **G1 (VERIFIED, compiled).** `LocalGlue` is false for some data (`not_localGlue_zero`).
- **G1' (SPECULATIVE, not formalized).** `LocalGlue` is not implied by
  `G7Out ∧ G8Out ∧ G7Clauses`. Example:
  - `L = ℚ`, and `A = E²` over a cyclic degree-`p` field `K ⊆ ℚ(ζ_{p²})`;
  - `Tm = ψ ⊗ tate`, with `ψ` of order `p` and conductor `p²`, trivial on `G_K`;
  - then `a·Tm(σ) = ψ(σ) ≠ 1` on some wild `σ`.

  `KerWild` is the missing link.
- **G2 (VERIFIED, read).** g0-mod-field's `G7Data` (`scratch/g0-mod-field/ModField.lean`
  l.611-631) has the kernel-field clause. g0-mod-galois's `G7Out` does not.
- **G3 (VERIFIED, arithmetic).** At `p ∈ {2,3,5}` the descent cannot be avoided: for every
  `m ≥ 3`, `‖GL₄(ℤ/m)‖` is divisible by `2`, `3` and `5`. Glazer's `E = L_v(A_L[m])` needs the
  model over `L`. `DescentPts` supplies it, and `torsFix_of_descent` is exactly Glazer's argument.
- **G4 (VERIFIED, compiled).** At `p ≥ 7`, `p ∤ ‖GL₄(𝔽₃)‖` (`p ≠ 13`) and `13 ∤ ‖GL₄(𝔽₇)‖`. So
  the torsion field can be replaced by `L_v` itself, and no descent or degree bound is needed.
- **G5 (VERIFIED, compiled).** The PkgI2 leaves I2-Tors and R6 apply to PkgI3 abelian varieties
  through `ObjBridge.toGrp`: torsion, the group law and `galAct` agree definitionally. R6 needs a
  base change (`bcPt`) and valuation rings at the place of `embP` (`normVS`), both built.
- **G6 (VERIFIED, compiled). T16 is not needed for G15 at `p = 2`.** local-data's `BetaUpper`
  bounds the conductor of `β|G_F` by local reciprocity. Instead:
  - `betaUpper_of_twist` uses a degree-`≤ 4` field `M` and the already-proved break bound;
  - `M` comes from `UnramRoots` and the proved `Beta4Inertia`.
- **G7 (VERIFIED, logical; fixed).** Raynaud at `m = p` would be unsatisfiable. `RaynaudPlace` is
  only claimed, and only used, at `m` prime to `p`.
- **G9 (VERIFIED, compiled).** `resQ K` restricts along an embedding `K ↪ ℚ̄` chosen by
  `IsAlgClosed.lift`. For `K = L'` and the model field `L`, the two choices can differ on `L` by
  `γ ∈ Gal(L/ℚ)`, so `(A₀)_{L'}` descends to the conjugate model `A₀ ×_{L,γ} L`, not to `A₀`
  itself. `descentPts_baseChange` handles this.
- **G8 (VERIFIED, read).** g0-assemble's `TateBridge` (`scratch/g0-assemble/parts/75_modfield.lean`
  l.1002-1020, `def TateBridge` at l.1007) produces `G7Out` with `ℚ̄_ℓ`-valued `β'`, but no relation to G7Data's `ℂ^×`-valued
  `β` or to `L' = ker β`. So `KerWild` for `β'` does not follow from its output.
  - Correction: add `KerWild K β' L` (equivalently `β' = ι ∘ β` with `ι` injective on roots of
    unity) to `TateBridge`'s conclusion.
  - Likewise, `DescentPts` can be added as the conjugate-model statement of `A_{L'} = (A_L)_{L'}`.

## 5. What remains

1. `UnramRoots` (textbook): Lean needs unramified extensions of `p`-adic fields of every degree,
   with cyclic Galois group generated by Frobenius. Mathlib 4.35 has neither (prereq-survey; not
   re-checked here).
2. Integration: `TateBridge` (g0-assemble) should also output the transport `β' = ι ∘ β`
   (`ι` injective). Then its data fills `G7LocalPackBC`, and `g15RamG_of_packBC` gives
   `G15RamG`.

## 6. Compile record

- `lake env lean scratch/local-glue/LocalGlue.lean`: exit 0, 0 errors, no `sorry`, about 90 s.
  All 78 `#print axioms` lines are standard (`compile.out`).
- `lake env lean scratch/local-glue/TailK.lean`: exit 0, 0 errors, no `sorry`, about 70 s.
  `modularConstituent_tail_{G,L,K,R,D,U,BC}` have standard axioms (`tail_compile.out`).
- Verbatim copies, VERIFIED by construction (`cat`/`sed -n` in the build scripts):
  - `scratch/local-data/LocalData.lean` and `Tail.lean`, whole;
  - `part_galois.lean` l.40-58;
  - `neron_block.lean`, `bc_block.lean` (`mk_*_block.sh`);
  - `resq_block.lean` (`mk_resq_block.sh`, with namespace renames listed there);
  - `dim_block.lean` (`mk_dim_block.sh`, g0-dim). Its 12 Mathlib imports, found by a test
    compile, are in `dim_imports.txt`. `import Mathlib` breaks a `rfl` in local-data's verbatim
    `Tail.lean`, so it is not used;
  - `G8LocalPack` (between the markers in `part_pack.lean`).
