# g0-split: the one `sorry` of the H decomposition, split into named pieces

Task g0-split, 2026-11-12. Lean: `scratch/g0-split/Split.lean` (assembled by
`scratch/g0-split/build.sh` from `scratch/h-decomposition/Leaves.lean`, glue-ssbc's proof and the
new section `scratch/g0-split/part_split.lean`). Log: `scratch/g0-split/log.md`.

## 1. Result

**`HSyn.glueOutputs_of_leaves` is now proved, with no `sorry`.** Its hypotheses are the two leaf
bundles, two concrete leaves, and eight named glue pieces. Each glue piece is a `def … : Prop`
whose docstring names its glue step. VERIFIED: `lake env lean scratch/g0-split/Split.lean` gives
0 errors and no `declaration uses sorry` (19983 lines, 4m13s). `#print axioms` gives
`[propext, Classical.choice, Quot.sound]` for `HSyn.glueOutputs_of_leaves`,
`HSyn.sixContactMin_of_leaves`, `G0Split.transfer_core`, `G0Split.javanpeykarJ1`,
`G0Split.thetaPazuki` and `G0Split.semisimpleBaseChange`.

```
theorem HSyn.glueOutputs_of_leaves (r : ResearchLeaves) (t : TextbookLeaves)
    (hR18 : R18_JavanpeykarConcrete) (hR22 : R22_PazukiConcrete)
    (hDim : DimBaseChange) (hBelyi : X1BelyiOnModel) (hSimp : FibreSimple)
    (hAdd : HeightAdditivity) (hBC : StableHeightBaseChange) (hProd : IsogenousProduct)
    (hThetaPt : ThetaPointOfFibre) (hMod : ModularConstituent) :
    GlueAssembly.GlueOutputs ZInQ.Mult.S_mul
```

`HSyn.sixContactMin_of_leaves r t hR18 hR22 m : ZInQ.SixContactMin` follows. Here
`m : G0Split.MissingPieces` bundles the eight pieces, and the proof composes with glue-assembly's
proved G18-G20.

**Why two concrete leaves are separate hypotheses.** In `ResearchLeaves`, `r18` and `r22` are
still `opaque` placeholders, so nothing can be derived from them. leaf-push2 stated both
concretely. Its two statements are copied here, transported to this file's objects (the same
definitions, with def-faltings' height taken through `LeafAdopt.abVarEquiv`), as
`R18_JavanpeykarConcrete` and `R22_PazukiConcrete`. Once leaf-push2 is folded into the bundles,
they become `r.r18` and `r.r22`.

### The missing pieces, smallest first

All sizes are SPECULATIVE: small < 500 lines, medium 0.5-3k, large 3-10k, very large > 10k.

| # | Lean name | glue step | statement (informal) | proved parts | size |
|---|---|---|---|---|---|
| 1 | `DimBaseChange` | definition level (used by E2, G17) | `dim (A_L) = dim A` for an abelian variety and any field extension (Stacks 00P4; STANDARD) | — | medium |
| 2 | `X1BelyiOnModel` | E2, Belyi half | every `J₁(N)` over `ℚ` (`IsJ1`) is the Jacobian of a pointed curve with a Belyi function of degree `≤ N²` | `belyiDeg_Gamma1_le`, `genus_Gamma1_le`; it follows from leaf-modcurves' glue target `BelyiX1` by transport along `ℚ(X) ≅ K_N` (transport not done) | medium |
| 3 | `FibreSimple` | G5-G6 on `A` (QM dichotomy + NoCM) | for `u ∉ 𝒞`, every number-field model `A` of the fibre surface over `J(u)` is simple over its field (`PkgI3.EndDivision`) | `qmDichotomy_B6` (T27), `GlueRepo.PR.fibre_free`, `LeafQM.AV.cm_of_val`, Elkies identities | medium |
| 4 | `HeightAdditivity` | E4 | `h_F(A) + h_F(Z) ≤ h_F(P)` for `P ≅ A × Z` (`IsProductOf`) over a number field | — (needs Néron models and H5, rv-blueprints F1) | medium-large |
| 5 | `StableHeightBaseChange` | definition level (E3-E4) | `h_F^st(A_L) = h_F^st(A)` for number fields `K ⊆ L` | — (for def-faltings' infimum it needs semistable reduction and H5's Néron minimality) | large |
| 6 | `IsogenousProduct` | G17 after Poincaré | from T8's isogeny `(f, g) : A × Z → J`, three things: `A × Z` exists as an abelian variety `P`, there is an isogeny `J → P`, and `dim J = dim A + dim Z` | — (products of abelian varieties, quasi-inverse isogenies, dimension under isogeny; Mumford §8, UNVERIFIED) | large |
| 7 | `ThetaPointOfFibre` | G19, F1 on `A` | for `u ∉ 𝒞` and the fibre surface `A`: a uniformization of `A(ℂ)_σ`, a period matrix `Ω ∈ 𝔥₂` and an algebraic theta-null point `z ∈ L¹⁶`, whose ten even coordinates `z'` satisfy `Φ(z') = J(u)` and `h(z') ≤ h(z)` | `PkgI1.f1_algebra`, `PkgI1.thetaRatio_invariant`, leaf-push2's `linYangTuple_onQMLocus` | very large |
| 8 | `ModularConstituent` | G2, G4, G7-G16 | for `u ∉ 𝒞` and an object `P` over `J(u)`: a number field `L' ⊆ ℚ̄` with `[L':ℚ] ≤ QM`, a model `A/L'` of `P`'s surface, a level `1 ≤ N ≤ QM²`, a `J₁(N)` over `ℚ`, and a common constituent of `V_ℓ(A)` and `V_ℓ(J₁(N)_{L'})` (E1's hypothesis) | cores of B3, D1-D5, G16, C2, C10, G12, G13, A6, G11 (names in the docstring) | very large |

Order: pieces 1-2 are standard algebraic geometry with existing partial Lean. Pieces 3-6 need
abelian-variety theory (endomorphisms, Néron models, products, isogenies) that Mathlib lacks.
Pieces 7-8 contain most of Glazer's Section 4. Piece 8 is the bulk: it bundles every
Galois-representation step (descent, de Rham, oddness, modularity, conductor). It is one piece
because its outputs share one existential (the same `L'`, `A`, `N`). Splitting it further needs
named intermediate objects (`r_ℓ`, `χ`, `f`) attached to the actual `A`.

## 2. Each field of `GlueOutputs`: the step that produces it

`GlueOutputs S` asks, for every `u ∉ 𝒞`, for `K'`, `z ∈ K'¹⁰`, `h_A`, F1, Pazuki, and
`NonCMOutput Q M h_A ∨ CMOutput h_A`.

| field | glue step | how it is produced in `Split.lean` |
|---|---|---|
| `K'`, `z`, `Φ(z) = J(u)` | G19 F1 | piece 7 |
| `PazukiOutput (h(z)) h_A` | G19 F3 (R22) | **proved**: `thetaPazuki`, R22 at `X = max(1, h_A + 3)` (the hardened form, rv-leaves-a), `log π ≤ 3`, piece 7's height comparison |
| `h_A` | stable Faltings height of the model `A/L'` | `faltingsHeight A`, a real number by H5 (`r.h5.1`) |
| `1 ≤ N`, `N ≤ QM²` | G13-G16 | piece 8 |
| `h_F(J₁(N)) ≤ 1.3·10⁷N¹²` | G18/E2 (R18) | **proved**: `javanpeykarJ1` (`13·10⁶·g·d⁵` with `g, d ≤ N²`) from concrete R18, piece 2, T34. Moved to `L'` by piece 5 |
| `2 ≤ g` | G17 | piece 6's `dim J = 2 + dim Z` with `dim A = 2` (`model_dim`, from piece 1 and `QML3.surface`) |
| `g ≤ N²` | E2 | **proved**: `LeafModCurves.dim_J1_le` (T34) with piece 1 |
| `1 ≤ d` | — | **proved** (`Module.finrank_pos`) |
| `d ≤ QM` | G7 (B3) | piece 8 |
| `L ≤ 1024g³(…)` | E3 (R19) | **proved**: `transfer_core` (R19 on the isogeny `J₁(N)_{L'} → A × Z`; `log κ` computed in `log_grKappa`) |
| `h_A + h_Z ≤ h_F(J) + L/2` | E4 | **proved** in `transfer_core` from R20 and piece 4 |
| `−(3/2)g ≤ h_Z` | E4 (R21) | **proved** in `transfer_core` from R21, with `dim Z ≤ g` from piece 6 |
| CM disjunct | — | not used: the route excludes CM by NoCM (G6), and the non-CM disjunct is supplied |

The isogeny of G17 is built from proved pieces: E1 (`PkgI3.E1_exists_hom_ne_zero`, from R9a,
R9b, T26 and glue-ssbc's `SemisimpleBaseChange`) gives a nonzero `A → J₁(N)_{L'}`; piece 3 says
`A` is simple; T8 (a leaf) gives `(f, g) : A × Z → J`; piece 6 turns this into Gaudron-Rémond's
input.

## 3. Checks on the pieces

**A false piece would make the reduction vacuous.** Each piece was checked to be a true
statement given the published mathematics. These are model checks, with no human review.

- **The fix found (VERIFIED as a logical point).** The first draft had a piece "for every
  number-field model `A/K` of the fibre there is `L ⊇ K` with `[L:ℚ] ≤ QM` …". That is false
  (base-change a model to a field of degree `> QM`). The draft compiled anyway. Now piece 8
  produces the field and the model together, as in Glazer (his `L'` contains the fibre field).
- **Pieces 3 and 7 quantify over all models `A` of the fibre.** That is harmless: simplicity
  over the field of definition follows from `End⁰(A_ℚ̄) = B` being a division algebra, and the
  theta point and the stable height are geometric.
- **Pieces 3, 7 and 8 quantify over every moduli datum `(Y, Φ, π)` satisfying `R1fpProps`,
  `R2fpProps`.** Their truth uses that these clauses pin down `Y₃` and the Hauptmodul (`π` is
  fixed by its values at the three CM points). This inherits the SPECULATIVE premise
  bp-qmmoduli §2.2 of every leaf-qm-fp object.
- **Pieces 4 and 5 are true for the published Faltings height.** For def-faltings' infimum they
  are true only if that definition is correct, which is exactly what H5 asserts (with
  `AnalyticUniformizationExists`, `HodgeLatticeTheorem`). Pieces 1 and 6 are textbook.
- **`FibreOver` ties `A` to `u`:** an iso of `ℚ̄`-schemes `A_ℚ̄ ≅ P.A` with an object `P` at a
  point of `Y₃` over `J(u)`. A scheme iso of abelian varieties is a group iso up to translation
  (rigidity), so heights and endomorphisms are determined.

## 4. What compiles, what remains

- Compiles (VERIFIED): the whole of `Split.lean`, with no `sorry`. Everything in
  `Leaves.lean` before the old `glueOutputs_of_leaves` is unchanged.
- New proved Lean: `model_dim`, `dim_eq_of_iso`, `log_grKappa`, `one_le_grKappa`,
  `transfer_core`, `javanpeykarJ1`, `thetaPazuki`, `hom_of_common`, and the main theorem.
- Copied proofs: glue-ssbc's `SemisimpleBaseChange` (section `GlueSSBCSec`) and leaf-push2's
  R22 definitions (`cptObj`, `CPts`, `IsUniformization`, `IsSiegel`, `IsPeriodMatrix`,
  `thetaConst`, `absLogHeight`, `pazukiC2`, `ffAlgebra`, `javanpeykarBound`).
- Remains: the eight pieces of §1. The cheapest next steps are (a) piece 2 from `BelyiX1` by
  transport (a pure Lean exercise once `BelyiX1` is proved), and (b) splitting piece 8 along
  G7 / G8-G12 / G13-G16 once `r_ℓ` and the twist are defined on the actual `A`.
- Integration: replace `Leaves.lean`'s §3 tail (from `glueOutputs_of_leaves` on) by
  `part_split.lean`, insert `GlueSSBCSec` before `namespace HSyn`, and, when leaf-push2 is folded
  in, replace the hypotheses `hR18`, `hR22` by `r.r18`, `r.r22`.
