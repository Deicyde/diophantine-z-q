# g0-mod-galois: glue steps G8-G12 (the Galois side of `ModularConstituent`)

Task g0-mod-galois, 2026-11-13. Lean: `scratch/g0-mod-galois/part_galois.lean` and
`scratch/g0-mod-galois/part_bundle.lean` (namespace `G0Galois`). `scratch/g0-mod-galois/build.sh`
appends them to g0-split's `scratch/g0-split/Split.lean`, giving
`scratch/g0-mod-galois/ModGalois.lean`. Log: `scratch/g0-mod-galois/log.md`. The base merges
`origin/wip/g0-split` (c20fa62b) for `Split.lean`.

## 1. Result

COMPILE-STATUS

```
theorem G0Galois.g8_g12_of_leaves (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : GaloisPieces)
    {K : Type} [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K) (T : Finset ℕ)
    (h2 : G2Out K T) (h6 : G6Out A) (h3 : G3Out A 5 T)
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl 5) (Vb A 5))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5) (a β : PkgI4.GQ → PadicAlgCl 5)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl 5) (Vb A 5))
    (h7 : G7Out A 5 Tm c ε a β u) :
    ∃ r₅ : GaloisRep 5 2, G8Out A 5 (GlueDescent.rho Tm a β) r₅ ∧ G9Out r₅ ∧ G10Out r₅ ∧
      G11Out T r₅ ∧ G12Out r₅
```

`m : GaloisPieces` bundles the five named glue Props of this range (§3). The same statement at
any prime `ℓ`, without G12, is `G0Galois.g8_g11` (used at `ℓ = 3` by G14-G15). The version with
the leaves as separate hypotheses is `G0Galois.g8_g12`.

**What is proved, not assumed.**

- **G8** (`G0Galois.g8`). Inputs: `G7Out`, the leaves R9a, R9b, T6, T26, and glue-ssbc's proved
  `SemisimpleBaseChange`. The descended operators `ρ = β⁻¹ a Tm` form a representation of `G_ℚ`
  (glue-descent's `rhoRep`). `ρ` commutes with the matrix units of `B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)` and is the
  Tate action on `G_{L'}`. `dim (ℚ̄_ℓ ⊗ V_ℓ(A)) = 4` comes from T26 with `dim A = 2`, so
  `W = e₀₀ V ≠ 0`. C2 (`PkgI3.C2_absolutelyIrreducible`), applied to `splitEquiv`, makes `ρ|_W`
  absolutely irreducible on `G_{L'}`. The step from there to a continuous
  `r : G_ℚ → GL₂(ℚ̄_ℓ)` in Burnside form is the named linear-algebra piece `G8Matrix`.
- **G11** (`G0Galois.g11`). Proved from `G2Out`, `G3Out` and G8's intertwining, with no named
  glue: an inertia element above `p ∉ T ∪ {ℓ}` lies in `G_K` (G2). It acts trivially on
  `V_ℓ(A)` (G3 with R7a), so trivially on `r ⊕ r`, so `r(σ) = 1`.
  `finitelyRamified_of_g11` gives Pan's finite-ramification hypothesis with `S = T ∪ {ℓ}`.
- **G12** (`G0Galois.g12`). Pan∘Berger (`PkgI4.PanBerger`, the bundle's `r11r12`) is applied at
  `p = 5`. Its hypotheses come from:
  - irreducibility: G8, through `isIrreducible_of_g8`;
  - finite ramification: G11;
  - de Rham, and distinct weights `0 ≠ −1`: G9;
  - oddness: G10.

  Pan gives an eigenform `g` of some weight `k ≥ 1` and a continuous twist `ψ`. The named piece
  `G12Weight` gives `{n, n+1−k} = {0, −1}`. The proved `PkgI4.weight_match` then gives `k = 2`
  (and `n = 0`). The named piece `G12Det` gives the determinant identities, and the proved
  `GlueAssembly.twist_finite` turns them into finiteness of `ψ`.
- **Link to `ModularConstituent`** (`G0Galois.commonConstituent_of_sides`, proved). G8's `e`,
  together with what G13-G16 must deliver on the `J₁(N)` side (`JSide`), gives
  `HSyn.G0Split.CommonConstituent A J`, the last field of `ModularConstituent`, with `ℓ = 5` and
  `E = ℚ̄₅`.

## 2. The interface (all `def … : Prop` in `part_galois.lean`, with docstrings)

The coefficient field is `ℚ̄_ℓ = PadicAlgCl ℓ` throughout (Pan's coefficients). The model is
`A : PkgI3.AbVar K` over `K = L'`. ModularConstituent's model is
`ZInQ.DefFaltings.AbVar L.K`, which `LeafAdopt.abVarEquiv` carries to `PkgI3.AbVar`.
`resQ K : G_K →* G_ℚ` is Mathlib's `Field.absoluteGaloisGroup.map (algebraMap ℚ K)`, and
`tate A ℓ` is the `G_K`-action on `ℚ̄_ℓ ⊗ V_ℓ(A)` (`GlueI3.repBaseChange` of pkg-I3's `galRep`).

**Inputs (outputs of earlier steps).**

| Prop | step | content |
|---|---|---|
| `G2Out K T` | G2 (PR(i)) | every inertia element of `G_ℚ` above `p ∉ T` lies in `resQ K (G_K)` (`K = L'` unramified outside `T`) |
| `G3Out A ℓ T` | G3 (PR(ii)) + R7a | for `p ∉ T`, `p ≠ ℓ`, inertia elements of `G_K` above `p` act trivially on `ℚ̄_ℓ ⊗ V_ℓ(A)` (instantiation of `PkgI2.inertiaTrivial_of_goodReduction`) |
| `G6Out A` | G5-G6 | `End_K(A)` is a division ring (`PkgI3.EndDivision`) and is noncommutative |
| `G7Out A ℓ Tm c ε a β u` | G7 (+ A9, G4) | `dim A = 2`; `rank_ℤ End_K(A) = 4`; operators `Tm σ = a_σμ_σ∘σ` with `Tm g Tm h = c(g,h) Tm(gh)`; `a_g a_h c(g,h) = ε(g,h) a_{gh}`; `β_gβ_h = ε(g,h)β_{gh}`, `β ≠ 0`; on `G_{L'}`: `Tm = tate`, `a = β = 1`; matrix units `u` commuting with every `Tm σ`; weak continuity of `β⁻¹ a Tm` |

**Outputs of this range.**

| Prop | step | content |
|---|---|---|
| `G8Out A ℓ ρ r` | G8 | `ρ ∘ resQ = tate`; `e : ℚ̄_ℓ ⊗ V_ℓ(A) ≅ ℚ̄_ℓ² × ℚ̄_ℓ²` intertwines `ρ(g)` with `r(g) ⊕ r(g)` for every `g ∈ G_ℚ`; the matrices `r(σ)`, `σ ∈ G_{L'}`, generate `M₂(ℚ̄_ℓ)` (absolutely irreducible) |
| `G9Out r` | G9 | `LocalIsDeRham ℓ 2 (r|G_{ℚ_ℓ})` and `HasHTWeightsAtSelf ℓ {0, −1}` |
| `G10Out r` | G10 | `r.IsOdd` |
| `G11Out T r` | G11 | `r` unramified at every prime `p ∉ T`, `p ≠ ℓ` |
| `G12Out r₅` | G12 | `∃ N ≥ 1, χ, g ∈ S₂(Γ₁(N))` normalized eigenform with nebentypus `χ`, `ψ` continuous of finite image, `ιC`, `ιL`, `S` finite: `r₅.AttachedUpToTwist ψ ιC ιL g S` |

## 3. What remains: five named glue Props (none is a leaf)

Sizes are SPECULATIVE (small < 500 lines, medium 0.5-3k, large 3-10k).

| Prop | content | inputs named in it | why true | size |
|---|---|---|---|---|
| `G8Matrix` | `ρ` on `ℚ̄_ℓ ⊗ V_ℓ(A)` of dimension 4 commuting with matrix units, weakly continuous, with `ρ\|_W` absolutely irreducible on `G_K` ⇒ continuous `r` with `e` intertwining `ρ` and `r ⊕ r` on `G_ℚ`, and `r(G_K)` spanning `M₂(ℚ̄_ℓ)` | none (linear algebra) | basis of `W` (`finrank_W`), `splitEquiv`, continuity from weak continuity, Burnside over the algebraically closed `ℚ̄_ℓ` (Mathlib has `jacobson_density`) (STANDARD) | small-medium |
| `G9Glue` | R10 → T23 → (`ℚ̄_ℓ ⊗ V_ℓ(A) ≅ r\|G_K ⊕ r\|G_K`, `dim A = 2` ⇒ `G9Out r`) | R10 (`DeRhamComparison`), T23 | N5's appendix lemma (h-trust C3, two model reviews) with the Galois choice of the local field. Needs base change of `PkgI3.AbVar` to a completion, the identification of pkg-I3's and pkg-I4's `AbVar` copies, and the reduction to a finite coefficient field | medium-large |
| `G10Glue` | T11 → T12 → R9b → (`K` Galois, `End_K(A)` rank 4, division, noncommutative, the same splitting ⇒ `r` odd) | T11, T12 (opaque placeholders), R9b | N5 L742-751 (h-trust C5). For any extension `r`, `φ = ρ(c)∘c⁻¹` is `B`-linear and in `Hom(A^c, A) ⊗ ℚ̄_ℓ` (Faltings), so it equals `a·μ_c`, and the Betti argument applies. SPECULATIVE as a reduction; each step STANDARD or model-reviewed | medium (needs analytification) |
| `G12Weight` | R14 → R13 → R15 → T18 → T19 → (Pan's output for an irreducible `r` with weights `{0,−1}` ⇒ `∃ n, {n, n+1−k} = {0,−1}`) | R13, R14, R15, T18, T19 | `r ≅ ρ_g ⊗ ψ` (Chebotarev, Brauer–Nesbitt), weights of a twist shift by the weight of `ψ`. For `k = 1`, Deligne–Serre gives weights `{0,0}`, which contradicts `{0,−1}` (h-trust C8) | medium (HT weights of tensor products) |
| `G12Det` | R14 → T9 → (`r` split on `G_K` as above, attached up to `ψ` to a weight-2 `g` ⇒ `H` of finite index, characters `dr, ε, χ_c` with `dr = εχ_cψ²`, `dr² = χ_c²` on `H`, `ε` of finite image) | R14 (determinant clause, as published), T9 | h-trust C8 items 1-3 (V16 L660-667). `dr = det r`, `ε` = the nebentypus, `χ_c` = cyclotomic, `H` = `G_K`. `det r = det(ρ_g ⊗ ψ)` everywhere (traces agree on a dense set, `det = (tr² − tr(g²))/2`); `det V₅(A) = χ_c²` (T9) and `V₅ ≅ r ⊕ r` | small-medium (plus R14's determinant clause, see below) |

**A leaf gap found (VERIFIED by reading the statement).** `G12Det` needs `det ρ_g = ε_g χ_c`
(at `k = 2`). The bundle's R14 (`HSyn.EigenformRepExists`, consequence form) omits the
determinant: its docstring says "the published statements also give the determinant". Its
`AttachedTo` gives only traces of arithmetic Frobenius elements at `p ∤ Nℓ`. These do not fix
`det ρ_g(Frob_p)`, since `Frob_p²` is not an arithmetic Frobenius at `p`. So either R14 is
strengthened to the published statement with `det ρ_g = ε_g χ_c^{k−1}` (still a consequence of
the published theorem, so still a leaf), or `G12Det` keeps this as glue from Eichler–Shimura.
Recommendation: strengthen R14 (one clause).

## 4. How the conclusion feeds G13-G16 and `ModularConstituent`

`ModularConstituent` (scratch/g0-split/part_split.lean) asks, for `u ∉ 𝒞` and a fibre object
`P`, for the following:

- `L'`, an embedding `L' → ℚ̄` and a model `A/L'` of `P.A`. Supplied by the G2-G7 range.
- `N ≥ 1` and `J ≅ J₁(N)` over `ℚ` (`IsJ1`). Supplied by G13.
- `N ≤ QM²`, supplied by G16, and `[L':ℚ] ≤ QM`, supplied by G7.
- `CommonConstituent A (J_{L'})`.

This range supplies `r₅` (and `r₃`) and closes `CommonConstituent` through the link lemma:

1. **Into G13** (g0-mod-newform's range). The input is `G12Out r₅`: a weight-2 eigenform `g`,
   `ψ` of finite image, and `r₅.AttachedUpToTwist ψ ιC ιL g S`. G13 first turns `ψ` into a
   Dirichlet character: its kernel field is finite abelian, so Kronecker–Weber (T17) applies,
   and h-trust C8 item 4 is this step. G13 then absorbs `ψ` into `g` (T24, `EigenformTwist`),
   takes the newform `f` (T25), and identifies `r₅ ≅ ρ_{f,5}` by Chebotarev with Brauer–Nesbitt
   (T18, T19). For the last step, `r₅` is irreducible by `isIrreducible_of_g8`, hence
   semisimple. R16 (`LeafModCurves.g13_constituent`) then puts `ρ_{f,5}` inside
   `V₅(J₁(N))`.
2. **Into G14-G15.** `g8_g11` at `ℓ = 3` gives `r₃` with G8-G11. G14 compares traces of `r₃`
   and `r₅`, which needs `G8Out`'s intertwining of `ρ` on all of `G_ℚ` (the descended operators,
   not only `G_{L'}`). G15 uses `G11Out` (unramified outside `T ∪ {ℓ}`) for the conductor
   exponent 0 outside `T`.
3. **Into `ModularConstituent`.** G13-G16 must deliver
   `JSide (J_{L'}) r₅`: an injective `G_{L'}`-equivariant map `ℚ̄₅² → ℚ̄₅ ⊗ V₅(J_{L'})` with
   `G_{L'}` acting on `ℚ̄₅²` by `r₅(resQ σ)`. Here `J_{L'}` is
   `abVarEquiv L'.K (((abVarEquiv ℚ).symm J).baseChange L'.K)`, as in `ModularConstituent`.
   `commonConstituent_of_sides A J r₅ e hint hJ : CommonConstituent A J` (proved) then gives the
   last field of `ModularConstituent`. Here `e`, `hint` come from `G8Out` through
   `intertwines_res`, and the `A` is the same model as in `G7Out`, through `abVarEquiv`.

So `ModularConstituent` follows from three pieces, `(G2-G7 outputs) ∧ (this theorem) ∧ (G13-G16:
N, J, IsJ1, N ≤ QM², JSide)`, plus the proved link lemma. That assembly is not written here,
because it needs the other two ranges' statements.

## 5. Checks

- **Truth of the named Props.** Each was checked as a statement about the genuine objects (model
  check, no human review); the arguments are in the docstrings and §3. Two points:
  - `G8Matrix` first had `dim A = 2` as hypothesis. Then it is true but not provable without T26.
    It now takes `dim (ℚ̄_ℓ ⊗ V_ℓ(A)) = 4`, which `g8` proves from T26.
  - `G10Glue` needs `K` Galois over `ℚ`. Glazer's `L'` is Galois (N5 L711-712).
- **No vacuity from the inputs.** The input Props are satisfiable: with `c = ε = 1` on `G_{L'}`
  they are consistent, and the matrix units must commute with the Tate action, which the
  `B`-action does.
- **T11, T12 are opaque placeholders** in the bundle. `G10Glue` names them as inputs for
  documentation only; logically they carry no content.

## 6. Status of the files

LEAN-STATUS
