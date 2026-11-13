# rleaf-elliptic: the leaves about elliptic curves

Task rleaf-elliptic, 2026-11-13. Branch `wip/rleaf-elliptic`, base 322303a2 (wip/integrate-w39),
with fork main 6c225515 merged. Results log `scratch/rleaf-elliptic/log.md`.

Marks: **VERIFIED** means compiled, or read in the source. **STANDARD** means a published theorem
with its reference. **SPECULATIVE** means an assessment. Theorem numbers given from memory are
marked UNVERIFIED.

## 0. Main result

Two textbook leaves about elliptic curves are now **proved outright**. Each closed theorem has
exactly the leaf's Prop as its type, with no hypotheses. As a consequence, the glue target
`LeafModCurves.BelyiX1` (E2's Belyi half, consumed through `G0Split.x1BelyiOnModel_of_belyiX1`)
now holds with no hypotheses. All of this is VERIFIED: `lake build ZInQKernel.Contrib.RLeaf.BelyiX1`
succeeds, and every `#print axioms` line reads `[propext, Classical.choice, Quot.sound]`.

| Declaration | Type (exact) | File |
|---|---|---|
| `ZInQ.RLeaf.t36_torsionStructure` | `X1Belyi.TorsionStructure` (leaf **T36**) | `ZInQKernel/Contrib/RLeaf/T36Torsion.lean` |
| `ZInQ.RLeaf.T37.t37_goodReductionUnramified` | `X1Belyi.GoodReductionUnramified` (leaf **T37**) | `ZInQKernel/Contrib/RLeaf/T37GoodReduction.lean` |
| `ZInQ.RLeaf.belyiX1` | `LeafModCurves.BelyiX1` (glue target) | `ZInQKernel/Contrib/RLeaf/BelyiX1.lean` |
| `ZInQ.RLeaf.x1Leaves_of` | `X1Belyi.CurveOfFunctionFieldQ → X1Belyi.X1ConstantField → X1Belyi.X1RationalCusp → X1Belyi.X1Leaves` | same |
| `ZInQ.RLeaf.x1ModelExists_of` | `X1Belyi.CurveOfFunctionFieldQ → X1Belyi.X1ConstantField → X1Belyi.X1RationalCusp → LeafModCurves.X1ModelExists` | same |

The leaf statements, verbatim from `ZInQKernel/HDecomp/ModCurves/X1Belyi.lean`:

```lean
def TorsionStructure : Prop :=
  ∀ (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K] (W : WeierstrassCurve K) [W.IsElliptic]
    (N : ℕ), 0 < N → Nonempty (nTors W N ≃+ (ZMod N × ZMod N))

def GoodReductionUnramified : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (W : WeierstrassCurve (RatFunc k)) [W.IsElliptic]
    [DecidableEq (AlgebraicClosure (RatFunc k))] (p : k[X]), Irreducible p →
    (∀ a ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set (RatFunc k)),
      ∃ b c : k[X], ¬ p ∣ c ∧ a * algebraMap k[X] (RatFunc k) c = algebraMap k[X] (RatFunc k) b) →
    (∃ b c : k[X], ¬ p ∣ b ∧ ¬ p ∣ c ∧
      W.Δ * algebraMap k[X] (RatFunc k) c = algebraMap k[X] (RatFunc k) b) →
    ∀ P : (W.baseChange (AlgebraicClosure (RatFunc k))).toAffine.Point,
    (∃ N : ℕ, 0 < N ∧ N • P = 0) →
    ∀ w : ValuationSubring (IntermediateField.adjoin (RatFunc k) {xCoord P}),
      (∀ c : k[X], algebraMap (RatFunc k) _ (algebraMap k[X] (RatFunc k) c) ∈ w) →
      algebraMap (RatFunc k) _ (algebraMap k[X] (RatFunc k) p) ∈ w.nonunits →
      ∀ x ∈ w.nonunits, ∃ y ∈ w,
        x = algebraMap (RatFunc k) _ (algebraMap k[X] (RatFunc k) p) * y
```

`#print axioms` output (VERIFIED, from the build log):

```
'ZInQ.RLeaf.nTors_eq_torsionBy' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.t36_torsionStructure' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.T37.core' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.T37.t37_goodReductionUnramified' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.belyiX1' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.x1Leaves_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.RLeaf.x1ModelExists_of' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Effect on the leaf list.** T36 and T37 leave the textbook list, which goes from 35 leaves to 33.
The `x1` field of `TextbookLeaves` (`X1Belyi.X1Leaves`) now needs only T38, T39 and T40
(`x1Leaves_of`). `BelyiX1` needs nothing, and `X1ModelExists` needs only T38-T40
(`x1ModelExists_of`). No research-level leaf changes, because none of them is about elliptic
curves (§1).

## 1. Survey: which leaves are about elliptic curves

Sources: docs/research/h-decomposition.md §2 (the leaf table), the Lean statements in
`scratch/h-decomposition/Leaves.lean` and `ZInQKernel/HDecomp/`, docs/research/tc-survey.md
(origin/wip/tc-survey), and the oct16 Tau Ceti tree (`~/tc-oct16`). The verdicts were read in the
statements (VERIFIED). Effort grades are SPECULATIVE.

### 1.1 Research-level leaves (R1-R22, H5)

**No research-level leaf is a statement about elliptic curves**, and none reduces to one. Each
leaf is quantified over abelian varieties of every dimension, over QM abelian surfaces, over
eigenforms, or over Faltings heights. The proof uses each of them on a dimension-2 object (the QM
fibre surface) or on `J₁(N)`. The only elliptic objects that appear inside research-leaf
statements are listed in the table.

| Leaf | Objects | Elliptic content | Lean reach | Effort for the elliptic part |
|---|---|---|---|---|
| R1 Shimura–Deligne | PEL moduli of QM surfaces | none (QM surfaces are "fake elliptic curves", dimension 2) | in part (`QML3`) | — |
| R2 Baba–Granath | `X₆`, its Hauptmodul | the three CM values `0, ∞, −16/27` are where the QM surface is isogenous to `E × E` with CM by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` (STANDARD, Rotger) | yes (`R2X6PropsIff`) | very large; CM theory of `E × E` with QM is not in Lean or Tau Ceti |
| R3 Lin–Yang | abelian surfaces with QM over ℂ | the second disjunct `A ≅ E₁ × E₂` (Weil's dichotomy at `j ∈ {0, ∞}`), a weaker conclusion, not an input | yes (`LeafPush2.R03_LinYang`) | very large (Jacobians, Weil 1957) |
| R4 Igusa theta | genus-2 theta constants | none | yes | — |
| R5 González–Rotger | CM points of `X₆` | CM QM surfaces are isogenous to `E²` with `E` CM; the count `2^{b(R)} h(R)` is a class-number statement (SPECULATIVE: could go through CM elliptic curves) | yes (`R5fpStrong`, `R5fpCount`) | very large |
| R6 Raynaud | abelian varieties over a DVR | the case `g = 1` is not used (A6 applies it at `g = 2`) | yes (`PkgI2.RaynaudCriterion`) | the `g = 1` case would not discharge the leaf |
| R7 Serre–Tate (NOS, potential good reduction) | abelian varieties over a DVR | the case `g = 1` is in Tau Ceti, over nonarchimedean local fields only: `WeierstrassCurve.isUnramified_divisionField_iff`, `isUnramified_divisionField_pow_of_tateModuleGaloisRepresentation_eq_one` (TateModule/Unramified.lean), `HasPotentialGoodReduction.finite_image_tateModuleGaloisRepresentation` (TateModule/PotentialGoodReduction.lean), all oct16 (VERIFIED, read) | yes (`PkgI2.NeronOggShafarevich`, `SerreTatePotentialGood`) | the leaf is for all `g` and every DVR; a `g = 1` form needs the bridge AV7 (an `AbVar` of dimension 1 ↔ a Weierstrass curve), which is absent, and it would not discharge the leaf |
| R8 Grothendieck | abelian varieties | none used | monodromy form | — |
| R9 Faltings | `Hom`, `T_ℓ` of abelian varieties | none (the `g = 1` case is still Faltings or Serre) | yes | — |
| R10-R12 | p-adic Hodge theory, Pan | none | yes | — |
| R13-R15 | eigenforms, Galois representations | none (modularity of elliptic curves is not used) | yes | — |
| R16 Eichler–Shimura in `J₁(N)` | newforms, `J₁(N)` | the model of `X₁(N)` is defined through `E_j` (`K_N = ℚ(j)(x(P))`); the conclusion is about `J₁(N)` | yes (`R16_EichlerShimuraJ1'`) | — (no elliptic reduction) |
| R17 Carayol | ℓ-adic conductors | none | placeholder (concrete form `CarayolR17'`) | — |
| R18 Javanpeykar | Faltings height of `Jac X`, Belyi maps | its Belyi input on `X₁(N)` is the glue `BelyiX1`, **proved here** (§0) | yes | done for the input; the leaf itself is not elliptic |
| R19-R22, H5 | Faltings heights of abelian varieties | the case `g = 1` is the acceptance test AT1 (`AcceptanceEC`, not a leaf), proved conditionally (`stableFaltingsHeight_eq_faltingsHeightEC`) | yes | AT1 needs AV7, AN3-AN5 and H5 itself |

So no research-level leaf is in reach through elliptic curves. To use Tau Ceti's elliptic results
for R7 one would need these **new definitions** (SPECULATIVE sizes):
- a bridge `AbVar`-of-dimension-1 ↔ `WeierstrassCurve`. `IsEllipticCurveOf` (AT1) is the
  statement; its existence half is AV7, which needs Riemann–Roch on a genus-1 curve (large).
- the DVR-generality of Tau Ceti's NOS. Tau Ceti assumes `IsNonarchimedeanLocalField`, that is a
  finite residue field (medium).

Even with both, the `g = 1` statements do not discharge the leaves, which the proof uses at
`g = 2`.

### 1.2 Textbook leaves about elliptic curves

| Leaf | Statement | Source | Status |
|---|---|---|---|
| **T36** `X1Belyi.TorsionStructure` | `E[N] ≅ (ℤ/N)²` over `K = K̄`, char 0 | Silverman, AEC Cor. III.6.4(b) (UNVERIFIED number) | **proved here** (Tau Ceti `WeierstrassCurve.torsion_addEquiv_prod`) |
| **T37** `X1Belyi.GoodReductionUnramified` | NOS over `k(T)`, residue characteristic 0 | Serre–Tate 1968 Thm 1; AEC VII.4.1, VIII.1.5(b) (UNVERIFIED numbers) | **proved here** (§2) |
| T39 `X1Belyi.X1ConstantField` | `ℚ` is algebraically closed in `K_N` | Igusa 1959; Shimura 1971 §6.2, Prop. 6.9 (UNVERIFIED) | open; needs Igusa's theorem (the monodromy of `E_j[N]` over `ℚ̄(j)` is `SL₂(ℤ/N)` up to `±1`); large |
| T40 `X1Belyi.X1RationalCusp` | `K_N` has a degree-1 place | Tate curve, Silverman ATAEC V.3.1; Ogg 1973 (UNVERIFIED) | open; needs the same Igusa transitivity (all points of exact order `N` are conjugate up to sign) plus a Tate-curve embedding `K_N → ℚ((q^{1/N}))`; Tau Ceti has the analytic Tate curve (TateCurve/, oct16); large |
| T38 `X1Belyi.CurveOfFunctionFieldQ` | curves from function fields | Hartshorne I.6, II.6.7 | not elliptic; very large |
| T5, T9, T26 | torsion, Weil pairing, Tate module of abelian varieties | Mumford | Tau Ceti has `g = 1` only (`card_ker_mulByIntIsogeny`, `tateModuleWeilPairing`, `free_tateModule`); the leaves are used at `g = 2`; not discharged |

## 2. The proof of T37

The statement: `k` has characteristic 0, `W/k(T)` has good reduction at an irreducible `p`, `P` is
a torsion point over `\overline{k(T)}`, and `w` is a valuation ring of `F = k(T)(x(P))` containing
`k[T]` with `p ∈ 𝔪_w`. Then `𝔪_w = p·w`. The Lean proof
(`ZInQKernel/Contrib/RLeaf/T37GoodReduction.lean`, 575 lines) runs as follows.

1. **The division field.** `divField W N = k(T)(x(Q), y(Q) : N•Q = 0) ⊆ \overline{k(T)}`.
   - It is finite over `k(T)`, because the `N`-torsion is finite: Tau Ceti `WeierstrassCurve.finite_torsionBy`.
   - It is Galois: it is stable under `Aut(\overline{k(T)}/k(T))`, by `IntermediateField.normal_iff_forall_map_le`.
   - Every `N`-torsion point over `\overline{k(T)}` descends to it (`exists_point_divField`), so
     the coordinates of its own `N`-torsion generate it (`adjoin_coords_eq_top`).
   - `F ≤ divField W N`, because `N • P = 0`.
2. **Extension of `w`.** `exists_valuationSubring_extend` uses Mathlib's
   `IsLocalRing.exists_factor_valuationRing`. It gives a valuation ring `B` of `M = divField W N`
   with `B ∩ F = w` and `𝔪_w ⊆ 𝔪_B`.
3. **`core`.** Let `𝒪_M` be the integral closure of `k[T]` in `M` (a Dedekind domain).
   - `𝒪_M ⊆ B`, so `u = 𝔪_B ∩ 𝒪_M` is a height-one prime, and `B` is the valuation ring of `u`.
     The two inclusions are proved directly, with `exists_primeCompl_mul_eq_of_integer`.
   - The coefficients of `W` are `u`-integral and `Δ` is a `u`-unit. This gives Mathlib's
     `IsIntegral` instance and `IsElliptic` for the integral model.
   - Tau Ceti's `WeierstrassCurve.inertiaSubgroup_eq_bot_of_adjoin_coords_eq_top` (vendored
     `Affine/Point/Inertia.lean`) then says that the inertia group of `𝒪_u` in `Gal(M/k(T))` is
     trivial (AEC VIII.1.5(b)).
   - The bridge `mem_inertiaSubgroup_of_forall_sub_mem` transfers this to the ideal-theoretic
     `Ideal.inertia`. It uses Tau Ceti's `valuation_ringEquivOfRingEquiv` and the presentation
     `y = n/d` with `d ∉ u`.
   - Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` gives `e(u|p) = 1`. The residue fields
     have characteristic 0, so they are perfect and separable.
   - With `Ideal.eq_prime_pow_mul_coprime`, `e = 1` gives `p ∉ u²`. So `v_u(p) = exp(−1)` (Tau
     Ceti `intValuation_eq_exp_neg_one_of_mem_of_notMem_sq`), and `y/p ∈ B` for every `y ∈ 𝔪_B`.
4. **Back to `F`.** For `x ∈ 𝔪_w`, `x/p ∈ B ∩ F = w`.

## 3. Vendoring and licence (VERIFIED)

- 192 modules from the oct16 closure of
  `AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure`
  (`scratch/rleaf-elliptic/vendor-new.txt`).
- 38 modules from the closure of `AlgebraicGeometry.EllipticCurve.Affine.Point.Inertia`
  (`vendor-new2.txt`).
- All 230 are from commit 5a01f5fe, copied by `tcport.py`. One file is modified:
  `AlgebraicGeometry/EllipticCurve/Projective/Prime.lean`, where `prime_X` is renamed to `X_prime`,
  its name in the pinned Mathlib. The file carries the `-- Modified for the Z-in-Q kernel` line,
  and NOTICE lists it.
- `ThirdParty/TauCeti/NOTICE` has a new source entry.
- `diffcheck2.py`: IDENT 1624, NOTE-ONLY 0, MOD-NOTED 30, MOD-UNNOTED 0.

## 4. What remains (not proved)

- T39, T40: both need Igusa's theorem. A reduction to (i) Igusa transitivity on the points of exact
  order `N` up to sign and (ii) one Tate-curve point with an embedding `K_N → ℚ((q^{1/N}))` is
  sketched in §1.2. It is not in Lean.
- T38: not elliptic.
- Research leaves: none is elliptic (§1.1).

No statement change is proposed.
