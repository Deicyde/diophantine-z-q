# def-faltings: the stable Faltings height, first layer, in Lean

Status: research note (task def-faltings, 2026-11-12). Lean: `scratch/def-faltings/Faltings.lean`
(Mathlib only, self-contained, compiled, no `sorry`, no `axiom`). Results log:
`scratch/def-faltings/log.md`. It follows the blueprint `docs/research/bp-faltings.md`; §1-14 of
the Lean file are copied from `scratch/bp-faltings/Hodge.lean`. No file under `ZInQKernel/` or
`blueprint/`, and no other task's notes or scratch files, was edited.

Marks: **VERIFIED** = compiled, or read in a source in the repository or in Mathlib.
**STANDARD** = published, with a reference. **SPECULATIVE** = estimate. **UNVERIFIED** = a locator
recalled from memory (no network).

## 0. Main result

1. **The stable Faltings height is now a Lean definition over Mathlib's objects** (VERIFIED:
   compiled; `#print axioms` lists `propext`, `Classical.choice`, `Quot.sound`):

   ```lean
   noncomputable def stableFaltingsHeight {K : Type} [Field K] (A : AbVar K) : EReal :=
     ⨅ (E : FinExt K) (g : ℕ) (M : MetrizedModel A E.L g), (M.hodge.modelHeight : EReal)
   ```

   The infimum (node H3) runs over number fields `L ⊇ K`, smooth separated finite-type group
   models `𝒢/𝓞_L` of `A_L` (node M1), and their metrized Hodge lines. A metrized model has:
   - the genuine algebraic lattice `⋀^g ω_𝒢`, built in Lean from the local rings of `𝒢` along the
     unit section (nodes AV3, AV4, M2, M3; §2 below);
   - archimedean data constrained by a concrete Prop, `IsAnalyticUniformization`;
   - the model height formula of `HodgeData.modelHeight` (bp-faltings), which uses Faltings'
     original normalization `(i/2)^g`.

   No definition contains an `axiom`, a `sorry`, an opaque constant or a structure made up for
   the purpose.
2. **The missing analytic input is one precisely stated theorem, not a hole in a definition.**
   - `AnalyticUniformizationExists` (node AN3) says: for every group model `𝒢` and every
     `τ : L → ℂ` there are a full lattice `Λ ⊂ ℂ^g` and a map `Φ : ℂ^g → 𝒢(ℂ)_τ` with
     `IsAnalyticUniformization 𝒢 τ Λ Φ` (the Prop quantifies `g` existentially; it does not tie `g` to
     `dim A`). That Prop asks that `Φ` be a surjective group
     homomorphism with kernel exactly `Λ`, that every `Φ⁻¹(U(ℂ))` be open, and that every regular
     function on every open `U ⊆ 𝒢` be holomorphic along `Φ` there.
   - `AnalyticUniformizationUnique` says that two such `Φ` differ by a `ℂ`-linear automorphism
     of `ℂ^g`.
   - Both are stated over Mathlib's objects: `𝒢(ℂ)_τ` is the group of `𝓞_L`-morphisms
     `Spec ℂ → 𝒢`, and regular functions are evaluated at points through `Scheme.Hom.appLE`.
     Neither is proved.
   - Without them the definition is still the right one, but nothing excludes `h = ⊤` (empty
     index set). The algebraic analogue is `HodgeLatticeTheorem`: `⋀^g ω_𝒢` is a full lattice in
     an `L`-line. It is also stated and unproved.
3. **Proved over the definition** (VERIFIED, compiled):
   - the model height does not depend on the uniformization, given
     `AnalyticUniformizationUnique` (`MetrizedModel.modelHeight_eq_of_model_eq`). The proof uses
     two new lemmas:
     - the coefficient map is determined by its values on the wedges `1 ⊗ df₁∧⋯∧df_g`
       (`GroupModel.semilinear_ext_wedge`);
     - the chain rule `jacDet (Φ ∘ T) = jacDet Φ · det T` (`GroupModel.jacDet_comp`);

     then bp-faltings' `modelHeight_recoord` absorbs `T`;
   - `GroupModel.height`, and `stableFaltingsHeight A = inf_{L, 𝒢} 𝒢.height`
     (`stableFaltingsHeight_eq_iInf_height`);
   - Deligne's normalization: `stableFaltingsHeightDeligne A = stableFaltingsHeight A + (g/2) log π`
     when all metrized models have dimension `g` (`stableFaltingsHeightDeligne_eq`, node H6);
   - acceptance tests AT1 and AT2 in conditional form over the general definition (§4).
4. **Leaves.**
   - R19 (Gaudron-Rémond), R20 (Faltings' Lemma 5) and R21 (Bost, in Gaudron-Rémond's form) are
     stated as Lean Props over `stableFaltingsHeight` and genuine `AbVar`s, isogenies and
     degrees.
   - R18 (Javanpeykar) and R22 (Pazuki) cannot be stated yet. Their height side is ready,
     including `h_D = h_F + log π` for surfaces. The missing objects are curves with their genus,
     Belyi maps, Jacobians, polarizations and theta heights (§5).

## 1. Definitions (Lean names, `ZInQ.DefFaltings`)

| Node | Lean | Content |
| --- | --- | --- |
| AV1, M1 | `AbVar`, `GroupModel` | copied from bp-faltings `Models.lean` (project `Objects.lean`, without its `IsCommMonObj` instance; `AbVar.dim` as in Objects.lean:181) |
| — | `genericPt L`, `GroupModel.unitSection`, `genericUnit` | `η ∈ Spec 𝓞_L`; `e = η[𝒢].left : Spec 𝓞_L → 𝒢`; `ξ = e(η)` |
| AV3 | `GroupModel.genStalk`, `cotangent`, `dCls` | `𝒪_{𝒢,ξ}` (= `𝒪_{A_L,0}`), `ω_{A_L} = 𝔪_ξ/𝔪_ξ²` (Mathlib `IsLocalRing.CotangentSpace`), `f ↦ df` |
| — | `structMap` | `𝓞_L = Γ(S) → Γ(𝒢) → 𝒪_{𝒢,ξ}`; the `𝓞_L`-module structure on `cotangent` (definitional) |
| M2 | `omegaAt s`, `omega` | `(ω_𝒢)_s` = span of the image of `I_{e(s)} = ker(𝒪_{𝒢,e(s)} → 𝒪_{S,s})` under specialization to `ξ`; `ω_𝒢 = ⋂_s (ω_𝒢)_s` |
| AV4 | `hodgeSpace g` | `L ⊗_{𝓞_L} ⋀^g_{𝓞_L} cotangent` (`≅ ⋀^g_L ω_{A_L}`) |
| M3 | `detLattice g`, `wedge f` | `𝓞_L`-span of `1 ⊗ v₁∧⋯∧v_g`, `vᵢ ∈ ω_𝒢`; `wedge f = 1 ⊗ df₁∧⋯∧df_g` |
| AN3 (data) | `ptC τ`, `Pts τ`, `evalAt`, `dom` | `𝒢(ℂ)_τ = Hom_{𝓞_L}(Spec ℂ, 𝒢)` (group by Mathlib's `MonObj.Hom.group`); value of `s ∈ Γ(U, 𝒪)` at `p ∈ U(ℂ)`; `Φ⁻¹(U(ℂ))` |
| AN3 (Prop) | `IsAnalyticUniformization 𝒢 τ Λ Φ` | homomorphism, kernel `= Λ`, surjective, `Φ⁻¹(U(ℂ))` open, regular functions holomorphic along `Φ` |
| AN3 → H1 | `germAlong`, `jacDet` | germ at `ξ` composed with `Φ` (through a chosen representative); `det(∂(fᵢ∘Φ)/∂z_j(0))` |
| M4 | `MetrizedModel A L g` | `model`, `hodge : HodgeData L g (model.hodgeSpace g)`, `lattice_eq : hodge.lattice = detLattice g`, `arch : ∀ τ, ∃ Φ, IsAnalyticUniformization … (hodge.periods τ) Φ ∧ ∀ f, hodge.coeff τ (wedge f) = jacDet Φ f` |
| H2 | `GroupModel.height` | `⨅ g, ⨅ M with M.model = 𝒢, modelHeight` |
| H3 | `FinExt K`, `stableFaltingsHeight` | index structure `(L, Field, NumberField, Algebra K L)`; the infimum in `EReal` |
| H6 | `stableFaltingsHeightDeligne` | each term shifted by `(g/2) log π` |
| — | `faltingsHeight A := (stableFaltingsHeight A).toReal` | meaningful only with `StableHeightFinite`; never used in a leaf |
| H5 | `GroupModel.IsNeronModel`, `StableHeightFinite`, `NeronModelMinimal` | Néron mapping property (bijectivity of `Hom(𝒴, 𝒩) → Hom(𝒴_L, A_L)` for smooth `𝒴`); statements of H5 |

## 2. Why each choice is the published object (STANDARD, not proved in Lean)

- **`ω_𝒢`.**
  - `𝒪_{𝒢,ξ}` is the local ring of `𝒢_L ≅ A_L` at the origin, so `𝔪_ξ/𝔪_ξ²` is `ω_{A_L}`.
  - For a section `e` of a smooth `𝒢/S`, `e*Ω¹_{𝒢/S} ≅ e*(I/I²)`, the conormal sheaf of `e`
    (EGA IV 17.2.5, UNVERIFIED locator). Its stalk at `s` is `I_x/I_x²` for `x = e(s)`, and it
    injects into the generic stalk `I_ξ/I_ξ² = 𝔪_ξ/𝔪_ξ²` because `I_x/I_x²` is free over
    `𝒪_{S,s}`.
  - A locally free sheaf on the integral scheme `Spec 𝓞_L` has global sections equal to the
    intersection of its stalks in the generic stalk.
  - In `omegaAt`, the condition "the specialization lies in `𝔪_ξ`" always holds; it is imposed
    so that the definition needs no proof term. The span adds nothing, because the image is
    already an `𝒪_{S,s}`-module.
- **The Hodge line.** `cotangent` is an `L`-vector space, so
  `L ⊗_{𝓞_L} ⋀^g_{𝓞_L} cotangent ≅ ⋀^g_L ω_{A_L}` (localization commutes with `⋀`). If `g` is
  not the dimension of `A` and `g > 0`, the field `hodge.finrank_eq_one` cannot hold, so there is
  no metrized model with that `g`. The case `g = 0` passes `finrank_eq_one`, because
  `hodgeSpace 0 ≅ L`. It is excluded for `dim A > 0` by surjectivity of `Φ : ℂ⁰ → A_τ(ℂ)`.
- **Archimedean data.**
  - Let `Φ` satisfy the Prop and let `Λ` be a full lattice. Then `Φ` is continuous for the
    analytic topology, because the topology of each `U(ℂ)` is induced by the regular functions on
    `U`. So `Φ` induces a continuous bijection from the compact space `ℂ^g/Λ` onto the Hausdorff
    space `A_τ(ℂ)`. This bijection is a homeomorphism and is holomorphic, hence biholomorphic.
  - Two such maps differ by a biholomorphic group isomorphism of tori, which lifts to a linear
    map of `ℂ^g`. That is the content of `AnalyticUniformizationUnique`.
  - An invariant `g`-form is determined by its value at `0`, so
    `Φ*(df₁∧⋯∧df_g) = det(∂(fᵢ∘Φ)/∂z_j(0)) dz₁∧⋯∧dz_g`. `HodgeData.norm` then gives
    `|c|²·covol(Λ) = (i/2)^g ∫ |η∧η̄|` for Lebesgue measure on `ℂ^g = ℝ^{2g}`: Faltings'
    normalization (bp-faltings §1).
  - The value `jacDet Φ f` depends only on the classes `dfᵢ`. Indeed, germs agree on an open
    neighbourhood of `0`; products of functions vanishing at `0` have derivative `0`; constants
    `c ∈ 𝓞_L` evaluate to `τ(c)` at `τ`-points. So `arch` is consistent with
    `τ`-semilinearity.
- **Why the infimum cannot be pushed down by fake data.**
  - `lattice_eq` fixes the lattice.
  - `arch` fixes `(Λ, coeff)` up to the linear changes above, under which `modelHeight` is
    invariant: proved, given uniqueness, as `MetrizedModel.modelHeight_eq_of_model_eq`.
  - So the values in the infimum are exactly the model heights `h(A_L, 𝒢)`.
  - Through the Néron mapping property and SGA 7 IX, the infimum is the Néron-model value over a
    semistable field (node H5, not proved; locators UNVERIFIED).

## 3. The named gaps (statements in the Lean file, all unproved)

| Name | Content | Node | Needed for |
| --- | --- | --- | --- |
| `AnalyticUniformizationExists` | every `𝒢(ℂ)_τ` has an analytic uniformization by `ℂ^g/Λ` (Mumford, *Abelian varieties* §1 with GAGA-type input; UNVERIFIED locator) | AN3 | `h < ⊤` |
| `AnalyticUniformizationUnique` | two uniformizations differ by a linear automorphism | AN3 | independence of the uniformization (already reduced to this) |
| `HodgeLatticeTheorem` | `finrank_L (hodgeSpace g) = 1` and `detLattice g` full, for `g = dim A` | AV2-AV4, M2, M3 | `h < ⊤` |
| `StableHeightFinite`, `NeronModelMinimal` | `h ≠ ⊤, ⊥`; the Néron model minimizes the height over each `L` | H5 (Néron, BLR; SGA 7 IX) | `faltingsHeight` is meaningful; AT1/AT2 unconditional |

Content of AN3 in Mathlib terms. Mathlib v4.35 cannot yet:
- put a complex-manifold structure on `X(ℂ)` for a smooth `ℂ`-scheme (analytification);
- prove that `X(ℂ)` is compact for `X` proper;
- prove that a compact connected commutative complex Lie group is a torus.

The Prop `IsAnalyticUniformization` avoids all three, because it tests holomorphy against regular
functions directly. So the definition needs none of this theory; only the theorem does.
Route (a) of bp-faltings §2.3 is the recommended way to prove the theorem.

## 4. Acceptance tests

| Test | Lean | Status |
| --- | --- | --- |
| AT1 statement | `AcceptanceEC : Prop`: for `W` elliptic over a number field `K` and `A : AbVar K` with `IsEllipticCurveOf A W`, `stableFaltingsHeight A = faltingsHeightEC W` | stated; unproved (needs AV7, AN4, AN5, M2 for the minimal model, AT1a, H5) |
| AT1 identification | `IsEllipticCurveOf A W`: `A ∖ {O}` is an affine open whose ring of functions is `K`-isomorphic to Mathlib's `W.toAffine.CoordinateRing` | the smooth projective model of a function field is unique, and so is the group law with a given origin (rigidity): STANDARD |
| AT1 conditional | `stableFaltingsHeight_eq_faltingsHeightEC` | **proved**. The hypotheses are the outputs of the missing nodes: a metrized model over `K` with lattice free on `η₀` and `η₀ ↦ dz` for period pairs (AN4, M2); the Weierstrass polynomial equal to `4x³ − g₂x − g₃` after a translation `x ↦ x + c_σ`, so any `b₂` is allowed, e.g. 11a1 with `b₂ = −4` (AN4); the vanishing finite part (AT1a); `PeriodAreaFormula` (AN5); and `hmin` (H5). **Caveat:** `hmin` ("no metrized model has smaller height") is literally the `≥` half of the conclusion. The theorem's content is the computation `M.hodge.modelHeight = faltingsHeightEC W`. `hmin` is what H5 (`IsNeronModel`, `NeronModelMinimal`, semistable base change) must supply. The theorem does not assume `IsEllipticCurveOf A W`; `M` is tied to `W` only through its hypotheses |
| AT2 statement | not writable: no Jacobians in Mathlib v4.35, so no way to say that an `AbVar` is `Jac C` | — |
| AT2 conditional | `HodgeData.modelHeight_eq_faltingsHeightGood`, `stableFaltingsHeight_eq_faltingsHeightGood` | **proved**. Hypotheses: lattice free on `η₀ = ω₀∧ω₁` (M8), archimedean metric `= hypVol 2` (AN6, Riemann bilinear relations), `hmin` (H5; same caveat as AT1) |

The right-hand sides `faltingsHeightEC` and `faltingsHeightGood` are pkg-I5's definitions, copied
verbatim.

## 5. Leaves over the general height

Normalizations follow `docs/research/locators.md`:
- R19 and R20 use the stable height in Faltings' original normalization, i.e.
  `stableFaltingsHeight`;
- R21 is in Gaudron-Rémond's form;
- R22 uses Deligne's metric, `h_D = h_F + (g/2) log π` (`stableFaltingsHeightDeligne_eq`).

When the height is an *input* to a bound (R19, R20), it enters through a real `x` with
`stableFaltingsHeight A = x`, never through `toReal`. The junk value `toReal ⊤ = 0` would make the
statement stronger than the published one.

| Leaf | Lean | Remarks |
| --- | --- | --- |
| R19 Gaudron-Rémond, Duke 163 (2014) Thm 1.4 | `R19_GaudronRemond` | `A.dim = g`, `h(A) = x`, `A`, `B` isogenous ⇒ isogenies `A → B` and `B → A` of degree `≤ grKappa g [K:ℚ] x = ((14g)^{64g²}[K:ℚ]max(x, log[K:ℚ], 1)²)^{1024g³}`. Specialized `k = K`; audit: YES with number-field hypotheses |
| R20 Faltings 1983 Lemma 5 | `R20_FaltingsLemma5` | `\|h(A) − h(B)\| ≤ ½ log deg φ`; Lemma 5 unread (audit: UNVERIFIED, including direction and hypotheses) |
| R21 Bost (via Gaudron-Rémond §9) | `R21_Bost` | `−(3/2) g ≤ h(A)` in `EReal`; `stableFaltingsHeight_ne_bot_of_R21` (proved) |
| R18 Javanpeykar | not stated | missing: genus of curves over `ℚ̄`, Belyi maps, Jacobians (AV7) |
| R22 Pazuki | not stated | missing: principal polarizations, level-2 theta structures and the theta height of an abelian surface; the genus-2 special case over `faltingsHeightGood` is rv-loc-leaves' `PazukiGoodGenus2Literal` |

Isogenies (`IsIsogeny`) are group-scheme homomorphisms (`IsMonHom`) that are finite and surjective
(the project's `IsIsogenyMor`). The degree `isogDeg φ` is `#ker φ(K̄)`, which equals the degree in
characteristic 0 (STANDARD). Dimension is the project's `AbVar.dim`, the Krull dimension of the
underlying space.

Caveat on vacuity. Until AN3 and `HodgeLatticeTheorem` are proved:
- lower bounds on `h` (R21) are trivially true when `h = ⊤`;
- R19 and R20 have no instance with `h = ⊤`.

The leaves are the published statements (or consequences of them); they become non-vacuous
exactly when the gaps are closed.

## 6. What compiles (VERIFIED)

`lake env lean scratch/def-faltings/Faltings.lean` reports no errors and no warnings. Every
`#print axioms` at the end of the file lists `[propext, Classical.choice, Quot.sound]`. The
listed declarations are: `stableFaltingsHeight`, `stableFaltingsHeight_le`,
`stableFaltingsHeightDeligne_eq`, `GroupModel.semilinear_ext_wedge`, `GroupModel.jacDet_comp`,
`MetrizedModel.modelHeight_eq_of_model_eq`, `GroupModel.height_eq`,
`stableFaltingsHeight_eq_iInf_height`, `faltingsHeight_coe`,
`stableFaltingsHeight_eq_faltingsHeightEC`, `HodgeData.modelHeight_eq_faltingsHeightGood`,
`stableFaltingsHeight_eq_faltingsHeightGood`, `stableFaltingsHeight_ne_bot_of_R21`,
`HodgeData.modelHeight_recoord`, `modelHeight_ofIdeal_eq_faltingsHeightEC`,
`GroupModel.omegaAt_genericPt` (16 in all; the last added in e5605439, listed by notes-fix).

## 7. What remains (recommended order; sizes SPECULATIVE)

1. `HodgeLatticeTheorem` (M-L): the dimension of `𝔪_ξ/𝔪_ξ²` from smoothness; projectivity of
   `ω_𝒢`; `⋀^g` of a rank-`g` projective module is invertible.
2. AN5 `PeriodAreaFormula` (M) and AN4 (L): these make AT1 unconditional on the archimedean side.
3. `AnalyticUniformizationExists` and `AnalyticUniformizationUnique` (XL): node AN3, route (a)
   of bp-faltings §2.3.
4. AV7 (L for elliptic curves): construct `A` with `IsEllipticCurveOf A W`. Then `AcceptanceEC`
   becomes a theorem modulo H5, AT1a and M2 for the minimal model (§4).
5. H5 (XL): Néron models and semistable reduction; `StableHeightFinite`, `NeronModelMinimal`.
6. R18 and R22: Jacobians, Belyi maps, polarizations, theta heights.

## 8. Independent review

A model review of §15-22 of the Lean file was run against the Mathlib sources and locators.md.
It found no faithfulness error in the definitions. It confirmed:
- the map directions in `omegaAt`;
- the line `hodgeSpace`;
- that `IsAnalyticUniformization` pins `Φ` down up to linear changes and excludes fake data
  (Galois twists, `g > dim A`, degenerate `Φ`);
- the Deligne shift;
- that R19-R21 are not stronger than the published statements.

It flagged three issues, all fixed:
- AT1's polynomial hypothesis forced `b₂ = 0`; it now allows a translation, as bp-faltings'
  `modelHeight_ofIdeal_eq_faltingsHeightEC'` does;
- `hmin` is half of the conclusion; this is now documented as the caveat in §4;
- the docstring on a wrong `g` was false for `g = 0`; it is now corrected.

The bp-faltings bridge `modelHeight_eq_faltingsHeightEC` (free case, copied in §5 of the Lean
file) still carries the `b₂ = 0` restriction. The general conditional theorem above does not use
it.

## 9. Unchecked items

- Locators recalled from memory: EGA IV 17.2.5; BLR 1.2/1, 1.4/3, 9.5 Thm 4; SGA 7 IX 3.3, 3.6;
  Mumford §1.
- The faithfulness arguments of §2 are STANDARD mathematics, not Lean proofs.
- `IsEllipticCurveOf` and `isogDeg` are faithful by standard arguments (§4, §5), not by Lean
  proofs.
