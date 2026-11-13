# rv-g0pieces: adversarial truth review of g0-split's ten glue pieces

Task rv-g0pieces, 2026-11-13. Object: the ten `def … : Prop` pieces of
`scratch/g0-split/part_split.lean` (assembled into `scratch/g0-split/Split.lean`, namespace
`HSyn.G0Split`), merged from `origin/wip/g0-split` (c20fa62b). Split.lean is not edited.
Scratch: `scratch/rv-g0pieces/` (log `log.md`, `Exotic.lean`, `nocm_square_check.py`,
`theta_igusa_check.py`). Model review only, no human review.

## 1. Verdict

**No piece is refuted. Seven are TRUE outright. Three are UNSURE, for one shared reason: as
stated, they cannot be proved from the leaves.** `FibreSimple`, `ThetaPointOfFibre` and
`ModularConstituent` quantify over *every* triple `(Y, Φ, π)` with `R1fpProps Y Φ` and
`R2fpProps Y Φ π`. g0-split justified this with "these clauses pin down `Y₃` and the
Hauptmodul" (g0-split.md §3). That is **false for `Φ`**. `R1fpProps` asks only that `Φ` be
natural under field homomorphisms. Composing `Φ` with a natural, non-geometric relabeling `τ`
of the field points of `Y` keeps both clause lists (compiled in `Exotic.lean`:
`r1fp_exotic`, `r1r2_relabel`; §3). Such a `τ` can move the points over `J(u)` to the points over another
rational value of `π`, provided the two fibres are isomorphic as finite étale `ℚ`-schemes.

- For the genuine triple, all three pieces are true. The arguments are below.
- For a relabeled triple, `FibreSimple` fails if a rational non-contact fibre is
  `ℚ`-isomorphic to a rational CM fibre. `ThetaPointOfFibre` fails if a fibre over `J(u₁)` is
  `ℚ`-isomorphic to a fibre whose theta point has height `< (h(J(u₁)) − 22)/40`.
- Whether such coincidences exist is an open arithmetic question. No such pair was found or
  excluded here.
- Either way, a Lean proof of these pieces as stated would have to rule the coincidences out.
  So the pieces are not provable glue in their present form, and the reduction is sound only
  if no coincidence exists.

The repair (§4) is to pin `Φ` in the leaf: `Y₃` is a fine moduli scheme, so `Φ` is induced by
a universal family. The pieces then quantify over triples with that family.

| rank | piece | verdict | one-line reason |
|---|---|---|---|
| 1 | `ThetaPointOfFibre` | **UNSURE** (universal form); TRUE for the genuine triple | F1 identity; constant `3779136` now checked numerically (§2.9); relabeled triples could break the height inequality |
| 2 | `FibreSimple` | **UNSURE** (universal form); TRUE for the genuine triple | NoCM (A10) plus descent of isogenies; relabeled triples could attach a CM class to `J(u)` |
| 3 | `ModularConstituent` | TRUE for the genuine triple, given Glazer §4; universal form UNSURE, likely robust (SPECULATIVE) | bounds `[L':ℚ] ≤ QM` (L713) and `N ≤ QM²` (L857) match the manuscript; the model is produced with the field |
| 4 | `HeightAdditivity` | TRUE (given def-faltings = the published stable height) | Néron model of a product is the product |
| 5 | `StableHeightBaseChange` | TRUE | provable from the definition (transport and base change of models, normalized heights) |
| 6 | `ReverseIsogeny` | TRUE | quasi-inverse of an isogeny, composed with `A × Z ≅ P` |
| 7 | `ProductExists` | TRUE | products of abelian varieties |
| 8 | `X1BelyiOnModel` | TRUE (given `BelyiX1`, which is true) | transport along `ℚ(X) ≅ K_N`; `[K_N : ℚ(j)] ≤ N²` |
| 9 | `DimBaseChange` | TRUE | dimension of a finite-type scheme over a field is invariant under any field extension |
| 10 | `DimFinite` | TRUE | proper ⇒ finite type; integral ⇒ nonempty |

## 2. Each piece

### 2.1 `ThetaPointOfFibre`: UNSURE as stated, TRUE for the genuine triple

*Statement.* For `u ∉ 𝒞` and `A/K` with `FibreOver Y Φ π u K A`, the piece asks for:

- a complex place `σ`;
- an analytic uniformization `Φu` of `A(ℂ)_σ` with kernel `Λ`;
- a period matrix `Ω ∈ 𝔥₂` of `Λ`;
- an algebraic representative `z ∈ L¹⁶` of `[θ_m(0, Ω)]`;
- a point `z' ∈ K'¹⁰` with `3779136 (∏z')⁴/(∑z'⁸)⁵ = J(u)` and `h(z') ≤ h(z)`.

*Genuine triple.* Choose an embedding `ι : ℚ̄ → ℂ` with `ι ∘ emb = σ`. Then
`A_σ ≅ (P.A)^γ` for some `γ ∈ Gal(ℚ̄/ℚ)`, and that surface lies over `γ(J(u)) = J(u)` because
`J(u)` is rational. The remaining existentials are filled as follows:

- `Φu`, `Λ`: complex uniformization.
- `Ω`: the period matrix of the principal polarization with Rosati involution `x ↦ μ⁻¹x̄μ`.
  It exists for QM by the maximal order (QML3 docstring, bp-qmmoduli §2.2).
- `z`, `L`, `c`: the theta-null ratios. They are algebraic, because they are values of level-(4,8)
  modular functions at a `ℚ̄`-point (STANDARD, Igusa/Shimura; UNVERIFIED locator). The six odd
  values are 0.
- `z'`, `K'`: take `K' = L` and `z'` = the ten even coordinates. Zero coordinates do not change
  the sup-norm height, so `h(z') ≤ h(z)`.

Since `J(u) ≠ 0, ∞` (`F(u) ≠ 0` off `𝒞`; `G` has no real root), the denominator is nonzero.
`Φ` is homogeneous of degree 0, so `c` cancels. The identity is F1. This review checks its
constant numerically in §2.9.

*Universal form.* Let `τ` swap the fibre over `J(u₁)` with a `ℚ`-isomorphic fibre over another
rational value `s₂` (§3). For `relabel Φ τ`, the piece asks for `z'` with `Φ(z') = J(u₁)` and
`h(z') ≤ h(θ(A_{s₂}))`. But `Φ(z') = J(u₁)` forces `h(J(u₁)) ≤ 40 h(z') + 22` (manuscript L928).
So the piece is false for that triple as soon as `h(J(u₁)) > 40·h(θ(A_{s₂})) + 22`.

*What would settle it.* Either a proof that rational fibres of `Y₃ → P¹` over distinct values
(with `u ∉ 𝒞`) are never `ℚ`-isomorphic, which looks out of reach, or the repair of §4.

### 2.2 `FibreSimple`: UNSURE as stated, TRUE for the genuine triple

*Genuine triple.* For `u ∉ 𝒞`, `End⁰(P.A) = B` is NoCM (h-trust A10, status [M]; rv-nocm).
This review adds an independent consistency check (`nocm_square_check.py`, VERIFIED):

- `t(u) = 1 + 27J(u)/16 = (H/G³)²` and `1 − t(u) = 3(180F/G³)²`.
- None of Elkies' 24 rational non-elliptic CM values passes this square test.
- `H² − t_D G⁶` has no rational root for any of the 24.
- The elliptic values are hit only at `F(u) = 0`, i.e. `u ∈ 𝒞` (`F`'s rational roots are exactly
  `𝒞`; `G` and `H` have none).

Then `A_ℚ̄ ≅ P.A` as schemes. Composing with a translation gives an iso of abelian varieties
(rigidity). `End_K(A) ↪ End(A_ℚ̄)`, and `End(A_ℚ̄)` is an order in the division algebra `B`.
So a nonzero `f` becomes an isogeny after base change, and finiteness and surjectivity descend
(fpqc). R2fp pins `π`: on `X₆/W ≅ P¹` it is bijective on `ℚ̄`-points, so it is a Möbius map in
characteristic 0, fixed by its three CM values.

*Universal form.* A relabeling `τ` swapping the fibre over `J(u₁)` with a `ℚ`-isomorphic
rational CM fibre gives a triple satisfying R1fp and R2fp (`r1r2_relabel`). For that triple,
`FibreOver` attaches to `u₁` a surface with CM. Over a large enough field its model is not
simple, so `EndDivision` fails. At the level of `X₆` no such fibre isomorphism exists:

- the fibre over `J(u)` is a free `W`-orbit with residue field `ℚ(i)`;
- the only rational CM fibres with quadratic residue field are those of `D = −19, −43, −67, −163`,
  with field `ℚ(√D)` (rv-nocm Part B, read).

But on `Y₃` the isomorphism of fibres need not respect the projection to `X₆`, so this does not
settle the question.

### 2.3 `ModularConstituent`: TRUE for the genuine triple (given Glazer §4)

- **Quantifier direction (VERIFIED).** The piece *produces* `L'`, the model `A/L'`, `N` and `J₁(N)`
  together. Its only hypothesis is a `ℚ̄`-point over `J(u)`. This is the corrected direction of
  g0-split's soundness fix.
- **Same surface at every point of the fibre (R2fp).** All points over `J(u)` carry
  twist-equivalent QM pairs, hence the same `A_ℚ̄`.
- **Bounds match the manuscript.** `Q = heightQ heightD = D^{D·E₀}`, the manuscript's `Q_R` at
  `R = D` (Height.lean L148; manuscript L392). `M = contactSupport S_mul u ≥ 1`, an empty product
  being allowed. `[L':ℚ] ≤ QM` is L713 and `N ≤ QM²` is L857 (read).
- **Common constituent.** `ρ_f` of the weight-2 newform `f` (level dividing `N`, any nebentypus)
  occurs in `V_ℓ(J₁(N)) ⊗ E`. On `G_{L'}` the twist is trivial (`twist_finite`), so `ρ_f` is a
  constituent of `V_ℓ(A) ⊗ E`. These are exactly Glazer's G8-G16.
- **Truth.** The piece is as true as Glazer's Section 4 (h-trust).
- **Universal form.** Every bound is field-level: the degree of `L'`, the ramification of `L'`
  and good reduction outside 3 over the fibre field. `M_S(u)` should be recoverable from the
  ramification of the fibre field. So a relabeling between `ℚ`-isomorphic fibres plausibly
  preserves truth, and the rational CM surfaces have bounded conductor while `Q` is astronomically
  large. SPECULATIVE; covered by the same repair.

### 2.4 `HeightAdditivity`: TRUE

`IsProductOf` makes `P ≅ A × Z` as group schemes. For the published stable height,
`h(A × Z) = h(A) + h(Z)`: the Néron model of a product is the product, `det ω` is a tensor
product, and the Faltings metrics multiply. In def-faltings this is
`covol(Λ_A ⊕ Λ_Z) = covol·covol` and coefficient of `η_A ∧ η_Z` = product. The shift
`(g/2) log π` of Deligne's normalization is additive in `g`.

For def-faltings' infimum:

- A smooth group model `𝒢` maps to the Néron model by the Néron mapping property.
- So `ω_𝒩 ⊆ ω_𝒢` and `h(𝒢) ≥ h(𝒩)`, since a larger lattice gives a larger Arakelov degree.
- The infimum is therefore attained at Néron models over semistable fields. It equals the
  published stable height once Néron models carry `MetrizedModel` data
  (`AnalyticUniformizationExists`, `HodgeLatticeTheorem`: true theorems).

### 2.5 `StableHeightBaseChange`: TRUE, and provable from the definition

The two directions:

- **`h(A) ≤ h(A_L)`.** A metrized model of `(A_L)_E` over an `L`-algebra `E` is a metrized model
  of `A_E`, with `E` a `K`-algebra through `L`. Here `(A_L)_E ≅ A_E` as group schemes by
  pseudofunctoriality of `Over.pullback`, and the Hodge data refer only to `𝒢`. So the infimum
  for `A` runs over a superset.
- **`h(A_L) ≤ h(A)`.** Base-change a model over `E ⊇ K` to a compositum `E' ⊇ E, L`. Smooth,
  separated and quasi-compact are preserved. `ω_{𝒢'} = 𝒪_{E'} ⊗ ω_𝒢` (the conormal sheaf of the
  unit section of a smooth group scheme commutes with base change). The complex points at
  `τ' : E' → ℂ` are those at `τ'|_E`, so the uniformization transfers. `log #(Λ'/𝒪_{E'}s)` and
  `∑_{τ'}` both scale by `[E':E]`, so `modelHeight` (normalized by `[E:ℚ]`) is unchanged.

Equality holds also when both sides are `⊤` or `⊥`. g0-split's remark that this "needs
semistable reduction and H5's Néron minimality" is too pessimistic: no Néron model is needed.

### 2.6 `ReverseIsogeny`: TRUE

`ψ = f + g : A × Z → J` is a homomorphism (`J` is commutative), finite and surjective. So it is
an isogeny, and `dim J = dim A + dim Z`. An isogeny has a quasi-inverse `χ : J → A × Z` with
`χψ = [deg ψ]` (Mumford §8, UNVERIFIED number). `χ` is finite and surjective because `[n]` is.
Compose with `(lift p₁ p₂)⁻¹ : A × Z ≅ P`, a group isomorphism because `p₁, p₂` are
homomorphisms. `IsIsogeny` (mon hom, finite, surjective) holds, and the source
`(abVarEquiv L).symm J` has the same scheme and group structure (`abVarEquiv` is the identity on
`X`, read L18773).

### 2.7 `ProductExists`: TRUE

`A ×_L Z` is a group object. It is proper and smooth, and geometrically integral as a product of
geometrically integral `L`-varieties. Its dimension is `dim A + dim Z`, finite, so the
`WithBot ℕ∞` sum is the right one. `IsProductOf` holds with the projections.

### 2.8 `X1BelyiOnModel`: TRUE (given `BelyiX1`)

`IsJ1 N J` supplies `X`, `P₀`, `aj` with `IsX1Model N X` (hence `IsCurve`, `IsIntegral`, and
`ℚ(X) ≃+* K_N`) and `IsJacobian`; reuse them.

- **Transport.** A ring isomorphism of characteristic-0 fields is `ℚ`-linear. It carries
  valuation subrings to valuation subrings, so `IsBelyiFunction` transports. Note that
  `IsBelyiFunction` quantifies over all valuation subrings containing `ℚ`; in a one-variable
  function field these are the field itself (excluded because `t` is transcendental) and the
  DVRs of places, so the definition is the intended one.
- **Degree.** `[ℚ(X) : ℚ(t)] = [K_N : ℚ(j)]`. This is `(N²/2)∏_{p|N}(1 − p⁻²)` for `N ≥ 3`, `3`
  for `N = 2` and `1` for `N = 1`, all `≤ N²`.
- **Belyi property.** `j/1728` is unramified outside `{0, 1, ∞}` (ramification only over
  `j = 0, 1728, ∞`).

### 2.9 The constant `3779136` and the CM values (part of `ThetaPointOfFibre`)

*Normalization (VERIFIED numerically, `theta_igusa_check.py`).* For two random real-rooted
sextics, the script computes period matrices by numerical integration. It searches period
combinations for a symmetric `Ω` with `Im Ω > 0`; both ratios are `Sp₄(ℤ)`-invariant, so no
theta labelling enters. It finds

`I4⁵/I10² = (∑_{even} θ_m⁸)⁵ / (∏_{even} θ_m²)²`

to relative error `7·10⁻²³` and `1·10⁻²²`.

*Consequence.* With Igusa's `J2 = I2/8`, `J4 = (4J2² − I4)/96`, `J10 = I10/4096` (STANDARD;
UNVERIFIED, from memory), Lin–Yang's identifications `ψ4 = J2² − 24J4 = I4/4` and
`χ10 = −J10/4 = −I10/2¹⁴` become Igusa's `ψ4 = 2⁻²∑θ⁸`, `χ10 = −2⁻¹⁴∏θ²` up to weighted
rescaling. On LY's Igusa vector `[12(j+1), 6(j²+j+1), ·, j³]` (h-v14 VERIFIED, `igusa_check.py`),
`I4⁵/I10² = 576⁵/(2²⁴ j)`, so

`3779136 (∏θ)⁴/(∑θ⁸)⁵ = 2⁶3¹⁰ · 2²⁴ j / (2³⁰ 3¹⁰) = j`.

This closes, numerically, the one item h-v14 left UNCHECKED: Igusa's theta normalization.

*CM values.* R2fp's values `−4 ↦ 0`, `−3 ↦ ∞`, `−24 ↦ −16/27` are Elkies' `t = 1, ∞, 0`, with
`t = 1 + 27J/16`. They agree with LY's vector: `J10 = 0` at `j = 0`, so the `D = −4` point is a
product and `∏θ = 0`. `J(u) ≤ 0` and `J(u) ∉ {0, −16/27}` off `𝒞`.

### 2.10 `DimBaseChange` and `DimFinite`: TRUE

An abelian variety is proper, hence of finite type, over `K`. It is geometrically integral,
hence nonempty. So its topological Krull dimension is a natural number. For a finite-type
scheme over a field, the dimension is invariant under an arbitrary field extension, by Noether
normalization (Stacks, the dimension-under-field-extension lemmas; tag UNVERIFIED). Both pieces
are stated for arbitrary fields and remain true there.

## 3. The relabeling argument (where the three UNSURE verdicts come from)

**Construction (VERIFIED, compiled).** A field point `y : Spec K → Y` over `ℚ` is a pair
`(x, ι : κ(x) → K)` (`Scheme.SpecToEquivOfField`). Take:

- a bijection `s` of the closed points of `Y`;
- ring isomorphisms `φ_x : κ(s x) ≅ κ(x)`.

Put `τ_K(x, ι) = (s x, ι ∘ φ_x)`. Then `τ` is a bijection, natural in `K`: post-composition
with `f : K → L` commutes with it (`specToEquivOfField_comp` in the file). `τ` comes from a
morphism of schemes only if `s` and `φ` do; nothing asks `s` to be continuous.

`Exotic.lean`, section `RvG0Exotic`, compiles this construction:

- `relabelPt` and `relabelPt_bijective`;
- `relabelPt_comp` (naturality);
- `relabelPt_point` (the point of `τ y` is `s` of the point of `y`);
- `relabelOver` and `relabelOver_natural` (on `fieldPt K ⟶ Y`; any two maps `Spec K → Spec ℚ`
  agree);
- `r1fp_exotic`: for every `(Y, Φ)` with `R1fpProps`, every bijection `s` of the points of `Y`
  and every family of residue-field isomorphisms, `relabel Φ (relabelOver Y s φ)` again
  satisfies `R1fpProps`.

**Effect on the clause lists (VERIFIED, compiled).** In `scratch/rv-g0pieces/Exotic.lean`,
`relabel Φ τ` is `τ` followed by `Φ`. Three lemmas are proved:

- `r1fp_relabel`: R1fp is preserved by every natural `τ`;
- `r2fp_relabel`: R2fp is preserved when `τ` maps `π`-fibres of `ℚ̄`-points to `π`-fibres and
  fixes the three CM fibres;
- `r1r2_relabel`: both together.

The file is Split.lean lines 1-15140 (through `R2fpProps`) followed by the two new sections.
Not compiled: the arithmetic input, i.e. a pair of `ℚ`-isomorphic rational fibres of `Y₃ → P¹`
with different properties.

**When `τ` can move a fibre.** `τ` is natural, hence Galois-equivariant on `ℚ̄`-points. So the
image of the fibre over a rational point is a Galois-stable geometric fibre, i.e. a fibre over a
rational point. Mapping it bijectively with residue-field isomorphisms is possible exactly when
the two fibres are isomorphic finite étale `ℚ`-schemes. If `s` preserves every fibre, the
relabeling is harmless: the class stays in the same twist class.

**Consequence.** Each of the three pieces must hold for every such relabeled triple. Its truth
therefore depends on which rational fibres of `Y₃ → P¹` are `ℚ`-isomorphic, which is unknown.
The other seven pieces do not mention `(Y, Φ, π)`.

## 4. Proposed repairs (for the three UNSURE pieces)

1. **Recommended: pin `Φ` by a universal family.** R1 says `Y₃` is a fine moduli scheme (h-b1
   uses the PEL moduli scheme). State in `R1fpProps`, or in a strengthened leaf, that `Φ` is
   induced by a family `𝒜 → Y`: an abelian scheme of relative dimension 2 with `𝒪`-action and
   level-3 structure. Then `Φ_K(y) = [y*𝒜]`. A relabeling then changes the family only by a
   scheme automorphism, and `R2fpProps` forces `π ∘ g = π` (a Möbius map fixing three points is
   the identity). So the triple is pinned up to harmless changes and the three pieces become
   provable glue. Cost: a definition of QML3 over a base scheme. That is new Lean, but it is the
   honest content of R1.
2. **Cheaper pin: tie `π` to an intrinsic invariant of the class.** Add an F1 clause to R2fp:
   for every `ℚ̄`-point `y` with `Φ y = [P]`, there is a period matrix `Ω` of `P.A` (for some
   principal polarization) with `3779136(∏θ)⁴/(∑θ⁸)⁵ = π(y)`. That is Lin–Yang plus Igusa, a
   leaf for the genuine triple. A relabeling that moves the fibre over `J(u₁)` to the fibre over
   `s₂` would then need some principal polarization of `A_{s₂}` with theta value `J(u₁)`. This
   collapses `ThetaPointOfFibre`'s problem entirely, since the piece's `Ω` becomes the leaf's.
   `FibreSimple` would still need that no principal polarization of a rational CM surface has
   theta value `J(u₁)` (a finite check per CM point, SPECULATIVE).
3. **Soundness-only stopgap.** Replace `∀ (Y Φ π), R1fpProps → R2fpProps → …` in the three
   pieces by the triple the leaf produces, bundled as one existential with `exists_fibre_object`.
   This makes the hypotheses true, so the reduction is not vacuous, but the pieces are then no
   longer glue that is provable from the stated leaves.

## 5. Lean outcomes

- `scratch/rv-g0pieces/Exotic.lean` (Split.lean 1-15140 plus sections `RvG0Pieces` and
  `RvG0Exotic`) gives **0 errors** (`lake env lean`, 2m05s, run2). `#print axioms` of
  `LeafQM.AV.r1r2_relabel`, `r1fp_exotic` and `relabelPt_point` is
  `[propext, Classical.choice, Quot.sound]`.
- `scratch/rv-g0pieces/ExoticCore.lean` (Mathlib only) is a fast test copy of the `RvG0Exotic`
  core. It gives 0 errors.
- No other Lean was needed: no piece is false in a way that a small Lean counterexample could
  exhibit. A vacuity witness is not meaningful here, because a vacuously true piece is harmless.
