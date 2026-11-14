# curve-split: the curve and model GLUE rows of frontier r3, split into published forms

Task curve-split (2026-11-14). Base: `cba8157f` (fork main after w54 and frontier r3).
Lean files: `scratch/curve-split/` (`X0Split.lean`, `CurvesGSplit.lean`, `CurveBij.lean`,
`GenusBound.lean`); results log `scratch/curve-split/log.md`. Every Lean claim below was compiled
with `lake env lean` on Lean 4.35.0 / Mathlib v4.35.0, and `#print axioms` reports only `propext`,
`Classical.choice`, `Quot.sound` (VERIFIED). Theorem numbers of printed sources are from memory
and UNVERIFIED (no network) unless a locator file is cited.

## 1. Verdict

Four of the six rows are now theorems, one of them with no leaf at all; two rows are not:

* **H-85 `CurveBijIso` is proved outright**, from Mathlib and `ZInQKernel/` with no hypothesis
  (`CurveSplit.curveBijIso`). Mathlib v4.35 has Zariski's Main Theorem (Stacks 03GW), fpqc descent
  of isomorphisms, ranks of finite flat algebras, the unramified locus, and Jacobson rings. The
  remaining glue, about 1300 lines, is proved in `CurveBij.lean`. Earlier
  stages of the same file also prove the row from published leaves (Springer's corollary; Zariski's
  Main Theorem in its original form, itself now proved; the degree formula), which document the
  classical route.
* **H-81 and H-82 are proved from one published leaf each, with no remaining glue.** H-82 uses a
  leaf the kernel already has (Zariski's connectedness theorem). H-81 uses one new leaf (Stacks
  00TV).
* **H-41 follows from Igusa's theorem.** The kernel already states it as a leaf (`IgusaSL2X`, or
  `IgusaGL2`). The modular-equation form the row cites cannot be stated in Lean today: Mathlib has
  no `j`-function and no modular polynomial.
* **H-79 cannot be split today, and it is stronger than the proof needs.** Its sources are
  statements about the compact Riemann surface `Γ₁(N)\ℍ*` (Shimura 1971, §6.7 and Prop. 1.40).
  Mathlib has no Lean definition of that surface. The proof uses the row only through
  `dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`). That bound is now proved from two textbook leaves
  about function fields, Riemann–Hurwitz and the fundamental identity (Stichtenoth), together with
  `X0Transitive` (H-41) and the kernel's first half of T34, `DimJacobianEqGenus`
  (`CurveSplit.dimJ1Le_of_rh_fi`). That places are DVRs is proved where it is needed
  (`CurveSplit.exists_uniformizer`).
* **H-83 cannot be split today.** Its published form is representability of a moduli problem of
  abelian schemes with `𝒪`-action and level structure over `ℤ_(p)`-schemes. That needs abelian
  schemes over a base, which the repository and Mathlib do not define. A leaf over the kernel's
  `QMFamily` would be over a structure invented for the purpose, and stronger than the source.
  §3.6 lists what is needed and how each clause would then follow.

No row statement was changed, and no row was found false or vacuous.

## 2. Table

| row | old form | new leaves (published form, source) | new glue | Lean name of the proof |
|---|---|---|---|---|
| H-41 `X0Transitive` | GLUE (irreducibility of `Φ_N` through `C ↦ j(E/C)`) | `ZInQ.RLeaf.IgusaSL2X` (kernel; Igusa 1959, `SL₂(ℤ/N)` in the Galois image on `E_j[N]`, on `x`-coordinates), or `ZInQ.RLeaf.IgusaGL2` (kernel; Igusa's theorem as usually printed) | none | `CurveSplit.x0Transitive_of_igusaSL2X`, `CurveSplit.x0Transitive_of_igusaGL2` (`X0Split.lean`) |
| H-79 `GenusX1Field` | GLUE (lit-composite: Shimura Prop. 6.9, Prop. 1.40, base change of `H⁰(Ω¹)`) | the row itself: none possible today (no `Γ₁(N)\ℍ*` in Lean). For its only use (`dim J₁(N) ≤ N²`): `CurveSplit.RiemannHurwitzQj` (Stichtenoth Thm 3.4.13 with Dedekind's different theorem 3.5.1, the genus as holomorphic differentials) and `CurveSplit.FundamentalIdentityQj` (Stichtenoth Thm 3.1.11 at `j = 0, 1728, ∞`), with `X0Transitive` (H-41) and the kernel's `DimJacobianEqGenus` | none (`BelyiGenusBound` and the uniformizers proved) | `CurveSplit.dimJ1Le_of_rh_fi`, `CurveSplit.belyiGenusBound_of_rh_fi`, `CurveSplit.exists_uniformizer`, `CurveSplit.genusX1Le_of_belyi`, `CurveSplit.genusX1Le_of_genusX1Field` (`GenusBound.lean`) |
| H-81 `NormalCurveSmoothQ` | GLUE (Stacks 00TV, 0B8X) | `CurveSplit.RegularSmoothPerfect` (Stacks 00TV: a finite type algebra over a perfect field is smooth at a prime with regular local ring) | none | `CurveSplit.normalCurveSmoothQ_of_regularSmooth` (`CurvesGSplit.lean`) |
| H-82 `GeomConnectedOfConstantFieldQ` | GLUE (`Γ(X,𝒪) = ℚ`, Stacks 0FD1) | `ZariskiConn.ZariskiConnectedness` (kernel; EGA III₁ 4.3.1 with 4.3.4) | none | `CurveSplit.geomConnectedOfConstantFieldQ_of_zariski` (`CurvesGSplit.lean`) |
| H-83 `ShimuraGoodReduction` | GLUE (lit-composite: Morita, Carayol, Kottwitz, Buzzard) | none possible today (no abelian schemes over a base) | see §3.6 | none |
| H-85 `CurveBijIso` | GLUE (generic smoothness and a degree count) | **none** (Mathlib only). Also proved from published leaves: (a) `CurveSplit.BijToNormalIsIso` (Springer, *LAG* Cor. 5.2.8), (b) `CurveSplit.DegreeGeneralFibre` (Humphreys §4.6) with `CurveSplit.ZMTOriginal` (Mumford *Red Book* III §9; proved: `CurveSplit.zmtOriginal`) | none | **`CurveSplit.curveBijIso`** (no hypotheses); also `curveBijIso_of_leaf`, `curveBijIso_of_degree`, `curveBijIso_of_zmt` (`CurveBij.lean`) |

## 3. The rows

### 3.1 H-41 `X0Transitive`

`X0Transitive` says that `Aut(\overline{ℚ(j)}/ℚ(j))` permutes transitively the cyclic subgroups of
order `N` of `E_j`. It is imported from `ZInQKernel/Contrib/RLeaf/IgusaX0.lean`. The kernel
already proves `igusaTransitive_of_igusaSL2X` and `x0Transitive_of_igusaTransitive`. Composing
them gives `x0Transitive_of_igusaSL2X`.

`IgusaSL2X` is the geometric part of Igusa's theorem (Igusa, Amer. J. Math. 81 (1959); Shimura
1971 Thm 6.6; Lang, *Elliptic functions*, Ch. 6 §3). It holds for every model of the generic curve,
because the monodromy maps onto `PSL₂(ℤ)` and `PSL₂(ℤ)` does not lift to `SL₂(ℤ)`.
`IgusaSL2X` (a matrix statement) is stronger than `X0Transitive`. The kernel proves
`TateMuN`, so transitivity on the points of order `N`
(`IgusaTransitive`) is equivalent to the row (`igusaTransitive_iff_x0Transitive`). The weaker
printed source the row cites is Lang Ch. 5 §2 Thm 3, the irreducibility of `Φ_N(X, j)` over
`ℂ(j)`. Its Lean statement would need the modular
`j`-function and the modular polynomial. Neither is in Mathlib v4.35: `NumberTheory/ModularForms`
has Eisenstein series and the discriminant, but no `j` and no `Φ_N` (VERIFIED by grep). It would
also need the comparison of `ℂ(j(τ))` with `ℚ(j)` through the analytic uniformization.

### 3.2 H-82 `GeomConnectedOfConstantFieldQ`

The leaf is the kernel's `ZariskiConn.ZariskiConnectedness`: Zariski's connectedness theorem in
its published form (EGA III₁ 4.3.1 with 4.3.4). A proper morphism `f : X → Y`, `Y` locally
noetherian, with `𝒪_Y = f_*𝒪_X` has non-empty, geometrically connected fibres. The glue is proved:

1. `Γ(X, 𝒪_X)` is integral over `Γ(Spec ℚ) = ℚ`. This is Mathlib's
   `isIntegral_appTop_of_universallyClosed`, so no finiteness theorem for coherent cohomology is
   needed.
2. `Γ(X, 𝒪_X)` embeds in the function field (`germToFunctionField_injective`, `X` integral), hence
   into `F`. There every element algebraic over `ℚ` is rational (`ConstantFieldIsQ`), so
   `ℚ → Γ(X, 𝒪_X)` is bijective (`appTop_bijective_of_constantField`).
3. `𝒪_{Spec ℚ} = f_*𝒪_X` follows from the kernel's
   `ZariskiConn.app_bijective_of_appTop_bijective`, and the leaf finishes the proof.

The hypothesis `IsNormalScheme X.left` of the row is not used.

### 3.3 H-81 `NormalCurveSmoothQ`

New leaf `RegularSmoothPerfect`. Let `k` be a perfect field, `S` a finite type `k`-algebra and `q`
a prime of `S` with `S_q` regular (Mathlib's `IsRegularLocalRing`, Stacks 00KU). Then some `g ∉ q`
has `S_g` smooth over `k`. This is the `⇐` half of Stacks Tag 00TV ("S is smooth at q iff S_q is
regular", for perfect `k`; tag and lemma number UNVERIFIED), with `k` and `S` in `Type`. The glue
is proved:

1. `isRegularLocalRing_stalk_of_normal`: the stalks of an integral, normal, locally noetherian
   scheme of dimension `≤ 1` are regular. Each stalk is a noetherian, integrally closed local domain
   with `KrullDimLE 1`, since `dim 𝒪_{X,x} = coheight x ≤ dim X`. So it is a Dedekind domain, and
   Mathlib's Dedekind domains are regular rings.
2. `mem_smoothLocus_of_regular` applies the leaf on an affine chart with `k = Γ(Spec ℚ, ⊤)`, a
   perfect field, and then `Algebra.basicOpen_subset_smoothLocus_iff_smooth` and
   `formallySmooth_stalkMap_iff`. So every point is in the smooth locus, and
   `smoothLocus_eq_top_iff` gives `Smooth`.
3. `smoothOfRelativeDimension_one`: on each chart the standard smooth presentation has relative
   dimension equal to the stalk dimension at a closed point of the chart, by the kernel's
   `ZInQ.Contrib.Dim.ringKrullDim_stalk_of_chart`. That stalk dimension is `dim X = 1`, by
   `topologicalKrullDim_eq_ringKrullDim_stalk_of_smooth`.

### 3.4 H-85 `CurveBijIso`

The row says that a morphism `g : S → Y` of proper smooth curves over `ℚ` (relative dimension 1)
that is bijective on `ℚ̄`-points is an isomorphism. It is copied verbatim from
`scratch/model-glue/ModelGlue6.lean` L2954; it uses only `fieldPt` and `Qbar` of
`ZInQKernel/HDecomp/QM/Pairs.lean`.

**Part A, descent (proved; `curveBijIso_of_closed`).** The square `S_ℚ̄ → Y_ℚ̄ → Y`,
`S_ℚ̄ → S → Y` is a pullback (`IsPullback.of_right`). `Spec ℚ̄ → Spec ℚ` is surjective, flat and
quasi-compact, so isomorphisms descend (Mathlib
`descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact`, Stacks 02L4). The
`ℚ̄`-points of `S` over `ℚ` are the sections of `S_ℚ̄ → Spec ℚ̄`, compatibly with `g` (`bij_bc`).
This reduces the row to `CurveBijIsoClosed`, the same statement over any algebraically closed
field `k` of characteristic 0.

**Part B, curves to varieties (proved).** Let `h : T → Z` be the morphism over `k`.

1. Closed points of a `k`-scheme locally of finite type are its `k`-points (Mathlib
   `pointEquivClosedPoint`). So `h` maps closed points to closed points, injectively and onto
   (`closedPoint_facts`).
2. The local rings of a smooth curve at closed points are DVRs (`stalk_closed_normal`). This
   combines the kernel's stalk dimension and cotangent rank with `isDomain_of_dim_one`, copied
   from `scratch/curve-glue/CIproof.lean.part`, and Mathlib's DVR TFAE. Hence the irreducible
   components of `T` are disjoint (`components_disjoint`), and those of `Z` are open
   (`isOpen_irreducibleComponent`).
3. Topology (`bijective_of_closedPoints`, pure topology): a continuous closed map of Jacobson
   spaces, with source T₀ of dimension `≤ 1` with disjoint components, that is bijective on
   closed points as in item 1, is bijective. A non-closed point is the generic point of a
   component (`closure_mem_irreducibleComponents`), and its image is not closed. So `h` is a
   homeomorphism, since it is proper and hence closed.
4. Over each component `W` of `Z`, `V = h⁻¹W` is irreducible (homeomorphism) and reduced (smooth
   over a field gives reduced: `isReduced_of_smooth`, via the kernel's
   `ZInQ.SmoothFibre.isReduced_of_smooth_of_field` on affine charts). `W` is integral and normal
   (`isNormal_of_integral`: DVRs at closed points, the function field at the generic point).
5. (a) The leaf `BijToNormalIsIso` applied to `h ∣_ W` (bijective on `k`-points, `bij_restrict`)
   gives `IsIso (h ∣_ W)`. Or (b): `h ∣_ W` is bijective on points, hence dominant with finite
   fibres. Its fibre over a general closed point has one closed point, so
   `DegreeGeneralFibre` gives `[K(V) : K(W)] = 1`: Tau Ceti's `functionFieldMap` is bijective,
   so `h ∣_ W` is birational. `ZMTOriginal` makes it an open immersion, and it is surjective, so
   it is an isomorphism (`restrict_isIso'`).
6. Isomorphisms are local on the target (`IsZariskiLocalAtTarget.of_iSup_eq_top`), and `Over.forget`
   reflects isomorphisms.

**Part C, Zariski's Main Theorem in its original form (proved; `zmtOriginal`).** The leaf
`ZMTOriginal` is: a birational morphism of varieties with finite fibres onto a normal variety is an
open immersion (Mumford, *Red Book* III §9; EGA III₁ 4.4.9). It is a theorem here.
* Mathlib's `Scheme.Hom.exists_isIso_morphismRestrict_toNormalization` (Stacks 03GW) says: a
  separated morphism of finite type is an isomorphism from its quasi-finite locus onto an open
  subset of the relative normalization `Y'`.
* With finite fibres the quasi-finite locus is everything.
* New: `isIso_fromNormalization`, `Y' = Y` when `Y` is normal and `f` birational. For an affine
  `V`, the integral closure of `Γ(Y, V)` in `Γ(X, f⁻¹V)` is `Γ(Y, V)`, because `Γ(X, f⁻¹V)`
  embeds in `K(X) = K(Y)`, which is `Frac Γ(Y, V)`, and `Γ(Y, V)` is integrally closed
  (`isIntegrallyClosed_of_normal`). Birationality is Tau Ceti's `functionFieldMap` being
  bijective.

**Part D, no leaf (proved; `curveBijIso`).** The restriction `f : V → W` of `h` over a component
of `Z` is a homeomorphism, and it is finite (proper and injective). On a nonempty affine open
`U ⊆ W`, take `A = Γ(W, U)` and `B = Γ(V, f⁻¹U)`.
1. `A` is a Dedekind domain (`isDedekindDomain_sections`) and `B` is a finite torsion-free
   `A`-algebra, hence flat.
2. The unramified locus of `B/A` is open, and it contains the generic point: this is Mathlib's
   `Algebra.isUnramifiedAt_bot`, in characteristic 0.
3. `B` is a Jacobson ring, so the unramified locus contains a maximal ideal `q`.
4. `q` is the only prime over `p = q ∩ A`, because `f` is injective on points.
5. `κ(p) → κ(q)` is onto, by the Nullstellensatz: `finite_of_finite_type_of_isJacobsonRing` and
   `IsAlgClosed.ringHom_bijective_of_isIntegral`.
6. `bijective_of_unramifiedAt`: then `A_p ≅ B_q` (Mathlib's
   `Localization.localRingHom_{injective,surjective}_of_primesOver_eq_singleton`). `B_q` is the
   localization of `B` at `p`, so the rank of `B` at `p` is 1. The rank at every prime equals the
   rank at the generic point (`Module.rankAtStalk_eq_of_le_of_finite_of_flat`), so it is 1
   everywhere, and `A → B` is bijective (`Module.algebraMap_bijective_of_rankAtStalk`).
7. Isomorphisms are local on the target, so `f` is an isomorphism (`isIso_of_finite_bijective`).

**The classical leaves (kept as documentation, no longer needed).**

* `BijToNormalIsIso`: a morphism of irreducible varieties over an algebraically closed field `k`
  of characteristic 0, bijective on `k`-points, with normal target, is an isomorphism (Springer,
  *Linear Algebraic Groups*, 2nd ed., Cor. 5.2.8, with "separable"; UNVERIFIED).
* `DegreeGeneralFibre`: let `f` be a dominant morphism of varieties of the same dimension in
  characteristic 0. On a nonempty open set of closed points `y`, the fibre has `[K(X) : K(Y)]`
  closed points (Humphreys, *LAG* §4.6; Shafarevich, *BAG 1*, II.6.3; Borel AG.18.4; UNVERIFIED).
* `ZMTOriginal`: now proved, see Part C.

### 3.5 H-79 `GenusX1Field`

**The row cannot be stated in published form.** `GenusX1Field` says `fieldGenus (fieldX1 P)` equals
the genus formula `1 + μ/12 − ν₂/4 − ν₃/3 − ν∞/2` of `Γ₁(N)`, where `fieldGenus` is the dimension
of the holomorphic differentials. Its sources are of two kinds:

* `K_N ⊗ ℂ` is the function field of the compact Riemann surface `Γ₁(N)\ℍ*` (Shimura 1971 §6.7 and
  Prop. 6.9, the canonical model);
* the genus of `Γ\ℍ*` is the formula (Shimura 1971 Prop. 1.40), unchanged by `ℚ → ℂ`.

Mathlib v4.35 has the upper half plane, `SL₂(ℤ)` and its congruence subgroups, but no compactified
quotient as a Riemann surface and no genus for it. So neither statement has a Lean form over
genuine definitions. An algebraic route exists but is long. It would combine:

* Riemann–Hurwitz for `K_N/ℚ(j)`;
* the inertia groups at `j = 0, 1728, ∞`: orders 3 and 2 from potentially good reduction, and a
  transvection from the Tate curve;
* the identification of the branch cycles with `ST`, `S`, `T` through the product relation, which
  needs the Riemann existence theorem or the analytic uniformization;
* the identity relating the cycle structure on `SL₂(ℤ/N)/±stab(x(P))` to `ν₂, ν₃, ν∞` on
  `SL₂(ℤ)/±Γ₁(N)`.

**What the proof uses (VERIFIED by reading the consumers).** T34 (`DimJ1Genus`) is used only through
`LeafModCurves.dim_J1_le` (`dim J₁(N) ≤ N²`). The two uses are `javanpeykarJ1`
(`scratch/g0-assemble2/olean/LPrefix.lean` L33840) and step E2 of
`scratch/g0-assemble2/olean/TailD.lean` L226. The equality is never used. So `GenusSplit.lean`'s
`dimJ1Genus_of_split` could be replaced by a bound, proved in `GenusBound.lean`:

* `GenusX1Le : ∀ N P, 0 < N → addOrderOf P = N → fieldGenus (fieldX1 P) ≤ N²` is a consequence of
  the row (`genusX1Le_of_genusX1Field`).
* `DimJ1Le` is the conclusion of `dim_J1_le`; `dimJ1Le_of : DimJacobianEqGenus → GenusX1Le →
  DimJ1Le`.
* `genusX1Le_of_belyi : BelyiGenusBound → X0Transitive → GenusX1Le`. It uses two kernel theorems:
  `ZInQ.RLeaf.belyiX1` (`j/1728` is a Belyi function on `K_N` and `[K_N : ℚ(j)] ≤ N²`, proved with
  no hypotheses) and `ZInQ.RLeaf.x1ConstantField_of_x0Transitive`.
* `BelyiGenusBound`: if `F/ℚ(j)` is finite, `ℚ` is algebraically closed in `F`, and `j/1728` is a
  Belyi function, then `2 fieldGenus F + 1 ≤ [F : ℚ(j)]`. **Proved** (`belyiGenusBound_of_leaves`)
  from three leaves stated over Mathlib's `ValuationSubring`. A place `P` (`CurveSplit.Place`) is a
  proper valuation subring containing `ℚ`. `e_P` (`Place.ramIdx`) is the index of
  `U_P · ℚ(j)^×` in `F^×` (`F^×/U_P` is the value group). `deg P` (`Place.deg`) is
  `dim_ℚ κ(P)`. The leaves:
  * `RiemannHurwitzQj`: only finitely many places ramify, and
    `2g(F) − 2 = −2[F : ℚ(j)] + Σ_P (e_P − 1) deg P` with `g = fieldGenus`, for `F` with
    constant field `ℚ`. This is Stichtenoth, *Algebraic Function Fields and Codes*, Thm 3.4.13
    with `g(ℚ(j)) = 0`, combined with Dedekind's different theorem 3.5.1 (`d_P = e_P − 1` in
    characteristic 0). That `fieldGenus` (holomorphic Kähler differentials) is the Riemann–Roch
    genus is a further published input: Stichtenoth §1.5/§4.3, Hartshorne II.8 (numbers
    UNVERIFIED). So the leaf is a composite of these printed statements.
  * `FundamentalIdentityQj`: at each of the three places `j = 0`, `j = 1728`, `j = ∞` of `ℚ(j)`,
    finitely many `P` lie over it and `Σ e_P deg P = [F : ℚ(j)]`. This is Stichtenoth Thm 3.1.11
    with `deg P = f(P|Q) deg Q` and `deg Q = 1`. Lying over is read off `t = j/1728`: `t ∈ 𝔪_P`,
    `t − 1 ∈ 𝔪_P`, `t ∉ 𝒪_P`.
  * `PlacesAreDVR`: every place has a uniformizer `π`, and every `x ∈ F^×` is `π^n` times a unit
    (Stichtenoth Thm 1.1.6). **No longer needed.** The proof only uses uniformizers at places
    containing `t`, and `exists_uniformizer` proves those exist. The integral closure `R` of
    `ℚ[j]` in `F` is a Dedekind domain with fraction field `F` (Mathlib). Since valuation rings
    are integrally closed, `R ⊆ 𝒪_P`. `𝔭 = R ∩ 𝔪_P` is a nonzero prime. A uniformizer of the DVR
    `R_𝔭 ⊆ F` (Mathlib's `Localization.subalgebra.ofField`) is a uniformizer of `𝒪_P`. So
    `belyiGenusBound_of_rh_fi : RiemannHurwitzQj → FundamentalIdentityQj → BelyiGenusBound`.

  The glue is proved:
  * `ramIdx_eq_one`: if `q(t)` divides `𝔪_P`, then `q(t)` is a uniformizer and `e_P = 1`;
  * `polyIdeal`: `{p ∈ ℚ[X] : p(t) ∈ 𝔪_P}` is a prime ideal, and nonzero. Otherwise `ℚ(j) ⊆ 𝒪_P`,
    and the minimal polynomial of `x⁻¹` for any `x ∉ 𝒪_P` gives a contradiction;
  * `place_cases`: by the kernel's `IsBelyiFunction`, every place lies over `j = 0`, `1728`, `∞`
    or has `e_P = 1`;
  * the sum estimate: `Σ_{P|Q} (e_P − 1) deg P = d − Σ_{P|Q} deg P ≤ d − 1` at each of the three
    places.

So for the consumers, H-79 can be replaced by the H-41 leaf (Igusa) and two textbook theorems on
function fields (Riemann–Hurwitz, the fundamental identity), with no modular curve over `ℂ`.
`CurveSplit.dimJ1Le_of_rh_fi : DimJacobianEqGenus → RiemannHurwitzQj → FundamentalIdentityQj →
X0Transitive → DimJ1Le` is compiled. The fundamental identity is in Mathlib for Dedekind
extensions (`Ideal.sum_ramification_inertia`). Turning `FundamentalIdentityQj` into a theorem
needs two things: the correspondence between places over `j = a` and primes of the integral
closure of `ℚ[j]`, and over `j = ∞` the integral closure of `ℚ[1/j]`; and the comparison of the
unit-group index `e_P` with Mathlib's `ramificationIdx`. That is glue, not done here. `DimJ1Le` is exactly the conclusion of `LeafModCurves.dim_J1_le`, so the
consumers `javanpeykarJ1` and E2 can be switched to it.

### 3.6 H-83 `ShimuraGoodReduction`

The row (`scratch/vert-witness/VertWitness.lean` L1477) asserts, for each prime `p > 324`, a pair
`(𝒴, 𝒜)` with `IsShimuraModel p 𝒴 𝒜`. Here `𝒴` is proper and smooth of relative dimension 1 over
`ℤ_(p)`, and `𝒜` is a kernel `QMFamily` over `𝒴` (proper smooth of relative dimension 2 with
`ι(a)` and `η(a)`, no group law). The clauses are: field-point fibres are objects; the moduli map is
injective and surjective on `ℚ̄`-points; Hecke automorphisms exist for each `α ∈ Aut 𝒪` and
`u ∈ 𝒪^×`; and a `ℚ̄`-point exists (the guard).

**The published statement is representability** (Kottwitz, J. AMS 5 (1992) §5 for the PEL problem
with neat `K^p` and hyperspecial `K_p`; Buzzard, Duke 87 (1997) for the polarization-free problem;
Morita 1981; locators UNVERIFIED, `docs/research/locators.md` row R1). The moduli functor sends a
`ℤ_(p)`-scheme `S` to the isomorphism classes of triples `(A, ι, η)`:

* `A/S` an abelian scheme of relative dimension 2;
* `ι : 𝒪 → End_S(A)`;
* `η : (𝒪/3𝒪)_S ≅ A[3]` a level-3 structure;
* in the PEL form, also a principal polarization of the fixed Rosati type.

The theorem says this functor is represented by a smooth proper curve over `ℤ_(p)`. A Lean
statement over genuine definitions needs objects that exist neither in Mathlib v4.35 nor in
`ZInQKernel/`:

1. abelian schemes over a base `S`: group objects in `Over S` (Mathlib has `GrpObj`) that are
   proper and smooth with geometrically connected fibres (`PkgI3.AbVar` is over a field only);
2. `𝒪`-actions by group endomorphisms over `S`;
3. the finite étale group scheme `A[3]`, the constant group scheme `(𝒪/3𝒪)_S`, and isomorphisms
   between them;
4. principal polarizations over `S` and their Rosati involution, in the PEL form;
5. isomorphism classes and pullback of triples, i.e. the moduli functor, and representability.

A leaf over `QMFamily` would quantify over families without a group law. It would assert more
objects than the published functor has, so it would be stronger than its source. That is the
pitfall the task forbids ("abstract structures invented for the purpose").

**How the row would follow once 1–5 exist.** All of these are glue, provable in Lean:

* the fibre clause is the restriction of the representing isomorphism to `Spec K`;
* injectivity and surjectivity on `ℚ̄`-points follow from Yoneda, with Lemma P (`QML3`'s
  docstring) to drop the polarization in characteristic 0;
* the Hecke clauses are Yoneda applied to the automorphisms `(A, ι, η) ↦ (A, ι∘α, η∘α)` and
  `η ↦ η∘u` of the functor;
* the guard follows from surjectivity and the existence of one object over `ℚ̄` (for example
  `CMObjectsExist`, derived from `R1R2fp`).

The review recorded in `docs/research/vert-witness.md` §6.1 judged the Lean form a weaker
consequence of representability, and that review stands. The remaining human check, from the
frontier, is whether the cited theorems cover level 3 at `3 ∣ D`. Kottwitz needs only `K_p`
hyperspecial at `p ≠ 3`, so it should; this is UNVERIFIED.

## 4. What compiles

| file | contents | result |
|---|---|---|
| `scratch/curve-split/X0Split.lean` | H-41 from `IgusaSL2X` / `IgusaGL2` | compiled, standard axioms |
| `scratch/curve-split/CurvesGSplit.lean` | H-81 from `RegularSmoothPerfect`; H-82 from `ZariskiConnectedness` | compiled, standard axioms |
| `scratch/curve-split/CurveBij.lean` | `CurveBijIso` (verbatim); Part A (descent), Part B (leaf (a)), Part B' (ZMT and the degree formula), Part C (`zmtOriginal`), Part D (`curveBijIso`, no leaf) | compiled, standard axioms |
| `scratch/curve-split/GenusBound.lean` | H-79 consumers: `GenusX1Le`, `DimJ1Le`, `BelyiGenusBound` from Riemann–Hurwitz and the fundamental identity, `exists_uniformizer` | compiled, standard axioms |

All four files import only `ZInQKernel/` modules (built with `lake build` for the imported
modules) and Mathlib. No scratch file imports another. `CurveBij.lean` contains copies of two
lemmas of `scratch/curve-glue/CIproof.lean.part` (`isDomain_of_dim_one`,
`irreducibleComponent_eq_of_isDomain_stalk`).

## 5. What remains

* H-79: the row itself stays a lit-composite. To drop it, switch the consumers of `dim_J1_le`
  (`javanpeykarJ1`, E2 in `TailD.lean`) to `DimJ1Le`. `DimJ1Le` is proved from
  `DimJacobianEqGenus`, `RiemannHurwitzQj`, `FundamentalIdentityQj` and `X0Transitive`. Not done
  here, because it edits other tasks' files. `FundamentalIdentityQj` can be reduced to Mathlib's
  Dedekind fundamental identity (glue, §3.5).
* H-83: the definitions 1–5 of §3.6, a Lean statement of Kottwitz/Buzzard representability, and
  the clause-by-clause glue.
* H-85: nothing remains (`curveBijIso` has no hypotheses). To adopt it, copy `CurveBij.lean`
  into `ZInQKernel/Contrib/` and close `ModelGlue.CurveBijIso` in `modelIntegral_of` and
  `modelFunctionField_of_curveBijIso`.
* Locators: every theorem number above is from memory (UNVERIFIED).
