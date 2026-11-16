# unif-topology: the classical topology of `X(ℂ)` is the analytic topology

**Result (VERIFIED: compiled, `lake build ZInQKernel.Contrib.OneProof.UniformizationTopology`; every theorem
below has axioms `propext`, `Classical.choice`, `Quot.sound`).** unif-printed (`wip/unif-printed` 9c2e1809, merged
here cleanly) proves the textbook field `uniformizationLeafAll` from four leaves. Three of them are stated over
`UnifPrinted.classicalTopology X`, the coarsest topology on `X(ℂ)` in which every `U(ℂ)` is open and every regular
function is continuous. That left a reading risk, since the prints use the analytic (Euclidean) topology. This
task closes it in Lean:

1. **Affine pieces.** Take `U ⊆ X` affine and `f₁, …, f_k` generating `Γ(X, U)` as a `ℂ`-algebra. Then
   `P ↦ (fᵢ(P))ᵢ` is a homeomorphism from `U(ℂ)`, with the classical topology, onto the affine variety
   `V(I) ⊂ ℂ^k` with the subspace topology. Here `I` is the ideal of relations among the `fᵢ`.
2. **Gluing.** Take any family of such affine charts whose `ℂ`-points cover `X(ℂ)`. The classical topology is the
   topology glued from the charts.
3. **Analytic topology.** For `X` locally of finite type over `ℂ`, `classicalTopology X = analyticTopology X`.
   `analyticTopology X` is the textbook definition: `S` is open iff `S ∩ U(ℂ)` is open in `U(ℂ) ⊂ ℂ^k` for every
   affine chart.

The three dictionary leaves are then restated over `analyticTopology`. Each restated leaf is proved
**equivalent** (`↔`) to unif-printed's leaf, so it is neither stronger nor weaker. The field follows from them and
Mumford's leaf:

```lean
theorem UnifTopology.uniformizationLeafAll_of_analytic (hM : MumfordComplexTorus)
    (hMan : SmoothComplexManifoldAn) (hPC : ProperCompactAn) (hCC : ConnectedConnectedAn) :
    BPAnalytic.Uniformization.UniformizationLeafAll
```

The file is `ZInQKernel/Contrib/OneProof/UniformizationTopology.lean` (25 KB). It imports
`ZInQKernel.Contrib.OneProof.UniformizationPrinted`, which imports the module that defines the statement,
`ZInQKernel.HDecomp.Analytic.Uniformization`. It needs unif-printed's file in the tree, so fold it with (or after)
unif-printed's file. The field statement is unchanged. Against the re-rated count (field GLUE) the fold is
**-1 GLUE**. The four leaves can be rated **printed form** (§3).

## 1. Theorems (verbatim, namespace `UnifTopology`; `X : Over (Spec (CommRingCat.of ℂ))` implicit)

Definitions, all concrete:
- `algC X U : ℂ →+* Γ(X.left, U)` is the structure map, `((ΓSpecIso ℂ).inv ≫ X.hom.appLE ⊤ U _).hom`.
- `Generates U f := Function.Surjective (MvPolynomial.eval₂Hom (algC X U) f)`.
- `UPt X U := {P : CPt X // XPtIn X P U}`.
- `coord f : UPt X U → (Fin k → ℂ) := fun P i => XevalAt X U (f i) P.1`.
- `zeroLocus f := {w | ∀ p, MvPolynomial.eval₂ (algC X U) f p = 0 → MvPolynomial.eval w p = 0}`.

`CPt`, `XPtIn`, `XevalAt` and `classicalTopology` are unif-printed's.

```lean
theorem induced_classicalTopology_eq {U : X.left.Opens} (hU : IsAffineOpen U) {k : ℕ}
    (f : Fin k → Γ(X.left, U)) (hf : Generates U f) :
    (classicalTopology X).induced (Subtype.val : UPt X U → CPt X) =
      (inferInstance : TopologicalSpace (Fin k → ℂ)).induced (coord f)

theorem coord_injective {U : X.left.Opens} (hU : IsAffineOpen U) {k : ℕ}
    (f : Fin k → Γ(X.left, U)) (hf : Generates U f) : Function.Injective (coord f)

theorem isEmbedding_coord {U : X.left.Opens} (hU : IsAffineOpen U) {k : ℕ}
    (f : Fin k → Γ(X.left, U)) (hf : Generates U f) :
    @Topology.IsEmbedding _ _ ((classicalTopology X).induced Subtype.val) _ (coord f)

theorem range_coord {U : X.left.Opens} (hU : IsAffineOpen U) {k : ℕ}
    (f : Fin k → Γ(X.left, U)) (hf : Generates U f) : Set.range (coord f) = zeroLocus f

theorem exists_homeomorph_zeroLocus {U : X.left.Opens} (hU : IsAffineOpen U) {k : ℕ}
    (f : Fin k → Γ(X.left, U)) (hf : Generates U f) :
    letI : TopologicalSpace (UPt X U) := (classicalTopology X).induced Subtype.val
    ∃ e : UPt X U ≃ₜ zeroLocus f, ∀ P, (e P : Fin k → ℂ) = coord f P

def gluedTopology {ι : Type*} (U : ι → X.left.Opens) (k : ι → ℕ)
    (f : ∀ j, Fin (k j) → Γ(X.left, U j)) : TopologicalSpace (CPt X) :=
  ⨆ j, TopologicalSpace.coinduced (Subtype.val : UPt X (U j) → CPt X)
    ((inferInstance : TopologicalSpace (Fin (k j) → ℂ)).induced (coord (f j)))

theorem classicalTopology_eq_gluedTopology {ι : Type*} (U : ι → X.left.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (k : ι → ℕ) (f : ∀ j, Fin (k j) → Γ(X.left, U j))
    (hf : ∀ j, Generates (U j) (f j)) (hcov : ∀ P : CPt X, ∃ j, XPtIn X P (U j)) :
    classicalTopology X = gluedTopology U k f

structure AffineChart (X) where
  U : X.left.Opens
  isAffine : IsAffineOpen U
  k : ℕ
  f : Fin k → Γ(X.left, U)
  generates : Generates U f

def analyticTopology (X) : TopologicalSpace (CPt X) :=
  gluedTopology (fun c : AffineChart X => c.U) (fun c => c.k) (fun c => c.f)

theorem exists_affineChart [LocallyOfFiniteType X.hom] (P : CPt X) :
    ∃ c : AffineChart X, XPtIn X P c.U

theorem classicalTopology_eq_analyticTopology [LocallyOfFiniteType X.hom] :
    classicalTopology X = analyticTopology X

theorem smoothComplexManifoldAn_iff : SmoothComplexManifoldAn ↔ SmoothComplexManifold
theorem properCompactAn_iff : ProperCompactAn ↔ ProperCompact
theorem connectedConnectedAn_iff : ConnectedConnectedAn ↔ ConnectedConnected

theorem uniformizationLeafAll_of_analytic (hM : MumfordComplexTorus)
    (hMan : SmoothComplexManifoldAn) (hPC : ProperCompactAn) (hCC : ConnectedConnectedAn) :
    BPAnalytic.Uniformization.UniformizationLeafAll
```

`#print axioms` (from `scratch/unif-topology/discharges.txt`, VERIFIED): `uniformizationLeafAll_of_analytic`,
`classicalTopology_eq_analyticTopology`, `classicalTopology_eq_gluedTopology`, `isEmbedding_coord`, `range_coord`,
`exists_homeomorph_zeroLocus`, `induced_classicalTopology_eq` and the three `*_iff`: all
`[propext, Classical.choice, Quot.sound]`.

## 2. `#discharges` (VERIFIED)

`lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` succeeded (12,994 jobs). Then
`lake env lean scratch/unif-topology/DischargesCheck.lean` (full output in `scratch/unif-topology/discharges.txt`):

```
DISCHARGES [OpenTextbookLeaves11.uniformizationLeafAll] by UnifTopology.uniformizationLeafAll_of_analytic
  still assumes: [UnifPrinted.MumfordComplexTorus,
 UnifTopology.SmoothComplexManifoldAn,
 UnifTopology.ProperCompactAn,
 UnifTopology.ConnectedConnectedAn]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1884 theorems checked, 10 discharge one
```

The output also lists unif-printed's two rows, because its module is imported.

## 3. Leaves and ratings

| leaf | statement | source (locators UNVERIFIED) | rating |
| --- | --- | --- | --- |
| `UnifPrinted.MumfordComplexTorus` | unchanged from unif-printed: a compact connected complex Lie group `X` of dimension `g` (Mathlib `LieGroup 𝓘(ℂ, ℂ^g) ω`) is `Torus Λ ≃ₘ^ω X`, additive to multiplicative | Mumford, *Abelian varieties*, §1; Birkenhake–Lange §1.1 | **printed form**. It does not involve the topology of `X(ℂ)`. |
| `SmoothComplexManifoldAn` | for `X` smooth, proper and irreducible over ℂ, `X(ℂ)` with `analyticTopology X` carries a complex analytic manifold structure (`∃ n`, `ChartedSpace (Fin n → ℂ)`) in which regular functions are holomorphic on `U(ℂ)` and some regular functions are local coordinates at every point | Shafarevich, *BAG 2*, VII §1.1; Serre, GAGA §2; SGA 1, XII 1.1, 3.1 | **printed form, special case**. The topology is now the print's (§1). Two weakenings from unif-printed remain, both making it weaker than the print: the chart dimension is existential, and "local parameters" became "some regular functions". `X` is restricted to proper. |
| `ProperCompactAn` | `X` proper over ℂ ⇒ `CompactSpace (CPt X)` for `analyticTopology X` | Serre, GAGA §2 Prop. 6; SGA 1, XII 3.2 | **printed form** |
| `ConnectedConnectedAn` | `X` proper and irreducible ⇒ `ConnectedSpace (CPt X)` for `analyticTopology X` | Shafarevich, *BAG 2*, VII §2.1 Thm. 1; SGA 1, XII 2.4 | **printed form, special case** (`X` proper) |

Why these are printed form. Each leaf is unif-printed's statement with `classicalTopology` replaced by
`analyticTopology`, and `*_iff` proves the two versions equivalent. `analyticTopology` is the definition in the
sources. GAGA §2, SGA 1 XII §1 and Hartshorne App. B (STANDARD; locators UNVERIFIED) define it as follows: cover `X`
by affine opens `U`, embed `U ↪ 𝔸^k`, give `U(ℂ) = V(I) ⊂ ℂ^k` the subspace topology, and glue. The Lean definition
has each part:
- The "embed" step is `Generates` (surjectivity of `ℂ[x₁, …, x_k] → Γ(X, U)`, which is exactly a closed embedding
  `U ↪ 𝔸^k`).
- `U(ℂ) = V(I)` holds as sets (`range_coord`), and `coord` is injective.
- The topology on `U(ℂ)` is the subspace topology (`exists_homeomorph_zeroLocus`).
- The gluing is `gluedTopology`.

The definition quantifies over all charts, while the sources fix one cover. They agree:
`classicalTopology_eq_gluedTopology` shows that every covering family of charts gives the same topology. The
covering condition is only on `ℂ`-points, which makes the theorem stronger. `AffineChart` is a data bundle of
concrete objects (an affine open, `k` sections and the surjectivity), not a hypothesis structure. Remaining risks
for a statement check: none from the topology. The two weakenings of `SmoothComplexManifold` noted above remain,
and both are weaker than the print. Shafarevich's varieties are reduced and quasi-projective, while the leaves
quantify over proper smooth `ℂ`-schemes. unif-printed's report §1 discusses this; SGA 1 XII covers schemes locally
of finite type.

**Alternative fold, if preferred.** Keep unif-printed's spec (`scratch/unif-printed/autofold.json`, leaves over
`classicalTopology`). Then rate those three leaves printed form, citing `classicalTopology_eq_analyticTopology` (and
the `*_iff`) as the identification. Both folds have the same count. The spec below uses the restated leaves, so the
definition in each statement is literally the print's.

## 4. Autofold spec

`scratch/unif-topology/autofold.json` discharges `uniformizationLeafAll` by
`_root_.UnifTopology.uniformizationLeafAll_of_analytic {n}.mumfordComplexTorus {n}.smoothComplexManifoldAn
{n}.properCompactAn {n}.connectedConnectedAn`. It adds the four leaves to the textbook bundle with kind `published`
and flag `unread: new printed leaf, no reading recorded; locator UNVERIFIED`. The import is
`ZInQKernel.Contrib.OneProof.UniformizationTopology`.

The `--dry-run` exits 0 and prints "strict count: 46/10 on 56 -> 49/10 on 59; strictest 45/11 -> 48/11". In this
base's `kinds.tsv` the field is still LEAF; with the field re-rated GLUE the count goes 46/11 -> 49/10. The dry-run
module minus its first line is `scratch/unif-topology/FoldDryRun.lean`. It compiles against the built tree, and
`HDec.HSyn.sixContactMin_of_open30` has axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED).

## 5. Method (all VERIFIED, compiled)

- **Evaluation is a ℂ-algebra map.** `evP P U h := (P.left.appLE U ⊤ h ≫ ΓSpecIso.hom).hom` (equal to `XevalAt`
  by `rfl`). `evP_comp_algC` holds because `P.left ≫ X.hom = 𝟙` (`Over.w`, `ptObj_hom`) and `appLE_comp_appLE`.
  Hence `evP P (eval₂ algC f p) = eval (coord P) p` (`evP_eval₂`).
- **Basic opens.** `P ∈ D(s)(ℂ) ↔ s(P) ≠ 0` (`Scheme.basicOpen_appLE`, `basicOpen_of_isUnit`, `basicOpen_zero`;
  `Spec ℂ` has one point).
- **Classical ≤ induced.** The coordinates are regular on `U`, so they are classical-continuous on `U(ℂ)`
  (`continuous_xevalAt_restrict`).
- **Induced ≤ classical** (`continuous_val_coord`). Take a basic classical open `{P ∈ V(ℂ) : |g(P) − z| < ε}` and a
  point `P₀ ∈ U(ℂ)` in it. Choose `s ∈ Γ(U)` with `P₀ ∈ D(s) ⊆ U ∩ V` (`IsAffineOpen.exists_basicOpen_le`). Write
  `g|D(s) · s^m = a|D(s)` (`IsAffineOpen.isLocalization_basicOpen`, `IsLocalization.surj`), and write `a`, `s` as
  polynomials in the `fᵢ` (`Generates`). Then near `P₀` the open set is the pullback of
  `{w : ps(w) ≠ 0, |pa(w)/ps(w)^m − z| < ε}`, which is open in `ℂ^k` (`MvPolynomial.continuous_eval`).
- **Injectivity** (`eq_of_appLE_eq`, `coord_injective`). `SpecMap_appLE_fromSpec` and `fromSpec_top` give
  `P.left = isoSpec.hom ≫ Spec.map (P.left.appLE U ⊤ _) ≫ hU.fromSpec`, and the ring map is fixed by the generators.
- **Image** (`range_coord`). For `w ∈ V(I)`, `ψ := lift(eval w) ∘ (quotientKerEquivOfSurjective)⁻¹ : Γ(U) → ℂ`, and
  the point is `Spec.map ψ ≫ hU.fromSpec`. It lies over `Spec ℂ` by `SpecMap_appLE_fromSpec` for `X.hom` and
  `isoSpec_Spec_inv`, lies in `U` by `range_fromSpec`, and has ring map `ψ` by `cancel_mono` and
  `Spec.map_injective`.
- **Gluing** (`classicalTopology_eq_gluedTopology`). `⨆ ≤ classical` by `coinduced_le_iff_le_induced` and the
  affine theorem. In the other direction, a glued-open `S` is `⋃ⱼ Oⱼ ∩ Uⱼ(ℂ)` with `Oⱼ` classical-open
  (`isOpen_induced_iff`) and `Uⱼ(ℂ)` classical-open (`isOpen_ptIn`).
- **Charts exist** (`exists_affineChart`). Use the affine basis (`isBasis_affineOpens`).
  `HasRingHomProperty.appLE` for `LocallyOfFiniteType` gives `X.hom.appLE ⊤ V` of finite type, so `algC` is of
  finite type, and `Algebra.FiniteType.iff_quotient_mvPolynomial''` gives the generators.
- **Leaves.** For proper `X`, `LocallyOfFiniteType` is an instance, so `rw [classicalTopology_eq_analyticTopology]`
  gives the `*_iff`.

## 6. Files

- `ZInQKernel/Contrib/OneProof/UniformizationTopology.lean`: the deliverable, copied from
  `scratch/unif-topology/Topo.lean`.
- `scratch/unif-topology/`: `Topo.lean` (the scratch, with `#print axioms`), `DischargesCheck.lean`,
  `discharges.txt`, `autofold.json`, `autofold-dryrun.txt`, `FoldDryRun.lean` and `log.md`.
