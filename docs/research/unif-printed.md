# unif-printed: `uniformizationLeafAll` from four printed leaves

**Main result (VERIFIED: compiled, `lake build ZInQKernel.Contrib.OneProof.UniformizationPrinted`, axioms
`propext`, `Classical.choice`, `Quot.sound`).** The textbook field `uniformizationLeafAll`
(`BPAnalytic.Uniformization.UniformizationLeafAll`, `ZInQKernel/HDecomp/Analytic/Uniformization.lean:91`), being
re-rated from published to consequence (GLUE), is proved in Lean from four printed statements:

```lean
theorem UnifPrinted.uniformizationLeafAll_of_printed (hM : MumfordComplexTorus) (hMan : SmoothComplexManifold)
    (hPC : ProperCompact) (hCC : ConnectedConnected) : UniformizationLeafAll
```

in `ZInQKernel/Contrib/OneProof/UniformizationPrinted.lean` (imports only
`ZInQKernel.HDecomp.Analytic.Uniformization`, the module that declares the statement). The statement of the field
is unchanged. Against the re-rated count this is **-1 GLUE**: one GLUE field out, four LEAF rows in
(the autofold dry run against the current `kinds.tsv`, where the field is still LEAF, reports
"strict count: 46/10 on 56 -> 49/10 on 59; strictest 45/11 -> 48/11"; with the field re-rated it is
46/11 -> 49/10). The field `gagaMorphism` is not used: the coordinate form needs only the analytic structure of
`A(ℂ)`, not the algebraicity of analytic maps.

**What Mathlib is missing.** Mumford's statement is about `A^an`. Mathlib (v4.35.0) has no complex analytic spaces,
no analytification functor `X ↦ X^an`, and no complex structure on `X(ℂ)` for a scheme `X` over `ℂ` (the vendored
libraries and the kernel have none either: `Torus.lean` gives the analytic structure of `ℂ^g ⧸ Λ` only). So "a
complex abelian variety is analytically isomorphic to `ℂ^g ⧸ Λ`" cannot be stated literally over genuine
definitions. The smallest faithful leaves are: Mumford's §1 theorem itself, which *can* be stated literally over
Mathlib's complex Lie groups, and three statements of the analytic dictionary (SGA 1 XII, Shafarevich VII), stated
over one concrete definition, the classical topology of `X(ℂ)`.

## 1. The leaves (Lean, `namespace UnifPrinted`)

`CPt X := AbVar.ptObj ℂ ⟶ X` (the `ℂ`-points of `X : Over (Spec ℂ)`; for `X = A.X` it is `A.Pt ℂ`), `XPtIn`,
`XevalAt` (bp-analytic's `PtIn`, `evalAt` for any `ℂ`-scheme; `rfl`-equal to them on `A.X`).

**Definition (concrete, not a leaf).** `classicalTopology X := generateFrom {{P | P ∈ U(ℂ), ‖f(P) - z‖ < ε}}`:
the coarsest topology in which every `U(ℂ)` is open and every regular function on `U` is continuous on `U(ℂ)`.
On an affine open `U ⊂ 𝔸^m` it is the subspace topology of `U(ℂ) ⊂ ℂ^m` (the coordinates are regular; every regular
function on a Zariski open of `U` is locally a quotient of polynomials); so it is the analytic topology of the
literature (STANDARD; the identification is not formalized).

| leaf | Lean statement (abridged) | source (locators UNVERIFIED) | rating |
| --- | --- | --- | --- |
| `MumfordComplexTorus` | `∀ g (X : Type) [TopologicalSpace X] [ChartedSpace (Fin g → ℂ) X] [Group X], IsManifold 𝓘(ℂ, ℂ^g) ω X → LieGroup 𝓘(ℂ, ℂ^g) ω X → T2Space X → CompactSpace X → ConnectedSpace X → ∃ Λ (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ) (e : Torus Λ ≃ₘ^ω⟮𝓘, 𝓘⟯ X), ∀ a b, e (a + b) = e a * e b` | Mumford, *Abelian varieties*, §1 (theorem: a compact connected complex Lie group is commutative and `≅ ℂ^g ⧸ Λ`); Birkenhake–Lange, *Complex abelian varieties*, §1.1 | **printed form** (the theorem as printed, over Mathlib's definitions; commutativity is implied by the conclusion) |
| `SmoothComplexManifold` | `∀ X, Smooth X.hom → IsProper X.hom → IrreducibleSpace X.left → (with classicalTopology X) ∃ n (_ : ChartedSpace (Fin n → ℂ) (CPt X)), IsManifold 𝓘(ℂ, ℂ^n) ω ∧ (∀ U f, ContMDiffOn … ω (XevalAt X U f) U(ℂ)) ∧ (∀ P, ∃ U (f : Fin n → Γ(X, U)), P ∈ U(ℂ) ∧ IsLocalDiffeomorphAt … ω (Q ↦ (f_i(Q))_i) P)` | Shafarevich, *Basic algebraic geometry 2*, 2nd ed., VII §1.1 (`X(ℂ)` of a nonsingular variety is a complex manifold; local parameters are local coordinates; regular functions are holomorphic); Serre, GAGA §2; SGA 1, XII 1.1, 3.1 | **printed form**, special case (`X` proper; "local parameters are coordinates" weakened to "some regular functions are coordinates") |
| `ProperCompact` | `∀ X, IsProper X.hom → CompactSpace (CPt X)` (classical topology) | Serre, GAGA §2, Prop. 6; SGA 1, XII 3.2; Shafarevich VII §2 | **printed form** |
| `ConnectedConnected` | `∀ X, IsProper X.hom → IrreducibleSpace X.left → ConnectedSpace (CPt X)` (classical topology) | Shafarevich VII §2.1, Thm. 1 (irreducible `X` ⇒ `X(ℂ)` connected); SGA 1, XII 2.4 (connected ⇔ connected, `X` locally of finite type) | **printed form**, special case (`X` proper) |

Reasons for the ratings. Each leaf is a published theorem (or a special case of one: extra hypotheses only), stated
over Mathlib's definitions (complex analytic manifolds, Lie groups, local diffeomorphisms, compactness,
connectedness, schemes) and the concrete `classicalTopology`; none is over a structure invented for the purpose.
The three dictionary leaves are separate theorems in the sources (existence of the complex structure; properness;
connectedness), so none is a composite. The one identification a reader must accept is `classicalTopology` = the
print's analytic topology (definitional in substance, see above). Risks for a statement check: (a) Shafarevich's
varieties are reduced and (in vol. 1) quasi-projective; the leaves quantify over all proper smooth (resp.
irreducible) `ℂ`-schemes; smooth proper schemes over `ℂ` are reduced and SGA 1 XII covers all schemes locally of
finite type, so the statements stay within the printed theorems; (b) in `SmoothComplexManifold` the chart
dimension is existential (`∃ n`); the print gives `n = dim X`, so this is weaker.

## 2. The proof (all VERIFIED, compiled)

Stage 1 (`uniformizationLeafAll_of_lieGroup`). Given a compact connected complex Lie group structure on `A(ℂ)`
whose topology and complex structure are those of regular functions (`IsAnalyticStr`: `U(ℂ)` open; regular
functions holomorphic; `g` regular functions are a local diffeomorphism at each point; neighbourhoods are cut out by
finitely many regular functions), Mumford gives `e : ℂ^g ⧸ Λ ≃ A(ℂ)`. Then `φ := e` satisfies bp-analytic's three
clauses: (i) composition of holomorphic maps, converted to `AnalyticOnNhd` on an open set
(`ContDiffOn.analyticOn`); (ii) `proj : ℂ^g → ℂ^g ⧸ Λ` is a local biholomorphism (`isLocalDiffeomorphAt_proj`, the
inverted charts of `Torus.lean`), so the coordinates composed with `e ∘ proj` are a local diffeomorphism and their
`mfderiv` is invertible; (iii) `e` is a homeomorphism, so `e(N)` is a neighbourhood, cut out by regular functions.

Stage 2a. `nhds_classical` (an open set of `classicalTopology` contains, around each point, a set
`{P ∈ U(ℂ) : |f_i(P) - f_i(P₀)| < ε}`; induction on `GenerateOpen`, with restriction of regular functions);
`continuous_comp` and `contMDiff_comp` (a morphism of `ℂ`-schemes is continuous and holomorphic on `ℂ`-points:
continuity from the generating sets; holomorphy through the local inverse of the target's coordinates).

Stage 2b (Mathlib only). `ker_eq_bot_of_injOn`: a map with surjective strict derivative, injective near the point,
has injective derivative (Mathlib's `implicitToOpenPartialHomeomorph`). `contMDiffAt_rightInverse`: a right inverse
`σ` of an injective holomorphic `ι : M₂ → N` with surjective `mfderiv` at `x₀` is holomorphic at `ι x₀` (in charts:
`Ψ = eN ∘ ι ∘ e2⁻¹` has invertible derivative, `ContDiffAt.to_localInverse` at `ω`, and `σ = e2⁻¹ ∘ Ψ⁻¹ ∘ eN` near
`ι x₀` by injectivity). `surjective_mfderiv_of_sections`: for `N = M × M`, sections `P ↦ (P, Q₀)`, `Q ↦ (P₀, Q)`
make `mfderiv ι` surjective (`mfderiv_prod_left/right`).

Stage 2c (`abVarAnalyticLieGroup_of_printed`). `SmoothComplexManifold` for `A` (dimension `g`) and for `A × A`
(dimension `n`, a priori unrelated; `A × A` is smooth, proper and integral over `ℂ` by Mathlib instances). The
comparison `ι : (A × A)(ℂ) → A(ℂ) × A(ℂ)` is holomorphic and bijective (inverse `σ(P, Q) = lift P Q`); the sections are
the scheme morphisms `secL Q = lift 𝟙 (toUnit ≫ inv (toUnit ptObj) ≫ Q)`, `secR P`; stage 2b makes `σ` holomorphic;
then `P * Q = lift P Q ≫ μ` is holomorphic, `P⁻¹ = P ≫ ι` is a regular map; `T₂` from `T₁`
(`ChartedSpace.t1Space`) and the group structure; compactness and connectedness from the two other leaves.

## 3. `#discharges` (VERIFIED)

`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` (12,994 jobs, success), then
`lake env lean scratch/unif-printed/DischargesCheck.lean` (full output in `DischargesCheck-output.txt`); the rows
for this contribution:

```
DISCHARGES [OpenTextbookLeaves11.uniformizationLeafAll] by UnifPrinted.uniformizationLeafAll_of_lieGroup
  still assumes: [UnifPrinted.MumfordComplexTorus, UnifPrinted.AbVarAnalyticLieGroup]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves11.uniformizationLeafAll] by UnifPrinted.uniformizationLeafAll_of_printed
  still assumes: [UnifPrinted.MumfordComplexTorus,
 UnifPrinted.SmoothComplexManifold,
 UnifPrinted.ProperCompact,
 UnifPrinted.ConnectedConnected]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1846 theorems checked, 9 discharge one
```

(The first row is the stage-1 intermediate, with the composite `AbVarAnalyticLieGroup`; the fold uses the second.)

## 4. Autofold spec

`scratch/unif-printed/autofold.json`: discharges `uniformizationLeafAll` by
`_root_.UnifPrinted.uniformizationLeafAll_of_printed {n}.mumfordComplexTorus {n}.smoothComplexManifold
{n}.properCompact {n}.connectedConnected`, adding the four leaves to the textbook bundle, kind `published`, flag
`unread: new printed leaf, no reading recorded; locator UNVERIFIED`. The dry run (`--dry-run`, output in
`scratch/unif-printed/autofold-dryrun.txt`) generates `OpenTextbookLeaves12` and `sixContactMin_of_open30`; that
module (`scratch/unif-printed/FoldDryRun.lean`, the dry run without its first line) compiles against the built tree,
`HDec.HSyn.sixContactMin_of_open30` with axioms `propext`, `Classical.choice`, `Quot.sound` (VERIFIED).

## 5. Files

* `ZInQKernel/Contrib/OneProof/UniformizationPrinted.lean` (the deliverable, generated from the stage files).
* `scratch/unif-printed/Stage1.lean`, `Stage2a.lean`, `Stage2b.lean`, `Stage2c.lean` (stage files; 1, 2a, 2b compile
  alone; 2c only inside `Unif.lean`), `build_unif.py` (concatenation), `Unif.lean` (the concatenation with
  `#print axioms`), `autofold.json`, `autofold-dryrun.txt`, `log.md`.
