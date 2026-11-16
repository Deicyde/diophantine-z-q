# sga1-etale: `SmoothComplexManifoldAn` from the étale clause of SGA 1 XII 3.1

**Result (VERIFIED: compiled; `lake build ZInQKernel.Contrib.OneProof.SmoothComplexManifoldEtale` succeeds,
and every theorem below has axioms `propext`, `Classical.choice`, `Quot.sound`).** unif-topology's leaf
`UnifTopology.SmoothComplexManifoldAn` is now a theorem. It is proved from one smaller leaf,
`SGA1Etale.SGA1_XII_3_1_Etale`, the étale clause of SGA 1 XII 3.1 over `analyticTopology`, with all the rest
proved in Lean from Mathlib and unif-topology:

```lean
theorem SGA1Etale.smoothComplexManifoldAn_of_etale (hL : SGA1_XII_3_1_Etale) :
    UnifTopology.SmoothComplexManifoldAn
```

The hypothesis stays Mathlib's `Smooth X.hom`. No smooth-to-nonsingular bridge is used, because SGA 1 says
*lisse*. As asked, the connectedness leaf is weakened from `ConnectedSpace` to `PreconnectedSpace` (Bourbaki's
*connexe*), and the nonemptiness is proved. The textbook field then follows:

```lean
theorem SGA1Etale.uniformizationLeafAll_of_etale (hM : MumfordComplexTorus) (hL : SGA1_XII_3_1_Etale)
    (hPC : ProperCompactAn) (hCC : ConnectedPreconnectedAn) :
    BPAnalytic.Uniformization.UniformizationLeafAll
```

The file is `ZInQKernel/Contrib/OneProof/SmoothComplexManifoldEtale.lean` (26 KB). It imports
`ZInQKernel.Contrib.OneProof.UniformizationTopology`, the module that defines `SmoothComplexManifoldAn`. It needs
unif-printed's and unif-topology's files in the tree, so fold it with them or after them. No statement was
changed, and nothing outside this file and `scratch/sga1-etale/` was edited.

**Count.** All four leaves can be rated printed form (§3). This base's `kinds.tsv` still rates the field
`uniformizationLeafAll` LEAF, so the dry run gives "strict count: 46/10 on 56 -> 49/10 on 59". That is the same
GLUE count as unif-topology's spec. Compared with unif-topology's fold, the difference is the
`SmoothComplexManifoldAn` row. That row bundles several printed facts (chart dimension, manifold, holomorphy,
local parameters), so if it is rated GLUE, unif-topology's fold is neutral and this one is **-1 GLUE**. With the
field rated GLUE, this fold goes from 46/11 to 49/10.

## 1. The new leaves (verbatim; namespace `SGA1Etale`, `open UnifPrinted UnifTopology`)

```lean
def SGA1_XII_3_1_Etale : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), LocallyOfFiniteType X.hom →
    ∀ (U : X.left.Opens), IsAffineOpen U → ∀ (n : ℕ) (f : Fin n → Γ(X.left, U)),
      (MvPolynomial.eval₂Hom (algC X U) f).Etale →
      letI := analyticTopology X
      ∀ P : CPt X, XPtIn X P U →
        (∃ e : OpenPartialHomeomorph (CPt X) (Fin n → ℂ), P ∈ e.source ∧
            e.source ⊆ {Q | XPtIn X Q U} ∧ ∀ Q ∈ e.source, e Q = fun i => XevalAt X U (f i) Q) ∧
        (∀ g : Γ(X.left, U), ∃ h : (Fin n → ℂ) → ℂ,
            AnalyticAt ℂ h (fun i => XevalAt X U (f i) P) ∧
            ∀ᶠ Q in 𝓝 P, XevalAt X U g Q = h (fun i => XevalAt X U (f i) Q))

def ConnectedPreconnectedAn : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), IsProper X.hom → IrreducibleSpace X.left →
    @PreconnectedSpace (CPt X) (analyticTopology X)
```

All the objects are concrete:
- `algC X U : ℂ →+* Γ(X, U)` is the structure map.
- `MvPolynomial.eval₂Hom (algC X U) f` is the ring map `ℂ[x₁, …, xₙ] → Γ(X, U)`, `xᵢ ↦ fᵢ`. For `U` affine, it
  is étale exactly when `U → 𝔸ⁿ_ℂ` is étale.
- `RingHom.Etale` is Mathlib's.
- `CPt`, `XPtIn` and `XevalAt` are unif-printed's ℂ-points, membership and evaluation.
- `analyticTopology X` is unif-topology's topology, glued from the subspace topologies of `U(ℂ) ⊂ ℂ^k`.
- `OpenPartialHomeomorph` and `AnalyticAt` are Mathlib's.

The two halves of the étale leaf, as the task asks:
1. `Q ↦ (fᵢ(Q))` is a homeomorphism from an open neighbourhood of `P` onto an open subset of `ℂⁿ`.
2. Every regular function on `U` is, near `P`, an analytic function of `f₁, …, fₙ`.

## 2. Glue proved (all VERIFIED, compiled; standard axioms)

| theorem | content | method |
| --- | --- | --- |
| `exists_etale_chart` | `[Smooth X.hom]`: every point `x` has an affine `U ∋ x` and `f : Fin n → Γ(X, U)` with `eval₂Hom (algC X U) f` étale | `Smooth.exists_isStandardSmooth`. The open of `Spec ℂ` is `⊤`, since `Spec ℂ` has one point. Then `RingHom.IsStandardSmooth.exists_etale_mvPolynomial` (already in the Mathlib pin: standard smooth implies étale over the polynomial ring in the free variables), composed with the isomorphism `MvPolynomial.mapEquiv` along `ΓSpecIso` |
| `etale_res` | étale coordinates restrict to basic opens `D(s) ⊆ U` | `eval₂Hom_res` (restriction commutes with the coordinate map, `Scheme.Hom.appLE_map`), `Algebra.Etale.of_isLocalizationAway`, `IsAffineOpen.isLocalization_basicOpen`, `RingHom.Etale.stableUnderComposition` |
| `exists_cPt_of_mem` | `[LocallyOfFiniteType X.hom]`: a nonempty open has a `ℂ`-point | affine `W` inside it with generators (as in `exists_affineChart`). `Γ(W) ≠ 0`, because `basicOpen 1 = W` and `basicOpen 0 = ⊥`. Hence the ideal of relations is `≠ ⊤`. Nullstellensatz (`MvPolynomial.vanishingIdeal_zeroLocus_eq_radical`) gives a zero `w`, and `range_coord` gives a point with coordinates `w` |
| `regFun_local` | a regular function on any open `W` is, near each point of `U(ℂ) ∩ W(ℂ)`, analytic in étale coordinates on `U` | the leaf's half (2) on a basic open `D(s) ⊆ U ∩ W` (`IsAffineOpen.exists_basicOpen_le`), with `xevalAt_res` and `isOpen_ptIn` (via `classicalTopology_eq_analyticTopology`) |
| `chart_rep`, `chart_rep_pi` | in the chart `e` of the leaf's half (1), `g ∘ e⁻¹` is analytic near each point | `regFun_local` and the continuity of `e⁻¹` |
| `eq_of_local_inverse` | `H : ℂⁿ → ℂᵐ` and `H' : ℂᵐ → ℂⁿ`, differentiable and inverse to each other near a point, force `n = m` | `fderiv_comp`, `EventuallyEq.fderiv_eq`, `LinearEquiv.finrank_eq` |
| `dim_eq` | two étale charts at a common `ℂ`-point have the same dimension | the transition maps both ways are analytic (`chart_rep_pi`) and inverse to each other near the point |
| `exists_echart` | `[Smooth X.hom] [IrreducibleSpace X.left]`: one `n` with an `n`-dimensional étale chart at every `ℂ`-point | two chart domains meet (`nonempty_preirreducible_inter`), the intersection has a `ℂ`-point (`exists_cPt_of_mem`), then `dim_eq` |
| `chartedSpaceOf`, `isManifold_of` | the atlas of leaf charts is an analytic atlas | `isManifold_of_contDiffOn`. Transition maps agree near each point with an analytic `H` (`chart_rep_pi`), and `AnalyticAt.contDiffAt` |
| `contMDiffOn_xevalAt` | regular functions on any `W` are holomorphic on `W(ℂ)` | `contMDiffAt_iff` and `chart_rep` |
| `chartDiffeo` | each chart is a `PartialDiffeomorph` | `contMDiffOn_chart`, `contMDiffOn_chart_symm` |
| `smoothComplexManifoldAn_of_etale` | `SmoothComplexManifoldAn` | the charts give the local coordinates `(ch P).f`, so `IsLocalDiffeomorphAt` holds by `chartDiffeo` |
| `connectedConnectedAn_of_preconnected` | `ConnectedPreconnectedAn → ConnectedConnectedAn` | for every proper irreducible `X`, `X(ℂ)` is nonempty (`exists_cPt_of_mem` on `⊤`) |

**On the Nonempty step.** The task suggested supplying `Nonempty` from `1 ∈ A(ℂ)` inside
`abVarAnalyticLieGroup_of_printed`. That theorem lives in unif-printed's file, which may not be edited, and it
consumes the general `ConnectedConnected`. So the nonemptiness is proved instead for every proper irreducible
`X` (Nullstellensatz), which upgrades the Bourbaki-convention leaf to `ConnectedConnectedAn`. The existing
assembly is then reused unchanged. The effect is the same: the leaf asks only for `PreconnectedSpace`, and
`Nonempty` is glue.

## 3. `#discharges` (VERIFIED)

`lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` (12,994 jobs) succeeded. Then
`lake env lean scratch/sga1-etale/DischargesCheck.lean`, with full output in `scratch/sga1-etale/discharges.txt`:

```
DISCHARGES [OpenTextbookLeaves11.uniformizationLeafAll] by SGA1Etale.uniformizationLeafAll_of_etale
  still assumes: [UnifPrinted.MumfordComplexTorus,
 SGA1Etale.SGA1_XII_3_1_Etale,
 UnifTopology.ProperCompactAn,
 SGA1Etale.ConnectedPreconnectedAn]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1916 theorems checked, 11 discharge one
```

The output also lists unif-printed's and unif-topology's rows, because their modules are imported. The
`#print axioms` results for `uniformizationLeafAll_of_etale`, `smoothComplexManifoldAn_of_etale`,
`connectedConnectedAn_of_preconnected`, `exists_etale_chart`, `exists_cPt_of_mem` and `dim_eq` are all
`[propext, Classical.choice, Quot.sound]`.

## 4. Leaves and ratings (locators UNVERIFIED; nobody has read SGA 1 XII for this task)

| leaf | source | rating |
| --- | --- | --- |
| `SGA1Etale.SGA1_XII_3_1_Etale` (new) | SGA 1 (LNM 224, 1971), Exp. XII: §1 (1.1, the analytic space `X^an`, the morphism `X^an → X`) and Prop. 3.1 (for a morphism of `ℂ`-schemes locally of finite type, `f` étale iff `f^an` étale) | **printed form, special case** (see below) |
| `SGA1Etale.ConnectedPreconnectedAn` (new; replaces `ConnectedConnectedAn`) | Shafarevich, *BAG 2*, VII §2.1 Thm. 1; SGA 1, XII 2.4 | **printed form, special case** (`X` proper). The conclusion is Bourbaki's *connexe*, which allows the empty space, so `PreconnectedSpace` is exactly the printed word and weaker than the previous `ConnectedSpace` |
| `UnifPrinted.MumfordComplexTorus` | unchanged (Mumford §1) | printed form (unif-printed) |
| `UnifTopology.ProperCompactAn` | unchanged (GAGA §2 Prop. 6; SGA 1 XII 3.2) | printed form (unif-topology) |

**Why `SGA1_XII_3_1_Etale` is printed form.** Take `X` locally of finite type over ℂ (SGA 1 XII's standing
hypothesis), `U` affine, and `U → 𝔸ⁿ_ℂ` étale. Then XII 3.1 says `U^an → (𝔸ⁿ)^an = ℂⁿ` is étale. For analytic
spaces, étale means a local isomorphism of ℂ-ringed spaces. Unpacked:
- Topologically: each `P` has an open neighbourhood `W ⊆ U^an` mapped homeomorphically onto an open `V ⊆ ℂⁿ`.
  This is half (1), since `U^an` is open in `X^an` and the map is `Q ↦ (fᵢ(Q))`.
- On structure sheaves: `O_V ≅ O_W`. A regular function `g` on `U` gives a section `g^an` of `O_{U^an}`, through
  the morphism `X^an → X` of XII 1.1. Its value at `Q ∈ X(ℂ)` is `g(Q)`. Restricted to `W`, it is `h ∘ f` for a
  holomorphic `h` on `V`, which is half (2), with `AnalyticAt` for holomorphic.

The underlying set of `X^an` is `X(ℂ)`, and its topology is the chart topology. unif-topology proved that this
topology is `analyticTopology` (`classicalTopology_eq_analyticTopology`; `analyticTopology` is that definition).
The special cases are `U` affine and the étale map given by its ring map. Both make the leaf weaker.

**What the leaf takes from more than XII 3.1 alone** (the task asked for this exactly):
- Half (2) uses two things from the construction in XII 1.1, not from the statement of 3.1:
  - the morphism of ringed spaces `X^an → X`, which sends regular functions to holomorphic functions;
  - the identification of the value of `g^an` at a point with `g(Q)`.
  Both are part of SGA 1's construction of `X^an`.
- Half (1) uses that the topology of `X^an` is the one glued from `U(ℂ) ⊂ ℂ^k`. This is also XII 1.1, and the
  Lean side of it is unif-topology's theorem.
- Nothing else is needed. The step from smooth to locally étale, the constancy of the dimension, and the manifold
  structure are proved glue. Of 3.1, the leaf states only the direction `f` étale ⇒ `f^an` étale. The
  converse and the *lisse* clause are not used.

**Statement check.** These statements need checking against the print:
- the numbering "Prop. 3.1" and that its list includes *étale* (from memory, UNVERIFIED);
- that SGA 1 XII defines étale analytic morphisms as local isomorphisms (UNVERIFIED).

If XII 3.1 lists only *lisse* and not *étale*, the leaf is still the étale case of the smooth clause of relative
dimension 0, but the rating would need that reading.

**Proposed rows for `docs/research/locators.md`** (not added; that file belongs to other tasks):
- `SGA1_XII_3_1_Etale`: SGA 1, Exp. XII, 1.1 and Prop. 3.1. The étale clause, with local isomorphism of analytic
  spaces, special case `U` affine. UNVERIFIED.
- `ConnectedPreconnectedAn`: SGA 1, Exp. XII, Prop. 2.4, and Shafarevich *BAG 2* VII §2.1 Thm. 1, with Bourbaki
  *connexe* (empty allowed). UNVERIFIED.

## 5. Autofold spec (VERIFIED dry run)

`scratch/sga1-etale/autofold.json` discharges `uniformizationLeafAll` by

```
_root_.SGA1Etale.uniformizationLeafAll_of_etale {n}.mumfordComplexTorus {n}.sga1_XII_3_1_Etale
  {n}.properCompactAn {n}.connectedPreconnectedAn
```

It adds the four leaves to the textbook bundle, each with kind `published` and flag
`unread: new printed leaf, no reading recorded; locator UNVERIFIED`. The import is
`ZInQKernel.Contrib.OneProof.SmoothComplexManifoldEtale`. It replaces unif-topology's spec: fold one or the other.

`python3 scripts/one_proof/autofold.py scratch/sga1-etale/autofold.json --dry-run` exits 0 and prints "strict
count: 46/10 on 56 -> 49/10 on 59; strictest 45/11 -> 48/11". The dry-run module minus its first line is
`scratch/sga1-etale/FoldDryRun.lean`. It compiles, and `HDec.HSyn.sixContactMin_of_open30` has axioms
`[propext, Classical.choice, Quot.sound]`.

## 6. Files

- `ZInQKernel/Contrib/OneProof/SmoothComplexManifoldEtale.lean`: the contribution.
- `scratch/sga1-etale/A.lean` … `E.lean`: the incremental scratch versions (E.lean is the module plus
  `#print axioms`). `DischargesCheck.lean` with `discharges.txt`, `autofold.json`, `autofold-dryrun.txt`,
  `FoldDryRun.lean`, `log.md`.
- Build note: the build tree was copied from `~/dzq-wt/pel-hodge`, a descendant of the base. Then
  `lake build ZInQKernel.Contrib.OneProof.UniformizationTopology` was run (9,052 jobs).
