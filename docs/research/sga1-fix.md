# sga1-fix: the analytic leaves in printed form

**Result (VERIFIED: compiled; `lake build ZInQKernel.Contrib.OneProof.SGA1Printed` succeeds, and every theorem
below has axioms `propext`, `Classical.choice`, `Quot.sound`).** Both textbook fields `uniformizationLeafAll` and
`gagaMorphism` are now theorems from printed leaves only. The review's three gaps are closed:

```lean
theorem SGA1Printed.uniformizationLeafAll_of_printed (hM : MumfordComplexTorus) (hL : SGA1_XII_3_3a)
    (hPC : ProperCompactAn) (hC : SGA1_XII_2_4) : BPAnalytic.Uniformization.UniformizationLeafAll

theorem SGA1Printed.gagaMorphism_of_printed (hM : MumfordComplexTorus) (hL : SGA1_XII_3_3a)
    (hPC : ProperCompactAn) (hC : SGA1_XII_2_4) (hG : SGA1_XII_4_4) : ZInQ.HomLattice.GAGAMorphism
```

What was done for each gap:

1. **Étale leaf.** `SGA1_XII_3_3a` is SGA 1 XII Remarque 3.3(a) ("`f` étale ⇒ `f^an` a local isomorphism").
   The leaf keeps only the topological part: `Q ↦ (fᵢ(Q))` is a local homeomorphism. sga1-etale's
   regular-functions half is no longer a hypothesis. It is **proved in Lean from étaleness alone**
   (`regular_half`), without the topological half. So no reading of "isomorphisme local" is needed: any
   reading implies a local homeomorphism.
2. **Connectedness leaf.** `SGA1_XII_2_4` is SGA 1 XII 2.4 ("only if") as the review asked: `X` locally of finite
   type and preconnected implies `X^an` preconnected.
3. **GAGA leaf.** `SGA1_XII_4_4` is GAGA for morphisms of abelian varieties, stated **without any atlas**: every
   morphism of analytic spaces `A^an → B^an` is `f^an`. "Morphism of analytic spaces" is `IsAnMorphism`. It is
   built on `AnFunAt`, a concrete Lean predicate for the structure sheaf of `X^an`. The following are proved in
   Lean:
   - in every `IsAnStr` atlas, the holomorphic functions are exactly `AnFunAt`, and the holomorphic maps are
     exactly the `IsAnMorphism`s;
   - `AnFunAt` is the pullback of `𝒪_{ℂⁿ}` along étale coordinates;
   - sga1-etale's étale atlas satisfies `IsAnStr`, using only the restated leaf;
   - hence `GAGAChart ↔ SGA1_XII_4_4`.

**Count (VERIFIED dry run).** The fold removes `uniformizationLeafAll` and `gagaMorphism` and adds five leaves.
Three are new and printed form (§3). Two are unif-printed's and unif-topology's existing printed leaves. At this
base both fields are still rated LEAF, so the dry run prints "46/10 on 56 -> 49/10 on 59; strictest 45/11 ->
48/11". With the two rows set to the 11-16 re-rating (`consequence`, GLUE, as on `wip/leaf-fold32`), it prints
"**44/12 on 56 -> 49/10 on 59; strictest 43/13 -> 48/11**". That is **−2 GLUE** in both columns, and the
strictest count does not rise. This meets the target.

The file is `ZInQKernel/Contrib/OneProof/SGA1Printed.lean` (31 KB). It imports
`ZInQKernel.Contrib.OneProof.GAGAChart`, which brings TailQ (where `GAGAMorphism` is defined), sga1-etale,
unif-topology and unif-printed. No statement was changed. Nothing outside that file, `scratch/sga1-fix/`, this
report and `.fleet/sga1-fix.md` was edited.

## 1. The leaves (verbatim; namespace `SGA1Printed`, `open UnifPrinted UnifTopology`)

```lean
def SGA1_XII_3_3a : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), LocallyOfFiniteType X.hom →
    ∀ (U : X.left.Opens), IsAffineOpen U → ∀ (n : ℕ) (f : Fin n → Γ(X.left, U)),
      (MvPolynomial.eval₂Hom (algC X U) f).Etale →
      letI := analyticTopology X
      ∀ P : CPt X, XPtIn X P U →
        ∃ e : OpenPartialHomeomorph (CPt X) (Fin n → ℂ), P ∈ e.source ∧
          e.source ⊆ {Q | XPtIn X Q U} ∧ ∀ Q ∈ e.source, e Q = fun i => XevalAt X U (f i) Q

def SGA1_XII_2_4 : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), LocallyOfFiniteType X.hom → PreconnectedSpace X.left →
    @PreconnectedSpace (CPt X) (analyticTopology X)

def AnFunAt (X : Over (Spec (CommRingCat.of ℂ))) (F : CPt X → ℂ) (P : CPt X) : Prop :=
  ∃ (U : X.left.Opens) (k : ℕ) (g : Fin k → Γ(X.left, U)) (H : (Fin k → ℂ) → ℂ),
    XPtIn X P U ∧ AnalyticAt ℂ H (fun i => XevalAt X U (g i) P) ∧
    ∀ᶠ Q in @nhds _ (analyticTopology X) P, F Q = H (fun i => XevalAt X U (g i) Q)

def AnFunOn (X : Over (Spec (CommRingCat.of ℂ))) (W : Set (CPt X)) (F : CPt X → ℂ) : Prop :=
  ∀ P ∈ W, AnFunAt X F P

def IsAnMorphism (X Y : Over (Spec (CommRingCat.of ℂ))) (F : CPt X → CPt Y) : Prop :=
  @Continuous _ _ (analyticTopology X) (analyticTopology Y) F ∧
  ∀ (W : Set (CPt Y)) (s : CPt Y → ℂ), @IsOpen _ (analyticTopology Y) W → AnFunOn Y W s →
    AnFunOn X (F ⁻¹' W) (s ∘ F)

def SGA1_XII_4_4 : Prop :=
  ∀ (A B : AbVar ℂ) (F : CPt A.X → CPt B.X), IsAnMorphism A.X B.X F →
    ∃ f : A.X ⟶ B.X, ∀ P, F P = P ≫ f
```

All objects are the existing concrete ones:
- `CPt`, `XPtIn`, `XevalAt`: unif-printed's `ℂ`-points, membership and evaluation;
- `algC`, `analyticTopology`: unif-topology's. `analyticTopology` is glued from `U(ℂ) ⊂ ℂ^k` and proved equal to
  the classical topology;
- `RingHom.Etale`, `OpenPartialHomeomorph`, `PreconnectedSpace`, `AnalyticAt`: Mathlib's;
- `PkgI3.AbVar`: the repository's abelian varieties.

No structure was invented. `AnFunAt` and `IsAnMorphism` are predicates on functions and maps of `ℂ`-points.

## 2. Glue proved (all VERIFIED, compiled; standard axioms)

| theorem | content | method |
| --- | --- | --- |
| `pfun`, `analyticAt_pfun`, `ev_aeval`, `hasDerivAt_pfun_snd` | `(y, τ) ↦ p(y; τ)` for `p ∈ ℂ[y₁, …, yₙ][τ]`: analytic everywhere, compatible with ring maps over `ℂ[y]`, with `τ`-derivative `p'(y; τ)` | `Polynomial.eval_eq_sum_range'`, `AnalyticAt.aeval_mvPolynomial`, `Polynomial.hasDerivAt` |
| `exists_analytic_of_standardEtale` | **holomorphic implicit functions.** Data: `S` standard étale over `ℂ[y]` with generator `x`, and ring maps `ev z : S → ℂ` over `y z ∈ ℂⁿ`, with `y` and `z ↦ ev z x` continuous at `z₀`. Conclusion: every `a ∈ S` is `h ∘ y` near `z₀`, with `h` analytic | `Φ(y, τ) = (y, f(y; τ))` has derivative `(dy, dτ) ↦ (dy, D(dy, dτ))`, invertible because `f'(x)` is a unit (`StandardEtalePair.HasMap.isUnit_derivative_f`). The local inverse is analytic (`OpenPartialHomeomorph.analyticAt_symm'`), so `ev z x = (Φ⁻¹(y z, 0)).2`. Each `a` has `a·g(x)^m = p(x)` (`exists_mul_aeval_x_g_pow_eq_aeval_x`) with `g(x)` a unit |
| `continuousAt_xevalAt_an` | regular functions are continuous on `U(ℂ)` (analytic topology) | gaga-chart's `continuousOn_xevalAt`, `classicalTopology_eq_analyticTopology` |
| `regular_half` | **sga1-etale's half (2), proved.** For `U` affine and `ℂ[x] → Γ(X, U)` étale, every regular `g` on `U` is near each `P ∈ U(ℂ)` an analytic function of `f₁, …, fₙ` | `Algebra.IsEtaleAt.exists_isStandardEtale` (Mathlib, Stacks 00UE) at the prime `ker(ev_P)` gives `s` with `s(P) ≠ 0` and `Γ(X, U)[1/s]` standard étale. `ev_Q` extends to `Γ(X, U)[1/s]` for `Q ∈ D(s)(ℂ)` (`IsLocalization.Away.lift`). Then apply `exists_analytic_of_standardEtale` |
| `sga1_XII_3_1_Etale_of_3_3a` | `SGA1_XII_3_3a → SGA1Etale.SGA1_XII_3_1_Etale` | the leaf plus `regular_half` |
| `connectedPreconnectedAn_of_2_4` | `SGA1_XII_2_4 → SGA1Etale.ConnectedPreconnectedAn` | proper ⇒ locally of finite type; irreducible ⇒ preconnected |
| `uniformizationLeafAll_of_printed` | **main theorem 1** | sga1-etale's `uniformizationLeafAll_of_etale` |
| `contMDiffAt_of_anFunAt`, `anFunAt_of_contMDiffAt`, `contMDiffAt_iff_anFunAt` | in any `IsAnStr` atlas, `F : X(ℂ) → ℂ` is holomorphic at `P` iff `AnFunAt X F P` | (←) clause 2 of `IsAnStr` and `AnalyticAt.contDiffAt`; (→) the regular coordinates of clause 3: `F = (F ∘ c⁻¹) ∘ c`, and `F ∘ c⁻¹` is analytic (`ContMDiffAt.contDiffAt`, `ContDiffAt.analyticAt`) |
| `anFunOn_xevalAt` | regular functions are `AnFunOn` on `U(ℂ)` | `H = proj₀` |
| `isAnMorphism_of_contMDiff`, `contMDiff_of_isAnMorphism`, `contMDiff_iff_isAnMorphism` | for `IsAnStr` atlases on `X(ℂ)` and `Y(ℂ)`, `F` is holomorphic iff `IsAnMorphism X Y F` | the previous line; gaga-chart's `contMDiffAt_of_regular` |
| `anFunAt_iff_etale` | for `X` smooth, from `SGA1_XII_3_3a`: `AnFunAt X F P` iff `F = h ∘ f` near `P`, with `f` étale coordinates on an affine `U ∋ P` and `h` holomorphic at `f(P)` | sga1-etale's `exists_etale_chart` and `regFun_local` (on the derived old leaf), `AnalyticAt.pi` |
| `isAnStr_of_3_3a` | sga1-etale's étale atlas satisfies `IsAnStr` (`X` smooth, proper, irreducible), from the restated leaf | gaga-chart's `isAnStr_of_etale` |
| `gagaChart_of_printed`, `printed_of_gagaChart`, `gagaChart_iff_printed` | `SGA1_XII_4_4 → GAGAChart`, unconditionally; `GAGAChart ↔ SGA1_XII_4_4` given `SGA1_XII_3_3a` (for the atlases) | `contMDiff_iff_isAnMorphism` |
| `gagaMorphism_of_printed` | **main theorem 2** | gaga-chart's `gagaMorphism_of_gagaChart` and `gagaChart_of_printed` |

## 3. Ratings of the new leaves (locators UNVERIFIED: nobody has read SGA 1 XII for this task)

| leaf | source | rating |
| --- | --- | --- |
| `SGA1Printed.SGA1_XII_3_3a` | SGA 1 (LNM 224, 1971), Exp. XII, Remarque 3.3(a), p. 325 (page from the 11-16 review), with `X^an` of XII 1.1 | **printed form (special case and consequence)** |
| `SGA1Printed.SGA1_XII_2_4` | SGA 1, Exp. XII, Prop. 2.4, "only if" | **printed form** |
| `SGA1Printed.SGA1_XII_4_4` | SGA 1, Exp. XII, Thm. 4.4 and its corollary on morphisms (`X` proper: `Hom(X, Y) → Hom(X^an, Y^an)` bijective); Serre, GAGA (1956), for projective varieties | **printed form (special case)** |

**`SGA1_XII_3_3a`: why printed form.** The print says that for `f` étale, `f^an` is a local isomorphism. The leaf
takes `f : U → 𝔸ⁿ_ℂ`, with `U` an affine open of `X` locally of finite type. Its conclusion is only the
topological part of the local isomorphism. The reading uses four facts:
- the underlying space of `X^an` is `X(ℂ)` with the analytic topology (XII 1.1; in Lean, unif-topology's
  `analyticTopology`, proved equal to the classical topology);
- `U^an` is the open subset `U(ℂ)` (XII 1.1);
- `(𝔸ⁿ)^an = ℂⁿ`, with `f^an` given by `Q ↦ (fᵢ(Q))`;
- a local isomorphism of ringed spaces is a local homeomorphism.

These are special cases and consequences only, so the leaf is weaker than the print.

**On "isomorphisme local" (the review's question).** I have not read SGA 1 XII 1.1 (UNVERIFIED; from memory,
analytic spaces there are `ℂ`-ringed spaces, so a local isomorphism includes the structure sheaves). The question
no longer matters for the leaf:
- sga1-etale's regular-functions half would have needed that reading, plus the morphism `X^an → X` of 1.1;
- it is now proved in Lean from the étaleness of `ℂ[x] → Γ(X, U)` alone (`regular_half`), without the
  topological half;
- the leaf keeps only the local homeomorphism, which every reading of "isomorphisme local" implies.

**`SGA1_XII_2_4`: why printed form.** It is the print's "`X` connected ⇒ `X^an` connected", for `X` locally of
finite type over `ℂ`, with no properness and no irreducibility. On both sides "connected" is `PreconnectedSpace`.
This is a consequence of the print under either convention for the empty space:
- under Bourbaki's convention (the empty space is connected) the leaf is exactly the print;
- if "connected" includes nonempty, then for `X ≠ ∅` the print gives the leaf, and for `X = ∅` we have
  `X(ℂ) = ∅`, so the leaf holds trivially.

The consumer's form (`X` proper and irreducible) is glue: `connectedPreconnectedAn_of_2_4`.

**`SGA1_XII_4_4`: why printed form, and why it is GAGA for `A^an` as printed.**
- **Special case.** The print gives a bijection `Hom(X, Y) → Hom(X^an, Y^an)` for `X` proper. The leaf takes
  `X = A` and `Y = B` abelian varieties, and asserts surjectivity only: every morphism `A^an → B^an` is `f^an`.
  On `ℂ`-points, `f^an` is `P ↦ P ≫ f`.
- **`IsAnMorphism` is "morphism of analytic spaces" for reduced spaces.** `A^an` and `B^an` are reduced: `A` and
  `B` are smooth, so `A^an` is smooth (XII 3.1; numbering UNVERIFIED), and its underlying space is a complex
  manifold (proved in Lean from `SGA1_XII_3_3a`: `isAnStr_of_3_3a`). A
  morphism of reduced complex spaces is determined by its underlying map, with `F^♯ s = s ∘ F`. A continuous map
  comes from a morphism exactly when it pulls back holomorphic functions to holomorphic functions
  (Grauert–Remmert, *Coherent analytic sheaves*, Ch. 1; locator UNVERIFIED). So every `IsAnMorphism` is a
  morphism `A^an → B^an`, and the leaf is not stronger than the print.
- **`AnFunAt` is the structure sheaf of `X^an`.** There are two readings, each proved consistent in Lean:
  1. *From 1.1.* For `U ↪ 𝔸^k` affine, `U^an` is the analytic subspace of `ℂ^k` cut out by the equations of `U`.
     Its sections are locally restrictions of holomorphic functions of the coordinates. Conversely, `H ∘ g` is
     the pullback of `H` along `g^an : U^an → ℂ^k`.
  2. *From 3.3(a).* For `X` smooth, the full local isomorphism `f^an` says that near `P` the structure sheaf is
     `(f^an)^* 𝒪_{ℂⁿ}`. By `anFunAt_iff_etale` (Lean), `AnFunAt` is exactly that sheaf.
- **Independence from the project's `IsAnStr`.** The leaf mentions no atlas. In Lean, `IsAnStr` atlases have
  exactly the holomorphic functions `AnFunAt` and exactly the holomorphic maps `IsAnMorphism`
  (`contMDiffAt_iff_anFunAt`, `contMDiff_iff_isAnMorphism`). sga1-etale's étale atlas is one of them
  (`isAnStr_of_3_3a`). So gaga-chart's `GAGAChart` is equivalent to this leaf (`gagaChart_iff_printed`), and its
  quantifier over `IsAnStr` atlases is GAGA for `A^an` as printed.

**Existing leaves in the fold** (not re-rated here; they keep their earlier ratings and flags):
- `UnifPrinted.MumfordComplexTorus`: Mumford §1, printed form (unif-printed);
- `UnifTopology.ProperCompactAn`: GAGA §2 Prop. 6, SGA 1 XII 3.2, printed form (unif-topology).

**Statement checks wanted.** Check each against the print:
- the numbering and wording of XII Remarque 3.3(a) (p. 325), Prop. 2.4 and Thm. 4.4 with its corollary;
- that XII 1.1 makes `U^an` the open subset `U(ℂ)` of `X^an`;
- that XII 1.1 builds `X^an` by gluing analytic subspaces of `ℂ^k` (or by the universal property, which gives
  the same).

**Proposed rows for `docs/research/locators.md`** (not added; the file belongs to other tasks):
- `SGA1_XII_3_3a`: SGA 1, Exp. XII, Rem. 3.3(a), p. 325. Topological part; special case `U → 𝔸ⁿ`, `U` affine.
  UNVERIFIED.
- `SGA1_XII_2_4`: SGA 1, Exp. XII, Prop. 2.4, "only if"; `PreconnectedSpace` on both sides. UNVERIFIED.
- `SGA1_XII_4_4`: SGA 1, Exp. XII, Thm. 4.4 and its corollary (`X` proper), and Serre GAGA (1956). Special case:
  abelian varieties, surjectivity only, reduced spaces. UNVERIFIED.

## 4. `#discharges` (VERIFIED)

`lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` (12,994 jobs, no rebuild) was run. Then
`lake env lean scratch/sga1-fix/DischargesCheck.lean`; the full output is in `scratch/sga1-fix/discharges.txt`:

```
DISCHARGES [OpenTextbookLeaves11.gagaMorphism] by SGA1Printed.gagaMorphism_of_printed
  still assumes: [UnifPrinted.MumfordComplexTorus,
 SGA1Printed.SGA1_XII_3_3a,
 UnifTopology.ProperCompactAn,
 SGA1Printed.SGA1_XII_2_4,
 SGA1Printed.SGA1_XII_4_4]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenTextbookLeaves11.uniformizationLeafAll] by SGA1Printed.uniformizationLeafAll_of_printed
  still assumes: [UnifPrinted.MumfordComplexTorus,
 SGA1Printed.SGA1_XII_3_3a,
 UnifTopology.ProperCompactAn,
 SGA1Printed.SGA1_XII_2_4]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 63 open hypotheses, 1976 theorems checked, 17 discharge one
```

The output also lists the rows of the imported contributions (unif-printed, unif-topology, sga1-etale,
gaga-chart and others). `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of:
`uniformizationLeafAll_of_printed`, `gagaMorphism_of_printed`, `regular_half`,
`exists_analytic_of_standardEtale`, `sga1_XII_3_1_Etale_of_3_3a`, `connectedPreconnectedAn_of_2_4`,
`contMDiffAt_iff_anFunAt`, `contMDiff_iff_isAnMorphism`, `anFunAt_iff_etale`, `isAnStr_of_3_3a` and
`gagaChart_iff_printed`.

## 5. Autofold spec (VERIFIED dry run)

`scratch/sga1-fix/autofold.json` discharges two fields of the textbook bundle:

```
uniformizationLeafAll := _root_.SGA1Printed.uniformizationLeafAll_of_printed {n}.mumfordComplexTorus
  {n}.sga1_XII_3_3a {n}.properCompactAn {n}.sga1_XII_2_4
gagaMorphism := _root_.SGA1Printed.gagaMorphism_of_printed {n}.mumfordComplexTorus {n}.sga1_XII_3_3a
  {n}.properCompactAn {n}.sga1_XII_2_4 {n}.sga1_XII_4_4
```

It adds five leaves, each with kind `published` and flag `unread: new printed leaf, no reading recorded; locator
UNVERIFIED`: `mumfordComplexTorus`, `sga1_XII_3_3a`, `properCompactAn`, `sga1_XII_2_4` and `sga1_XII_4_4`. The
import is `ZInQKernel.Contrib.OneProof.SGA1Printed`.

`python3 scripts/one_proof/autofold.py scratch/sga1-fix/autofold.json --dry-run` exits 0 and prints "strict
count: 46/10 on 56 -> 49/10 on 59; strictest 45/11 -> 48/11". The re-rating simulation went as follows:
- `kinds.tsv` was edited temporarily, setting the two rows to `consequence`/GLUE/GLUE as on `wip/leaf-fold32`;
- the dry run printed "44/12 on 56 -> 49/10 on 59; strictest 43/13 -> 48/11";
- the file was then restored.

The dry-run module minus its first line is `scratch/sga1-fix/FoldDryRun.lean`. It compiles, and
`HDec.HSyn.sixContactMin_of_open30` has standard axioms.

**Fold order.** This spec **replaces** sga1-etale's and gaga-chart's specs: fold this one instead of them. If
either of those lands first, the order matters:
- **sga1-etale first:** `uniformizationLeafAll` is gone, and `sga1_XII_3_1_Etale` and `connectedPreconnectedAn`
  are in the bundle. Discharge those two fields with `sga1_XII_3_1_Etale_of_3_3a {n}.sga1_XII_3_3a` and
  `connectedPreconnectedAn_of_2_4 {n}.sga1_XII_2_4`.
- **gaga-chart first:** discharge `gagaChart` with `gagaChart_of_printed {n}.sga1_XII_4_4`.

## 6. What remains

- Statement checks of the three new leaves against SGA 1 XII (§3). None of the SGA 1 or GAGA numbers has been
  read by this task.
- The locator rows (§3) and the fold.
- Not attempted: a Lean notion of complex analytic space (ringed space). `AnFunAt`/`IsAnMorphism` are the
  function-level form for reduced spaces, which is all the consumers need.

## 7. Files

- `ZInQKernel/Contrib/OneProof/SGA1Printed.lean`: the contribution.
- `scratch/sga1-fix/`:
  - `A.lean`: implicit functions;
  - `B.lean`: the regular half and the leaves 3.3(a) and 2.4;
  - `C.lean`: the structure sheaf, `IsAnMorphism`, GAGA, with `#print axioms`;
  - `DischargesCheck.lean` with `discharges.txt`, `autofold.json`, `autofold-dryrun.txt`, `FoldDryRun.lean`;
  - `log.md`.
- Build note: the build tree was copied (`cp -r`, both `.lake/build` and `lean/.lake/build`) from
  `~/dzq-wt/gaga-chart`, which is at the same commit as this base.
