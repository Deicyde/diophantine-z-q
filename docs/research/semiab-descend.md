# semiab-descend: `SemiAbelianDescendsPerfect` reduced to Chevalley's theorem over a perfect field

Task semiab-descend, 2026-11-16/17. Base: wip/height-fix 49e6d97d, with origin/main (merge 530ef0e7) and
origin/wip/leaf-fold32b (merge de506e7e) merged. Model work only; no human has reviewed it. There is no network
here, so every theorem number below is recalled and marked UNVERIFIED.

Marks: **VERIFIED** (compiled, or read in a file), **STANDARD** (published, with a reference), **SPECULATIVE**
(my argument), **UNVERIFIED** (a theorem number recalled from memory).

## 1. Result

**height-fix's last glue Prop, `ZInQ.HeightFix.SemiAbelianDescendsPerfect`, is proved in Lean, statement
unchanged and for every perfect field, from one new published leaf, `ChevalleyPerfect`. That is Chevalley's
structure theorem over a perfect field, existence and uniqueness.** Everything else in the descent is proved
(VERIFIED: compiled, standard axioms, §6).

```lean
theorem ZInQ.SemiAbDescend.semiAbelianDescendsPerfect_of_chevalley (hC : ChevalleyPerfect) :
    ZInQ.HeightFix.SemiAbelianDescendsPerfect
theorem ZInQ.SemiAbDescend.bostLowerBound_of_printed_chevalley (hB : BostLowerBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll) (hMT : AvSplit.MumfordTorsionAlgClosed)
    (hC : ChevalleyPerfect) : ZInQ.HeightSplit.BostLowerBound
theorem ZInQ.SemiAbDescend.gaudronRemondThm14_of_printed_chevalley (hGR : GaudronRemondThm14Printed)
    (hUL : …) (hMT : …) (hC : ChevalleyPerfect) : ZInQ.HeightSplit.GaudronRemondThm14
```

The file is `ZInQKernel/Contrib/OneProof/SemiAbelianDescendsPerfect.lean` (namespace `ZInQ.SemiAbDescend`). It
imports `PrintedStableHeight` (where the statement is defined), `GeomConnOfRationalPoint` (Stacks 04KV, already
proved in the tree) and `ZInQKernel.OneProof.H.TailZ19` (for `idCompSet` and the `OpenSub` construction of an open
subgroup scheme). It does not import `Main`.

**Fields covered.** The proof covers **every perfect field**, so it is the full Prop. The only place the Prop is
applied is `isSemistableRes_of_geom` (`PrintedStableHeight.lean`). It applies it at `k = 𝔭.ResidueField`, for
maximal ideals `𝔭` of `𝓞_L`; these are finite fields, perfect by `perfectField_residueField`. All the other
mentions take the Prop as a hypothesis: `isPrintedStableHeight_of`, `isPrintedStableHeight_iff`,
`bostLowerBound_of_printed`, `gaudronRemondThm14_of_printed`, `javanpeykarBound_of_printed` and
`pazukiCor13Upper_of_printed` (VERIFIED: grep). So every use is covered. Finiteness of the residue fields is not
needed.

**Count.** The target was the height-fix fold at −2 GLUE against the re-rated base, where `bostLowerBound` and
`gaudronRemondThm14` are both GLUE in `docs/one-proof/kinds.tsv`. The combined fold
(`scratch/semiab-descend/autofold.json`) does three things:
- it replaces those two GLUE rows by height-fix's printed leaves `bostLowerBoundPrinted` and
  `gaudronRemondThm14Printed`;
- it adds the published leaf `chevalleyPerfect`;
- it adds no glue.

So the result is −2 GLUE, provided `chevalleyPerfect` is accepted as printed form (§4). The dry run is in §6.

## 2. The statement (VERIFIED: copied verbatim, `scratch/semiab-descend/Statements.lean` checks it by `rfl`)

```lean
def SemiAbelianDescendsPerfect : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom],
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj G) := Functor.grpObjObj
    HasSemiAbelianIdentityComponent ((Over.pullback (sφ (φbar k))).obj G) →
      HasSemiAbelianIdCompTorus G
```

The hypothesis is the kernel's definition (TailY), over `k̄`:
- there is an open connected subgroup `U' ⊆ G_{k̄}`;
- there is a faithfully flat homomorphism `π' : U' → B'` onto an abelian variety;
- `ker π'` is a split torus in the functor of points: `(Rˣ)^r ≅ ker(U'(R) → B'(R))`, naturally in `k̄`-algebras.

The conclusion is dict-models' general-torus form over `k`. No falsity, vacuity or inertness was found. The Prop
is true (STANDARD, §3), and the Lean proof confirms it given the leaf.

## 3. The proof (all VERIFIED, compiled)

| § | Lean | content |
| --- | --- | --- |
| 1 | `isIso_of_bijective_affine` | Yoneda on affine test schemes: a morphism over `S` that is bijective on `T`-points for every affine `T` is an isomorphism (gluing over an affine open cover) |
| 2 | `exists_algPtMap`, `exists_iso_algPt`, `bijective_affine_of_algPt` | affine `K`-schemes are `Spec` of `K`-algebras; morphisms between them are `Spec` of algebra maps |
| 3-4 | `isSmoothConnAffineKer_of_torus` | a kernel that is a split torus in the functor of points is `Spec K[x₁^{±1},…,x_r^{±1}]`, so it is smooth, connected and affine |
| 5 | `isPullback_shear`, `smooth_of_smoothKer` | a faithfully flat quasi-compact homomorphism with smooth kernel onto a smooth group has smooth source: the shear square `U × ker π ⇉ U` is a pullback of `π` along `π`, and Mathlib's `DescendsAlong @Smooth (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` applies |
| 6 | `isClosed_range_openSubgroup` | over an algebraically closed field, an open subgroup scheme of a group locally of finite type is closed. A closed point outside it is a `K`-point `s` (`pointOfClosedPoint`), and `s·U` is an open neighbourhood that misses `U`: otherwise it would meet `U` in a `K`-point, and then `s ∈ U(K)`. Closed points are dense in closed sets (Jacobson) |
| 7 | `isOpen_idCompSet`, `isSubgroupOpen_W0`, `connectedSpace_W0` | the identity component of a group of finite type over a field is an open, connected subgroup. Openness: noetherian space. Closure under the group law: TailZ19's argument, with 04KV; it needs flatness over the field, not smoothness |
| 8 | `isSmoothConnAffineKer_bc` | a smooth connected affine kernel stays so after a field extension: `Over.pullback` preserves the kernel square; connectedness comes from 04KV |
| 9 | `semiAbelianDescendsPerfect_of_chevalley` | the assembly below |

The assembly, for `G` over a perfect field `k` with the data `(U', π', B', e')` over `k̄`:

1. `U := G⁰` over `k` (§7), with its group structure as an open subgroup.
2. `U'` and `(G⁰)_{k̄}` have the same image in `G_{k̄}`.
   - The image of `(G⁰)_{k̄}` is `p⁻¹(G⁰)`. It is clopen, and it is connected by 04KV.
   - `U'` is connected, so it lies in `p⁻¹(G⁰)`.
   - `U'` is clopen (§6), so it contains `p⁻¹(G⁰)`.

   This gives an isomorphism of groups `φU : (G⁰)_{k̄} ≅ U'`.
3. `U'` is smooth: its kernel is smooth (§3-4) and §5 applies. So `(G⁰)_{k̄}` is smooth, and `G⁰` is smooth
   (Mathlib's flat descent along `Spec k̄ → Spec k`).
4. Chevalley over `k` (leaf, existence) gives `π : G⁰ → B` with smooth connected affine kernel.
5. Over `k̄` there are two Chevalley presentations of `(G⁰)_{k̄}`:
   - `π_{k̄}`, whose kernel is smooth, connected and affine by §8;
   - `φU ≫ π'`, whose kernel is a split torus, so smooth, connected and affine by §3-4.

   The leaf's uniqueness clause gives them the same kernel on all points.
6. The torus data `e'`, transported by `φU` and the adjunction bijection `Φ` of `RaynaudSemistableOr`, is the
   required `e` over `k`. Injectivity, the kernel condition and naturality follow.

## 4. The new leaf and its rating

`ZInQ.SemiAbDescend.ChevalleyPerfect` (in the new file, §9):

```lean
def ChevalleyPerfect : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G],
    Smooth G.hom → QuasiCompact G.hom → ConnectedSpace G.left →
    (∃ (B : PkgI3.AbVar k) (π : G ⟶ B.X), IsChevalleyQuotient B π) ∧
    ∀ (B₁ B₂ : PkgI3.AbVar k) (π₁ : G ⟶ B₁.X) (π₂ : G ⟶ B₂.X),
      IsChevalleyQuotient B₁ π₁ → IsChevalleyQuotient B₂ π₂ →
      ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G), x ≫ π₁ = 1 ↔ x ≫ π₂ = 1
```

Here `IsChevalleyQuotient B π` says that `π` is a homomorphism, flat and surjective, and that its scheme-theoretic
kernel `kerObj π = pullback π η[B]` is smooth, connected and affine (`Smooth`, `IsAffine`, `ConnectedSpace`). All
definitions are genuine: Mathlib's morphism properties, the kernel as a fibre product, and `PkgI3.AbVar` (a
proper, smooth, geometrically integral group scheme).

- **Source.** Chevalley's structure theorem over a perfect field: B. Conrad, "A modern proof of Chevalley's
  theorem on algebraic groups", J. Ramanujan Math. Soc. 17 (2002), 1-18, Thm. 1.1; J. S. Milne, *Algebraic
  Groups* (CUP 2017), Thm. 8.27; originally Chevalley (1960) and Rosenlicht (1956). The numbers are UNVERIFIED,
  recalled without network. As recalled, the print says: a smooth connected group scheme `G` of finite type over a
  perfect field has a unique normal smooth connected affine subgroup `H` such that `G/H` is an abelian variety.
- **Rating: printed form**, flagged "locator UNVERIFIED".
  - The existence clause is the existence half of the print. The uniqueness clause is the uniqueness half, stated
    on points: `ker π₁ = H₁ = H₂ = ker π₂`.
  - The one translation is reading "`G/H` is an abelian variety" as "there is a faithfully flat homomorphism from
    `G` onto an abelian variety with kernel `H`". That is the definition of the quotient: a quotient map is a
    faithfully flat homomorphism, and its target is `G/ker` (Milne, *Algebraic Groups*, §5.c; SGA 3 VI_A
    3.2-5.4; UNVERIFIED numbers).
  - Over the finite-type hypotheses, `π` is locally of finite presentation. So a flat surjective `π` is an fppf
    epimorphism and identifies `B` with `G/ker π`.
  - The leaf is never stronger than the print. Commutativity of `G` is not assumed, as Chevalley does not need it.
  - If a reviewer counts the quotient dictionary as a step, the rating becomes "consequence"; it is not a stronger
    statement.
- **Truth.** True as stated (STANDARD).
- **Not vacuous.** The kernel is the genuine fibre product, `B` a genuine abelian variety, and `G` ranges over all
  smooth connected group schemes of finite type.
- **Use.**
  - Existence is used over the residue field `k` (for the application, a finite field).
  - Uniqueness is used over `k̄ = AlgebraicClosure k`, to compare the Chevalley presentation from `k` with the given
    torus presentation.
  - No other leaf is used. In particular, no rigidity statement of the form "homomorphisms from affine groups to
    abelian varieties are trivial" is needed: uniqueness does that work.

A smaller printed statement would be SGA 7 IX §2's remark that semi-abelianness can be tested over `k̄`, if it is
printed (UNVERIFIED, as height-fix noted). Here it is not needed: the remark's content is proved, from Chevalley.

## 5. What this does not cover

- `UnipotentForward.SemiAbelianDescendsSepClosed` (separably closed, possibly imperfect residue fields, split-torus
  conclusion) is a different Prop. It is used only on unipotent-b's reading-robust path. The present argument needs
  a perfect field for Chevalley's theorem, and the split-torus conclusion would also need Galois descent of the
  characters.
- The reading R4 of height-fix (fibre of the global Néron model versus the local one) is unchanged.

## 6. Checks (VERIFIED on this host)

- `lake build ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect` succeeds (12787 jobs). The development copy
  `scratch/semiab-descend/A.lean` compiles with `lake env lean` in about 20 s, and
  `#print axioms semiAbelianDescendsPerfect_of_chevalley` = `[propext, Classical.choice, Quot.sound]`.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect`
  succeeds.
- `#discharges` (`scratch/semiab-descend/Discharges.lean`, output in `discharges.txt`):

  ```
  DISCHARGES [OpenResearchLeaves28.bostLowerBound] by ZInQ.SemiAbDescend.bostLowerBound_of_printed_chevalley
    still assumes: [ZInQ.HeightFix.BostLowerBoundPrinted,
   BPAnalytic.Uniformization.UniformizationLeafAll,
   AvSplit.MumfordTorsionAlgClosed,
   ZInQ.SemiAbDescend.ChevalleyPerfect]
    axioms: [propext, Classical.choice, Quot.sound]
  DISCHARGES [OpenResearchLeaves28.gaudronRemondThm14] by ZInQ.SemiAbDescend.gaudronRemondThm14_of_printed_chevalley
    still assumes: [ZInQ.HeightFix.GaudronRemondThm14Printed,
   BPAnalytic.Uniformization.UniformizationLeafAll,
   AvSplit.MumfordTorsionAlgClosed,
   ZInQ.SemiAbDescend.ChevalleyPerfect]
    axioms: [propext, Classical.choice, Quot.sound]
  ```

  The optional `javanpeykarBound` and `pazukiCor13Upper` are discharged likewise, by
  `javanpeykarBound_of_printed_chevalley` and `pazukiCor13Upper_of_printed_chevalley`. The full output ends
  "45 open hypotheses, 6883 theorems checked, 27 discharge one". The count includes other contributions in the
  build.
  - `UniformizationLeafAll` is proved on this base (`_root_.uniformizationLeafAll_proof`), so it is not a new
    assumption.
  - `MumfordTorsionAlgClosed` is a textbook field.
  - The printed leaves are height-fix's.
  - `ChevalleyPerfect` is the only new leaf.
- `scratch/semiab-descend/Statements.lean`: verbatim copies of `SemiAbelianDescendsPerfect`,
  `HasSemiAbelianIdCompTorus` and `HasSemiAbelianIdentityComponent` equal the originals by `rfl`.
- **Autofold.**
  - **Combined spec** (`scratch/semiab-descend/autofold.json`, height-fix's fold with the glue replaced by
    `chevalleyPerfect`).
    - It discharges `bostLowerBound` and `gaudronRemondThm14` and adds the leaves `bostLowerBoundPrinted`,
      `chevalleyPerfect` (both published, flag "locator UNVERIFIED (see the source)") and
      `gaudronRemondThm14Printed` (published, no flag).
    - Change from height-fix's spec: on this base `uniformizationLeafAll` is no longer a textbook field, so
      `{t}.uniformizationLeafAll` does not compile. The spec uses `_root_.uniformizationLeafAll_proof` and imports
      `ZInQKernel.Contrib.OneProof.UniformizationLeafAll`.
  - **Dry run** (`autofold-dryrun.txt`): `strict count: 16/21 on 37 -> 19/19 on 38; strictest 16/21 -> 19/19`,
    i.e. **−2 GLUE**, accepted without `--allow-rise`.
    - The printed module (`FoldDryRun.lean`, output minus line 1) compiles (`FoldDryRunCheck.lean`).
    - `HDec.HSyn.sixContactMin_of_open39` has the standard axioms.
  - **If height-fix is folded first** (with `semiAbelianDescendsPerfect` as a field),
    `scratch/semiab-descend/autofold-after-height-fix.json` discharges that field by
    `semiAbelianDescendsPerfect_of_chevalley {n}.chevalleyPerfect`. On the present base it is correctly refused:
    the field does not exist yet.
  - The fold itself was not run: `ZInQKernel/OneProof/` is not this task's to edit.
