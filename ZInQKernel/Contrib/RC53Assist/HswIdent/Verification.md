# Coefficient and trace identifications of the residual switch: verification report


## Note after independent review (2026-11-18)

An independent review approved the identifications with notes. The declaration census is 60 named declarations plus 7 instances. `ReciprocityAt` is an arithmetic, non-circular input and is not proved here.

Compiled contribution for the six identifications `eT`, `eM₂`, `hWeil`, `eμ`, `heμ`, `hmatch` taken by the residual bridge `derivSwitch_switchCoordinates_tame_of_Milne` (module `ZInQKernel.Contrib.RC53Assist.HswResidual.Residual`), constructed for the genuine residual objects. Single module: `ZInQKernel.Contrib.RC53Assist.HswIdent.Identifications`.

## The genuine objects

* Coefficient module: `ETwo K S W = E(K_S)[2]`, the `2`-torsion of the points of the elliptic curve `W` with coordinates in `K_S` (the existing `TorsS K S W 2`, `G_{K,S}` acting on coordinates), packaged as a discrete `F_2[G_{K,S}]`-module. Continuity of the action is the existing `isOpen_stabilizer_torsS`. The same is done for the actual residual module `ResidualM W j α = F_2 ⊗_{A_{j+1}} M_{j+1}`, through the existing equivariant identification `residualEquiv` with `E(K_S)[2]` (`residualToETwo`).
* Target: `MuTwo K S = F_2` with the trivial `G_{K,S}`-action. This is `μ_2 = F_2(1)`: `μ_2 = {±1} ⊂ K`, so the Galois action is trivial. It is the cyclotomic twist of the Selmer-duality statements (`isCyclotomicTwist_muTwo`, from the existing `isCyclotomicTwist_example`), and it is identified with the square roots of unity of `K_S` by `muTwoRoots` (`1 ↦ -1`, `muTwoRoots_one`), equivariantly for the Galois action on roots of unity (`muTwoRoots_smul`).
* Pairing: `weilTwo K S W`, the Weil pairing `e_2` of the vendored Tau Ceti construction (Silverman III.8.1) on `E(K_S)[2]`, read in `F_2` (the existing `weilS`, whose discrete logarithm on `μ_2` is the unique isomorphism), made `F_2`-bilinear. It is equivariant (`weilTwo_smul`: `e_2` transforms by the cyclotomic character, trivial modulo `2`), alternating (`weilTwo_self`), and nondegenerate under the existing hypothesis `FullTorsion K S W 2` (`weilTwo_nondegenerate`). This is the pairing of the manuscript's Lemma `ex:arith-conjugate-duality` (tex 2798).

## The six identifications

| input of the bridge | supplied by | status |
|---|---|---|
| `eT : T_q ≃ₗ F_2` | `eTq K S q` | defined (the restricted module is `F_2`) |
| `eM₂` | `eM` itself (the given tame coordinates) | no new datum |
| `hWeil` | `weilTwo_hWeil hW q eM` | proved, for every coordinate system `eM` |
| `eμ : T_q ≃+ μ_2(K_q^sep)` | `eMuq K S q` | defined; `eMuq_one`: `1 ↦ -1` |
| `heμ` | `heMuq K S q` | proved (both actions trivial; `-1 ∈ K_q`) |
| `hmatch` | `hmatch_genuine` / `hmatch_of_reciprocity` | proved from `InducesIsoH3 tr`, `ReciprocityAt`, and the A23 input |

The bridge's `htrivT` is `locMap_smul_muTwo q` (proved). When `G_{K,S}` fixes `E(K_S)[2]` (tex 4479–4480), the consumer's polarization `γ`, `hγ`, `hpol` are supplied by `weilTwo_polarization` and its local triviality `htriv` by restriction.

The linear algebra behind `hWeil`: over `F_2` the alternating forms on a two-dimensional space form a line, so a nonzero alternating pairing into a line is the determinant form `weil` in every coordinate system (`alternating_eq_weil`, `alternating_eq_weil_of_nondegenerate`). For the conjugate pairing `(x, y) ↦ e_2(x, J y)` (tex 2818, 4889–4890, 5035–5036) the second coordinates are `J ≫ eM` (`weilTwo_hWeil_conj`); the tame consumer requires a polarized, hence alternating, pairing, which over `F_2` is `e_2` itself.

### How they plug in

`derivSwitch_switchCoordinates_tame_genuine` is the term

```text
derivSwitch_switchCoordinates_tame_of_Milne F hR hMilne φ σ eM Tc hIur (weilTwo K S W) γ
  (weilTwo_smul K S W) hγ hpol Iso tr htr hUS2 hε hJ2 htriv (locMap_smul_muTwo q)
  (eTq K S q) eM (weilTwo_hWeil hW q eM) hKB (eMuq K S q) (heMuq K S q)
  (hmatch_of_reciprocity _ (weilTwo K S W) (weilTwo_smul K S W) Iso tr htr htr3 q hrec hKB
    (eMuq K S q) (heMuq K S q))
```

with conclusion literally that of the bridge for `M = E(K_S)[2]`, `T = μ_2`, `β = e_2`. Specializations:

* `derivSwitch_switchCoordinates_tame_genuine_rational`: `G_{K,S}` fixes `E(K_S)[2]`; `γ`, `hγ`, `hpol`, `htriv` derived.
* `derivSwitch_switchCoordinates_tame_curveEll`: the manuscript's curve `E_ℓ : y^2 = x (x - ℓ) (x + 3 ℓ)` (tex 1763–1766, full rational two-torsion, `ℓ ≠ 0`); `FullTorsion` (existing `fullTorsion_two_curveEll`) and the trivial action (existing `smul_torsTwo_cubicCurve`) are proved, so no coefficient hypothesis is left.
* `derivSwitch_switchCoordinates_tame_residualM`: the actual residual module `F_2 ⊗_{A_{j+1}} M_{j+1}` with the transported Weil pairing `weilResidual` (`weilResidual_hWeil`, `weilResidual_smul`, `weilResidual_polarization`); the continuity instance is the existing `continuousSMul_residualM`.

## The trace matching

`LocalTraceMatchesInvariant eμ heμ tr_q` (for `tr_q = residualTraceAt X β hβ Iso tr q`) depends on the cone trace `tr`, an input of the consumer. With the project's convention for the genuine trace, `InducesIsoH3 tr` (as in `NekovarProp543`; existence is the printed `NekovarProp541`):

1. `localTraceMatchesInvariant_of_inducesIsoH2`: given the A23 comparison, a local trace killing coboundaries matches the Brauer invariant as soon as it induces `H^2(K_q, T) ≅ F_2`. Over `F_2` the normalization `1 ↦ 1/2` is automatic: on a coboundary both sides vanish; otherwise the trace is `1` and the invariant is a nonzero two-torsion element of `Q/Z`, hence `1/2` (`addCircle_two_torsion`). Together with the existing `inducesIsoH2_of_KummerBrauer`, `hmatch ↔ InducesIsoH2 tr_q`.
2. `inducesIsoH2_residualTraceAt`: `InducesIsoH3 tr`, `ReciprocityAt K S T q`, and one non-coboundary local two-cocycle (`exists_kerToH2_ne_zero`, from the A23 surjectivity and `Br K_q ≅ Q/Z`) give `InducesIsoH2 tr_q`. A local cocycle `z` with `tr(0, z) = 0` is a cone coboundary `d(e, y)`; `e` is a global cocycle that is a local coboundary away from `q`, so by reciprocity it is one at `q`, and then so is `z`.
3. `reciprocityAt_of_inducesIsoH2`: conversely `InducesIsoH2 tr_q` implies `ReciprocityAt`. Hence `hmatch_iff_reciprocityAt`, `hmatch_genuine_iff`: for a trace killing cone coboundaries and inducing `H^3_c ≅ F_2`, `hmatch` is equivalent to `ReciprocityAt`. Nothing weaker than reciprocity at `q` can supply `hmatch`.

`ReciprocityAt K S T q`: every continuous two-cocycle `e` of `G_{K,S}` with values in `T` whose restriction `res_v e` is a coboundary at every place `v ∈ S`, `v ≠ q`, has `res_q e` a coboundary (stated on the genuine complexes `globalCx`, `localCx`, `resS`).

## What remains open

* `ReciprocityAt K S μ_2 q` (new explicit input, not proved). It is the reciprocity law for `H^2(G_{K,S}, μ_2)`: by Hasse's sum formula — proved in the vendored Tau Ceti library as `TauCeti.ClassFieldTheory.sumLocalInv_brLocalization_eq_zero` — the local invariants of a global Brauer class sum to zero; a class inflated from `G_{K,S}` has no invariant at a finite place outside `S` (its restriction factors through `Gal(K_v^ur/K_v) ≅ Ẑ`, whose `H^2` with finite coefficients vanishes) and none at a complex place. It holds for totally complex `K`, as in the manuscript (tex 2839: `K` imaginary quadratic; tex 4584: no real places). It is false when `K` has a real place: over `Q` with `S = {2}` the class of the quaternion algebra `(-1, -1)` lies in `H^2(G_{Q,S}, μ_2)` and is nonzero at `2`. Missing for its derivation from the sum formula: (a) inflation from `G_{K,S}` to the absolute Galois group and from `μ_2` to the units of the separable closure; (b) the comparison of `locMap` (`Field.absoluteGaloisGroup.map` followed by restriction to `K_S`) with the localizations of `brLocalization`: Tau Ceti proves that base change does not depend on the embedding of separable closures (`TauCeti.ClassFieldTheory.brBaseChange_apply`, via the triviality of inner automorphisms on `H^2`), so what is missing is an embedding compatible with `locMap` and the transport between `Field.absoluteGaloisGroup` and `TauCeti.AbsoluteGaloisGroup`; (c) the vanishing at finite places outside `S`, either through the factorization `UnramifiedAtFactorization` (stated, not proved, in the tree) and `H^2(Ẑ, F_2) = 0`, or through Tau Ceti's vanishing of unramified inflated classes (used in its proof that local invariants have finite support) together with a comparison of the tree's `IsUnramifiedOutside` with `Algebra.IsUnramifiedAt`; (d) the vanishing at the complex places. For finite `S` containing the places above `2` it is a part of the Poitou–Tate sequence (Milne, Arithmetic Duality Theorems, I.4.10, cited at tex 4526); that locator was not checked against the printed text, and no print was added.
* `KummerBrauerComparisonF2 K_q` (A23, another lane, kept as input as instructed).
* `MilneCor23Residual` (the printed input of the bridge, unchanged).
* `InducesIsoH3 tr` (the genuine-trace convention; existence is `NekovarProp541`).
* `FullTorsion K S W 2` for a general curve (existing Néron–Ogg–Shafarevich hypothesis; proved for `E_ℓ`), and global triviality of the action in the rational specializations (proved for `E_ℓ`).
* The unrelated switch inputs of the consumer: derivative family and `RelAt`, tame coordinates and the inertia containment, isotropy data, cone-trace coboundary vanishing, strict degree-two vanishing, the nonzero scalar and the involutive matrix.

No assertion is made about characteristic-zero coefficient fibres or the full theorem.

## Verification

* Lean 4.35.0, release, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Source base: integration head `27579f4a1`.
* The module build had completed (11274 jobs) before the first single-file compilation.
* The prescribed single-file invocation was used (six threads, processor affinity 112–127, priority adjustment 10). Final compilation: exit 0, no errors, no warnings. Imports: `ZInQKernel.Contrib.RC53Assist.HswResidual.Residual`, `ZInQKernel.Contrib.OneProof.RC.CoefModules.Weil`, `ZInQKernel.Contrib.CloudB3RC53.GenuineInst.CoefResidualCounts` (all built).
* All 60 declarations of the module were checked individually; every axiom report is exactly `propext`, `Classical.choice`, `Quot.sound`.
* Source restrictions checked: no proof gaps, new axiom declarations, kernel bypasses, custom parsing extensions, evaluation or inspection commands, forbidden phrases, private identifiers or filesystem paths; heartbeat limit 800000; no existing file edited.
* Construction failures during development (rewrites through type synonyms not type-correct at reducible transparency, a heartbeat timeout from comparing two presentations of the same cochain map, an unbound section variable) were repaired; only the final successful check is credited.

`Verification.txt` is the raw output of the final check run (the module, compiled with a type query and an axiom query for each of its 60 declarations; the queries are not part of the module). The standard pretty printer elides proof terms as `⋯`. Digests:

* `Identifications.lean`: 63738 bytes; SHA-256 `e1f2bc5e0eea2154cf135021b1e9c38390e3943a2979f98ccff40dc952948de0`.
* `Verification.txt`: 75350 bytes; SHA-256 `5b58c5415fe9d8c4acb4e03a292fd7fe41f061a2961c48f6c1d87b4b5038720d`.

## Principal statements and axiom reports

### `alternating_eq_weil`

```lean
@alternating_eq_weil : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module (ZMod 2) V] {T : Type}
  [inst_2 : AddCommGroup T] [inst_3 : Module (ZMod 2) T] (e : V ≃ₗ[ZMod 2] Fin 2 → ZMod 2) (eT : T ≃ₗ[ZMod 2] ZMod 2)
  (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] T),
  (∀ (x : V), (B x) x = 0) →
    (∃ x y, (B x) y ≠ 0) → ∀ (x y : V), eT ((B x) y) = (ZInQ.Manuscript.RC.Uniform.weil (e x)) (e y)
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.alternating_eq_weil' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `alternating_eq_weil_of_nondegenerate`

```lean
@alternating_eq_weil_of_nondegenerate : ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : Module (ZMod 2) V] {T : Type}
  [inst_2 : AddCommGroup T] [inst_3 : Module (ZMod 2) T] (e : V ≃ₗ[ZMod 2] Fin 2 → ZMod 2) (eT : T ≃ₗ[ZMod 2] ZMod 2)
  (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] T),
  (∀ (x : V), (B x) x = 0) →
    (∀ (x : V), (∀ (y : V), (B x) y = 0) → x = 0) →
      ∀ (x y : V), eT ((B x) y) = (ZInQ.Manuscript.RC.Uniform.weil (e x)) (e y)
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.alternating_eq_weil_of_nondegenerate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ETwo`

```lean
ETwo : (K : Type) →
  [inst : Field K] → Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) → WeierstrassCurve K → Type
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.ETwo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `MuTwo`

```lean
MuTwo : (K : Type) → [inst : Field K] → Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) → Type
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.MuTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `isCyclotomicTwist_muTwo`

```lean
isCyclotomicTwist_muTwo : ∀ (K : Type) [inst : Field K] [NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  ZInQ.Manuscript.RC.SelmerComplex.IsCyclotomicTwist K S (ZMod 2) (MuTwo K S)
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.isCyclotomicTwist_muTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `muTwoRoots`

```lean
muTwoRoots : (K : Type) →
  [inst : Field K] →
    [NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        MuTwo K S ≃+ Additive ↥(rootsOfUnity 2 (ZInQ.Manuscript.RC.CoefModules.KS K S))
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.muTwoRoots' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `muTwoRoots_smul`

```lean
muTwoRoots_smul : ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (σ : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (t : MuTwo K S),
  (muTwoRoots K S) (σ • t) =
    Additive.ofMul
      ((restrictRootsOfUnity (ZInQ.Manuscript.RC.CoefModules.galS K S σ) 2) (Additive.toMul ((muTwoRoots K S) t)))
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.muTwoRoots_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `muTwoRoots_one`

```lean
muTwoRoots_one : ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
  ↑(Additive.toMul
        ((muTwoRoots K S)
          (have this := 1;
          this))) =
    -1
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.muTwoRoots_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilTwo`

```lean
weilTwo : (K : Type) →
  [inst : Field K] →
    [NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        (W : WeierstrassCurve K) → [W.IsElliptic] → ETwo K S W →ₗ[ZMod 2] ETwo K S W →ₗ[ZMod 2] MuTwo K S
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilTwo_apply`

```lean
weilTwo_apply : ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (W : WeierstrassCurve K)
  [inst_2 : W.IsElliptic] (P Q : ETwo K S W), ((weilTwo K S W) P) Q = ((ZInQ.Manuscript.RC.CoefModules.weilS W ⋯) P) Q
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilTwo_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilTwo_smul`

```lean
weilTwo_smul : ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (W : WeierstrassCurve K)
  [inst_2 : W.IsElliptic] (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (P Q : ETwo K S W),
  ((weilTwo K S W) (g • P)) (g • Q) = g • ((weilTwo K S W) P) Q
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilTwo_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilTwo_self`

```lean
weilTwo_self : ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (W : WeierstrassCurve K)
  [inst_2 : W.IsElliptic] (P : ETwo K S W), ((weilTwo K S W) P) P = 0
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilTwo_self' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilTwo_nondegenerate`

```lean
@weilTwo_nondegenerate : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {W : WeierstrassCurve K}
  [inst_2 : W.IsElliptic],
  ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2 →
    ∀ (P : ETwo K S W), (∀ (Q : ETwo K S W), ((weilTwo K S W) P) Q = 0) → P = 0
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilTwo_nondegenerate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `eTq`

```lean
eTq : (K : Type) →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S) →
          ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q)
              (MuTwo K S) ≃ₗ[ZMod 2]
            ZMod 2
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.eTq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilTwo_hWeil`

```lean
@weilTwo_hWeil : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {W : WeierstrassCurve K}
  [inst_2 : W.IsElliptic],
  ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2 →
    ∀ (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
      (eM :
        ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) (ETwo K S W) ≃ₗ[ZMod 2]
          Fin 2 → ZMod 2)
      (x y : ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) (ETwo K S W)),
      (eTq K S q)
          (((ZInQ.Manuscript.RC.SelmerComplex.resPairing (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
                (weilTwo K S W) (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q))
              x)
            y) =
        (ZInQ.Manuscript.RC.Uniform.weil (eM x)) (eM y)
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilTwo_hWeil' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilTwo_hWeil_conj`

```lean
@weilTwo_hWeil_conj : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {W : WeierstrassCurve K}
  [inst_2 : W.IsElliptic],
  ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2 →
    ∀ (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
      (eM :
        ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) (ETwo K S W) ≃ₗ[ZMod 2]
          Fin 2 → ZMod 2)
      (J :
        ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) (ETwo K S W) ≃ₗ[ZMod 2]
          ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) (ETwo K S W))
      (x y : ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) (ETwo K S W)),
      (eTq K S q)
          (((ZInQ.Manuscript.RC.SelmerComplex.resPairing (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
                (weilTwo K S W) (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q))
              x)
            (J y)) =
        (ZInQ.Manuscript.RC.Uniform.weil (eM x)) ((J ≪≫ₗ eM) y)
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilTwo_hWeil_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilTwo_polarization`

```lean
@weilTwo_polarization : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {W : WeierstrassCurve K}
  [inst_2 : W.IsElliptic],
  ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2 →
    ∀ (e : ETwo K S W ≃ₗ[ZMod 2] Fin 2 → ZMod 2),
      (∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (P : ETwo K S W), g • P = P) →
        ∃ γ,
          (∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : ETwo K S W), (γ (g • x)) (g • y) = g • (γ x) y) ∧
            ∀ (x y : ETwo K S W), ((weilTwo K S W) x) y = (γ x) y - (γ y) x
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilTwo_polarization' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `eMuq`

```lean
eMuq : (K : Type) →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S) →
          ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) (MuTwo K S) ≃+
            TauCeti.KummerCoeff (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) 2
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.eMuq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `eMuq_one`

```lean
@eMuq_one : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S),
  ↑(Additive.toMul
        ((eMuq K S q)
          (have this := 1;
          this))) =
    -1
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.eMuq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `heMuq`

```lean
heMuq : ∀ (K : Type) [inst : Field K] [inst_1 : NumberField K]
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (g : TauCeti.AbsoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q))
  (t : ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) (MuTwo K S)),
  (eMuq K S q)
      ((TauCeti.absoluteGaloisGroupRestrictEquiv (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q)).symm g • t) =
    g • (eMuq K S q) t
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.heMuq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `locMap_smul_muTwo`

```lean
@locMap_smul_muTwo : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q) (m : MuTwo K S),
  (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) g • m = m
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.locMap_smul_muTwo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `addCircle_two_torsion`

```lean
addCircle_two_torsion : ∀ (x : AddCircle 1), 2 • x = 0 → x = 0 ∨ x = ↑(1 / 2)
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.addCircle_two_torsion' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `exists_kerToH2_ne_zero`

```lean
@exists_kerToH2_ne_zero : ∀ {L : Type} [inst : Field L] [inst_1 : CharZero L] [inst_2 : ValuativeRel L]
  [inst_3 : TopologicalSpace L] [IsNonarchimedeanLocalField L] {T : Type} [inst_5 : AddCommGroup T]
  [inst_6 : Module (ZMod 2) T] [inst_7 : DistribMulAction (Field.absoluteGaloisGroup L) T]
  [inst_8 : SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) T] [inst_9 : TopologicalSpace T]
  [inst_10 : DiscreteTopology T] [inst_11 : ContinuousSMul (Field.absoluteGaloisGroup L) T]
  (eμ : T ≃+ TauCeti.KummerCoeff L 2),
  (∀ (g : TauCeti.AbsoluteGaloisGroup L) (t : T),
      eμ ((TauCeti.absoluteGaloisGroupRestrictEquiv L).symm g • t) = g • eμ t) →
    ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2 L → ∃ c, ZInQ.Manuscript.RC.SelmerComplex.kerToH2 c ≠ 0
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.exists_kerToH2_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `localTraceMatchesInvariant_of_inducesIsoH2`

```lean
@localTraceMatchesInvariant_of_inducesIsoH2 : ∀ {L : Type} [inst : Field L] [inst_1 : CharZero L]
  [inst_2 : ValuativeRel L] [inst_3 : TopologicalSpace L] [inst_4 : IsNonarchimedeanLocalField L] {T : Type}
  [inst_5 : AddCommGroup T] [inst_6 : Module (ZMod 2) T] [inst_7 : DistribMulAction (Field.absoluteGaloisGroup L) T]
  [inst_8 : SMulCommClass (Field.absoluteGaloisGroup L) (ZMod 2) T] [inst_9 : TopologicalSpace T]
  [inst_10 : DiscreteTopology T] [inst_11 : ContinuousSMul (Field.absoluteGaloisGroup L) T]
  (eμ : T ≃+ TauCeti.KummerCoeff L 2)
  (heμ :
    ∀ (g : TauCeti.AbsoluteGaloisGroup L) (t : T),
      eμ ((TauCeti.absoluteGaloisGroupRestrictEquiv L).symm g • t) = g • eμ t),
  ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2 L →
    ∀
      (tr2 :
        ↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).X 2) →ₗ[ZMod 2]
          ZMod 2),
      (∀ (c : ↑((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).X 1)),
          tr2
              ((ModuleCat.Hom.hom
                  ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2) (Field.absoluteGaloisGroup L) T).d 1 2))
                c) =
            0) →
        ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH2 tr2 →
          ZInQ.Contrib.RC53Assist.HswResidual.LocalTraceMatchesInvariant eμ heμ tr2
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.localTraceMatchesInvariant_of_inducesIsoH2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ReciprocityAt`

```lean
ReciprocityAt : (K : Type) →
  [inst : Field K] →
    [NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        (T : Type) →
          [inst_2 : AddCommGroup T] →
            [inst_3 : Module (ZMod 2) T] →
              [inst_4 : DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T] →
                [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) T] →
                  [inst_6 : TopologicalSpace T] →
                    [DiscreteTopology T] →
                      [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T] →
                        ZInQ.Manuscript.RC.SelmerComplex.Places K S → Prop
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.ReciprocityAt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `inducesIsoH2_residualTraceAt`

```lean
@inducesIsoH2_residualTraceAt : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {M : Type} [inst_2 : AddCommGroup M]
  [inst_3 : Module (ZMod 2) M] [inst_4 : DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [inst_5 : SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) M] [inst_6 : TopologicalSpace M]
  [inst_7 : DiscreteTopology M] [inst_8 : ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [inst_9 : DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {T : Type} [inst_10 : AddCommGroup T]
  [inst_11 : Module (ZMod 2) T] [inst_12 : DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  [inst_13 : SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) T] [inst_14 : TopologicalSpace T]
  [inst_15 : DiscreteTopology T] [inst_16 : ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  (X : ZInQ.Manuscript.RC.SelmerComplex.GenuineSwitch K S (ZMod 2) M) (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
  (hβ : ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : M), (β (g • x)) (g • y) = g • (β x) y)
  (Iso : ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) β hβ X.ΔS X.ΔR)
  (tr :
    ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X
          3) →ₗ[ZMod 2]
      ZMod 2),
  ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH3 tr →
    ∀ (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S),
      ReciprocityAt K S T q →
        (∃ z,
            (ModuleCat.Hom.hom
                    ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2)
                          (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
                          (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q)
                            T)).d
                      2 3))
                  z =
                0 ∧
              ¬∃ y,
                  (ModuleCat.Hom.hom
                        ((ZInQ.Manuscript.RC.SelmerComplex.contCochains (ZMod 2)
                              (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
                              (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q)
                                T)).d
                          1 2))
                      y =
                    z) →
          ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH2
            (ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt X β hβ Iso tr q)
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.inducesIsoH2_residualTraceAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `hmatch_of_reciprocity`

```lean
@hmatch_of_reciprocity : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {M : Type} [inst_2 : AddCommGroup M]
  [inst_3 : Module (ZMod 2) M] [inst_4 : DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [inst_5 : SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) M] [inst_6 : TopologicalSpace M]
  [inst_7 : DiscreteTopology M] [inst_8 : ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [inst_9 : DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {T : Type} [inst_10 : AddCommGroup T]
  [inst_11 : Module (ZMod 2) T] [inst_12 : DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  [inst_13 : SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) T] [inst_14 : TopologicalSpace T]
  [inst_15 : DiscreteTopology T] [inst_16 : ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  (X : ZInQ.Manuscript.RC.SelmerComplex.GenuineSwitch K S (ZMod 2) M) (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
  (hβ : ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : M), (β (g • x)) (g • y) = g • (β x) y)
  (Iso : ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) β hβ X.ΔS X.ΔR)
  (tr :
    ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X
          3) →ₗ[ZMod 2]
      ZMod 2),
  (∀
      (c :
        ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X
            2)),
      tr
          (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                  (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).d
              2 3 ⋯)
            c) =
        0) →
    ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH3 tr →
      ∀ (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S),
        ReciprocityAt K S T q →
          ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2
              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) →
            ∀
              (eμ :
                ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) T ≃+
                  TauCeti.KummerCoeff (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) 2)
              (heμ :
                ∀ (g : TauCeti.AbsoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q))
                  (t : ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) T),
                  eμ
                      ((TauCeti.absoluteGaloisGroupRestrictEquiv
                              (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q)).symm
                          g •
                        t) =
                    g • eμ t),
              ZInQ.Contrib.RC53Assist.HswResidual.LocalTraceMatchesInvariant eμ heμ
                (ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt X β hβ Iso tr q)
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.hmatch_of_reciprocity' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `reciprocityAt_of_inducesIsoH2`

```lean
@reciprocityAt_of_inducesIsoH2 : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {M : Type} [inst_2 : AddCommGroup M]
  [inst_3 : Module (ZMod 2) M] [inst_4 : DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [inst_5 : SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) M] [inst_6 : TopologicalSpace M]
  [inst_7 : DiscreteTopology M] [inst_8 : ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [inst_9 : DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {T : Type} [inst_10 : AddCommGroup T]
  [inst_11 : Module (ZMod 2) T] [inst_12 : DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  [inst_13 : SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) T] [inst_14 : TopologicalSpace T]
  [inst_15 : DiscreteTopology T] [inst_16 : ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  (X : ZInQ.Manuscript.RC.SelmerComplex.GenuineSwitch K S (ZMod 2) M) (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
  (hβ : ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : M), (β (g • x)) (g • y) = g • (β x) y)
  (Iso : ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) β hβ X.ΔS X.ΔR)
  (tr :
    ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X
          3) →ₗ[ZMod 2]
      ZMod 2),
  (∀
      (c :
        ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X
            2)),
      tr
          (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                  (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).d
              2 3 ⋯)
            c) =
        0) →
    ∀ (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S),
      ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH2
          (ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt X β hβ Iso tr q) →
        ReciprocityAt K S T q
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.reciprocityAt_of_inducesIsoH2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `hmatch_iff_reciprocityAt`

```lean
@hmatch_iff_reciprocityAt : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {M : Type} [inst_2 : AddCommGroup M]
  [inst_3 : Module (ZMod 2) M] [inst_4 : DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [inst_5 : SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) M] [inst_6 : TopologicalSpace M]
  [inst_7 : DiscreteTopology M] [inst_8 : ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [inst_9 : DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {T : Type} [inst_10 : AddCommGroup T]
  [inst_11 : Module (ZMod 2) T] [inst_12 : DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  [inst_13 : SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) T] [inst_14 : TopologicalSpace T]
  [inst_15 : DiscreteTopology T] [inst_16 : ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
  (X : ZInQ.Manuscript.RC.SelmerComplex.GenuineSwitch K S (ZMod 2) M) (β : M →ₗ[ZMod 2] M →ₗ[ZMod 2] T)
  (hβ : ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : M), (β (g • x)) (g • y) = g • (β x) y)
  (Iso : ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) β hβ X.ΔS X.ΔR)
  (tr :
    ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X
          3) →ₗ[ZMod 2]
      ZMod 2),
  (∀
      (c :
        ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).X
            2)),
      tr
          (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                  (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) β hβ X.ΔS X.ΔR Iso).resE).d
              2 3 ⋯)
            c) =
        0) →
    ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH3 tr →
      ∀ (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S),
        ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) →
          ∀
            (eμ :
              ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) T ≃+
                TauCeti.KummerCoeff (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) 2)
            (heμ :
              ∀ (g : TauCeti.AbsoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q))
                (t : ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) T),
                eμ
                    ((TauCeti.absoluteGaloisGroupRestrictEquiv
                            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q)).symm
                        g •
                      t) =
                  g • eμ t),
            ZInQ.Contrib.RC53Assist.HswResidual.LocalTraceMatchesInvariant eμ heμ
                (ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt X β hβ Iso tr q) ↔
              ReciprocityAt K S T q
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.hmatch_iff_reciprocityAt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `hmatch_genuine`

```lean
@hmatch_genuine : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [inst_2 : DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {W : WeierstrassCurve K} [inst_3 : W.IsElliptic]
  (F : ZInQ.Contrib.CloudB3RC53.SwitchInputs.DerivFamily (ZInQ.Contrib.CloudB3RC53.SwitchInputs.galLv K S (ETwo K S W)))
  {q : ZInQ.Manuscript.RC.SelmerComplex.Places K S} (hR : ZInQ.Contrib.CloudB3RC53.SwitchInputs.RelAt F.str F.rel q)
  (φ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
  (eM :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) (ETwo K S W) ≃ₗ[ZMod 2]
      Fin 2 → ZMod 2)
  {I : Subgroup (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)}
  (Tc : ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinates I φ σ)
  (Iso :
    ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) (weilTwo K S W) ⋯
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR)
  (tr :
    ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                  Iso).resE).X
          3) →ₗ[ZMod 2]
      ZMod 2),
  (∀
      (c :
        ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                    Iso).resE).X
            2)),
      tr
          (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                  (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                      Iso).resE).d
              2 3 ⋯)
            c) =
        0) →
    ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH3 tr →
      ReciprocityAt K S (MuTwo K S) q →
        ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2
            (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) →
          ZInQ.Contrib.RC53Assist.HswResidual.LocalTraceMatchesInvariant (eMuq K S q) ⋯
            (ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt
              (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc))
              (weilTwo K S W) ⋯ Iso tr q)
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.hmatch_genuine' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `hmatch_genuine_iff`

```lean
@hmatch_genuine_iff : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [inst_2 : DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {W : WeierstrassCurve K} [inst_3 : W.IsElliptic]
  (F : ZInQ.Contrib.CloudB3RC53.SwitchInputs.DerivFamily (ZInQ.Contrib.CloudB3RC53.SwitchInputs.galLv K S (ETwo K S W)))
  {q : ZInQ.Manuscript.RC.SelmerComplex.Places K S} (hR : ZInQ.Contrib.CloudB3RC53.SwitchInputs.RelAt F.str F.rel q)
  (φ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
  (eM :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) (ETwo K S W) ≃ₗ[ZMod 2]
      Fin 2 → ZMod 2)
  {I : Subgroup (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)}
  (Tc : ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinates I φ σ)
  (Iso :
    ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) (weilTwo K S W) ⋯
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR)
  (tr :
    ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                  Iso).resE).X
          3) →ₗ[ZMod 2]
      ZMod 2),
  (∀
      (c :
        ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                    Iso).resE).X
            2)),
      tr
          (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                  (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                      Iso).resE).d
              2 3 ⋯)
            c) =
        0) →
    ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH3 tr →
      ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) →
        (ZInQ.Contrib.RC53Assist.HswResidual.LocalTraceMatchesInvariant (eMuq K S q) ⋯
            (ZInQ.Contrib.RC53Assist.HswResidual.residualTraceAt
              (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc))
              (weilTwo K S W) ⋯ Iso tr q) ↔
          ReciprocityAt K S (MuTwo K S) q)
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.hmatch_genuine_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `derivSwitch_switchCoordinates_tame_genuine`

```lean
@derivSwitch_switchCoordinates_tame_genuine : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [inst_2 : DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {W : WeierstrassCurve K} [inst_3 : W.IsElliptic]
  (F : ZInQ.Contrib.CloudB3RC53.SwitchInputs.DerivFamily (ZInQ.Contrib.CloudB3RC53.SwitchInputs.galLv K S (ETwo K S W)))
  {q : ZInQ.Manuscript.RC.SelmerComplex.Places K S} (hR : ZInQ.Contrib.CloudB3RC53.SwitchInputs.RelAt F.str F.rel q),
  ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2 →
    ZInQ.Contrib.RC53Assist.HswResidual.MilneCor23Residual →
      ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) →
        ReciprocityAt K S (MuTwo K S) q →
          ∀ (φ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
            (eM :
              ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q)
                  (ETwo K S W) ≃ₗ[ZMod 2]
                Fin 2 → ZMod 2)
            {I : Subgroup (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)}
            (Tc : ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinates I φ σ),
            (∀ (g : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q)),
                (ZInQ.Manuscript.RC.SelmerComplex.urRes K ↑q) g = 1 → g ∈ I) →
              ∀ (γ : ETwo K S W →ₗ[ZMod 2] ETwo K S W →ₗ[ZMod 2] MuTwo K S),
                (∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : ETwo K S W),
                    (γ (g • x)) (g • y) = g • (γ x) y) →
                  (∀ (x y : ETwo K S W), ((weilTwo K S W) x) y = (γ x) y - (γ y) x) →
                    ∀
                      (Iso :
                        ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) (weilTwo K S W) ⋯
                          (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                              (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                          (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                              (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR)
                      (tr :
                        ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                                  (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                      Iso).resE).X
                              3) →ₗ[ZMod 2]
                          ZMod 2),
                      (∀
                          (c :
                            ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                                    (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                                        (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                            (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                        (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                            (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                        Iso).resE).X
                                2)),
                          tr
                              (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                                      (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                                          (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                              (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                          (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                              (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                          Iso).resE).d
                                  2 3 ⋯)
                                c) =
                            0) →
                        ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH3 tr →
                          (∀ (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (x : ↑((F.str v).cx.X 2)), x = 0) →
                            ∀ {ε : ZMod 2},
                              ε ≠ 0 →
                                ∀ {J : Matrix (Fin 2) (Fin 2) (ZMod 2)},
                                  J * J = 1 →
                                    (∀ (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q) (m : ETwo K S W),
                                        (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q) g • m = m) →
                                      let X :=
                                        ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc);
                                      ∃ Φ,
                                        Submodule.map (↑Φ)
                                              (ZInQ.Manuscript.RC.Uniform.finPlane (ZMod 2) (Fin 2 → ZMod 2)
                                                (Fin 2 → ZMod 2)) =
                                            ZInQ.Manuscript.RC.Uniform.finPlane (ZMod 2) (Fin 2 → ZMod 2)
                                              (Fin 2 → ZMod 2) ∧
                                          { ΔR := X.ΔR, US := X.US, φ := X.φ, W := X.W, g := X.g, hfg := ⋯, φ_inj := ⋯,
                                                g_surj := ⋯, ex := ⋯, eR := X.eR ≪≫ₗ Φ }.SwitchCoordinates
                                            (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2)
                                              (weilTwo K S W) ⋯ X.ΔS X.ΔR Iso)
                                            tr ε (- -1) J
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.derivSwitch_switchCoordinates_tame_genuine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `derivSwitch_switchCoordinates_tame_genuine_rational`

```lean
@derivSwitch_switchCoordinates_tame_genuine_rational : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [inst_2 : DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {W : WeierstrassCurve K} [inst_3 : W.IsElliptic]
  (F : ZInQ.Contrib.CloudB3RC53.SwitchInputs.DerivFamily (ZInQ.Contrib.CloudB3RC53.SwitchInputs.galLv K S (ETwo K S W)))
  {q : ZInQ.Manuscript.RC.SelmerComplex.Places K S} (hR : ZInQ.Contrib.CloudB3RC53.SwitchInputs.RelAt F.str F.rel q),
  ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2 →
    ZInQ.Contrib.RC53Assist.HswResidual.MilneCor23Residual →
      ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) →
        ReciprocityAt K S (MuTwo K S) q →
          (∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (P : ETwo K S W), g • P = P) →
            ∀ (φ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
              (eM :
                ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q)
                    (ETwo K S W) ≃ₗ[ZMod 2]
                  Fin 2 → ZMod 2)
              {I : Subgroup (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)}
              (Tc : ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinates I φ σ),
              (∀ (g : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q)),
                  (ZInQ.Manuscript.RC.SelmerComplex.urRes K ↑q) g = 1 → g ∈ I) →
                ∀
                  (Iso :
                    ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) (weilTwo K S W) ⋯
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR)
                  (tr :
                    ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                  Iso).resE).X
                          3) →ₗ[ZMod 2]
                      ZMod 2),
                  (∀
                      (c :
                        ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                    Iso).resE).X
                            2)),
                      tr
                          (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                                  (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                      (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                      Iso).resE).d
                              2 3 ⋯)
                            c) =
                        0) →
                    ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH3 tr →
                      (∀ (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (x : ↑((F.str v).cx.X 2)), x = 0) →
                        ∀ {ε : ZMod 2},
                          ε ≠ 0 →
                            ∀ {J : Matrix (Fin 2) (Fin 2) (ZMod 2)},
                              J * J = 1 →
                                let X :=
                                  ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc);
                                ∃ Φ,
                                  Submodule.map (↑Φ)
                                        (ZInQ.Manuscript.RC.Uniform.finPlane (ZMod 2) (Fin 2 → ZMod 2)
                                          (Fin 2 → ZMod 2)) =
                                      ZInQ.Manuscript.RC.Uniform.finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ∧
                                    { ΔR := X.ΔR, US := X.US, φ := X.φ, W := X.W, g := X.g, hfg := ⋯, φ_inj := ⋯,
                                          g_surj := ⋯, ex := ⋯, eR := X.eR ≪≫ₗ Φ }.SwitchCoordinates
                                      (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilTwo K S W) ⋯
                                        X.ΔS X.ΔR Iso)
                                      tr ε (- -1) J
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.derivSwitch_switchCoordinates_tame_genuine_rational' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `derivSwitch_switchCoordinates_tame_curveEll`

```lean
@derivSwitch_switchCoordinates_tame_curveEll : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  [inst_2 : DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)] {ℓ : K}
  [inst_3 : (ZInQ.Manuscript.RC.CoefModules.curveEll ℓ).IsElliptic]
  (F :
    ZInQ.Contrib.CloudB3RC53.SwitchInputs.DerivFamily
      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.galLv K S (ETwo K S (ZInQ.Manuscript.RC.CoefModules.curveEll ℓ))))
  {q : ZInQ.Manuscript.RC.SelmerComplex.Places K S} (hR : ZInQ.Contrib.CloudB3RC53.SwitchInputs.RelAt F.str F.rel q),
  ℓ ≠ 0 →
    ZInQ.Contrib.RC53Assist.HswResidual.MilneCor23Residual →
      ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) →
        ReciprocityAt K S (MuTwo K S) q →
          ∀ (φ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
            (eM :
              ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q)
                  (ETwo K S (ZInQ.Manuscript.RC.CoefModules.curveEll ℓ)) ≃ₗ[ZMod 2]
                Fin 2 → ZMod 2)
            {I : Subgroup (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)}
            (Tc : ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinates I φ σ),
            (∀ (g : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q)),
                (ZInQ.Manuscript.RC.SelmerComplex.urRes K ↑q) g = 1 → g ∈ I) →
              ∀
                (Iso :
                  ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2)
                    (weilTwo K S (ZInQ.Manuscript.RC.CoefModules.curveEll ℓ)) ⋯
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR)
                (tr :
                  ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                            (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2)
                                (weilTwo K S (ZInQ.Manuscript.RC.CoefModules.curveEll ℓ)) ⋯
                                (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                Iso).resE).X
                        3) →ₗ[ZMod 2]
                    ZMod 2),
                (∀
                    (c :
                      ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2)
                                  (weilTwo K S (ZInQ.Manuscript.RC.CoefModules.curveEll ℓ)) ⋯
                                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                  Iso).resE).X
                          2)),
                    tr
                        (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2)
                                    (weilTwo K S (ZInQ.Manuscript.RC.CoefModules.curveEll ℓ)) ⋯
                                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                    Iso).resE).d
                            2 3 ⋯)
                          c) =
                      0) →
                  ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH3 tr →
                    (∀ (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (x : ↑((F.str v).cx.X 2)), x = 0) →
                      ∀ {ε : ZMod 2},
                        ε ≠ 0 →
                          ∀ {J : Matrix (Fin 2) (Fin 2) (ZMod 2)},
                            J * J = 1 →
                              let X :=
                                ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                  (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc);
                              ∃ Φ,
                                Submodule.map (↑Φ)
                                      (ZInQ.Manuscript.RC.Uniform.finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)) =
                                    ZInQ.Manuscript.RC.Uniform.finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ∧
                                  { ΔR := X.ΔR, US := X.US, φ := X.φ, W := X.W, g := X.g, hfg := ⋯, φ_inj := ⋯,
                                        g_surj := ⋯, ex := ⋯, eR := X.eR ≪≫ₗ Φ }.SwitchCoordinates
                                    (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2)
                                      (weilTwo K S (ZInQ.Manuscript.RC.CoefModules.curveEll ℓ)) ⋯ X.ΔS X.ΔR Iso)
                                    tr ε (- -1) J
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.derivSwitch_switchCoordinates_tame_curveEll' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `residualToETwo`

```lean
@residualToETwo : {K : Type} →
  [inst : Field K] →
    {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
      (W : WeierstrassCurve K) →
        (j : ℕ) →
          (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef (j + 1))ˣ) →
            ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ (j + 1)) →
              ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ j) →
                ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2 →
                  ZInQ.Contrib.CloudB3RC53.GenuineInst.ResidualM W j α ≃ₗ[ZMod 2] ETwo K S W
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.residualToETwo' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilResidual`

```lean
@weilResidual : {K : Type} →
  [inst : Field K] →
    [NumberField K] →
      {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
        (W : WeierstrassCurve K) →
          [W.IsElliptic] →
            (j : ℕ) →
              (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef (j + 1))ˣ) →
                ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ (j + 1)) →
                  ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ j) →
                    ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2 →
                      ZInQ.Contrib.CloudB3RC53.GenuineInst.ResidualM W j α →ₗ[ZMod 2]
                        ZInQ.Contrib.CloudB3RC53.GenuineInst.ResidualM W j α →ₗ[ZMod 2] MuTwo K S
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilResidual' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilResidual_smul`

```lean
@weilResidual_smul : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [inst_2 : W.IsElliptic] (j : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef (j + 1))ˣ)
  (hT : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ (j + 1)))
  (hM : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ j))
  (h2 : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2) (σ : ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
  (x y : ZInQ.Contrib.CloudB3RC53.GenuineInst.ResidualM W j α),
  ((weilResidual W j α hT hM h2) (σ • x)) (σ • y) = σ • ((weilResidual W j α hT hM h2) x) y
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilResidual_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilResidual_hWeil`

```lean
@weilResidual_hWeil : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [inst_2 : W.IsElliptic] (j : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef (j + 1))ˣ)
  (hT : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ (j + 1)))
  (hM : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ j))
  (h2 : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2) (q : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (eM :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q)
        (ZInQ.Contrib.CloudB3RC53.GenuineInst.ResidualM W j α) ≃ₗ[ZMod 2]
      Fin 2 → ZMod 2)
  (x y :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q)
      (ZInQ.Contrib.CloudB3RC53.GenuineInst.ResidualM W j α)),
  (eTq K S q)
      (((ZInQ.Manuscript.RC.SelmerComplex.resPairing (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
            (weilResidual W j α hT hM h2) (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q))
          x)
        y) =
    (ZInQ.Manuscript.RC.Uniform.weil (eM x)) (eM y)
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilResidual_hWeil' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `weilResidual_polarization`

```lean
@weilResidual_polarization : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [inst_2 : W.IsElliptic] (j : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef (j + 1))ˣ)
  (hT : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ (j + 1)))
  (hM : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ j))
  (h2 : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2),
  (∀ (σ : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (P : ZInQ.Manuscript.RC.CoefModules.TorsS K S W ↑2), σ • P = P) →
    ∃ γ,
      (∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (x y : ZInQ.Contrib.CloudB3RC53.GenuineInst.ResidualM W j α),
          (γ (g • x)) (g • y) = g • (γ x) y) ∧
        ∀ (x y : ZInQ.Contrib.CloudB3RC53.GenuineInst.ResidualM W j α),
          ((weilResidual W j α hT hM h2) x) y = (γ x) y - (γ y) x
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.weilResidual_polarization' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `derivSwitch_switchCoordinates_tame_residualM`

```lean
@derivSwitch_switchCoordinates_tame_residualM : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [inst_2 : W.IsElliptic] (j : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef (j + 1))ˣ)
  (hT : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ (j + 1)))
  (hM : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ j))
  (h2 : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W 2)
  [inst_3 :
    ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZInQ.Contrib.CloudB3RC53.GenuineInst.ResidualM W j α)]
  [inst_4 : DecidableEq (ZInQ.Manuscript.RC.SelmerComplex.Places K S)]
  (F :
    ZInQ.Contrib.CloudB3RC53.SwitchInputs.DerivFamily
      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.galLv K S (ZInQ.Contrib.CloudB3RC53.GenuineInst.ResidualM W j α)))
  {q : ZInQ.Manuscript.RC.SelmerComplex.Places K S} (hR : ZInQ.Contrib.CloudB3RC53.SwitchInputs.RelAt F.str F.rel q),
  (∀ (σ : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (P : ZInQ.Manuscript.RC.CoefModules.TorsS K S W ↑2), σ • P = P) →
    ZInQ.Contrib.RC53Assist.HswResidual.MilneCor23Residual →
      ZInQ.Contrib.RC53Assist.HswResidual.KummerBrauerComparisonF2
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q) →
        ReciprocityAt K S (MuTwo K S) q →
          ∀ (φ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)
            (eM :
              ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑q)
                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.ResidualM W j α) ≃ₗ[ZMod 2]
                Fin 2 → ZMod 2)
            {I : Subgroup (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑q)}
            (Tc : ZInQ.Contrib.CloudB3RC53.SwitchInputs.TameCoordinates I φ σ),
            (∀ (g : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑q)),
                (ZInQ.Manuscript.RC.SelmerComplex.urRes K ↑q) g = 1 → g ∈ I) →
              ∀
                (Iso :
                  ZInQ.Manuscript.RC.SelmerComplex.GaloisIsotropyData K S (ZMod 2) (weilResidual W j α hT hM h2) ⋯
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR)
                (tr :
                  ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                            (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2) (weilResidual W j α hT hM h2)
                                ⋯
                                (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                Iso).resE).X
                        3) →ₗ[ZMod 2]
                    ZMod 2),
                (∀
                    (c :
                      ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                              (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2)
                                  (weilResidual W j α hT hM h2) ⋯
                                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                  (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                  Iso).resE).X
                          2)),
                    tr
                        (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx
                                (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2)
                                    (weilResidual W j α hT hM h2) ⋯
                                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔS
                                    (ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                        (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc)).ΔR
                                    Iso).resE).d
                            2 3 ⋯)
                          c) =
                      0) →
                  ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH3 tr →
                    (∀ (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (x : ↑((F.str v).cx.X 2)), x = 0) →
                      ∀ {ε : ZMod 2},
                        ε ≠ 0 →
                          ∀ {J : Matrix (Fin 2) (Fin 2) (ZMod 2)},
                            J * J = 1 →
                              let X :=
                                ZInQ.Contrib.CloudB3RC53.GenuineInst.derivSwitch F
                                  (ZInQ.Contrib.CloudB3RC53.SwitchInputs.eRAt ⋯ hR φ σ eM Tc);
                              ∃ Φ,
                                Submodule.map (↑Φ)
                                      (ZInQ.Manuscript.RC.Uniform.finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2)) =
                                    ZInQ.Manuscript.RC.Uniform.finPlane (ZMod 2) (Fin 2 → ZMod 2) (Fin 2 → ZMod 2) ∧
                                  { ΔR := X.ΔR, US := X.US, φ := X.φ, W := X.W, g := X.g, hfg := ⋯, φ_inj := ⋯,
                                        g_surj := ⋯, ex := ⋯, eR := X.eR ≪≫ₗ Φ }.SwitchCoordinates
                                    (ZInQ.Manuscript.RC.SelmerComplex.galoisPairData K S (ZMod 2)
                                      (weilResidual W j α hT hM h2) ⋯ X.ΔS X.ΔR Iso)
                                    tr ε (- -1) J
```

Axioms:

```text
'ZInQ.Contrib.RC53Assist.HswIdent.derivSwitch_switchCoordinates_tame_residualM' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Definition of `ReciprocityAt`

```lean
def ZInQ.Contrib.RC53Assist.HswIdent.ReciprocityAt : (K : Type) →
  [inst : Field K] →
    [NumberField K] →
      (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
        (T : Type) →
          [inst_2 : AddCommGroup T] →
            [inst_3 : Module (ZMod 2) T] →
              [inst_4 : DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T] →
                [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) T] →
                  [inst_6 : TopologicalSpace T] →
                    [DiscreteTopology T] →
                      [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T] →
                        ZInQ.Manuscript.RC.SelmerComplex.Places K S → Prop :=
fun K [Field K] [NumberField K] S T [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T]
    [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZMod 2) T] [TopologicalSpace T] [DiscreteTopology T]
    [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T] q =>
  ∀ (e : ↑((ZInQ.Manuscript.RC.SelmerComplex.globalCx (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T).X 2)),
    ((ZInQ.Manuscript.RC.SelmerComplex.globalCx (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) T).d 2 3
            ReciprocityAt._proof_3)
          e =
        0 →
      (∀ (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S),
          v ≠ q →
            ∃ y,
              ((ZInQ.Manuscript.RC.SelmerComplex.localCx (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
                        (fun v => ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
                        (fun v => ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v) T v).d
                    1 2 ReciprocityAt._proof_5)
                  y =
                ((ZInQ.Manuscript.RC.SelmerComplex.resS (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
                        (fun v => ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
                        (fun v => ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v) T).f
                    2 2 ReciprocityAt._proof_6)
                  e v) →
        ∃ y,
          ((ZInQ.Manuscript.RC.SelmerComplex.localCx (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
                    (fun v => ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
                    (fun v => ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v) T q).d
                1 2 ReciprocityAt._proof_5)
              y =
            ((ZInQ.Manuscript.RC.SelmerComplex.resS (ZMod 2) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
                    (fun v => ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
                    (fun v => ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v) T).f
                2 2 ReciprocityAt._proof_6)
              e q
```
