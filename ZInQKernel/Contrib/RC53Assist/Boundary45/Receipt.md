# Boundary (4.5): verified local hypotheses


## Update after independent review (2026-11-18)

The file hashes and sizes recorded further below refer to an earlier, instrumented edition of the sources; the shipped sources are:

- `LocalFacts.lean`: 16297 bytes, SHA-256 `8c6efef340e07cc8a8893073b2fce514ee293f50d638e97cb2a3c30b2651b57d`
- `InflationFacts.lean`: 5172 bytes, SHA-256 `826e54a99af23d187c3088952c1f1b62ce2d387a3e530927e7327013926a5fb2`
- `RetainedStage.lean`: 5456 bytes, SHA-256 `8dc57582e8083ea98e949e994d10038f3ed90d09b56db3a37faf85434e331bba`

The unneeded `maxHeartbeats` option was removed from `LocalFacts.lean` and `InflationFacts.lean`. The consumed form of the local facts is the pair of fields `honto`/`hinj` of `RetainedStage45` (fed to `InnerLimit45Base.ofStages`), not `boundary45_finite_of_construction`; `RetainedStage.lean` adds `retainedStageOfLocalFacts` and `mixedRetainedStage`, which fill those fields verbatim, and `not_localFacts_zero_into_const`, which shows the predicate is not vacuous. The independent review also compiled the Kummer-span case against the repository's `kummerActualSelData`. Still open: matching the actual finite stages with `mixedStageSelData`; note that `RetainedStage45` works in the fibre t = 0 over Z/2^i while `mixedStageSelData` is over (Z/2^n)[t]/t^n. The compiler logs cited below are not part of the shipped files.

## Result and scope

Two individually checked Lean files prove the representative-level local facts for continuous cocycle conditions, full conditions, the existing unramified condition, and the mixed finite-stage pattern. A further theorem proves the same two facts for genuine continuous inflation with the invariant coefficient subgroup. The finite-boundary adapter consumes exactly the original two local inputs.

The supplied source snapshot is `6ea158a404343c90a445c129cd0d1f3a0d4b8ddc`. The pinned toolchain is Lean 4.35.0. Both final single-file checks exited 0 with no warnings or errors. All thirteen theorem reports contain only the standard axioms.

No preexisting source file was changed, no version-control command or dependency build was run, and no additional agent or human contact was used. The two source files set `maxHeartbeats` to 600000. No printed leaf is introduced.

## Exact mathematical hypotheses

At one stage and place let `i : U → L` be the local-condition cochain map. The two predicates are exactly:

```text
honto:
  for every c in L^0 with d_L c = 0,
  there exists w in U^0 such that d_U w = 0 and i^0(w) = c.

hinj:
  for every u in U^1 with d_U u = 0,
  if there exists c in L^0 with i^1(u) = d_L c,
  then there exists w in U^0 with d_U w = u.
```

These say that zeroth cohomology maps onto local invariants and that the first-cohomology map is injective. They do not assert surjectivity of the degree-one cochain map. `LocalFacts i` is their conjunction, in that order.

For a cocycle condition, `U^0 = C_cont^0(G_v,M)` and `U^1 = Z_v + B_cont^1(G_v,M)`. The inclusion is onto all degree-zero cochains and injective on degree-one cochains. Commutativity with the differential then proves both predicates. This applies to the existing Kummer spans and their coefficient extensions; no Kummer-image or local-duality assertion is assumed as a new leaf.

For the existing unramified map `[W ⟶ W]`, with differential `Phi - 1`, degree zero sends a coefficient to its constant cochain and degree one sends it to its inflated Frobenius cocycle. A bijective coefficient comparison and a Frobenius lift suffice. Both are proved for `urAt`: its coefficient comparison is the identity and restriction to the unramified quotient is surjective.

The inflation file also covers a proper invariant subgroup: `U^0 = M^N`, `L^0 = M`, and the degree-one maps are actual pullbacks of continuous cochains. It uses the existing degree-zero inflation surjection and degree-one inflation injection, not a five-term statement supplied as a hypothesis.

## Manuscript alignment

Lines 3917-3918 assert the lifting step but do not supply a separate argument there. The required local choices are the old Kummer conditions, good unramified conditions, and full active/moving conditions of lines 2865-2868. The finite Kummer shape is described at lines 3413-3438, and unramified support comparison at lines 3471-3498. The existing continuous definitions and proved lemmas suffice for the local facts themselves.

`mixedStageSelData` uses the existing actual coefficient module `MinS`, the existing `actualSelData` constructor, a cocycle condition at each old place outside the selected full set, the full condition at each selected old place, and the existing `urAt` outside the coefficient support. At Kummer places choose `Z_v` to be the existing extended Kummer span and use its existing cocycle lemma. At unused places choose the zero span; no Kummer coefficient map is needed at a full or new place.

## Supplying the unchanged boundary theorem

At each stage set

```lean
D := mixedStageSelData hS W n a F Z hZ
h := mixedStage_localFacts hS W n a F Z hZ
```

Then `h.1` has the exact type of `honto` and `h.2` the exact type of `hinj`, with `dU0`, `dU1`, `dL0`, `i0`, and `i1` taken from `D`. The linear maps are converted with `toAddMonoidHom`, exactly as in the checked adapter `boundary45_finite_of_construction_of_localFacts`. That adapter preserves every global construction, Kummer, class-map, and cycle hypothesis of the original theorem and produces the retained witness `(v,w)` with the same multiplier.

## What remains open

1. Bind the integration lead's actual finite-stage cochain tuple and local maps to this data, or to a proved comparison carrying the same degree-zero and degree-one maps. `SplitNormStage` contains ring-class point and norm data only; the original boundary theorem quantifies independently over its cochain groups and maps. It therefore cannot furnish that identification by itself.
2. The compiled modules `ZInQKernel.Contrib.OneProof.RC.CoefModules.Kummer` and `ZInQKernel.Contrib.OneProof.RC.CoefModules.KummerAt` were absent. No dependency build was attempted. Consequently the named Kummer specialization was not separately compiled; its underlying cocycle-condition statement is proved and checked here. The actual twist/embedding coefficient maps remain the existing construction's data, not a new printed leaf.
3. There is no claim for orthogonal zero conditions with nonzero local invariants. There is also no proof here of the inner-limit statement `Boundary45Base.hlim` or of the complete `RCSteps.base_zero` leaf.

## Files and reproducibility

The sources and compiler stdout are included in the same review packet. The sources are standalone: neither needs a compiled module from the other. Each was checked from the supplied repository root using six Lean threads, CPU affinity 16-31, niceness 10, and the prescribed `lake env lean` single-file invocation.

- `LocalFacts.lean`: 17126 bytes; SHA-256 `791ddf174027f14a4bf9630be2a2317fb2a3221a04bf5b820d2eb721d40c33fa`.
- `InflationFacts.lean`: 5331 bytes; SHA-256 `7b4d5ae48e4fe97dbeecd0c22fada7ca6280587c27539bd5fb647247bf0dfc08`.
- `check-local-final.log`: 7964 bytes; SHA-256 `c7b6463d7754b0fa715f4a11294605b23c0e27eda5cf682fa14fe802e5351f07`.
- `check-inflation-final.log`: 1623 bytes; SHA-256 `b950ef79c6fd4362862e782bb173b162c0ce3b74633613d7d10a86559f763c1f`.

Four earlier checks failed during elaboration or name resolution; two intermediate checks succeeded with warnings. Their stdout is preserved, labeled by the log names, rather than treated as proof evidence. The two final logs above are the clean checks of the final sources.

## Every compiler-checked statement and axiom report

The following statements are copied from the final compiler stdout. The displayed ellipses are proof-term suppression by the pretty-printer, not omitted mathematical assumptions. The complete explicit declarations and bodies are in the source files.

### `localFacts_of_surjective_zero_injective_one`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.localFacts_of_surjective_zero_injective_one.{u} {k : Type u}
  [CommRing k] {U L : GCx k} (i : GHom U L) (h0 : Function.Surjective ⇑(i.f 0 0 ⋯))
  (h1 : Function.Injective ⇑(i.f 1 1 ⋯)) : LocalFacts i
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.localFacts_of_surjective_zero_injective_one' depends on axioms: [propext]
```

### `localFacts_pi`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.localFacts_pi.{u} {k : Type u} [CommRing k] {V : Type u}
  {Us Ls : V → GCx k} (i : (v : V) → GHom (Us v) (Ls v)) (hi : ∀ (v : V), LocalFacts (i v)) : LocalFacts (piMap i)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.localFacts_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `full_localFacts`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.full_localFacts.{u} {k : Type u} [CommRing k] (L : GCx k) :
  LocalFacts (idGHom L)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.full_localFacts' depends on axioms: [propext]
```

### `cocycleCondition_localFacts`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.cocycleCondition_localFacts.{u} {k : Type u} [CommRing k]
  {G : Type u} [Group G] [TopologicalSpace G] [ContinuousMul G] {M : Type u} [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M]
  [ContinuousSMul G M] (Z : Submodule k ↥(contCochain k G M 1)) (hZ : ∀ z ∈ Z, (contD k G M 1) z = 0) :
  LocalFacts (cocycleConditionι Z hZ)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.cocycleCondition_localFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `unramified_localFacts`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.unramified_localFacts {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Type} [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] (e : H ≃ₜ* ↑TauCeti.zHat.toProfinite.toTop) (p : G →ₜ* H) (X : TopRep k H)
  [ContinuousSMul H ↑X] [DiscreteTopology ↑X] [Finite ↑X] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction G M] [SMulCommClass G k M] [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  (f : ↑X →ₗ[k] M) (hf : ∀ (g : G) (x : ↑X), f (p g • x) = g • f x) (hfb : Function.Bijective ⇑f)
  (hp : ∃ g, p g = frobElt e) : LocalFacts (ofCCHom (urToLocal e p X f hf))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.unramified_localFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `urAt_localFacts`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.urAt_localFacts {K : Type} [Field K] [NumberField K]
  {S S0 : Set (HeightOneSpectrum (𝓞 K))} (hS : S0 ⊆ S) (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k]
  (M0 : Type) [AddCommGroup M0] [Module k M0] [DistribMulAction (GKS K S0) M0] [SMulCommClass (GKS K S0) k M0]
  [TopologicalSpace M0] [DiscreteTopology M0] [ContinuousSMul (GKS K S0) M0] [Finite M0] (v : Places K S)
  (hv : ↑v ∉ S0) : LocalFacts (urAt hS k M0 v hv).i
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.urAt_localFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `actual_localFacts`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.actual_localFacts {K : Type} [Field K] [NumberField K]
  {S S0 : Set (HeightOneSpectrum (𝓞 K))} (hS : S0 ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ)
  (a : GKS K S0 →* (HeegnerAlgebra.Acoef n)ˣ) [IsOpenKer a]
  (c : (v : Places K S) → ↑v ∈ S0 → CondAt K S (HeegnerAlgebra.Acoef n) (MinS hS W n a) v)
  (hc : ∀ (v : Places K S) (h : ↑v ∈ S0), LocalFacts (c v h).i) : LocalFacts (actualSelData hS W n a c).ι
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.actual_localFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `cocycleStage_localFacts`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.cocycleStage_localFacts {K : Type} [Field K] [NumberField K]
  {S S0 : Set (HeightOneSpectrum (𝓞 K))} (hS : S0 ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ)
  (a : GKS K S0 →* (HeegnerAlgebra.Acoef n)ˣ) [IsOpenKer a]
  (Z :
    (v : Places K S) →
      Submodule (HeegnerAlgebra.Acoef n)
        ↥(contCochain (HeegnerAlgebra.Acoef n) (Gloc K ↑v) (ResMod (locMap K S ↑v) (MinS hS W n a)) 1))
  (hZ :
    ∀ (v : Places K S),
      ∀ z ∈ Z v, (contD (HeegnerAlgebra.Acoef n) (Gloc K ↑v) (ResMod (locMap K S ↑v) (MinS hS W n a)) 1) z = 0) :
  LocalFacts (cocycleStageSelData hS W n a Z hZ).ι
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.cocycleStage_localFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `mixedStage_localFacts`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.mixedStage_localFacts {K : Type} [Field K] [NumberField K]
  {S S0 : Set (HeightOneSpectrum (𝓞 K))} (hS : S0 ⊆ S) (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ)
  (a : GKS K S0 →* (HeegnerAlgebra.Acoef n)ˣ) [IsOpenKer a] (F : Set (Places K S))
  (Z :
    (v : Places K S) →
      Submodule (HeegnerAlgebra.Acoef n)
        ↥(contCochain (HeegnerAlgebra.Acoef n) (Gloc K ↑v) (ResMod (locMap K S ↑v) (MinS hS W n a)) 1))
  (hZ :
    ∀ (v : Places K S),
      ∀ z ∈ Z v, (contD (HeegnerAlgebra.Acoef n) (Gloc K ↑v) (ResMod (locMap K S ↑v) (MinS hS W n a)) 1) z = 0) :
  LocalFacts (mixedStageSelData hS W n a F Z hZ).ι
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.mixedStage_localFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `selmerCone_lift_of_localFacts`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.selmerCone_lift_of_localFacts.{u} {k : Type u} [CommRing k]
  (D : SelData k) (h : LocalFacts D.ι) {p p' : ↑(D.G.X 1)} {a a' : ↑(D.U.X 1)} {q q' : ↑(D.L.X 0)}
  (ha : (D.U.d 1 2 ⋯) a = 0) (ha' : (D.U.d 1 2 ⋯) a' = 0) (hpq : (D.res.f 1 1 ⋯) p - (D.ι.f 1 1 ⋯) a = (D.L.d 0 1 ⋯) q)
  (hpq' : (D.res.f 1 1 ⋯) p' - (D.ι.f 1 1 ⋯) a' = (D.L.d 0 1 ⋯) q') {g : ↑(D.G.X 0)} (hg : p - p' = (D.G.d 0 1 ⋯) g) :
  ∃ w, (D.U.d 0 1 ⋯) w = a - a' ∧ (D.res.f 0 0 ⋯) g - (D.ι.f 0 0 ⋯) w = q - q'
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.selmerCone_lift_of_localFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `boundary45_finite_of_construction_of_localFacts`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.boundary45_finite_of_construction_of_localFacts.{u, u_1, u_2, u_3,
    u_4, u_5}
  {k : Type u} [CommRing k] {PGroup : Type} [AddCommGroup PGroup] {P : PGroup} (T : SplitNormStage P) (D : SelData k)
  (hlocal : LocalFacts D.ι) {H1 : Type u_1} {A : Type u_2} {B : Type u_3} {C : Type u_4} {Q : Type u_5}
  [AddCommGroup H1] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup Q] (cls : ↑(D.G.X 1) →+ H1)
  (hexact : ∀ (c : ↑(D.G.X 1)), (D.G.d 1 2 ⋯) c = 0 → cls c = 0 → ∃ g, (D.G.d 0 1 ⋯) g = c) (δ : PGroup →+ H1) (e : ℕ)
  (Inp : HeegnerAlgebra.InfResInput A B C Q e) (κ : T.Pt →+ B) (δa : T.Pt →+ C)
  (hκ : ∀ (x : T.Pt), Inp.seq.res (κ x) = δa x) (m0 Cπ Cbad : ℕ) (Tr : B →+ H1) (Wsum : T.Pt →+ PGroup)
  (hWsum : ∀ (x : T.Pt), T.incl (Wsum x) = ∑ γ, (T.act γ) x) (hTr : ∀ (x : T.Pt), Tr (κ x) = δ (Wsum x))
  {zG jG : ↑(D.G.X 1)} {zU jU : ↑(D.U.X 1)} {zL jL : ↑(D.L.X 0)} (hzG : (D.G.d 1 2 ⋯) zG = 0)
  (hjG : (D.G.d 1 2 ⋯) jG = 0) (hzU : (D.U.d 1 2 ⋯) zU = 0) (hjU : (D.U.d 1 2 ⋯) jU = 0)
  (hz : (D.res.f 1 1 ⋯) zG - (D.ι.f 1 1 ⋯) zU = (D.L.d 0 1 ⋯) zL)
  (hj : (D.res.f 1 1 ⋯) jG - (D.ι.f 1 1 ⋯) jU = (D.L.d 0 1 ⋯) jL)
  (hzcls : cls zG = Tr (↑(m0 * Cbad) • Inp.seq.descend e ⋯ (δa (↑Cπ • T.yr)))) (hjcls : cls jG = δ P) :
  ∃ v w,
    zG - (HeegnerAlgebra.Lmult m0 Cπ Cbad e * (T.a - 2)) • jG = (D.G.d 0 1 ⋯) v ∧
      zU - (HeegnerAlgebra.Lmult m0 Cπ Cbad e * (T.a - 2)) • jU = (D.U.d 0 1 ⋯) w ∧
        (D.res.f 0 0 ⋯) v - (D.ι.f 0 0 ⋯) w = zL - (HeegnerAlgebra.Lmult m0 Cπ Cbad e * (T.a - 2)) • jL
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.boundary45_finite_of_construction_of_localFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `inflation_coboundary`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Inflation.inflation_coboundary.{u, v} (G : Type u) [Group G]
  [TopologicalSpace G] (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] (N : Subgroup G) [N.Normal]
  [ContinuousSMul (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M)] (w : ↥(FixedPoints.addSubgroup (↥N) M)) :
  (inflation1 G M N) ((coboundaryC1 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M)) w) =
    (coboundaryC1 G M) ((inflation0 G M N) w)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Inflation.inflation_coboundary' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `inflation_localFacts`

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Inflation.inflation_localFacts.{u, v} (G : Type u) [Group G]
  [TopologicalSpace G] (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] (N : Subgroup G) [N.Normal]
  [ContinuousSMul (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M)] :
  (∀ (c : M),
      (coboundaryC1 G M) c = 0 →
        ∃ w, (coboundaryC1 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M)) w = 0 ∧ (inflation0 G M N) w = c) ∧
    ∀ (a : ↥(C1 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M))),
      (d1 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M)) ↑a = 0 →
        (∃ c, (inflation1 G M N) a = (coboundaryC1 G M) c) →
          ∃ w, (coboundaryC1 (G ⧸ N) ↥(FixedPoints.addSubgroup (↥N) M)) w = a
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Inflation.inflation_localFacts' depends on axioms: [propext, Classical.choice, Quot.sound]
```
