# Review corrections: exact declarations and kernel dependencies

The compiler statements and individual dependency reports below are verbatim final-check output. The symbol `⋯` suppresses proof arguments only. Definitions and input records are displayed by type; their complete bodies and fields are in the production sources. These records are conditional contracts, not arithmetic existence proofs.

## Obstructions.lean

### eraseModel

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) {P : W.toAffine.Point}
  (T : ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P) (L : ℤ) (N M0 : ℕ)
  (C : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput W i hS hFull Pold hdiv T L N M0)
  (A : Matrix (Fin N) (Fin M0) ℤ_[2]) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput W i hS hFull Pold hdiv T L N M0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### eraseModel_spec

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel_spec {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) {P : W.toAffine.Point}
  (T : ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P) (L : ℤ) (N M0 : ℕ)
  (C : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput W i hS hFull Pold hdiv T L N M0)
  (A : Matrix (Fin N) (Fin M0) ℤ_[2]) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel W i hS hFull Pold hdiv T L N M0 C A).zG =
      C.zG ∧
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel W i hS hFull Pold hdiv T L N M0 C
            A).zU =
        C.zU ∧
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel W i hS hFull Pold hdiv T L N M0 C
              A).jU =
          C.jU ∧
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel W i hS hFull Pold hdiv T L N M0 C
                A).p1 =
            0 ∧
          (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel W i hS hFull Pold hdiv T L N M0 C
                  A).p0 =
              0 ∧
            (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel W i hS hFull Pold hdiv T L N M0
                    C A).dC =
                A ∧
              (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel W i hS hFull Pold hdiv T L N
                      M0 C A).zeta =
                  0 ∧
                (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel W i hS hFull Pold hdiv T L
                      N M0 C A).jay =
                  0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.eraseModel_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### class_premise_iff_global_boundary

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.class_premise_iff_global_boundary {K : Type} [Field K]
  [NumberField K] [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) {P : W.toAffine.Point}
  (T : ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P) (L : ℤ)
  (zG : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).G.X 1)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClass
          (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
        zG =
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerMap W i hdiv hS hFull Pold) (L • T.W) ↔
    ∃ (g : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).G.X 0)),
      ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).G.d 0 1 ⋯) g =
        zG -
          (L * (T.a - 2)) •
            ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle W i hdiv hS hFull Pold P
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.class_premise_iff_global_boundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### zeroProjectionInputFixed

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.zeroProjectionInputFixed {K : Type} [Field K]
  [NumberField K] [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) {P : W.toAffine.Point}
  (T : ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P) (L : ℤ) (N M0 : ℕ)
  (jU : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).U.X 1))
  (jL : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).L.X 0))
  (hjU : ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).U.d 1 2 ⋯) jU = 0)
  (hj :
    ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).res.f 1 1 ⋯)
          (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle W i hdiv hS hFull Pold P) -
        ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).ι.f 1 1 ⋯) jU =
      ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).L.d 0 1 ⋯) jL)
  (A : Matrix (Fin N) (Fin M0) ℤ_[2]) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput W i hS hFull Pold hdiv T L N M0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.zeroProjectionInputFixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### zeroProjectionInputFixed_spec

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.zeroProjectionInputFixed_spec {K : Type} [Field K]
  [NumberField K] [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) {P : W.toAffine.Point}
  (T : ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P) (L : ℤ) (N M0 : ℕ)
  (jU : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).U.X 1))
  (jL : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).L.X 0))
  (hjU : ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).U.d 1 2 ⋯) jU = 0)
  (hj :
    ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).res.f 1 1 ⋯)
          (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle W i hdiv hS hFull Pold P) -
        ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).ι.f 1 1 ⋯) jU =
      ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).L.d 0 1 ⋯) jL)
  (A : Matrix (Fin N) (Fin M0) ℤ_[2]) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.zeroProjectionInputFixed W i hS hFull Pold hdiv T L
          N M0 jU jL hjU hj A).zG =
      (L * (T.a - 2)) •
        ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle W i hdiv hS hFull Pold P ∧
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.zeroProjectionInputFixed W i hS hFull Pold hdiv T
            L N M0 jU jL hjU hj A).p1 =
        0 ∧
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.zeroProjectionInputFixed W i hS hFull Pold hdiv
            T L N M0 jU jL hjU hj A).dC =
        A
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.zeroProjectionInputFixed_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### emptyPartition_at

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.emptyPartition_at {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) [W.IsElliptic]
  (i : ℕ) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) :
  ZInQ.Manuscript.RC.CoefModules.urOutside ⋯ (ZMod (2 ^ i))
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i)
      (fun (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (x : ↑v ∈ S) =>
        ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralOldCondition W i ⋯ hFull ∅ v)
      v =
    ZInQ.Manuscript.RC.CoefModules.fullAt K S (ZMod (2 ^ i))
      (ZInQ.Manuscript.RC.CoefModules.InflMod ⋯ (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i))
      v
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.emptyPartition_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### emptyPartition_conditions

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.emptyPartition_conditions {K : Type} [Field K]
  [NumberField K] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ i)) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralConditions W i ⋯ hFull ∅ =
    ZInQ.Manuscript.RC.SelmerComplex.relaxedConditions (ZMod (2 ^ i)) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
      (fun (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) => ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
      (fun (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) => ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
      (ZInQ.Manuscript.RC.CoefModules.InflMod ⋯ (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.emptyPartition_conditions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### emptyPartition_data

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.emptyPartition_data {K : Type} [Field K]
  [NumberField K] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ i)) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i ⋯ hFull ∅ =
    ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S (ZMod (2 ^ i))
      (ZInQ.Manuscript.RC.CoefModules.InflMod ⋯ (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i))
      (ZInQ.Manuscript.RC.SelmerComplex.relaxedConditions (ZMod (2 ^ i)) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
        (fun (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) => ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
        (fun (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) => ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
        (ZInQ.Manuscript.RC.CoefModules.InflMod ⋯
          (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i)))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.emptyPartition_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### fullPattern_lift

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.fullPattern_lift {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) [W.IsElliptic]
  (i : ℕ) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ i))
  (z : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i ⋯ hFull ∅).G.X 1)) :
  ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i ⋯ hFull ∅).G.d 1 2 ⋯) z = 0 →
    ∃ (u : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i ⋯ hFull ∅).U.X 1)) (l :
      ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i ⋯ hFull ∅).L.X 0)),
      ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i ⋯ hFull ∅).U.d 1 2 ⋯) u = 0 ∧
        ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i ⋯ hFull ∅).res.f 1 1 ⋯) z -
            ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i ⋯ hFull ∅).ι.f 1 1 ⋯) u =
          ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i ⋯ hFull ∅).L.d 0 1 ⋯) l
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.fullPattern_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### arbitrary_model_record

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.arbitrary_model_record {K : Type} [Field K]
  [NumberField K] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ i)) [DecidableEq K]
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) {P : W.toAffine.Point}
  (T : ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P) (L : ℤ) (N M0 : ℕ) (A : Matrix (Fin N) (Fin M0) ℤ_[2]) :
  ∃ (C : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput W i ⋯ hFull ∅ hdiv T L N M0),
    C.p1 = 0 ∧ C.p0 = 0 ∧ C.dC = A ∧ C.zeta = 0 ∧ C.jay = 0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.arbitrary_model_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### positive_precision_trivial_stage

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.positive_precision_trivial_stage {K : Type} [Field K]
  [NumberField K] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [DecidableEq K] (hF : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ 1))
  (hD : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W 1) (P : W.toAffine.Point) :
  ∃ (R : ZInQ.Manuscript.RC.BaseZeroLimit.RetainedStage45 P 1 1 1 1),
    R.S = ZInQ.Manuscript.RC.BaseZeroLimit.selfStage P ∧ R.dC = 1 ∧ R.p1 = 0 ∧ R.p0 = 0 ∧ R.zeta = 0 ∧ R.jay = 0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions.positive_precision_trivial_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## PinnedConstruction.lean

### additiveCx

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.additiveCx {R : Type} [CommRing R]
  (C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx R) : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx ℤ
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.additiveCx' depends on axioms: [propext]
```

### DeformationRetractContract

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.DeformationRetractContract
  (C M : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx ℤ) (p : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom C M)
  (s : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom M C) (h : (n m : ℤ) → n = m + 1 → ↑(C.X n) →ₗ[ℤ] ↑(C.X m)) : Prop
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.DeformationRetractContract' depends on axioms: [propext,
 Quot.sound]
```

### retract_projection_surjective

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.retract_projection_surjective
  (C M : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx ℤ) (p : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom C M)
  (s : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom M C) (h : (n m : ℤ) → n = m + 1 → ↑(C.X n) →ₗ[ℤ] ↑(C.X m))
  (H : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.DeformationRetractContract C M p s h) (n : ℤ) :
  Function.Surjective ⇑(p.f n n ⋯)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.retract_projection_surjective' depends on axioms: [propext,
 Quot.sound]
```

### retract_projection_not_zero

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.retract_projection_not_zero
  (C M : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx ℤ) (p : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom C M)
  (s : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom M C) (h : (n m : ℤ) → n = m + 1 → ↑(C.X n) →ₗ[ℤ] ↑(C.X m))
  (H : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.DeformationRetractContract C M p s h) (n : ℤ)
  (x : ↑(M.X n)) (hx : x ≠ 0) : p.f n n ⋯ ≠ 0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.retract_projection_not_zero' depends on axioms: [propext,
 Quot.sound]
```

### retract_homotopy_identity

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.retract_homotopy_identity
  (C M : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx ℤ) (p : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom C M)
  (s : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom M C) (h : (n m : ℤ) → n = m + 1 → ↑(C.X n) →ₗ[ℤ] ↑(C.X m))
  (H : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.DeformationRetractContract C M p s h) (n : ℤ)
  (x : ↑(C.X n)) :
  (C.d (n - 1) n ⋯) ((h n (n - 1) ⋯) x) + (h (n + 1) n ⋯) ((C.d n (n + 1) ⋯) x) = x - (s.f n n ⋯) ((p.f n n ⋯) x)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.retract_homotopy_identity' depends on axioms: [propext,
 Quot.sound]
```

### FiniteFreeModel

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel (i : ℕ) : Type 1
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### coordinateRing_one_ne_zero

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.coordinateRing_one_ne_zero (i : ℕ) (hi : 0 < i) : 1 ≠ 0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.coordinateRing_one_ne_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ModelComparison

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison {R : Type} [CommRing R]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) {i : ℕ}
  (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i) : Type 1
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### selmerZeroPair

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.selmerZeroPair {R : Type} [CommRing R]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) :
  ↑(D.G.X 0) × ↑(D.U.X 0) →+ ↑((ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx D).X 0)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.selmerZeroPair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### selmerZeroPair_surjective

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.selmerZeroPair_surjective {R : Type} [CommRing R]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) [Subsingleton ↑(D.L.X (-1))] :
  Function.Surjective ⇑(ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.selmerZeroPair D)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.selmerZeroPair_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### selmerZeroPair_d

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.selmerZeroPair_d {R : Type} [CommRing R]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) (v : ↑(D.G.X 0)) (w : ↑(D.U.X 0)) :
  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx D).d 0 1 ⋯)
      ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.selmerZeroPair D) (v, w)) =
    ((D.G.d 0 1 ⋯) v, (D.U.d 0 1 ⋯) w, (D.res.f 0 0 ⋯) v - (D.ι.f 0 0 ⋯) w)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.selmerZeroPair_d' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### modelProjection0

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection0 {R : Type} [CommRing R]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) {i : ℕ}
  (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison D M) :
  ↑(D.G.X 0) × ↑(D.U.X 0) →+ Fin (M.rank 0) → ℤ_[2] ⧸ ZInQ.Manuscript.RC.BaseZeroLimit.twoAdicStage i
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### modelProjection1

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1 {R : Type} [CommRing R]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) {i : ℕ}
  (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison D M) :
  ↑(D.G.X 1) × ↑(D.U.X 1) × ↑(D.L.X 0) →+ Fin (M.rank 1) → ℤ_[2] ⧸ ZInQ.Manuscript.RC.BaseZeroLimit.twoAdicStage i
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### modelProjection_d

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection_d {R : Type} [CommRing R]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) {i : ℕ}
  (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison D M) (v : ↑(D.G.X 0))
  (w : ↑(D.U.X 0)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1 D M F)
      ((D.G.d 0 1 ⋯) v, (D.U.d 0 1 ⋯) w, (D.res.f 0 0 ⋯) v - (D.ι.f 0 0 ⋯) w) =
    (M.d01.map ⇑(Ideal.Quotient.mk (ZInQ.Manuscript.RC.BaseZeroLimit.twoAdicStage i))).mulVec
      ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection0 D M F) (v, w))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection_d' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### modelProjection1_surjective

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1_surjective {R : Type} [CommRing R]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) {i : ℕ}
  (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison D M) :
  Function.Surjective ⇑(ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1 D M F)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### modelProjection1_not_zero

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1_not_zero {R : Type} [CommRing R]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) {i : ℕ}
  (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison D M) (a : Fin (M.rank 1))
  (u : ℤ_[2] ⧸ ZInQ.Manuscript.RC.BaseZeroLimit.twoAdicStage i) (hu : u ≠ 0) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1 D M F ≠ 0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1_not_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### modelProjection0_surjective

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection0_surjective {R : Type} [CommRing R]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) {i : ℕ}
  (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i) [Subsingleton ↑(D.L.X (-1))]
  (F : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison D M) :
  Function.Surjective ⇑(ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection0 D M F)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection0_surjective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### modelProjection0_not_zero_of_positive_precision

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection0_not_zero_of_positive_precision {R : Type}
  [CommRing R] (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) {i : ℕ}
  (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i) [Subsingleton ↑(D.L.X (-1))]
  (F : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison D M) (hi : 0 < i)
  (hrank : 0 < M.rank 0) : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection0 D M F ≠ 0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection0_not_zero_of_positive_precision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### modelProjection1_not_zero_of_positive_precision

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1_not_zero_of_positive_precision {R : Type}
  [CommRing R] (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) {i : ℕ}
  (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison D M) (hi : 0 < i)
  (hrank : 0 < M.rank 1) : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1 D M F ≠ 0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1_not_zero_of_positive_precision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### fixedPlacesAboveTwoN

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.fixedPlacesAboveTwoN {K : Type} [Field K] (N : ℕ) :
  Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.fixedPlacesAboveTwoN' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### FixedPlacesIncluded

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FixedPlacesIncluded {K : Type} [Field K] (N : ℕ)
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) : Prop
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FixedPlacesIncluded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### dyadic_mem_fixedPlaces

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.dyadic_mem_fixedPlaces {K : Type} [Field K] (N : ℕ)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (hv : 2 ∈ v.asIdeal) :
  v ∈ ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.fixedPlacesAboveTwoN N
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.dyadic_mem_fixedPlaces' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### fixedPlacesIncluded_not_empty

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.fixedPlacesIncluded_not_empty {K : Type} [Field K] (N : ℕ)
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (H : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FixedPlacesIncluded N Pold)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (hv : 2 ∈ v.asIdeal) : Pold ≠ ∅
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.fixedPlacesIncluded_not_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### SpecifiedNormGeometry

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry {K : Type} [Field K] [DecidableEq K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (P : W.toAffine.Point) : Type 1
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### SpecifiedNormGeometry.stage

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry.stage {K : Type} [Field K]
  [DecidableEq K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) (P : W.toAffine.Point)
  (A : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry W P) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry.stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### SpecifiedNormGeometry.stage_spec

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry.stage_spec {K : Type} [Field K]
  [DecidableEq K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) (P : W.toAffine.Point)
  (A : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry W P) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry.stage W P A).Pt =
      (W.baseChange ↥A.H).toAffine.Point ∧
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry.stage W P A).Δ = Gal(↥A.H/K) ∧
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry.stage W P A).a = A.trace ∧
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry.stage W P A).incl =
            ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointInclusion W A.H ∧
          (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry.stage W P A).yr = A.yr
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry.stage_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### SpecifiedHeegnerCycle

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle {R : Type} [CommRing R]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R) : Type
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle' depends on axioms: [propext]
```

### SpecifiedFiniteHeegner

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (sourceCycle :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold)) :
  Type 1
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ConstructedClassIdentity

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ConstructedClassIdentity {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (Z :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
  (A :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor
      Z)
  (L : ℤ) : Prop
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ConstructedClassIdentity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### specifiedConstruction_partition_not_empty

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.specifiedConstruction_partition_not_empty {K : Type}
  [Field K] [NumberField K] [DecidableEq K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (Z :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
  (A :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor
      Z) :
  Pold ≠ ∅
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.specifiedConstruction_partition_not_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### specifiedConstruction_moving_not_fixed

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.specifiedConstruction_moving_not_fixed {K : Type} [Field K]
  [NumberField K] [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (Z :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
  (A :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor
      Z) :
  A.moving ∉ ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.fixedPlacesAboveTwoN conductor
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.specifiedConstruction_moving_not_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### PinnedCoordinates

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.PinnedCoordinates {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (Z :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
  (A :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor
      Z)
  (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold) M)
  (zeta jay : Fin (M.rank 1) → ℤ_[2]) : Prop
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.PinnedCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### pinnedPacket

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedPacket {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (Z :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
  (A :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor
      Z)
  (L : ℤ) (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold) M)
  (zeta jay : Fin (M.rank 1) → ℤ_[2])
  (hclass :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ConstructedClassIdentity W i hS hFull Pold hdiv P
      conductor Z A L)
  (hcoords :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.PinnedCoordinates W i hS hFull Pold hdiv P conductor Z A
      M F zeta jay) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput W i hS hFull Pold hdiv
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry.stage W P A.geometry) L (M.rank 1)
    (M.rank 0)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedPacket' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### pinnedRetainedStage

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (Z :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
  (A :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor
      Z)
  (L : ℤ) (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold) M)
  (zeta jay : Fin (M.rank 1) → ℤ_[2])
  (hclass :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ConstructedClassIdentity W i hS hFull Pold hdiv P
      conductor Z A L)
  (hcoords :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.PinnedCoordinates W i hS hFull Pold hdiv P conductor Z A
      M F zeta jay) :
  ZInQ.Manuscript.RC.BaseZeroLimit.RetainedStage45 P L i (M.rank 1) (M.rank 0)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### pinnedRetainedStage_spec

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage_spec {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (Z :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
  (A :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor
      Z)
  (L : ℤ) (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold) M)
  (zeta jay : Fin (M.rank 1) → ℤ_[2])
  (hclass :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ConstructedClassIdentity W i hS hFull Pold hdiv P
      conductor Z A L)
  (hcoords :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.PinnedCoordinates W i hS hFull Pold hdiv P conductor Z A
      M F zeta jay) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A
          L M F zeta jay hclass hcoords).S =
      ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedNormGeometry.stage W P A.geometry ∧
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z
            A L M F zeta jay hclass hcoords).zG =
        Z.zG ∧
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P conductor
              Z A L M F zeta jay hclass hcoords).zU =
          Z.zU ∧
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P
                conductor Z A L M F zeta jay hclass hcoords).p1 =
            ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection1
              (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold) M F ∧
          (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P
                  conductor Z A L M F zeta jay hclass hcoords).p0 =
              ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.modelProjection0
                (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold) M F ∧
            (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P
                    conductor Z A L M F zeta jay hclass hcoords).dC =
                M.d01 ∧
              (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P
                      conductor Z A L M F zeta jay hclass hcoords).zeta =
                  zeta ∧
                (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P
                      conductor Z A L M F zeta jay hclass hcoords).jay =
                  jay
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### pinnedRetainedStage_projection_not_zero

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage_projection_not_zero {K : Type} [Field K]
  [NumberField K] [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (Z :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
  (A :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor
      Z)
  (L : ℤ) (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold) M)
  (zeta jay : Fin (M.rank 1) → ℤ_[2])
  (hclass :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ConstructedClassIdentity W i hS hFull Pold hdiv P
      conductor Z A L)
  (hcoords :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.PinnedCoordinates W i hS hFull Pold hdiv P conductor Z A
      M F zeta jay)
  (a : Fin (M.rank 1)) (u : ℤ_[2] ⧸ ZInQ.Manuscript.RC.BaseZeroLimit.twoAdicStage i) (hu : u ≠ 0) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A
        L M F zeta jay hclass hcoords).p1 ≠
    0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage_projection_not_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### pinnedRetainedStage_projections_not_zero

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage_projections_not_zero {K : Type} [Field K]
  [NumberField K] [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (Z :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
  (A :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor
      Z)
  (L : ℤ) (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold) M)
  (zeta jay : Fin (M.rank 1) → ℤ_[2])
  (hclass :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ConstructedClassIdentity W i hS hFull Pold hdiv P
      conductor Z A L)
  (hcoords :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.PinnedCoordinates W i hS hFull Pold hdiv P conductor Z A
      M F zeta jay)
  (hi : 0 < i) (h0 : 0 < M.rank 0) (h1 : 0 < M.rank 1) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A
          L M F zeta jay hclass hcoords).p0 ≠
      0 ∧
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z
          A L M F zeta jay hclass hcoords).p1 ≠
      0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage_projections_not_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### pinnedRetainedStage_source_not_replaced

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage_source_not_replaced {K : Type} [Field K]
  [NumberField K] [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (Z :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
  (A :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor
      Z)
  (L : ℤ) (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold) M)
  (zeta jay : Fin (M.rank 1) → ℤ_[2])
  (hclass :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ConstructedClassIdentity W i hS hFull Pold hdiv P
      conductor Z A L)
  (hcoords :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.PinnedCoordinates W i hS hFull Pold hdiv P conductor Z A
      M F zeta jay)
  (hc :
    Z.zG ≠
      (L * (A.geometry.trace - 2)) •
        ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle W i hdiv hS hFull Pold P) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage W i hS hFull Pold hdiv P conductor Z A
        L M F zeta jay hclass hcoords).zG ≠
    (L * (A.geometry.trace - 2)) •
      ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle W i hdiv hS hFull Pold P
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage_source_not_replaced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### pinnedRetainedStage_exists_witness

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage_exists_witness {K : Type} [Field K]
  [NumberField K] [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (conductor : ℕ)
  (Z :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedHeegnerCycle
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
  (A :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.SpecifiedFiniteHeegner W i hS hFull Pold hdiv P conductor
      Z)
  (L : ℤ) (M : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.FiniteFreeModel i)
  (F :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ModelComparison
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold) M)
  (zeta jay : Fin (M.rank 1) → ℤ_[2])
  (hclass :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.ConstructedClassIdentity W i hS hFull Pold hdiv P
      conductor Z A L)
  (hcoords :
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.PinnedCoordinates W i hS hFull Pold hdiv P conductor Z A
      M F zeta jay) :
  ∃ (v : Fin (M.rank 0) → ℤ_[2]),
    ∀ (a : Fin (M.rank 1)),
      zeta a - ↑(L * (A.geometry.trace - 2)) * jay a - M.d01.mulVec v a ∈
        ZInQ.Manuscript.RC.BaseZeroLimit.twoAdicStage i
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned.pinnedRetainedStage_exists_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Unchanged mathematical declarations

The 116 named declarations of the corrected original source were freshly audited. All 68 theorem statements are unchanged. The complete current output is in `audit-review-Identification.log`; `COMMENT_ONLY.diff` records the scope corrections.
