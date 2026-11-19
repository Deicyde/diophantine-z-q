# Exact theorem statements and kernel dependencies

The statements and dependency reports below are verbatim compiler output for the final source. Function-binder types are displayed. The symbol `⋯` suppresses proof arguments only; no logical hypothesis has been removed. The additional definition entries report their types, not expanded definition bodies. The source contains every body and the complete typed input records.

## Theorems

### actualKummerAt_localFacts

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.actualKummerAt_localFacts {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) [W.IsElliptic]
  (i : ℕ) (s : ZInQ.Manuscript.RC.CoefModules.KS K S) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (hα : ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) ↑v) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.LocalFacts
    (ZInQ.Manuscript.RC.KummerMaps.actualKummerAt W i s hs hs0 α hFull v hα).i
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.actualKummerAt_localFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### actualKummerAtS_localFacts

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.actualKummerAtS_localFacts {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (hα : ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) ↑v) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.LocalFacts
    (ZInQ.Manuscript.RC.KummerMaps.actualKummerAtS hS W i s hs hs0 α hFull v hα).i
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.actualKummerAtS_localFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### kummerIotaS_injective

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerIotaS_injective {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i)) (hi : i ≠ 0)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) :
  Function.Injective ⇑(ZInQ.Manuscript.RC.KummerMaps.kummerIotaS hS W i s hs hs0 α hFull v)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerIotaS_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### cocycleCondAt_congr

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cocycleCondAt_congr {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (hS : S0 ⊆ S) (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (Z Z' :
    Submodule (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
      ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
          (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
          (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
            (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α))
          1))
  (hZ :
    ∀ z ∈ Z,
      (ZInQ.Manuscript.RC.CoefModules.contD (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
            (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
            (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
              (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α))
            1)
          z =
        0)
  (hZ' :
    ∀ z ∈ Z',
      (ZInQ.Manuscript.RC.CoefModules.contD (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
            (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
            (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
              (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α))
            1)
          z =
        0)
  (he : Z = Z') :
  { U := ZInQ.Manuscript.RC.CoefModules.cocycleCondition Z hZ,
      i := ZInQ.Manuscript.RC.CoefModules.cocycleConditionι Z hZ } =
    { U := ZInQ.Manuscript.RC.CoefModules.cocycleCondition Z' hZ',
      i := ZInQ.Manuscript.RC.CoefModules.cocycleConditionι Z' hZ' }
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cocycleCondAt_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### actualKummerAtS_range_eq_span

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.actualKummerAtS_range_eq_span {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (hα : ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) ↑v) :
  (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap
          (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC
            (ZInQ.Manuscript.RC.KummerMaps.actualKummerAtS hS W i s hs hs0 α hFull v hα).i)
          1)).range =
    Submodule.span (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
      (Set.range ⇑(ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.actualKummerMapS W i hS s hs hs0 α hFull v hα))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.actualKummerAtS_range_eq_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### fixedKummerSpan_cocycle

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.fixedKummerSpan_cocycle {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hα : ∀ v ∈ P, ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) v)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (z :
    ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
        (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
        (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
          (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α))
        1)) :
  z ∈ ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.fixedKummerSpan W i hS s hs hs0 α hFull P v →
    (ZInQ.Manuscript.RC.CoefModules.contD (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
          (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
          (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
            (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α))
          1)
        z =
      0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.fixedKummerSpan_cocycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### kummerFullSelData_eq_mixed

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_eq_mixed {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hα :
    ∀ v ∈ P, ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) v) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData W i hS s hs hs0 α hFull P hα =
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.mixedStageSelData hS W i α
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.fixedFullPlaces P)
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.fixedKummerSpan W i hS s hs hs0 α hFull P) ⋯
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_eq_mixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### kummerFullSelData_localFacts

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_localFacts {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hα :
    ∀ v ∈ P, ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) v) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.LocalFacts
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData W i hS s hs hs0 α hFull P hα).ι
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_localFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### kummerFullSelData_eq_galois

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_eq_galois {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hα :
    ∀ v ∈ P, ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) v) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData W i hS s hs hs0 α hFull P hα =
    ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
      (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α)
      (ZInQ.Manuscript.RC.CoefModules.actualConditions hS W i α
        fun (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (x : ↑v ∈ S0) =>
        if hP : ↑v ∈ P then ZInQ.Manuscript.RC.KummerMaps.actualKummerAtS hS W i s hs hs0 α hFull v ⋯
        else
          ZInQ.Manuscript.RC.CoefModules.fullAt K S (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
            (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α) v)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_eq_galois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### kummerFullSelData_global_X

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_global_X {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hα : ∀ v ∈ P, ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) v)
  (n : ℕ) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData W i hS s hs hs0 α hFull P hα).G.X ↑n =
    ↧↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
          (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α) n)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_global_X' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### kummerFullSelData_local_X

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_local_X {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hα : ∀ v ∈ P, ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) v)
  (n : ℕ) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData W i hS s hs hs0 α hFull P hα).L.X ↑n =
    ↧((v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) →
        ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
            (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
            (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
              (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α))
            n))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_local_X' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### kummerFullSelData_res_apply

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_res_apply {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hα : ∀ v ∈ P, ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) v)
  (n : ℕ)
  (c : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData W i hS s hs hs0 α hFull P hα).G.X ↑n))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) :
  ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData W i hS s hs hs0 α hFull P hα).res.f ↑n ↑n ⋯) c
      v =
    (ModuleCat.Hom.hom
        ((ZInQ.Manuscript.RC.SelmerComplex.resCochains (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)).f n))
      c
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_res_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### kummerFullSelData_isGalois

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_isGalois {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S) (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hα : ∀ v ∈ P, ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i α (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) v)
  (hSfin : S.Finite) :
  ZInQ.Manuscript.RC.Wiring.IsGaloisSelData
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData W i hS s hs hs0 α hFull P hα)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.kummerFullSelData_isGalois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### geometricPointInclusion_injective

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointInclusion_injective {K : Type} [Field K]
  [DecidableEq K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) :
  Function.Injective ⇑(ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointInclusion W H)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointInclusion_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### geometricSplitNormStage_spec

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricSplitNormStage_spec {K : Type} [Field K] [DecidableEq K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) [FiniteDimensional K ↥H]
  (hAb : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.AbelianStageExtension H) (N : Subgroup Gal(↥H/K))
  (Q : Finset Gal(↥H/K)) (hQ : ∀ (δ : Gal(↥H/K)), ∃! t : Gal(↥H/K), t ∈ Q ∧ t⁻¹ * δ ∈ N)
  (y1 yr : (W.baseChange ↥H).toAffine.Point)
  (hy1 : ∀ n ∈ N, ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointAction W H) n) y1 = y1) (a : ℤ)
  (σ : Gal(↥H/K))
  (hnorm : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GeometricSplitNormRelation W H N y1 yr a σ)
  (P : W.toAffine.Point)
  (hP :
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointInclusion W H) P =
      ∑ t ∈ Q, ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointAction W H) t) y1) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricSplitNormStage W H hAb N Q hQ y1 yr hy1 a σ hnorm P
          hP).Pt =
      (W.baseChange ↥H).toAffine.Point ∧
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricSplitNormStage W H hAb N Q hQ y1 yr hy1 a σ hnorm P
            hP).Δ =
        Gal(↥H/K) ∧
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricSplitNormStage W H hAb N Q hQ y1 yr hy1 a σ hnorm P
              hP).incl =
          ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointInclusion W H ∧
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricSplitNormStage W H hAb N Q hQ y1 yr hy1 a σ hnorm
                P hP).act =
            ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointAction W H ∧
          (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricSplitNormStage W H hAb N Q hQ y1 yr hy1 a σ
                hnorm P hP).W =
            (a - 2) • P
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricSplitNormStage_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### finiteStageCharacter_isOpenKer

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter_isOpenKer {K : Type} [Field K] [NumberField K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (i : ℕ)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) [Normal K ↥H] [FiniteDimensional K ↥H]
  (ξ : Gal(↥H/K) →* Multiplicative (ZMod (2 ^ (2 * i)))) :
  ZInQ.Manuscript.RC.CoefModules.IsOpenKer
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter i s hs hs0 H ξ)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter_isOpenKer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### finiteStageCharacter_localType

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter_localType {K : Type} [Field K] [NumberField K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (i : ℕ)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) [Normal K ↥H]
  (ξ : Gal(↥H/K) →* Multiplicative (ZMod (2 ^ (2 * i))))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hξ : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.FiniteCharacterOldType i H ξ P)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
  v ∈ P →
    ZInQ.Manuscript.RC.KummerMaps.IsLocallyQuadAt i
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter i s hs hs0 H ξ)
      (ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) v
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter_localType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### finiteStageSelData_localFacts

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageSelData_localFacts {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (i : ℕ)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) [Normal K ↥H] [FiniteDimensional K ↥H]
  (ξ : Gal(↥H/K) →* Multiplicative (ZMod (2 ^ (2 * i))))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (hS : S0 ⊆ S) (W : WeierstrassCurve K)
  [W.IsElliptic] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (hξ : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.FiniteCharacterOldType i H ξ P) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.LocalFacts
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageSelData i s hs hs0 H ξ P hS W hFull hξ).ι
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageSelData_localFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### baseSqrt_sq

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.baseSqrt_sq {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} :
  1 ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) 1
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.baseSqrt_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### baseQuadChar_eq_one

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.baseQuadChar_eq_one {K : Type} [Field K] [NumberField K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} :
  ZInQ.Manuscript.RC.CoefModules.quadChar 1 ⋯ ⋯ = 1
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.baseQuadChar_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### acoefConst_tA

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.acoefConst_tA (i : ℕ) (hi : i ≠ 0) :
  (ZInQ.Manuscript.RC.KummerMaps.acoefConst i hi) (ZInQ.Manuscript.RC.HeegnerAlgebra.tA i) = 0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.acoefConst_tA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### acoefConst_movingChar

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.acoefConst_movingChar {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (i : ℕ) (hi : i ≠ 0)
  (ξ : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* Multiplicative (ZMod (2 ^ (2 * i))))
  (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0) :
  (ZInQ.Manuscript.RC.KummerMaps.acoefConst i hi) ↑((ZInQ.Manuscript.RC.CoefModules.movingCharS i ξ) g) = 1
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.acoefConst_movingChar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### finiteStageCharacter_at_base_const

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter_at_base_const {K : Type} [Field K]
  [NumberField K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (i : ℕ) (hi : i ≠ 0)
  (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) [Normal K ↥H] [FiniteDimensional K ↥H]
  (ξ : Gal(↥H/K) →* Multiplicative (ZMod (2 ^ (2 * i)))) (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0) :
  (ZInQ.Manuscript.RC.KummerMaps.acoefConst i hi)
      ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter i 1 ⋯ ⋯ H ξ) g) =
    1
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter_at_base_const' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralEval_pos

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval_pos (i : ℕ) (hi : i ≠ 0) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval i = ZInQ.Manuscript.RC.KummerMaps.acoefConst i hi
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### finiteStageCharacter_at_base_central

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter_at_base_central {K : Type} [Field K]
  [NumberField K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (i : ℕ)
  (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) [Normal K ↥H] [FiniteDimensional K ↥H]
  (ξ : Gal(↥H/K) →* Multiplicative (ZMod (2 ^ (2 * i)))) (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval i)
      ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter i 1 ⋯ ⋯ H ξ) g) =
    1
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter_at_base_central' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralEval_mk

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval_mk (i : ℕ) (p : Polynomial (ZMod (2 ^ i))) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval i)
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.X ^ i})) p) =
    p.coeff 0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval_mk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralEval_scalarSection

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval_scalarSection (i : ℕ) (a : ZMod (2 ^ i)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval i)
      ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralScalarSection i) a) =
    a
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval_scalarSection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralEval_tA

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval_tA (i : ℕ) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval i) (ZInQ.Manuscript.RC.HeegnerAlgebra.tA i) = 0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval_tA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### coefficient_central_decomposition

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.coefficient_central_decomposition (i : ℕ)
  (a : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) :
  ∃ (b : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i),
    a =
      ZInQ.Manuscript.RC.HeegnerAlgebra.tA i * b +
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralScalarSection i)
          ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval i) a)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.coefficient_central_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralCoeffProjection_tmul

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_tmul {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  (a : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (t : ZInQ.Manuscript.RC.CoefModules.TorsS K S0 W ↑(2 ^ i)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α)
      ((ZInQ.Manuscript.RC.CoefModules.CoefMod.equiv (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) α
          (ZInQ.Manuscript.RC.CoefModules.TorsS K S0 W ↑(2 ^ i)))
        (a ⊗ₜ[ℤ] t)) =
    (ZInQ.Manuscript.RC.CoefModules.CoefMod.equiv (ZMod (2 ^ i)) 1
        (ZInQ.Manuscript.RC.CoefModules.TorsS K S0 W ↑(2 ^ i)))
      ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval i) a ⊗ₜ[ℤ] t)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_tmul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralCoeffProjection_oneTmul

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_oneTmul {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  (t : ZInQ.Manuscript.RC.CoefModules.TorsS K S0 W ↑(2 ^ i)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α)
      ((ZInQ.Manuscript.RC.KummerMaps.oneTmul (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) α
          (ZInQ.Manuscript.RC.CoefModules.TorsS K S0 W ↑(2 ^ i)))
        t) =
    (ZInQ.Manuscript.RC.KummerMaps.oneTmul (ZMod (2 ^ i)) 1 (ZInQ.Manuscript.RC.CoefModules.TorsS K S0 W ↑(2 ^ i))) t
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_oneTmul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralCoeffProjection_galois

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_galois {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  (hα :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0),
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval i) ↑(α g) = 1)
  (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0) (m : ZInQ.Manuscript.RC.CoefModules.Mcoef K S0 W i α) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α) (g • m) =
    g • (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α) m
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_galois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralCoeffProjection_section

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_section {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  (m : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α)
      ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffSection W i α) m) =
    m
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_section' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralCoeffProjection_smul

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_smul {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  (a : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) (m : ZInQ.Manuscript.RC.CoefModules.Mcoef K S0 W i α) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α) (a • m) =
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval i) a •
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α) m
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralCoeff_decomposition

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeff_decomposition {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  (m : ZInQ.Manuscript.RC.CoefModules.Mcoef K S0 W i α) :
  ∃ (b : ZInQ.Manuscript.RC.CoefModules.Mcoef K S0 W i α),
    m =
      ZInQ.Manuscript.RC.HeegnerAlgebra.tA i • b +
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffSection W i α)
          ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α) m)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeff_decomposition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralCoeffProjection_eq_zero_iff

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_eq_zero_iff {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  (m : ZInQ.Manuscript.RC.CoefModules.Mcoef K S0 W i α) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α) m = 0 ↔
    ∃ (b : ZInQ.Manuscript.RC.CoefModules.Mcoef K S0 W i α), ZInQ.Manuscript.RC.HeegnerAlgebra.tA i • b = m
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralCoeffProjection_ker

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_ker {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α).ker =
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralMovingImage W i α).toAddSubgroup
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection_ker' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralCoeffQuotientEquiv_mk

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffQuotientEquiv_mk {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  (m : ZInQ.Manuscript.RC.CoefModules.Mcoef K S0 W i α) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffQuotientEquiv W i α) ↑m =
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α) m
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffQuotientEquiv_mk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralCoeffQuotientEquiv_galois

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffQuotientEquiv_galois {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) [Normal K ↥H]
  [FiniteDimensional K ↥H] (ξ : Gal(↥H/K) →* Multiplicative (ZMod (2 ^ (2 * i))))
  (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0)
  (m :
    ZInQ.Manuscript.RC.CoefModules.Mcoef K S0 W i
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter i 1 ⋯ ⋯ H ξ)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffQuotientEquiv W i
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter i 1 ⋯ ⋯ H ξ))
      ↑(g • m) =
    g •
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffQuotientEquiv W i
          (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageCharacter i 1 ⋯ ⋯ H ξ))
        ↑m
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffQuotientEquiv_galois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralOneTmul_bijective

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralOneTmul_bijective {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ) :
  Function.Bijective
    ⇑(ZInQ.Manuscript.RC.KummerMaps.oneTmul (ZMod (2 ^ i)) 1 (ZInQ.Manuscript.RC.CoefModules.TorsS K S0 W ↑(2 ^ i)))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralOneTmul_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralKummerIotaS_from_actual

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS_from_actual {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (t :
    ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
      (ZInQ.Manuscript.RC.KummerMaps.localTwist W 1 ↑v) (2 ^ i)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffProjection W i α)
      ((ZInQ.Manuscript.RC.KummerMaps.kummerIotaS hS W i 1 ⋯ ⋯ α hFull v) t) =
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS W i hS hFull v) t
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS_from_actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralKummerIotaS_smul

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS_smul {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (g : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
  (t :
    ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
      (ZInQ.Manuscript.RC.KummerMaps.localTwist W 1 ↑v) (2 ^ i)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS W i hS hFull v) (g • t) =
    g • (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS W i hS hFull v) t
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralKummerIotaS_bijective

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS_bijective {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) :
  Function.Bijective ⇑(ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS W i hS hFull v)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### localCochainProjection_smul

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.localCochainProjection_smul {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S0 ⊆ S)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (n : ℕ)
  (a : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
  (c :
    ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
        (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
        (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
          (ZInQ.Manuscript.RC.CoefModules.MinS hS W i α))
        n)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.localCochainProjection W i hS α v n) (a • c) =
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval i) a •
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.localCochainProjection W i hS α v n) c
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.localCochainProjection_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### localCochainProjection_kummer

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.localCochainProjection_kummer {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S)
  (a : ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
  (p : (ZInQ.Manuscript.RC.KummerMaps.localTwist W 1 ↑v).toAffine.Point) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.localCochainProjection W i hS α v 1)
      (ZInQ.Manuscript.RC.CoefModules.kummerCocycleIn (ZInQ.Manuscript.RC.KummerMaps.kummerIotaS hS W i 1 ⋯ ⋯ α hFull v)
        a p) =
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval i) a •
      ZInQ.Manuscript.RC.CoefModules.kummerCocycleIn
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS W i hS hFull v) 1 p
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.localCochainProjection_kummer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### localKummerSpan_projection

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.localKummerSpan_projection {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ)
  [ZInQ.Manuscript.RC.CoefModules.IsOpenKer α] (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) :
  (Set.range
      fun
        (z :
          ↥(ZInQ.Manuscript.RC.CoefModules.kummerZ' (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
              (ZInQ.Manuscript.RC.KummerMaps.kummerIotaS hS W i 1 ⋯ ⋯ α hFull v))) =>
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.localCochainProjection W i hS α v 1) ↑z) =
    ↑(ZInQ.Manuscript.RC.CoefModules.kummerZ' (ZMod (2 ^ i))
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerIotaS W i hS hFull v))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.localKummerSpan_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralKummerAt_localFacts

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerAt_localFacts {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.LocalFacts
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerAt W i hS hFull v).i
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerAt_localFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralKummerAt_range_eq_span

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerAt_range_eq_span {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) :
  (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap
          (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC
            (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerAt W i hS hFull v).i)
          1)).range =
    Submodule.span (ZMod (2 ^ i))
      (Set.range ⇑(ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralLocalKummerMap W i hS hFull v))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerAt_range_eq_span' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralSelData_localFacts

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData_localFacts {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Local.LocalFacts
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).ι
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData_localFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralSelData_global_X

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData_global_X {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).G.X ↑n =
    ↧↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain (ZMod (2 ^ i)) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
          (ZInQ.Manuscript.RC.CoefModules.InflMod hS
            (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i))
          n)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData_global_X' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralSelData_local_X

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData_local_X {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (n : ℕ) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).L.X ↑n =
    ↧((v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) →
        ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain (ZMod (2 ^ i)) (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
            (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K S ↑v)
              (ZInQ.Manuscript.RC.CoefModules.InflMod hS
                (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i)))
            n))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData_local_X' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralSelData_localHypotheses

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData_localHypotheses {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
  (∀ (c : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).L.X 0)),
      ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).L.d 0 1 ⋯) c = 0 →
        ∃ (w : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).U.X 0)),
          ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).U.d 0 1 ⋯) w = 0 ∧
            ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).ι.f 0 0 ⋯) w = c) ∧
    ∀ (u : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).U.X 1)),
      ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).U.d 1 2 ⋯) u = 0 →
        (∃ (c : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).L.X 0)),
            ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).ι.f 1 1 ⋯) u =
              ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).L.d 0 1 ⋯) c) →
          ∃ (w : ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).U.X 0)),
            ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull P).U.d 0 1 ⋯) w = u
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData_localHypotheses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### cochainClass_eq_zero_iff

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClass_eq_zero_iff {k : Type} [CommRing k]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData k) (c : ↑(D.G.X 1)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClass D) c = 0 ↔ ∃ (g : ↑(D.G.X 0)), (D.G.d 0 1 ⋯) g = c
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClass_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### cohomologyToClasses_injective

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cohomologyToClasses_injective {k : Type} [CommRing k]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData k) :
  Function.Injective ⇑(ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cohomologyToClasses D)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cohomologyToClasses_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### cohomologyToClasses_π

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cohomologyToClasses_π {k : Type} [CommRing k]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData k) (c : ↑(HomologicalComplex.cycles D.G.toCC 1)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cohomologyToClasses D)
      ((ModuleCat.Hom.hom (HomologicalComplex.homologyπ D.G.toCC 1)) c) =
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClass D)
      ((ModuleCat.Hom.hom (HomologicalComplex.iCycles D.G.toCC 1)) c)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cohomologyToClasses_π' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### cochainClasses_eq_iff_homology

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClasses_eq_iff_homology {k : Type} [CommRing k]
  (D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData k) (c c' : ↑(HomologicalComplex.cycles D.G.toCC 1)) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClass D)
        ((ModuleCat.Hom.hom (HomologicalComplex.iCycles D.G.toCC 1)) c) =
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClass D)
        ((ModuleCat.Hom.hom (HomologicalComplex.iCycles D.G.toCC 1)) c') ↔
    (ModuleCat.Hom.hom (HomologicalComplex.homologyπ D.G.toCC 1)) c =
      (ModuleCat.Hom.hom (HomologicalComplex.homologyπ D.G.toCC 1)) c'
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClasses_eq_iff_homology' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### supportBasePoint_fixed

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportBasePoint_fixed {K : Type} [Field K] [DecidableEq K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0) (P : W.toAffine.Point) :
  g • (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportBasePoint W) P =
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportBasePoint W) P
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportBasePoint_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### supportDivisionPoint_spec

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportDivisionPoint_spec {K : Type} [Field K] [DecidableEq K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i)
  (P : W.toAffine.Point) :
  2 ^ i • ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportDivisionPoint W i hdiv P =
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportBasePoint W) P
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportDivisionPoint_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### supportTorsionCoefficient_smul

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportTorsionCoefficient_smul {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (g : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0)
  (t : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.SupportTorsion W i) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportTorsionCoefficient W i) (g • t) =
    g • (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportTorsionCoefficient W i) t
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportTorsionCoefficient_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### supportKummerDifference_mul

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerDifference_mul {K : Type} [Field K] [DecidableEq K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) (P : W.toAffine.Point)
  (g g' : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerDifference W i hdiv P (g * g') =
    g • ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerDifference W i hdiv P g' +
      ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerDifference W i hdiv P g
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerDifference_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### supportKummerDifference_continuous

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerDifference_continuous {K : Type} [Field K]
  [NumberField K] [DecidableEq K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) (i : ℕ)
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i)
  (P : W.toAffine.Point) :
  Continuous (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerDifference W i hdiv P)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerDifference_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### supportKummerCocycle_closed

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerCocycle_closed {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) (i : ℕ)
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i)
  (P : W.toAffine.Point) :
  (ZInQ.Manuscript.RC.CoefModules.contD (ZMod (2 ^ i)) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S0)
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i) 1)
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerCocycle W i hdiv P) =
    0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerCocycle_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### supportKummerCocycle_add

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerCocycle_add {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) (i : ℕ)
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i)
  (P P' : W.toAffine.Point) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerCocycle W i hdiv (P + P') -
        ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerCocycle W i hdiv P -
      ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerCocycle W i hdiv P' ∈
    ZInQ.Manuscript.RC.CoefModules.contB1 (ZMod (2 ^ i)) (ZInQ.Manuscript.RC.SelmerComplex.GKS K S0)
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportKummerCocycle_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### globalKummerCocycle_closed

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle_closed {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) (i : ℕ)
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S0 ⊆ S) [W.IsElliptic]
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (P : W.toAffine.Point) :
  ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).G.d 1 2 ⋯)
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle W i hdiv hS hFull Pold P) =
    0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### globalKummerCocycle_add

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle_add {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) (i : ℕ)
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S0 ⊆ S) [W.IsElliptic]
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (P P' : W.toAffine.Point) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle W i hdiv hS hFull Pold (P + P') -
        ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle W i hdiv hS hFull Pold P -
      ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle W i hdiv hS hFull Pold P' ∈
    ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).G.d 0 1 ⋯).range
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### globalKummerMap_apply

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerMap_apply {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) (i : ℕ)
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S0 ⊆ S) [W.IsElliptic]
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (P : W.toAffine.Point) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerMap W i hdiv hS hFull Pold) P =
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClass
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold))
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerCocycle W i hdiv hS hFull Pold P)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerMap_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralRetainedStage_spec

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage_spec {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) {P : W.toAffine.Point}
  (T : ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P) (L : ℤ) (N M0 : ℕ)
  (C : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput W i hS hFull Pold hdiv T L N M0) :
  (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).S = T ∧
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).G1 =
        ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).G.X 1) ∧
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage W i hS hFull Pold hdiv T L N M0 C).U1 =
          ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).U.X 1) ∧
        (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage W i hS hFull Pold hdiv T L N M0
                C).L0 =
            ↑((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).L.X 0) ∧
          (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage W i hS hFull Pold hdiv T L N M0
                  C).loc0 =
              ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).res.f 0 0
                  ⋯).toAddMonoidHom ∧
            (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage W i hS hFull Pold hdiv T L N M0
                    C).ι0 =
                ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold).ι.f 0 0
                    ⋯).toAddMonoidHom ∧
              (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage W i hS hFull Pold hdiv T L N M0
                      C).δ =
                  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerMap W i hdiv hS hFull Pold ∧
                (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage W i hS hFull Pold hdiv T L N
                      M0 C).cls =
                  ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClass
                    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralRetainedStage_exists_witness

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage_exists_witness {K : Type} [Field K]
  [NumberField K] [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) {P : W.toAffine.Point}
  (T : ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P) (L : ℤ) (N M0 : ℕ)
  (C : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput W i hS hFull Pold hdiv T L N M0) :
  ∃ (v : Fin M0 → ℤ_[2]),
    ∀ (a : Fin N),
      C.zeta a - ↑(L * (T.a - 2)) * C.jay a - C.dC.mulVec v a ∈ ZInQ.Manuscript.RC.BaseZeroLimit.twoAdicStage i
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage_exists_witness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Additional definitions

### geometricSplitNormStage

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricSplitNormStage {K : Type} [Field K] [DecidableEq K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) [FiniteDimensional K ↥H]
  (hAb : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.AbelianStageExtension H) (N : Subgroup Gal(↥H/K))
  (Q : Finset Gal(↥H/K)) (hQ : ∀ (δ : Gal(↥H/K)), ∃! t : Gal(↥H/K), t ∈ Q ∧ t⁻¹ * δ ∈ N)
  (y1 yr : (W.baseChange ↥H).toAffine.Point)
  (hy1 : ∀ n ∈ N, ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointAction W H) n) y1 = y1) (a : ℤ)
  (σ : Gal(↥H/K))
  (hnorm : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GeometricSplitNormRelation W H N y1 yr a σ)
  (P : W.toAffine.Point)
  (hP :
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointInclusion W H) P =
      ∑ t ∈ Q, ((ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricPointAction W H) t) y1) :
  ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.geometricSplitNormStage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### finiteStageSelData

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageSelData {K : Type} [Field K] [NumberField K]
  {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (i : ℕ)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S0) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) h) (hs0 : s ≠ 0)
  (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) [Normal K ↥H] [FiniteDimensional K ↥H]
  (ξ : Gal(↥H/K) →* Multiplicative (ZMod (2 ^ (2 * i))))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (hS : S0 ⊆ S) (W : WeierstrassCurve K)
  [W.IsElliptic] (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (hξ : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.FiniteCharacterOldType i H ξ P) :
  ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.finiteStageSelData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralEval

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval (i : ℕ) :
  ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i →+* ZMod (2 ^ i)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralEval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralCoeffQuotientEquiv

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffQuotientEquiv {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (α : ZInQ.Manuscript.RC.SelmerComplex.GKS K S0 →* (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)ˣ) :
  ZInQ.Manuscript.RC.CoefModules.Mcoef K S0 W i α ⧸
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralMovingImage W i α).toAddSubgroup ≃+
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralCoeffQuotientEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralKummerAt

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerAt {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) :
  ZInQ.Manuscript.RC.CoefModules.CondAt K S (ZMod (2 ^ i))
    (ZInQ.Manuscript.RC.CoefModules.InflMod hS (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralCoeff W i)) v
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralKummerAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralSelData

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  [NumberField K] [W.IsElliptic] {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (hS : S0 ⊆ S) (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
  ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (ZMod (2 ^ i))
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### globalKummerMap

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerMap {K : Type} [Field K] [NumberField K] [DecidableEq K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ)
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i)
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S0 ⊆ S) [W.IsElliptic]
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
  W.toAffine.Point →+
    ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClasses
      (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS hFull Pold)
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.globalKummerMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### centralRetainedStage

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) {P : W.toAffine.Point}
  (T : ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P) (L : ℤ) (N M0 : ℕ)
  (C : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput W i hS hFull Pold hdiv T L N M0) :
  ZInQ.Manuscript.RC.BaseZeroLimit.RetainedStage45 P L i N M0
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralRetainedStage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### GlobalDivisionPointsInSupport

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport {K : Type} [Field K] [DecidableEq K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K) (i : ℕ) : Prop
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### AbelianStageExtension

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.AbelianStageExtension {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) : Prop
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.AbelianStageExtension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### GeometricSplitNormRelation

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GeometricSplitNormRelation {K : Type} [Field K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) [FiniteDimensional K ↥H] (N : Subgroup Gal(↥H/K))
  (y1 yr : (W.baseChange ↥H).toAffine.Point) (a : ℤ) (σ : Gal(↥H/K)) : Prop
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GeometricSplitNormRelation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### FiniteCharacterOldType

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.FiniteCharacterOldType {K : Type} [Field K] [NumberField K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (i : ℕ)
  (H : IntermediateField K (ZInQ.Manuscript.RC.CoefModules.KS K S0)) [Normal K ↥H]
  (ξ : Gal(↥H/K) →* Multiplicative (ZMod (2 ^ (2 * i))))
  (P : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) : Prop
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.FiniteCharacterOldType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### CentralRetainedInput

```lean
ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput {K : Type} [Field K] [NumberField K]
  [DecidableEq K] {S S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (hS : S0 ⊆ S)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i))
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (hdiv : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i) {P : W.toAffine.Point}
  (T : ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P) (L : ℤ) (N M0 : ℕ) : Type
```

```text
'ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

