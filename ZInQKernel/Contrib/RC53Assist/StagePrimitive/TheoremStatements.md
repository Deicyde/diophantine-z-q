# Exact theorem statements and axiom outputs

The following types and axiom reports are copied from the successful single-file check of the final source. Full names, universes, and proof arguments are retained. The source SHA-256 is `dc84d78a5bc66ecdceae7dd6af52055e6fe5c2adf9666e72af74d250bd2aba44`.

There are 26 theorems and 21 other named declarations. All 47 axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The full source accompanies this inventory, including every input-record field and all explicit binder annotations.

## Theorems

### `ZInQ.Contrib.RC53Assist.StagePrimitive.genuineClassVec_ne_zero_iff`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.genuineClassVec_ne_zero_iff (K : Type) [Field.{0} K] [NumberField.{0} K]
  (S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))) (A : Type) [CommRing.{0} A]
  (M : Type) [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  (Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M)
  (R : ZInQ.Contrib.RC53Assist.StageCone.GenuineTwoTermRealization K S A M Delta)
  (z :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        1))
  (hz :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
          1 2 rfl.{1})
        z)
      0) :
  Ne.{1} (ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.classVec R z hz) 0 ↔
    ∀
      (y :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
            0)),
      Ne.{1}
        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
            0 1 rfl.{1})
          y)
        z
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.genuineClassVec_ne_zero_iff' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.genuineClass_not_torsion_boundary`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.genuineClass_not_torsion_boundary (K : Type) [Field.{0} K] [NumberField.{0} K]
  (S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))) (A : Type) [CommRing.{0} A]
  (M : Type) [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  (Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M) [IsDomain.{0} A]
  (R : ZInQ.Contrib.RC53Assist.StageCone.GenuineTwoTermRealization K S A M Delta)
  (z :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        1))
  (hz :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
          1 2 rfl.{1})
        z)
      0)
  (hnb :
    ∀
      (y :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
            0)),
      Ne.{1}
        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
            0 1 rfl.{1})
          y)
        z)
  (a : A) (ha : Ne.{1} a 0)
  (y :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        0)) :
  Ne.{1}
    ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        0 1 rfl.{1})
      y)
    (HSMul.hSMul.{0, 0, 0} a z)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.genuineClass_not_torsion_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.genuineStage_coordinate_zero_of_boundary`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.genuineStage_coordinate_zero_of_boundary (K : Type) [Field.{0} K]
  [NumberField.{0} K] (S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K)))
  (A : Type) [CommRing.{0} A] (M : Type) [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  (Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M) {F : Type} [Field.{0} F]
  (ι : RingHom.{0, 0} A F) (R : ZInQ.Contrib.RC53Assist.StageCone.GenuineTwoTermRealization K S A M Delta)
  (z :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        1))
  (hz :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
          1 2 rfl.{1})
        z)
      0)
  (lam :
    LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A)
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
          2))
      A)
  (hlam :
    ∀
      (y :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
            1)),
      Eq.{1}
        (lam
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
                (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
              1 2 rfl.{1})
            y))
        0)
  (hdet :
    Eq.{1}
      (Matrix.det.{0, 0} (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.matrix R) ⇑ι))
      0)
  (hadj :
    Ne.{1}
      (Matrix.adjugate.{0, 0}
        (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.matrix R) ⇑ι))
      0)
  (y :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        0))
  (hy :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
          0 1 rfl.{1})
        y)
      z) :
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0}
      (ZInQ.Contrib.RC53Assist.StageCone.genuineStage K S A M ι Delta R z hz lam hlam hdet hadj))
    0
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.genuineStage_coordinate_zero_of_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.genuineStage_primitiveKernel`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.genuineStage_primitiveKernel (K : Type) [Field.{0} K] [NumberField.{0} K]
  (S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))) (A : Type) [CommRing.{0} A]
  (M : Type) [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  (Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M) {F k : Type} [Field.{0} F] [Field.{0} k]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] (ι : RingHom.{0, 0} A F) (hι : Function.Injective.{1, 1} ⇑ι)
  (ρ : RingHom.{0, 0} A k) (R : ZInQ.Contrib.RC53Assist.StageCone.GenuineTwoTermRealization K S A M Delta)
  (z :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        1))
  (hz :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
          1 2 rfl.{1})
        z)
      0)
  (lam :
    LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A)
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
          2))
      A)
  (hlam :
    ∀
      (y :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
            1)),
      Eq.{1}
        (lam
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
                (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
              1 2 rfl.{1})
            y))
        0)
  (hdet :
    Eq.{1}
      (Matrix.det.{0, 0} (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.matrix R) ⇑ι))
      0)
  (hadj :
    Ne.{1}
      (Matrix.adjugate.{0, 0}
        (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.matrix R) ⇑ι))
      0)
  (hnb :
    ∀
      (y :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
            0)),
      Ne.{1}
        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
            0 1 rfl.{1})
          y)
        z) :
  Nonempty.{1}
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.PrimitiveKernelVector.{0, 0, 0}
      (ZInQ.Contrib.RC53Assist.StageCone.genuineStage K S A M ι Delta R z hz lam hlam hdet hadj) ρ)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.genuineStage_primitiveKernel' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation.realization_spec`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation.realization_spec {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  {Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M}
  (P : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation K S A M Delta) :
  Eq.{1} P.realization.n P.n ∧
    ∀ (i j : ℤ) (hij : Eq.{1} (HAdd.hAdd.{0, 0, 0} i 1) j)
      (x : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} P.realization.model i)),
      Membership.mem.{0, 0} (HSMul.hSMul.{0, 0, 0} (IsLocalRing.maximalIdeal.{0} A) Top.top.{0})
        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} P.realization.model i j hij) x)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation.realization_spec' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation.matrix_residue_zero`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation.matrix_residue_zero {K : Type} [Field.{0} K]
  [NumberField.{0} K] {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))}
  {A : Type} [CommRing.{0} A] [IsLocalRing.{0} A] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  {Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M} {k : Type} [Field.{0} k]
  (P : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation K S A M Delta) (ρ : RingHom.{0, 0} A k)
  (hρ : ∀ (x : A), Membership.mem.{0, 0} (IsLocalRing.maximalIdeal.{0} A) x → Eq.{1} (ρ x) 0) :
  Eq.{1} (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.matrix P.realization) ⇑ρ) 0
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation.matrix_residue_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing.functional_closed`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing.functional_closed {K : Type} [Field.{0} K]
  [NumberField.{0} K] {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))}
  {A : Type} [CommRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  {Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M}
  {z :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        1)}
  (P : ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing K S A M N Delta z)
  (y :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        1)) :
  Eq.{1}
    (P.functional
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
          1 2 rfl.{1})
        y))
    0
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing.functional_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing.functional_nonzero_on_cycles`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing.functional_nonzero_on_cycles {K : Type} [Field.{0} K]
  [NumberField.{0} K] {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))}
  {A : Type} [CommRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  {Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M}
  {z :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        1)}
  [IsDomain.{0} A] (P : ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing K S A M N Delta z)
  (R : ZInQ.Contrib.RC53Assist.StageCone.GenuineTwoTermRealization K S A M Delta)
  (hz :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
          1 2 rfl.{1})
        z)
      0)
  (hnb :
    ∀
      (y :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
            0)),
      Ne.{1}
        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
            0 1 rfl.{1})
          y)
        z) :
  ∃ w,
    Eq.{1}
        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
            2 3 rfl.{1})
          w)
        0 ∧
      Ne.{1} (P.functional w) 0
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing.functional_nonzero_on_cycles' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.retains_class`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.retains_class {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  (G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι) :
  Eq.{1}
    ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} G.presentation.realization.f 1 1 rfl.{1})
      ((LinearEquiv.symm.{0, 0, 0, 0} (Module.Basis.equivFun.{0, 0, 0} G.presentation.realization.b1))
        (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.z.{0, 0} G.stage)))
    (HAdd.hAdd.{0, 0, 0} G.actualClass
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M G.conditions))
          0 1 rfl.{1})
        (ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.boundaryWitness G.presentation.realization G.actualClass
          G.class_closed)))
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.retains_class' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.retains_functional`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.retains_functional {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  (G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι)
  (x : Fin (HAdd.hAdd.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.n.{0, 0} G.stage) 1) → A) :
  Eq.{1} (dotProduct.{0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.w.{0, 0} G.stage) x)
    (G.paired.functional
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} G.presentation.realization.f 2 2 rfl.{1})
        ((LinearEquiv.symm.{0, 0, 0, 0} (Module.Basis.equivFun.{0, 0, 0} G.presentation.realization.b2)) x)))
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.retains_functional' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.coord_ne_zero`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.coord_ne_zero {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  [IsDomain.{0} A] (G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι)
  (hι : Function.Injective.{1, 1} ⇑ι) : Ne.{1} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} G.stage) 0
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.coord_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.fiberDim_eq`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.fiberDim_eq {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {k : Type} [Field.{0} k] (G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι)
  (ρ : RingHom.{0, 0} A k) (hρ : ∀ (x : A), Membership.mem.{0, 0} (IsLocalRing.maximalIdeal.{0} A) x → Eq.{1} (ρ x) 0) :
  Eq.{1} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.fiberDim.{0, 0, 0} ρ G.stage)
    (HAdd.hAdd.{0, 0, 0} G.presentation.n 1)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.fiberDim_eq' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.fiberDim_residualHomology`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.fiberDim_residualHomology {K : Type} [Field.{0} K]
  [NumberField.{0} K] {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))}
  {A : Type} [CommRing.{0} A] [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  (G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι) :
  Eq.{1} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.fiberDim.{0, 0, 0} (IsLocalRing.residue.{0} A) G.stage)
    (Module.finrank.{0, 0} (IsLocalRing.ResidueField.{0} A)
      ↑(HomologicalComplex.homology.{0, 1, 0}
          (ZInQ.Contrib.CloudB3RC53.ResidualTransfer.resCx.{0} G.presentation.complex) 1))
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.fiberDim_residualHomology' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.terminal_regular`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.terminal_regular {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {k : Type} [Field.{0} k] (G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι)
  (hι : Function.Injective.{1, 1} ⇑ι) (ρ : RingHom.{0, 0} A k)
  (hρ : ∀ (x : A), Membership.mem.{0, 0} (IsLocalRing.maximalIdeal.{0} A) x → Eq.{1} (ρ x) 0)
  (hn : Eq.{1} G.presentation.n 0) :
  ∃ a, Eq.{1} (ι a) (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} G.stage)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.terminal_regular' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.matrix_mulVec`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.matrix_mulVec {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (L : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization G)
  (x : Fin (HAdd.hAdd.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.n.{0, 0} G.stage) 1) → A) :
  Eq.{1} (Matrix.mulVec.{0, 0, 0} L.matrix x) (L.vectorMap x)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.matrix_mulVec' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.class_identity`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.class_identity {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (L : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization G) :
  Eq.{1} (Matrix.mulVec.{0, 0, 0} L.matrix (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.z.{0, 0} G.stage))
    (L.onCochains G.actualClass)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.class_identity' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.isCompl`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.isCompl {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι} {k : Type} [Field.{0} k]
  {ρ : RingHom.{0, 0} A k} (X : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns G ρ) : IsCompl.{0} X.plus X.minus
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.isCompl' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.sign_sum`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.sign_sum {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι} {k : Type} [Field.{0} k]
  {ρ : RingHom.{0, 0} A k} (X : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns G ρ) :
  Eq.{1} (HAdd.hAdd.{0, 0, 0} (Module.finrank.{0, 0} k ↥X.plus) (Module.finrank.{0, 0} k ↥X.minus))
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.fiberDim.{0, 0, 0} ρ G.stage)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.sign_sum' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.detects_actual`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.detects_actual {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} {G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (L : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization G) (hι : Function.Injective.{1, 1} ⇑ι)
  (ρ : RingHom.{0, 0} A k)
  (hL :
    Ne.{1}
      (Matrix.mulVec.{0, 0, 0} (Matrix.map.{0, 0, 0, 0} L.matrix ⇑ρ) fun i =>
        ρ (ZInQ.Contrib.CloudB3RC53.UniformSwitch.PrimitiveKernelVector.v.{0, 0, 0} (G.primitiveKernel hι ρ) i))
      0) :
  Ne.{1} L.genericVector 0
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.detects_actual' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison.oldIntegralUnit_iff`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison.oldIntegralUnit_iff {K : Type} [Field.{0} K]
  [NumberField.{0} K] {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))}
  {A : Type} [CommRing.{0} A] [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M]
  [Module.{0, 0} A M] [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} {hι : Function.Injective.{1, 1} ⇑ι} {ρ : RingHom.{0, 0} A k}
  {G G' : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (C : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison hι ρ G G') :
  C.oldMap.IntegralUnit (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hz C.epsilon C.localization.genericVector)
      (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hl C.epsilon C.localization.genericVector) ↔
    ∃ c, Eq.{1} C.strictFactor (ι ↑c)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison.oldIntegralUnit_iff' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison.stageConeComparison_iff`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison.stageConeComparison_iff {K : Type} [Field.{0} K]
  [NumberField.{0} K] {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))}
  {A : Type} [CommRing.{0} A] [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M]
  [Module.{0, 0} A M] [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} {hι : Function.Injective.{1, 1} ⇑ι} {ρ : RingHom.{0, 0} A k}
  {G G' : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (C : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison hι ρ G G') :
  ZInQ.Contrib.CloudB3RC53.StageCone.StageConeComparison G.stage G'.stage C.epsilon C.sigma C.J
      C.localization.genericVector ↔
    ∃ c, Eq.{1} C.strictFactor (ι ↑c)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison.stageConeComparison_iff' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily.sign_sum`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily.sign_sum {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} {ρ : RingHom.{0, 0} A k} {I : Type}
  {family : I → ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (T : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily ρ family) (hq : T.quadratic) (i : I) :
  Eq.{1} (HAdd.hAdd.{0, 0, 0} (T.sp i) (T.sm i))
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.fiberDim.{0, 0, 0} ρ (family i).stage)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily.sign_sum' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem.regular`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem.regular {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} {hι : Function.Injective.{1, 1} ⇑ι} {ρ : RingHom.{0, 0} A k} {I : Type}
  {family : I → ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (X : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem hι ρ family)
  (hρ : ∀ (x : A), Membership.mem.{0, 0} (IsLocalRing.maximalIdeal.{0} A) x → Eq.{1} (ρ x) 0) (i : I) :
  ∃ a, Eq.{1} (ι a) (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} (family i).stage)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem.regular' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.lambdaAtPrime_dvr`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.lambdaAtPrime_dvr (P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda)
  [Ideal.IsPrime.{0} P] (hp : Eq.{1} (Ideal.height.{0} P) 1) : IsDiscreteValuationRing.{0} (Localization.AtPrime.{0} P)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.lambdaAtPrime_dvr' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.regularAtPrime_of_genuineSwitches`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.regularAtPrime_of_genuineSwitches
  (P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda) [Ideal.IsPrime.{0} P] (hp : Eq.{1} (Ideal.height.{0} P) 1)
  {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {M N : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} (Localization.AtPrime.{0} P) M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Localization.AtPrime.{0} P) M]
  [TopologicalSpace.{0} M] [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} (Localization.AtPrime.{0} P) M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N]
  [Module.{0, 0} (Localization.AtPrime.{0} P) N] [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Localization.AtPrime.{0} P) N]
  [TopologicalSpace.{0} N] [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} (Localization.AtPrime.{0} P) N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {I : Type}
  (family :
    I →
      ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S (Localization.AtPrime.{0} P) M N
        (ZInQ.Contrib.CloudB3RC53.UniformSwitch.toFracAt P))
  (X :
    ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem
      (ZInQ.Contrib.CloudB3RC53.UniformSwitch.toFracAt_injective P)
      (IsLocalRing.residue.{0} (Localization.AtPrime.{0} P)) family)
  (i : I) :
  ZInQ.Manuscript.RC.Uniform.RegularAtPrime P
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} (family i).stage)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.regularAtPrime_of_genuineSwitches' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.exists_process_of_genuineSwitches`

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.exists_process_of_genuineSwitches
  (P : Ideal.{0} ZInQ.Manuscript.RC.Uniform.Lambda) [Ideal.IsPrime.{0} P] (hp : Eq.{1} (Ideal.height.{0} P) 1)
  {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {M N : Type}
  [AddCommGroup.{0} M] [Module.{0, 0} (Localization.AtPrime.{0} P) M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Localization.AtPrime.{0} P) M]
  [TopologicalSpace.{0} M] [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} (Localization.AtPrime.{0} P) M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N]
  [Module.{0, 0} (Localization.AtPrime.{0} P) N] [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (Localization.AtPrime.{0} P) N]
  [TopologicalSpace.{0} N] [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} (Localization.AtPrime.{0} P) N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {I : Type}
  (family :
    I →
      ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S (Localization.AtPrime.{0} P) M N
        (ZInQ.Contrib.CloudB3RC53.UniformSwitch.toFracAt P))
  (X :
    ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem
      (ZInQ.Contrib.CloudB3RC53.UniformSwitch.toFracAt_injective P)
      (IsLocalRing.residue.{0} (Localization.AtPrime.{0} P)) family)
  (i : I) :
  ∃ Pr i₀,
    Eq.{1} (ZInQ.Manuscript.RC.Uniform.RegularitySwitchProcess.coord.{0} Pr i₀)
      (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} (family i).stage)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.exists_process_of_genuineSwitches' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## Other named declarations

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation` (structure)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation (K : Type) [Field.{0} K] [NumberField.{0} K]
  (S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))) (A : Type) [CommRing.{0} A]
  [IsLocalRing.{0} A] (M : Type) [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  (Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M) : Type 1
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation.realization` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation.realization {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  {Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M}
  (P : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation K S A M Delta) :
  ZInQ.Contrib.RC53Assist.StageCone.GenuineTwoTermRealization K S A M Delta
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuinePresentation.realization' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing` (structure)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing (K : Type) [Field.{0} K] [NumberField.{0} K]
  (S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))) (A : Type) [CommRing.{0} A]
  (M N : Type) [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  (Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M)
  (z :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        1)) :
  Type 1
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing.functional` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing.functional {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  {Delta : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S A M}
  {z :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        1)}
  (P : ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing K S A M N Delta z) :
  LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A)
    (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
          (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData K S A M Delta))
        2))
    A
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.RetainedIntegralPairing.functional' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData` (structure)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData (K : Type) [Field.{0} K] [NumberField.{0} K]
  (S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))) (A : Type) [CommRing.{0} A]
  [IsLocalRing.{0} A] (M N : Type) [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F]
  (ι : RingHom.{0, 0} A F) : Type 1
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.stage` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.stage {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  (G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι) :
  ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.stage' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization` (structure)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  (G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι) : Type
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.vectorMap` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.vectorMap {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (L : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization G) :
  LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A)
    (Fin (HAdd.hAdd.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.n.{0, 0} G.stage) 1) → A) (Fin 2 → A)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.vectorMap' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.matrix` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.matrix {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (L : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization G) :
  Matrix.{0, 0, 0} (Fin 2)
    (Fin (HAdd.hAdd.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.n.{0, 0} G.stage) 1)) A
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.matrix' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.genericVector` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.genericVector {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (L : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization G) : Fin 2 → F
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineLocalization.genericVector' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns` (structure)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {k : Type} [Field.{0} k] (G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι)
  (ρ : RingHom.{0, 0} A k) : Type
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.plus` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.plus {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι} {k : Type} [Field.{0} k]
  {ρ : RingHom.{0, 0} A k} (X : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns G ρ) :
  Submodule.{0, 0} k
    ↥(LinearMap.ker.{0, 0, 0, 0}
        (Matrix.mulVecLin.{0, 0, 0}
          (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.D.{0, 0} G.stage) ⇑ρ)))
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.plus' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.minus` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.minus {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsLocalRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F : Type} [Field.{0} F] {ι : RingHom.{0, 0} A F}
  {G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι} {k : Type} [Field.{0} k]
  {ρ : RingHom.{0, 0} A k} (X : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns G ρ) :
  Submodule.{0, 0} k
    ↥(LinearMap.ker.{0, 0, 0, 0}
        (Matrix.mulVecLin.{0, 0, 0}
          (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.D.{0, 0} G.stage) ⇑ρ)))
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSigns.minus' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.primitiveKernel` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.primitiveKernel {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} (G : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι)
  (hι : Function.Injective.{1, 1} ⇑ι) (ρ : RingHom.{0, 0} A k) :
  ZInQ.Contrib.CloudB3RC53.UniformSwitch.PrimitiveKernelVector.{0, 0, 0} G.stage ρ
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData.primitiveKernel' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison` (structure)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} (hι : Function.Injective.{1, 1} ⇑ι) (ρ : RingHom.{0, 0} A k)
  (G G' : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι) : Type
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison.toCoordStep` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison.toCoordStep {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} {hι : Function.Injective.{1, 1} ⇑ι} {ρ : RingHom.{0, 0} A k}
  {G G' : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (C : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison hι ρ G G') :
  ZInQ.Contrib.CloudB3RC53.UniformSwitch.CoordStep.{0, 0} ι
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} G.stage)
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} G'.stage)
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchComparison.toCoordStep' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily` (structure)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} {I : Type} (ρ : RingHom.{0, 0} A k)
  (family : I → ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι) : Type
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily.sp` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily.sp {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} {ρ : RingHom.{0, 0} A k} {I : Type}
  {family : I → ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (T : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily ρ family) (i : I) : ℕ
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily.sp' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily.sm` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily.sm {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} {ρ : RingHom.{0, 0} A k} {I : Type}
  {family : I → ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (T : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily ρ family) (i : I) : ℕ
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSignFamily.sm' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem` (structure)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} {I : Type} (hι : Function.Injective.{1, 1} ⇑ι) (ρ : RingHom.{0, 0} A k)
  (family : I → ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι) : Type
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem.toData` (def)

```text
ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem.toData {K : Type} [Field.{0} K] [NumberField.{0} K]
  {S : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {A : Type} [CommRing.{0} A]
  [IsDomain.{0} A] [IsDiscreteValuationRing.{0} A] {M N : Type} [AddCommGroup.{0} M] [Module.{0, 0} A M]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A M] [TopologicalSpace.{0} M]
  [ContinuousAdd.{0} M] [ContinuousConstSMul.{0, 0} A M]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M] [AddCommGroup.{0} N] [Module.{0, 0} A N]
  [DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N]
  [SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) A N] [TopologicalSpace.{0} N]
  [ContinuousAdd.{0} N] [ContinuousConstSMul.{0, 0} A N]
  [ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) N] {F k : Type} [Field.{0} F] [Field.{0} k]
  {ι : RingHom.{0, 0} A F} {hι : Function.Injective.{1, 1} ⇑ι} {ρ : RingHom.{0, 0} A k} {I : Type}
  {family : I → ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineStageData K S A M N ι}
  (X : ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem hι ρ family) :
  ZInQ.Contrib.CloudB3RC53.UniformSwitch.HeightOneSwitchDataPK.{0, 0, 0} ι ρ
```

```text
'ZInQ.Contrib.RC53Assist.StagePrimitive.GenuineSwitchSystem.toData' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

