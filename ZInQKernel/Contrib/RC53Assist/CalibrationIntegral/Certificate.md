# Integral central Kummer calibration certificate

## Result and scope

`DiskTie` is proved from an explicit integral retained-basis model comparison. The comparison itself remains an input; this is not an unconditional arithmetic proof of the calibration or of Theorem 5.3.

The final source has 72 theorems and 161 named declarations. Every declaration was rechecked in a separate single-file verification. Every individual dependency report contains only the standard foundation axioms `propext`, `Classical.choice`, and `Quot.sound`, or a subset of them. There are no additional axioms or proof placeholders. The source also checks with implicit declaration generation disabled and a heartbeat limit of 600000.

## The actual central compact complex

For `G : GenuineKummerData K E₀ hZ`, the compact complex used here is

```lean
compactKummerComplex G.S (centralCurve G) (centralFullTorsion G)
```

where `centralCurve G = twistK G.W (hZ : K)`. The quadratic twist matters: the finite coefficient module has the central quadratic character, so the untwisted compact complex cannot simply be substituted for it. Full two-power torsion of this actual twist is proved from the given square root and the original full-torsion data.

The coefficient projection is the Tate projection at level `i`, followed by the global quadratic-twist identification and the map `t ↦ 1 ⊗ t`. It is integral-coefficient semilinear, continuous, and Galois equivariant. The global and local twist identifications commute with the fixed decomposition embeddings. In particular, `localCoefficientReduction_tateKummer` proves that each integral Kummer cocycle reduces to the finite Kummer cocycle of the same division tower, pushed forward by the genuine local coefficient map. The push-forward of any choice of division point lies in the actual Kummer condition. Coboundaries and the whole integral Kummer span are also preserved.

Consequently `centralReductionCompatibility G` is a theorem, not an input. The resulting `canonicalCentralReductionMap G i` is a constructed cochain map

```lean
scalarChangedComplex (constRed i) (compactCentralComplex G) ⟶
  (selCx (centralKummerSelData G.W G.s G.hs G.hs0 G.hFull i)).toCC
```

Its target is precisely the genuine finite-level complex defining `G.selH`, not a complex with freely assigned cohomology orders.

## Integral normal forms and finite orders

The scalar normal form has a free line with zero differential in degrees one and two, and scalar disks in degrees zero to one, one to two, and two to three. All its cohomology modules are calculated explicitly. Its actual coefficient extension is isomorphic to the reduced-differential normal form; no flatness of the coefficient map is assumed for this calculation.

A single scalar disk has cyclic cokernel. To retain noncyclic finite torsion, the matrix-disk version has integral matrices `B₁`, `B₂`, and `B₃`, with scalar disk orders read from `x₁ = B₁.det`, `x₂ = B₂.det`, and `x₃ = B₃.det`. Its finite cohomology is calculated as

- degree zero: the kernel of the first reduced matrix;
- degree two: the free coefficient line, the middle reduced-matrix cokernel, and the last reduced-matrix kernel;
- degree three: the last reduced-matrix cokernel.

For an endomorphism of a finite module, the kernel and cokernel have equal orders. Smith normal form over the two-adic integers then gives, for nonzero determinant and sufficiently large precision,

```lean
Nat.card ((Fin m → Acoef i) ⧸ LinearMap.range (B.map (constRed i)).mulVecLin)
  = cycOrder i B.det
```

Given the integral model input, the constructed finite comparison is a quasi-isomorphism in every degree. It induces actual cohomology isomorphisms, from which the three equalities are obtained:

```lean
Nat.card (G.selH i 0) = cycOrder i B₁.det
Nat.card (G.selH i 2) = 2 ^ (i * i) * cycOrder i B₂.det * cycOrder i B₃.det
Nat.card (G.selH i 3) = cycOrder i B₃.det
```

A common eventual bound is `B₁.det.valuation + B₂.det.valuation + B₃.det.valuation + 1`. This proves `DiskTie G B₁.det B₂.det B₃.det`. The literal three-scalar-disk version likewise proves `DiskTie G x₁ x₂ x₃`.

The degreewise basis comparison is an integral linear equivalence. Its matrices have unit determinants. The inverse determinant-line comparison is the alternating product of these degreewise determinant units and is proved to have valuation zero. This is a comparison of the displayed normal form with the retained finite-free model, not a new assertion identifying the separate rational calibration basis.

## Remaining comparison input

`CanonicalIntegralCentralModel` is the literal scalar-disk input with the local compatibility theorem already supplied. `IntegralBlockCentralModel` is the more general matrix-disk input. Their exact field types are included below.

The essential remaining work is to construct the finite-free retained model `P`, its integral normalization, the map `comparison : P ⟶ compactCentralComplex G`, and its quasi-isomorphism. One must also establish the quasi-isomorphism of the canonical finite coefficient composite

```lean
((ModuleCat.extendScalars (constRed i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
  comparison ≫ canonicalCentralReductionMap G i
```

This last field is a derived-reduction comparison: `P` is finite free and represents the compact complex, so its coefficient extension is the intended derived finite fibre. Reduction of individual cocycles alone does not establish this quasi-isomorphism, and a rational quasi-isomorphism cannot supply its integral lattice information.

Neither model input contains `Nat.card` or the three order equalities. It specifies complexes, maps, integral bases, and comparisons in all cohomological degrees. It is therefore not an order-predicate restatement of `DiskTie`.

## Arithmetic and calibration scope

`DiskArith G tA shaA` remains the separate ELLIOT arithmetic-order input. With it, the new matrix-model theorem derives

```lean
B₁.det.valuation = padicValNat 2 tA ∧
B₂.det.valuation = padicValNat 2 shaA ∧
B₃.det.valuation = padicValNat 2 tA
```

No identification with the actual elliptic-curve torsion group or Tate–Shafarevich group is asserted without that arithmetic input. The rational calibration identification `I`, the coordinate transfer `link`, and the free class and functional coefficients also remain inputs. The constructor `kummerCoordinateBlockOfIntegralModel` supplies the existing `KummerCoordinateBlockG.tie` field using the proved integral-model `DiskTie` theorem while preserving those separate inputs. The matrix-model `diskTie` supplies the same field with determinant scalars.

Only new files were written. Existing source files were not edited, and no repository operations or aggregate builds were performed.

## Verification inventory

The exact elaborated type and individual dependency report for each theorem follow. Definitions and their individual dependency reports are also included, so the cohomology equivalences and cochain-map constructions can be inspected directly.

## Exact remaining comparison records

### IntegralCentralModel

```lean
variable {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ}

structure IntegralCentralModel (G : GenuineKummerData K E₀ hZ)
    (H : CentralReductionCompatibility G) (x₁ x₂ x₃ : ℤ_[2]) where
  P : CochainComplex (ModuleCat ℤ_[2]) ℤ
  coordinates : (n : ℤ) → P.X n ≃ₗ[ℤ_[2]] (Fin (normalRank n) → ℤ_[2])
  normalization : normalComplex x₁ x₂ x₃ ≅ P
  comparison : P ⟶ compactCentralComplex G
  quasi_iso : QuasiIso comparison
  fibre_quasi_iso : ∀ i : ℕ, i ≠ 0 →
    QuasiIso (((ModuleCat.extendScalars (constRed i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      comparison ≫ centralReductionMap G H i)
  disk1_ne_zero : x₁ ≠ 0
  disk2_ne_zero : x₂ ≠ 0
  disk3_ne_zero : x₃ ≠ 0
```

### IntegralBlockCentralModel

```lean
variable {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ}

structure IntegralBlockCentralModel (G : GenuineKummerData K E₀ hZ)
    (B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]) (B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2])
    (B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]) where
  P : CochainComplex (ModuleCat ℤ_[2]) ℤ
  coordinates : (n : ℤ) → P.X n ≃ₗ[ℤ_[2]] (blockIndex m₁ m₂ m₃ n → ℤ_[2])
  normalization : blockComplex B₁ B₂ B₃ ≅ P
  comparison : P ⟶ compactCentralComplex G
  quasi_iso : QuasiIso comparison
  fibre_quasi_iso : ∀ i : ℕ, i ≠ 0 →
    QuasiIso (((ModuleCat.extendScalars (constRed i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      comparison ≫ canonicalCentralReductionMap G i)
  disk1_det_ne_zero : B₁.det ≠ 0
  disk2_det_ne_zero : B₂.det ≠ 0
  disk3_det_ne_zero : B₃.det ≠ 0
```

## All theorem statements and individual axiom reports

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD_sq

Source statement:

```lean
theorem normalD_sq (x₁ x₂ x₃ : R) (n : ℕ) :
    normalD x₁ x₂ x₃ n ≫ normalD x₁ x₂ x₃ (n + 1) = 0
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD_sq {R : Type} [CommRing R] (x₁ x₂ x₃ : R) (n : ℕ) :
  CategoryTheory.CategoryStruct.comp (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD x₁ x₂ x₃ n)
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD x₁ x₂ x₃ (n + 1)) =
    0
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD_sq' depends on axioms: [propext, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d0

Source statement:

```lean
theorem normalComplex_d0 (x₁ x₂ x₃ : R) :
    ((normalComplex x₁ x₂ x₃).d 0 1).hom = normalD0 x₁
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d0 {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ModuleCat.Hom.hom ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃).d 0 1) =
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD0 x₁
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d0' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d1

Source statement:

```lean
theorem normalComplex_d1 (x₁ x₂ x₃ : R) :
    ((normalComplex x₁ x₂ x₃).d 1 2).hom = normalD1 x₂
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d1 {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ModuleCat.Hom.hom ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃).d 1 2) =
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD1 x₂
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d2

Source statement:

```lean
theorem normalComplex_d2 (x₁ x₂ x₃ : R) :
    ((normalComplex x₁ x₂ x₃).d 2 3).hom = normalD2 x₃
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d2 {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ModuleCat.Hom.hom ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃).d 2 3) =
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD2 x₃
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_dneg

Source statement:

```lean
theorem normalComplex_dneg (x₁ x₂ x₃ : R) :
    ((normalComplex x₁ x₂ x₃).d (-1) 0).hom = 0
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_dneg {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ModuleCat.Hom.hom ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃).d (-1) 0) = 0
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_dneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d3

Source statement:

```lean
theorem normalComplex_d3 (x₁ x₂ x₃ : R) :
    ((normalComplex x₁ x₂ x₃).d 3 4).hom = 0
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d3 {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ModuleCat.Hom.hom ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃).d 3 4) = 0
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex_d3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.range_scalarMap

Source statement:

```lean
theorem range_scalarMap (x : R) :
    LinearMap.range (scalarMap x) = (Ideal.span {x} : Submodule R R)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.range_scalarMap {R : Type} [CommRing R] (x : R) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.scalarMap x).range = Ideal.span {x}
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.range_scalarMap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.card_scalar_kernel

Source statement:

```lean
theorem card_scalar_kernel [Finite R] (x : R) :
    Nat.card (LinearMap.ker (scalarMap x)) = Nat.card (R ⧸ Ideal.span {x})
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.card_scalar_kernel {R : Type} [CommRing R] [Finite R] (x : R) :
  Nat.card ↥(ZInQ.Contrib.RC53Assist.CalibrationIntegral.scalarMap x).ker = Nat.card (R ⧸ Ideal.span {x})
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.card_scalar_kernel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normal_card0

Source statement:

```lean
theorem normal_card0 [Finite R] (x₁ x₂ x₃ : R) :
    Nat.card ((normalComplex x₁ x₂ x₃).homology 0) = Nat.card (R ⧸ Ideal.span {x₁})
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normal_card0 {R : Type} [CommRing R] [Finite R] (x₁ x₂ x₃ : R) :
  Nat.card ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) 0) =
    Nat.card (R ⧸ Ideal.span {x₁})
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normal_card0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normal_card2

Source statement:

```lean
theorem normal_card2 [Finite R] (x₁ x₂ x₃ : R) :
    Nat.card ((normalComplex x₁ x₂ x₃).homology 2) =
      Nat.card R * Nat.card (R ⧸ Ideal.span {x₂}) * Nat.card (R ⧸ Ideal.span {x₃})
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normal_card2 {R : Type} [CommRing R] [Finite R] (x₁ x₂ x₃ : R) :
  Nat.card ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) 2) =
    Nat.card R * Nat.card (R ⧸ Ideal.span {x₂}) * Nat.card (R ⧸ Ideal.span {x₃})
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normal_card2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normal_card3

Source statement:

```lean
theorem normal_card3 (x₁ x₂ x₃ : R) :
    Nat.card ((normalComplex x₁ x₂ x₃).homology 3) = Nat.card (R ⧸ Ideal.span {x₃})
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normal_card3 {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  Nat.card ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) 3) =
    Nat.card (R ⧸ Ideal.span {x₃})
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normal_card3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteNormal_orders

Source statement:

```lean
theorem finiteNormal_orders (i : ℕ) (hi : i ≠ 0) (x₁ x₂ x₃ : ℤ_[2]) :
    Nat.card ((normalComplex (constRed i x₁) (constRed i x₂) (constRed i x₃)).homology 0) =
        cycOrder i x₁ ∧
      Nat.card ((normalComplex (constRed i x₁) (constRed i x₂) (constRed i x₃)).homology 2) =
        2 ^ (i * i) * cycOrder i x₂ * cycOrder i x₃ ∧
      Nat.card ((normalComplex (constRed i x₁) (constRed i x₂) (constRed i x₃)).homology 3) =
        cycOrder i x₃
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteNormal_orders (i : ℕ) (hi : i ≠ 0) (x₁ x₂ x₃ : ℤ_[2]) :
  Nat.card
        ↑(HomologicalComplex.homology
            (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex
              ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₁)
              ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₂)
              ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₃))
            0) =
      ZInQ.Contrib.RC53Assist.Calibration.cycOrder i x₁ ∧
    Nat.card
          ↑(HomologicalComplex.homology
              (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex
                ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₁)
                ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₂)
                ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₃))
              2) =
        2 ^ (i * i) * ZInQ.Contrib.RC53Assist.Calibration.cycOrder i x₂ *
          ZInQ.Contrib.RC53Assist.Calibration.cycOrder i x₃ ∧
      Nat.card
          ↑(HomologicalComplex.homology
              (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex
                ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₁)
                ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₂)
                ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₃))
              3) =
        ZInQ.Contrib.RC53Assist.Calibration.cycOrder i x₃
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteNormal_orders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_nonsingular

Source statement:

```lean
theorem globalTwistPointEquiv_nonsingular {x y : KS K S}
    (hxy : ((twistK W h).baseChange (KS K S)).toAffine.Nonsingular x y) :
    (W.baseChange (KS K S)).toAffine.Nonsingular (s⁻¹ ^ 2 * x)
      (s⁻¹ ^ 3 * y + s⁻¹ ^ 2 * (-(W.baseChange (KS K S)).a₁ / 2) * x -
        (W.baseChange (KS K S)).a₃ / 2)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_nonsingular {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h) (hs0 : s ≠ 0)
  {x y : ZInQ.Manuscript.RC.CoefModules.KS K S}
  (hxy :
    ((ZInQ.Manuscript.RC.TwistDictionary.twistK W h).baseChange
            (ZInQ.Manuscript.RC.CoefModules.KS K S)).toAffine.Nonsingular
      x y) :
  (W.baseChange (ZInQ.Manuscript.RC.CoefModules.KS K S)).toAffine.Nonsingular (s⁻¹ ^ 2 * x)
    (s⁻¹ ^ 3 * y + s⁻¹ ^ 2 * (-(W.baseChange (ZInQ.Manuscript.RC.CoefModules.KS K S)).a₁ / 2) * x -
      (W.baseChange (ZInQ.Manuscript.RC.CoefModules.KS K S)).a₃ / 2)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_nonsingular' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_some

Source statement:

```lean
theorem globalTwistPointEquiv_some {x y : KS K S}
    (hxy : ((twistK W h).baseChange (KS K S)).toAffine.Nonsingular x y) :
    globalTwistPointEquiv W s hs hs0 (.some x y hxy) =
      .some _ _ (globalTwistPointEquiv_nonsingular W s hs hs0 hxy)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_some {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h) (hs0 : s ≠ 0)
  {x y : ZInQ.Manuscript.RC.CoefModules.KS K S}
  (hxy :
    ((ZInQ.Manuscript.RC.TwistDictionary.twistK W h).baseChange
            (ZInQ.Manuscript.RC.CoefModules.KS K S)).toAffine.Nonsingular
      x y) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv W s hs hs0)
      (WeierstrassCurve.Affine.Point.some x y hxy) =
    WeierstrassCurve.Affine.Point.some (s⁻¹ ^ 2 * x)
      (s⁻¹ ^ 3 * y + s⁻¹ ^ 2 * (-(W.baseChange (ZInQ.Manuscript.RC.CoefModules.KS K S)).a₁ / 2) * x -
        (W.baseChange (ZInQ.Manuscript.RC.CoefModules.KS K S)).a₃ / 2)
      ⋯
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_galois

Source statement:

```lean
theorem globalTwistPointEquiv_galois (σ : GKS K S)
    (P : ((twistK W h).baseChange (KS K S)).toAffine.Point) :
    globalTwistPointEquiv W s hs hs0 (Affine.Point.map (galS K S σ).toAlgHom P) =
      ((quadChar s hs hs0 σ : ℤˣ) : ℤ) •
        Affine.Point.map (galS K S σ).toAlgHom (globalTwistPointEquiv W s hs hs0 P)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_galois {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h) (hs0 : s ≠ 0)
  (σ : ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
  (P :
    ((ZInQ.Manuscript.RC.TwistDictionary.twistK W h).baseChange
          (ZInQ.Manuscript.RC.CoefModules.KS K S)).toAffine.Point) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv W s hs hs0)
      ((WeierstrassCurve.Affine.Point.map ↑(ZInQ.Manuscript.RC.CoefModules.galS K S σ)) P) =
    ↑((ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) σ) •
      (WeierstrassCurve.Affine.Point.map ↑(ZInQ.Manuscript.RC.CoefModules.galS K S σ))
        ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv W s hs hs0) P)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_galois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv_galois

Source statement:

```lean
theorem globalTwistTorsEquiv_galois (i : ℕ) (σ : GKS K S)
    (P : TorsS K S (twistK W h) ((2 ^ i : ℕ) : ℤ)) :
    globalTwistTorsEquiv W s hs hs0 i (σ • P) =
      ((quadChar s hs hs0 σ : ℤˣ) : ℤ) • (σ • globalTwistTorsEquiv W s hs hs0 i P)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv_galois {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h) (hs0 : s ≠ 0) (i : ℕ)
  (σ : ZInQ.Manuscript.RC.SelmerComplex.GKS K S)
  (P : ZInQ.Manuscript.RC.CoefModules.TorsS K S (ZInQ.Manuscript.RC.TwistDictionary.twistK W h) ↑(2 ^ i)) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv W s hs hs0 i) (σ • P) =
    ↑((ZInQ.Manuscript.RC.CoefModules.quadChar s hs hs0) σ) •
      σ • (ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv W s hs hs0 i) P
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv_galois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.fullTorsion_twist

Source statement:

```lean
theorem fullTorsion_twist (i : ℕ) (hFull : FullTorsion K S W (2 ^ i)) :
    FullTorsion K S (twistK W h) (2 ^ i)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.fullTorsion_twist {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h) (hs0 : s ≠ 0) (i : ℕ)
  (hFull : ZInQ.Manuscript.RC.CoefModules.FullTorsion K S W (2 ^ i)) :
  ZInQ.Manuscript.RC.CoefModules.FullTorsion K S (ZInQ.Manuscript.RC.TwistDictionary.twistK W h) (2 ^ i)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.fullTorsion_twist' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralFullTorsion

Source statement:

```lean
theorem centralFullTorsion (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    FullTorsion K G.S (centralCurve G) (2 ^ i)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralFullTorsion {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ) :
  ZInQ.Manuscript.RC.CoefModules.FullTorsion K G.S (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G) (2 ^ i)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralFullTorsion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralComplex_eq

Source statement:

```lean
theorem compactCentralComplex_eq (G : GenuineKummerData K E₀ hZ) :
    compactCentralComplex G =
      compactKummerComplex G.S (centralCurve G) (centralFullTorsion G)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralComplex_eq {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralComplex G =
    ZInQ.Manuscript.RC53Assist.CentralKummer.compactKummerComplex G.S
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G) ⋯
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralComplex_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralChar_apply

Source statement:

```lean
theorem centralChar_apply (G : GenuineKummerData K E₀ hZ) (i : ℕ) (σ : GKS K G.S) :
    centralChar i G.s G.hs G.hs0 σ = intUnitsTo (Acoef i) (quadChar G.s G.hs G.hs0 σ)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralChar_apply {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (σ : ZInQ.Manuscript.RC.SelmerComplex.GKS K G.S) :
  (ZInQ.Contrib.RC53Assist.Calibration.centralChar i G.s ⋯ ⋯) σ =
    (ZInQ.Manuscript.RC.CoefModules.intUnitsTo (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i))
      ((ZInQ.Manuscript.RC.CoefModules.quadChar G.s ⋯ ⋯) σ)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralChar_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReductionAdd_smul

Source statement:

```lean
theorem centralCoefficientReductionAdd_smul (G : GenuineKummerData K E₀ hZ) (i : ℕ)
    (a : ℤ_[2]) (P : TateS K G.S (twistK G.W (hZ : K))) :
    centralCoefficientReductionAdd G i (a • P) =
      constRed i a • centralCoefficientReductionAdd G i P
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReductionAdd_smul {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (a : ℤ_[2]) (P : ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (ZInQ.Manuscript.RC.TwistDictionary.twistK G.W ↑hZ)) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReductionAdd G i) (a • P) =
    (ZInQ.Contrib.RC53Assist.Calibration.constRed i) a •
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReductionAdd G i) P
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReductionAdd_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction_galois

Source statement:

```lean
theorem centralCoefficientReduction_galois (G : GenuineKummerData K E₀ hZ) (i : ℕ)
    (σ : GKS K G.S) (P : TateS K G.S (twistK G.W (hZ : K))) :
    centralCoefficientReduction G i (σ • P) = σ • centralCoefficientReduction G i P
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction_galois {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (σ : ZInQ.Manuscript.RC.SelmerComplex.GKS K G.S)
  (P : ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (ZInQ.Manuscript.RC.TwistDictionary.twistK G.W ↑hZ)) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction G i) (σ • P) =
    σ • (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction G i) P
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction_galois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction_continuous

Source statement:

```lean
theorem centralCoefficientReduction_continuous (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    Continuous (centralCoefficientReduction G i)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction_continuous {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ) :
  Continuous ⇑(ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction G i)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflMap_self

Source statement:

```lean
theorem inflMap_self {S : Set (HeightOneSpectrum (𝓞 K))} (σ : GKS K S) :
    inflMap K (subset_refl S) σ = σ
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflMap_self {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (σ : ZInQ.Manuscript.RC.SelmerComplex.GKS K S) : (ZInQ.Manuscript.RC.SelmerComplex.inflMap K ⋯) σ = σ
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflMap_self' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.extend_tmul

Source statement:

```lean
theorem CoefficientComplexMap.extend_tmul {π : R →+* S} {A : GCx R} {B : GCx S}
    (f : CoefficientComplexMap π A B) (n : ℤ)
    (b : (ModuleCat.restrictScalars π).obj (ModuleCat.of S S)) (a : A.X n) :
    let b₀ : S := b
    (f.extend.f n).hom (b ⊗ₜ[R] a) = b₀ • f.f n a
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.extend_tmul {R S : Type} [CommRing R] [CommRing S]
  {π : R →+* S} {A : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx R}
  {B : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx S}
  (f : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap π A B) (n : ℤ)
  (b : ↑((ModuleCat.restrictScalars π).obj ↧S)) (a : ↑(A.X n)) :
  have b₀ := b;
  (ModuleCat.Hom.hom (f.extend.f n)) (b ⊗ₜ[R] a) = b₀ • (f.f n) a
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.extend_tmul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap_d

Source statement:

```lean
theorem cochainCoefficientMap_d (f : M →ₛₗ[π] N) (hfc : Continuous f)
    (hf : ∀ (σ : G) (a : M), f (σ • a) = σ • f a) (n : ℕ) (c : contCochain R G M n) :
    cochainCoefficientMap f hfc (n + 1) (contD R G M n c) =
      contD S G N n (cochainCoefficientMap f hfc n c)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap_d {R S : Type} [CommRing R] [CommRing S] {π : R →+* S}
  {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] {M : Type} [AddCommGroup M] [Module R M]
  [DistribMulAction G M] [SMulCommClass G R M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
  [ContinuousSMul G M] {N : Type} [AddCommGroup N] [Module S N] [DistribMulAction G N] [SMulCommClass G S N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul S N] [ContinuousSMul G N] (f : M →ₛₗ[π] N)
  (hfc : Continuous ⇑f) (hf : ∀ (σ : G) (a : M), f (σ • a) = σ • f a) (n : ℕ)
  (c : ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain R G M n)) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap f hfc (n + 1))
      ((ZInQ.Manuscript.RC.CoefModules.contD R G M n) c) =
    (ZInQ.Manuscript.RC.CoefModules.contD S G N n)
      ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap f hfc n) c)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap_d' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap_mem_B1

Source statement:

```lean
theorem cochainCoefficientMap_mem_B1 (f : M →ₛₗ[π] N) (hfc : Continuous f)
    (hf : ∀ (σ : G) (a : M), f (σ • a) = σ • f a) (b : contCochain R G M 1)
    (hb : b ∈ contB1 R G M) : cochainCoefficientMap f hfc 1 b ∈ contB1 S G N
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap_mem_B1 {R S : Type} [CommRing R] [CommRing S]
  {π : R →+* S} {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] {M : Type} [AddCommGroup M] [Module R M]
  [DistribMulAction G M] [SMulCommClass G R M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
  [ContinuousSMul G M] {N : Type} [AddCommGroup N] [Module S N] [DistribMulAction G N] [SMulCommClass G S N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul S N] [ContinuousSMul G N] (f : M →ₛₗ[π] N)
  (hfc : Continuous ⇑f) (hf : ∀ (σ : G) (a : M), f (σ • a) = σ • f a)
  (b : ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain R G M 1)) (hb : b ∈ ZInQ.Manuscript.RC.CoefModules.contB1 R G M) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap f hfc 1) b ∈
    ZInQ.Manuscript.RC.CoefModules.contB1 S G N
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap_mem_B1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction_galois

Source statement:

```lean
theorem inflatedCoefficientReduction_galois (G : GenuineKummerData K E₀ hZ) (i : ℕ)
    (σ : GKS K G.S) (P : TateS K G.S (centralCurve G)) :
    inflatedCoefficientReduction G i (σ • P) = σ • inflatedCoefficientReduction G i P
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction_galois {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (σ : ZInQ.Manuscript.RC.SelmerComplex.GKS K G.S)
  (P : ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G)) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction G i) (σ • P) =
    σ • (ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction G i) P
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction_galois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction_continuous

Source statement:

```lean
theorem inflatedCoefficientReduction_continuous (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    Continuous (inflatedCoefficientReduction G i)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction_continuous {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ) :
  Continuous ⇑(ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction G i)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_galois

Source statement:

```lean
theorem localCoefficientReduction_galois (G : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K G.S) (σ : Gloc K v.1)
    (P : ResMod (locMap K G.S v.1) (TateS K G.S (centralCurve G))) :
    localCoefficientReduction G i v (σ • P) = σ • localCoefficientReduction G i v P
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_galois {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S) (σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
  (P :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K G.S ↑v)
      (ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G))) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction G i v) (σ • P) =
    σ • (ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction G i v) P
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_galois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_continuous

Source statement:

```lean
theorem localCoefficientReduction_continuous (G : GenuineKummerData K E₀ hZ) (i : ℕ)
    (v : Places K G.S) : Continuous (localCoefficientReduction G i v)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_continuous {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S) :
  Continuous ⇑(ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction G i v)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralZ_cocycle

Source statement:

```lean
theorem finiteCentralZ_cocycle (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S) :
    ∀ z ∈ finiteCentralZ G i v,
      contD (Acoef i) (Gloc K v.1) (ResMod (locMap K G.S v.1) (finiteCentralModule G i)) 1 z = 0
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralZ_cocycle {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S)
  (z :
    ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
        (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
        (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K G.S ↑v)
          (ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralModule G i))
        1)) :
  z ∈ ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralZ G i v →
    (ZInQ.Manuscript.RC.CoefModules.contD (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
          (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
          (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K G.S ↑v)
            (ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralModule G i))
          1)
        z =
      0
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralZ_cocycle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility.span_mem

Source statement:

```lean
theorem CentralReductionCompatibility.span_mem (G : GenuineKummerData K E₀ hZ)
    (H : CentralReductionCompatibility G) (i : ℕ) (v : Places K G.S) :
    ∀ z ∈ tateKummerZ (centralCurve G) (centralFullTorsion G) v.1,
      cochainCoefficientMap (localCoefficientReduction G i v)
        (localCoefficientReduction_continuous G i v) 1 z ∈
      finiteCentralZ G i v ⊔
        contB1 (Acoef i) (Gloc K v.1) (ResMod (locMap K G.S v.1) (finiteCentralModule G i))
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility.span_mem {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ)
  (H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S)
  (z :
    ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain ℤ_[2] (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
        (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K G.S ↑v)
          (ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G)))
        1)) :
  z ∈
      ZInQ.Manuscript.RC53Assist.CentralKummer.tateKummerZ (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G)
        ⋯ ↑v →
    (ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap
          (ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction G i v) ⋯ 1)
        z ∈
      ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralZ G i v ⊔
        ZInQ.Manuscript.RC.CoefModules.contB1 (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
          (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
          (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K G.S ↑v)
            (ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralModule G i))
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility.span_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.simpleCentralSelData_eq

Source statement:

```lean
theorem simpleCentralSelData_eq (G : GenuineKummerData K E₀ hZ) (i : ℕ) :
    simpleCentralSelData G i = centralKummerSelData G.W G.s G.hs G.hs0 G.hFull i
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.simpleCentralSelData_eq {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.simpleCentralSelData G i =
    ZInQ.Contrib.RC53Assist.Calibration.centralKummerSelData G.W G.s ⋯ ⋯ ⋯ i
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.simpleCentralSelData_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisMatrix_isUnit_det

Source statement:

```lean
theorem basisMatrix_isUnit_det (M : IntegralCentralModel G H x₁ x₂ x₃) (n : ℤ) :
    IsUnit (M.basisMatrix n).det
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisMatrix_isUnit_det {K : Type} [Field K]
  [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G} {x₁ x₂ x₃ : ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃) (n : ℤ) :
  IsUnit (M.basisMatrix n).det
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisMatrix_isUnit_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisMatrix_valuation

Source statement:

```lean
theorem basisMatrix_valuation (M : IntegralCentralModel G H x₁ x₂ x₃) (n : ℤ) :
    (M.basisMatrix n).det.valuation = 0
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisMatrix_valuation {K : Type} [Field K]
  [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G} {x₁ x₂ x₃ : ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃) (n : ℤ) :
  (M.basisMatrix n).det.valuation = 0
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisMatrix_valuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finiteComparison_quasiIso

Source statement:

```lean
theorem finiteComparison_quasiIso (M : IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) (hi : i ≠ 0) :
    QuasiIso (M.finiteComparison i)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finiteComparison_quasiIso {K : Type} [Field K]
  [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G} {x₁ x₂ x₃ : ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) (hi : i ≠ 0) :
  QuasiIso (M.finiteComparison i)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finiteComparison_quasiIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finite_orders

Source statement:

```lean
theorem finite_orders (M : IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) (hi : i ≠ 0) :
    Nat.card (G.selH i 0) = cycOrder i x₁ ∧
      Nat.card (G.selH i 2) = 2 ^ (i * i) * cycOrder i x₂ * cycOrder i x₃ ∧
      Nat.card (G.selH i 3) = cycOrder i x₃
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finite_orders {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G} {x₁ x₂ x₃ : ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) (hi : i ≠ 0) :
  Nat.card ↑(G.selH i 0) = ZInQ.Contrib.RC53Assist.Calibration.cycOrder i x₁ ∧
    Nat.card ↑(G.selH i 2) =
        2 ^ (i * i) * ZInQ.Contrib.RC53Assist.Calibration.cycOrder i x₂ *
          ZInQ.Contrib.RC53Assist.Calibration.cycOrder i x₃ ∧
      Nat.card ↑(G.selH i 3) = ZInQ.Contrib.RC53Assist.Calibration.cycOrder i x₃
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finite_orders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.diskTie

Source statement:

```lean
theorem diskTie (M : IntegralCentralModel G H x₁ x₂ x₃) : DiskTie G x₁ x₂ x₃
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.diskTie {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G} {x₁ x₂ x₃ : ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃) :
  ZInQ.Contrib.RC53Assist.Calibration.DiskTie G x₁ x₂ x₃
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.diskTie' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.disk_valuations

Source statement:

```lean
theorem disk_valuations (M : IntegralCentralModel G H x₁ x₂ x₃) {tA shaA : ℕ}
    (A : DiskArith G tA shaA) :
    x₁.valuation = padicValNat 2 tA ∧ x₂.valuation = padicValNat 2 shaA ∧
      x₃.valuation = padicValNat 2 tA
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.disk_valuations {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G} {x₁ x₂ x₃ : ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃) {tA shaA : ℕ}
  (A : ZInQ.Contrib.RC53Assist.Calibration.DiskArith G tA shaA) :
  x₁.valuation = padicValNat 2 tA ∧ x₂.valuation = padicValNat 2 shaA ∧ x₃.valuation = padicValNat 2 tA
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.disk_valuations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.pointCurveCast_some

Source statement:

```lean
theorem pointCurveCast_some {F : Type} [Field F] {B B' : WeierstrassCurve F} (e : B = B')
    {x y : AlgebraicClosure F} (hxy : (B.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x y) :
    pointCurveCast e (ptEquiv F B (.some x y hxy)) =
      ptEquiv F B' (.some x y (e ▸ hxy))
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.pointCurveCast_some {F : Type} [Field F] {B B' : WeierstrassCurve F}
  (e : B = B') {x y : AlgebraicClosure F} (hxy : (B.baseChange (AlgebraicClosure F)).toAffine.Nonsingular x y) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.pointCurveCast e)
      ((ZInQ.Manuscript.RC.CoefModules.ptEquiv F B) (WeierstrassCurve.Affine.Point.some x y hxy)) =
    (ZInQ.Manuscript.RC.CoefModules.ptEquiv F B') (WeierstrassCurve.Affine.Point.some x y ⋯)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.pointCurveCast_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast_coe

Source statement:

```lean
theorem torsionCurveCast_coe {F : Type} [Field F] {B B' : WeierstrassCurve F} (e : B = B')
    (n : ℕ) (P : TorsAlg F B n) :
    (torsionCurveCast e n P : PtAlg F B') = pointCurveCast e (P : PtAlg F B)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast_coe {F : Type} [Field F] {B B' : WeierstrassCurve F}
  (e : B = B') (n : ℕ) (P : ZInQ.Manuscript.RC.CoefModules.TorsAlg F B n) :
  ↑((ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast e n) P) =
    (ZInQ.Contrib.RC53Assist.CalibrationIntegral.pointCurveCast e) ↑P
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast_coe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_compPt

Source statement:

```lean
theorem globalTwistPointEquiv_compPt {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (v : HeightOneSpectrum (𝓞 K))
    (P : ((twistK W h).baseChange (KS K S)).toAffine.Point) :
    compPt W v (globalTwistPointEquiv W s hs hs0 P) =
      twistPt (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
        two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v)
          (pointCurveCast (localTwist_eq_baseChange W h v).symm (compPt (twistK W h) v P))
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_compPt {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h) (hs0 : s ≠ 0)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
  (P :
    ((ZInQ.Manuscript.RC.TwistDictionary.twistK W h).baseChange
          (ZInQ.Manuscript.RC.CoefModules.KS K S)).toAffine.Point) :
  (ZInQ.Manuscript.RC.KummerMaps.compPt W v)
      ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv W s hs hs0) P) =
    (ZInQ.Manuscript.RC.KummerMaps.twistPt (W.baseChange (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
        ((algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) h) ⋯ ⋯ ⋯)
      ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.pointCurveCast ⋯)
        ((ZInQ.Manuscript.RC.KummerMaps.compPt (ZInQ.Manuscript.RC.TwistDictionary.twistK W h) v) P))
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv_compPt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv_compTors

Source statement:

```lean
theorem globalTwistTorsEquiv_compTors {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K) (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (v : HeightOneSpectrum (𝓞 K)) (i : ℕ)
    (P : TorsS K S (twistK W h) ((2 ^ i : ℕ) : ℤ)) :
    compTors W (2 ^ i) v (globalTwistTorsEquiv W s hs hs0 i P) =
      twistTors (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
        two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v) (2 ^ i)
          (torsionCurveCast (localTwist_eq_baseChange W h v).symm (2 ^ i)
            (compTors (twistK W h) (2 ^ i) v P))
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv_compTors {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h) (hs0 : s ≠ 0)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (i : ℕ)
  (P : ZInQ.Manuscript.RC.CoefModules.TorsS K S (ZInQ.Manuscript.RC.TwistDictionary.twistK W h) ↑(2 ^ i)) :
  (ZInQ.Manuscript.RC.KummerMaps.compTors W (2 ^ i) v)
      ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv W s hs hs0 i) P) =
    (ZInQ.Manuscript.RC.KummerMaps.twistTors (W.baseChange (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v))
        ((algebraMap K (IsDedekindDomain.HeightOneSpectrum.adicCompletion K v)) h) ⋯ ⋯ ⋯ (2 ^ i))
      ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast ⋯ (2 ^ i))
        ((ZInQ.Manuscript.RC.KummerMaps.compTors (ZInQ.Manuscript.RC.TwistDictionary.twistK W h) (2 ^ i) v) P))
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv_compTors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.integerCoefficientMap_continuous

Source statement:

```lean
theorem integerCoefficientMap_continuous (ι : TorsAlg F B m →+ N) :
    Continuous (integerCoefficientMap (A := A) ι)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.integerCoefficientMap_continuous {F : Type} [Field F]
  {B : WeierstrassCurve F} {m : ℕ} {A : Type} [CommRing A] {N : Type} [AddCommGroup N] [Module A N] [TopologicalSpace N]
  (ι : ZInQ.Manuscript.RC.CoefModules.TorsAlg F B m →+ N) :
  Continuous ⇑(ZInQ.Contrib.RC53Assist.CalibrationIntegral.integerCoefficientMap ι)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.integerCoefficientMap_continuous' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerCocycleOf_pushforward_mem

Source statement:

```lean
theorem kummerCocycleOf_pushforward_mem (ι : TorsAlg F B m →+ N)
    (hι : ∀ (σ : Field.absoluteGaloisGroup F) (a : TorsAlg F B m), ι (σ • a) = σ • ι a)
    {P : B.toAffine.Point} {Q : PtAlg F B} (hQ : m • Q = basePt F B P) :
    cochainCoefficientMap (integerCoefficientMap (A := A) ι) (integerCoefficientMap_continuous (A
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerCocycleOf_pushforward_mem {F : Type} [Field F] [CharZero F]
  [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic] {m : ℕ} [NeZero m] {A : Type} [CommRing A] {N : Type}
  [AddCommGroup N] [Module A N] [DistribMulAction (Field.absoluteGaloisGroup F) N]
  [SMulCommClass (Field.absoluteGaloisGroup F) A N] [TopologicalSpace N] [DiscreteTopology N]
  [ContinuousSMul (Field.absoluteGaloisGroup F) N] (ι : ZInQ.Manuscript.RC.CoefModules.TorsAlg F B m →+ N)
  (hι : ∀ (σ : Field.absoluteGaloisGroup F) (a : ZInQ.Manuscript.RC.CoefModules.TorsAlg F B m), ι (σ • a) = σ • ι a)
  {P : B.toAffine.Point} {Q : ZInQ.Manuscript.RC.CoefModules.PtAlg F B}
  (hQ : m • Q = (ZInQ.Manuscript.RC.CoefModules.basePt F B) P) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap
        (ZInQ.Contrib.RC53Assist.CalibrationIntegral.integerCoefficientMap ι) ⋯ 1)
      (ZInQ.Manuscript.RC.CoefModules.kummerCocycleOf F B m hQ) ∈
    ZInQ.Manuscript.RC.CoefModules.kummerZ' A ι ⊔
      ZInQ.Manuscript.RC.CoefModules.contB1 A (Field.absoluteGaloisGroup F) N
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerCocycleOf_pushforward_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast_galois

Source statement:

```lean
theorem torsionCurveCast_galois {B' : WeierstrassCurve F} (e : B = B') (n : ℕ)
    (σ : Field.absoluteGaloisGroup F) (P : TorsAlg F B n) :
    torsionCurveCast e n (σ • P) = σ • torsionCurveCast e n P
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast_galois {F : Type} [Field F] {B B' : WeierstrassCurve F}
  (e : B = B') (n : ℕ) (σ : Field.absoluteGaloisGroup F) (P : ZInQ.Manuscript.RC.CoefModules.TorsAlg F B n) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast e n) (σ • P) =
    σ • (ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast e n) P
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast_galois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerZ'_curveCast

Source statement:

```lean
theorem kummerZ'_curveCast {B' : WeierstrassCurve F} [B'.IsElliptic] (e : B = B')
    (ι : TorsAlg F B' m →+ N) :
    kummerZ' A (ι.comp (torsionCurveCast e m).toAddMonoidHom) = kummerZ' A ι
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerZ'_curveCast {F : Type} [Field F] [CharZero F] [DecidableEq F]
  {B : WeierstrassCurve F} [B.IsElliptic] {m : ℕ} [NeZero m] {A : Type} [CommRing A] {N : Type} [AddCommGroup N]
  [Module A N] [DistribMulAction (Field.absoluteGaloisGroup F) N] [SMulCommClass (Field.absoluteGaloisGroup F) A N]
  [TopologicalSpace N] [DiscreteTopology N] {B' : WeierstrassCurve F} [B'.IsElliptic] (e : B = B')
  (ι : ZInQ.Manuscript.RC.CoefModules.TorsAlg F B' m →+ N) :
  ZInQ.Manuscript.RC.CoefModules.kummerZ' A
      (ι.comp (ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast e m).toAddMonoidHom) =
    ZInQ.Manuscript.RC.CoefModules.kummerZ' A ι
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerZ'_curveCast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.localTwistIota_galois

Source statement:

```lean
theorem localTwistIota_galois (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S)
    (σ : Gloc K v.1)
    (P : TorsAlg (v.1.adicCompletion K) ((centralCurve G).baseChange (v.1.adicCompletion K)) (2 ^ i)) :
    localTwistIota G i v (σ • P) = σ • localTwistIota G i v P
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.localTwistIota_galois {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S) (σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
  (P :
    ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
      ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G).baseChange
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))
      (2 ^ i)) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.localTwistIota G i v) (σ • P) =
    σ • (ZInQ.Contrib.RC53Assist.CalibrationIntegral.localTwistIota G i v) P
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.localTwistIota_galois' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_eq

Source statement:

```lean
theorem localCoefficientReduction_eq (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S)
    (P : ResMod (locMap K G.S v.1) (TateS K G.S (centralCurve G))) :
    localCoefficientReduction G i v P =
      localTwistIota G i v (compTors (centralCurve G) (2 ^ i) v.1 (projLev i P))
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_eq {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S)
  (P :
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K G.S ↑v)
      (ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G))) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction G i v) P =
    (ZInQ.Contrib.RC53Assist.CalibrationIntegral.localTwistIota G i v)
      ((ZInQ.Manuscript.RC.KummerMaps.compTors (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G) (2 ^ i) ↑v)
        ((ZInQ.Manuscript.RC.LambdaCoef.projLev i) P))
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_tateKummer

Source statement:

```lean
theorem localCoefficientReduction_tateKummer (G : GenuineKummerData K E₀ hZ) (i : ℕ) (v : Places K G.S)
    (P : ((centralCurve G).baseChange (v.1.adicCompletion K)).toAffine.Point) :
    cochainCoefficientMap (localCoefficientReduction G i v)
      (localCoefficientReduction_continuous G i v) 1
        (tateKummerCocycle (centralCurve G) (centralFullTorsion G) v.1 P) =
      cochainCoefficientMap (integerCoefficientMap (A
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_tateKummer {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S)
  (P :
    ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G).baseChange
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)).toAffine.Point) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap
        (ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction G i v) ⋯ 1)
      (ZInQ.Manuscript.RC53Assist.CentralKummer.tateKummerCocycle
        (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G) ⋯ (↑v) P) =
    (ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap
        (ZInQ.Contrib.RC53Assist.CalibrationIntegral.integerCoefficientMap
          (ZInQ.Contrib.RC53Assist.CalibrationIntegral.localTwistIota G i v))
        ⋯ 1)
      (ZInQ.Manuscript.RC.CoefModules.kummerCocycleOf (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
        ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G).baseChange
          (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))
        (2 ^ i) ⋯)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction_tateKummer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralReductionCompatibility

Source statement:

```lean
theorem centralReductionCompatibility (G : GenuineKummerData K E₀ hZ) : CentralReductionCompatibility G
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralReductionCompatibility {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralReductionCompatibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.diskTie_of_integralCentralModel

Source statement:

```lean
theorem diskTie_of_integralCentralModel (G : GenuineKummerData K E₀ hZ) (x₁ x₂ x₃ : ℤ_[2])
    (M : CanonicalIntegralCentralModel G x₁ x₂ x₃) : DiskTie G x₁ x₂ x₃
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.diskTie_of_integralCentralModel {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ)
  (x₁ x₂ x₃ : ℤ_[2]) (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CanonicalIntegralCentralModel G x₁ x₂ x₃) :
  ZInQ.Contrib.RC53Assist.Calibration.DiskTie G x₁ x₂ x₃
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.diskTie_of_integralCentralModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD_sq

Source statement:

```lean
theorem blockD_sq (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) (n : ℕ) :
    blockD B₁ B₂ B₃ n ≫ blockD B₁ B₂ B₃ (n + 1) = 0
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD_sq {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) (n : ℕ) :
  CategoryTheory.CategoryStruct.comp (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD B₁ B₂ B₃ n)
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD B₁ B₂ B₃ (n + 1)) =
    0
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d0

Source statement:

```lean
theorem blockComplex_d0 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    ((blockComplex B₁ B₂ B₃).d 0 1).hom = blockD0 B₁
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d0 {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ModuleCat.Hom.hom ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃).d 0 1) =
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD0 B₁
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d1

Source statement:

```lean
theorem blockComplex_d1 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    ((blockComplex B₁ B₂ B₃).d 1 2).hom = blockD1 B₂
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d1 {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ModuleCat.Hom.hom ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃).d 1 2) =
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD1 B₂
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d2

Source statement:

```lean
theorem blockComplex_d2 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    ((blockComplex B₁ B₂ B₃).d 2 3).hom = blockD2 B₃
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d2 {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ModuleCat.Hom.hom ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃).d 2 3) =
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD2 B₃
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_dneg

Source statement:

```lean
theorem blockComplex_dneg (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) : ((blockComplex B₁ B₂ B₃).d (-1) 0).hom = 0
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_dneg {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ModuleCat.Hom.hom ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃).d (-1) 0) = 0
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_dneg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d3

Source statement:

```lean
theorem blockComplex_d3 (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
    (B₃ : Matrix (Fin m₃) (Fin m₃) R) : ((blockComplex B₁ B₂ B₃).d 3 4).hom = 0
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d3 {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ModuleCat.Hom.hom ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃).d 3 4) = 0
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex_d3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.matrix_map_mulVec_scalar

Source statement:

```lean
theorem matrix_map_mulVec_scalar {m : ℕ} (φ : R →+* S) (B : Matrix (Fin m) (Fin m) R)
    (a : Fin m → R) (b : S) :
    (B.map φ).mulVecLin (fun j => φ (a j) * b) = fun j => φ (B.mulVecLin a j) * b
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.matrix_map_mulVec_scalar {R S : Type} [CommRing R] [CommRing S] {m : ℕ}
  (φ : R →+* S) (B : Matrix (Fin m) (Fin m) R) (a : Fin m → R) (b : S) :
  ((B.map ⇑φ).mulVecLin fun j => φ (a j) * b) = fun j => φ (B.mulVecLin a j) * b
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.matrix_map_mulVec_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.block_card0

Source statement:

```lean
theorem block_card0 [Finite R] (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    Nat.card ((blockComplex B₁ B₂ B₃).homology 0) =
      Nat.card ((Fin m₁ → R) ⧸ LinearMap.range B₁.mulVecLin)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.block_card0 {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ} [Finite R]
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  Nat.card ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃) 0) =
    Nat.card ((Fin m₁ → R) ⧸ B₁.mulVecLin.range)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.block_card0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.block_card2

Source statement:

```lean
theorem block_card2 [Finite R] (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    Nat.card ((blockComplex B₁ B₂ B₃).homology 2) =
      Nat.card R * Nat.card ((Fin m₂ → R) ⧸ LinearMap.range B₂.mulVecLin) *
        Nat.card ((Fin m₃ → R) ⧸ LinearMap.range B₃.mulVecLin)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.block_card2 {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ} [Finite R]
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  Nat.card ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃) 2) =
    Nat.card R * Nat.card ((Fin m₂ → R) ⧸ B₂.mulVecLin.range) * Nat.card ((Fin m₃ → R) ⧸ B₃.mulVecLin.range)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.block_card2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.block_card3

Source statement:

```lean
theorem block_card3 (B₁ : Matrix (Fin m₁) (Fin m₁) R)
    (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
    Nat.card ((blockComplex B₁ B₂ B₃).homology 3) =
      Nat.card ((Fin m₃ → R) ⧸ LinearMap.range B₃.mulVecLin)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.block_card3 {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  Nat.card ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃) 3) =
    Nat.card ((Fin m₃ → R) ⧸ B₃.mulVecLin.range)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.block_card3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.card_matrixDisk_cycOrder

Source statement:

```lean
theorem card_matrixDisk_cycOrder {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ_[2]) (hB : B.det ≠ 0)
    (i : ℕ) (hi : i ≠ 0) (hv : B.det.valuation ≤ i) :
    Nat.card ((Fin m → Acoef i) ⧸ LinearMap.range (B.map (constRed i)).mulVecLin) =
      cycOrder i B.det
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.card_matrixDisk_cycOrder {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ_[2])
  (hB : B.det ≠ 0) (i : ℕ) (hi : i ≠ 0) (hv : B.det.valuation ≤ i) :
  Nat.card
      ((Fin m → ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) ⧸
        (B.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i)).mulVecLin.range) =
    ZInQ.Contrib.RC53Assist.Calibration.cycOrder i B.det
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.card_matrixDisk_cycOrder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteBlock_orders

Source statement:

```lean
theorem finiteBlock_orders (B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2])
    (B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]) (B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2])
    (h₁ : B₁.det ≠ 0) (h₂ : B₂.det ≠ 0) (h₃ : B₃.det ≠ 0)
    (i : ℕ) (hi : i ≠ 0) (hv₁ : B₁.det.valuation ≤ i) (hv₂ : B₂.det.valuation ≤ i)
    (hv₃ : B₃.det.valuation ≤ i) :
    Nat.card ((blockComplex (B₁.map (constRed i)) (B₂.map (constRed i))
      (B₃.map (constRed i))).homology 0) = cycOrder i B₁.det ∧
      Nat.card ((blockComplex (B₁.map (constRed i)) (B₂.map (constRed i))
        (B₃.map (constRed i))).homology 2) =
          2 ^ (i * i) * cycOrder i B₂.det * cycOrder i B₃.det ∧
      Nat.card ((blockComplex (B₁.map (constRed i)) (B₂.map (constRed i))
        (B₃.map (constRed i))).homology 3) = cycOrder i B₃.det
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteBlock_orders {m₁ m₂ m₃ : ℕ} (B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2])
  (B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]) (B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]) (h₁ : B₁.det ≠ 0) (h₂ : B₂.det ≠ 0)
  (h₃ : B₃.det ≠ 0) (i : ℕ) (hi : i ≠ 0) (hv₁ : B₁.det.valuation ≤ i) (hv₂ : B₂.det.valuation ≤ i)
  (hv₃ : B₃.det.valuation ≤ i) :
  Nat.card
        ↑(HomologicalComplex.homology
            (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex
              (B₁.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i))
              (B₂.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i))
              (B₃.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i)))
            0) =
      ZInQ.Contrib.RC53Assist.Calibration.cycOrder i B₁.det ∧
    Nat.card
          ↑(HomologicalComplex.homology
              (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex
                (B₁.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i))
                (B₂.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i))
                (B₃.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i)))
              2) =
        2 ^ (i * i) * ZInQ.Contrib.RC53Assist.Calibration.cycOrder i B₂.det *
          ZInQ.Contrib.RC53Assist.Calibration.cycOrder i B₃.det ∧
      Nat.card
          ↑(HomologicalComplex.homology
              (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex
                (B₁.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i))
                (B₂.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i))
                (B₃.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i)))
              3) =
        ZInQ.Contrib.RC53Assist.Calibration.cycOrder i B₃.det
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteBlock_orders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.basisMatrix_isUnit_det

Source statement:

```lean
theorem basisMatrix_isUnit_det (M : IntegralBlockCentralModel G B₁ B₂ B₃) (n : ℤ) :
    IsUnit (M.basisMatrix n).det
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.basisMatrix_isUnit_det {K : Type} [Field K]
  [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ}
  {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ} {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]}
  {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) (n : ℤ) :
  IsUnit (M.basisMatrix n).det
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.basisMatrix_isUnit_det' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.inverseDeterminantBasisFactor_valuation

Source statement:

```lean
theorem inverseDeterminantBasisFactor_valuation (M : IntegralBlockCentralModel G B₁ B₂ B₃) :
    (M.inverseDeterminantBasisFactor : ℤ_[2]).valuation = 0
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.inverseDeterminantBasisFactor_valuation {K : Type}
  [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ}
  {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ} {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]}
  {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) :
  (↑M.inverseDeterminantBasisFactor).valuation = 0
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.inverseDeterminantBasisFactor_valuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finiteComparison_quasiIso

Source statement:

```lean
theorem finiteComparison_quasiIso (M : IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) (hi : i ≠ 0) :
    QuasiIso (M.finiteComparison i)
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finiteComparison_quasiIso {K : Type} [Field K]
  [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ}
  {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ} {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]}
  {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) (hi : i ≠ 0) :
  QuasiIso (M.finiteComparison i)
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finiteComparison_quasiIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finite_orders

Source statement:

```lean
theorem finite_orders (M : IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) (hi : i ≠ 0)
    (hv₁ : B₁.det.valuation ≤ i) (hv₂ : B₂.det.valuation ≤ i) (hv₃ : B₃.det.valuation ≤ i) :
    Nat.card (G.selH i 0) = cycOrder i B₁.det ∧
      Nat.card (G.selH i 2) = 2 ^ (i * i) * cycOrder i B₂.det * cycOrder i B₃.det ∧
      Nat.card (G.selH i 3) = cycOrder i B₃.det
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finite_orders {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]} {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) (hi : i ≠ 0)
  (hv₁ : B₁.det.valuation ≤ i) (hv₂ : B₂.det.valuation ≤ i) (hv₃ : B₃.det.valuation ≤ i) :
  Nat.card ↑(G.selH i 0) = ZInQ.Contrib.RC53Assist.Calibration.cycOrder i B₁.det ∧
    Nat.card ↑(G.selH i 2) =
        2 ^ (i * i) * ZInQ.Contrib.RC53Assist.Calibration.cycOrder i B₂.det *
          ZInQ.Contrib.RC53Assist.Calibration.cycOrder i B₃.det ∧
      Nat.card ↑(G.selH i 3) = ZInQ.Contrib.RC53Assist.Calibration.cycOrder i B₃.det
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finite_orders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.diskTie

Source statement:

```lean
theorem diskTie (M : IntegralBlockCentralModel G B₁ B₂ B₃) : DiskTie G B₁.det B₂.det B₃.det
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.diskTie {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]} {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) :
  ZInQ.Contrib.RC53Assist.Calibration.DiskTie G B₁.det B₂.det B₃.det
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.diskTie' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.disk_valuations

Source statement:

```lean
theorem disk_valuations (M : IntegralBlockCentralModel G B₁ B₂ B₃) {tA shaA : ℕ}
    (A : DiskArith G tA shaA) :
    B₁.det.valuation = padicValNat 2 tA ∧ B₂.det.valuation = padicValNat 2 shaA ∧
      B₃.det.valuation = padicValNat 2 tA
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.disk_valuations {K : Type} [Field K]
  [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ}
  {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ} {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]}
  {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) {tA shaA : ℕ}
  (A : ZInQ.Contrib.RC53Assist.Calibration.DiskArith G tA shaA) :
  B₁.det.valuation = padicValNat 2 tA ∧ B₂.det.valuation = padicValNat 2 shaA ∧ B₃.det.valuation = padicValNat 2 tA
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.disk_valuations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.diskTie_of_integralBlockCentralModel

Source statement:

```lean
theorem diskTie_of_integralBlockCentralModel (G : GenuineKummerData K E₀ hZ)
    (B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]) (B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2])
    (B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]) (M : IntegralBlockCentralModel G B₁ B₂ B₃) :
    DiskTie G B₁.det B₂.det B₃.det
```

Elaborated type:

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.diskTie_of_integralBlockCentralModel {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ)
  (B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]) (B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]) (B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2])
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) :
  ZInQ.Contrib.RC53Assist.Calibration.DiskTie G B₁.det B₂.det B₃.det
```

Dependency report:

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.diskTie_of_integralBlockCentralModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## Other declarations and individual axiom reports

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.scalarMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.scalarMap {R : Type} [CommRing R] (x : R) : R →ₗ[R] R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.scalarMap' depends on axioms: [propext]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalTerms

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalTerms (R : Type) [CommRing R] : ℕ → ModuleCat R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalTerms' depends on axioms: [propext, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD0

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD0 {R : Type} [CommRing R] (x : R) : R →ₗ[R] R × R × R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD0' depends on axioms: [propext, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD1

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD1 {R : Type} [CommRing R] (x : R) : R × R × R →ₗ[R] R × R × R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD1' depends on axioms: [propext, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD2

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD2 {R : Type} [CommRing R] (x : R) : R × R × R →ₗ[R] R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD2' depends on axioms: [propext, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD {R : Type} [CommRing R] (x₁ x₂ x₃ : R) (n : ℕ) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalTerms R n ⟶
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalTerms R (n + 1)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalD' depends on axioms: [propext, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  CochainComplex (ModuleCat R) ℤ
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.homologyEquivOfClass

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.homologyEquivOfClass.{u_1} {R : Type} [CommRing R]
  (C : CochainComplex (ModuleCat R) ℤ) (i n j : ℤ) (hi : (ComplexShape.up ℤ).prev n = i)
  (hj : (ComplexShape.up ℤ).next n = j) {H : Type} [AddCommGroup H] [Module R H]
  (f : ↥(ModuleCat.Hom.hom (HomologicalComplex.sc' C i n j).g).ker →ₗ[R] H) (hf : Function.Surjective ⇑f)
  (hker : (HomologicalComplex.sc' C i n j).moduleCatToCycles.range = f.ker) : ↑(HomologicalComplex.homology C n) ≃ₗ[R] H
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.homologyEquivOfClass' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.class0

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.class0 {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ↥(ModuleCat.Hom.hom
          (HomologicalComplex.sc' (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) (-1) 0
              1).g).ker →ₗ[R]
    ↥(ZInQ.Contrib.RC53Assist.CalibrationIntegral.scalarMap x₁).ker
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.class0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH0Equiv

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH0Equiv {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) 0) ≃ₗ[R]
    ↥(ZInQ.Contrib.RC53Assist.CalibrationIntegral.scalarMap x₁).ker
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH0Equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.class2

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.class2 {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ↥(ModuleCat.Hom.hom
          (HomologicalComplex.sc' (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) 1 2
              3).g).ker →ₗ[R]
    R × (R ⧸ Ideal.span {x₂}) × ↥(ZInQ.Contrib.RC53Assist.CalibrationIntegral.scalarMap x₃).ker
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.class2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH2Equiv

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH2Equiv {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) 2) ≃ₗ[R]
    R × (R ⧸ Ideal.span {x₂}) × ↥(ZInQ.Contrib.RC53Assist.CalibrationIntegral.scalarMap x₃).ker
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH2Equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.class3

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.class3 {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ↥(ModuleCat.Hom.hom
          (HomologicalComplex.sc' (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) 2 3
              4).g).ker →ₗ[R]
    R ⧸ Ideal.span {x₃}
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.class3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH3Equiv

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH3Equiv {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) 3) ≃ₗ[R]
    R ⧸ Ideal.span {x₃}
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH3Equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.class1

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.class1 {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ↥(ModuleCat.Hom.hom
          (HomologicalComplex.sc' (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) 0 1
              2).g).ker →ₗ[R]
    R × (R ⧸ Ideal.span {x₁}) × ↥(ZInQ.Contrib.RC53Assist.CalibrationIntegral.scalarMap x₂).ker
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.class1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH1Equiv

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH1Equiv {R : Type} [CommRing R] (x₁ x₂ x₃ : R) :
  ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) 1) ≃ₗ[R]
    R × (R ⧸ Ideal.span {x₁}) × ↥(ZInQ.Contrib.RC53Assist.CalibrationIntegral.scalarMap x₂).ker
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalH1Equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalRank

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalRank : ℤ → ℕ
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalRank' does not depend on any axioms
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.lineCoordinates

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.lineCoordinates (R : Type) [CommRing R] : R ≃ₗ[R] Fin 1 → R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.lineCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.tripleCoordinates

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.tripleCoordinates (R : Type) [CommRing R] : (R × R × R) ≃ₗ[R] Fin 3 → R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.tripleCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.zeroCoordinates

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.zeroCoordinates (R : Type) [CommRing R] : PUnit ≃ₗ[R] Fin 0 → R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.zeroCoordinates' depends on axioms: [propext, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalCoordinates

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalCoordinates {R : Type} [CommRing R] (x₁ x₂ x₃ : R) (n : ℤ) :
  ↑((ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃).X n) ≃ₗ[R]
    Fin (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalRank n) → R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.extendedNormalCoordinates

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.extendedNormalCoordinates {R S : Type} [CommRing R] [CommRing S]
  (φ : R →+* S) (x₁ x₂ x₃ : R) (n : ℤ) :
  ↑((ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex φ
            (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃)).X
        n) ≃ₗ[S]
    ↑((ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex (φ x₁) (φ x₂) (φ x₃)).X n)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.extendedNormalCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalScalarChangeIso

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalScalarChangeIso {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
  (x₁ x₂ x₃ : R) :
  ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex φ
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex x₁ x₂ x₃) ≅
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex (φ x₁) (φ x₂) (φ x₃)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalScalarChangeIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h) (hs0 : s ≠ 0) :
  ((ZInQ.Manuscript.RC.TwistDictionary.twistK W h).baseChange (ZInQ.Manuscript.RC.CoefModules.KS K S)).toAffine.Point ≃+
    (W.baseChange (ZInQ.Manuscript.RC.CoefModules.KS K S)).toAffine.Point
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistPointEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv {K : Type} [Field K] [NumberField K]
  {S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (W : WeierstrassCurve K)
  (s : ZInQ.Manuscript.RC.CoefModules.KS K S) {h : K}
  (hs : s ^ 2 = (algebraMap K (ZInQ.Manuscript.RC.CoefModules.KS K S)) h) (hs0 : s ≠ 0) (i : ℕ) :
  ZInQ.Manuscript.RC.CoefModules.TorsS K S (ZInQ.Manuscript.RC.TwistDictionary.twistK W h) ↑(2 ^ i) ≃+
    ZInQ.Manuscript.RC.CoefModules.TorsS K S W ↑(2 ^ i)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.globalTwistTorsEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ}
  {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) : WeierstrassCurve K
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve_elliptic

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve_elliptic {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G).IsElliptic
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve_elliptic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralSelData

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralSelData {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) :
  ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData ℤ_[2]
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralSelData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralComplex

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralComplex {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) :
  CochainComplex (ModuleCat ℤ_[2]) ℤ
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralComplex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReductionAdd

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReductionAdd {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ) :
  ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (ZInQ.Manuscript.RC.TwistDictionary.twistK G.W ↑hZ) →+
    ZInQ.Manuscript.RC.CoefModules.Mcoef K G.S G.W i (ZInQ.Contrib.RC53Assist.Calibration.centralChar i G.s ⋯ ⋯)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReductionAdd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ) :
  ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S
      (ZInQ.Manuscript.RC.TwistDictionary.twistK G.W ↑hZ) →ₛₗ[ZInQ.Contrib.RC53Assist.Calibration.constRed i]
    ZInQ.Manuscript.RC.CoefModules.Mcoef K G.S G.W i (ZInQ.Contrib.RC53Assist.Calibration.centralChar i G.s ⋯ ⋯)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientReduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap {R S : Type} [CommRing R] [CommRing S] (π : R →+* S)
  (A : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx R) (B : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx S) : Type
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap' depends on axioms: [propext]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.semilinearRestriction

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.semilinearRestriction.{u_1} {R S : Type} [CommRing R] [CommRing S]
  (π : R →+* S) {M : ModuleCat R} {N : ModuleCat S} (f : ↑M →ₛₗ[π] ↑N) : M ⟶ (ModuleCat.restrictScalars π).obj N
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.semilinearRestriction' depends on axioms: [propext, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.extend

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.extend {R S : Type} [CommRing R] [CommRing S]
  {π : R →+* S} {A : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx R}
  {B : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx S}
  (f : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap π A B) :
  ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex π A.toCC ⟶ B.toCC
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.pi

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.pi {R S : Type} [CommRing R] [CommRing S]
  {π : R →+* S} {ι : Type} {A : ι → ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx R}
  {B : ι → ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx S}
  (f : (v : ι) → ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap π (A v) (B v)) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap π (ZInQ.Manuscript.RC.SelmerComplex.piCx A)
    (ZInQ.Manuscript.RC.SelmerComplex.piCx B)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.pi' depends on axioms: [propext, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.selmer

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.selmer {R S : Type} [CommRing R] [CommRing S]
  {π : R →+* S} {D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData R}
  {D' : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData S}
  (g : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap π D.G D'.G)
  (u : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap π D.U D'.U)
  (l : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap π D.L D'.L)
  (hres : ∀ (i j : ℤ) (hij : i = j) (a : ↑(D.G.X i)), (l.f j) ((D.res.f i j hij) a) = (D'.res.f i j hij) ((g.f i) a))
  (hι : ∀ (i j : ℤ) (hij : i = j) (a : ↑(D.U.X i)), (l.f j) ((D.ι.f i j hij) a) = (D'.ι.f i j hij) ((u.f i) a)) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap π
    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx D) (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx D')
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap.selmer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap {R S : Type} [CommRing R] [CommRing S] {π : R →+* S}
  {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module R M] [DistribMulAction G M]
  [SMulCommClass G R M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M] {N : Type} [AddCommGroup N]
  [Module S N] [DistribMulAction G N] [SMulCommClass G S N] [TopologicalSpace N] [ContinuousAdd N]
  [ContinuousConstSMul S N] (f : M →ₛₗ[π] N) (hfc : Continuous ⇑f) (n : ℕ) :
  ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain R G M n) →ₛₗ[π] ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain S G N n)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.continuousCoefficientComplexMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.continuousCoefficientComplexMap {R S : Type} [CommRing R] [CommRing S]
  {π : R →+* S} {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] {M : Type} [AddCommGroup M] [Module R M]
  [DistribMulAction G M] [SMulCommClass G R M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
  [ContinuousSMul G M] {N : Type} [AddCommGroup N] [Module S N] [DistribMulAction G N] [SMulCommClass G S N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul S N] [ContinuousSMul G N] (f : M →ₛₗ[π] N)
  (hfc : Continuous ⇑f) (hf : ∀ (σ : G) (a : M), f (σ • a) = σ • f a) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap π
    (ZInQ.Manuscript.RC.SelmerComplex.natCx (ZInQ.Manuscript.RC.SelmerComplex.contCochains R G M))
    (ZInQ.Manuscript.RC.SelmerComplex.natCx (ZInQ.Manuscript.RC.SelmerComplex.contCochains S G N))
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.continuousCoefficientComplexMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.cocycleCoefficientComplexMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.cocycleCoefficientComplexMap {R S : Type} [CommRing R] [CommRing S]
  {π : R →+* S} {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] {M : Type} [AddCommGroup M] [Module R M]
  [DistribMulAction G M] [SMulCommClass G R M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul R M]
  [ContinuousSMul G M] {N : Type} [AddCommGroup N] [Module S N] [DistribMulAction G N] [SMulCommClass G S N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul S N] [ContinuousSMul G N] (f : M →ₛₗ[π] N)
  (hfc : Continuous ⇑f) (hf : ∀ (σ : G) (a : M), f (σ • a) = σ • f a)
  (Z : Submodule R ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain R G M 1))
  (hZ : ∀ z ∈ Z, (ZInQ.Manuscript.RC.CoefModules.contD R G M 1) z = 0)
  (Z' : Submodule S ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain S G N 1))
  (hZ' : ∀ z ∈ Z', (ZInQ.Manuscript.RC.CoefModules.contD S G N 1) z = 0)
  (hmem :
    ∀ z ∈ Z,
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.cochainCoefficientMap f hfc 1) z ∈
        Z' ⊔ ZInQ.Manuscript.RC.CoefModules.contB1 S G N) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap π
    (ZInQ.Manuscript.RC.CoefModules.cocycleCondition Z hZ) (ZInQ.Manuscript.RC.CoefModules.cocycleCondition Z' hZ')
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.cocycleCoefficientComplexMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralModule

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralModule {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ) : Type
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralModule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ) :
  ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G) →ₛₗ[ZInQ.Contrib.RC53Assist.Calibration.constRed i]
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralModule G i
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.inflatedCoefficientReduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S) :
  ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K G.S ↑v)
      (ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S
        (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve
          G)) →ₛₗ[ZInQ.Contrib.RC53Assist.Calibration.constRed i]
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K G.S ↑v)
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralModule G i)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.localCoefficientReduction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralZ

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralZ {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S) :
  Submodule (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
    ↥(ZInQ.Manuscript.RC.SelmerComplex.contCochain (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
        (ZInQ.Manuscript.RC.SelmerComplex.Gloc K ↑v)
        (ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K G.S ↑v)
          (ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralModule G i))
        1)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralZ' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) : Prop
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.simpleCentralSelData

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.simpleCentralSelData {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ) :
  ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.simpleCentralSelData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.fullLocalCoefficientMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.fullLocalCoefficientMap {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap (ZInQ.Contrib.RC53Assist.Calibration.constRed i)
    (ZInQ.Manuscript.RC.CoefModules.locAt K G.S ℤ_[2]
      (ZInQ.Manuscript.RC.LambdaCoef.TateS K G.S (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G)) v)
    (ZInQ.Manuscript.RC.CoefModules.locAt K G.S (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i)
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralModule G i) v)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.fullLocalCoefficientMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerLocalCoefficientMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerLocalCoefficientMap {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ)
  (H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap (ZInQ.Contrib.RC53Assist.Calibration.constRed i)
    (ZInQ.Manuscript.RC53Assist.CentralKummer.tateKummerCondition
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G) ⋯ ↑v)
    (ZInQ.Manuscript.RC.KummerMaps.actualKummerAtS ⋯ G.W i G.s ⋯ ⋯
        (ZInQ.Contrib.RC53Assist.Calibration.centralChar i G.s ⋯ ⋯) ⋯ v ⋯).U
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerLocalCoefficientMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientComplexMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientComplexMap {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ)
  (H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G) (i : ℕ) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.CoefficientComplexMap (ZInQ.Contrib.RC53Assist.Calibration.constRed i)
    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralSelData G))
    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx
      (ZInQ.Contrib.RC53Assist.Calibration.centralKummerSelData G.W G.s ⋯ ⋯ ⋯ i))
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCoefficientComplexMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralReductionMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralReductionMap {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ)
  (H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G) (i : ℕ) :
  ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex (ZInQ.Contrib.RC53Assist.Calibration.constRed i)
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralComplex G) ⟶
    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx
        (ZInQ.Contrib.RC53Assist.Calibration.centralKummerSelData G.W G.s ⋯ ⋯ ⋯ i)).toCC
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralReductionMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralReductionHomologyIso

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralReductionHomologyIso {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ)
  (H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G) (i : ℕ)
  [QuasiIso (ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralReductionMap G H i)] (n : ℤ) :
  HomologicalComplex.homology
      (ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex (ZInQ.Contrib.RC53Assist.Calibration.constRed i)
        (ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralComplex G))
      n ≅
    G.selH i n
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralReductionHomologyIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ)
  (H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G) (x₁ x₂ x₃ : ℤ_[2]) : Type 1
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisComparison

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisComparison {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G} {x₁ x₂ x₃ : ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃) (n : ℤ) :
  (Fin (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalRank n) → ℤ_[2]) ≃ₗ[ℤ_[2]]
    Fin (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalRank n) → ℤ_[2]
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisMatrix

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisMatrix {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G} {x₁ x₂ x₃ : ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃) (n : ℤ) :
  Matrix (Fin (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalRank n))
    (Fin (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalRank n)) ℤ_[2]
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.basisMatrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.fibreMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.fibreMap {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G} {x₁ x₂ x₃ : ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) :
  ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex (ZInQ.Contrib.RC53Assist.Calibration.constRed i) M.P ⟶
    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx
        (ZInQ.Contrib.RC53Assist.Calibration.centralKummerSelData G.W G.s ⋯ ⋯ ⋯ i)).toCC
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.fibreMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finiteComparison

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finiteComparison {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G} {x₁ x₂ x₃ : ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₁)
      ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₂) ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₃) ⟶
    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx
        (ZInQ.Contrib.RC53Assist.Calibration.centralKummerSelData G.W G.s ⋯ ⋯ ⋯ i)).toCC
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finiteComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finiteHomologyIso

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finiteHomologyIso {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G} {x₁ x₂ x₃ : ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃) (i : ℕ) (hi : i ≠ 0) (n : ℤ) :
  HomologicalComplex.homology
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.normalComplex ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₁)
        ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₂) ((ZInQ.Contrib.RC53Assist.Calibration.constRed i) x₃))
      n ≅
    G.selH i n
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel.finiteHomologyIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerCoordinateBlockOfIntegralModel

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerCoordinateBlockOfIntegralModel {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {n : ℕ} {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])}
  {zK wK : Fin n → PowerSeries ℚ_[2]} {j vL m : ℤ} {tA shaA : ℕ}
  (S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) (hSfin : S.Finite) (M : Type)
  [AddCommGroup M] [Module (PowerSeries ℚ_[2]) M] [DistribMulAction (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  [SMulCommClass (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) (PowerSeries ℚ_[2]) M] [TopologicalSpace M]
  [ContinuousAdd M] [ContinuousConstSMul (PowerSeries ℚ_[2]) M]
  [ContinuousSMul (ZInQ.Manuscript.RC.SelmerComplex.GKS K S) M]
  (Δ : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions K S (PowerSeries ℚ_[2]) M)
  (hinj : ∀ (v : ZInQ.Manuscript.RC.SelmerComplex.Places K S) (k : ℤ), Function.Injective ⇑((Δ.i v).f k k ⋯))
  (I : ZInQ.Manuscript.RC.SelmerComplex.GenuineKummerModelIdentification K S (PowerSeries ℚ_[2]) M Δ)
  (link :
    ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord DK zK wK
      (ZInQ.Contrib.CloudB3RC53.Torsion.KummerModelIdentification.coord I))
  (aP bP : PowerSeries ℚ_[2]) (ha : I.a = PowerSeries.C ↑m * aP) (hb : I.b = PowerSeries.C ↑m * bP)
  (haP : ZInQ.Manuscript.RC.v2 (ZInQ.Manuscript.RC.central aP) = ↑(j + vL))
  (hbP : ZInQ.Manuscript.RC.v2 (ZInQ.Manuscript.RC.central bP) = ↑(j + vL))
  (hu₀ : ZInQ.Manuscript.RC.v2 (ZInQ.Manuscript.RC.central I.u₀) = 0)
  (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (x₁ x₂ x₃ : ℤ_[2])
  (hx₁ : ZInQ.Manuscript.RC.central ↑I.δ₁ = ↑x₁) (hx₂ : ZInQ.Manuscript.RC.central ↑I.δ₂ = ↑x₂)
  (hx₃ : ZInQ.Manuscript.RC.central ↑I.δ₃ = ↑x₃)
  (H : ZInQ.Contrib.RC53Assist.CalibrationIntegral.CentralReductionCompatibility G)
  (J : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralCentralModel G H x₁ x₂ x₃)
  (A : ZInQ.Contrib.RC53Assist.Calibration.DiskArith G tA shaA) :
  ZInQ.Contrib.RC53Assist.Calibration.KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.kummerCoordinateBlockOfIntegralModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.pointCurveCast

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.pointCurveCast {F : Type} [Field F] {B B' : WeierstrassCurve F}
  (e : B = B') : ZInQ.Manuscript.RC.CoefModules.PtAlg F B ≃+ ZInQ.Manuscript.RC.CoefModules.PtAlg F B'
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.pointCurveCast' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast {F : Type} [Field F] {B B' : WeierstrassCurve F}
  (e : B = B') (n : ℕ) : ZInQ.Manuscript.RC.CoefModules.TorsAlg F B n ≃+ ZInQ.Manuscript.RC.CoefModules.TorsAlg F B' n
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.torsionCurveCast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.integerCoefficientMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.integerCoefficientMap {F : Type} [Field F] {B : WeierstrassCurve F} {m : ℕ}
  {A : Type} [CommRing A] {N : Type} [AddCommGroup N] [Module A N]
  (ι : ZInQ.Manuscript.RC.CoefModules.TorsAlg F B m →+ N) :
  ZInQ.Manuscript.RC.CoefModules.TorsAlg F B m →ₛₗ[Int.castRingHom A] N
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.integerCoefficientMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.localTwistIota

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.localTwistIota {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ)
  (v : ZInQ.Manuscript.RC.SelmerComplex.Places K G.S) :
  ZInQ.Manuscript.RC.CoefModules.TorsAlg (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v)
      ((ZInQ.Contrib.RC53Assist.CalibrationIntegral.centralCurve G).baseChange
        (IsDedekindDomain.HeightOneSpectrum.adicCompletion K ↑v))
      (2 ^ i) →+
    ZInQ.Manuscript.RC.SelmerComplex.ResMod (ZInQ.Manuscript.RC.SelmerComplex.locMap K G.S ↑v)
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.finiteCentralModule G i)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.localTwistIota' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.canonicalCentralReductionMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.canonicalCentralReductionMap {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ) (i : ℕ) :
  ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex (ZInQ.Contrib.RC53Assist.Calibration.constRed i)
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.compactCentralComplex G) ⟶
    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx
        (ZInQ.Contrib.RC53Assist.Calibration.centralKummerSelData G.W G.s ⋯ ⋯ ⋯ i)).toCC
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.canonicalCentralReductionMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.CanonicalIntegralCentralModel

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.CanonicalIntegralCentralModel {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ)
  (x₁ x₂ x₃ : ℤ_[2]) : Type 1
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.CanonicalIntegralCentralModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockTerms

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockTerms (R : Type) [CommRing R] (m₁ m₂ m₃ : ℕ) : ℕ → ModuleCat R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockTerms' depends on axioms: [propext, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD0

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD0 {R : Type} [CommRing R] {m₁ m₂ : ℕ}
  (B : Matrix (Fin m₁) (Fin m₁) R) : (Fin m₁ → R) →ₗ[R] R × (Fin m₁ → R) × (Fin m₂ → R)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD1

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD1 {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B : Matrix (Fin m₂) (Fin m₂) R) : R × (Fin m₁ → R) × (Fin m₂ → R) →ₗ[R] R × (Fin m₂ → R) × (Fin m₃ → R)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD2

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD2 {R : Type} [CommRing R] {m₂ m₃ : ℕ}
  (B : Matrix (Fin m₃) (Fin m₃) R) : R × (Fin m₂ → R) × (Fin m₃ → R) →ₗ[R] Fin m₃ → R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) (n : ℕ) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockTerms R m₁ m₂ m₃ n ⟶
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockTerms R m₁ m₂ m₃ (n + 1)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockD' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  CochainComplex (ModuleCat R) ℤ
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockClass0

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockClass0 {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ↥(ModuleCat.Hom.hom
          (HomologicalComplex.sc' (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃) (-1) 0
              1).g).ker →ₗ[R]
    ↥B₁.mulVecLin.ker
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockClass0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockH0Equiv

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockH0Equiv {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃) 0) ≃ₗ[R]
    ↥B₁.mulVecLin.ker
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockH0Equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockClass2

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockClass2 {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ↥(ModuleCat.Hom.hom
          (HomologicalComplex.sc' (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃) 1 2
              3).g).ker →ₗ[R]
    R × ((Fin m₂ → R) ⧸ B₂.mulVecLin.range) × ↥B₃.mulVecLin.ker
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockClass2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockH2Equiv

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockH2Equiv {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃) 2) ≃ₗ[R]
    R × ((Fin m₂ → R) ⧸ B₂.mulVecLin.range) × ↥B₃.mulVecLin.ker
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockH2Equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockClass3

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockClass3 {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ↥(ModuleCat.Hom.hom
          (HomologicalComplex.sc' (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃) 2 3
              4).g).ker →ₗ[R]
    (Fin m₃ → R) ⧸ B₃.mulVecLin.range
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockClass3' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockH3Equiv

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockH3Equiv {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ↑(HomologicalComplex.homology (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃) 3) ≃ₗ[R]
    (Fin m₃ → R) ⧸ B₃.mulVecLin.range
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockH3Equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndex

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndex (m₁ m₂ m₃ : ℕ) : ℤ → Type
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndex' does not depend on any axioms
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndexFintype

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndexFintype (m₁ m₂ m₃ : ℕ) (n : ℤ) :
  Fintype (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndex m₁ m₂ m₃ n)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndexFintype' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndexDecidableEq

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndexDecidableEq (m₁ m₂ m₃ : ℕ) (n : ℤ) :
  DecidableEq (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndex m₁ m₂ m₃ n)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndexDecidableEq' does not depend on any axioms
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.mixedCoordinates

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.mixedCoordinates (R : Type) [CommRing R] (a b : ℕ) :
  (R × (Fin a → R) × (Fin b → R)) ≃ₗ[R] Unit ⊕ Fin a ⊕ Fin b → R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.mixedCoordinates' depends on axioms: [propext, Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockCoordinates

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockCoordinates {R : Type} [CommRing R] {m₁ m₂ m₃ : ℕ}
  (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) (n : ℤ) :
  ↑((ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃).X n) ≃ₗ[R]
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndex m₁ m₂ m₃ n → R
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.extendedBlockCoordinates

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.extendedBlockCoordinates {R S : Type} [CommRing R] [CommRing S]
  {m₁ m₂ m₃ : ℕ} (φ : R →+* S) (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R)
  (B₃ : Matrix (Fin m₃) (Fin m₃) R) (n : ℤ) :
  ↑((ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex φ
            (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃)).X
        n) ≃ₗ[S]
    ↑((ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex (B₁.map ⇑φ) (B₂.map ⇑φ) (B₃.map ⇑φ)).X n)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.extendedBlockCoordinates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockScalarChangeIso

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockScalarChangeIso {R S : Type} [CommRing R] [CommRing S] {m₁ m₂ m₃ : ℕ}
  (φ : R →+* S) (B₁ : Matrix (Fin m₁) (Fin m₁) R) (B₂ : Matrix (Fin m₂) (Fin m₂) R) (B₃ : Matrix (Fin m₃) (Fin m₃) R) :
  ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex φ
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex B₁ B₂ B₃) ≅
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex (B₁.map ⇑φ) (B₂.map ⇑φ) (B₃.map ⇑φ)
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockScalarChangeIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ} (G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ)
  (B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]) (B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]) (B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]) :
  Type 1
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.basisComparison

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.basisComparison {K : Type} [Field K]
  [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ}
  {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ} {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]}
  {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) (n : ℤ) :
  (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndex m₁ m₂ m₃ n → ℤ_[2]) ≃ₗ[ℤ_[2]]
    ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndex m₁ m₂ m₃ n → ℤ_[2]
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.basisComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.basisMatrix

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.basisMatrix {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]} {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) (n : ℤ) :
  Matrix (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndex m₁ m₂ m₃ n)
    (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockIndex m₁ m₂ m₃ n) ℤ_[2]
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.basisMatrix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.inverseDeterminantBasisFactor

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.inverseDeterminantBasisFactor {K : Type} [Field K]
  [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ}
  {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ} {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]}
  {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) : ℤ_[2]ˣ
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.inverseDeterminantBasisFactor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.fibreMap

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.fibreMap {K : Type} [Field K] [NumberField K]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ} {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ}
  {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]} {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) :
  ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex (ZInQ.Contrib.RC53Assist.Calibration.constRed i) M.P ⟶
    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx
        (ZInQ.Contrib.RC53Assist.Calibration.centralKummerSelData G.W G.s ⋯ ⋯ ⋯ i)).toCC
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.fibreMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finiteComparison

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finiteComparison {K : Type} [Field K]
  [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ}
  {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ} {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]}
  {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) :
  ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex (B₁.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i))
      (B₂.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i))
      (B₃.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i)) ⟶
    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx
        (ZInQ.Contrib.RC53Assist.Calibration.centralKummerSelData G.W G.s ⋯ ⋯ ⋯ i)).toCC
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finiteComparison' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finiteHomologyIso

```lean
ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finiteHomologyIso {K : Type} [Field K]
  [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {m₁ m₂ m₃ : ℕ}
  {G : ZInQ.Contrib.RC53Assist.Calibration.GenuineKummerData K E₀ hZ} {B₁ : Matrix (Fin m₁) (Fin m₁) ℤ_[2]}
  {B₂ : Matrix (Fin m₂) (Fin m₂) ℤ_[2]} {B₃ : Matrix (Fin m₃) (Fin m₃) ℤ_[2]}
  (M : ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel G B₁ B₂ B₃) (i : ℕ) (hi : i ≠ 0) (n : ℤ) :
  HomologicalComplex.homology
      (ZInQ.Contrib.RC53Assist.CalibrationIntegral.blockComplex
        (B₁.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i))
        (B₂.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i))
        (B₃.map ⇑(ZInQ.Contrib.RC53Assist.Calibration.constRed i)))
      n ≅
    G.selH i n
```

```text
'ZInQ.Contrib.RC53Assist.CalibrationIntegral.IntegralBlockCentralModel.finiteHomologyIso' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

