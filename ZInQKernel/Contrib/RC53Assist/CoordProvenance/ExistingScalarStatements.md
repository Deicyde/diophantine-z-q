# Statements and individual axiom reports
There are 50 new theorems. The self-contained source files also reproduce support results in separate namespaces. All 201 explicit declarations, including all 132 theorem declarations, have individual axiom reports below.
The readable type rendering is followed by its exact fully explicit kernel-type location. Download and decompress each `.exact.txt.gz` file to the corresponding `.exact.txt` file before applying the stated byte/line ranges. Those exact types were printed with all type arguments, binder types, universes and proofs visible and contain no printer ellipses. Byte ranges are zero-based, half-open. The source files give the written mathematical statements and proofs.
## New theorem index

### ExistingScalar.lean
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_endpoint_on_carrier`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_common_fraction`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_unique`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_from_corrected_representative`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent_injective`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.isCoordOn_map`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint_laurent`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_no_unused`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.isCoordOn_relabel`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint_finite`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_laurent_scalar_common_fraction`

### EndpointComparison.lean
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.endpoint_row_of_values`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.existing_endpoint_original_basis`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.existing_endpoint_two_realizations`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.original_coordinate_eq_existing_relaxed`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.relIsKMG_of_existing_realizations`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.origCoordLink_of_existing_realizations`

### FullModelAdapter.lean
- `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy_unit`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy_cancel`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy_class`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy_functional`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacyFunctional_closed`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacy_cycle_closed`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.full_coordinate_eq_inverseDiskLegacy`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.same_disk_factor_obstruction`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverse_matrix_lift_forces_integral_unit`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.no_integral_inverse_disk_lift`

### CoefficientRealization.lean
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent_injective`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToClearing_injective`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent_injective`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing_injective`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent_ofIntegral`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing_ofIntegral`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.sign_toLaurent`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.sign_toClearing`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.matrix_toClearing`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.matrix_toLaurent`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.vector_toClearing`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.vector_toLaurent`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.inverse_toLaurent`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.inverse_toClearing`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.schur_toClearing`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.schur_toLaurent`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toClearing`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toLaurent_fraction`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toLaurent_rep`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre_toClearing`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre_toLaurent`
- `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.local_block_regular_common`

## Complete declaration audit

# ExistingScalar.lean

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint`

new theorem; source line 32.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint : ∀ {ℓ : ℕ}
  {Dd : ZInQ.Manuscript.RC.RCData ℓ} {F : ZInQ.Manuscript.RC.Family} {x : ZInQ.Manuscript.RC.Addr F.b}
  (T : ZInQ.Contrib.CloudB3RC53.CommonCoordinate.CommonCoordinateTrianglesN Dd F x),
  Finset.Nonempty.{0} T.U → ∃ n D z w, ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w T.urel
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [0, 5757), lines 1–86.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_endpoint_on_carrier`

new theorem; source line 47.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_endpoint_on_carrier : ∀ {A : Type} [inst : CommRing.{0} A]
  (U : Finset.{0} ℕ),
  Finset.Nonempty.{0} U →
    ∀ (F : ℕ → Matrix.{0, 0, 0} (Fin 2) (Fin 2) A) (q qi a z zi eps : ℕ → A) (u : Finset.{0} ℕ → A)
      (unitR unitP : A → Prop),
      (∀ T ⊆ U,
          ∀ (p : ℕ),
            Membership.mem.{0, 0} U p →
              p ∉ T →
                ZInQ.Contrib.CloudB3RC53.CommonCoordinate.ActualStep (F p) (q p) (qi p) (a p) (z p) (zi p) (u T)
                  (u (Insert.insert.{0, 0} p T)) (eps p) unitR unitP) →
        ∃ n D zc wc, ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D zc wc (u U)
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [5903, 11408), lines 88–184.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_endpoint_on_carrier' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_common_fraction`

new theorem; source line 69.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_common_fraction : ∀ {R A K : Type}
  [inst : CommRing.{0} R] [inst_1 : CommRing.{0} A] [inst_2 : Field.{0} K] {ι : Type} [inst_3 : Fintype.{0} ι]
  [inst_4 : DecidableEq.{1} ι] (f : RingHom.{0, 0} R A),
  Function.Injective.{1, 1} ⇑f →
    ∀ (g : RingHom.{0, 0} R K),
      Function.Injective.{1, 1} ⇑g →
        ∀ (D : Matrix.{0, 0, 0} ι ι R) (z w : ι → R) (u : A),
          ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑f)
              (Function.comp.{1, 1, 1} (⇑f) z) (Function.comp.{1, 1, 1} (⇑f) w) u →
            Ne.{1} (Matrix.adjugate.{0, 0} D) 0 →
              ∃ num den,
                Ne.{1} den 0 ∧
                  Eq.{1} (HMul.hMul.{0, 0, 0} (f den) u) (f num) ∧
                    ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑g)
                      (Function.comp.{1, 1, 1} (⇑g) z) (Function.comp.{1, 1, 1} (⇑g) w)
                      (HDiv.hDiv.{0, 0, 0} (g num) (g den))
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [11554, 23575), lines 186–401.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_common_fraction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_unique`

new theorem; source line 121.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_unique : ∀ {K : Type} [inst : Field.{0} K] {ι : Type}
  [inst_1 : Fintype.{0} ι] [inst_2 : DecidableEq.{1} ι] (D : Matrix.{0, 0, 0} ι ι K) (z w : ι → K) (u v : K),
  Ne.{1} (Matrix.adjugate.{0, 0} D) 0 →
    ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w u →
      ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w v → Eq.{1} u v
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [23724, 24750), lines 403–421.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_unique' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_from_corrected_representative`

new theorem; source line 134.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_from_corrected_representative : ∀ {R A K : Type}
  [inst : CommRing.{0} R] [inst_1 : CommRing.{0} A] [inst_2 : Field.{0} K] (f : RingHom.{0, 0} R A),
  Function.Injective.{1, 1} ⇑f →
    ∀ (g : RingHom.{0, 0} R K),
      Function.Injective.{1, 1} ⇑g →
        ∀ (uA : A) (uK correctedK : K) (eta num den correctedNum correctedDen : R),
          Ne.{1} den 0 →
            Ne.{1} correctedDen 0 →
              Eq.{1} (HMul.hMul.{0, 0, 0} (f den) uA) (f num) →
                Eq.{1} (HMul.hMul.{0, 0, 0} (f correctedDen) (HMul.hMul.{0, 0, 0} (f eta) uA)) (f correctedNum) →
                  Eq.{1} (HMul.hMul.{0, 0, 0} (g correctedDen) correctedK) (g correctedNum) →
                    Eq.{1} correctedK (HMul.hMul.{0, 0, 0} (g eta) uK) →
                      Ne.{1} (g eta) 0 → Eq.{1} uK (HDiv.hDiv.{0, 0, 0} (g num) (g den))
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [24890, 37089), lines 423–638.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_from_corrected_representative' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent`

abbrev; source line 162.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent : RingHom.{0, 0} (PowerSeries.{0} ℚ_[2])
  (LaurentSeries.{0} ℚ_[2])
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [37252, 39448), lines 640–670.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent_injective`

new theorem; source line 166.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent_injective : Function.Injective.{1, 1}
  ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [39575, 45082), lines 672–743.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent_injective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.isCoordOn_map`

new theorem; source line 170.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.isCoordOn_map : ∀ {R S : Type} [inst : CommRing.{0} R]
  [inst_1 : CommRing.{0} S] {ι : Type} [inst_2 : Fintype.{0} ι] [inst_3 : DecidableEq.{1} ι] (f : RingHom.{0, 0} R S)
  (D : Matrix.{0, 0, 0} ι ι R) (z w : ι → R) (u : R),
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w u →
    ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑f)
      (Function.comp.{1, 1, 1} (⇑f) z) (Function.comp.{1, 1, 1} (⇑f) w) (f u)
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [45219, 48525), lines 745–796.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.isCoordOn_map' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint_laurent`

new theorem; source line 187.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint_laurent : ∀ {ℓ : ℕ}
  {Dd : ZInQ.Manuscript.RC.RCData ℓ} {F : ZInQ.Manuscript.RC.Family} {x : ZInQ.Manuscript.RC.Addr F.b}
  (T : ZInQ.Contrib.CloudB3RC53.CommonCoordinate.CommonCoordinateTrianglesN Dd F x),
  Finset.Nonempty.{0} T.U →
    ∃ n D z w,
      ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0}
        (Matrix.map.{0, 0, 0, 0} D ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent)
        (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent) z)
        (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent) w)
        (ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.toLaurent T.urel)
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [48656, 81544), lines 798–1238.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint_laurent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_no_unused`

new theorem; source line 198.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_no_unused : ∀ {ℓ : ℕ} {Dd : ZInQ.Manuscript.RC.RCData ℓ}
  {F : ZInQ.Manuscript.RC.Family} {x : ZInQ.Manuscript.RC.Addr F.b}
  (T : ZInQ.Contrib.CloudB3RC53.CommonCoordinate.CommonCoordinateTrianglesN Dd F x),
  Eq.{1} T.U EmptyCollection.emptyCollection.{0} → Eq.{1} T.urel (Dd.uPrim F x)
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [81698, 82503), lines 1240–1251.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_scalar_no_unused' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.isCoordOn_relabel`

new theorem; source line 203.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.isCoordOn_relabel : ∀ {R : Type} [inst : CommRing.{0} R] {ι κ : Type}
  [inst_1 : Fintype.{0} ι] [inst_2 : DecidableEq.{1} ι] [inst_3 : Fintype.{0} κ] [inst_4 : DecidableEq.{1} κ]
  (e : Equiv.{1, 1} κ ι) (D : Matrix.{0, 0, 0} ι ι R) (z w : ι → R) (u : R),
  ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w u →
    ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.submatrix.{0, 0, 0, 0, 0} D ⇑e ⇑e)
      (Function.comp.{1, 1, 1} z ⇑e) (Function.comp.{1, 1, 1} w ⇑e) u
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [82646, 84029), lines 1253–1271.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.isCoordOn_relabel' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint_finite`

new theorem; source line 214.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint_finite : ∀ {ℓ : ℕ}
  {Dd : ZInQ.Manuscript.RC.RCData ℓ} {F : ZInQ.Manuscript.RC.Family} {x : ZInQ.Manuscript.RC.Addr F.b}
  (T : ZInQ.Contrib.CloudB3RC53.CommonCoordinate.CommonCoordinateTrianglesN Dd F x),
  Finset.Nonempty.{0} T.U → ∃ m D z w, ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w T.urel
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [84164, 88152), lines 1273–1339.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_relaxation_endpoint_finite' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_laurent_scalar_common_fraction`

new theorem; source line 226.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_laurent_scalar_common_fraction : ∀ {R : Type}
  [inst : CommRing.{0} R] {m : ℕ} (f : RingHom.{0, 0} R (LaurentSeries.{0} ℚ_[2])),
  Function.Injective.{1, 1} ⇑f →
    ∀ (g : RingHom.{0, 0} R (FractionRing.{0} ZInQ.Manuscript.RC.Determinant.OO)),
      Function.Injective.{1, 1} ⇑g →
        ∀ (D : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) R)
          (z w : Fin (HAdd.hAdd.{0, 0, 0} m 1) → R) (urel : LaurentSeries.{0} ℚ_[2]),
          ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑f)
              (Function.comp.{1, 1, 1} (⇑f) z) (Function.comp.{1, 1, 1} (⇑f) w) urel →
            Ne.{1} (Matrix.adjugate.{0, 0} D) 0 →
              ∃ num den,
                Ne.{1} den 0 ∧
                  Eq.{1} (HMul.hMul.{0, 0, 0} (f den) urel) (f num) ∧
                    ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑g)
                      (Function.comp.{1, 1, 1} (⇑g) z) (Function.comp.{1, 1, 1} (⇑g) w)
                      (HDiv.hDiv.{0, 0, 0} (g num) (g den))
```

Exact kernel type: decompress `ExistingScalar.exact.txt.gz` to `ExistingScalar.exact.txt`; bytes [88305, 1451798), lines 1341–19517.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar.existing_laurent_scalar_common_fraction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

# EndpointComparison.lean

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison`

structure; source line 47.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8,
    u_9} : {K : Type u_1} →
  [inst : Field.{u_1} K] →
    {ι0 : Type u_2} →
      {ι1 : Type u_3} →
        {ι2 : Type u_4} →
          {ι3 : Type u_5} →
            {ι0' : Type u_6} →
              {ι1' : Type u_7} →
                {ι2' : Type u_8} →
                  {ι3' : Type u_9} →
                    [inst_1 : Fintype.{u_3} ι1] →
                      [inst_2 : Fintype.{u_4} ι2] →
                        [Fintype.{u_5} ι3] →
                          [Fintype.{u_6} ι0'] →
                            [inst_5 : Fintype.{u_7} ι1'] →
                              [inst_6 : Fintype.{u_8} ι2'] →
                                ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3 →
                                  ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3' →
                                    (ι1 → K) →
                                      (ι2 → K) →
                                        (ι1' → K) →
                                          (ι2' → K) →
                                            Type
                                              (max
                                                  (max (max (max (max (max (max (max u_1 u_2) u_3) u_4) u_5) u_6) u_7)
                                                      u_8)
                                                  u_9)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [0, 1850), lines 1–33.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.class_discrepancy`

support theorem; source line 60.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.class_discrepancy.{u_1, u_2, u_3, u_4, u_5,
    u_6, u_7, u_8,
    u_9} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  {ι0' : Type u_6} {ι1' : Type u_7} {ι2' : Type u_8} {ι3' : Type u_9} [inst_1 : Fintype.{u_3} ι1]
  [inst_2 : Fintype.{u_4} ι2] [inst_3 : Fintype.{u_5} ι3] [inst_4 : Fintype.{u_6} ι0'] [inst_5 : Fintype.{u_7} ι1']
  [inst_6 : Fintype.{u_8} ι2'] {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8,
        u_9}
      C D zC lC zD lD),
  Eq.{max (u_1 + 1) (u_7 + 1)}
    (HSub.hSub.{max u_1 u_7, max u_1 u_7, max u_1 u_7}
      (Matrix.mulVec.{u_1, u_7, u_3}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f1.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{u_1, u_2, u_3, u_4, u_5, u_6,
              u_7, u_8, u_9}
            H))
        zC)
      zD)
    (Matrix.mulVec.{u_1, u_7, u_6} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{u_1, u_6, u_7, u_8, u_9} D)
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.classBoundary.{u_1, u_2, u_3, u_4,
          u_5, u_6, u_7, u_8, u_9}
        H))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [1995, 5298), lines 35–86.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.class_discrepancy' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.functional_on_cycles`

support theorem; source line 69.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.functional_on_cycles.{u_1, u_2, u_3, u_4,
    u_5, u_6, u_7, u_8,
    u_9} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  {ι0' : Type u_6} {ι1' : Type u_7} {ι2' : Type u_8} {ι3' : Type u_9} [inst_1 : Fintype.{u_3} ι1]
  [inst_2 : Fintype.{u_4} ι2] [inst_3 : Fintype.{u_5} ι3] [inst_4 : Fintype.{u_6} ι0'] [inst_5 : Fintype.{u_7} ι1']
  [inst_6 : Fintype.{u_8} ι2'] {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8,
        u_9}
      C D zC lC zD lD)
  (w : ι2 → K),
  Eq.{max (u_1 + 1) (u_5 + 1)}
      (Matrix.mulVec.{u_1, u_5, u_4} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{u_1, u_2, u_3, u_4, u_5} C) w) 0 →
    Eq.{u_1 + 1}
      (dotProduct.{u_1, u_8} lD
        (Matrix.mulVec.{u_1, u_8, u_4}
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f2.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{u_1, u_2, u_3, u_4, u_5, u_6,
                u_7, u_8, u_9}
              H))
          w))
      (dotProduct.{u_1, u_4} lC w)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [5461, 9273), lines 88–152.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.functional_on_cycles' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f0aug`

def; source line 75.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f0aug.{u_1, u_2, u_3, u_4, u_5, u_6, u_7,
    u_8,
    u_9} : {K : Type u_1} →
  [inst : Field.{u_1} K] →
    {ι0 : Type u_2} →
      {ι1 : Type u_3} →
        {ι2 : Type u_4} →
          {ι3 : Type u_5} →
            {ι0' : Type u_6} →
              {ι1' : Type u_7} →
                {ι2' : Type u_8} →
                  {ι3' : Type u_9} →
                    [inst_1 : Fintype.{u_3} ι1] →
                      [inst_2 : Fintype.{u_4} ι2] →
                        [inst_3 : Fintype.{u_5} ι3] →
                          [inst_4 : Fintype.{u_6} ι0'] →
                            [inst_5 : Fintype.{u_7} ι1'] →
                              [inst_6 : Fintype.{u_8} ι2'] →
                                {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3} →
                                  {D :
                                      ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2'
                                        ι3'} →
                                    {zC : ι1 → K} →
                                      {lC : ι2 → K} →
                                        {zD : ι1' → K} →
                                          {lD : ι2' → K} →
                                            ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1,
                                                  u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
                                                C D zC lC zD lD →
                                              Matrix.{u_6, u_2, u_1} (Sum.{u_6, 0} ι0' Unit) (Sum.{u_2, 0} ι0 Unit) K
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [9439, 11584), lines 154–189.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f0aug' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f3aug`

def; source line 80.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f3aug.{u_1, u_2, u_3, u_4, u_5, u_6, u_7,
    u_8,
    u_9} : {K : Type u_1} →
  [inst : Field.{u_1} K] →
    {ι0 : Type u_2} →
      {ι1 : Type u_3} →
        {ι2 : Type u_4} →
          {ι3 : Type u_5} →
            {ι0' : Type u_6} →
              {ι1' : Type u_7} →
                {ι2' : Type u_8} →
                  {ι3' : Type u_9} →
                    [inst_1 : Fintype.{u_3} ι1] →
                      [inst_2 : Fintype.{u_4} ι2] →
                        [inst_3 : Fintype.{u_5} ι3] →
                          [inst_4 : Fintype.{u_6} ι0'] →
                            [inst_5 : Fintype.{u_7} ι1'] →
                              [inst_6 : Fintype.{u_8} ι2'] →
                                {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3} →
                                  {D :
                                      ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2'
                                        ι3'} →
                                    {zC : ι1 → K} →
                                      {lC : ι2 → K} →
                                        {zD : ι1' → K} →
                                          {lD : ι2' → K} →
                                            ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1,
                                                  u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
                                                C D zC lC zD lD →
                                              Matrix.{u_9, u_5, u_1} (Sum.{u_9, 0} ι3' Unit) (Sum.{u_5, 0} ι3 Unit) K
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [11735, 13880), lines 191–226.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f3aug' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f3aug_value`

support theorem; source line 87.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f3aug_value.{u_1, u_2, u_3, u_4, u_5, u_6,
    u_7, u_8,
    u_9} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  {ι0' : Type u_6} {ι1' : Type u_7} {ι2' : Type u_8} {ι3' : Type u_9} [inst_1 : Fintype.{u_3} ι1]
  [inst_2 : Fintype.{u_4} ι2] [inst_3 : Fintype.{u_5} ι3] [inst_4 : Fintype.{u_6} ι0'] [inst_5 : Fintype.{u_7} ι1']
  [inst_6 : Fintype.{u_8} ι2'] {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8,
        u_9}
      C D zC lC zD lD)
  (r : ι3 → K) (a : K),
  Eq.{max (u_1 + 1) (u_9 + 1)}
    (Matrix.mulVec.{u_1, u_9, u_5}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f3aug.{u_1, u_2, u_3, u_4, u_5, u_6,
          u_7, u_8, u_9}
        H)
      (Sum.elim.{u_5, 0, u_1 + 1} r fun x => a))
    (Sum.elim.{u_9, 0, u_1 + 1}
      (Matrix.mulVec.{u_1, u_9, u_5}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f3.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{u_1, u_2, u_3, u_4, u_5, u_6,
              u_7, u_8, u_9}
            H))
        r)
      fun x =>
      HAdd.hAdd.{u_1, u_1, u_1} a
        (dotProduct.{u_1, u_5}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.functionalBoundary.{u_1, u_2, u_3,
              u_4, u_5, u_6, u_7, u_8, u_9}
            H)
          r))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [14031, 17933), lines 228–289.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f3aug_value' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.comm0_aug`

support theorem; source line 102.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.comm0_aug.{u_1, u_2, u_3, u_4, u_5, u_6,
    u_7, u_8,
    u_9} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  {ι0' : Type u_6} {ι1' : Type u_7} {ι2' : Type u_8} {ι3' : Type u_9} [inst_1 : Fintype.{u_3} ι1]
  [inst_2 : Fintype.{u_4} ι2] [inst_3 : Fintype.{u_5} ι3] [inst_4 : Fintype.{u_6} ι0'] [inst_5 : Fintype.{u_7} ι1']
  [inst_6 : Fintype.{u_8} ι2'] {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8,
        u_9}
      C D zC lC zD lD),
  Eq.{max (max (u_1 + 1) (u_2 + 1)) (u_7 + 1)}
    (HMul.hMul.{max (max u_1 u_6) u_7, max (max u_1 u_2) u_6, max (max u_1 u_2) u_7}
      (Matrix.fromCols.{u_1, u_7, u_6, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{u_1, u_6, u_7, u_8, u_9} D)
        (Matrix.replicateCol.{u_1, u_7, 0} Unit zD))
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f0aug.{u_1, u_2, u_3, u_4, u_5, u_6,
          u_7, u_8, u_9}
        H))
    (HMul.hMul.{max (max u_1 u_3) u_7, max (max u_1 u_2) u_3, max (max u_1 u_2) u_7}
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f1.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{u_1, u_2, u_3, u_4, u_5, u_6,
            u_7, u_8, u_9}
          H))
      (Matrix.fromCols.{u_1, u_3, u_2, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{u_1, u_2, u_3, u_4, u_5} C)
        (Matrix.replicateCol.{u_1, u_3, 0} Unit zC)))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [18090, 22159), lines 291–345.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.comm0_aug' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.comm2_aug`

support theorem; source line 118.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.comm2_aug.{u_1, u_2, u_3, u_4, u_5, u_6,
    u_7, u_8,
    u_9} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  {ι0' : Type u_6} {ι1' : Type u_7} {ι2' : Type u_8} {ι3' : Type u_9} [inst_1 : Fintype.{u_3} ι1]
  [inst_2 : Fintype.{u_4} ι2] [inst_3 : Fintype.{u_5} ι3] [inst_4 : Fintype.{u_6} ι0'] [inst_5 : Fintype.{u_7} ι1']
  [inst_6 : Fintype.{u_8} ι2'] {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8,
        u_9}
      C D zC lC zD lD),
  Eq.{max (max (u_1 + 1) (u_4 + 1)) (u_9 + 1)}
    (HMul.hMul.{max (max u_1 u_8) u_9, max (max u_1 u_4) u_8, max (max u_1 u_4) u_9}
      (Matrix.fromRows.{u_1, u_9, 0, u_8} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{u_1, u_6, u_7, u_8, u_9} D)
        (Matrix.replicateRow.{u_1, u_8, 0} Unit lD))
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f2.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{u_1, u_2, u_3, u_4, u_5, u_6,
            u_7, u_8, u_9}
          H)))
    (HMul.hMul.{max (max u_1 u_5) u_9, max (max u_1 u_4) u_5, max (max u_1 u_4) u_9}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f3aug.{u_1, u_2, u_3, u_4, u_5, u_6,
          u_7, u_8, u_9}
        H)
      (Matrix.fromRows.{u_1, u_5, 0, u_4} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{u_1, u_2, u_3, u_4, u_5} C)
        (Matrix.replicateRow.{u_1, u_4, 0} Unit lC)))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [22314, 26382), lines 347–401.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.comm2_aug' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap`

def; source line 134.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{u_1, u_2, u_3, u_4, u_5, u_6, u_7,
    u_8,
    u_9} : {K : Type u_1} →
  [inst : Field.{u_1} K] →
    {ι0 : Type u_2} →
      {ι1 : Type u_3} →
        {ι2 : Type u_4} →
          {ι3 : Type u_5} →
            {ι0' : Type u_6} →
              {ι1' : Type u_7} →
                {ι2' : Type u_8} →
                  {ι3' : Type u_9} →
                    [inst_1 : Fintype.{u_2} ι0] →
                      [inst_2 : Fintype.{u_3} ι1] →
                        [inst_3 : Fintype.{u_4} ι2] →
                          [inst_4 : Fintype.{u_5} ι3] →
                            [inst_5 : Fintype.{u_6} ι0'] →
                              [inst_6 : Fintype.{u_7} ι1'] →
                                [inst_7 : Fintype.{u_8} ι2'] →
                                  [inst_8 : Fintype.{u_9} ι3'] →
                                    {C :
                                        ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2
                                          ι3} →
                                      {D :
                                          ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1'
                                            ι2' ι3'} →
                                        {zC : ι1 → K} →
                                          {lC : ι2 → K} →
                                            {zD : ι1' → K} →
                                              {lD : ι2' → K} →
                                                ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1,
                                                      u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
                                                    C D zC lC zD lD →
                                                  (hzC :
                                                      Eq.{max (u_1 + 1) (u_4 + 1)}
                                                        (Matrix.mulVec.{u_1, u_4, u_3}
                                                          (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3,
                                                              u_4, u_5}
                                                            C)
                                                          zC)
                                                        0) →
                                                    (hlC :
                                                        Eq.{max (u_1 + 1) (u_3 + 1)}
                                                          (Matrix.vecMul.{u_1, u_4, u_3} lC
                                                            (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3,
                                                                u_4, u_5}
                                                              C))
                                                          0) →
                                                      (hzD :
                                                          Eq.{max (u_1 + 1) (u_8 + 1)}
                                                            (Matrix.mulVec.{u_1, u_8, u_7}
                                                              (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6,
                                                                  u_7, u_8, u_9}
                                                                D)
                                                              zD)
                                                            0) →
                                                        (hlD :
                                                            Eq.{max (u_1 + 1) (u_7 + 1)}
                                                              (Matrix.vecMul.{u_1, u_8, u_7} lD
                                                                (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6,
                                                                    u_7, u_8, u_9}
                                                                  D))
                                                              0) →
                                                          ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{u_1, max u_2 u_4,
                                                              max u_3 u_5, max u_6 u_8, max u_7 u_9}
                                                            (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{u_1, u_2,
                                                                u_3, u_4, u_5}
                                                              (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{u_1, u_2,
                                                                  u_3, u_4, u_5}
                                                                C zC lC hzC hlC))
                                                            (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{u_1, u_6,
                                                                u_7, u_8, u_9}
                                                              (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{u_1, u_6,
                                                                  u_7, u_8, u_9}
                                                                D zD lD hzD hlD))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [26537, 42971), lines 403–583.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.kmCoord_eq_of_augmented_comparison`

support theorem; source line 164.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.kmCoord_eq_of_augmented_comparison.{u_1, u_2, u_3, u_4, u_5,
    u_6, u_7, u_8,
    u_9} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  {ι0' : Type u_6} {ι1' : Type u_7} {ι2' : Type u_8} {ι3' : Type u_9} [inst_1 : Fintype.{u_2} ι0]
  [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3] [inst_5 : Fintype.{u_6} ι0']
  [inst_6 : Fintype.{u_7} ι1'] [inst_7 : Fintype.{u_8} ι2'] [inst_8 : Fintype.{u_9} ι3']
  [inst_9 : DecidableEq.{u_2 + 1} ι0] [inst_10 : DecidableEq.{u_3 + 1} ι1] [inst_11 : DecidableEq.{u_4 + 1} ι2]
  [inst_12 : DecidableEq.{u_5 + 1} ι3] [inst_13 : DecidableEq.{u_6 + 1} ι0'] [inst_14 : DecidableEq.{u_7 + 1} ι1']
  [inst_15 : DecidableEq.{u_8 + 1} ι2'] [inst_16 : DecidableEq.{u_9 + 1} ι3']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (hzC :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) zC) 0)
  (hlC :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (hzD :
    Eq.{max (u_1 + 1) (u_8 + 1)}
      (Matrix.mulVec.{u_1, u_8, u_7} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D) zD) 0)
  (hlD :
    Eq.{max (u_1 + 1) (u_7 + 1)}
      (Matrix.vecMul.{u_1, u_8, u_7} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D)) 0)
  (f :
    ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapB.{u_1, max u_2 u_4, max u_3 u_5, max u_6 u_8, max u_7 u_9}
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{u_1, u_2, u_3, u_4, u_5}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{u_1, u_2, u_3, u_4, u_5} C zC lC hzC hlC))
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{u_1, u_6, u_7, u_8, u_9}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{u_1, u_6, u_7, u_8, u_9} D zD lD hzD hlD)))
  (σC :
    Equiv.{max (u_4 + 1) (u_2 + 1), max (u_5 + 1) (u_3 + 1)} (Sum.{u_2, u_4} (Sum.{u_2, 0} ι0 Unit) ι2)
      (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit)))
  (σD :
    Equiv.{max (u_8 + 1) (u_6 + 1), max (u_9 + 1) (u_7 + 1)} (Sum.{u_6, u_8} (Sum.{u_6, 0} ι0' Unit) ι2')
      (Sum.{u_7, u_9} ι1' (Sum.{u_9, 0} ι3' Unit))),
  Ne.{u_1 + 1}
      (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_1, max (max u_6 u_8) u_3 u_5, max (max u_7 u_9) u_2 u_4}
        (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{u_1, max u_2 u_4, max u_3 u_5, max u_6 u_8, max u_7 u_9} f)
        (Equiv.sumCongr.{max u_7 u_9, max u_3 u_5, max u_2 u_4, max u_6 u_8} σD
          (Equiv.symm.{max (u_2 + 1) (u_4 + 1), max (u_3 + 1) (u_5 + 1)} σC)))
      0 →
    Eq.{u_1 + 1} (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_2, u_3, u_4, u_5} C zC lC hzC hlC σC)
      (HMul.hMul.{u_1, u_1, u_1}
        (HMul.hMul.{u_1, u_1, u_1}
          (HPow.hPow.{u_1, 0, u_1} (-1) (Fintype.card.{max u_5 u_3} (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit))))
          (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_6, u_7, u_8, u_9} D zD lD hzD hlD σD))
        (Inv.inv.{u_1}
          (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_1, max (max u_6 u_8) u_3 u_5, max (max u_7 u_9) u_2 u_4}
            (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{u_1, max u_2 u_4, max u_3 u_5, max u_6 u_8, max u_7 u_9} f)
            (Equiv.sumCongr.{max u_7 u_9, max u_3 u_5, max u_2 u_4, max u_6 u_8} σD
              (Equiv.symm.{max (u_2 + 1) (u_4 + 1), max (u_3 + 1) (u_5 + 1)} σC)))))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [43123, 65597), lines 585–918.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.kmCoord_eq_of_augmented_comparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_formula`

support theorem; source line 189.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_formula.{u_1, u_2, u_3, u_4, u_5,
    u_6, u_7, u_8,
    u_9} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  {ι0' : Type u_6} {ι1' : Type u_7} {ι2' : Type u_8} {ι3' : Type u_9} [inst_1 : Fintype.{u_2} ι0]
  [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3] [inst_5 : Fintype.{u_6} ι0']
  [inst_6 : Fintype.{u_7} ι1'] [inst_7 : Fintype.{u_8} ι2'] [inst_8 : Fintype.{u_9} ι3']
  [inst_9 : DecidableEq.{u_2 + 1} ι0] [inst_10 : DecidableEq.{u_3 + 1} ι1] [inst_11 : DecidableEq.{u_4 + 1} ι2]
  [inst_12 : DecidableEq.{u_5 + 1} ι3] [inst_13 : DecidableEq.{u_6 + 1} ι0'] [inst_14 : DecidableEq.{u_7 + 1} ι1']
  [inst_15 : DecidableEq.{u_8 + 1} ι2'] [inst_16 : DecidableEq.{u_9 + 1} ι3']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8,
        u_9}
      C D zC lC zD lD)
  (hzC :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) zC) 0)
  (hlC :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (hzD :
    Eq.{max (u_1 + 1) (u_8 + 1)}
      (Matrix.mulVec.{u_1, u_8, u_7} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D) zD) 0)
  (hlD :
    Eq.{max (u_1 + 1) (u_7 + 1)}
      (Matrix.vecMul.{u_1, u_8, u_7} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D)) 0)
  (σC :
    Equiv.{max (u_4 + 1) (u_2 + 1), max (u_5 + 1) (u_3 + 1)} (Sum.{u_2, u_4} (Sum.{u_2, 0} ι0 Unit) ι2)
      (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit)))
  (σD :
    Equiv.{max (u_8 + 1) (u_6 + 1), max (u_9 + 1) (u_7 + 1)} (Sum.{u_6, u_8} (Sum.{u_6, 0} ι0' Unit) ι2')
      (Sum.{u_7, u_9} ι1' (Sum.{u_9, 0} ι3' Unit))),
  Ne.{u_1 + 1}
      (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_1, max (max u_6 u_8) u_3 u_5, max (max u_7 u_9) u_2 u_4}
        (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{u_1, max u_2 u_4, max u_3 u_5, max u_6 u_8, max u_7 u_9}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{u_1, u_2, u_3, u_4, u_5,
              u_6, u_7, u_8, u_9}
            H hzC hlC hzD hlD))
        (Equiv.sumCongr.{max u_7 u_9, max u_3 u_5, max u_2 u_4, max u_6 u_8} σD
          (Equiv.symm.{max (u_2 + 1) (u_4 + 1), max (u_3 + 1) (u_5 + 1)} σC)))
      0 →
    Eq.{u_1 + 1} (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_2, u_3, u_4, u_5} C zC lC hzC hlC σC)
      (HMul.hMul.{u_1, u_1, u_1}
        (HMul.hMul.{u_1, u_1, u_1}
          (HPow.hPow.{u_1, 0, u_1} (-1) (Fintype.card.{max u_5 u_3} (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit))))
          (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_6, u_7, u_8, u_9} D zD lD hzD hlD σD))
        (Inv.inv.{u_1}
          (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_1, max (max u_6 u_8) u_3 u_5, max (max u_7 u_9) u_2 u_4}
            (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{u_1, max u_2 u_4, max u_3 u_5, max u_6 u_8, max u_7 u_9}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{u_1, u_2, u_3, u_4,
                  u_5, u_6, u_7, u_8, u_9}
                H hzC hlC hzD hlD))
            (Equiv.sumCongr.{max u_7 u_9, max u_3 u_5, max u_2 u_4, max u_6 u_8} σD
              (Equiv.symm.{max (u_2 + 1) (u_4 + 1), max (u_3 + 1) (u_5 + 1)} σC)))))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [65758, 87203), lines 920–1240.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_formula' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor`

def; source line 202.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor.{u_1, u_2, u_3, u_4, u_5,
    u_6, u_7, u_8,
    u_9} : {K : Type u_1} →
  [inst : Field.{u_1} K] →
    {ι0 : Type u_2} →
      {ι1 : Type u_3} →
        {ι2 : Type u_4} →
          {ι3 : Type u_5} →
            {ι0' : Type u_6} →
              {ι1' : Type u_7} →
                {ι2' : Type u_8} →
                  {ι3' : Type u_9} →
                    [Fintype.{u_2} ι0] →
                      [inst_2 : Fintype.{u_3} ι1] →
                        [inst_3 : Fintype.{u_4} ι2] →
                          [inst_4 : Fintype.{u_5} ι3] →
                            [inst_5 : Fintype.{u_6} ι0'] →
                              [inst_6 : Fintype.{u_7} ι1'] →
                                [inst_7 : Fintype.{u_8} ι2'] →
                                  [Fintype.{u_9} ι3'] →
                                    [DecidableEq.{u_2 + 1} ι0] →
                                      [DecidableEq.{u_3 + 1} ι1] →
                                        [DecidableEq.{u_4 + 1} ι2] →
                                          [DecidableEq.{u_5 + 1} ι3] →
                                            [DecidableEq.{u_6 + 1} ι0'] →
                                              [DecidableEq.{u_7 + 1} ι1'] →
                                                [DecidableEq.{u_8 + 1} ι2'] →
                                                  [DecidableEq.{u_9 + 1} ι3'] →
                                                    {C :
                                                        ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4,
                                                            u_5}
                                                          K ι0 ι1 ι2 ι3} →
                                                      {D :
                                                          ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8,
                                                              u_9}
                                                            K ι0' ι1' ι2' ι3'} →
                                                        {zC : ι1 → K} →
                                                          {lC : ι2 → K} →
                                                            {zD : ι1' → K} →
                                                              {lD : ι2' → K} →
                                                                ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1,
                                                                      u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
                                                                    C D zC lC zD lD →
                                                                  Eq.{max (u_1 + 1) (u_4 + 1)}
                                                                      (Matrix.mulVec.{u_1, u_4, u_3}
                                                                        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1,
                                                                            u_2, u_3, u_4, u_5}
                                                                          C)
                                                                        zC)
                                                                      0 →
                                                                    Eq.{max (u_1 + 1) (u_3 + 1)}
                                                                        (Matrix.vecMul.{u_1, u_4, u_3} lC
                                                                          (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1,
                                                                              u_2, u_3, u_4, u_5}
                                                                            C))
                                                                        0 →
                                                                      Eq.{max (u_1 + 1) (u_8 + 1)}
                                                                          (Matrix.mulVec.{u_1, u_8, u_7}
                                                                            (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1,
                                                                                u_6, u_7, u_8, u_9}
                                                                              D)
                                                                            zD)
                                                                          0 →
                                                                        Eq.{max (u_1 + 1) (u_7 + 1)}
                                                                            (Matrix.vecMul.{u_1, u_8, u_7} lD
                                                                              (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1,
                                                                                  u_6, u_7, u_8, u_9}
                                                                                D))
                                                                            0 →
                                                                          Equiv.{max (u_4 + 1) (u_2 + 1),
                                                                                max (u_5 + 1) (u_3 + 1)}
                                                                              (Sum.{u_2, u_4} (Sum.{u_2, 0} ι0 Unit) ι2)
                                                                              (Sum.{u_3, u_5} ι1
                                                                                (Sum.{u_5, 0} ι3 Unit)) →
                                                                            Equiv.{max (u_8 + 1) (u_6 + 1),
                                                                                  max (u_9 + 1) (u_7 + 1)}
                                                                                (Sum.{u_6, u_8} (Sum.{u_6, 0} ι0' Unit)
                                                                                  ι2')
                                                                                (Sum.{u_7, u_9} ι1'
                                                                                  (Sum.{u_9, 0} ι3' Unit)) →
                                                                              K
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [87367, 105090), lines 1242–1423.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor_ne_zero`

support theorem; source line 211.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor_ne_zero.{u_1, u_2, u_3, u_4,
    u_5, u_6, u_7, u_8,
    u_9} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  {ι0' : Type u_6} {ι1' : Type u_7} {ι2' : Type u_8} {ι3' : Type u_9} [inst_1 : Fintype.{u_2} ι0]
  [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3] [inst_5 : Fintype.{u_6} ι0']
  [inst_6 : Fintype.{u_7} ι1'] [inst_7 : Fintype.{u_8} ι2'] [inst_8 : Fintype.{u_9} ι3']
  [inst_9 : DecidableEq.{u_2 + 1} ι0] [inst_10 : DecidableEq.{u_3 + 1} ι1] [inst_11 : DecidableEq.{u_4 + 1} ι2]
  [inst_12 : DecidableEq.{u_5 + 1} ι3] [inst_13 : DecidableEq.{u_6 + 1} ι0'] [inst_14 : DecidableEq.{u_7 + 1} ι1']
  [inst_15 : DecidableEq.{u_8 + 1} ι2'] [inst_16 : DecidableEq.{u_9 + 1} ι3']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8,
        u_9}
      C D zC lC zD lD)
  (hzC :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) zC) 0)
  (hlC :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (hzD :
    Eq.{max (u_1 + 1) (u_8 + 1)}
      (Matrix.mulVec.{u_1, u_8, u_7} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D) zD) 0)
  (hlD :
    Eq.{max (u_1 + 1) (u_7 + 1)}
      (Matrix.vecMul.{u_1, u_8, u_7} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D)) 0)
  (σC :
    Equiv.{max (u_4 + 1) (u_2 + 1), max (u_5 + 1) (u_3 + 1)} (Sum.{u_2, u_4} (Sum.{u_2, 0} ι0 Unit) ι2)
      (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit)))
  (σD :
    Equiv.{max (u_8 + 1) (u_6 + 1), max (u_9 + 1) (u_7 + 1)} (Sum.{u_6, u_8} (Sum.{u_6, 0} ι0' Unit) ι2')
      (Sum.{u_7, u_9} ι1' (Sum.{u_9, 0} ι3' Unit))),
  Ne.{u_1 + 1}
      (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_1, max (max u_6 u_8) u_3 u_5, max (max u_7 u_9) u_2 u_4}
        (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{u_1, max u_2 u_4, max u_3 u_5, max u_6 u_8, max u_7 u_9}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{u_1, u_2, u_3, u_4, u_5,
              u_6, u_7, u_8, u_9}
            H hzC hlC hzD hlD))
        (Equiv.sumCongr.{max u_7 u_9, max u_3 u_5, max u_2 u_4, max u_6 u_8} σD
          (Equiv.symm.{max (u_2 + 1) (u_4 + 1), max (u_3 + 1) (u_5 + 1)} σC)))
      0 →
    Ne.{u_1 + 1}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor.{u_1, u_2, u_3, u_4,
          u_5, u_6, u_7, u_8, u_9}
        H hzC hlC hzD hlD σC σD)
      0
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [105250, 118270), lines 1425–1624.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_in_original_basis`

support theorem; source line 222.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_in_original_basis.{u_1, u_2, u_3,
    u_4, u_5, u_6, u_7, u_8,
    u_9} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  {ι0' : Type u_6} {ι1' : Type u_7} {ι2' : Type u_8} {ι3' : Type u_9} [inst_1 : Fintype.{u_2} ι0]
  [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3] [inst_5 : Fintype.{u_6} ι0']
  [inst_6 : Fintype.{u_7} ι1'] [inst_7 : Fintype.{u_8} ι2'] [inst_8 : Fintype.{u_9} ι3']
  [inst_9 : DecidableEq.{u_2 + 1} ι0] [inst_10 : DecidableEq.{u_3 + 1} ι1] [inst_11 : DecidableEq.{u_4 + 1} ι2]
  [inst_12 : DecidableEq.{u_5 + 1} ι3] [inst_13 : DecidableEq.{u_6 + 1} ι0'] [inst_14 : DecidableEq.{u_7 + 1} ι1']
  [inst_15 : DecidableEq.{u_8 + 1} ι2'] [inst_16 : DecidableEq.{u_9 + 1} ι3']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8,
        u_9}
      C D zC lC zD lD)
  (hzC :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) zC) 0)
  (hlC :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (hzD :
    Eq.{max (u_1 + 1) (u_8 + 1)}
      (Matrix.mulVec.{u_1, u_8, u_7} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D) zD) 0)
  (hlD :
    Eq.{max (u_1 + 1) (u_7 + 1)}
      (Matrix.vecMul.{u_1, u_8, u_7} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D)) 0)
  (σC :
    Equiv.{max (u_4 + 1) (u_2 + 1), max (u_5 + 1) (u_3 + 1)} (Sum.{u_2, u_4} (Sum.{u_2, 0} ι0 Unit) ι2)
      (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit)))
  (σD :
    Equiv.{max (u_8 + 1) (u_6 + 1), max (u_9 + 1) (u_7 + 1)} (Sum.{u_6, u_8} (Sum.{u_6, 0} ι0' Unit) ι2')
      (Sum.{u_7, u_9} ι1' (Sum.{u_9, 0} ι3' Unit))),
  Ne.{u_1 + 1}
      (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_1, max (max u_6 u_8) u_3 u_5, max (max u_7 u_9) u_2 u_4}
        (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{u_1, max u_2 u_4, max u_3 u_5, max u_6 u_8, max u_7 u_9}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{u_1, u_2, u_3, u_4, u_5,
              u_6, u_7, u_8, u_9}
            H hzC hlC hzD hlD))
        (Equiv.sumCongr.{max u_7 u_9, max u_3 u_5, max u_2 u_4, max u_6 u_8} σD
          (Equiv.symm.{max (u_2 + 1) (u_4 + 1), max (u_3 + 1) (u_5 + 1)} σC)))
      0 →
    Eq.{u_1 + 1} (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_2, u_3, u_4, u_5} C zC lC hzC hlC σC)
      (HMul.hMul.{u_1, u_1, u_1}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor.{u_1, u_2, u_3, u_4,
            u_5, u_6, u_7, u_8, u_9}
          H hzC hlC hzD hlD σC σD)
        (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_6, u_7, u_8, u_9} D zD lD hzD hlD σD))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [118438, 131885), lines 1626–1829.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_in_original_basis' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_eq_of_retained_basis`

support theorem; source line 236.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_eq_of_retained_basis.{u_1, u_2,
    u_3, u_4, u_5, u_6, u_7, u_8,
    u_9} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  {ι0' : Type u_6} {ι1' : Type u_7} {ι2' : Type u_8} {ι3' : Type u_9} [inst_1 : Fintype.{u_2} ι0]
  [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3] [inst_5 : Fintype.{u_6} ι0']
  [inst_6 : Fintype.{u_7} ι1'] [inst_7 : Fintype.{u_8} ι2'] [inst_8 : Fintype.{u_9} ι3']
  [inst_9 : DecidableEq.{u_2 + 1} ι0] [inst_10 : DecidableEq.{u_3 + 1} ι1] [inst_11 : DecidableEq.{u_4 + 1} ι2]
  [inst_12 : DecidableEq.{u_5 + 1} ι3] [inst_13 : DecidableEq.{u_6 + 1} ι0'] [inst_14 : DecidableEq.{u_7 + 1} ι1']
  [inst_15 : DecidableEq.{u_8 + 1} ι2'] [inst_16 : DecidableEq.{u_9 + 1} ι3']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8,
        u_9}
      C D zC lC zD lD)
  (hzC :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) zC) 0)
  (hlC :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (hzD :
    Eq.{max (u_1 + 1) (u_8 + 1)}
      (Matrix.mulVec.{u_1, u_8, u_7} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D) zD) 0)
  (hlD :
    Eq.{max (u_1 + 1) (u_7 + 1)}
      (Matrix.vecMul.{u_1, u_8, u_7} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D)) 0)
  (σC :
    Equiv.{max (u_4 + 1) (u_2 + 1), max (u_5 + 1) (u_3 + 1)} (Sum.{u_2, u_4} (Sum.{u_2, 0} ι0 Unit) ι2)
      (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit)))
  (σD :
    Equiv.{max (u_8 + 1) (u_6 + 1), max (u_9 + 1) (u_7 + 1)} (Sum.{u_6, u_8} (Sum.{u_6, 0} ι0' Unit) ι2')
      (Sum.{u_7, u_9} ι1' (Sum.{u_9, 0} ι3' Unit))),
  Eq.{u_1 + 1}
      (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_1, max (max u_6 u_8) u_3 u_5, max (max u_7 u_9) u_2 u_4}
        (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{u_1, max u_2 u_4, max u_3 u_5, max u_6 u_8, max u_7 u_9}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{u_1, u_2, u_3, u_4, u_5,
              u_6, u_7, u_8, u_9}
            H hzC hlC hzD hlD))
        (Equiv.sumCongr.{max u_7 u_9, max u_3 u_5, max u_2 u_4, max u_6 u_8} σD
          (Equiv.symm.{max (u_2 + 1) (u_4 + 1), max (u_3 + 1) (u_5 + 1)} σC)))
      (HPow.hPow.{u_1, 0, u_1} (-1) (Fintype.card.{max u_5 u_3} (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit)))) →
    Eq.{u_1 + 1} (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_2, u_3, u_4, u_5} C zC lC hzC hlC σC)
      (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_6, u_7, u_8, u_9} D zD lD hzD hlD σD)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [132059, 145918), lines 1831–2043.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_eq_of_retained_basis' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComplex`

def; source line 259.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComplex.{u_1} : {K : Type u_1} →
  [inst : Field.{u_1} K] → ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, 0, 0, 0, 0} K Empty Empty Unit Unit
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [146095, 146383), lines 2045–2050.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComplex' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailTarget`

def; source line 267.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailTarget.{u_1} : {K : Type u_1} →
  [inst : Field.{u_1} K] → ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, 0, 0, 0, 0} K Empty Unit Unit Empty
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [146521, 146808), lines 2052–2057.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailTarget' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailOrientation`

def; source line 275.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailOrientation : Equiv.{1, 1}
  (Sum.{0, 0} (Sum.{0, 0} Empty Unit) Unit) (Sum.{0, 0} Empty (Sum.{0, 0} Unit Unit))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [146945, 147119), lines 2059–2062.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailOrientation' does not depend on any axioms
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison`

def; source line 301.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison.{u_1} : {K : Type u_1} →
  [inst : Field.{u_1} K] →
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{u_1, 0, 0, 0, 0, 0, 0, 0, 0}
      ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComplex.{u_1}
      ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailTarget.{u_1} 0 1 0 0
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [147222, 149450), lines 2062–2098.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison_off_diagonal`

support theorem; source line 317.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison_off_diagonal.{u_1} : ∀ {K : Type u_1}
  [inst : Field.{u_1} K] (r a : K),
  Eq.{u_1 + 1}
    (Matrix.mulVec.{u_1, 0, 0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f3aug.{u_1, 0, 0, 0, 0, 0, 0, 0, 0}
        ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison.{u_1})
      (Sum.elim.{0, 0, u_1 + 1} (fun x => r) fun x => a))
    (Sum.elim.{0, 0, u_1 + 1} (fun e => Empty.elim.{u_1 + 1} e) fun x => HSub.hSub.{u_1, u_1, u_1} a r)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [149591, 153053), lines 2100–2154.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison_off_diagonal' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailConeContraction`

def; source line 326.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailConeContraction.{u_1} : {K : Type u_1} →
  [inst : Field.{u_1} K] →
    ZInQ.Contrib.CloudB3RC53.Torsion.Contraction.{u_1, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{u_1, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{u_1, 0, 0, 0, 0, 0, 0, 0, 0}
          ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison.{u_1} ⋯ ⋯ ⋯ ⋯))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [153207, 189616), lines 2156–2646.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailConeContraction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison_cone_torsion_ne_zero`

support theorem; source line 359.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison_cone_torsion_ne_zero.{u_1} : ∀ {K : Type u_1}
  [inst : Field.{u_1} K],
  Ne.{u_1 + 1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_1, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{u_1, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{u_1, 0, 0, 0, 0, 0, 0, 0, 0}
          ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison.{u_1} ⋯ ⋯ ⋯ ⋯))
      (Equiv.sumCongr.{0, 0, 0, 0} (Equiv.sumComm.{0, 0} (Sum.{0, 0} Empty Unit) Unit)
        (Equiv.symm.{1, 1} ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailOrientation)))
    0
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [189762, 226942), lines 2648–3149.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison_cone_torsion_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailEvenEquiv`

def; source line 366.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailEvenEquiv : Equiv.{1, 1} (Fin 4)
  (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} Empty Unit) Unit) (Sum.{0, 0} Empty (Sum.{0, 0} Unit Unit)))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [227104, 227359), lines 3151–3155.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailEvenEquiv' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison_retained_cone_basis`

support theorem; source line 384.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison_retained_cone_basis.{u_1} : ∀ {K : Type u_1}
  [inst : Field.{u_1} K],
  Eq.{u_1 + 1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_1, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{u_1, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{u_1, 0, 0, 0, 0, 0, 0, 0, 0}
          ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison.{u_1} ⋯ ⋯ ⋯ ⋯))
      (Equiv.sumCongr.{0, 0, 0, 0} (Equiv.sumComm.{0, 0} (Sum.{0, 0} Empty Unit) Unit)
        (Equiv.symm.{1, 1} ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailOrientation)))
    1
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [227499, 264685), lines 3157–3658.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tailComparison_retained_cone_basis' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tail_functional_ne_zero`

support theorem; source line 406.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tail_functional_ne_zero.{u_1} : ∀ {K : Type u_1}
  [inst : Field.{u_1} K], Ne.{u_1 + 1} 1 0
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [264846, 265786), lines 3660–3677.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.tail_functional_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadIndex`

abbrev; source line 426.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadIndex : Type → Type → Type → Type → ℤ → Type
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [265936, 266047), lines 3679–3681.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadIndex' does not depend on any axioms
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadD`

def; source line 434.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadD : {K : Type} →
  [inst : Field.{0} K] →
    {ι0 ι1 ι2 ι3 : Type} →
      [Fintype.{0} ι0] →
        [inst_2 : Fintype.{0} ι1] →
          [inst_3 : Fintype.{0} ι2] →
            ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3 →
              (n : ℤ) →
                LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K)
                  (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadIndex ι0 ι1 ι2 ι3 n → K)
                  (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadIndex ι0 ι1 ι2 ι3
                      (HAdd.hAdd.{0, 0, 0} n 1) →
                    K)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [266144, 270890), lines 3681–3750.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadD' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadD_square`

support theorem; source line 443.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadD_square : ∀ {K : Type} [inst : Field.{0} K]
  {ι0 ι1 ι2 ι3 : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1] [inst_3 : Fintype.{0} ι2]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3) (n : ℤ)
  (v : ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadIndex ι0 ι1 ι2 ι3 n → K),
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadD C (HAdd.hAdd.{0, 0, 0} n 1))
      ((ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadD C n) v))
    0
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [271022, 294238), lines 3752–4082.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadD_square' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx`

abbrev; source line 455.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx : {K : Type} →
  [inst : Field.{0} K] →
    {ι0 ι1 ι2 ι3 : Type} →
      [Fintype.{0} ι0] →
        [inst_2 : Fintype.{0} ι1] →
          [inst_3 : Fintype.{0} ι2] →
            ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3 →
              ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [294377, 294901), lines 4084–4095.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.lift_linear_cycles`

support theorem; source line 464.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.lift_linear_cycles : ∀ {K : Type} [inst : Field.{0} K]
  {ι : Type} [Fintype.{0} ι] [DecidableEq.{1} ι] (E : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K),
  ZInQ.Contrib.CloudB3RC53.SelmerDuality.GAcyclic.{0} E →
    ∀ (n : ℤ)
      (M :
        LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (ι → K) ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} E n)),
      (∀ (v : ι → K),
          Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} E n (HAdd.hAdd.{0, 0, 0} n 1) ⋯) (M v)) 0) →
        ∃ L,
          ∀ (v : ι → K),
            Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} E (HSub.hSub.{0, 0, 0} n 1) n ⋯) (L v)) (M v)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [295034, 337236), lines 4097–4616.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.lift_linear_cycles' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf`

def; source line 482.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf : {K : Type} →
  [inst : Field.{0} K] →
    {ι κ : Type} →
      [Fintype.{0} ι] →
        [DecidableEq.{1} ι] → LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (ι → K) (κ → K) → Matrix.{0, 0, 0} κ ι K
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [337381, 339690), lines 4618–4652.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf_mulVec`

support theorem; source line 486.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf_mulVec : ∀ {K : Type} [inst : Field.{0} K]
  {ι κ : Type} [inst_1 : Fintype.{0} ι] [inst_2 : DecidableEq.{1} ι]
  (F : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (ι → K) (κ → K)) (v : ι → K),
  Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf F) v) (F v)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [339825, 346042), lines 4654–4743.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf_mulVec' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf_chain`

support theorem; source line 495.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf_chain : ∀ {K : Type} [inst : Field.{0} K]
  {a b c d : Type} [inst_1 : Fintype.{0} a] [inst_2 : DecidableEq.{1} a] [inst_3 : Fintype.{0} b]
  [inst_4 : DecidableEq.{1} b] [inst_5 : Fintype.{0} c] [DecidableEq.{1} c] [Fintype.{0} d] [DecidableEq.{1} d]
  (A : Matrix.{0, 0, 0} d c K) (B : Matrix.{0, 0, 0} b a K)
  (F : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (a → K) (c → K))
  (G : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (b → K) (d → K)),
  (∀ (v : a → K), Eq.{1} (Matrix.mulVec.{0, 0, 0} A (F v)) (G (Matrix.mulVec.{0, 0, 0} B v))) →
    Eq.{1} (HMul.hMul.{0, 0, 0} A (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf F))
      (HMul.hMul.{0, 0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf G) B)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [346184, 360200), lines 4745–4938.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.matrixOf_chain' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison`

structure; source line 508.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison : {K : Type} →
  [inst : Field.{0} K] →
    {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} →
      [inst_1 : Fintype.{0} ι0] →
        [inst_2 : Fintype.{0} ι1] →
          [inst_3 : Fintype.{0} ι2] →
            [Fintype.{0} ι3] →
              [inst_5 : Fintype.{0} ι0'] →
                [inst_6 : Fintype.{0} ι1'] →
                  [inst_7 : Fintype.{0} ι2'] →
                    (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3) →
                      (D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3') →
                        (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K) →
                          ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                              (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S →
                            ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                                (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) S →
                              Type
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [360341, 362114), lines 4940–4969.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_model_comparison`

support theorem; source line 526.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_model_comparison : ∀ {K : Type} [inst : Field.{0} K]
  {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1] [inst_3 : Fintype.{0} ι2]
  [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1'] [inst_7 : Fintype.{0} ι2']
  [Fintype.{0} ι3'] [DecidableEq.{1} ι0] [DecidableEq.{1} ι1] [DecidableEq.{1} ι2] [DecidableEq.{1} ι3]
  [DecidableEq.{1} ι0'] [DecidableEq.{1} ι1'] [DecidableEq.{1} ι2'] [DecidableEq.{1} ι3']
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3)
  (D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3')
  (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K)
  (ψC :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S)
  (ψD :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) S),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψD) →
    Nonempty.{1} (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison C D S ψC ψD)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [362256, 370956), lines 4971–5084.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_model_comparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMapLinear`

def; source line 661.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMapLinear : {K : Type} →
  [inst : Field.{0} K] →
    {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} →
      [inst_1 : Fintype.{0} ι0] →
        [inst_2 : Fintype.{0} ι1] →
          [inst_3 : Fintype.{0} ι2] →
            [inst_4 : Fintype.{0} ι3] →
              [inst_5 : Fintype.{0} ι0'] →
                [inst_6 : Fintype.{0} ι1'] →
                  [inst_7 : Fintype.{0} ι2'] →
                    {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3} →
                      {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'} →
                        ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.{0, 0, 0, 0, 0, 0, 0, 0, 0} C D →
                          (n : ℤ) →
                            LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K)
                              ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                  (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) n)
                              ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                                  (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) n)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [371106, 377344), lines 5086–5174.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMapLinear' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMapLinear_comm`

support theorem; source line 672.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMapLinear_comm : ∀ {K : Type} [inst : Field.{0} K]
  {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1] [inst_3 : Fintype.{0} ι2]
  [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1'] [inst_7 : Fintype.{0} ι2']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'}
  (F : ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.{0, 0, 0, 0, 0, 0, 0, 0, 0} C D) (n : ℤ)
  (v :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) n)),
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMapLinear F (HAdd.hAdd.{0, 0, 0} n 1))
      ((ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadD C n) v))
    ((ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadD D n)
      ((ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMapLinear F n) v))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [377484, 414727), lines 5176–5675.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMapLinear_comm' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap`

def; source line 687.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap : {K : Type} →
  [inst : Field.{0} K] →
    {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} →
      [inst_1 : Fintype.{0} ι0] →
        [inst_2 : Fintype.{0} ι1] →
          [inst_3 : Fintype.{0} ι2] →
            [inst_4 : Fintype.{0} ι3] →
              [inst_5 : Fintype.{0} ι0'] →
                [inst_6 : Fintype.{0} ι1'] →
                  [inst_7 : Fintype.{0} ι2'] →
                    {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3} →
                      {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'} →
                        ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.{0, 0, 0, 0, 0, 0, 0, 0, 0} C D →
                          ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C)
                            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [414872, 416455), lines 5677–5702.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.homotopyComponent`

def; source line 695.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.homotopyComponent : {K : Type} →
  [inst : Field.{0} K] →
    {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} →
      [inst_1 : Fintype.{0} ι0] →
        [inst_2 : Fintype.{0} ι1] →
          [inst_3 : Fintype.{0} ι2] →
            [inst_4 : Fintype.{0} ι3] →
              [inst_5 : Fintype.{0} ι0'] →
                [inst_6 : Fintype.{0} ι1'] →
                  [inst_7 : Fintype.{0} ι2'] →
                    {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3} →
                      {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'} →
                        {S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K} →
                          {ψC :
                              ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                                (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S} →
                            {ψD :
                                ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                                  (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) S} →
                              ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison C D S ψC ψD →
                                (i j : ℤ) →
                                  Quiver.Hom.{0, 1}
                                    (HomologicalComplex.X.{0, 1, 0}
                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
                                        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C))
                                      i)
                                    (HomologicalComplex.X.{0, 1, 0}
                                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0} S) j)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [416589, 424283), lines 5704–5799.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.homotopyComponent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.toCCHomotopy`

def; source line 708.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.toCCHomotopy : {K : Type} →
  [inst : Field.{0} K] →
    {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} →
      [inst_1 : Fintype.{0} ι0] →
        [inst_2 : Fintype.{0} ι1] →
          [inst_3 : Fintype.{0} ι2] →
            [inst_4 : Fintype.{0} ι3] →
              [inst_5 : Fintype.{0} ι0'] →
                [inst_6 : Fintype.{0} ι1'] →
                  [inst_7 : Fintype.{0} ι2'] →
                    {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3} →
                      {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'} →
                        {S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K} →
                          {ψC :
                              ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                                (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S} →
                            {ψD :
                                ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                                  (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) S} →
                              (H :
                                  ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison C D S ψC ψD) →
                                Homotopy.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψC)
                                  (CategoryTheory.CategoryStruct.comp.{0, 1}
                                    (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap H.f))
                                    (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψD))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [424443, 437991), lines 5801–5960.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.toCCHomotopy' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.quasiIso`

support theorem; source line 760.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.quasiIso : ∀ {K : Type} [inst : Field.{0} K]
  {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1] [inst_3 : Fintype.{0} ι2]
  [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1'] [inst_7 : Fintype.{0} ι2']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'}
  {S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K}
  {ψC :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S}
  {ψD :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) S}
  (H : ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison C D S ψC ψD),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψC) →
    QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψD) →
      QuasiIso.{0, 1, 0}
        (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap H.f))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [438146, 461362), lines 5962–6260.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.quasiIso' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.evenVector`

abbrev; source line 803.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.evenVector : {K ι1 ι3 ι0' ι2' : Type} →
  (ι0' → K) →
    K →
      (ι2' → K) →
        (ι1 → K) →
          (ι3 → K) → K → Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} ι0' Unit) ι2') (Sum.{0, 0} ι1 (Sum.{0, 0} ι3 Unit)) → K
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [461513, 461866), lines 6262–6270.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.evenVector' does not depend on any axioms
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.oddVector`

abbrev; source line 810.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.oddVector : {K ι0 ι2 ι1' ι3' : Type} →
  (ι1' → K) →
    (ι3' → K) →
      K →
        (ι0 → K) →
          K → (ι2 → K) → Sum.{0, 0} (Sum.{0, 0} ι1' (Sum.{0, 0} ι3' Unit)) (Sum.{0, 0} (Sum.{0, 0} ι0 Unit) ι2) → K
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [461964, 462316), lines 6270–6278.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.oddVector' does not depend on any axioms
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.cone_even_differential`

support theorem; source line 822.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.cone_even_differential : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1']
  [inst_7 : Fintype.{0} ι2'] [inst_8 : Fintype.{0} ι3']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{0, 0, 0, 0, 0, 0, 0, 0, 0} C D zC lC zD
      lD)
  (hzC : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0)
  (hlC : Eq.{1} (Matrix.vecMul.{0, 0, 0} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C)) 0)
  (hzD : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D) zD) 0)
  (hlD : Eq.{1} (Matrix.vecMul.{0, 0, 0} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D)) 0)
  (d0 : ι0' → K) (a : K) (d2 : ι2' → K) (c1 : ι1 → K) (c3 : ι3 → K) (b : K),
  Eq.{1}
    (Matrix.mulVec.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.dOE.{0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            H hzC hlC hzD hlD)))
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.evenVector d0 a d2 c1 c3 b))
    (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.oddVector
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{0, 0, 0, 0, 0} D) d0)
          (HSMul.hSMul.{0, 0, 0} a zD))
        (Matrix.mulVec.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f1.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{0, 0, 0, 0, 0, 0, 0, 0, 0}
              H))
          c1))
      (HAdd.hAdd.{0, 0, 0} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{0, 0, 0, 0, 0} D) d2)
        (Matrix.mulVec.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f3.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{0, 0, 0, 0, 0, 0, 0, 0, 0}
              H))
          c3))
      (HAdd.hAdd.{0, 0, 0}
        (HAdd.hAdd.{0, 0, 0} (dotProduct.{0, 0} lD d2)
          (dotProduct.{0, 0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.functionalBoundary.{0, 0, 0, 0,
                0, 0, 0, 0, 0}
              H)
            c3))
        b)
      0 0 (Neg.neg.{0} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) c1)))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [462413, 479013), lines 6278–6535.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.cone_even_differential' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.cone_odd_differential`

support theorem; source line 839.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.cone_odd_differential : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1']
  [inst_7 : Fintype.{0} ι2'] [inst_8 : Fintype.{0} ι3']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{0, 0, 0, 0, 0, 0, 0, 0, 0} C D zC lC zD
      lD)
  (hzC : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0)
  (hlC : Eq.{1} (Matrix.vecMul.{0, 0, 0} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C)) 0)
  (hzD : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D) zD) 0)
  (hlD : Eq.{1} (Matrix.vecMul.{0, 0, 0} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D)) 0)
  (d1 : ι1' → K) (d3 : ι3' → K) (b : K) (c0 : ι0 → K) (a : K) (c2 : ι2 → K),
  Eq.{1}
    (Matrix.mulVec.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.dEO.{0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            H hzC hlC hzD hlD)))
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.oddVector d1 d3 b c0 a c2))
    (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.evenVector
      (HAdd.hAdd.{0, 0, 0}
        (Matrix.mulVec.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f0.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{0, 0, 0, 0, 0, 0, 0, 0, 0}
              H))
          c0)
        (HSMul.hSMul.{0, 0, 0} a
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.classBoundary.{0, 0, 0, 0, 0, 0,
              0, 0, 0}
            H)))
      a
      (HAdd.hAdd.{0, 0, 0} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D) d1)
        (Matrix.mulVec.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f2.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{0, 0, 0, 0, 0, 0, 0, 0, 0}
              H))
          c2))
      (HSub.hSub.{0, 0, 0}
        (Neg.neg.{0} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{0, 0, 0, 0, 0} C) c0))
        (HSMul.hSMul.{0, 0, 0} a zC))
      (Neg.neg.{0} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{0, 0, 0, 0, 0} C) c2))
      (Neg.neg.{0} (dotProduct.{0, 0} lC c2)))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [479181, 495556), lines 6537–6791.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.cone_odd_differential' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.aug_cone_exact`

support theorem; source line 858.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.aug_cone_exact : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1']
  [inst_7 : Fintype.{0} ι2'] [inst_8 : Fintype.{0} ι3']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{0, 0, 0, 0, 0, 0, 0, 0, 0} C D zC lC zD
      lD)
  (hzC : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0)
  (hlC : Eq.{1} (Matrix.vecMul.{0, 0, 0} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C)) 0)
  (hzD : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D) zD) 0)
  (hlD : Eq.{1} (Matrix.vecMul.{0, 0, 0} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D)) 0),
  QuasiIso.{0, 1, 0}
      (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            H))) →
    ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.IsExact.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{0, 0, 0, 0, 0, 0, 0, 0, 0} H
          hzC hlC hzD hlD))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [495723, 511202), lines 6793–7005.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.aug_cone_exact' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.aug_cone_torsion_ne_zero`

support theorem; source line 997.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.aug_cone_torsion_ne_zero : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1']
  [inst_7 : Fintype.{0} ι2'] [inst_8 : Fintype.{0} ι3'] [inst_9 : DecidableEq.{1} ι0] [inst_10 : DecidableEq.{1} ι1]
  [inst_11 : DecidableEq.{1} ι2] [inst_12 : DecidableEq.{1} ι3] [inst_13 : DecidableEq.{1} ι0']
  [inst_14 : DecidableEq.{1} ι1'] [inst_15 : DecidableEq.{1} ι2'] [inst_16 : DecidableEq.{1} ι3']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{0, 0, 0, 0, 0, 0, 0, 0, 0} C D zC lC zD
      lD)
  (hzC : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0)
  (hlC : Eq.{1} (Matrix.vecMul.{0, 0, 0} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C)) 0)
  (hzD : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D) zD) 0)
  (hlD : Eq.{1} (Matrix.vecMul.{0, 0, 0} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D)) 0),
  QuasiIso.{0, 1, 0}
      (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            H))) →
    ∀ (σC : Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0 Unit) ι2) (Sum.{0, 0} ι1 (Sum.{0, 0} ι3 Unit)))
      (σD : Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0' Unit) ι2') (Sum.{0, 0} ι1' (Sum.{0, 0} ι3' Unit))),
      Ne.{1}
        (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{0, 0, 0, 0, 0, 0, 0, 0,
                0}
              H hzC hlC hzD hlD))
          (Equiv.sumCongr.{0, 0, 0, 0} σD (Equiv.symm.{1, 1} σC)))
        0
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [511362, 529679), lines 7007–7262.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.aug_cone_torsion_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_formula_of_quasiIso`

support theorem; source line 1010.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_formula_of_quasiIso : ∀
  {K : Type} [inst : Field.{0} K] {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0]
  [inst_2 : Fintype.{0} ι1] [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0']
  [inst_6 : Fintype.{0} ι1'] [inst_7 : Fintype.{0} ι2'] [inst_8 : Fintype.{0} ι3'] [inst_9 : DecidableEq.{1} ι0]
  [inst_10 : DecidableEq.{1} ι1] [inst_11 : DecidableEq.{1} ι2] [inst_12 : DecidableEq.{1} ι3]
  [inst_13 : DecidableEq.{1} ι0'] [inst_14 : DecidableEq.{1} ι1'] [inst_15 : DecidableEq.{1} ι2']
  [inst_16 : DecidableEq.{1} ι3'] {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'} {zC : ι1 → K} {lC : ι2 → K}
  {zD : ι1' → K} {lD : ι2' → K}
  (H :
    ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{0, 0, 0, 0, 0, 0, 0, 0, 0} C D zC lC zD
      lD)
  (hzC : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0)
  (hlC : Eq.{1} (Matrix.vecMul.{0, 0, 0} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C)) 0)
  (hzD : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D) zD) 0)
  (hlD : Eq.{1} (Matrix.vecMul.{0, 0, 0} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D)) 0),
  QuasiIso.{0, 1, 0}
      (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{0, 0, 0, 0, 0, 0, 0, 0, 0}
            H))) →
    ∀ (σC : Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0 Unit) ι2) (Sum.{0, 0} ι1 (Sum.{0, 0} ι3 Unit)))
      (σD : Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0' Unit) ι2') (Sum.{0, 0} ι1' (Sum.{0, 0} ι3' Unit))),
      Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} C zC lC hzC hlC σC)
        (HMul.hMul.{0, 0, 0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor.{0, 0, 0, 0, 0, 0,
              0, 0, 0}
            H hzC hlC hzD hlD σC σD)
          (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} D zD lD hzD hlD σD))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [529849, 543844), lines 7264–7463.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.coordinate_formula_of_quasiIso' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actual_cycle_lift`

support theorem; source line 1039.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actual_cycle_lift : ∀ {K : Type} [inst : Field.{0} K]
  {ι0 ι1 ι2 ι3 : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1] [inst_3 : Fintype.{0} ι2]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3)
  (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K)
  (ψ :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψ) →
    ∀ (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)),
      Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 1 2 ⋯) z) 0 →
        ∃ zC,
          Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0 ∧
            ∃ b,
              Eq.{1} (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψ 1 1 ⋯) zC) z)
                ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) b)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [544020, 582419), lines 7465–7939.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actual_cycle_lift' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow`

def; source line 1060.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow : {K : Type} →
  [inst : Field.{0} K] →
    {ι0 ι1 ι2 ι3 : Type} →
      [inst_1 : Fintype.{0} ι0] →
        [inst_2 : Fintype.{0} ι1] →
          [inst_3 : Fintype.{0} ι2] →
            [DecidableEq.{1} ι2] →
              (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3) →
                (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K) →
                  ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S →
                    LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K)
                        (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2)) K →
                      ι2 → K
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [582563, 585987), lines 7941–7989.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow_value`

support theorem; source line 1066.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow_value : ∀ {K : Type} [inst : Field.{0} K]
  {ι0 ι1 ι2 ι3 : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1] [inst_3 : Fintype.{0} ι2]
  [inst_4 : DecidableEq.{1} ι2] (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3)
  (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K)
  (ψ :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S)
  (L : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2)) K)
  (v : ι2 → K),
  Eq.{1} (dotProduct.{0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow C S ψ L) v)
    (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψ 2 2 ⋯) v))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [586122, 601805), lines 7991–8196.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow_value' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow_closed`

support theorem; source line 1076.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow_closed : ∀ {K : Type} [inst : Field.{0} K]
  {ι0 ι1 ι2 ι3 : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1] [inst_3 : Fintype.{0} ι2]
  [DecidableEq.{1} ι1] [inst_5 : DecidableEq.{1} ι2]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3)
  (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K)
  (ψ :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S)
  (L : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2)) K),
  (∀ (v : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)),
      Eq.{1} (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 1 2 ⋯) v)) 0) →
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow C S ψ L)
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C))
      0
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [601946, 617896), lines 8198–8404.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.functionalPrimitive`

def; source line 1088.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.functionalPrimitive : {K : Type} →
  [inst : Field.{0} K] →
    {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} →
      [inst_1 : Fintype.{0} ι0] →
        [inst_2 : Fintype.{0} ι1] →
          [inst_3 : Fintype.{0} ι2] →
            [inst_4 : Fintype.{0} ι3] →
              [inst_5 : Fintype.{0} ι0'] →
                [inst_6 : Fintype.{0} ι1'] →
                  [inst_7 : Fintype.{0} ι2'] →
                    [DecidableEq.{1} ι3] →
                      {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3} →
                        {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'} →
                          {S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K} →
                            {ψC :
                                ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                                  (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S} →
                              {ψD :
                                  ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) S} →
                                ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison C D S ψC ψD →
                                  LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K)
                                      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2)) K →
                                    ι3 → K
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [618038, 623513), lines 8406–8478.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.functionalPrimitive' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.functionalPrimitive_value`

support theorem; source line 1097.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.functionalPrimitive_value : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1']
  [inst_7 : Fintype.{0} ι2'] [inst_8 : DecidableEq.{1} ι3]
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'}
  {S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K}
  {ψC :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S}
  {ψD :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) S}
  (H : ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison C D S ψC ψD)
  (L : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2)) K)
  (v : ι3 → K), Eq.{1} (dotProduct.{0, 0} (H.functionalPrimitive L) v) (Neg.neg.{0} (L (H.h3 v)))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [623675, 637778), lines 8480–8667.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.functionalPrimitive_value' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.actual_functional_discrepancy`

support theorem; source line 1114.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.actual_functional_discrepancy : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1']
  [inst_7 : Fintype.{0} ι2'] [inst_8 : DecidableEq.{1} ι2] [inst_9 : DecidableEq.{1} ι3] [inst_10 : DecidableEq.{1} ι2']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'}
  {S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K}
  {ψC :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S}
  {ψD :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) S}
  (H : ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison C D S ψC ψD)
  (L : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2)) K),
  (∀ (v : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)),
      Eq.{1} (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 1 2 ⋯) v)) 0) →
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow D S ψD L)
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f2.{0, 0, 0, 0, 0, 0, 0, 0, 0} H.f))
      (HAdd.hAdd.{0, 0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow C S ψC L)
        (Matrix.vecMul.{0, 0, 0} (H.functionalPrimitive L)
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{0, 0, 0, 0, 0} C)))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [637946, 655772), lines 8669–8899.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.actual_functional_discrepancy' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.actual_class_discrepancy`

support theorem; source line 1138.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.actual_class_discrepancy : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1']
  [inst_7 : Fintype.{0} ι2'] {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3'}
  {S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K}
  {ψC :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S}
  {ψD :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) S}
  (H : ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison C D S ψC ψD),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψD) →
    ∀ (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)) (zC : ι1 → K) (zD : ι1' → K),
      Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0 →
        Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D) zD) 0 →
          ∀ (bC bD : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 0)),
            Eq.{1} (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψC 1 1 ⋯) zC) z)
                ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bC) →
              Eq.{1} (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψD 1 1 ⋯) zD) z)
                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bD) →
                ∃ b,
                  Eq.{1}
                    (Matrix.mulVec.{0, 0, 0}
                      (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f1.{0, 0, 0, 0, 0, 0, 0, 0, 0} H.f) zC)
                    (HAdd.hAdd.{0, 0, 0} zD
                      (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{0, 0, 0, 0, 0} D) b))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [655944, 704751), lines 8901–9528.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.ModelComparison.actual_class_discrepancy' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_actual_homotopy_comparison`

support theorem; source line 1173.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_actual_homotopy_comparison : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1']
  [inst_7 : Fintype.{0} ι2'] [Fintype.{0} ι3'] [DecidableEq.{1} ι0] [DecidableEq.{1} ι1] [inst_11 : DecidableEq.{1} ι2]
  [DecidableEq.{1} ι3] [DecidableEq.{1} ι0'] [DecidableEq.{1} ι1'] [inst_15 : DecidableEq.{1} ι2'] [DecidableEq.{1} ι3']
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3)
  (D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3')
  (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K)
  (ψC :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S)
  (ψD :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) S),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψC) →
    QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψD) →
      ∀ (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)),
        Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 1 2 ⋯) z) 0 →
          ∀
            (L :
              LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2)) K),
            (∀ (v : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)),
                Eq.{1} (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 1 2 ⋯) v)) 0) →
              ∃ zC zD bC bD,
                Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0 ∧
                  Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D) zD) 0 ∧
                    Eq.{1} (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψC 1 1 ⋯) zC) z)
                        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bC) ∧
                      Eq.{1}
                          (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψD 1 1 ⋯) zD) z)
                          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bD) ∧
                        Nonempty.{1}
                          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{0, 0, 0, 0, 0, 0,
                              0, 0, 0}
                            C D zC (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow C S ψC L) zD
                            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow D S ψD L))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [704918, 791396), lines 9530–10558.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_actual_homotopy_comparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_actual_retained_comparison`

support theorem; source line 1196.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_actual_retained_comparison : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : Fintype.{0} ι0'] [inst_6 : Fintype.{0} ι1']
  [inst_7 : Fintype.{0} ι2'] [inst_8 : Fintype.{0} ι3'] [inst_9 : DecidableEq.{1} ι0] [inst_10 : DecidableEq.{1} ι1]
  [inst_11 : DecidableEq.{1} ι2] [inst_12 : DecidableEq.{1} ι3] [inst_13 : DecidableEq.{1} ι0']
  [inst_14 : DecidableEq.{1} ι1'] [inst_15 : DecidableEq.{1} ι2'] [inst_16 : DecidableEq.{1} ι3']
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3)
  (D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0' ι1' ι2' ι3')
  (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K)
  (ψC :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S)
  (ψD :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx D) S),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψC) →
    QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψD) →
      ∀ (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)),
        Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 1 2 ⋯) z) 0 →
          ∀
            (L :
              LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2)) K),
            (∀ (v : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)),
                Eq.{1} (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 1 2 ⋯) v)) 0) →
              ∀ (σC : Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0 Unit) ι2) (Sum.{0, 0} ι1 (Sum.{0, 0} ι3 Unit)))
                (σD : Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0' Unit) ι2') (Sum.{0, 0} ι1' (Sum.{0, 0} ι3' Unit))),
                ∃ zC lC zD lD,
                  ∃ (hzC :
                    Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC)
                      0)
                    (hlC :
                    Eq.{1} (Matrix.vecMul.{0, 0, 0} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C))
                      0)
                    (hzD :
                    Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D) zD)
                      0)
                    (hlD :
                    Eq.{1} (Matrix.vecMul.{0, 0, 0} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} D))
                      0),
                    (∃ bC,
                        Eq.{1}
                          (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψC 1 1 ⋯) zC) z)
                          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bC)) ∧
                      (∃ bD,
                          Eq.{1}
                            (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψD 1 1 ⋯) zD) z)
                            ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bD)) ∧
                        (∀ (v : ι2 → K),
                            Eq.{1} (dotProduct.{0, 0} lC v)
                              (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψC 2 2 ⋯) v))) ∧
                          (∀ (v : ι2' → K),
                              Eq.{1} (dotProduct.{0, 0} lD v)
                                (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψD 2 2 ⋯) v))) ∧
                            ∃ H,
                              QuasiIso.{0, 1, 0}
                                  (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{0,
                                          0, 0, 0, 0, 0, 0, 0, 0}
                                        H))) ∧
                                Ne.{1}
                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor.{0,
                                        0, 0, 0, 0, 0, 0, 0, 0}
                                      H hzC hlC hzD hlD σC σD)
                                    0 ∧
                                  Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} C zC lC hzC hlC σC)
                                    (HMul.hMul.{0, 0, 0}
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor.{0,
                                          0, 0, 0, 0, 0, 0, 0, 0}
                                        H hzC hlC hzD hlD σC σD)
                                      (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} D zD lD hzD hlD σD))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [791556, 943760), lines 10560–12369.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_actual_retained_comparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_unique_adjugate_coordinate`

support theorem; source line 1247.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_unique_adjugate_coordinate : ∀ {K : Type}
  [inst : Field.{0} K] {m : ℕ} (D : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) K)
  (z w : Fin (HAdd.hAdd.{0, 0, 0} m 1) → K),
  Eq.{1} (Matrix.mulVec.{0, 0, 0} D z) 0 →
    Eq.{1} (Matrix.vecMul.{0, 0, 0} w D) 0 →
      Ne.{1} (Matrix.adjugate.{0, 0} D) 0 →
        ExistsUnique.{1} fun u => ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord.{0} D z w u
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [943920, 952152), lines 12371–12548.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_unique_adjugate_coordinate' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_actual_adjugate_coordinate`

support theorem; source line 1266.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_actual_adjugate_coordinate : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : DecidableEq.{1} ι0] [inst_6 : DecidableEq.{1} ι1]
  [inst_7 : DecidableEq.{1} ι2] [inst_8 : DecidableEq.{1} ι3] {m : ℕ}
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3)
  (D : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) K),
  Ne.{1} (Matrix.adjugate.{0, 0} D) 0 →
    ∀ (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K)
      (ψC :
        ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S)
      (ψD :
        ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx
            (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} D))
          S),
      QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψC) →
        QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψD) →
          ∀ (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)),
            Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 1 2 ⋯) z) 0 →
              ∀
                (L :
                  LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2))
                    K),
                (∀ (v : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)),
                    Eq.{1} (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 1 2 ⋯) v)) 0) →
                  ∀ (σC : Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0 Unit) ι2) (Sum.{0, 0} ι1 (Sum.{0, 0} ι3 Unit))),
                    ∃ zC lC zD lD,
                      ∃ (hzC :
                        Eq.{1}
                          (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0)
                        (hlC :
                        Eq.{1}
                          (Matrix.vecMul.{0, 0, 0} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C)) 0)
                        (hzD :
                        Eq.{1}
                          (Matrix.mulVec.{0, 0, 0}
                            (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0}
                              (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} D))
                            zD)
                          0)
                        (hlD :
                        Eq.{1}
                          (Matrix.vecMul.{0, 0, 0} lD
                            (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0}
                              (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} D)))
                          0),
                        (∃ bC,
                            Eq.{1}
                              (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψC 1 1 ⋯) zC)
                                z)
                              ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bC)) ∧
                          (∃ bD,
                              Eq.{1}
                                (HSub.hSub.{0, 0, 0}
                                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψD 1 1 ⋯) zD) z)
                                ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bD)) ∧
                            (∀ (v : ι2 → K),
                                Eq.{1} (dotProduct.{0, 0} lC v)
                                  (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψC 2 2 ⋯) v))) ∧
                              (∀ (v : Fin (HAdd.hAdd.{0, 0, 0} m 1) → K),
                                  Eq.{1} (dotProduct.{0, 0} lD v)
                                    (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψD 2 2 ⋯) v))) ∧
                                ∃ H u,
                                  ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord.{0} D zD lD u ∧
                                    QuasiIso.{0, 1, 0}
                                        (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap
                                            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{0,
                                                0, 0, 0, 0, 0, 0, 0, 0}
                                              H))) ∧
                                      Ne.{1}
                                          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor.{0,
                                              0, 0, 0, 0, 0, 0, 0, 0}
                                            H hzC hlC hzD hlD σC
                                            (ZInQ.Contrib.CloudB3RC53.Torsion.σ₀ (HAdd.hAdd.{0, 0, 0} m 1)))
                                          0 ∧
                                        Eq.{1}
                                          (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} C zC lC hzC hlC σC)
                                          (HMul.hMul.{0, 0, 0}
                                            (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor.{0,
                                                0, 0, 0, 0, 0, 0, 0, 0}
                                              H hzC hlC hzD hlD σC
                                              (ZInQ.Contrib.CloudB3RC53.Torsion.σ₀ (HAdd.hAdd.{0, 0, 0} m 1)))
                                            u)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [952312, 1174052), lines 12550–15273.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_actual_adjugate_coordinate' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.lift_conjugate_actual_class`

support theorem; source line 1307.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.lift_conjugate_actual_class : ∀ {R : Type} [inst : Field.{0} R]
  {A B T : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} R}
  (j : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} A T)
  (c : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} B T),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} j) →
    ∀ (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} B 1)),
      Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} B 1 2 ⋯) z) 0 →
        ∃ zperp,
          Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} A 1 2 ⋯) zperp) 0 ∧
            ∃ b,
              Eq.{1}
                (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} j 1 1 ⋯) zperp)
                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} c 1 1 ⋯) z))
                ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} T 0 1 ⋯) b)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [1174212, 1227118), lines 15275–15909.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.lift_conjugate_actual_class' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.cup_actual_functional_closed`

support theorem; source line 1329.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.cup_actual_functional_closed : ∀ {R : Type}
  [inst : Field.{0} R] {D D' : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0} R}
  (P : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0} D D')
  (tr :
    LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R)
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      R),
  (∀
      (v :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 ⋯)
            v))
        0) →
    ∀
      (zperp :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} D)
            1)),
      Eq.{1}
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} D)
              1 2 ⋯)
            zperp)
          0 →
        ∀
          (v :
            ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} D') 1)),
          Eq.{1}
            ((ZInQ.Contrib.CloudB3RC53.CommonCoordinate.pairedFun.{0} P tr zperp)
              ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} D') 1 2 ⋯)
                v))
            0
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [1227272, 1288533), lines 15911–16653.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.cup_actual_functional_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualCupData`

abbrev; source line 1362.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualCupData : {R : Type} →
  [inst : Field.{0} R] →
    (N : Type) →
      [inst_1 : Field.{0} N] →
        [inst_2 : NumberField.{0} N] →
          (S₀ : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))) →
            {A B T : Type} →
              [inst_3 : AddCommGroup.{0} A] →
                [inst_4 : Module.{0, 0} R A] →
                  [inst_5 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) A] →
                    [inst_6 : SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R A] →
                      [inst_7 : TopologicalSpace.{0} A] →
                        [inst_8 : ContinuousAdd.{0} A] →
                          [inst_9 : ContinuousConstSMul.{0, 0} R A] →
                            [inst_10 : ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) A] →
                              [inst_11 : AddCommGroup.{0} B] →
                                [inst_12 : Module.{0, 0} R B] →
                                  [inst_13 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) B] →
                                    [inst_14 :
                                        SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R B] →
                                      [inst_15 : TopologicalSpace.{0} B] →
                                        [inst_16 : ContinuousAdd.{0} B] →
                                          [inst_17 : ContinuousConstSMul.{0, 0} R B] →
                                            [inst_18 :
                                                ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) B] →
                                              [inst_19 : AddCommGroup.{0} T] →
                                                [inst_20 : Module.{0, 0} R T] →
                                                  [inst_21 :
                                                      DistribMulAction.{0, 0}
                                                        (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) T] →
                                                    [inst_22 :
                                                        SMulCommClass.{0, 0, 0}
                                                          (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R T] →
                                                      [inst_23 : TopologicalSpace.{0} T] →
                                                        [inst_24 : ContinuousAdd.{0} T] →
                                                          [inst_25 : ContinuousConstSMul.{0, 0} R T] →
                                                            [inst_26 :
                                                                ContinuousSMul.{0, 0}
                                                                  (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) T] →
                                                              (β :
                                                                  LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R) A
                                                                    (LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R) B T)) →
                                                                (hβ :
                                                                    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀)
                                                                      (a : A) (b : B),
                                                                      Eq.{1}
                                                                        ((β (HSMul.hSMul.{0, 0, 0} g a))
                                                                          (HSMul.hSMul.{0, 0, 0} g b))
                                                                        (HSMul.hSMul.{0, 0, 0} g ((β a) b))) →
                                                                  (hβc : Continuous.{0, 0} fun p => (β p.1) p.2) →
                                                                    (Δperp :
                                                                        ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions
                                                                          N S₀ R A) →
                                                                      (Δ :
                                                                          ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions
                                                                            N S₀ R B) →
                                                                        ZInQ.Manuscript.RC.SelmerComplex.IsotropyData.{0}
                                                                            R
                                                                            (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀)
                                                                            (fun v =>
                                                                              ZInQ.Manuscript.RC.SelmerComplex.Gloc N
                                                                                ↑v)
                                                                            (fun v =>
                                                                              ZInQ.Manuscript.RC.SelmerComplex.locMap N
                                                                                S₀ ↑v)
                                                                            β hβ hβc Δperp Δ →
                                                                          ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
                                                                            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData
                                                                              N S₀ R A Δperp)
                                                                            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData
                                                                              N S₀ R B Δ)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [1288688, 1468299), lines 16655–18372.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualCupData' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_genuine_paired_model_comparison`

support theorem; source line 1371.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_genuine_paired_model_comparison : ∀ {R : Type}
  [inst : Field.{0} R] (N : Type) [inst_1 : Field.{0} N] [inst_2 : NumberField.{0} N]
  (S₀ : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))) {A B T : Type}
  [inst_3 : AddCommGroup.{0} A] [inst_4 : Module.{0, 0} R A]
  [inst_5 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) A]
  [inst_6 : SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R A] [inst_7 : TopologicalSpace.{0} A]
  [inst_8 : ContinuousAdd.{0} A] [inst_9 : ContinuousConstSMul.{0, 0} R A]
  [inst_10 : ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) A] [inst_11 : AddCommGroup.{0} B]
  [inst_12 : Module.{0, 0} R B] [inst_13 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) B]
  [inst_14 : SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R B] [inst_15 : TopologicalSpace.{0} B]
  [inst_16 : ContinuousAdd.{0} B] [inst_17 : ContinuousConstSMul.{0, 0} R B]
  [inst_18 : ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) B] [inst_19 : AddCommGroup.{0} T]
  [inst_20 : Module.{0, 0} R T] [inst_21 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) T]
  [inst_22 : SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R T] [inst_23 : TopologicalSpace.{0} T]
  [inst_24 : ContinuousAdd.{0} T] [inst_25 : ContinuousConstSMul.{0, 0} R T]
  [inst_26 : ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) T]
  (β : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R) A (LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R) B T))
  (hβ :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) (a : A) (b : B),
      Eq.{1} ((β (HSMul.hSMul.{0, 0, 0} g a)) (HSMul.hSMul.{0, 0, 0} g b)) (HSMul.hSMul.{0, 0, 0} g ((β a) b)))
  (hβc : Continuous.{0, 0} fun p => (β p.1) p.2)
  (Δperp Δconj : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions N S₀ R A)
  (Δ : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions N S₀ R B)
  (I :
    ZInQ.Manuscript.RC.SelmerComplex.IsotropyData.{0} R (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀)
      (fun v => ZInQ.Manuscript.RC.SelmerComplex.Gloc N ↑v) (fun v => ZInQ.Manuscript.RC.SelmerComplex.locMap N S₀ ↑v) β
      hβ hβc Δperp Δ)
  (j :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
        (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R A Δperp))
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
        (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R A Δconj)))
  (c :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R B Δ))
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
        (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R A Δconj))),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} j) →
    ∀
      (z :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R B Δ))
            1)),
      Eq.{1}
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
                (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R B Δ))
              1 2 ⋯)
            z)
          0 →
        ∀
          (tr :
            LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R)
              (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualCupData N S₀ β hβ hβc Δperp Δ I)))
                  3))
              R),
          (∀
              (v :
                ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualCupData N S₀ β hβ hβc Δperp Δ
                          I)))
                    2)),
              Eq.{1}
                (tr
                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} ⋯))
                      2 3 ⋯)
                    v))
                0) →
            ∀ {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_27 : Fintype.{0} ι0] [inst_28 : Fintype.{0} ι1]
              [inst_29 : Fintype.{0} ι2] [inst_30 : Fintype.{0} ι3] [inst_31 : Fintype.{0} ι0']
              [inst_32 : Fintype.{0} ι1'], ⋯
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [1468439, 1862142), lines 18374–22890.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_genuine_paired_model_comparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.rightPairedFun`

def; source line 1412.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.rightPairedFun : {R : Type} →
  [inst : Field.{0} R] →
    {D D' : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0} R} →
      (P : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0} D D') →
        LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R)
            (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
                3))
            R →
          ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} D')
                1) →
            LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R)
              (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} D) 2))
              R
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [1862307, 1869728), lines 22892–22983.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.rightPairedFun' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.rightPairedFun_closed`

support theorem; source line 1418.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.rightPairedFun_closed : ∀ {R : Type} [inst : Field.{0} R]
  {D D' : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{0} R}
  (P : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0} D D')
  (tr :
    LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R)
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
          3))
      R),
  (∀
      (v :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
            2)),
      Eq.{1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} P))
              2 3 ⋯)
            v))
        0) →
    ∀
      (zperp :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} D')
            1)),
      Eq.{1}
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} D')
              1 2 ⋯)
            zperp)
          0 →
        ∀
          (v :
            ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} D) 1)),
          Eq.{1}
            ((ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.rightPairedFun P tr zperp)
              ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} D) 1 2 ⋯)
                v))
            0
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [1869869, 1931131), lines 22985–23727.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.rightPairedFun_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualRightCupData`

abbrev; source line 1449.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualRightCupData : {R : Type} →
  [inst : Field.{0} R] →
    (N : Type) →
      [inst_1 : Field.{0} N] →
        [inst_2 : NumberField.{0} N] →
          (S₀ : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))) →
            {A B T : Type} →
              [inst_3 : AddCommGroup.{0} A] →
                [inst_4 : Module.{0, 0} R A] →
                  [inst_5 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) A] →
                    [inst_6 : SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R A] →
                      [inst_7 : TopologicalSpace.{0} A] →
                        [inst_8 : ContinuousAdd.{0} A] →
                          [inst_9 : ContinuousConstSMul.{0, 0} R A] →
                            [inst_10 : ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) A] →
                              [inst_11 : AddCommGroup.{0} B] →
                                [inst_12 : Module.{0, 0} R B] →
                                  [inst_13 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) B] →
                                    [inst_14 :
                                        SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R B] →
                                      [inst_15 : TopologicalSpace.{0} B] →
                                        [inst_16 : ContinuousAdd.{0} B] →
                                          [inst_17 : ContinuousConstSMul.{0, 0} R B] →
                                            [inst_18 :
                                                ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) B] →
                                              [inst_19 : AddCommGroup.{0} T] →
                                                [inst_20 : Module.{0, 0} R T] →
                                                  [inst_21 :
                                                      DistribMulAction.{0, 0}
                                                        (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) T] →
                                                    [inst_22 :
                                                        SMulCommClass.{0, 0, 0}
                                                          (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R T] →
                                                      [inst_23 : TopologicalSpace.{0} T] →
                                                        [inst_24 : ContinuousAdd.{0} T] →
                                                          [inst_25 : ContinuousConstSMul.{0, 0} R T] →
                                                            [inst_26 :
                                                                ContinuousSMul.{0, 0}
                                                                  (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) T] →
                                                              (β :
                                                                  LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R) A
                                                                    (LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R) B T)) →
                                                                (hβ :
                                                                    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀)
                                                                      (a : A) (b : B),
                                                                      Eq.{1}
                                                                        ((β (HSMul.hSMul.{0, 0, 0} g a))
                                                                          (HSMul.hSMul.{0, 0, 0} g b))
                                                                        (HSMul.hSMul.{0, 0, 0} g ((β a) b))) →
                                                                  (hβc : Continuous.{0, 0} fun p => (β p.1) p.2) →
                                                                    (Δ :
                                                                        ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions
                                                                          N S₀ R A) →
                                                                      (Δperp :
                                                                          ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions
                                                                            N S₀ R B) →
                                                                        ZInQ.Manuscript.RC.SelmerComplex.IsotropyData.{0}
                                                                            R
                                                                            (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀)
                                                                            (fun v =>
                                                                              ZInQ.Manuscript.RC.SelmerComplex.Gloc N
                                                                                ↑v)
                                                                            (fun v =>
                                                                              ZInQ.Manuscript.RC.SelmerComplex.locMap N
                                                                                S₀ ↑v)
                                                                            β hβ hβc Δ Δperp →
                                                                          ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{0}
                                                                            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData
                                                                              N S₀ R A Δ)
                                                                            (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData
                                                                              N S₀ R B Δperp)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [1931279, 2110895), lines 23729–25446.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualRightCupData' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_genuine_retained_PD_comparison`

support theorem; source line 1458.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_genuine_retained_PD_comparison : ∀ {R : Type}
  [inst : Field.{0} R] (N : Type) [inst_1 : Field.{0} N] [inst_2 : NumberField.{0} N]
  (S₀ : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))) {A B T : Type}
  [inst_3 : AddCommGroup.{0} A] [inst_4 : Module.{0, 0} R A]
  [inst_5 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) A]
  [inst_6 : SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R A] [inst_7 : TopologicalSpace.{0} A]
  [inst_8 : ContinuousAdd.{0} A] [inst_9 : ContinuousConstSMul.{0, 0} R A]
  [inst_10 : ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) A] [inst_11 : AddCommGroup.{0} B]
  [inst_12 : Module.{0, 0} R B] [inst_13 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) B]
  [inst_14 : SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R B] [inst_15 : TopologicalSpace.{0} B]
  [inst_16 : ContinuousAdd.{0} B] [inst_17 : ContinuousConstSMul.{0, 0} R B]
  [inst_18 : ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) B] [inst_19 : AddCommGroup.{0} T]
  [inst_20 : Module.{0, 0} R T] [inst_21 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) T]
  [inst_22 : SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R T] [inst_23 : TopologicalSpace.{0} T]
  [inst_24 : ContinuousAdd.{0} T] [inst_25 : ContinuousConstSMul.{0, 0} R T]
  [inst_26 : ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) T]
  (β : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R) A (LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R) B T))
  (hβ :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) (a : A) (b : B),
      Eq.{1} ((β (HSMul.hSMul.{0, 0, 0} g a)) (HSMul.hSMul.{0, 0, 0} g b)) (HSMul.hSMul.{0, 0, 0} g ((β a) b)))
  (hβc : Continuous.{0, 0} fun p => (β p.1) p.2) (Δ : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions N S₀ R A)
  (Δperp Δconj : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions N S₀ R B)
  (I :
    ZInQ.Manuscript.RC.SelmerComplex.IsotropyData.{0} R (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀)
      (fun v => ZInQ.Manuscript.RC.SelmerComplex.Gloc N ↑v) (fun v => ZInQ.Manuscript.RC.SelmerComplex.locMap N S₀ ↑v) β
      hβ hβc Δ Δperp)
  (j :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
        (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R B Δperp))
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
        (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R B Δconj)))
  (c :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R A Δ))
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
        (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R B Δconj))),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} j) →
    ∀
      (z :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R A Δ))
            1)),
      Eq.{1}
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
                (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R A Δ))
              1 2 ⋯)
            z)
          0 →
        ∀
          (tr :
            LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R)
              (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualRightCupData N S₀ β hβ hβc Δ Δperp
                        I)))
                  3))
              R),
          (∀
              (v :
                ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualRightCupData N S₀ β hβ hβc Δ
                          Δperp I)))
                    2)),
              Eq.{1}
                (tr
                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} ⋯))
                      2 3 ⋯)
                    v))
                0) →
            ∀ {ι0 ι1 ι2 ι3 ι0' ι1' ι2' ι3' : Type} [inst_27 : Fintype.{0} ι0] [inst_28 : Fintype.{0} ι1]
              [inst_29 : Fintype.{0} ι2] [inst_30 : Fintype.{0} ι3] [inst_31 : Fintype.{0} ι0']
              [inst_32 : Fintype.{0} ι1'], ⋯
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [2111040, 2604531), lines 25448–31051.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_genuine_retained_PD_comparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_genuine_adjugate_PD_coordinate`

support theorem; source line 1511.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_genuine_adjugate_PD_coordinate : ∀ {R : Type}
  [inst : Field.{0} R] (N : Type) [inst_1 : Field.{0} N] [inst_2 : NumberField.{0} N]
  (S₀ : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))) {A B T : Type}
  [inst_3 : AddCommGroup.{0} A] [inst_4 : Module.{0, 0} R A]
  [inst_5 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) A]
  [inst_6 : SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R A] [inst_7 : TopologicalSpace.{0} A]
  [inst_8 : ContinuousAdd.{0} A] [inst_9 : ContinuousConstSMul.{0, 0} R A]
  [inst_10 : ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) A] [inst_11 : AddCommGroup.{0} B]
  [inst_12 : Module.{0, 0} R B] [inst_13 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) B]
  [inst_14 : SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R B] [inst_15 : TopologicalSpace.{0} B]
  [inst_16 : ContinuousAdd.{0} B] [inst_17 : ContinuousConstSMul.{0, 0} R B]
  [inst_18 : ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) B] [inst_19 : AddCommGroup.{0} T]
  [inst_20 : Module.{0, 0} R T] [inst_21 : DistribMulAction.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) T]
  [inst_22 : SMulCommClass.{0, 0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) R T] [inst_23 : TopologicalSpace.{0} T]
  [inst_24 : ContinuousAdd.{0} T] [inst_25 : ContinuousConstSMul.{0, 0} R T]
  [inst_26 : ContinuousSMul.{0, 0} (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) T]
  (β : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R) A (LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R) B T))
  (hβ :
    ∀ (g : ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀) (a : A) (b : B),
      Eq.{1} ((β (HSMul.hSMul.{0, 0, 0} g a)) (HSMul.hSMul.{0, 0, 0} g b)) (HSMul.hSMul.{0, 0, 0} g ((β a) b)))
  (hβc : Continuous.{0, 0} fun p => (β p.1) p.2) (Δ : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions N S₀ R A)
  (Δperp Δconj : ZInQ.Manuscript.RC.SelmerComplex.GaloisLocalConditions N S₀ R B)
  (I :
    ZInQ.Manuscript.RC.SelmerComplex.IsotropyData.{0} R (ZInQ.Manuscript.RC.SelmerComplex.GKS N S₀)
      (fun v => ZInQ.Manuscript.RC.SelmerComplex.Gloc N ↑v) (fun v => ZInQ.Manuscript.RC.SelmerComplex.locMap N S₀ ↑v) β
      hβ hβc Δ Δperp)
  (j :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
        (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R B Δperp))
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
        (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R B Δconj)))
  (c :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0} (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R A Δ))
      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
        (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R B Δconj))),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} j) →
    ∀
      (z :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
              (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R A Δ))
            1)),
      Eq.{1}
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{0}
                (ZInQ.Manuscript.RC.SelmerComplex.galoisSelData N S₀ R A Δ))
              1 2 ⋯)
            z)
          0 →
        ∀
          (tr :
            LinearMap.{0, 0, 0, 0} (RingHom.id.{0} R)
              (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualRightCupData N S₀ β hβ hβc Δ Δperp
                        I)))
                  3))
              R),
          (∀
              (v :
                ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                    (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0}
                        (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.actualRightCupData N S₀ β hβ hβc Δ
                          Δperp I)))
                    2)),
              Eq.{1}
                (tr
                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                      (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{0}
                        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{0} ⋯))
                      2 3 ⋯)
                    v))
                0) →
            ∀ {ι0 ι1 ι2 ι3 : Type} [inst_27 : Fintype.{0} ι0] [inst_28 : Fintype.{0} ι1] [inst_29 : Fintype.{0} ι2]
              [inst_30 : Fintype.{0} ι3] [inst_31 : DecidableEq.{1} ι0] [inst_32 : DecidableEq.{1} ι1], ⋯
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [2604695, 3176454), lines 31053–37617.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.exists_genuine_adjugate_PD_coordinate' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_relaxation_endpoint`

support theorem; source line 1592.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_relaxation_endpoint : ∀ {ℓ : ℕ}
  {Dd : ZInQ.Manuscript.RC.RCData ℓ} {F : ZInQ.Manuscript.RC.Family} {x : ZInQ.Manuscript.RC.Addr F.b}
  (T : ZInQ.Contrib.CloudB3RC53.CommonCoordinate.CommonCoordinateTrianglesN Dd F x),
  Finset.Nonempty.{0} T.U → ∃ n D z w, ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w T.urel
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [3176618, 3182391), lines 37619–37705.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_relaxation_endpoint' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_endpoint_on_carrier`

support theorem; source line 1607.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_endpoint_on_carrier : ∀ {A : Type}
  [inst : CommRing.{0} A] (U : Finset.{0} ℕ),
  Finset.Nonempty.{0} U →
    ∀ (F : ℕ → Matrix.{0, 0, 0} (Fin 2) (Fin 2) A) (q qi a z zi eps : ℕ → A) (u : Finset.{0} ℕ → A)
      (unitR unitP : A → Prop),
      (∀ T ⊆ U,
          ∀ (p : ℕ),
            Membership.mem.{0, 0} U p →
              p ∉ T →
                ZInQ.Contrib.CloudB3RC53.CommonCoordinate.ActualStep (F p) (q p) (qi p) (a p) (z p) (zi p) (u T)
                  (u (Insert.insert.{0, 0} p T)) (eps p) unitR unitP) →
        ∃ n D zc wc, ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D zc wc (u U)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [3182552, 3188072), lines 37707–37803.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_endpoint_on_carrier' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_scalar_common_fraction`

support theorem; source line 1629.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_scalar_common_fraction : ∀ {R A K : Type}
  [inst : CommRing.{0} R] [inst_1 : CommRing.{0} A] [inst_2 : Field.{0} K] {ι : Type} [inst_3 : Fintype.{0} ι]
  [inst_4 : DecidableEq.{1} ι] (f : RingHom.{0, 0} R A),
  Function.Injective.{1, 1} ⇑f →
    ∀ (g : RingHom.{0, 0} R K),
      Function.Injective.{1, 1} ⇑g →
        ∀ (D : Matrix.{0, 0, 0} ι ι R) (z w : ι → R) (u : A),
          ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑f)
              (Function.comp.{1, 1, 1} (⇑f) z) (Function.comp.{1, 1, 1} (⇑f) w) u →
            Ne.{1} (Matrix.adjugate.{0, 0} D) 0 →
              ∃ num den,
                Ne.{1} den 0 ∧
                  Eq.{1} (HMul.hMul.{0, 0, 0} (f den) u) (f num) ∧
                    ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑g)
                      (Function.comp.{1, 1, 1} (⇑g) z) (Function.comp.{1, 1, 1} (⇑g) w)
                      (HDiv.hDiv.{0, 0, 0} (g num) (g den))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [3188233, 3200269), lines 37805–38020.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_scalar_common_fraction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_scalar_unique`

support theorem; source line 1681.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_scalar_unique : ∀ {K : Type}
  [inst : Field.{0} K] {ι : Type} [inst_1 : Fintype.{0} ι] [inst_2 : DecidableEq.{1} ι] (D : Matrix.{0, 0, 0} ι ι K)
  (z w : ι → K) (u v : K),
  Ne.{1} (Matrix.adjugate.{0, 0} D) 0 →
    ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w u →
      ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D z w v → Eq.{1} u v
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [3200433, 3201476), lines 38022–38041.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_scalar_unique' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_scalar_from_corrected_representative`

support theorem; source line 1694.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_scalar_from_corrected_representative : ∀
  {R A K : Type} [inst : CommRing.{0} R] [inst_1 : CommRing.{0} A] [inst_2 : Field.{0} K] (f : RingHom.{0, 0} R A),
  Function.Injective.{1, 1} ⇑f →
    ∀ (g : RingHom.{0, 0} R K),
      Function.Injective.{1, 1} ⇑g →
        ∀ (uA : A) (uK correctedK : K) (eta num den correctedNum correctedDen : R),
          Ne.{1} den 0 →
            Ne.{1} correctedDen 0 →
              Eq.{1} (HMul.hMul.{0, 0, 0} (f den) uA) (f num) →
                Eq.{1} (HMul.hMul.{0, 0, 0} (f correctedDen) (HMul.hMul.{0, 0, 0} (f eta) uA)) (f correctedNum) →
                  Eq.{1} (HMul.hMul.{0, 0, 0} (g correctedDen) correctedK) (g correctedNum) →
                    Eq.{1} correctedK (HMul.hMul.{0, 0, 0} (g eta) uK) →
                      Ne.{1} (g eta) 0 → Eq.{1} uK (HDiv.hDiv.{0, 0, 0} (g num) (g den))
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [3201631, 3213845), lines 38043–38258.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointScalarSupport.existing_scalar_from_corrected_representative' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.endpoint_row_of_values`

new theorem; source line 1737.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.endpoint_row_of_values : ∀ {K : Type} [inst : Field.{0} K] {m : ℕ}
  (D : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) K)
  (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K)
  (ψ :
    ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} D))
      S)
  (L : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2)) K)
  (w : Fin (HAdd.hAdd.{0, 0, 0} m 1) → K),
  (∀ (v : Fin (HAdd.hAdd.{0, 0, 0} m 1) → K),
      Eq.{1} (dotProduct.{0, 0} w v) (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψ 2 2 ⋯) v))) →
    Eq.{1} w
      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} D)
        S ψ L)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [3214023, 3245786), lines 38260–38710.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.endpoint_row_of_values' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.existing_endpoint_original_basis`

new theorem; source line 1749.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.existing_endpoint_original_basis : ∀ {K : Type} [inst : Field.{0} K]
  {ι0 ι1 ι2 ι3 : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1] [inst_3 : Fintype.{0} ι2]
  [inst_4 : Fintype.{0} ι3] [inst_5 : DecidableEq.{1} ι0] [inst_6 : DecidableEq.{1} ι1] [inst_7 : DecidableEq.{1} ι2]
  [inst_8 : DecidableEq.{1} ι3] {m : ℕ} (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3)
  (D : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) K),
  Ne.{1} (Matrix.adjugate.{0, 0} D) 0 →
    ∀ (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K)
      (ψC :
        ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S)
      (ψD :
        ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx
            (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} D))
          S),
      QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψC) →
        QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψD) →
          ∀ (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)) (zC : ι1 → K)
            (zD wD : Fin (HAdd.hAdd.{0, 0, 0} m 1) → K)
            (hzC : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0)
            (hzD : Eq.{1} (Matrix.mulVec.{0, 0, 0} D zD) 0)
            (bC bD : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 0)),
            Eq.{1} (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψC 1 1 ⋯) zC) z)
                ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bC) →
              Eq.{1} (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψD 1 1 ⋯) zD) z)
                  ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bD) →
                ∀
                  (L :
                    LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K)
                      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2)) K)
                  (hL :
                    ∀ (v : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)),
                      Eq.{1} (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 1 2 ⋯) v)) 0),
                  (∀ (v : Fin (HAdd.hAdd.{0, 0, 0} m 1) → K),
                      Eq.{1} (dotProduct.{0, 0} wD v)
                        (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψD 2 2 ⋯) v))) →
                    ∀ (urel : K),
                      ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} D zD wD urel →
                        ∀ (σC : Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0 Unit) ι2) (Sum.{0, 0} ι1 (Sum.{0, 0} ι3 Unit))),
                          ∃ (hlD : Eq.{1} (Matrix.vecMul.{0, 0, 0} wD D) 0),
                            ∃ H,
                              QuasiIso.{0, 1, 0}
                                  (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.f.{0,
                                          0, 0, 0, 0, 0, 0, 0, 0}
                                        H))) ∧
                                Ne.{1}
                                    (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor.{0,
                                        0, 0, 0, 0, 0, 0, 0, 0}
                                      H hzC ⋯ hzD hlD σC
                                      (ZInQ.Contrib.CloudB3RC53.Torsion.σ₀ (HAdd.hAdd.{0, 0, 0} m 1)))
                                    0 ∧
                                  Eq.{1}
                                    (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} C zC
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.modelRow C S ψC L) hzC ⋯
                                      σC)
                                    (HMul.hMul.{0, 0, 0}
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor.{0,
                                          0, 0, 0, 0, 0, 0, 0, 0}
                                        H hzC ⋯ hzD hlD σC
                                        (ZInQ.Contrib.CloudB3RC53.Torsion.σ₀ (HAdd.hAdd.{0, 0, 0} m 1)))
                                      urel)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [3245928, 3389548), lines 38712–40738.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.existing_endpoint_original_basis' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.existing_endpoint_two_realizations`

new theorem; source line 1790.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.existing_endpoint_two_realizations : ∀ {K : Type} [inst : Field.{0} K]
  {ι0 ι1 ι2 ι3 : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1] [inst_3 : Fintype.{0} ι2]
  [inst_4 : Fintype.{0} ι3] [inst_5 : DecidableEq.{1} ι0] [inst_6 : DecidableEq.{1} ι1] [inst_7 : DecidableEq.{1} ι2]
  [inst_8 : DecidableEq.{1} ι3] {R A : Type} [inst_9 : CommRing.{0} R] [inst_10 : CommRing.{0} A] {m : ℕ}
  (f : RingHom.{0, 0} R A),
  Function.Injective.{1, 1} ⇑f →
    ∀ (g : RingHom.{0, 0} R K),
      Function.Injective.{1, 1} ⇑g →
        ∀ (D : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) R)
          (zd wd : Fin (HAdd.hAdd.{0, 0, 0} m 1) → R) (urel : A),
          ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑f)
              (Function.comp.{1, 1, 1} (⇑f) zd) (Function.comp.{1, 1, 1} (⇑f) wd) urel →
            Ne.{1} (Matrix.adjugate.{0, 0} D) 0 →
              ∀ (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3)
                (S : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} K)
                (ψC :
                  ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                    (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx C) S)
                (ψD :
                  ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0}
                    (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadCx
                      (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} (Matrix.map.{0, 0, 0, 0} D ⇑g)))
                    S),
                QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψC) →
                  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} ψD) →
                    ∀ (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)) (zC : ι1 → K)
                      (hzC :
                        Eq.{1}
                          (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zC) 0)
                      (hzd :
                        Eq.{1}
                          (Matrix.mulVec.{0, 0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑g) (Function.comp.{1, 1, 1} (⇑g) zd)) 0)
                      (bC bD : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 0)),
                      Eq.{1}
                          (HSub.hSub.{0, 0, 0} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψC 1 1 ⋯) zC) z)
                          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bC) →
                        Eq.{1}
                            (HSub.hSub.{0, 0, 0}
                              ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψD 1 1 ⋯)
                                (Function.comp.{1, 1, 1} (⇑g) zd))
                              z)
                            ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 0 1 ⋯) bD) →
                          ∀
                            (L :
                              LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K)
                                (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 2)) K)
                            (hL :
                              ∀ (v : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} S 1)),
                                Eq.{1} (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} S 1 2 ⋯) v)) 0),
                            (∀ (v : Fin (HAdd.hAdd.{0, 0, 0} m 1) → K),
                                Eq.{1} (dotProduct.{0, 0} (Function.comp.{1, 1, 1} (⇑g) wd) v)
                                  (L ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} ψD 2 2 ⋯) v))) →
                              ∀
                                (σC :
                                  Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0 Unit) ι2)
                                    (Sum.{0, 0} ι1 (Sum.{0, 0} ι3 Unit))),
                                ∃ num den,
                                  ∃ (hwK :
                                    Eq.{1}
                                      (Matrix.vecMul.{0, 0, 0} (Function.comp.{1, 1, 1} (⇑g) wd)
                                        (Matrix.map.{0, 0, 0, 0} D ⇑g))
                                      0),
                                    ∃ H,
                                      Ne.{1} den 0 ∧
                                        Eq.{1} (HMul.hMul.{0, 0, 0} (f den) urel) (f num) ∧
                                          QuasiIso.{0, 1, 0}
                                              (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
                                                (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.quadMap ⋯)) ∧
                                            Ne.{1}
                                                (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.retainedFactor.{0,
                                                    0, 0, 0, 0, 0, 0, 0, 0}
                                                  H hzC ⋯ hzd hwK σC
                                                  (ZInQ.Contrib.CloudB3RC53.Torsion.σ₀ (HAdd.hAdd.{0, 0, 0} m 1)))
                                                0 ∧
                                              Eq.{1}
                                                (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} C zC ⋯ hzC ⋯
                                                  σC)
                                                (HMul.hMul.{0, 0, 0} ⋯ ⋯)
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [3389700, 3619984), lines 40740–44075.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.existing_endpoint_two_realizations' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.original_coordinate_eq_existing_relaxed`

new theorem; source line 1832.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.original_coordinate_eq_existing_relaxed : ∀ {K : Type}
  [inst : Field.{0} K] {ι0 ι1 ι2 ι3 : Type} [inst_1 : Fintype.{0} ι0] [inst_2 : Fintype.{0} ι1]
  [inst_3 : Fintype.{0} ι2] [inst_4 : Fintype.{0} ι3] [inst_5 : DecidableEq.{1} ι0] [inst_6 : DecidableEq.{1} ι1]
  [inst_7 : DecidableEq.{1} ι2] [inst_8 : DecidableEq.{1} ι3] {R A : Type} [inst_9 : CommRing.{0} R]
  [inst_10 : CommRing.{0} A] {m : ℕ} (f : RingHom.{0, 0} R A),
  Function.Injective.{1, 1} ⇑f →
    ∀ (g : RingHom.{0, 0} R K),
      Function.Injective.{1, 1} ⇑g →
        ∀ (D : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) R)
          (zd wd : Fin (HAdd.hAdd.{0, 0, 0} m 1) → R) (uA : A),
          ZInQ.Contrib.CloudB3RC53.CommonCoordinate.IsCoordOn.{0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑f)
              (Function.comp.{1, 1, 1} (⇑f) zd) (Function.comp.{1, 1, 1} (⇑f) wd) uA →
            Ne.{1} (Matrix.adjugate.{0, 0} D) 0 →
              ∀ (eta correctedNum correctedDen : R),
                Ne.{1} correctedDen 0 →
                  ∀ (correctedK urelK : K),
                    Eq.{1} (HMul.hMul.{0, 0, 0} (f correctedDen) (HMul.hMul.{0, 0, 0} (f eta) uA)) (f correctedNum) →
                      Eq.{1} (HMul.hMul.{0, 0, 0} (g correctedDen) correctedK) (g correctedNum) →
                        Eq.{1} correctedK (HMul.hMul.{0, 0, 0} (g eta) urelK) →
                          Ne.{1} (g eta) 0 →
                            ∀ (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} K ι0 ι1 ι2 ι3) (zc : ι1 → K)
                              (lc : ι2 → K)
                              (hzc :
                                Eq.{1}
                                  (Matrix.mulVec.{0, 0, 0}
                                    (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C) zc)
                                  0)
                              (hlc :
                                Eq.{1}
                                  (Matrix.vecMul.{0, 0, 0} lc
                                    (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C))
                                  0)
                              (hzd :
                                Eq.{1}
                                  (Matrix.mulVec.{0, 0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑g)
                                    (Function.comp.{1, 1, 1} (⇑g) zd))
                                  0)
                              (hwd :
                                Eq.{1}
                                  (Matrix.vecMul.{0, 0, 0} (Function.comp.{1, 1, 1} (⇑g) wd)
                                    (Matrix.map.{0, 0, 0, 0} D ⇑g))
                                  0)
                              (H :
                                ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.{0, 0, 0, 0,
                                    0, 0, 0, 0, 0}
                                  C (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} (Matrix.map.{0, 0, 0, 0} D ⇑g)) zc lc
                                  (Function.comp.{1, 1, 1} (⇑g) zd) (Function.comp.{1, 1, 1} (⇑g) wd))
                              (σC :
                                Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} ι0 Unit) ι2) (Sum.{0, 0} ι1 (Sum.{0, 0} ι3 Unit))),
                              Eq.{1}
                                  (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
                                    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{0, 0, 0, 0, 0}
                                      (ZInQ.Contrib.RC53Assist.CoordProvenance.EndpointSupport.HomotopyComparison.augMap.{0,
                                          0, 0, 0, 0, 0, 0, 0, 0}
                                        H hzc hlc hzd hwd))
                                    (Equiv.sumCongr.{0, 0, 0, 0}
                                      (ZInQ.Contrib.CloudB3RC53.Torsion.σ₀ (HAdd.hAdd.{0, 0, 0} m 1))
                                      (Equiv.symm.{1, 1} σC)))
                                  (HPow.hPow.{0, 0, 0} (-1) (Fintype.card.{0} (Sum.{0, 0} ι1 (Sum.{0, 0} ι3 Unit)))) →
                                Eq.{1} (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} C zc lc hzc hlc σC)
                                  urelK
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [3620138, 3673404), lines 44077–45066.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.original_coordinate_eq_existing_relaxed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.ExistingRelaxationRealizationG`

structure; source line 1894.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.ExistingRelaxationRealizationG : {N : Type} →
  [inst : Field.{0} N] →
    [inst_1 : NumberField.{0} N] →
      {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} →
        {hS : S ⊆ S'} →
          [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
            [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] →
              {dK hK cE tK ℓ : ℕ} →
                ZInQ.Manuscript.RC.RCData ℓ →
                  (F : ZInQ.Manuscript.RC.Family) →
                    (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G N S S' hS F.b dK hK cE tK) →
                      (z :
                          Sum.{0, 0} (Fin (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.m0.{0} M.D))
                              (Sum.{0, 0} Unit
                                (Fin (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.m1.{0} M.D))) →
                            MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                              (ZInQ.Manuscript.RC.Determinant.SignGroup F.b)) →
                        (lam :
                            Sum.{0, 0} (Sum.{0, 0} (Fin M.C.m1) (Sum.{0, 0} Unit (Fin M.C.m2))) M.C.N →
                              MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                (ZInQ.Manuscript.RC.Determinant.SignGroup F.b)) →
                          Eq.{1}
                              (Matrix.mulVec.{0, 0, 0}
                                (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d1.{0} M.D) z)
                              0 →
                            Eq.{1}
                                (Matrix.vecMul.{0, 0, 0} lam
                                  (Matrix.fromRows.{0, 0, 0, 0}
                                    (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO F.b)).X
                                    (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO F.b)).Y))
                                0 →
                              MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO
                                  (ZInQ.Manuscript.RC.Determinant.SignGroup F.b) →
                                (ZInQ.Manuscript.RC.Addr F.b → ℕ) →
                                  (ZInQ.Manuscript.RC.Addr F.b → ZInQ.Manuscript.RC.Determinant.Lam) →
                                    ZInQ.Manuscript.RC.Addr F.b → LaurentSeries.{0} ℚ_[2] → Type 1
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [3673563, 13636484), lines 45068–155103.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.ExistingRelaxationRealizationG' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.relIsKMG_of_existing_realizations`

new theorem; source line 1936.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.relIsKMG_of_existing_realizations : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {dK hK cE tK ℓ : ℕ}
  (Dd : ZInQ.Manuscript.RC.RCData ℓ) (F : ZInQ.Manuscript.RC.Family)
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G N S S' hS F.b dK hK cE tK)
  (z :
    Sum.{0, 0} (Fin (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.m0.{0} M.D))
        (Sum.{0, 0} Unit (Fin (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.m1.{0} M.D))) →
      MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b))
  (lam :
    Sum.{0, 0} (Sum.{0, 0} (Fin M.C.m1) (Sum.{0, 0} Unit (Fin M.C.m2))) M.C.N →
      MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b))
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d1.{0} M.D) z) 0)
  (hlam :
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0} lam
        (Matrix.fromRows.{0, 0, 0, 0} (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO F.b)).X
          (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO F.b)).Y))
      0)
  (eta : MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b))
  (urel : ZInQ.Manuscript.RC.Addr F.b → FractionRing.{0} ZInQ.Manuscript.RC.Determinant.OO),
  ZInQ.Contrib.CloudB3RC53.CoordLink.CorrectedIsEta Dd F eta urel →
    ∀ (urelL : ZInQ.Manuscript.RC.Addr F.b → LaurentSeries.{0} ℚ_[2]) (e₀ : ZInQ.Manuscript.RC.Addr F.b → ℕ)
      (g₀ : ZInQ.Manuscript.RC.Addr F.b → ZInQ.Manuscript.RC.Determinant.Lam),
      ZInQ.Manuscript.RC.Wiring.UTildeRep Dd F e₀ g₀ →
        (∀ (x : ZInQ.Manuscript.RC.Determinant.Addr F.b),
            Ne.{1}
                ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x))
                  (ZInQ.Manuscript.RC.Determinant.SmithBlocks.Δ.{0, 0} M.toIdentification.B))
                0 →
              Ne.{1} ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x)) eta) 0) →
          (∀ (x : ZInQ.Manuscript.RC.Determinant.Addr F.b),
              Ne.{1}
                  ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x))
                    (ZInQ.Manuscript.RC.Determinant.SmithBlocks.Δ.{0, 0} M.toIdentification.B))
                  0 →
                Nonempty.{2}
                  (ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.ExistingRelaxationRealizationG Dd F M z lam
                    hz hlam eta e₀ g₀ x (urelL x))) →
            ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M urel z lam hz hlam
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [13636643, 20145407), lines 155105–242468.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.relIsKMG_of_existing_realizations' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.origCoordLink_of_existing_realizations`

new theorem; source line 1966.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.origCoordLink_of_existing_realizations : ∀ {N : Type}
  [inst : Field.{0} N] [inst_1 : NumberField.{0} N]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} N))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces N S S')] {dK hK cE tK ℓ : ℕ}
  (Dd : ZInQ.Manuscript.RC.RCData ℓ) (F : ZInQ.Manuscript.RC.Family)
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G N S S' hS F.b dK hK cE tK)
  (z :
    Sum.{0, 0} (Fin (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.m0.{0} M.D))
        (Sum.{0, 0} Unit (Fin (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.m1.{0} M.D))) →
      MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b))
  (lam :
    Sum.{0, 0} (Sum.{0, 0} (Fin M.C.m1) (Sum.{0, 0} Unit (Fin M.C.m2))) M.C.N →
      MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b))
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d1.{0} M.D) z) 0)
  (hlam :
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0} lam
        (Matrix.fromRows.{0, 0, 0, 0} (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO F.b)).X
          (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO F.b)).Y))
      0)
  (eta : MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b))
  (urel : ZInQ.Manuscript.RC.Addr F.b → FractionRing.{0} ZInQ.Manuscript.RC.Determinant.OO),
  ZInQ.Contrib.CloudB3RC53.CoordLink.CorrectedIsEta Dd F eta urel →
    ∀ (urelL : ZInQ.Manuscript.RC.Addr F.b → LaurentSeries.{0} ℚ_[2]) (e₀ : ZInQ.Manuscript.RC.Addr F.b → ℕ)
      (g₀ : ZInQ.Manuscript.RC.Addr F.b → ZInQ.Manuscript.RC.Determinant.Lam),
      ZInQ.Manuscript.RC.Wiring.UTildeRep Dd F e₀ g₀ →
        (∀ (x : ZInQ.Manuscript.RC.Determinant.Addr F.b),
            Ne.{1}
                ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x))
                  (ZInQ.Manuscript.RC.Determinant.SmithBlocks.Δ.{0, 0} M.toIdentification.B))
                0 →
              Ne.{1} ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x)) eta) 0) →
          (∀ (x : ZInQ.Manuscript.RC.Determinant.Addr F.b),
              Ne.{1}
                  ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x))
                    (ZInQ.Manuscript.RC.Determinant.SmithBlocks.Δ.{0, 0} M.toIdentification.B))
                  0 →
                Nonempty.{2}
                  (ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.ExistingRelaxationRealizationG Dd F M z lam
                    hz hlam eta e₀ g₀ x (urelL x))) →
            ZInQ.Manuscript.RC.Wiring.OrigCoordLink Dd F M z lam hz hlam eta
```

Exact kernel type: decompress `EndpointComparison.exact.txt.gz` to `EndpointComparison.exact.txt`; bytes [20145569, 26654306), lines 242470–329832.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint.Clearing.origCoordLink_of_existing_realizations' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

# FullModelAdapter.lean

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex`

structure; source line 70.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex : (S : Type) → [CommRing.{0} S] → Type 1
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [0, 121), lines 1–2.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.D1`

abbrev; source line 96.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.D1 : {S : Type} →
  [inst : CommRing.{0} S] → ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S → Type
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [267, 498), lines 4–8.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.D1' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.D2`

abbrev; source line 97.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.D2 : {S : Type} →
  [inst : CommRing.{0} S] → ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S → Type
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [647, 878), lines 10–14.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.D2' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.Pc0_QY`

support theorem; source line 99.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.Pc0_QY : ∀ {S : Type}
  [inst : CommRing.{0} S] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S),
  Eq.{1} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} C.P C.c0) (HMul.hMul.{0, 0, 0} C.Q C.Y)) 0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [1027, 10605), lines 16–141.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.Pc0_QY' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.Tc0_BY`

support theorem; source line 104.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.Tc0_BY : ∀ {S : Type}
  [inst : CommRing.{0} S] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S),
  Eq.{1} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} C.T C.c0) (HMul.hMul.{0, 0, 0} C.B C.Y)) 0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [10758, 17837), lines 143–226.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.Tc0_BY' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.UP_VT`

support theorem; source line 109.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.UP_VT : ∀ {S : Type}
  [inst : CommRing.{0} S] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S),
  Eq.{1} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} C.U C.P) (HMul.hMul.{0, 0, 0} C.V C.T)) 0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [17990, 27656), lines 228–362.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.UP_VT' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.UQ_VB`

support theorem; source line 114.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.UQ_VB : ∀ {S : Type}
  [inst : CommRing.{0} S] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S),
  Eq.{1} (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} C.U C.Q) (HMul.hMul.{0, 0, 0} C.V C.B)) 0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [27808, 34955), lines 364–454.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.UQ_VB' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.Y_eq`

support theorem; source line 121.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.Y_eq : ∀ {S : Type} [inst : CommRing.{0} S]
  {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S},
  IsUnit.{0} (Matrix.det.{0, 0} C.B) →
    Eq.{1} C.Y (Neg.neg.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} (Inv.inv.{0} C.B) C.T) C.c0))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [35107, 42433), lines 456–544.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.Y_eq' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.V_eq`

support theorem; source line 128.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.V_eq : ∀ {S : Type} [inst : CommRing.{0} S]
  {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S},
  IsUnit.{0} (Matrix.det.{0, 0} C.B) →
    Eq.{1} C.V (Neg.neg.{0} (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} C.U C.Q) (Inv.inv.{0} C.B)))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [42584, 49487), lines 546–631.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.V_eq' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancel`

abbrev; source line 139.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancel : {S : Type} →
  [inst : CommRing.{0} S] →
    (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S) →
      IsUnit.{0} (Matrix.det.{0, 0} C.B) → ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.{0} S
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [49638, 50551), lines 633–646.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancel' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.idx`

def; source line 162.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.idx : {S : Type} →
  [inst : CommRing.{0} S] → ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S → ℤ → Type
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [50704, 50944), lines 648–652.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.idx' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.ddL`

def; source line 170.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.ddL : {S : Type} →
  [inst : CommRing.{0} S] →
    (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S) →
      (i : ℤ) → LinearMap.{0, 0, 0, 0} (RingHom.id.{0} S) (C.idx i → S) (C.idx (HAdd.hAdd.{0, 0, 0} i 1) → S)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [51094, 54710), lines 654–701.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.ddL' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.ddL_ddL`

support theorem; source line 176.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.ddL_ddL : ∀ {S : Type}
  [inst : CommRing.{0} S] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S) (i : ℤ)
  (x : C.idx i → S), Eq.{1} ((C.ddL (HAdd.hAdd.{0, 0, 0} i 1)) ((C.ddL i) x)) 0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [54860, 76728), lines 703–1004.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.ddL_ddL' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.toGCx`

def; source line 195.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.toGCx : {S : Type} →
  [inst : CommRing.{0} S] →
    ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S →
      ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} S
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [76882, 77175), lines 1006–1011.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.toGCx' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.kidx`

def; source line 203.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.kidx : {S : Type} →
  [inst : CommRing.{0} S] → ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S → ℤ → Type
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [77327, 77568), lines 1013–1017.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.kidx' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.isEmpty_kidx`

support theorem; source line 208.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.isEmpty_kidx : ∀ {S : Type}
  [inst : CommRing.{0} S] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S) (j : ℤ),
  Ne.{1} j 1 → Ne.{1} j 2 → IsEmpty.{1} (C.kidx j)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [77719, 78229), lines 1019–1025.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.isEmpty_kidx' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.kdL`

def; source line 217.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.kdL : {S : Type} →
  [inst : CommRing.{0} S] →
    (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S) →
      (i : ℤ) → LinearMap.{0, 0, 0, 0} (RingHom.id.{0} S) (C.kidx i → S) (C.kidx (HAdd.hAdd.{0, 0, 0} i 1) → S)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [78388, 82028), lines 1027–1075.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.kdL' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.kdL_kdL`

support theorem; source line 221.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.kdL_kdL : ∀ {S : Type}
  [inst : CommRing.{0} S] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S) (i : ℤ)
  (x : C.kidx i → S), Eq.{1} ((C.kdL (HAdd.hAdd.{0, 0, 0} i 1)) ((C.kdL i) x)) 0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [82178, 104127), lines 1077–1380.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.kdL_kdL' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.disk`

def; source line 229.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.disk : {S : Type} →
  [inst : CommRing.{0} S] →
    ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S →
      ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} S
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [104281, 104573), lines 1382–1387.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.disk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.disk_acyclic`

support theorem; source line 237.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.disk_acyclic : ∀ {S : Type}
  [inst : CommRing.{0} S] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S),
  IsUnit.{0} (Matrix.det.{0, 0} C.B) → ZInQ.Contrib.CloudB3RC53.SelmerDuality.GAcyclic.{0} C.disk
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [104724, 105653), lines 1389–1400.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.disk_acyclic' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.inc`

def; source line 269.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.inc : {S : Type} →
  [inst : CommRing.{0} S] →
    {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S} →
      (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) →
        (i : ℤ) → LinearMap.{0, 0, 0, 0} (RingHom.id.{0} S) ((C.cancel hB).idx i → S) (C.idx i → S)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [105812, 109832), lines 1402–1456.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.inc' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.inc_comm`

support theorem; source line 276.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.inc_comm : ∀ {S : Type}
  [inst : CommRing.{0} S] {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S}
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) (i : ℤ) (x : (C.cancel hB).idx i → S),
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.inc hB (HAdd.hAdd.{0, 0, 0} i 1))
      (((C.cancel hB).ddL i) x))
    ((C.ddL i) ((ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.inc hB i) x))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [109982, 145677), lines 1458–1947.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.inc_comm' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.incl`

def; source line 317.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.incl : {S : Type} →
  [inst : CommRing.{0} S] →
    {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S} →
      (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) →
        ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} (C.cancel hB).toGCx C.toGCx
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [145832, 147030), lines 1949–1965.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.incl' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.proj`

def; source line 324.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.proj : {S : Type} →
  [inst : CommRing.{0} S] →
    {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S} →
      IsUnit.{0} (Matrix.det.{0, 0} C.B) →
        (i : ℤ) → LinearMap.{0, 0, 0, 0} (RingHom.id.{0} S) (C.idx i → S) (C.kidx i → S)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [147181, 150620), lines 1967–2009.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.proj' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.proj_comm`

support theorem; source line 329.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.proj_comm : ∀ {S : Type}
  [inst : CommRing.{0} S] {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S}
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) (i : ℤ) (x : C.idx i → S),
  Eq.{1}
    ((ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.proj hB (HAdd.hAdd.{0, 0, 0} i 1))
      ((C.ddL i) x))
    ((C.kdL i) ((ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.proj hB i) x))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [150771, 181543), lines 2011–2409.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.proj_comm' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.projH`

def; source line 360.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.projH : {S : Type} →
  [inst : CommRing.{0} S] →
    {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S} →
      IsUnit.{0} (Matrix.det.{0, 0} C.B) → ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} C.toGCx C.disk
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [181699, 182811), lines 2411–2426.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.projH' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancelSES`

def; source line 370.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancelSES : {S : Type} →
  [inst : CommRing.{0} S] →
    {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S} →
      IsUnit.{0} (Matrix.det.{0, 0} C.B) →
        CategoryTheory.ShortComplex.{0, 1} (CochainComplex.{0, 1, 0} (ModuleCat.{0, 0} S) ℤ)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [182963, 187310), lines 2428–2488.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancelSES' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.comp_inl_fromRows_mulVec`

support theorem; source line 400.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.comp_inl_fromRows_mulVec : ∀ {S : Type}
  [inst : CommRing.{0} S] {m₁ m₂ n : Type} [inst_1 : Fintype.{0} n] (A₁ : Matrix.{0, 0, 0} m₁ n S)
  (A₂ : Matrix.{0, 0, 0} m₂ n S) (v : n → S),
  Eq.{1} (Function.comp.{1, 1, 1} (Matrix.mulVec.{0, 0, 0} (Matrix.fromRows.{0, 0, 0, 0} A₁ A₂) v) Sum.inl.{0, 0})
    (Matrix.mulVec.{0, 0, 0} A₁ v)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [187466, 188542), lines 2490–2507.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.comp_inl_fromRows_mulVec' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.exact_fromCols_one`

support theorem; source line 404.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.exact_fromCols_one : ∀ {S : Type}
  [inst : CommRing.{0} S] {m n : Type} [inst_1 : Fintype.{0} m] [inst_2 : DecidableEq.{1} m] [inst_3 : Fintype.{0} n]
  [inst_4 : DecidableEq.{1} n] (M : Matrix.{0, 0, 0} n m S) (c : Sum.{0, 0} m n → S),
  Eq.{1} (Matrix.mulVec.{0, 0, 0} (Matrix.fromCols.{0, 0, 0, 0} M 1) c) 0 →
    Eq.{1}
      (Matrix.mulVec.{0, 0, 0} (Matrix.fromRows.{0, 0, 0, 0} 1 (Neg.neg.{0} M))
        (Function.comp.{1, 1, 1} c Sum.inl.{0, 0}))
      c
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [188713, 191830), lines 2509–2564.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.exact_fromCols_one' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.inj_fromRows_one`

support theorem; source line 414.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.inj_fromRows_one : ∀ {S : Type}
  [inst : CommRing.{0} S] {m n : Type} [inst_1 : Fintype.{0} m] [inst_2 : DecidableEq.{1} m]
  (M : Matrix.{0, 0, 0} n m S) (a b : m → S),
  Eq.{1} (Matrix.mulVec.{0, 0, 0} (Matrix.fromRows.{0, 0, 0, 0} 1 M) a)
      (Matrix.mulVec.{0, 0, 0} (Matrix.fromRows.{0, 0, 0, 0} 1 M) b) →
    Eq.{1} a b
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [191995, 194187), lines 2566–2607.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.inj_fromRows_one' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.surj_fromCols_one`

support theorem; source line 421.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.surj_fromCols_one : ∀ {S : Type}
  [inst : CommRing.{0} S] {m n : Type} [inst_1 : Fintype.{0} m] [inst_2 : Fintype.{0} n] [inst_3 : DecidableEq.{1} n]
  (M : Matrix.{0, 0, 0} n m S) (y : n → S),
  Eq.{1} (Matrix.mulVec.{0, 0, 0} (Matrix.fromCols.{0, 0, 0, 0} M 1) (Sum.elim.{0, 0, 1} 0 y)) y
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [194350, 195961), lines 2609–2638.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.surj_fromCols_one' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancelSES_shortExact`

support theorem; source line 426.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancelSES_shortExact : ∀ {S : Type}
  [inst : CommRing.{0} S] {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S}
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)),
  CategoryTheory.ShortComplex.ShortExact.{0, 1}
    (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancelSES hB)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [196125, 200208), lines 2640–2696.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancelSES_shortExact' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.idSES`

def; source line 468.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.idSES : {S : Type} →
  [inst : CommRing.{0} S] →
    {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S} →
      CategoryTheory.ShortComplex.{0, 1} (CochainComplex.{0, 1, 0} (ModuleCat.{0, 0} S) ℤ)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [200375, 204013), lines 2698–2750.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.idSES' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.idSES_shortExact`

support theorem; source line 473.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.idSES_shortExact : ∀ {S : Type}
  [inst : CommRing.{0} S] {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S},
  CategoryTheory.ShortComplex.ShortExact.{0, 1}
    ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.idSES
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [204165, 207692), lines 2752–2802.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.idSES_shortExact' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancelSESHom`

def; source line 488.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancelSESHom : {S : Type} →
  [inst : CommRing.{0} S] →
    {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S} →
      (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) →
        Quiver.Hom.{0, 1} (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancelSES hB)
          ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.idSES
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [207855, 224089), lines 2804–3020.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.cancelSESHom' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.zeroGCx_acyclic`

support theorem; source line 495.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.zeroGCx_acyclic : ∀ {S : Type}
  [inst : CommRing.{0} S],
  ZInQ.Contrib.CloudB3RC53.SelmerDuality.GAcyclic.{0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.zeroGCx S)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [224248, 224507), lines 3022–3026.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.zeroGCx_acyclic' depends on axioms: [propext,
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.incl_quasiIso`

support theorem; source line 500.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.incl_quasiIso : ∀ {S : Type}
  [inst : CommRing.{0} S] {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S}
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)),
  QuasiIso.{0, 1, 0}
    (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.incl hB))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [224646, 231871), lines 3027–3125.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.incl_quasiIso' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.map`

def; source line 525.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.map : {S S' : Type} →
  [inst : CommRing.{0} S] →
    [inst_1 : CommRing.{0} S'] →
      ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S →
        RingHom.{0, 0} S S' → ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S'
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [232031, 232727), lines 3127–3139.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.map' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.map_Y_zero`

support theorem; source line 545.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.map_Y_zero : ∀ {S S' : Type}
  [inst : CommRing.{0} S] [inst_1 : CommRing.{0} S']
  (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S) (f : RingHom.{0, 0} S S'),
  Eq.{1} C.Y 0 → Eq.{1} (C.map f).Y 0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [232877, 237097), lines 3141–3204.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.map_Y_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.map_T_zero`

support theorem; source line 549.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.map_T_zero : ∀ {S S' : Type}
  [inst : CommRing.{0} S] [inst_1 : CommRing.{0} S']
  (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S) (f : RingHom.{0, 0} S S'),
  Eq.{1} C.T 0 → Eq.{1} (C.map f).T 0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [237254, 243452), lines 3206–3307.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.map_T_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.old`

def; source line 557.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.old : {S : Type} →
  [inst : CommRing.{0} S] →
    (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex S) →
      Eq.{1} C.Y 0 → Eq.{1} C.T 0 → ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.{0} S
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [243609, 247738), lines 3309–3373.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.old' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.toFour`

def; source line 608.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.toFour : {R : Type} →
  [inst : CommRing.{0} R] →
    (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex R) →
      ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} R (Fin C.m0) (Sum.{0, 0} C.D1 C.N) (Sum.{0, 0} C.D2 C.N)
        (Fin C.m2)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [247888, 250904), lines 3375–3412.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.toFour' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.hz_full`

support theorem; source line 619.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.hz_full : ∀ {R : Type}
  [inst : CommRing.{0} R] {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex R}
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) {z : Sum.{0, 0} C.D1 C.N → R},
  Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0 →
    Eq.{1}
      (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d1.{0} (C.cancel hB))
        (Function.comp.{1, 1, 1} z Sum.inl.{0, 0}))
      0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [251057, 265956), lines 3414–3646.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.hz_full' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.hlam_full`

support theorem; source line 644.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.hlam_full : ∀ {R : Type}
  [inst : CommRing.{0} R] {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex R}
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) {lam : Sum.{0, 0} C.D2 C.N → R},
  Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0 →
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0} (Function.comp.{1, 1, 1} lam Sum.inl.{0, 0})
        (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d1.{0} (C.cancel hB)))
      0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [266110, 279357), lines 3648–3847.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex.hlam_full' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.eOf`

def; source line 678.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.eOf : (m0 m1 m2 : ℕ) →
  (N : Type) →
    Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Fin m0) (Sum.{0, 0} Unit (Fin m1))) N) (Sum.{0, 0} (Fin m2) Unit))
      (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Fin m0) (Sum.{0, 0} Unit (Fin m1))) (Sum.{0, 0} (Fin m2) Unit)) N)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [279513, 279850), lines 3849–3854.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.eOf' does not depend on any axioms
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.σFull`

def; source line 693.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.σFull : (m0 m1 m2 : ℕ) →
  (N : Type) →
    Equiv.{1, 1} (Sum.{0, 0} (Sum.{0, 0} (Fin m0) Unit) (Sum.{0, 0} (Sum.{0, 0} (Fin m1) (Sum.{0, 0} Unit (Fin m2))) N))
      (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Fin m0) (Sum.{0, 0} Unit (Fin m1))) N) (Sum.{0, 0} (Fin m2) Unit))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [279946, 280286), lines 3854–3859.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.σFull' depends on axioms: [propext, Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf`

def; source line 709.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf : {K : Type} →
  [inst : Field.{0} K] →
    {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K} →
      (z : Sum.{0, 0} C.D1 C.N → K) →
        (lam : Sum.{0, 0} C.D2 C.N → K) →
          Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0 →
            Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour))
                0 →
              ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{0, 0, 0} K
                (Sum.{0, 0} (Sum.{0, 0} (Sum.{0, 0} (Fin C.m0) Unit) C.D2) C.N)
                (Sum.{0, 0} (Sum.{0, 0} C.D1 (Sum.{0, 0} (Fin C.m2) Unit)) C.N)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [280400, 310127), lines 3859–4323.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_degO`

support theorem; source line 713.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_degO : ∀ {K : Type} [inst : Field.{0} K]
  {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K} (z : Sum.{0, 0} C.D1 C.N → K)
  (lam : Sum.{0, 0} C.D2 C.N → K)
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0)
  (hlam : Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0)
  (n : C.N),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.degO.{0, 0, 0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf z lam hz hlam) (Sum.inr.{0, 0} n))
    1
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [310261, 335898), lines 4325–4802.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_degO' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_degE`

support theorem; source line 714.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_degE : ∀ {K : Type} [inst : Field.{0} K]
  {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K} (z : Sum.{0, 0} C.D1 C.N → K)
  (lam : Sum.{0, 0} C.D2 C.N → K)
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0)
  (hlam : Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0)
  (n : C.N),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.degE.{0, 0, 0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf z lam hz hlam) (Sum.inr.{0, 0} n))
    (HAdd.hAdd.{0, 0, 0} 1 1)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [336037, 361813), lines 4804–5283.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_degE' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_blk`

support theorem; source line 716.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_blk : ∀ {K : Type} [inst : Field.{0} K]
  {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K} (z : Sum.{0, 0} C.D1 C.N → K)
  (lam : Sum.{0, 0} C.D2 C.N → K)
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0)
  (hlam : Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0),
  Eq.{1}
    (Matrix.toBlocks₂₂.{0, 0, 0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.dEO.{0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf z lam hz hlam)))
    C.B
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [361952, 388526), lines 5285–5776.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_blk' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_hA`

support theorem; source line 722.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_hA : ∀ {K : Type} [inst : Field.{0} K]
  {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K},
  IsUnit.{0} (Matrix.det.{0, 0} C.B) →
    ∀ {z : Sum.{0, 0} C.D1 C.N → K} {lam : Sum.{0, 0} C.D2 C.N → K}
      {hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0}
      {hlam :
        Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0},
      IsUnit.{0}
        (Matrix.det.{0, 0}
          (Matrix.toBlocks₂₂.{0, 0, 0, 0, 0}
            (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.dEO.{0, 0, 0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf z lam hz hlam))))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [388664, 416485), lines 5778–6286.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf_hA' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.schurO_Xf`

support theorem; source line 727.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.schurO_Xf : ∀ {K : Type} [inst : Field.{0} K]
  {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K}
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) {z : Sum.{0, 0} C.D1 C.N → K} {lam : Sum.{0, 0} C.D2 C.N → K}
  {hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0}
  {hlam : Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0},
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.ClearingComplex.schurO.{0, 0, 0, 0}
      (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Xf z lam hz hlam) 1 ⋯ ⋯ ⋯)
    (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{0, 0, 0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{0, 0, 0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.toFour.{0} (C.cancel hB))
        (Function.comp.{1, 1, 1} z Sum.inl.{0, 0}) (Function.comp.{1, 1, 1} lam Sum.inl.{0, 0}) ⋯ ⋯))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [416622, 467100), lines 6288–7210.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.schurO_Xf' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.kmCoord_fullCancel`

support theorem; source line 749.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.kmCoord_fullCancel : ∀ {K : Type} [inst : Field.{0} K]
  {C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K}
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) {z : Sum.{0, 0} C.D1 C.N → K} {lam : Sum.{0, 0} C.D2 C.N → K}
  {hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0}
  {hlam : Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0},
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} C.toFour z lam hz hlam
      (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.σFull C.m0 C.m1 C.m2 C.N))
    (HMul.hMul.{0, 0, 0} (Inv.inv.{0} (Matrix.det.{0, 0} C.B))
      (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.toFour.{0} (C.cancel hB))
        (Function.comp.{1, 1, 1} z Sum.inl.{0, 0}) (Function.comp.{1, 1, 1} lam Sum.inl.{0, 0}) ⋯ ⋯
        (ZInQ.Contrib.CloudB3RC53.ClearingComplex.σBlock C.m0 C.m1 C.m2)))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [467241, 514373), lines 7212–8030.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.kmCoord_fullCancel' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.isUnit_B_full`

support theorem; source line 775.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.isUnit_B_full : ∀ {b : ℕ} {Qn ιn : Type} [Fintype.{0} Qn]
  [inst : DecidableEq.{1} Qn] [inst_1 : Fintype.{0} ιn] [inst_2 : DecidableEq.{1} ιn]
  (A : Qn → Matrix.{0, 0, 0} ιn ιn ZInQ.Manuscript.RC.Determinant.Lam) (dq : Qn → ℕ),
  (∀ (q : Qn), LE.le.{0} (dq q) 4) →
    ∀ (v : Qn → Units.{0} ZInQ.Manuscript.RC.Determinant.Lam) (w : Qn → ZInQ.Manuscript.RC.Determinant.Lam),
      (∀ (q : Qn),
          Eq.{1} (Matrix.det.{0, 0} (A q))
            (HAdd.hAdd.{0, 0, 0} (HMul.hMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} PowerSeries.X.{0} (dq q)) ↑(v q))
              (HMul.hMul.{0, 0, 0} 2 (w q)))) →
        ∀
          (C :
            ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex
              (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
          (eN : Equiv.{1, 1} C.N (Prod.{0, 0} ιn Qn)),
          Eq.{1}
              (Matrix.map.{0, 0, 0, 0}
                (Matrix.submatrix.{0, 0, 0, 0, 0} C.B ⇑(Equiv.symm.{1, 1} eN) ⇑(Equiv.symm.{1, 1} eN))
                ⇑ZInQ.Manuscript.RC.Determinant.aug.{0, 0})
              (Matrix.blockDiagonal.{0, 0, 0, 0} A) →
            IsUnit.{0} (Matrix.det.{0, 0} (C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)).B)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [514523, 1306117), lines 8032–19238.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.isUnit_B_full' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore`

structure; source line 798.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore : (Qn : Type) →
  [Fintype.{0} Qn] → [DecidableEq.{1} Qn] → ℕ → ℕ → ℕ → ℕ → ℕ → Type 1
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [1306262, 1306432), lines 19240–19243.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.isUnit_B`

support theorem; source line 836.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.isUnit_B : ∀ {b : ℕ} {Qn : Type}
  [inst : Fintype.{0} Qn] [inst_1 : DecidableEq.{1} Qn] {dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore Qn b dK hK cE tK),
  IsUnit.{0} (Matrix.det.{0, 0} (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)).B)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [1306572, 2030870), lines 19245–29587.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.isUnit_B' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.D`

def; source line 840.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.D : {b : ℕ} →
  {Qn : Type} →
    [inst : Fintype.{0} Qn] →
      [inst_1 : DecidableEq.{1} Qn] →
        {dK hK cE tK : ℕ} →
          ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore Qn b dK hK cE tK →
            ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.{0}
              (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [2031019, 2087249), lines 29589–30366.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.D' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.oldC`

abbrev; source line 844.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.oldC : {b : ℕ} →
  {Qn : Type} →
    [inst : Fintype.{0} Qn] →
      [inst_1 : DecidableEq.{1} Qn] →
        {dK hK cE tK : ℕ} →
          ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore Qn b dK hK cE tK →
            ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.{0} ZInQ.Manuscript.RC.Determinant.Lam
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [2087391, 2088136), lines 30368–30380.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.oldC' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.Bsub`

abbrev; source line 847.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.Bsub : {b : ℕ} →
  {Qn : Type} →
    [inst : Fintype.{0} Qn] →
      [inst_1 : DecidableEq.{1} Qn] →
        {dK hK cE tK : ℕ} →
          (M : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore Qn b dK hK cE tK) →
            Matrix.{0, 0, 0} (Prod.{0, 0} M.ιn Qn) (Prod.{0, 0} M.ιn Qn)
              (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [2088281, 2089789), lines 30382–30407.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.Bsub' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.d1_map_aug`

support theorem; source line 851.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.d1_map_aug : ∀ {b : ℕ} {Qn : Type}
  [inst : Fintype.{0} Qn] [inst_1 : DecidableEq.{1} Qn] {dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore Qn b dK hK cE tK),
  Eq.{1}
    (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d1.{0} M.D)
      ⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.augS b))
    (Matrix.map.{0, 0, 0, 0} (Matrix.map.{0, 0, 0, 0} M.C.P ⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.augR b))
      ⇑(Algebra.algebraMap.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam ZInQ.Manuscript.RC.Determinant.OO))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [2089934, 3150430), lines 30409–45224.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.d1_map_aug' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.aug_eq`

support theorem; source line 857.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.aug_eq : ∀ {b : ℕ} {Qn : Type}
  [inst : Fintype.{0} Qn] [inst_1 : DecidableEq.{1} Qn] {dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore Qn b dK hK cE tK) (i : ℕ),
  Eq.{1}
    (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.Ai.{0} M.D i)
      ⇑ZInQ.Manuscript.RC.Determinant.aug.{0, 0})
    (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.Ai.{0} M.oldC i)
      ⇑(Algebra.algebraMap.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam ZInQ.Manuscript.RC.Determinant.OO))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [3150581, 3697442), lines 45226–52960.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.aug_eq' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.poles1`

support theorem; source line 869.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.poles1 : ∀ {b : ℕ} {Qn : Type}
  [inst : Fintype.{0} Qn] [inst_1 : DecidableEq.{1} Qn] {dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore Qn b dK hK cE tK),
  ZInQ.Contrib.CloudB3RC53.ClearingComplex.IsNewLocalSchur fun x =>
    Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d1.{0} M.D)
      ⇑(ZInQ.Manuscript.RC.Determinant.signEval.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [3697589, 4332159), lines 52962–61870.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.poles1' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.toIdentification`

def; source line 904.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.toIdentification : {b : ℕ} →
  {Qn : Type} →
    [inst : Fintype.{0} Qn] →
      [inst_1 : DecidableEq.{1} Qn] →
        {dK hK cE tK : ℕ} →
          ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore Qn b dK hK cE tK →
            ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification b dK hK cE tK
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4332306, 4332735), lines 61872–61880.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullCore.toIdentification' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy`

abbrev; source line 930.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy : {K : Type} →
  [inst : Field.{0} K] →
    (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K) →
      IsUnit.{0} (Matrix.det.{0, 0} C.B) → ZInQ.Contrib.CloudB3RC53.ClearingComplex.PreComplex K
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4332892, 4334110), lines 61882–61902.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy_unit`

new theorem; source line 950.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy_unit : ∀ {K : Type}
  [inst : Field.{0} K] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K)
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)),
  IsUnit.{0}
    (Matrix.det.{0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy C hB).B)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4334267, 4336183), lines 61904–61935.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy_unit' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy_cancel`

new theorem; source line 958.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy_cancel : ∀ {K : Type}
  [inst : Field.{0} K] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K)
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.toFour.{0}
      ((ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy C hB).cancel ⋯))
    (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.toFour.{0} (C.cancel hB))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4336345, 4346237), lines 61937–62072.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy_cancel' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy`

def; source line 966.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy : {K : Type} →
  [inst : Field.{0} K] →
    (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K) →
      (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) →
        ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.{0, 0, 0, 0, 0, 0, 0, 0, 0} C.toFour
          (ZInQ.Contrib.CloudB3RC53.CoordLink.PreComplex'.toFour
            (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy C hB))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4346401, 4358427), lines 62074–62264.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy_class`

new theorem; source line 993.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy_class : ∀ {K : Type}
  [inst : Field.{0} K] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K)
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) (z : Sum.{0, 0} C.D1 C.N → K),
  Eq.{1}
    (Matrix.mulVec.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f1.{0, 0, 0, 0, 0, 0, 0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy C hB))
      z)
    (Function.comp.{1, 1, 1} z Sum.inl.{0, 0})
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4358579, 4374271), lines 62266–62527.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy_class' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacyFunctional`

def; source line 1001.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacyFunctional : {K : Type} →
  [inst : Field.{0} K] →
    (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K) →
      (Sum.{0, 0} C.D2 C.N → K) → Sum.{0, 0} C.D2 C.N → K
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4374429, 4375363), lines 62529–62547.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacyFunctional' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy_functional`

new theorem; source line 1006.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy_functional : ∀ {K : Type}
  [inst : Field.{0} K] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K)
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) (lam : Sum.{0, 0} C.D2 C.N → K),
  Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0 →
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacyFunctional C lam)
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f2.{0, 0, 0, 0, 0, 0, 0, 0, 0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy C hB)))
      lam
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4375519, 4399090), lines 62549–62952.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.fullToLegacy_functional' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacyFunctional_closed`

new theorem; source line 1027.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacyFunctional_closed : ∀ {K : Type}
  [inst : Field.{0} K] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K)
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) (lam : Sum.{0, 0} C.D2 C.N → K),
  Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0 →
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacyFunctional C lam)
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.CoordLink.PreComplex'.toFour
            (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy C hB))))
      0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4399253, 4422162), lines 62954–63346.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacyFunctional_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacy_cycle_closed`

new theorem; source line 1039.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacy_cycle_closed : ∀ {K : Type}
  [inst : Field.{0} K] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K)
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) (z : Sum.{0, 0} C.D1 C.N → K),
  Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0 →
    Eq.{1}
      (Matrix.mulVec.{0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.CoordLink.PreComplex'.toFour
            (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy C hB)))
        (Function.comp.{1, 1, 1} z Sum.inl.{0, 0}))
      0
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4422325, 4448786), lines 63348–63790.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacy_cycle_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.full_coordinate_eq_inverseDiskLegacy`

new theorem; source line 1050.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.full_coordinate_eq_inverseDiskLegacy : ∀
  {K : Type} [inst : Field.{0} K] (C : ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.FullPreComplex K)
  (hB : IsUnit.{0} (Matrix.det.{0, 0} C.B)) (z : Sum.{0, 0} C.D1 C.N → K) (lam : Sum.{0, 0} C.D2 C.N → K)
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour) z) 0)
  (hlam : Eq.{1} (Matrix.vecMul.{0, 0, 0} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} C.toFour)) 0),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0} C.toFour z lam hz hlam
      (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.σFull C.m0 C.m1 C.m2 C.N))
    (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{0, 0, 0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.CoordLink.PreComplex'.toFour
        (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverseDiskLegacy C hB))
      (Function.comp.{1, 1, 1} z Sum.inl.{0, 0})
      (ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.legacyFunctional C lam) ⋯ ⋯
      (ZInQ.Contrib.CloudB3RC53.CoordLink.σPre C.m0 C.m1 C.m2 C.N))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4448945, 4496678), lines 63792–64615.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.full_coordinate_eq_inverseDiskLegacy' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.same_disk_factor_obstruction`

new theorem; source line 1074.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.same_disk_factor_obstruction : ∀ {K : Type}
  [inst : Field.{0} K] (d c : K),
  Ne.{1} d 0 →
    Ne.{1} c 0 →
      Ne.{1} (HPow.hPow.{0, 0, 0} d 2) 1 → Ne.{1} (HMul.hMul.{0, 0, 0} (Inv.inv.{0} d) c) (HMul.hMul.{0, 0, 0} d c)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4496854, 4499150), lines 64617–64669.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.same_disk_factor_obstruction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverse_matrix_lift_forces_integral_unit`

new theorem; source line 1089.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverse_matrix_lift_forces_integral_unit : ∀
  {R S : Type} [inst : CommRing.{0} R] [inst_1 : CommRing.{0} S] {ι : Type} [inst_2 : Fintype.{0} ι]
  [inst_3 : DecidableEq.{1} ι] (f : RingHom.{0, 0} R S),
  Function.Injective.{1, 1} ⇑f →
    ∀ (D E : Matrix.{0, 0, 0} ι ι R),
      IsUnit.{0} (Matrix.det.{0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑f)) →
        Eq.{1} (Matrix.map.{0, 0, 0, 0} E ⇑f) (Inv.inv.{0} (Matrix.map.{0, 0, 0, 0} D ⇑f)) →
          IsUnit.{0} (Matrix.det.{0, 0} D)
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4499318, 4503262), lines 64671–64739.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.inverse_matrix_lift_forces_integral_unit' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.no_integral_inverse_disk_lift`

new theorem; source line 1107.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.no_integral_inverse_disk_lift : ∀ {R S : Type}
  [inst : CommRing.{0} R] [inst_1 : CommRing.{0} S] {ι : Type} [inst_2 : Fintype.{0} ι] [inst_3 : DecidableEq.{1} ι]
  (f : RingHom.{0, 0} R S),
  Function.Injective.{1, 1} ⇑f →
    ∀ (D : Matrix.{0, 0, 0} ι ι R),
      IsUnit.{0} (Matrix.det.{0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑f)) →
        ¬IsUnit.{0} (Matrix.det.{0, 0} D) →
          ¬∃ E, Eq.{1} (Matrix.map.{0, 0, 0, 0} E ⇑f) (Inv.inv.{0} (Matrix.map.{0, 0, 0, 0} D ⇑f))
```

Exact kernel type: decompress `FullModelAdapter.exact.txt.gz` to `FullModelAdapter.exact.txt`; bytes [4503442, 4507568), lines 64741–64813.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.FullConditionSupport.Adapter.no_integral_inverse_disk_lift' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

# CoefficientRealization.lean

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField`

abbrev; source line 36.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField : Type
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [0, 72), lines 1–2.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.ofIntegral`

abbrev; source line 38.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.ofIntegral : RingHom.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam
  ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [207, 3368), lines 4–45.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.ofIntegral' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.powerSeriesToLaurent`

abbrev; source line 40.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.powerSeriesToLaurent : RingHom.{0, 0} (PowerSeries.{0} ℚ_[2])
  (LaurentSeries.{0} ℚ_[2])
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [3502, 5715), lines 47–77.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.powerSeriesToLaurent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent`

abbrev; source line 43.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent : RingHom.{0, 0}
  ZInQ.Manuscript.RC.Determinant.Lam (LaurentSeries.{0} ℚ_[2])
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [5859, 7794), lines 79–106.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent_injective`

new theorem; source line 46.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent_injective : Function.Injective.{1, 1}
  ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [7935, 12681), lines 108–171.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent_injective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToClearing_injective`

new theorem; source line 49.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToClearing_injective : Function.Injective.{1, 1}
  ⇑ZInQ.Contrib.CloudB3RC53.CoordLink.ψO
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [12832, 174633), lines 173–2514.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToClearing_injective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent`

abbrev; source line 54.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent : RingHom.{0, 0}
  ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField (LaurentSeries.{0} ℚ_[2])
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [174785, 178494), lines 2516–2565.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing`

abbrev; source line 58.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing : RingHom.{0, 0}
  ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField (FractionRing.{0} ZInQ.Manuscript.RC.Determinant.OO)
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [178627, 250859), lines 2567–3643.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent_injective`

new theorem; source line 61.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent_injective : Function.Injective.{1, 1}
  ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [250993, 259593), lines 3645–3754.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent_injective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing_injective`

new theorem; source line 63.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing_injective : Function.Injective.{1, 1}
  ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [259736, 425424), lines 3756–6143.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing_injective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent_ofIntegral`

new theorem; source line 65.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent_ofIntegral : ∀ (a : ZInQ.Manuscript.RC.Determinant.Lam),
  Eq.{1}
    (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent
      (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.ofIntegral a))
    (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent a)
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [425568, 446178), lines 6145–6407.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent_ofIntegral' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing_ofIntegral`

new theorem; source line 68.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing_ofIntegral : ∀ (a : ZInQ.Manuscript.RC.Determinant.Lam),
  Eq.{1}
    (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing
      (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.ofIntegral a))
    (ZInQ.Contrib.CloudB3RC53.CoordLink.ψO a)
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [446322, 789295), lines 6409–11252.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing_ofIntegral' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon`

abbrev; source line 74.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon : {b : ℕ} →
  MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} ℤ) →
    RingHom.{0, 0}
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b))
      ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [789440, 796125), lines 11254–11337.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.sign_toLaurent`

new theorem; source line 77.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.sign_toLaurent : ∀ {b : ℕ}
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} ℤ))
  (a : MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b)),
  Eq.{1}
    (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent
      ((ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ) a))
    (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent
      ((ZInQ.Manuscript.RC.Determinant.signEval.{0, 0} χ) a))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [796261, 839096), lines 11339–11881.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.sign_toLaurent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.sign_toClearing`

new theorem; source line 82.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.sign_toClearing : ∀ {b : ℕ}
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} ℤ))
  (a : MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b)),
  Eq.{1}
    (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing
      ((ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ) a))
    ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} χ) ((ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b) a))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [839234, 1379003), lines 11883–19477.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.sign_toClearing' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.matrix_toClearing`

new theorem; source line 95.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.matrix_toClearing : ∀ {b : ℕ} {ι κ : Type}
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} ℤ))
  (D :
    Matrix.{0, 0, 0} ι κ
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b))),
  Eq.{1}
    (Matrix.map.{0, 0, 0, 0}
      (Matrix.map.{0, 0, 0, 0} D ⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ))
      ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing)
    (Matrix.map.{0, 0, 0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b))
      ⇑(ZInQ.Manuscript.RC.Determinant.evK.{0, 0} χ))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [1379142, 2037699), lines 19479–28679.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.matrix_toClearing' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.matrix_toLaurent`

new theorem; source line 100.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.matrix_toLaurent : ∀ {b : ℕ} {ι κ : Type}
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} ℤ))
  (D :
    Matrix.{0, 0, 0} ι κ
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b))),
  Eq.{1}
    (Matrix.map.{0, 0, 0, 0}
      (Matrix.map.{0, 0, 0, 0} D ⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ))
      ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
    (Matrix.map.{0, 0, 0, 0} D
      ⇑(RingHom.comp.{0, 0, 0} ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent
          (AlgHom.toRingHom.{0, 0, 0} (ZInQ.Manuscript.RC.Determinant.signEval.{0, 0} χ))))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [2037840, 2086949), lines 28681–29292.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.matrix_toLaurent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.vector_toClearing`

new theorem; source line 105.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.vector_toClearing : ∀ {b : ℕ} {ι : Type}
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} ℤ))
  (z : ι → MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b)),
  Eq.{1}
    (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing)
      (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ)) z))
    (Function.comp.{1, 1, 1} (⇑(ZInQ.Manuscript.RC.Determinant.evK.{0, 0} χ))
      (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)) z))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [2087089, 2672423), lines 29294–37442.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.vector_toClearing' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.vector_toLaurent`

new theorem; source line 110.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.vector_toLaurent : ∀ {b : ℕ} {ι : Type}
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} ℤ))
  (z : ι → MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b)),
  Eq.{1}
    (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
      (Function.comp.{1, 1, 1} (⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ)) z))
    (Function.comp.{1, 1, 1} (⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent)
      (Function.comp.{1, 1, 1} (⇑(AlgHom.toRingHom.{0, 0, 0} (ZInQ.Manuscript.RC.Determinant.signEval.{0, 0} χ))) z))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [2672564, 2719768), lines 37444–38035.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.vector_toLaurent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.inverse_toLaurent`

new theorem; source line 122.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.inverse_toLaurent : ∀ {ι : Type} [inst : Fintype.{0} ι]
  [inst_1 : DecidableEq.{1} ι]
  (B : Matrix.{0, 0, 0} ι ι ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField),
  Ne.{1} (Matrix.det.{0, 0} B) 0 →
    Eq.{1} (Matrix.map.{0, 0, 0, 0} (Inv.inv.{0} B) ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
      (Inv.inv.{0} (Matrix.map.{0, 0, 0, 0} B ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [2719908, 2748404), lines 38037–38390.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.inverse_toLaurent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.inverse_toClearing`

new theorem; source line 127.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.inverse_toClearing : ∀ {ι : Type} [inst : Fintype.{0} ι]
  [inst_1 : DecidableEq.{1} ι]
  (B : Matrix.{0, 0, 0} ι ι ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField),
  Ne.{1} (Matrix.det.{0, 0} B) 0 →
    Eq.{1} (Matrix.map.{0, 0, 0, 0} (Inv.inv.{0} B) ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing)
      (Inv.inv.{0} (Matrix.map.{0, 0, 0, 0} B ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [2748545, 3162548), lines 38392–44151.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.inverse_toClearing' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.schur_toClearing`

new theorem; source line 134.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.schur_toClearing : ∀ {ι : Type} [inst : Fintype.{0} ι]
  [inst_1 : DecidableEq.{1} ι] {r c : Type}
  (P : Matrix.{0, 0, 0} r c ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField)
  (Q : Matrix.{0, 0, 0} r ι ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField)
  (T : Matrix.{0, 0, 0} ι c ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField)
  (B : Matrix.{0, 0, 0} ι ι ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField),
  Ne.{1} (Matrix.det.{0, 0} B) 0 →
    Eq.{1}
      (Matrix.map.{0, 0, 0, 0} (HSub.hSub.{0, 0, 0} P (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Q (Inv.inv.{0} B)) T))
        ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing)
      (HSub.hSub.{0, 0, 0} (Matrix.map.{0, 0, 0, 0} P ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing)
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (Matrix.map.{0, 0, 0, 0} Q ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing)
            (Inv.inv.{0} (Matrix.map.{0, 0, 0, 0} B ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing)))
          (Matrix.map.{0, 0, 0, 0} T ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing)))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [3162690, 4759298), lines 44153–65828.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.schur_toClearing' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.schur_toLaurent`

new theorem; source line 141.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.schur_toLaurent : ∀ {ι : Type} [inst : Fintype.{0} ι]
  [inst_1 : DecidableEq.{1} ι] {r c : Type}
  (P : Matrix.{0, 0, 0} r c ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField)
  (Q : Matrix.{0, 0, 0} r ι ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField)
  (T : Matrix.{0, 0, 0} ι c ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField)
  (B : Matrix.{0, 0, 0} ι ι ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField),
  Ne.{1} (Matrix.det.{0, 0} B) 0 →
    Eq.{1}
      (Matrix.map.{0, 0, 0, 0} (HSub.hSub.{0, 0, 0} P (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} Q (Inv.inv.{0} B)) T))
        ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
      (HSub.hSub.{0, 0, 0} (Matrix.map.{0, 0, 0, 0} P ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (Matrix.map.{0, 0, 0, 0} Q ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)
            (Inv.inv.{0} (Matrix.map.{0, 0, 0, 0} B ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)))
          (Matrix.map.{0, 0, 0, 0} T ⇑ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent)))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [4759438, 4850489), lines 65830–66938.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.schur_toLaurent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.correctedCommon`

abbrev; source line 151.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.correctedCommon : ℕ →
  ZInQ.Manuscript.RC.Determinant.Lam → ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [4850628, 4850826), lines 66940–66943.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.correctedCommon' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toClearing`

new theorem; source line 153.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toClearing : ∀ (e : ℕ)
  (a : ZInQ.Manuscript.RC.Determinant.Lam),
  Eq.{1}
    (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing
      (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.correctedCommon e a))
    (ZInQ.Manuscript.RC.Determinant.uK.{0} e a)
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [4850965, 5028277), lines 66945–69465.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toClearing' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toLaurent_fraction`

new theorem; source line 157.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toLaurent_fraction : ∀ (e : ℕ)
  (a : ZInQ.Manuscript.RC.Determinant.Lam),
  Eq.{1}
    (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent
      (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.correctedCommon e a))
    (HDiv.hDiv.{0, 0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent a)
      (HPow.hPow.{0, 0, 0} 2 e))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [5028421, 5048010), lines 69467–69716.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toLaurent_fraction' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toLaurent_rep`

new theorem; source line 162.

```lean
ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toLaurent_rep : ∀ (e : ℕ)
  (a : ZInQ.Manuscript.RC.Determinant.Lam),
  Eq.{1}
    (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent
      (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.correctedCommon e a))
    (ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.powerSeriesToLaurent
      (HMul.hMul.{0, 0, 0} (PowerSeries.C.{0} (Inv.inv.{0} (HPow.hPow.{0, 0, 0} 2 e)))
        (ZInQ.Contrib.CloudB3RC53.CoordLink.ιQ a)))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [5048162, 5076794), lines 69718–70085.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.corrected_toLaurent_rep' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre`

abbrev; source line 181.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre : {b : ℕ} →
  ZInQ.Contrib.CloudB3RC53.ClearingComplex.PreComplex
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b)) →
    MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} ℤ) →
      ZInQ.Contrib.CloudB3RC53.ClearingComplex.PreComplex
        ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.CommonField
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [5076941, 5082830), lines 70087–70160.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre_toClearing`

new theorem; source line 185.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre_toClearing : ∀ {b : ℕ}
  (C :
    ZInQ.Contrib.CloudB3RC53.ClearingComplex.PreComplex
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} ℤ)),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.CoordLink.PreComplex'.toFour
      ((ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre C χ).map
        ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toClearing))
    (ZInQ.Contrib.CloudB3RC53.CoordLink.PreComplex'.toFour
      ((C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)).map (ZInQ.Manuscript.RC.Determinant.evK.{0, 0} χ)))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [5082963, 6144238), lines 70162–85141.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre_toClearing' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre_toLaurent`

new theorem; source line 204.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre_toLaurent : ∀ {b : ℕ}
  (C :
    ZInQ.Contrib.CloudB3RC53.ClearingComplex.PreComplex
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} ℤ)),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.CoordLink.PreComplex'.toFour
      ((ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre C χ).map
        ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.toLaurent))
    (ZInQ.Contrib.CloudB3RC53.CoordLink.PreComplex'.toFour
      (C.map
        (RingHom.comp.{0, 0, 0} ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.integralToLaurent
          (AlgHom.toRingHom.{0, 0, 0} (ZInQ.Manuscript.RC.Determinant.signEval.{0, 0} χ)))))
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [6144382, 6271420), lines 85143–86704.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.commonPre_toLaurent' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.local_block_regular_common`

new theorem; source line 227.

```lean
@ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.local_block_regular_common : ∀ {b : ℕ} {ι : Type}
  [inst : Fintype.{0} ι] [inst_1 : DecidableEq.{1} ι]
  (χ : MonoidHom.{0, 0} (ZInQ.Manuscript.RC.Determinant.SignGroup b) (Units.{0} ℤ))
  (B :
    Matrix.{0, 0, 0} ι ι
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.Lam (ZInQ.Manuscript.RC.Determinant.SignGroup b))),
  IsUnit.{0} (Matrix.det.{0, 0} (Matrix.map.{0, 0, 0, 0} B ⇑(ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b))) →
    Ne.{1}
      (Matrix.det.{0, 0}
        (Matrix.map.{0, 0, 0, 0} B ⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.signToCommon χ)))
      0
```

Exact kernel type: decompress `CoefficientRealization.exact.txt.gz` to `CoefficientRealization.exact.txt`; bytes [6271563, 6772632), lines 86706–93677.

```text
'ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients.local_block_regular_common' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```
