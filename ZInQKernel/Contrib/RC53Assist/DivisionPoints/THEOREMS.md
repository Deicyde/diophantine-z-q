# Division points over the support field: statements and kernel dependencies

Source: `ZInQKernel/Contrib/RC53Assist/DivisionPoints/Support.lean`, namespace
`ZInQ.Manuscript.RC.DivisionPoints`. Each entry is the elaborated statement (`#check`, with
binder types) followed by its `#print axioms` report, produced by a separate scratch file that is
not part of the source. Every declaration depends only on `propext`, `Classical.choice` and
`Quot.sound`.

Checking the source needs these vendored modules to be built; their sources are unchanged and
none of them is built by the default target:

* `ZInQKernel.Contrib.TauCeti.Algebra.Module.Torsion.Int`
* `ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular`
* `ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Singular`
* `ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.GoodReduction`
* `ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction`
* `ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Inertia`

## `valuation_apply_le_one_and_sub_lt_one`

```lean
@valuation_apply_le_one_and_sub_lt_one : ∀ {A : Type u_1} {L : Type u_2} {K : Type u_3} [inst : CommRing A]
  [inst_1 : IsDedekindDomain A] [inst_2 : Field L] [inst_3 : Algebra A L] [inst_4 : IsFractionRing A L]
  [inst_5 : Field K] [inst_6 : Algebra K L] (u : IsDedekindDomain.HeightOneSpectrum A) (ρ : Gal(L/K)),
  (∀ (a : A), ∃ (b : A), (algebraMap A L) b = ρ ((algebraMap A L) a) ∧ b - a ∈ u.asIdeal) →
    ∀ {z : L},
      (IsDedekindDomain.HeightOneSpectrum.valuation L u) z ≤ 1 →
        (IsDedekindDomain.HeightOneSpectrum.valuation L u) (ρ z) ≤ 1 ∧
          (IsDedekindDomain.HeightOneSpectrum.valuation L u) (ρ z - z) < 1
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.valuation_apply_le_one_and_sub_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `exists_mem_inertiaSubgroup`

```lean
@exists_mem_inertiaSubgroup : ∀ {A : Type u_1} {L : Type u_2} {K : Type u_3} [inst : CommRing A]
  [inst_1 : IsDedekindDomain A] [inst_2 : Field L] [inst_3 : Algebra A L] [inst_4 : IsFractionRing A L]
  [inst_5 : Field K] [inst_6 : Algebra K L] (u : IsDedekindDomain.HeightOneSpectrum A) (σ : Gal(L/K)),
  (∀ (a : A), ∃ (b : A), (algebraMap A L) b = σ ((algebraMap A L) a) ∧ b - a ∈ u.asIdeal) →
    (∀ (a : A), ∃ (b : A), (algebraMap A L) b = σ⁻¹ ((algebraMap A L) a) ∧ b - a ∈ u.asIdeal) →
      ∃ τ ∈ ValuationSubring.inertiaSubgroup K (IsDedekindDomain.HeightOneSpectrum.valuation L u).valuationSubring,
        ↑τ = σ
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.exists_mem_inertiaSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `valuation_algebraMap_le_one`

```lean
@valuation_algebraMap_le_one : ∀ {R : Type u_1} {B : Type u_2} {K : Type u_3} {L : Type u_4} [inst : CommRing R]
  [inst_1 : IsDedekindDomain R] [inst_2 : CommRing B] [inst_3 : IsDedekindDomain B] [inst_4 : Field K]
  [inst_5 : Field L] [inst_6 : Algebra R K] [inst_7 : IsFractionRing R K] [inst_8 : Algebra B L]
  [inst_9 : IsFractionRing B L] [inst_10 : Algebra R B] [inst_11 : Algebra K L] [inst_12 : Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L] (v : IsDedekindDomain.HeightOneSpectrum R)
  (u : IsDedekindDomain.HeightOneSpectrum B),
  (∀ (a : R), (algebraMap R B) a ∈ u.asIdeal ↔ a ∈ v.asIdeal) →
    ∀ {z : K},
      (IsDedekindDomain.HeightOneSpectrum.valuation K v) z ≤ 1 →
        (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) z) ≤ 1
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.valuation_algebraMap_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `valuation_algebraMap_eq_one`

```lean
@valuation_algebraMap_eq_one : ∀ {R : Type u_1} {B : Type u_2} {K : Type u_3} {L : Type u_4} [inst : CommRing R]
  [inst_1 : IsDedekindDomain R] [inst_2 : CommRing B] [inst_3 : IsDedekindDomain B] [inst_4 : Field K]
  [inst_5 : Field L] [inst_6 : Algebra R K] [inst_7 : IsFractionRing R K] [inst_8 : Algebra B L]
  [inst_9 : IsFractionRing B L] [inst_10 : Algebra R B] [inst_11 : Algebra K L] [inst_12 : Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L] (v : IsDedekindDomain.HeightOneSpectrum R)
  (u : IsDedekindDomain.HeightOneSpectrum B),
  (∀ (a : R), (algebraMap R B) a ∈ u.asIdeal ↔ a ∈ v.asIdeal) →
    ∀ {z : K},
      (IsDedekindDomain.HeightOneSpectrum.valuation K v) z = 1 →
        (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) z) = 1
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.valuation_algebraMap_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `map_eq_self_of_valuation`

```lean
@map_eq_self_of_valuation : ∀ {A : Type u_1} {K : Type u_2} {L : Type u_3} [inst : CommRing A]
  [inst_1 : IsDedekindDomain A] [inst_2 : Field K] [inst_3 : Field L] [inst_4 : Algebra K L] [inst_5 : Algebra A L]
  [inst_6 : IsFractionRing A L] [inst_7 : DecidableEq L] (u : IsDedekindDomain.HeightOneSpectrum A)
  (W : WeierstrassCurve K),
  (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) W.a₁) ≤ 1 →
    (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) W.a₂) ≤ 1 →
      (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) W.a₃) ≤ 1 →
        (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) W.a₄) ≤ 1 →
          (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) W.a₆) ≤ 1 →
            (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) W.Δ) = 1 →
              ∀ {n : ℕ},
                ↑n ∉ u.asIdeal →
                  ∀
                    {σ :
                      ↥(ValuationSubring.decompositionSubgroup K
                          (IsDedekindDomain.HeightOneSpectrum.valuation L u).valuationSubring)},
                    σ ∈
                        ValuationSubring.inertiaSubgroup K
                          (IsDedekindDomain.HeightOneSpectrum.valuation L u).valuationSubring →
                      ∀ {P : (W.baseChange L).toAffine.Point},
                        (WeierstrassCurve.Affine.Point.map ↑↑σ) (n • P) = n • P →
                          (WeierstrassCurve.Affine.Point.map ↑↑σ) P = P
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.map_eq_self_of_valuation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `map_eq_self_of_variableChange`

```lean
@map_eq_self_of_variableChange : ∀ {A : Type u_1} {K : Type u_2} {L : Type u_3} [inst : CommRing A]
  [inst_1 : IsDedekindDomain A] [inst_2 : Field K] [inst_3 : Field L] [inst_4 : Algebra K L] [inst_5 : Algebra A L]
  [inst_6 : IsFractionRing A L] [inst_7 : DecidableEq L] (u : IsDedekindDomain.HeightOneSpectrum A)
  (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K),
  (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) (C • W).a₁) ≤ 1 →
    (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) (C • W).a₂) ≤ 1 →
      (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) (C • W).a₃) ≤ 1 →
        (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) (C • W).a₄) ≤ 1 →
          (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) (C • W).a₆) ≤ 1 →
            (IsDedekindDomain.HeightOneSpectrum.valuation L u) ((algebraMap K L) (C • W).Δ) = 1 →
              ∀ {n : ℕ},
                ↑n ∉ u.asIdeal →
                  ∀
                    {σ :
                      ↥(ValuationSubring.decompositionSubgroup K
                          (IsDedekindDomain.HeightOneSpectrum.valuation L u).valuationSubring)},
                    σ ∈
                        ValuationSubring.inertiaSubgroup K
                          (IsDedekindDomain.HeightOneSpectrum.valuation L u).valuationSubring →
                      ∀ {P : (W.baseChange L).toAffine.Point},
                        (WeierstrassCurve.Affine.Point.map ↑↑σ) (n • P) = n • P →
                          (WeierstrassCurve.Affine.Point.map ↑↑σ) P = P
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.map_eq_self_of_variableChange' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `HasGoodReductionAt`

```lean
@HasGoodReductionAt : {K : Type} →
  [inst : Field K] →
    [NumberField K] → WeierstrassCurve K → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → Prop
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `hasGoodReductionAt_baseChange`

```lean
@hasGoodReductionAt_baseChange : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] {R : Type u_1}
  [inst_2 : CommRing R] [inst_3 : Algebra R (NumberField.RingOfIntegers K)] [inst_4 : Algebra R K]
  [IsScalarTower R (NumberField.RingOfIntegers K) K] (W₀ : WeierstrassCurve R)
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
  (algebraMap R (NumberField.RingOfIntegers K)) W₀.Δ ∉ v.asIdeal → HasGoodReductionAt (W₀.baseChange K) v
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.hasGoodReductionAt_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `map_map_ofId`

```lean
@map_map_ofId : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (W : WeierstrassCurve K) {E F : Type}
  [inst_2 : Field E] [inst_3 : Field F] [inst_4 : Algebra K E] [inst_5 : Algebra K F] [inst_6 : DecidableEq E]
  [inst_7 : DecidableEq F] (f : E →ₐ[K] F) (X : (W.baseChange K).toAffine.Point),
  (WeierstrassCurve.Affine.Point.map f) ((WeierstrassCurve.Affine.Point.map (Algebra.ofId K E)) X) =
    (WeierstrassCurve.Affine.Point.map (Algebra.ofId K F)) X
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.map_map_ofId' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `closurePoint`

```lean
@closurePoint : {K : Type} →
  [inst : Field K] →
    [DecidableEq K] → (W : WeierstrassCurve K) → W.toAffine.Point → (W.baseChange (AlgebraicClosure K)).toAffine.Point
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.closurePoint' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `map_closurePoint`

```lean
@map_closurePoint : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (W : WeierstrassCurve K)
  (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) (P : W.toAffine.Point),
  (WeierstrassCurve.Affine.Point.map σ) (closurePoint W P) = closurePoint W P
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.map_closurePoint' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `divisionPoints`

```lean
@divisionPoints : {K : Type} →
  [inst : Field K] →
    [DecidableEq K] →
      (W : WeierstrassCurve K) → ℕ → W.toAffine.Point → Set (W.baseChange (AlgebraicClosure K)).toAffine.Point
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.divisionPoints' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `divisionCoords`

```lean
@divisionCoords : {K : Type} →
  [inst : Field K] → [DecidableEq K] → (W : WeierstrassCurve K) → ℕ → W.toAffine.Point → Set (AlgebraicClosure K)
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.divisionCoords' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `divisionField`

```lean
@divisionField : {K : Type} →
  [inst : Field K] →
    [DecidableEq K] → (W : WeierstrassCurve K) → ℕ → W.toAffine.Point → IntermediateField K (AlgebraicClosure K)
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.divisionField' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `exists_mem_divisionPoints`

```lean
@exists_mem_divisionPoints : ∀ {K : Type} [inst : Field K] [NumberField K] [inst_2 : DecidableEq K]
  (W : WeierstrassCurve K) [W.IsElliptic] {m : ℕ},
  m ≠ 0 → ∀ (P : W.toAffine.Point), ∃ (Q : (W.baseChange (AlgebraicClosure K)).toAffine.Point), Q ∈ divisionPoints W m P
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.exists_mem_divisionPoints' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `finite_divisionPoints`

```lean
@finite_divisionPoints : ∀ {K : Type} [inst : Field K] [NumberField K] [inst_2 : DecidableEq K] (W : WeierstrassCurve K)
  [W.IsElliptic] {m : ℕ}, m ≠ 0 → ∀ (P : W.toAffine.Point), (divisionPoints W m P).Finite
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.finite_divisionPoints' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `finite_divisionCoords`

```lean
@finite_divisionCoords : ∀ {K : Type} [inst : Field K] [NumberField K] [inst_2 : DecidableEq K] (W : WeierstrassCurve K)
  [W.IsElliptic] {m : ℕ}, m ≠ 0 → ∀ (P : W.toAffine.Point), (divisionCoords W m P).Finite
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.finite_divisionCoords' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `finiteDimensional_divisionField`

```lean
@finiteDimensional_divisionField : ∀ {K : Type} [inst : Field K] [NumberField K] [inst_2 : DecidableEq K]
  (W : WeierstrassCurve K) [W.IsElliptic] {m : ℕ},
  m ≠ 0 → ∀ (P : W.toAffine.Point), FiniteDimensional K ↥(divisionField W m P)
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.finiteDimensional_divisionField' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `map_mem_divisionPoints`

```lean
@map_mem_divisionPoints : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (W : WeierstrassCurve K)
  (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) {m : ℕ} {P : W.toAffine.Point}
  {Q : (W.baseChange (AlgebraicClosure K)).toAffine.Point},
  Q ∈ divisionPoints W m P → (WeierstrassCurve.Affine.Point.map σ) Q ∈ divisionPoints W m P
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.map_mem_divisionPoints' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `normal_divisionField`

```lean
@normal_divisionField : ∀ {K : Type} [inst : Field K] [inst_1 : DecidableEq K] (W : WeierstrassCurve K) (m : ℕ)
  (P : W.toAffine.Point), Normal K ↥(divisionField W m P)
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.normal_divisionField' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `isUnramifiedOutside_divisionField`

```lean
@isUnramifiedOutside_divisionField : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] [inst_2 : DecidableEq K]
  (W : WeierstrassCurve K) [W.IsElliptic] {m : ℕ},
  m ≠ 0 →
    ∀ (S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))),
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑m ∈ v.asIdeal → v ∈ S0) →
        (∀ v ∉ S0, HasGoodReductionAt W v) →
          ∀ (P : W.toAffine.Point), ZInQ.Contrib.CloudB3RC53.RankCounts.IsUnramifiedOutside K S0 (divisionField W m P)
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.isUnramifiedOutside_divisionField' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `divisionField_le_unramifiedOutside`

```lean
@divisionField_le_unramifiedOutside : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] [inst_2 : DecidableEq K]
  (W : WeierstrassCurve K) [W.IsElliptic] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {m : ℕ},
  m ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑m ∈ v.asIdeal → v ∈ S0) →
      (∀ v ∉ S0, HasGoodReductionAt W v) →
        ∀ (P : W.toAffine.Point), divisionField W m P ≤ ZInQ.Contrib.CloudB3RC53.RankCounts.unramifiedOutside K S0
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.divisionField_le_unramifiedOutside' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `iSup_divisionField_le_unramifiedOutside`

```lean
@iSup_divisionField_le_unramifiedOutside : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {m : ℕ},
  m ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑m ∈ v.asIdeal → v ∈ S0) →
      (∀ v ∉ S0, HasGoodReductionAt W v) →
        ⨆ (P : W.toAffine.Point), divisionField W m P ≤ ZInQ.Contrib.CloudB3RC53.RankCounts.unramifiedOutside K S0
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.iSup_divisionField_le_unramifiedOutside' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `exists_supportPoint_map_eq`

```lean
@exists_supportPoint_map_eq : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] [inst_2 : DecidableEq K]
  (W : WeierstrassCurve K) [W.IsElliptic] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {m : ℕ},
  m ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑m ∈ v.asIdeal → v ∈ S0) →
      (∀ v ∉ S0, HasGoodReductionAt W v) →
        ∀ (P : W.toAffine.Point) (R : (W.baseChange (AlgebraicClosure K)).toAffine.Point),
          m • R = closurePoint W P →
            ∃ (Q : (W.baseChange (ZInQ.Manuscript.RC.CoefModules.KS K S0)).toAffine.Point),
              (WeierstrassCurve.Affine.Point.map (ZInQ.Contrib.CloudB3RC53.RankCounts.unramifiedOutside K S0).val) Q = R
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.exists_supportPoint_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `exists_nsmul_eq_supportBasePoint`

```lean
@exists_nsmul_eq_supportBasePoint : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] [inst_2 : DecidableEq K]
  (W : WeierstrassCurve K) [W.IsElliptic] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {m : ℕ},
  m ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑m ∈ v.asIdeal → v ∈ S0) →
      (∀ v ∉ S0, HasGoodReductionAt W v) →
        ∀ (P : W.toAffine.Point),
          ∃ (Q : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.SupportPoints W),
            m • Q = (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportBasePoint W) P
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.exists_nsmul_eq_supportBasePoint' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `natCast_mem_of_two_pow`

```lean
@natCast_mem_of_two_pow : ∀ {K : Type} [inst : Field K]
  {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {i : ℕ}, ↑(2 ^ i) ∈ v.asIdeal → 2 ∈ v.asIdeal
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.natCast_mem_of_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `globalDivisionPointsInSupport_of_goodReduction`

```lean
@globalDivisionPointsInSupport_of_goodReduction : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))},
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), 2 ∈ v.asIdeal → v ∈ S0) →
    (∀ v ∉ S0, HasGoodReductionAt W v) →
      ∀ (i : ℕ), ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport W i
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.globalDivisionPointsInSupport_of_goodReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `fullTorsion_of_goodReduction`

```lean
@fullTorsion_of_goodReduction : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] [DecidableEq K]
  (W : WeierstrassCurve K) [W.IsElliptic] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {N : ℕ},
  N ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), ↑N ∈ v.asIdeal → v ∈ S0) →
      (∀ v ∉ S0, HasGoodReductionAt W v) → ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W N
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.fullTorsion_of_goodReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `fullTorsion_two_pow_of_goodReduction`

```lean
@fullTorsion_two_pow_of_goodReduction : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] [DecidableEq K]
  (W : WeierstrassCurve K) [W.IsElliptic]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))},
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), 2 ∈ v.asIdeal → v ∈ S0) →
    (∀ v ∉ S0, HasGoodReductionAt W v) → ∀ (i : ℕ), ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 W (2 ^ i)
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.fullTorsion_two_pow_of_goodReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `supportDivisionPoint_spec_of_goodReduction`

```lean
@supportDivisionPoint_spec_of_goodReduction : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : DecidableEq K] (W : WeierstrassCurve K) [inst_3 : W.IsElliptic]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), 2 ∈ v.asIdeal → v ∈ S0)
  (hgood : ∀ v ∉ S0, HasGoodReductionAt W v) (i : ℕ) (P : W.toAffine.Point),
  2 ^ i • ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportDivisionPoint W i ⋯ P =
    (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.supportBasePoint W) P
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.supportDivisionPoint_spec_of_goodReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `globalDivisionPointsInSupport_of_baseChange`

```lean
@globalDivisionPointsInSupport_of_baseChange : ∀ {K : Type} [inst : Field K] [NumberField K] [inst_2 : DecidableEq K]
  {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {R : Type u_1} [inst_3 : CommRing R]
  [inst_4 : Algebra R (NumberField.RingOfIntegers K)] [inst_5 : Algebra R K]
  [IsScalarTower R (NumberField.RingOfIntegers K) K] (W₀ : WeierstrassCurve R) [(W₀.baseChange K).IsElliptic],
  (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), 2 ∈ v.asIdeal → v ∈ S0) →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        (algebraMap R (NumberField.RingOfIntegers K)) W₀.Δ ∈ v.asIdeal → v ∈ S0) →
      ∀ (i : ℕ),
        ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport (W₀.baseChange K) i ∧
          ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 (W₀.baseChange K) (2 ^ i)
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.globalDivisionPointsInSupport_of_baseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `goodReductionKummerMap`

```lean
@goodReductionKummerMap : {K : Type} →
  [inst : Field K] →
    [inst_1 : NumberField K] →
      [inst_2 : DecidableEq K] →
        (W : WeierstrassCurve K) →
          [inst_3 : W.IsElliptic] →
            {S0 S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} →
              (hS : S0 ⊆ S) →
                (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) →
                  (h2 :
                      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
                        2 ∈ v.asIdeal → v ∈ S0) →
                    (hgood : ∀ v ∉ S0, HasGoodReductionAt W v) →
                      (i : ℕ) →
                        W.toAffine.Point →+
                          ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.cochainClasses
                            (ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.centralSelData W i hS ⋯ Pold)
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.goodReductionKummerMap' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `centralRetainedStage_exists_witness_of_goodReduction`

```lean
@centralRetainedStage_exists_witness_of_goodReduction : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : DecidableEq K] (W : WeierstrassCurve K) [inst_3 : W.IsElliptic]
  {S0 S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hS : S0 ⊆ S)
  (Pold : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
  (h2 : ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), 2 ∈ v.asIdeal → v ∈ S0)
  (hgood : ∀ v ∉ S0, HasGoodReductionAt W v) (i : ℕ) {P : W.toAffine.Point}
  (T : ZInQ.Manuscript.RC.BaseZeroAssembly.SplitNormStage P) (L : ℤ) (N M0 : ℕ)
  (C : ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.CentralRetainedInput W i hS ⋯ Pold ⋯ T L N M0),
  ∃ (v : Fin M0 → ℤ_[2]),
    ∀ (a : Fin N),
      C.zeta a - ↑(L * (T.a - 2)) * C.jay a - C.dC.mulVec v a ∈ ZInQ.Manuscript.RC.BaseZeroLimit.twoAdicStage i
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.centralRetainedStage_exists_witness_of_goodReduction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `valuation_natCast_eq_one`

```lean
@valuation_natCast_eq_one : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {n : ℕ},
  ↑n ∉ v.asIdeal → (IsDedekindDomain.HeightOneSpectrum.valuation K v) ↑n = 1
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.valuation_natCast_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `hasGoodReductionAt_cubicCurve`

```lean
@hasGoodReductionAt_cubicCurve : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {e₁ e₂ e₃ : K},
  (IsDedekindDomain.HeightOneSpectrum.valuation K v) e₁ ≤ 1 →
    (IsDedekindDomain.HeightOneSpectrum.valuation K v) e₂ ≤ 1 →
      (IsDedekindDomain.HeightOneSpectrum.valuation K v) e₃ ≤ 1 →
        2 ∉ v.asIdeal →
          (IsDedekindDomain.HeightOneSpectrum.valuation K v) ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) = 1 →
            HasGoodReductionAt (ZInQ.Manuscript.RC.CoefModules.cubicCurve e₁ e₂ e₃) v
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.hasGoodReductionAt_cubicCurve' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `hasGoodReductionAt_curveEll`

```lean
@hasGoodReductionAt_curveEll : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {ℓ : K},
  (IsDedekindDomain.HeightOneSpectrum.valuation K v) ℓ = 1 →
    2 ∉ v.asIdeal → 3 ∉ v.asIdeal → HasGoodReductionAt (ZInQ.Manuscript.RC.CoefModules.curveEll ℓ) v
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.hasGoodReductionAt_curveEll' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `globalDivisionPointsInSupport_curveEll`

```lean
@globalDivisionPointsInSupport_curveEll : ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K]
  [inst_2 : DecidableEq K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {ℓ : K},
  ℓ ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), 2 ∈ v.asIdeal → v ∈ S0) →
      (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), 3 ∈ v.asIdeal → v ∈ S0) →
        (∀ v ∉ S0, (IsDedekindDomain.HeightOneSpectrum.valuation K v) ℓ = 1) →
          ∀ (i : ℕ),
            ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport
                (ZInQ.Manuscript.RC.CoefModules.curveEll ℓ) i ∧
              ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0 (ZInQ.Manuscript.RC.CoefModules.curveEll ℓ) (2 ^ i)
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.globalDivisionPointsInSupport_curveEll' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## `globalDivisionPointsInSupport_curveEll_of_integer`

```lean
@globalDivisionPointsInSupport_curveEll_of_integer : ∀ {K : Type} [inst : Field K] [NumberField K]
  [inst_2 : DecidableEq K] {S0 : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
  {ℓ : NumberField.RingOfIntegers K},
  ℓ ≠ 0 →
    (∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)), 6 * ℓ ∈ v.asIdeal → v ∈ S0) →
      ∀ (i : ℕ),
        ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.GlobalDivisionPointsInSupport
            (ZInQ.Manuscript.RC.CoefModules.curveEll ((algebraMap (NumberField.RingOfIntegers K) K) ℓ)) i ∧
          ZInQ.Manuscript.RC.CoefModules.FullTorsion K S0
            (ZInQ.Manuscript.RC.CoefModules.curveEll ((algebraMap (NumberField.RingOfIntegers K) K) ℓ)) (2 ^ i)
```

```text
'ZInQ.Manuscript.RC.DivisionPoints.globalDivisionPointsInSupport_curveEll_of_integer' depends on axioms: [propext, Classical.choice, Quot.sound]
```
