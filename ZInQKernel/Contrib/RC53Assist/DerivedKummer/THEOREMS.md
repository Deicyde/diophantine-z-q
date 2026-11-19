# Exact Lean statements and axiom reports

All 35 new theorems were checked by standalone single-file compilation. Each block below reproduces its exact `#check` output with full declaration names and its verbatim `#print axioms` result. All lists are exactly `[propext, Classical.choice, Quot.sound]`.

These kernel dependency lists do not discharge the named Milne Prop inputs or the displayed completion, trace, and chain-model identification hypotheses. Those boundaries are described in REPORT.md and in the theorem types below.

## LocalDuality.lean

### `ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.right_injective`

Source: `LocalDuality.lean:67`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.right_injective.{u_1, u_2} {P : Type u_1} {C : Type u_2}
  [AddCommGroup P] [AddCommGroup C] (D : ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData P C) :
  Function.Injective ⇑D.pairing.flip
'ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.right_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.nondegenerate_right`

Source: `LocalDuality.lean:72`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.nondegenerate_right.{u_1, u_2} {P : Type u_1} {C : Type u_2}
  [AddCommGroup P] [AddCommGroup C] (D : ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData P C) (c : C)
  (hc : ∀ (p : P), (D.pairing p) c = 0) : c = 0
'ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.nondegenerate_right' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.pointMod_nsmul_mk`

Source: `LocalDuality.lean:80`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.pointMod_nsmul_mk.{u_1} {P : Type u_1} [AddCommGroup P] (n : ℕ)
  (p : P) : n • ↑p = 0
'ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.pointMod_nsmul_mk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.modPair_mk`

Source: `LocalDuality.lean:109`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.modPair_mk.{u_1, u_2} {P : Type u_1} {C : Type u_2}
  [AddCommGroup P] [AddCommGroup C] (D : ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData P C) (n : ℕ)
  (c : ↥(AddSubgroup.torsionBy C ↑n)) (p : P) : ((D.modPair n) c) ↑p = (D.pairing p) ↑c
'ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.modPair_mk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.modPair_bijective`

Source: `LocalDuality.lean:115`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.modPair_bijective.{u_1, u_2} {P : Type u_1} {C : Type u_2}
  [AddCommGroup P] [AddCommGroup C] (D : ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData P C) (n : ℕ)
  (hn : 0 < n) : Function.Bijective ⇑(D.modPair n)
'ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.modPair_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.MilneCompatiblePairings.toRC53`

Source: `LocalDuality.lean:160`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.MilneCompatiblePairings.toRC53 {F : Type} [Field F] [DecidableEq F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
  (D : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneCompatiblePairings B) (n : ℕ) (hn : IsUnit ↑n) :
  ZInQ.Contrib.CloudB3RC53.Duality.MilneLocalTateDualityKummer B n hn
'ZInQ.Contrib.RC53Assist.DerivedKummer.MilneCompatiblePairings.toRC53' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_exact_annihilator`

Source: `LocalDuality.lean:166`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_exact_annihilator {F : Type} [Field F] [DecidableEq F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
  (D : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneCompatiblePairings B) (n : ℕ) (hn : IsUnit ↑n)
  (y : TauCeti.ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (B.TorsionCoeff n)) :
  y ∈ (B.kummerMap n hn).range ↔
    ∀ x ∈ (B.kummerMap n hn).range, ((ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B n hn) x) y = 0
'ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_exact_annihilator' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_finite_isotropy`

Source: `LocalDuality.lean:174`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_finite_isotropy {F : Type} [Field F] [DecidableEq F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
  (D : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneCompatiblePairings B) (n : ℕ) (hn : IsUnit ↑n)
  (p q : B.toAffine.Point) :
  ((ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B n hn) ((B.kummerMap n hn) p)) ((B.kummerMap n hn) q) = 0
'ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_finite_isotropy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.ker_torsion_projection`

Source: `LocalDuality.lean:181`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.ker_torsion_projection {F : Type} [Field F] [DecidableEq F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic] (n : ℕ) (hn : IsUnit ↑n) :
  (B.torsionCoeffInclH1 n).ker = (B.kummerMap n hn).range
'ZInQ.Contrib.RC53Assist.DerivedKummer.ker_torsion_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.kummerQuotientComparison_mk`

Source: `LocalDuality.lean:204`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.kummerQuotientComparison_mk {F : Type} [Field F] [DecidableEq F] [ValuativeRel F]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
  (D : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneCompatiblePairings B) (n : ℕ) (hn : IsUnit ↑n)
  (y : TauCeti.ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (B.TorsionCoeff n)) (p : B.toAffine.Point) :
  ((ZInQ.Contrib.RC53Assist.DerivedKummer.kummerQuotientComparison B D n hn) ↑y) ↑p =
    ((ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B n hn) ((B.kummerMap n hn) p)) y
'ZInQ.Contrib.RC53Assist.DerivedKummer.kummerQuotientComparison_mk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.kummerQuotientComparison_bijective`

Source: `LocalDuality.lean:213`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.kummerQuotientComparison_bijective {F : Type} [Field F] [DecidableEq F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
  (D : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneCompatiblePairings B) (n : ℕ) (hn : IsUnit ↑n) :
  Function.Bijective ⇑(ZInQ.Contrib.RC53Assist.DerivedKummer.kummerQuotientComparison B D n hn)
'ZInQ.Contrib.RC53Assist.DerivedKummer.kummerQuotientComparison_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_exact_annihilator_of_print`

Source: `LocalDuality.lean:259`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_exact_annihilator_of_print
  (hM : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneLocalDualityPrint) (F : Type) [Field F] [DecidableEq F] [CharZero F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic] (n : ℕ)
  (hn : IsUnit ↑n) (y : TauCeti.ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (B.TorsionCoeff n)) :
  y ∈ (B.kummerMap n hn).range ↔
    ∀ x ∈ (B.kummerMap n hn).range, ((ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B n hn) x) y = 0
'ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_exact_annihilator_of_print' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_modTwo_comparison_of_print`

Source: `LocalDuality.lean:271`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_modTwo_comparison_of_print
  (hM : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneLocalDualityPrint) (F : Type) [Field F] [DecidableEq F] [CharZero F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
  (h2 : IsUnit 2) :
  ∃ e,
    ∀ (y : TauCeti.ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (B.TorsionCoeff 2)) (p : B.toAffine.Point),
      (e ↑y) ↑p = ((ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 h2) ((B.kummerMap 2 h2) p)) y
'ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_modTwo_comparison_of_print' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.circleTorsionEquiv_toRat`

Source: `LocalDuality.lean:306`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.circleTorsionEquiv_toRat (n : ℕ) [NeZero n]
  (z : ↥(AddSubgroup.torsionBy ZInQ.Contrib.RC53Assist.DerivedKummer.RationalCircle ↑n)) :
  (ZMod.toRatAddCircle n) ((ZInQ.Contrib.RC53Assist.DerivedKummer.circleTorsionEquiv n) z) = ↑z
'ZInQ.Contrib.RC53Assist.DerivedKummer.circleTorsionEquiv_toRat' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.charactersToZMod_apply`

Source: `LocalDuality.lean:332`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.charactersToZMod_apply.{u_1} (n : ℕ) [NeZero n] {V : Type u_1} [AddCommGroup V]
  (hV : ∀ (v : V), n • v = 0) (ψ : V →+ ZInQ.Contrib.RC53Assist.DerivedKummer.RationalCircle) (v : V) :
  (ZMod.toRatAddCircle n) (((ZInQ.Contrib.RC53Assist.DerivedKummer.charactersToZMod n hV) ψ) v) = ψ v
'ZInQ.Contrib.RC53Assist.DerivedKummer.charactersToZMod_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.pointModTwo_nsmul`

Source: `LocalDuality.lean:346`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.pointModTwo_nsmul.{u_1} (P : Type u_1) [AddCommGroup P]
  (q : ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.pointMod 2) : 2 • q = 0
'ZInQ.Contrib.RC53Assist.DerivedKummer.pointModTwo_nsmul' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.kummerModTwoLinearComparison_bijective`

Source: `LocalDuality.lean:381`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.kummerModTwoLinearComparison_bijective {F : Type} [Field F] [DecidableEq F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
  (D : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneCompatiblePairings B) (h2 : IsUnit 2) :
  Function.Bijective ⇑(ZInQ.Contrib.RC53Assist.DerivedKummer.kummerModTwoLinearComparison B D h2)
'ZInQ.Contrib.RC53Assist.DerivedKummer.kummerModTwoLinearComparison_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.kummerModTwoLinearComparison_mk`

Source: `LocalDuality.lean:388`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.kummerModTwoLinearComparison_mk {F : Type} [Field F] [DecidableEq F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
  (D : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneCompatiblePairings B) (h2 : IsUnit 2)
  (y : TauCeti.ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (B.TorsionCoeff 2)) (p : B.toAffine.Point) :
  (ZMod.toRatAddCircle 2) (((ZInQ.Contrib.RC53Assist.DerivedKummer.kummerModTwoLinearComparison B D h2) ↑y) ↑p) =
    ((ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 h2) ((B.kummerMap 2 h2) p)) y
'ZInQ.Contrib.RC53Assist.DerivedKummer.kummerModTwoLinearComparison_mk' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_modTwo_linear_comparison_of_print`

Source: `LocalDuality.lean:453`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_modTwo_linear_comparison_of_print
  (hM : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneLocalDualityPrint) (F : Type) [Field F] [DecidableEq F] [CharZero F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
  (h2 : IsUnit 2) :
  ∃ e,
    ∀ (y : TauCeti.ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (B.TorsionCoeff 2)) (p : B.toAffine.Point),
      (ZMod.toRatAddCircle 2) ((e ↑y) ↑p) =
        ((ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 h2) ((B.kummerMap 2 h2) p)) y
'ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_modTwo_linear_comparison_of_print' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_modTwo_torsion_comparison_of_print`

Source: `LocalDuality.lean:469`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_modTwo_torsion_comparison_of_print
  (hM : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneFiniteLocalDualityPrint) (F : Type) [Field F] [DecidableEq F]
  [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F)
  [B.IsElliptic] (h2 : IsUnit 2) :
  ∃ e,
    ∀ (y : TauCeti.ContCohomology.H2 (TauCeti.AbsoluteGaloisGroup F) (B.TorsionCoeff 2))
      (t : ↥(AddSubgroup.torsionBy B.toAffine.Point 2)),
      (ZMod.toRatAddCircle 2) ((e y) t) = ZInQ.Contrib.RC53Assist.DerivedKummer.localH2TorsionValue B 2 h2 y t
'ZInQ.Contrib.RC53Assist.DerivedKummer.kummer_modTwo_torsion_comparison_of_print' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.padicInvariant_eq_zero_iff`

Source: `LocalDuality.lean:499`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.padicInvariant_eq_zero_iff (a : ℕ) (z : ℤ_[2]) :
  (ZInQ.Contrib.RC53Assist.DerivedKummer.padicInvariant a) z = 0 ↔ 2 ^ a ∣ z
'ZInQ.Contrib.RC53Assist.DerivedKummer.padicInvariant_eq_zero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.twoPower_isUnit`

Source: `LocalDuality.lean:509`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.twoPower_isUnit (F : Type) [Field F] [CharZero F] (a : ℕ) : IsUnit ↑(2 ^ a)
'ZInQ.Contrib.RC53Assist.DerivedKummer.twoPower_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.actualCup_divisible_of_print`

Source: `LocalDuality.lean:516`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.actualCup_divisible_of_print.{u_1, u_2}
  (hM : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneLocalDualityPrint) (F : Type) [Field F] [DecidableEq F] [CharZero F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (B : WeierstrassCurve F) [B.IsElliptic]
  {X : Type u_1} {Y : Type u_2} (β : X → Y → ℤ_[2])
  (hred :
    ∀ (a : ℕ) (x : X) (y : Y),
      ∃ p q,
        (ZInQ.Contrib.RC53Assist.DerivedKummer.padicInvariant a) (β x y) =
          ((ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B (2 ^ a) ⋯) ((B.kummerMap (2 ^ a) ⋯) p))
            ((B.kummerMap (2 ^ a) ⋯) q))
  (a : ℕ) (x : X) (y : Y) : 2 ^ a ∣ β x y
'ZInQ.Contrib.RC53Assist.DerivedKummer.actualCup_divisible_of_print' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.derived_modTwo_comparisons_of_print`

Source: `LocalDuality.lean:611`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.derived_modTwo_comparisons_of_print.{u_1, u_2, u_3} {F : Type} [Field F]
  [DecidableEq F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (B : WeierstrassCurve F) [B.IsElliptic] {P₁ : Type u_1} {P₀ : Type u_2} {M : Type u_3} [AddCommGroup P₁]
  [Module ℤ_[2] P₁] [AddCommGroup P₀] [Module ℤ_[2] P₀] [AddCommGroup M] [Module ℤ_[2] M] (f : P₁ →ₗ[ℤ_[2]] P₀)
  (g : P₀ →ₗ[ℤ_[2]] M) (hM : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneLocalDualityPrint)
  (hF : ZInQ.Contrib.RC53Assist.DerivedKummer.MilneFiniteLocalDualityPrint) (h2 : IsUnit 2) (hfg : g ∘ₗ f = 0)
  (hf : Function.Injective ⇑f) (hg : Function.Surjective ⇑g) (hex : ∀ (y : P₀), g y = 0 → ∃ x, f x = y)
  (hreg : IsSMulRegular P₀ 2)
  (η₀ : ↥(ZInQ.Contrib.CloudB3RC53.Duality.torsionN 2 M) ≃+ ↥(AddSubgroup.torsionBy B.toAffine.Point 2))
  (η₁ :
    M ⧸ ZInQ.Contrib.CloudB3RC53.Duality.nSub 2 M ≃+ ZInQ.Contrib.RC53Assist.DerivedKummer.TateDualityData.pointMod 2) :
  (∃ e,
      ∀ (y : TauCeti.ContCohomology.H1 (TauCeti.AbsoluteGaloisGroup F) (B.TorsionCoeff 2))
        (r : ZInQ.Contrib.RC53Assist.DerivedKummer.reductionH1 f) (p : B.toAffine.Point),
        (ZInQ.Contrib.RC53Assist.DerivedKummer.derivedH1Identification B f g hfg hg hex η₁) r = ↑p →
          (e ↑y) r = ((ZInQ.Contrib.CloudB3RC53.Duality.localTatePairing B 2 h2) ((B.kummerMap 2 h2) p)) y) ∧
    ∃ e,
      ∀ (y : TauCeti.ContCohomology.H2 (TauCeti.AbsoluteGaloisGroup F) (B.TorsionCoeff 2))
        (r : ↥(ZInQ.Contrib.RC53Assist.DerivedKummer.reductionH0 f)),
        (e y) r =
          ZInQ.Contrib.RC53Assist.DerivedKummer.localH2TorsionValue B 2 h2 y
            ((ZInQ.Contrib.RC53Assist.DerivedKummer.derivedH0Identification B f g hfg hf hg hex hreg η₀) r)
'ZInQ.Contrib.RC53Assist.DerivedKummer.derived_modTwo_comparisons_of_print' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## ComparisonAlgebra.lean

### `ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.coneR_isExact_of_cohomology`

Source: `ComparisonAlgebra.lean:47`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.coneR_isExact_of_cohomology.{u_1, u_2, u_3, u_4, u_5} {R : Type u_1}
  [CommRing R] {κe : Type u_2} {κo : Type u_3} {κe' : Type u_4} {κo' : Type u_5} [Fintype κe] [Fintype κo] [Fintype κe']
  [Fintype κo'] [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx R κe κo} {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx R κe' κo'}
  (f : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapR C D)
  (h : ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.CohomologyComparison f) :
  (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.coneR f).IsExact
'ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.coneR_isExact_of_cohomology' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.comparison_of_models`

Source: `ComparisonAlgebra.lean:163`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.comparison_of_models.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9}
  {R : Type u_1} [CommRing R] {κe : Type u_2} {κo : Type u_3} {κe' : Type u_4} {κo' : Type u_5} [Fintype κe]
  [Fintype κo] [Fintype κe'] [Fintype κo'] [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx R κe κo} {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx R κe' κo'}
  {HE : Type u_6} {HO : Type u_7} {HE' : Type u_8} {HO' : Type u_9} [AddCommGroup HE] [Module R HE] [AddCommGroup HO]
  [Module R HO] [AddCommGroup HE'] [Module R HE'] [AddCommGroup HO'] [Module R HO']
  (f : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapR C D)
  (M : ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.CohomologyModel C HE HO)
  (N : ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.CohomologyModel D HE' HO') (αE : HE →ₗ[R] HE')
  (αO : HO →ₗ[R] HO') (hE : Function.Bijective ⇑αE) (hO : Function.Bijective ⇑αO)
  (commE :
    ∀ (x : ↥(ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cyclesE C)),
      N.classE ((ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cycleMapE f) x) = αE (M.classE x))
  (commO :
    ∀ (x : ↥(ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cyclesO C)),
      N.classO ((ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cycleMapO f) x) = αO (M.classO x)) :
  ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.CohomologyComparison f
'ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.comparison_of_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.contraction_of_cohomology`

Source: `ComparisonAlgebra.lean:209`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.contraction_of_cohomology.{u_2, u_3, u_4, u_5, u_10} {κe : Type u_2}
  {κo : Type u_3} {κe' : Type u_4} {κo' : Type u_5} [Fintype κe] [Fintype κo] [Fintype κe'] [Fintype κo']
  [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo'] {K : Type u_10} [Field K]
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx K κe κo} {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx K κe' κo'}
  (f : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapR C D)
  (h : ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.CohomologyComparison f) :
  Nonempty (ZInQ.Contrib.CloudB3RC53.Torsion.Contraction (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.coneR f))
'ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.contraction_of_cohomology' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.nakayama_comparison_of_models`

Source: `ComparisonAlgebra.lean:227`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.nakayama_comparison_of_models.{u_1, u_2, u_3, u_4, u_5, u_10, u_11,
    u_12, u_13}
  {R : Type u_1} [CommRing R] {κe : Type u_2} {κo : Type u_3} {κe' : Type u_4} {κo' : Type u_5} [Fintype κe]
  [Fintype κo] [Fintype κe'] [Fintype κo'] [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo']
  [IsLocalRing R] {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx R κe κo}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx R κe' κo'} {VE : Type u_10} {VO : Type u_11} {VE' : Type u_12}
  {VO' : Type u_13} [AddCommGroup VE] [Module (IsLocalRing.ResidueField R) VE] [AddCommGroup VO]
  [Module (IsLocalRing.ResidueField R) VO] [AddCommGroup VE'] [Module (IsLocalRing.ResidueField R) VE']
  [AddCommGroup VO'] [Module (IsLocalRing.ResidueField R) VO'] (f : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapR C D)
  (M :
    ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.CohomologyModel
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.map (IsLocalRing.residue R) C) VE VO)
  (N :
    ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.CohomologyModel
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.map (IsLocalRing.residue R) D) VE' VO')
  (αE : VE →ₗ[IsLocalRing.ResidueField R] VE') (αO : VO →ₗ[IsLocalRing.ResidueField R] VO')
  (hE : Function.Bijective ⇑αE) (hO : Function.Bijective ⇑αO)
  (commE :
    ∀
      (x :
        ↥(ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cyclesE
            (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.map (IsLocalRing.residue R) C))),
      N.classE
          ((ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cycleMapE
              (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapR.map (IsLocalRing.residue R) f))
            x) =
        αE (M.classE x))
  (commO :
    ∀
      (x :
        ↥(ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cyclesO
            (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.map (IsLocalRing.residue R) C))),
      N.classO
          ((ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cycleMapO
              (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapR.map (IsLocalRing.residue R) f))
            x) =
        αO (M.classO x)) :
  Nonempty (ZInQ.Contrib.CloudB3RC53.Torsion.Contraction (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.coneR f))
'ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.nakayama_comparison_of_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.based_map_comp`

Source: `ComparisonAlgebra.lean:263`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.based_map_comp.{u_1, u_2, u_3, u_10, u_11} {R : Type u_1} [CommRing R]
  {κe : Type u_2} {κo : Type u_3} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo] {S : Type u_10}
  {T : Type u_11} [CommRing S] [CommRing T] (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx R κe κo) (π : R →+* S)
  (ρ : S →+* T) :
  ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.map ρ (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.map π C) =
    ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.map (ρ.comp π) C
'ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.based_map_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.residue_eq_comp_modTwo`

Source: `ComparisonAlgebra.lean:269`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.residue_eq_comp_modTwo :
  PadicInt.residueField.symm.toRingHom.comp PadicInt.toZMod = IsLocalRing.residue ℤ_[2]
'ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.residue_eq_comp_modTwo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.nakayama_comparison_modTwo`

Source: `ComparisonAlgebra.lean:290`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.nakayama_comparison_modTwo.{u_2, u_3, u_4, u_5} {κe : Type u_2}
  {κo : Type u_3} {κe' : Type u_4} {κo' : Type u_5} [Fintype κe] [Fintype κo] [Fintype κe'] [Fintype κo']
  [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx ℤ_[2] κe κo}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx ℤ_[2] κe' κo'} (f : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapR C D)
  (hbar :
    ZInQ.Contrib.CloudB3RC53.Torsion.Contraction
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.coneR
        (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapR.map PadicInt.toZMod f))) :
  Nonempty (ZInQ.Contrib.CloudB3RC53.Torsion.Contraction (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.coneR f))
'ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.nakayama_comparison_modTwo' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.nakayama_comparison_of_modTwo_models`

Source: `ComparisonAlgebra.lean:305`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.nakayama_comparison_of_modTwo_models.{u_2, u_3, u_4, u_5, u_10, u_11,
    u_12, u_13}
  {κe : Type u_2} {κo : Type u_3} {κe' : Type u_4} {κo' : Type u_5} [Fintype κe] [Fintype κo] [Fintype κe']
  [Fintype κo'] [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo'] {VE : Type u_10} {VO : Type u_11}
  {VE' : Type u_12} {VO' : Type u_13} [AddCommGroup VE] [Module (ZMod 2) VE] [AddCommGroup VO] [Module (ZMod 2) VO]
  [AddCommGroup VE'] [Module (ZMod 2) VE'] [AddCommGroup VO'] [Module (ZMod 2) VO']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx ℤ_[2] κe κo}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx ℤ_[2] κe' κo'} (f : ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapR C D)
  (M :
    ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.CohomologyModel
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.map PadicInt.toZMod C) VE VO)
  (N :
    ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.CohomologyModel
      (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.map PadicInt.toZMod D) VE' VO')
  (αE : VE →ₗ[ZMod 2] VE') (αO : VO →ₗ[ZMod 2] VO') (hE : Function.Bijective ⇑αE) (hO : Function.Bijective ⇑αO)
  (commE :
    ∀
      (x :
        ↥(ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cyclesE
            (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.map PadicInt.toZMod C))),
      N.classE
          ((ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cycleMapE
              (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapR.map PadicInt.toZMod f))
            x) =
        αE (M.classE x))
  (commO :
    ∀
      (x :
        ↥(ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cyclesO
            (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.map PadicInt.toZMod C))),
      N.classO
          ((ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.cycleMapO
              (ZInQ.Contrib.CloudB3RC53.Torsion.ChainMapR.map PadicInt.toZMod f))
            x) =
        αO (M.classO x)) :
  Nonempty (ZInQ.Contrib.CloudB3RC53.Torsion.Contraction (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.coneR f))
'ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison.nakayama_comparison_of_modTwo_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

## DegreeZero.lean

### `ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionToH0_bijective`

Source: `DegreeZero.lean:29`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionToH0_bijective {F : Type} [Field F] [DecidableEq F]
  (B : WeierstrassCurve F) (n : ℕ) :
  Function.Bijective ⇑(ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionToH0 B n)
'ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionToH0_bijective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionH0Equiv_apply`

Source: `DegreeZero.lean:45`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionH0Equiv_apply {F : Type} [Field F] [DecidableEq F]
  (B : WeierstrassCurve F) (n : ℕ) (t : ↥(AddSubgroup.torsionBy B.toAffine.Point ↑n)) :
  ↑((ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionH0Equiv B n) t) = (B.baseTorsionCoeff n) t
'ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionH0Equiv_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

### `ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionH0Equiv_point_apply`

Source: `DegreeZero.lean:50`

```lean
ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionH0Equiv_point_apply {F : Type} [Field F] [DecidableEq F]
  (B : WeierstrassCurve F) (n : ℕ) (t : ↥(AddSubgroup.torsionBy B.toAffine.Point ↑n)) :
  ↑↑((ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionH0Equiv B n) t) = B.basePointCoeff ↑t
'ZInQ.Contrib.RC53Assist.DerivedKummer.DegreeZero.torsionH0Equiv_point_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
