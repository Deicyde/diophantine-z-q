# Exact theorem statements and axiom reports

These are the complete declaration types printed by the individual-file Lean checks. Implicit parameters, universe parameters, and proof arguments are visible. The source files and full receipts are included alongside this inventory. All 48 theorems passed the kernel check; their hypotheses remain exactly those shown below.

## IntegralLattice.lean

### `ZInQ.Contrib.RC53Assist.StageCone.tau_baseChange`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.tau_baseChange.{u_1, u_2, u_3,
    u_4} : ∀ {A : Type u_1} {B : Type u_2} [inst : CommRing.{u_1} A] [inst_1 : CommRing.{u_2} B] {E : Type u_3}
  {O : Type u_4} [inst_2 : Fintype.{u_3} E] [inst_3 : Fintype.{u_4} O] [inst_4 : DecidableEq.{u_3 + 1} E]
  [inst_5 : DecidableEq.{u_4 + 1} O] (f : RingHom.{u_1, u_2} A B)
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{u_1, u_3, u_4} A E O)
  (h : ZInQ.Contrib.CloudB3RC53.Torsion.Contraction.{u_1, u_3, u_4} C) (s : Equiv.{u_3 + 1, u_4 + 1} E O),
  Eq.{u_2 + 1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.tau.{u_2, u_3, u_4}
      (ZInQ.Contrib.RC53Assist.StageCone.basedBaseChange.{u_1, u_2, u_3, u_4} f C)
      (ZInQ.Contrib.RC53Assist.StageCone.contractionBaseChange.{u_1, u_2, u_3, u_4} f h) s)
    (f (ZInQ.Contrib.CloudB3RC53.Torsion.tau.{u_1, u_3, u_4} C h s))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.tau_baseChange
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.tau_baseChange' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.torsion_baseChange`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.torsion_baseChange.{u_1, u_2, u_3,
    u_4} : ∀ {A : Type u_1} {B : Type u_2} [inst : CommRing.{u_1} A] [inst_1 : CommRing.{u_2} B] {E : Type u_3}
  {O : Type u_4} [inst_2 : Fintype.{u_3} E] [inst_3 : Fintype.{u_4} O] [inst_4 : DecidableEq.{u_3 + 1} E]
  [inst_5 : DecidableEq.{u_4 + 1} O] [IsDomain.{u_1} A] [IsDomain.{u_2} B] (f : RingHom.{u_1, u_2} A B)
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.{u_1, u_3, u_4} A E O)
  (h : ZInQ.Contrib.CloudB3RC53.Torsion.Contraction.{u_1, u_3, u_4} C) (s : Equiv.{u_3 + 1, u_4 + 1} E O),
  Eq.{u_2 + 1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_2, u_3, u_4}
      (ZInQ.Contrib.RC53Assist.StageCone.basedBaseChange.{u_1, u_2, u_3, u_4} f C) s)
    (f (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_1, u_3, u_4} C s))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.torsion_baseChange
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.torsion_baseChange' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.integralUnit_of_contractibleLift`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.integralUnit_of_contractibleLift : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} A F} {S : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  {M : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F} {z₀ l₀ : Fin 2 → F} [IsDomain.{0} A]
  (g : ZInQ.Contrib.CloudB3RC53.StageCone.StageMap S M z₀ l₀)
  (hz₀ :
    Eq.{1}
      (Matrix.mulVec.{0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M))
        z₀)
      0)
  (hl₀ :
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0} l₀
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M)))
      0)
  (H :
    ZInQ.Contrib.RC53Assist.StageCone.ContractibleIntegralLift.{0, 0, 0, 0} ι
      (ZInQ.Contrib.RC53Assist.StageCone.augmentedComparisonCone g hz₀ hl₀)),
  g.IntegralUnit hz₀ hl₀
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.integralUnit_of_contractibleLift
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.integralUnit_of_contractibleLift' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.exists_stageMap`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.exists_stageMap : ∀ {A F : Type} [inst : CommRing.{0} A] [inst_1 : Field.{0} F]
  {ι : RingHom.{0, 0} A F} (S : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι)
  (M : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F) (z₀ l₀ : Fin 2 → F),
  Eq.{1}
      (Matrix.mulVec.{0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M))
        z₀)
      0 →
    Eq.{1}
        (Matrix.vecMul.{0, 0, 0} l₀
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M)))
        0 →
      Ne.{1} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} S) 0 →
        Ne.{1}
            (Matrix.adjugate.{0, 0}
              (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.D.{0, 0} S) ⇑ι))
            0 →
          Ne.{1} l₀ 0 → Nonempty.{1} (ZInQ.Contrib.CloudB3RC53.StageCone.StageMap S M z₀ l₀)
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.exists_stageMap
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.exists_stageMap' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.stageConeComparison_iff_links`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.stageConeComparison_iff_links : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} A F} (S S' : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι)
  {ε σ : F},
  Ne.{1} ε 0 →
    Ne.{1} σ 0 →
      ∀ {J : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F} {v : Fin 2 → F},
        Ne.{1} v 0 →
          Ne.{1} (Matrix.mulVec.{0, 0, 0} J v) 0 →
            Ne.{1} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} S) 0 →
              Ne.{1}
                  (Matrix.adjugate.{0, 0}
                    (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.D.{0, 0} S) ⇑ι))
                  0 →
                Ne.{1} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} S') 0 →
                  Ne.{1}
                      (Matrix.adjugate.{0, 0}
                        (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.D.{0, 0} S') ⇑ι))
                      0 →
                    (ZInQ.Contrib.CloudB3RC53.StageCone.StageConeComparison S S' ε σ J v ↔
                      ZInQ.Contrib.CloudB3RC53.SwitchInputs.StageModelLink ι
                          (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} S)
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.oldMat.{0} ε v) v (Pi.single.{0, 0} 0 1) ∧
                        ZInQ.Contrib.CloudB3RC53.SwitchInputs.StageModelLink ι
                          (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} S')
                          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.newMat.{0} ε σ J v) (Matrix.mulVec.{0, 0, 0} J v)
                          (Pi.single.{0, 0} 1 1))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.stageConeComparison_iff_links
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.stageConeComparison_iff_links' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.stageConeComparison_of_identification`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.stageConeComparison_of_identification : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} A F} (S S' : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι)
  {ε σ : F},
  Ne.{1} ε 0 →
    Ne.{1} σ 0 →
      ∀ {J : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F} {v : Fin 2 → F},
        Ne.{1} v 0 →
          Ne.{1} (Matrix.mulVec.{0, 0, 0} J v) 0 →
            Ne.{1} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} S) 0 →
              Ne.{1}
                  (Matrix.adjugate.{0, 0}
                    (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.D.{0, 0} S) ⇑ι))
                  0 →
                Ne.{1} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} S') 0 →
                  Ne.{1}
                      (Matrix.adjugate.{0, 0}
                        (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.D.{0, 0} S') ⇑ι))
                      0 →
                    ZInQ.Contrib.CloudB3RC53.SwitchInputs.StageConeIdentification ι S S' ε σ J v →
                      ZInQ.Contrib.CloudB3RC53.StageCone.StageConeComparison S S' ε σ J v
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.stageConeComparison_of_identification
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.stageConeComparison_of_identification' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## CommonFactor.lean

### `ZInQ.Contrib.RC53Assist.StageCone.stage_coord_eq_normalized`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.stage_coord_eq_normalized : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} A F} {S : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  {M : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F} {z₀ l₀ : Fin 2 → F}
  (g : ZInQ.Contrib.CloudB3RC53.StageCone.StageMap S M z₀ l₀)
  (hz₀ :
    Eq.{1}
      (Matrix.mulVec.{0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M))
        z₀)
      0)
  (hl₀ :
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0} l₀
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M)))
      0),
  Ne.{1} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} S) 0 →
    Ne.{1}
        (Matrix.adjugate.{0, 0}
          (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.D.{0, 0} S) ⇑ι))
        0 →
      ∀ {u₀ : F},
        ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord.{0} M z₀ l₀ u₀ →
          Ne.{1} u₀ 0 →
            Ne.{1} (Matrix.adjugate.{0, 0} M) 0 →
              Eq.{1} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} S)
                (HMul.hMul.{0, 0, 0} u₀
                  (Inv.inv.{0} (ZInQ.Contrib.RC53Assist.StageCone.normalizedConeTorsion g hz₀ hl₀)))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.stage_coord_eq_normalized
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.stage_coord_eq_normalized' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.normalizedConeTorsion_ne_zero`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.normalizedConeTorsion_ne_zero : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} A F} {S : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  {M : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F} {z₀ l₀ : Fin 2 → F}
  (g : ZInQ.Contrib.CloudB3RC53.StageCone.StageMap S M z₀ l₀)
  (hz₀ :
    Eq.{1}
      (Matrix.mulVec.{0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M))
        z₀)
      0)
  (hl₀ :
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0} l₀
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M)))
      0),
  Ne.{1} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0} S) 0 →
    Ne.{1}
        (Matrix.adjugate.{0, 0}
          (Matrix.map.{0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.D.{0, 0} S) ⇑ι))
        0 →
      ∀ {u₀ : F},
        ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord.{0} M z₀ l₀ u₀ →
          Ne.{1} u₀ 0 →
            Ne.{1} (Matrix.adjugate.{0, 0} M) 0 →
              Ne.{1} (ZInQ.Contrib.RC53Assist.StageCone.normalizedConeTorsion g hz₀ hl₀) 0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.normalizedConeTorsion_ne_zero
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.normalizedConeTorsion_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.integralUnit_iff_normalized`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.integralUnit_iff_normalized : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} A F} {S : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  {M : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F} {z₀ l₀ : Fin 2 → F}
  (g : ZInQ.Contrib.CloudB3RC53.StageCone.StageMap S M z₀ l₀)
  (hz₀ :
    Eq.{1}
      (Matrix.mulVec.{0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M))
        z₀)
      0)
  (hl₀ :
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0} l₀
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M)))
      0),
  g.IntegralUnit hz₀ hl₀ ↔ ∃ c, Eq.{1} (ZInQ.Contrib.RC53Assist.StageCone.normalizedConeTorsion g hz₀ hl₀) (ι ↑c)
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.integralUnit_iff_normalized
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.integralUnit_iff_normalized' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.volumeSwitchData_uF`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.volumeSwitchData_uF : ∀ {F : Type} [inst : Field.{0} F] {ε σ : F} (hε : Ne.{1} ε 0)
  (hσ : Eq.{1} (HMul.hMul.{0, 0, 0} σ σ) 1) {J : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F}
  (hJ : Eq.{1} (HMul.hMul.{0, 0, 0} J J) 1) (hJdet : Eq.{1} (Matrix.det.{0, 0} J) (-1)) {v : Fin 2 → F}
  (hv : Ne.{1} v 0) (θ : F) (hθ : Ne.{1} θ 0) (μF μS : F),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.SwitchCoordData.uF.{0}
      (ZInQ.Contrib.RC53Assist.StageCone.volumeSwitchData hε hσ hJ hJdet hv θ hθ μF μS))
    (HDiv.hDiv.{0, 0, 0} μF (HMul.hMul.{0, 0, 0} ε θ))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.volumeSwitchData_uF
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.volumeSwitchData_uF' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.volumeSwitchData_uS`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.volumeSwitchData_uS : ∀ {F : Type} [inst : Field.{0} F] {ε σ : F} (hε : Ne.{1} ε 0)
  (hσ : Eq.{1} (HMul.hMul.{0, 0, 0} σ σ) 1) {J : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F}
  (hJ : Eq.{1} (HMul.hMul.{0, 0, 0} J J) 1) (hJdet : Eq.{1} (Matrix.det.{0, 0} J) (-1)) {v : Fin 2 → F}
  (hv : Ne.{1} v 0) (θ : F) (hθ : Ne.{1} θ 0) (μF μS : F),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.SwitchCoordData.uS.{0}
      (ZInQ.Contrib.RC53Assist.StageCone.volumeSwitchData hε hσ hJ hJdet hv θ hθ μF μS))
    (HDiv.hDiv.{0, 0, 0} (Neg.neg.{0} μS) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} σ ε) θ))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.volumeSwitchData_uS
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.volumeSwitchData_uS' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.relativeConeUnit_of_commonFactor`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.relativeConeUnit_of_commonFactor : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} A F} {S S' : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  {ε σ : F} {J : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F} {v : Fin 2 → F}
  (g :
    ZInQ.Contrib.CloudB3RC53.StageCone.StageMap S (ZInQ.Contrib.CloudB3RC53.SwitchInputs.oldMat.{0} ε v) v
      (Pi.single.{0, 0} 0 1))
  (g' :
    ZInQ.Contrib.CloudB3RC53.StageCone.StageMap S' (ZInQ.Contrib.CloudB3RC53.SwitchInputs.newMat.{0} ε σ J v)
      (Matrix.mulVec.{0, 0, 0} J v) (Pi.single.{0, 0} 1 1))
  (θ : F) (a b : Units.{0} A),
  Eq.{1}
      (ZInQ.Contrib.RC53Assist.StageCone.normalizedConeTorsion g (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hz ε v)
        (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hl ε v))
      (HMul.hMul.{0, 0, 0} θ (ι ↑a)) →
    Eq.{1}
        (ZInQ.Contrib.RC53Assist.StageCone.normalizedConeTorsion g'
          (ZInQ.Contrib.CloudB3RC53.StageCone.newMat_hz ε σ J v) (ZInQ.Contrib.CloudB3RC53.StageCone.newMat_hl ε σ J v))
        (HMul.hMul.{0, 0, 0} θ (ι ↑b)) →
      ZInQ.Contrib.RC53Assist.StageCone.RelativeConeUnit g g'
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.relativeConeUnit_of_commonFactor
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.relativeConeUnit_of_commonFactor' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.relativeConeUnit_of_integralUnits`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.relativeConeUnit_of_integralUnits : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] {ι : RingHom.{0, 0} A F} {S S' : ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.{0, 0} ι}
  {ε σ : F} {J : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F} {v : Fin 2 → F}
  (g :
    ZInQ.Contrib.CloudB3RC53.StageCone.StageMap S (ZInQ.Contrib.CloudB3RC53.SwitchInputs.oldMat.{0} ε v) v
      (Pi.single.{0, 0} 0 1))
  (g' :
    ZInQ.Contrib.CloudB3RC53.StageCone.StageMap S' (ZInQ.Contrib.CloudB3RC53.SwitchInputs.newMat.{0} ε σ J v)
      (Matrix.mulVec.{0, 0, 0} J v) (Pi.single.{0, 0} 1 1)),
  g.IntegralUnit (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hz ε v) (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hl ε v) →
    g'.IntegralUnit (ZInQ.Contrib.CloudB3RC53.StageCone.newMat_hz ε σ J v)
        (ZInQ.Contrib.CloudB3RC53.StageCone.newMat_hl ε σ J v) →
      ZInQ.Contrib.RC53Assist.StageCone.RelativeConeUnit g g'
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.relativeConeUnit_of_integralUnits
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.relativeConeUnit_of_integralUnits' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.planeCoordWithSummand_eq`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.planeCoordWithSummand_eq : ∀ {F : Type} [inst : Field.{0} F] {E₀ E₁ E₂ E₃ : Type}
  [inst_1 : Fintype.{0} E₀] [inst_2 : Fintype.{0} E₁] [inst_3 : Fintype.{0} E₂] [inst_4 : Fintype.{0} E₃]
  [inst_5 : DecidableEq.{1} E₀] [inst_6 : DecidableEq.{1} E₁] [inst_7 : DecidableEq.{1} E₂]
  [inst_8 : DecidableEq.{1} E₃] (M : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F) (z l : Fin 2 → F)
  (hz :
    Eq.{1}
      (Matrix.mulVec.{0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M)) z)
      0)
  (hl :
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0} l
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{0, 0, 0, 0, 0} (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M)))
      0)
  (E : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} F E₀ E₁ E₂ E₃)
  (sE : Equiv.{1, 1} (Sum.{0, 0} E₀ E₂) (Sum.{0, 0} E₁ E₃))
  (hE :
    ZInQ.Contrib.CloudB3RC53.Torsion.Contraction.{0, 0, 0}
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{0, 0, 0, 0, 0} E))
  {u : F},
  ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord.{0} M z l u →
    ∀
      (hC :
        ZInQ.Contrib.CloudB3RC53.Torsion.Contraction.{0, 0, 0}
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{0, 0, 0, 0, 0}
            (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{0, 0, 0, 0, 0}
              (ZInQ.Contrib.CloudB3RC53.Torsion.twoTerm.{0} M) z l hz hl))),
      Eq.{1} (ZInQ.Contrib.RC53Assist.StageCone.planeCoordWithSummand M z l hz hl E sE)
        (HMul.hMul.{0, 0, 0} u
          (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{0, 0, 0}
            (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{0, 0, 0, 0, 0} E) sE))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.planeCoordWithSummand_eq
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.planeCoordWithSummand_eq' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.commonSummand_switch_relation`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.commonSummand_switch_relation : ∀ {F : Type} [inst : Field.{0} F]
  {E₀ E₁ E₂ E₃ : Type} [inst_1 : Fintype.{0} E₀] [inst_2 : Fintype.{0} E₁] [inst_3 : Fintype.{0} E₂]
  [inst_4 : Fintype.{0} E₃] [inst_5 : DecidableEq.{1} E₀] [inst_6 : DecidableEq.{1} E₁] [inst_7 : DecidableEq.{1} E₂]
  [inst_8 : DecidableEq.{1} E₃] {ε σ : F},
  Ne.{1} ε 0 →
    Eq.{1} (HMul.hMul.{0, 0, 0} σ σ) 1 →
      ∀ {J : Matrix.{0, 0, 0} (Fin 2) (Fin 2) F},
        Eq.{1} (HMul.hMul.{0, 0, 0} J J) 1 →
          ∀ {v : Fin 2 → F},
            Ne.{1} v 0 →
              ∀ (E : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{0, 0, 0, 0, 0} F E₀ E₁ E₂ E₃)
                (sE : Equiv.{1, 1} (Sum.{0, 0} E₀ E₂) (Sum.{0, 0} E₁ E₃))
                (hE :
                  ZInQ.Contrib.CloudB3RC53.Torsion.Contraction.{0, 0, 0}
                    (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{0, 0, 0, 0, 0} E)),
                Eq.{1}
                  (ZInQ.Contrib.RC53Assist.StageCone.planeCoordWithSummand
                    (ZInQ.Contrib.CloudB3RC53.SwitchInputs.oldMat.{0} ε v) v (Pi.single.{0, 0} 0 1)
                    (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hz ε v)
                    (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hl ε v) E sE)
                  (HMul.hMul.{0, 0, 0} (Neg.neg.{0} σ)
                    (ZInQ.Contrib.RC53Assist.StageCone.planeCoordWithSummand
                      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.newMat.{0} ε σ J v) (Matrix.mulVec.{0, 0, 0} J v)
                      (Pi.single.{0, 0} 1 1) (ZInQ.Contrib.CloudB3RC53.StageCone.newMat_hz ε σ J v)
                      (ZInQ.Contrib.CloudB3RC53.StageCone.newMat_hl ε σ J v) E sE))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.commonSummand_switch_relation
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.commonSummand_switch_relation' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## GenuineModel.lean

### `ZInQ.Contrib.RC53Assist.StageCone.cycle_lift_one`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.cycle_lift_one : ∀ {A : Type} [inst : CommRing.{0} A]
  {B C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A}
  (f : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} B C),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} f) →
    ∀ (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1)),
      Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) z) 0 →
        ∃ x y,
          Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} B 1 2 rfl.{1}) x) 0 ∧
            Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} f 1 1 rfl.{1}) x)
              (HAdd.hAdd.{0, 0, 0} z ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 0 1 rfl.{1}) y))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.cycle_lift_one
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.cycle_lift_one' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.cycle_lift_two`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.cycle_lift_two : ∀ {A : Type} [inst : CommRing.{0} A]
  {B C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A}
  (f : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.{0} B C),
  QuasiIso.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} f) →
    ∀ (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 2)),
      Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 2 3 rfl.{1}) z) 0 →
        ∃ x y,
          Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} B 2 3 rfl.{1}) x) 0 ∧
            Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} f 2 2 rfl.{1}) x)
              (HAdd.hAdd.{0, 0, 0} z ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) y))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.cycle_lift_two
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.cycle_lift_two' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.functionalRow_dot`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.functionalRow_dot : ∀ {A : Type} [inst : CommRing.{0} A] {n : ℕ}
  (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A) (Fin n → A) A) (x : Fin n → A),
  Eq.{1} (dotProduct.{0, 0} (ZInQ.Contrib.RC53Assist.StageCone.functionalRow f) x) (f x)
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.functionalRow_dot
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.functionalRow_dot' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.map_cycle`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.map_cycle : ∀ {A : Type} [inst : CommRing.{0} A] {n : ℕ} {F : Type}
  [inst_1 : CommRing.{0} F] (ι : RingHom.{0, 0} A F) (D : Matrix.{0, 0, 0} (Fin n) (Fin n) A) (z : Fin n → A),
  Eq.{1} (Matrix.mulVec.{0, 0, 0} D z) 0 →
    Eq.{1} (Matrix.mulVec.{0, 0, 0} (Matrix.map.{0, 0, 0, 0} D ⇑ι) fun j => ι (z j)) 0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.map_cycle
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.map_cycle' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.map_closedRow`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.map_closedRow : ∀ {A : Type} [inst : CommRing.{0} A] {n : ℕ} {F : Type}
  [inst_1 : CommRing.{0} F] (ι : RingHom.{0, 0} A F) (D : Matrix.{0, 0, 0} (Fin n) (Fin n) A) (w : Fin n → A),
  Eq.{1} (Matrix.vecMul.{0, 0, 0} w D) 0 →
    Eq.{1} (Matrix.vecMul.{0, 0, 0} (fun j => ι (w j)) (Matrix.map.{0, 0, 0, 0} D ⇑ι)) 0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.map_closedRow
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.map_closedRow' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.map_vector_ne_zero`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.map_vector_ne_zero : ∀ {A : Type} [inst : CommRing.{0} A] {n : ℕ} {F : Type}
  [inst_1 : CommRing.{0} F] (ι : RingHom.{0, 0} A F),
  Function.Injective.{1, 1} ⇑ι → ∀ {z : Fin n → A}, Ne.{1} z 0 → Ne.{1} (fun j => ι (z j)) 0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.map_vector_ne_zero
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.map_vector_ne_zero' depends on axioms: [Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.coordinate_ne_zero`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.coordinate_ne_zero : ∀ {n : ℕ} {F : Type} [inst : Field.{0} F]
  {D : Matrix.{0, 0, 0} (Fin n) (Fin n) F} {z w : Fin n → F} {u : F},
  ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord.{0} D z w u → Ne.{1} z 0 → Ne.{1} w 0 → Ne.{1} u 0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.coordinate_ne_zero
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.coordinate_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.matrix_mulVec`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.matrix_mulVec : ∀ {A : Type} [inst : CommRing.{0} A]
  {C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A} (R : ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization C)
  (x : Fin (HAdd.hAdd.{0, 0, 0} R.n 1) → A), Eq.{1} (Matrix.mulVec.{0, 0, 0} R.matrix x) (R.dVec x)
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.matrix_mulVec
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.matrix_mulVec' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.liftedClass_closed`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.liftedClass_closed : ∀ {A : Type} [inst : CommRing.{0} A]
  {C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A} (R : ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization C)
  (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1))
  (hz : Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) z) 0),
  Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} R.model 1 2 rfl.{1}) (R.liftedClass z hz)) 0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.liftedClass_closed
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.liftedClass_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.liftedClass_image`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.liftedClass_image : ∀ {A : Type} [inst : CommRing.{0} A]
  {C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A} (R : ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization C)
  (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1))
  (hz : Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) z) 0),
  Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} R.f 1 1 rfl.{1}) (R.liftedClass z hz))
    (HAdd.hAdd.{0, 0, 0} z
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 0 1 rfl.{1}) (R.boundaryWitness z hz)))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.liftedClass_image
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.liftedClass_image' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.classVec_closed`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.classVec_closed : ∀ {A : Type} [inst : CommRing.{0} A]
  {C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A} (R : ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization C)
  (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1))
  (hz : Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) z) 0),
  Eq.{1} (Matrix.mulVec.{0, 0, 0} R.matrix (R.classVec z hz)) 0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.classVec_closed
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.classVec_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.functional_closed`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.functional_closed : ∀ {A : Type} [inst : CommRing.{0} A]
  {C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A} (R : ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization C)
  (lam : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 2)) A),
  (∀ (y : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1)),
      Eq.{1} (lam ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) y)) 0) →
    ∀ (x : Fin (HAdd.hAdd.{0, 0, 0} R.n 1) → A), Eq.{1} ((R.functional lam) (Matrix.mulVec.{0, 0, 0} R.matrix x)) 0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.functional_closed
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.functional_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.row_closed`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.row_closed : ∀ {A : Type} [inst : CommRing.{0} A]
  {C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A} (R : ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization C)
  (lam : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 2)) A),
  (∀ (y : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1)),
      Eq.{1} (lam ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) y)) 0) →
    Eq.{1} (Matrix.vecMul.{0, 0, 0} (R.row lam) R.matrix) 0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.row_closed
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization.row_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_class`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_class : ∀ {A : Type} [inst : CommRing.{0} A]
  {C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A} (R : ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization C)
  {F : Type} [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F)
  (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1))
  (hz : Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) z) 0)
  (lam : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 2)) A)
  (hlam :
    ∀ (y : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1)),
      Eq.{1} (lam ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) y)) 0)
  (hdet : Eq.{1} (Matrix.det.{0, 0} (Matrix.map.{0, 0, 0, 0} R.matrix ⇑ι)) 0)
  (hadj : Ne.{1} (Matrix.adjugate.{0, 0} (Matrix.map.{0, 0, 0, 0} R.matrix ⇑ι)) 0),
  Eq.{1}
    ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} R.f 1 1 rfl.{1})
      ((LinearEquiv.symm.{0, 0, 0, 0} (Module.Basis.equivFun.{0, 0, 0} R.b1))
        (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.z.{0, 0}
          (ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization R ι z hz lam hlam hdet hadj))))
    (HAdd.hAdd.{0, 0, 0} z
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 0 1 rfl.{1}) (R.boundaryWitness z hz)))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_class
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_class' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_functional`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_functional : ∀ {A : Type} [inst : CommRing.{0} A]
  {C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A} (R : ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization C)
  {F : Type} [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F)
  (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1))
  (hz : Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) z) 0)
  (lam : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 2)) A)
  (hlam :
    ∀ (y : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1)),
      Eq.{1} (lam ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) y)) 0)
  (hdet : Eq.{1} (Matrix.det.{0, 0} (Matrix.map.{0, 0, 0, 0} R.matrix ⇑ι)) 0)
  (hadj : Ne.{1} (Matrix.adjugate.{0, 0} (Matrix.map.{0, 0, 0, 0} R.matrix ⇑ι)) 0)
  (x : Fin (HAdd.hAdd.{0, 0, 0} R.n 1) → A),
  Eq.{1}
    (dotProduct.{0, 0}
      (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.w.{0, 0}
        (ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization R ι z hz lam hlam hdet hadj))
      x)
    (lam
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{0} R.f 2 2 rfl.{1})
        ((LinearEquiv.symm.{0, 0, 0, 0} (Module.Basis.equivFun.{0, 0, 0} R.b2)) x)))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_functional
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_functional' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_ne_zero`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_ne_zero : ∀ {A : Type} [inst : CommRing.{0} A]
  {C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A} (R : ZInQ.Contrib.RC53Assist.StageCone.TwoTermRealization C)
  {F : Type} [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F),
  Function.Injective.{1, 1} ⇑ι →
    ∀ (z : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1))
      (hz : Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) z) 0)
      (lam : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A) (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 2)) A)
      (hlam :
        ∀ (y : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 1)),
          Eq.{1} (lam ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 1 2 rfl.{1}) y)) 0)
      (hdet : Eq.{1} (Matrix.det.{0, 0} (Matrix.map.{0, 0, 0, 0} R.matrix ⇑ι)) 0)
      (hadj : Ne.{1} (Matrix.adjugate.{0, 0} (Matrix.map.{0, 0, 0, 0} R.matrix ⇑ι)) 0),
      (∀ (y : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} C 0)),
          Ne.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 0 1 rfl.{1}) y) z) →
        (∃ x, Eq.{1} ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} C 2 3 rfl.{1}) x) 0 ∧ Ne.{1} (lam x) 0) →
          Ne.{1}
            (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0}
              (ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization R ι z hz lam hlam hdet hadj))
            0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_ne_zero
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.stageOfRealization_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.free_subsingleton_of_finrank_zero`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.free_subsingleton_of_finrank_zero : ∀ {A : Type} [inst : CommRing.{0} A]
  [Nontrivial.{0} A] (V : Type) [inst_2 : AddCommGroup.{0} V] [inst_3 : Module.{0, 0} A V] [Module.Free.{0, 0} A V]
  [Module.Finite.{0, 0} A V], Eq.{1} (Module.finrank.{0, 0} A V) 0 → Subsingleton.{1} V
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.free_subsingleton_of_finrank_zero
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.free_subsingleton_of_finrank_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.ofCCHom_quasiIso`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.ofCCHom_quasiIso : ∀ {A : Type} [inst : CommRing.{0} A]
  {K : CochainComplex.{0, 1, 0} (ModuleCat.{0, 0} A) ℤ} {C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A}
  (f : Quiver.Hom.{0, 1} K (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0} C)),
  QuasiIso.{0, 1, 0} f →
    QuasiIso.{0, 1, 0}
      (ZInQ.Contrib.CloudB3RC53.SelmerDuality.GHom.toCC.{0} (ZInQ.Manuscript.RC.SelmerComplex.ofCCHom.{0} f))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.ofCCHom_quasiIso
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.ofCCHom_quasiIso' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.exists_twoTermRealization_of_boundedFree`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.exists_twoTermRealization_of_boundedFree : ∀ {A : Type} [inst : CommRing.{0} A]
  [inst_1 : IsLocalRing.{0} A] (C : ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.{0} A)
  (K : CochainComplex.{0, 1, 0} (ModuleCat.{0, 0} A) ℤ),
  (∀ (i : ℤ),
      Module.Free.{0, 0} A ↑(HomologicalComplex.X.{0, 1, 0} K i) ∧
        Module.Finite.{0, 0} A ↑(HomologicalComplex.X.{0, 1, 0} K i)) →
    (∃ a b, ∀ (i : ℤ), LT.lt.{0} i a ∨ LT.lt.{0} b i → Subsingleton.{1} ↑(HomologicalComplex.X.{0, 1, 0} K i)) →
      ∀ (f : Quiver.Hom.{0, 1} K (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0} C)),
        QuasiIso.{0, 1, 0} f →
          ∀ (n : ℕ),
            (∀ (i : ℤ),
                Eq.{1}
                  (Module.finrank.{0, 0} (IsLocalRing.ResidueField.{0} A)
                    ↑(HomologicalComplex.homology.{0, 1, 0} (ZInQ.Contrib.CloudB3RC53.ResidualTransfer.resCx.{0} K) i))
                  (ite.{1} (Eq.{1} i 1 ∨ Eq.{1} i 2) (HAdd.hAdd.{0, 0, 0} n 1) 0)) →
              ∃ R,
                Eq.{1} R.n n ∧
                  ∀ (i j : ℤ) (hij : Eq.{1} (HAdd.hAdd.{0, 0, 0} i 1) j)
                    (x : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} R.model i)),
                    Membership.mem.{0, 0} (HSMul.hSMul.{0, 0, 0} (IsLocalRing.maximalIdeal.{0} A) Top.top.{0})
                      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} R.model i j hij) x)
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.exists_twoTermRealization_of_boundedFree
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.exists_twoTermRealization_of_boundedFree' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.isEmpty_ringHom_acoef_charZero`

```lean
ZInQ.Contrib.RC53Assist.StageCone.isEmpty_ringHom_acoef_charZero : ∀ (i : ℕ) (F : Type) [inst : Field.{0} F]
  [CharZero.{0} F], IsEmpty.{1} (RingHom.{0, 0} (ZInQ.Manuscript.RC.HeegnerAlgebra.Acoef i) F)
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.isEmpty_ringHom_acoef_charZero
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.isEmpty_ringHom_acoef_charZero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

## TorsionObstruction.lean

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector_ne_zero`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector_ne_zero : ∀ {F : Type} [inst : Field.{0} F],
  Ne.{1} ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector 0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector_ne_zero
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.switchedVector`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.switchedVector : ∀ {F : Type} [inst : Field.{0} F],
  Eq.{1}
    (Matrix.mulVec.{0, 0, 0} (ZInQ.Manuscript.RC.Uniform.switchJ0.{0} F)
      ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector)
    ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.switchedVector
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.switchedVector' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_ne_zero`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_ne_zero : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F) (a : A) (ha : Ne.{1} (ι a) 0),
  Ne.{1}
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0}
      (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage ι a ha))
    0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_ne_zero
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_ne_zero`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_ne_zero : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F) (a : A) (ha : Ne.{1} (ι a) 0),
  Ne.{1}
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0}
      (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage ι a ha))
    0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_ne_zero
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_ne_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_adjugate`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_adjugate : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F) (a : A) (ha : Ne.{1} (ι a) 0),
  Ne.{1}
    (Matrix.adjugate.{0, 0}
      (Matrix.map.{0, 0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.D.{0, 0}
          (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage ι a ha))
        ⇑ι))
    0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_adjugate
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_adjugate' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_adjugate`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_adjugate : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F) (a : A) (ha : Ne.{1} (ι a) 0),
  Ne.{1}
    (Matrix.adjugate.{0, 0}
      (Matrix.map.{0, 0, 0, 0}
        (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.D.{0, 0}
          (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage ι a ha))
        ⇑ι))
    0
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_adjugate
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_adjugate' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_sign`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_sign : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F) (a : A) (ha : Ne.{1} (ι a) 0),
  Eq.{1} (ZInQ.Contrib.CloudB3RC53.StageCone.stageSign (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage ι a ha))
    1
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_sign
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage_sign' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_sign`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_sign : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F) (a : A) (ha : Ne.{1} (ι a) 0),
  Eq.{1} (ZInQ.Contrib.CloudB3RC53.StageCone.stageSign (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage ι a ha))
    1
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_sign
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage_sign' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldComparison_torsion`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldComparison_torsion : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F) (a : A) (ha : Ne.{1} (ι a) 0)
  (g :
    ZInQ.Contrib.CloudB3RC53.StageCone.StageMap (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage ι a ha)
      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.oldMat.{0} 1 ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector)
      ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector (Pi.single.{0, 0} 0 1)),
  Eq.{1}
    (g.coneTorsion
      (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hz 1 ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector)
      (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hl 1 ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector))
    (ι a)
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldComparison_torsion
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldComparison_torsion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newComparison_torsion`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newComparison_torsion : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F) (a : A) (ha : Ne.{1} (ι a) 0)
  (g :
    ZInQ.Contrib.CloudB3RC53.StageCone.StageMap (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage ι a ha)
      (ZInQ.Contrib.CloudB3RC53.SwitchInputs.newMat.{0} 1 1 (ZInQ.Manuscript.RC.Uniform.switchJ0.{0} F)
        ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector)
      (Matrix.mulVec.{0, 0, 0} (ZInQ.Manuscript.RC.Uniform.switchJ0.{0} F)
        ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector)
      (Pi.single.{0, 0} 1 1)),
  Eq.{1}
    (g.coneTorsion
      (ZInQ.Contrib.CloudB3RC53.StageCone.newMat_hz 1 1 (ZInQ.Manuscript.RC.Uniform.switchJ0.{0} F)
        ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector)
      (ZInQ.Contrib.CloudB3RC53.StageCone.newMat_hl 1 1 (ZInQ.Manuscript.RC.Uniform.switchJ0.{0} F)
        ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector))
    (ι a)
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newComparison_torsion
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newComparison_torsion' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldIntegralUnit_iff`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldIntegralUnit_iff : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F) (a : A) (ha : Ne.{1} (ι a) 0),
  Function.Injective.{1, 1} ⇑ι →
    ∀
      (g :
        ZInQ.Contrib.CloudB3RC53.StageCone.StageMap (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage ι a ha)
          (ZInQ.Contrib.CloudB3RC53.SwitchInputs.oldMat.{0} 1 ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector)
          ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector (Pi.single.{0, 0} 0 1)),
      g.IntegralUnit
          (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hz 1 ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector)
          (ZInQ.Contrib.CloudB3RC53.StageCone.oldMat_hl 1 ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector) ↔
        IsUnit.{0} a
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldIntegralUnit_iff
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldIntegralUnit_iff' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.not_stageConeComparison_of_nonunit`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.not_stageConeComparison_of_nonunit : ∀ {A F : Type}
  [inst : CommRing.{0} A] [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F) (a : A) (ha : Ne.{1} (ι a) 0),
  Function.Injective.{1, 1} ⇑ι →
    ¬IsUnit.{0} a →
      ¬ZInQ.Contrib.CloudB3RC53.StageCone.StageConeComparison
          (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage ι a ha)
          (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage ι a ha) 1 1
          (ZInQ.Manuscript.RC.Uniform.switchJ0.{0} F) ZInQ.Contrib.RC53Assist.StageCone.Obstruction.planeVector
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.not_stageConeComparison_of_nonunit
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.not_stageConeComparison_of_nonunit' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```

### `ZInQ.Contrib.RC53Assist.StageCone.Obstruction.coordinate_sign_relation`

```lean
@ZInQ.Contrib.RC53Assist.StageCone.Obstruction.coordinate_sign_relation : ∀ {A F : Type} [inst : CommRing.{0} A]
  [inst_1 : Field.{0} F] (ι : RingHom.{0, 0} A F) (a : A) (ha : Ne.{1} (ι a) 0),
  Eq.{1}
    (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0}
      (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.oldStage ι a ha))
    (Neg.neg.{0}
      (ZInQ.Contrib.CloudB3RC53.UniformSwitch.TwoTermStage.u.{0, 0}
        (ZInQ.Contrib.RC53Assist.StageCone.Obstruction.newStage ι a ha)))
```

```lean
#print axioms ZInQ.Contrib.RC53Assist.StageCone.Obstruction.coordinate_sign_relation
```

```text
'ZInQ.Contrib.RC53Assist.StageCone.Obstruction.coordinate_sign_relation' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
```
