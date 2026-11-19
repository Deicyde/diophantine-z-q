# Exact theorem types and axiom reports

These are the complete compiler type and axiom reports for every theorem in the three proof files. The source declarations retain the exact proof arguments and enclosing contexts. Every audited dependency is a standard axiom.

## GenuineRetention

```text
@ZInQ.Contrib.RC53Assist.CoordProvenance.toFullAt_compat.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  {G : Type u_1} [inst_1 : Group.{u_1} G] [inst_2 : TopologicalSpace.{u_1} G] {Vo Vn : Type u_1}
  {Gv : Sum.{u_1, u_1} Vo Vn → Type u_1} [inst_3 : (v : Sum.{u_1, u_1} Vo Vn) → Group.{u_1} (Gv v)]
  [inst_4 : (v : Sum.{u_1, u_1} Vo Vn) → TopologicalSpace.{u_1} (Gv v)]
  [inst_5 : ∀ (v : Sum.{u_1, u_1} Vo Vn), IsTopologicalGroup.{u_1} (Gv v)]
  {loc : (v : Sum.{u_1, u_1} Vo Vn) → ContinuousMonoidHom.{u_1, u_1} (Gv v) G} {A : Type u_1}
  [inst_6 : AddCommGroup.{u_1} A] [inst_7 : Module.{u_1, u_1} R A] [inst_8 : DistribMulAction.{u_1, u_1} G A]
  [inst_9 : SMulCommClass.{u_1, u_1, u_1} G R A] [inst_10 : TopologicalSpace.{u_1} A] [inst_11 : ContinuousAdd.{u_1} A]
  [inst_12 : ContinuousConstSMul.{u_1, u_1} R A] [inst_13 : ContinuousSMul.{u_1, u_1} G A]
  (Δ : ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.{u_1} R G Gv loc A) (v : Sum.{u_1, u_1} Vo Vn) (n : ℤ)
  (a :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
        (ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.U.{u_1} Δ v) n)),
  Eq.{u_1 + 1}
    ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{u_1}
        (ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.i.{u_1}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.fullAt.{u_1} Δ) v)
        n n ⋯)
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{u_1}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.toFullAt.{u_1} Δ v) n n ⋯)
        a))
    ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{u_1}
        (ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.i.{u_1} Δ v) n n ⋯)
      a)
'ZInQ.Contrib.RC53Assist.CoordProvenance.toFullAt_compat' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.fromZeroAt_compat.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  {G : Type u_1} [inst_1 : Group.{u_1} G] [inst_2 : TopologicalSpace.{u_1} G] {Vo Vn : Type u_1}
  {Gv : Sum.{u_1, u_1} Vo Vn → Type u_1} [inst_3 : (v : Sum.{u_1, u_1} Vo Vn) → Group.{u_1} (Gv v)]
  [inst_4 : (v : Sum.{u_1, u_1} Vo Vn) → TopologicalSpace.{u_1} (Gv v)]
  [inst_5 : ∀ (v : Sum.{u_1, u_1} Vo Vn), IsTopologicalGroup.{u_1} (Gv v)]
  {loc : (v : Sum.{u_1, u_1} Vo Vn) → ContinuousMonoidHom.{u_1, u_1} (Gv v) G} {A : Type u_1}
  [inst_6 : AddCommGroup.{u_1} A] [inst_7 : Module.{u_1, u_1} R A] [inst_8 : DistribMulAction.{u_1, u_1} G A]
  [inst_9 : SMulCommClass.{u_1, u_1, u_1} G R A] [inst_10 : TopologicalSpace.{u_1} A] [inst_11 : ContinuousAdd.{u_1} A]
  [inst_12 : ContinuousConstSMul.{u_1, u_1} R A] [inst_13 : ContinuousSMul.{u_1, u_1} G A]
  (Δ : ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.{u_1} R G Gv loc A) (v : Sum.{u_1, u_1} Vo Vn) (n : ℤ)
  (a :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
        (ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.U.{u_1}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.zeroAt.{u_1} Δ) v)
        n)),
  Eq.{u_1 + 1}
    ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{u_1}
        (ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.i.{u_1} Δ v) n n ⋯)
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{u_1}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.fromZeroAt.{u_1} Δ v) n n ⋯)
        a))
    ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{u_1}
        (ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.i.{u_1}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.zeroAt.{u_1} Δ) v)
        n n ⋯)
      a)
'ZInQ.Contrib.RC53Assist.CoordProvenance.fromZeroAt_compat' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.relaxedIsotropy_retained.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  {G : Type u_1} [inst_1 : Group.{u_1} G] [inst_2 : TopologicalSpace.{u_1} G] {Vo Vn : Type u_1}
  {Gv : Sum.{u_1, u_1} Vo Vn → Type u_1} [inst_3 : (v : Sum.{u_1, u_1} Vo Vn) → Group.{u_1} (Gv v)]
  [inst_4 : (v : Sum.{u_1, u_1} Vo Vn) → TopologicalSpace.{u_1} (Gv v)]
  [inst_5 : ∀ (v : Sum.{u_1, u_1} Vo Vn), IsTopologicalGroup.{u_1} (Gv v)]
  {loc : (v : Sum.{u_1, u_1} Vo Vn) → ContinuousMonoidHom.{u_1, u_1} (Gv v) G} {A B T : Type u_1}
  [inst_6 : AddCommGroup.{u_1} A] [inst_7 : Module.{u_1, u_1} R A] [inst_8 : DistribMulAction.{u_1, u_1} G A]
  [inst_9 : SMulCommClass.{u_1, u_1, u_1} G R A] [inst_10 : TopologicalSpace.{u_1} A] [inst_11 : ContinuousAdd.{u_1} A]
  [inst_12 : ContinuousConstSMul.{u_1, u_1} R A] [inst_13 : ContinuousSMul.{u_1, u_1} G A]
  [inst_14 : AddCommGroup.{u_1} B] [inst_15 : Module.{u_1, u_1} R B] [inst_16 : DistribMulAction.{u_1, u_1} G B]
  [inst_17 : SMulCommClass.{u_1, u_1, u_1} G R B] [inst_18 : TopologicalSpace.{u_1} B] [inst_19 : ContinuousAdd.{u_1} B]
  [inst_20 : ContinuousConstSMul.{u_1, u_1} R B] [inst_21 : ContinuousSMul.{u_1, u_1} G B]
  [inst_22 : AddCommGroup.{u_1} T] [inst_23 : Module.{u_1, u_1} R T] [inst_24 : DistribMulAction.{u_1, u_1} G T]
  [inst_25 : SMulCommClass.{u_1, u_1, u_1} G R T] [inst_26 : TopologicalSpace.{u_1} T] [inst_27 : ContinuousAdd.{u_1} T]
  [inst_28 : ContinuousConstSMul.{u_1, u_1} R T] [inst_29 : ContinuousSMul.{u_1, u_1} G T]
  (β : LinearMap.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} R) A (LinearMap.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} R) B T))
  (hβ :
    ∀ (g : G) (a : A) (b : B),
      Eq.{u_1 + 1} ((β (HSMul.hSMul.{u_1, u_1, u_1} g a)) (HSMul.hSMul.{u_1, u_1, u_1} g b))
        (HSMul.hSMul.{u_1, u_1, u_1} g ((β a) b)))
  (hβc : Continuous.{u_1, u_1} fun x => (β x.1) x.2)
  (ΔPp : ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.{u_1} R G Gv loc A)
  (ΔP : ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.{u_1} R G Gv loc B)
  (I : ZInQ.Manuscript.RC.SelmerComplex.IsotropyData.{u_1} R G Gv loc β hβ hβc ΔPp ΔP) (v : Sum.{u_1, u_1} Vo Vn)
  (i j l : ℤ) (h : Eq.{1} (HAdd.hAdd.{0, 0, 0} i j) (HAdd.hAdd.{0, 0, 0} l 1))
  (a :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
        (ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.U.{u_1}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.zeroAt.{u_1} ΔPp) v)
        i))
  (b :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
        (ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.U.{u_1} ΔP v) j)),
  Eq.{u_1 + 1}
    (((ZInQ.Manuscript.RC.SelmerComplex.IsotropyData.h.{u_1} ⋯ v i j l h) a)
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{u_1} ⋯ j j ⋯) b))
    (((ZInQ.Manuscript.RC.SelmerComplex.IsotropyData.h.{u_1} I v i j l h) (⋯ a)) b)
'ZInQ.Contrib.RC53Assist.CoordProvenance.relaxedIsotropy_retained' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.actual_cup_naturality.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  {G : Type u_1} [inst_1 : Group.{u_1} G] [inst_2 : TopologicalSpace.{u_1} G] [inst_3 : IsTopologicalGroup.{u_1} G]
  {Vo Vn : Type u_1} {Gv : Sum.{u_1, u_1} Vo Vn → Type u_1} [inst_4 : (v : Sum.{u_1, u_1} Vo Vn) → Group.{u_1} (Gv v)]
  [inst_5 : (v : Sum.{u_1, u_1} Vo Vn) → TopologicalSpace.{u_1} (Gv v)]
  [inst_6 : ∀ (v : Sum.{u_1, u_1} Vo Vn), IsTopologicalGroup.{u_1} (Gv v)]
  {loc : (v : Sum.{u_1, u_1} Vo Vn) → ContinuousMonoidHom.{u_1, u_1} (Gv v) G} {A B T : Type u_1}
  [inst_7 : AddCommGroup.{u_1} A] [inst_8 : Module.{u_1, u_1} R A] [inst_9 : DistribMulAction.{u_1, u_1} G A]
  [inst_10 : SMulCommClass.{u_1, u_1, u_1} G R A] [inst_11 : TopologicalSpace.{u_1} A] [inst_12 : ContinuousAdd.{u_1} A]
  [inst_13 : ContinuousConstSMul.{u_1, u_1} R A] [inst_14 : ContinuousSMul.{u_1, u_1} G A]
  [inst_15 : AddCommGroup.{u_1} B] [inst_16 : Module.{u_1, u_1} R B] [inst_17 : DistribMulAction.{u_1, u_1} G B]
  [inst_18 : SMulCommClass.{u_1, u_1, u_1} G R B] [inst_19 : TopologicalSpace.{u_1} B] [inst_20 : ContinuousAdd.{u_1} B]
  [inst_21 : ContinuousConstSMul.{u_1, u_1} R B] [inst_22 : ContinuousSMul.{u_1, u_1} G B]
  [inst_23 : AddCommGroup.{u_1} T] [inst_24 : Module.{u_1, u_1} R T] [inst_25 : DistribMulAction.{u_1, u_1} G T]
  [inst_26 : SMulCommClass.{u_1, u_1, u_1} G R T] [inst_27 : TopologicalSpace.{u_1} T] [inst_28 : ContinuousAdd.{u_1} T]
  [inst_29 : ContinuousConstSMul.{u_1, u_1} R T] [inst_30 : ContinuousSMul.{u_1, u_1} G T]
  (β : LinearMap.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} R) A (LinearMap.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} R) B T))
  (hβ :
    ∀ (g : G) (a : A) (b : B),
      Eq.{u_1 + 1} ((β (HSMul.hSMul.{u_1, u_1, u_1} g a)) (HSMul.hSMul.{u_1, u_1, u_1} g b))
        (HSMul.hSMul.{u_1, u_1, u_1} g ((β a) b)))
  (hβc : Continuous.{u_1, u_1} fun x => (β x.1) x.2)
  (ΔPp : ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.{u_1} R G Gv loc A)
  (ΔP : ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.{u_1} R G Gv loc B)
  (I : ZInQ.Manuscript.RC.SelmerComplex.IsotropyData.{u_1} R G Gv loc β hβ hβc ΔPp ΔP) (i j n : ℤ)
  (h : Eq.{1} (HAdd.hAdd.{0, 0, 0} i j) n)
  (s :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{u_1}
          (ZInQ.Manuscript.RC.SelmerComplex.selData.{u_1} R G Gv loc A
            (ZInQ.Contrib.RC53Assist.CoordProvenance.zeroAt.{u_1} ΔPp)))
        i))
  (p :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{u_1}
          (ZInQ.Manuscript.RC.SelmerComplex.selData.{u_1} R G Gv loc B ΔP))
        j)),
  Eq.{u_1 + 1}
    (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCup.{u_1} ⋯ i j n h) s)
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GHom.f.{u_1} ⋯ j j ⋯) p))
    (((ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCup.{u_1} ⋯ i j n h) (⋯ s)) p)
'ZInQ.Contrib.RC53Assist.CoordProvenance.actual_cup_naturality' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.actual_pairedFunctional_natural.{u_1} : ∀ {R : Type u_1}
  [inst : CommRing.{u_1} R] {G : Type u_1} [inst_1 : Group.{u_1} G] [inst_2 : TopologicalSpace.{u_1} G]
  [inst_3 : IsTopologicalGroup.{u_1} G] {Vo Vn : Type u_1} {Gv : Sum.{u_1, u_1} Vo Vn → Type u_1}
  [inst_4 : (v : Sum.{u_1, u_1} Vo Vn) → Group.{u_1} (Gv v)]
  [inst_5 : (v : Sum.{u_1, u_1} Vo Vn) → TopologicalSpace.{u_1} (Gv v)]
  [inst_6 : ∀ (v : Sum.{u_1, u_1} Vo Vn), IsTopologicalGroup.{u_1} (Gv v)]
  {loc : (v : Sum.{u_1, u_1} Vo Vn) → ContinuousMonoidHom.{u_1, u_1} (Gv v) G} {A B T : Type u_1}
  [inst_7 : AddCommGroup.{u_1} A] [inst_8 : Module.{u_1, u_1} R A] [inst_9 : DistribMulAction.{u_1, u_1} G A]
  [inst_10 : SMulCommClass.{u_1, u_1, u_1} G R A] [inst_11 : TopologicalSpace.{u_1} A] [inst_12 : ContinuousAdd.{u_1} A]
  [inst_13 : ContinuousConstSMul.{u_1, u_1} R A] [inst_14 : ContinuousSMul.{u_1, u_1} G A]
  [inst_15 : AddCommGroup.{u_1} B] [inst_16 : Module.{u_1, u_1} R B] [inst_17 : DistribMulAction.{u_1, u_1} G B]
  [inst_18 : SMulCommClass.{u_1, u_1, u_1} G R B] [inst_19 : TopologicalSpace.{u_1} B] [inst_20 : ContinuousAdd.{u_1} B]
  [inst_21 : ContinuousConstSMul.{u_1, u_1} R B] [inst_22 : ContinuousSMul.{u_1, u_1} G B]
  [inst_23 : AddCommGroup.{u_1} T] [inst_24 : Module.{u_1, u_1} R T] [inst_25 : DistribMulAction.{u_1, u_1} G T]
  [inst_26 : SMulCommClass.{u_1, u_1, u_1} G R T] [inst_27 : TopologicalSpace.{u_1} T] [inst_28 : ContinuousAdd.{u_1} T]
  [inst_29 : ContinuousConstSMul.{u_1, u_1} R T] [inst_30 : ContinuousSMul.{u_1, u_1} G T]
  (β : LinearMap.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} R) A (LinearMap.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} R) B T))
  (hβ :
    ∀ (g : G) (a : A) (b : B),
      Eq.{u_1 + 1} ((β (HSMul.hSMul.{u_1, u_1, u_1} g a)) (HSMul.hSMul.{u_1, u_1, u_1} g b))
        (HSMul.hSMul.{u_1, u_1, u_1} g ((β a) b)))
  (hβc : Continuous.{u_1, u_1} fun x => (β x.1) x.2)
  (ΔPp : ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.{u_1} R G Gv loc A)
  (ΔP : ZInQ.Manuscript.RC.SelmerComplex.LocalConditions.{u_1} R G Gv loc B)
  (I : ZInQ.Manuscript.RC.SelmerComplex.IsotropyData.{u_1} R G Gv loc β hβ hβc ΔPp ΔP)
  (tr :
    LinearMap.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} R)
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{u_1}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{u_1}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.actualPrimitivePairData.{u_1} β hβ hβc ΔPp ΔP I)))
          3))
      R),
  (∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{u_1}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{u_1}
                (ZInQ.Contrib.RC53Assist.CoordProvenance.actualPrimitivePairData.{u_1} β hβ hβc ΔPp ΔP I)))
            2)),
      Eq.{u_1 + 1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{u_1}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{u_1} ⋯) 2 3 ⋯)
            c))
        0) →
    ∀
      (zS :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{u_1}
              (ZInQ.Manuscript.RC.SelmerComplex.selData.{u_1} R G Gv loc A
                (ZInQ.Contrib.RC53Assist.CoordProvenance.zeroAt.{u_1} ΔPp)))
            1))
      (zPp :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{u_1}
              (ZInQ.Manuscript.RC.SelmerComplex.selData.{u_1} R G Gv loc A ΔPp))
            1))
      (e : R) (b : ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1} ⋯ 0)), Eq.{u_1 + 1} ⋯ ⋯ → ∀ (w : ⋯), ⋯
'ZInQ.Contrib.RC53Assist.CoordProvenance.actual_pairedFunctional_natural' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

Compiler exit code: 0
```

## CohomologyLift

```text
@ZInQ.Contrib.RC53Assist.CoordProvenance.liftCycle_cochain.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  (C : CochainComplex.{u_1, u_1 + 1, 0} (ModuleCat.{u_1, u_1} R) ℤ) (n : ℤ)
  (x :
    ↥(LinearMap.ker.{u_1, u_1, u_1, u_1}
        (ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} C n (HAdd.hAdd.{0, 0, 0} n 1))))),
  Eq.{u_1 + 1}
    ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.iCycles.{u_1, u_1 + 1, 0} C n))
      ((ModuleCat.Hom.hom.{u_1, u_1} (ZInQ.Contrib.RC53Assist.CoordProvenance.liftCycle.{u_1} C n)) x))
    ↑x
'ZInQ.Contrib.RC53Assist.CoordProvenance.liftCycle_cochain' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.classOf_surjective.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  (C : CochainComplex.{u_1, u_1 + 1, 0} (ModuleCat.{u_1, u_1} R) ℤ) (n : ℤ),
  Function.Surjective.{u_1 + 1, u_1 + 1} ⇑(ZInQ.Contrib.RC53Assist.CoordProvenance.classOf.{u_1} C n)
'ZInQ.Contrib.RC53Assist.CoordProvenance.classOf_surjective' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.boundary_of_classOf_zero.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  (C : CochainComplex.{u_1, u_1 + 1, 0} (ModuleCat.{u_1, u_1} R) ℤ) (n : ℤ)
  (x :
    ↥(LinearMap.ker.{u_1, u_1, u_1, u_1}
        (ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} C n (HAdd.hAdd.{0, 0, 0} n 1))))),
  Eq.{u_1 + 1} ((ZInQ.Contrib.RC53Assist.CoordProvenance.classOf.{u_1} C n) x) 0 →
    ∃ b,
      Eq.{u_1 + 1}
        ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} C (HSub.hSub.{0, 0, 0} n 1) n)) b) ↑x
'ZInQ.Contrib.RC53Assist.CoordProvenance.boundary_of_classOf_zero' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.classOf_natural.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  {C D : CochainComplex.{u_1, u_1 + 1, 0} (ModuleCat.{u_1, u_1} R) ℤ} (f : Quiver.Hom.{u_1, u_1 + 1} C D) (n : ℤ)
  (x :
    ↥(LinearMap.ker.{u_1, u_1, u_1, u_1}
        (ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} C n (HAdd.hAdd.{0, 0, 0} n 1)))))
  (hf :
    Eq.{u_1 + 1}
      ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} D n (HAdd.hAdd.{0, 0, 0} n 1)))
        ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.Hom.f.{u_1, u_1 + 1, 0} f n)) ↑x))
      0),
  Eq.{u_1 + 1}
    ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.homologyMap.{u_1, u_1 + 1, 0} f n))
      ((ZInQ.Contrib.RC53Assist.CoordProvenance.classOf.{u_1} C n) x))
    ((ZInQ.Contrib.RC53Assist.CoordProvenance.classOf.{u_1} D n)
      (Subtype.mk.{u_1 + 1} ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.Hom.f.{u_1, u_1 + 1, 0} f n)) ↑x) ⋯))
'ZInQ.Contrib.RC53Assist.CoordProvenance.classOf_natural' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.exists_lift_with_boundary.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  {C D : CochainComplex.{u_1, u_1 + 1, 0} (ModuleCat.{u_1, u_1} R) ℤ} (f : Quiver.Hom.{u_1, u_1 + 1} C D),
  QuasiIso.{u_1, u_1 + 1, 0} f →
    ∀ (n : ℤ) (z : ↑(HomologicalComplex.X.{u_1, u_1 + 1, 0} D n)),
      Eq.{u_1 + 1}
          ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} D n (HAdd.hAdd.{0, 0, 0} n 1))) z) 0 →
        ∃ a,
          Eq.{u_1 + 1}
              ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} C n (HAdd.hAdd.{0, 0, 0} n 1))) a)
              0 ∧
            ∃ b,
              Eq.{u_1 + 1}
                (HSub.hSub.{u_1, u_1, u_1}
                  ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.Hom.f.{u_1, u_1 + 1, 0} f n)) a) z)
                ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} D (HSub.hSub.{0, 0, 0} n 1) n))
                  b)
'ZInQ.Contrib.RC53Assist.CoordProvenance.exists_lift_with_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.lifts_differ_by_boundary.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  {C D : CochainComplex.{u_1, u_1 + 1, 0} (ModuleCat.{u_1, u_1} R) ℤ} (f : Quiver.Hom.{u_1, u_1 + 1} C D),
  QuasiIso.{u_1, u_1 + 1, 0} f →
    ∀ (n : ℤ) (a a' : ↑(HomologicalComplex.X.{u_1, u_1 + 1, 0} C n)),
      Eq.{u_1 + 1}
          ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} C n (HAdd.hAdd.{0, 0, 0} n 1))) a) 0 →
        Eq.{u_1 + 1}
            ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} C n (HAdd.hAdd.{0, 0, 0} n 1))) a')
            0 →
          ∀ (b : ↑(HomologicalComplex.X.{u_1, u_1 + 1, 0} D (HSub.hSub.{0, 0, 0} n 1))),
            Eq.{u_1 + 1}
                (HSub.hSub.{u_1, u_1, u_1}
                  ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.Hom.f.{u_1, u_1 + 1, 0} f n)) a)
                  ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.Hom.f.{u_1, u_1 + 1, 0} f n)) a'))
                ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} D (HSub.hSub.{0, 0, 0} n 1) n))
                  b) →
              ∃ c,
                Eq.{u_1 + 1} (HSub.hSub.{u_1, u_1, u_1} a a')
                  ((ModuleCat.Hom.hom.{u_1, u_1} (HomologicalComplex.d.{u_1, u_1 + 1, 0} C (HSub.hSub.{0, 0, 0} n 1) n))
                    c)
'ZInQ.Contrib.RC53Assist.CoordProvenance.lifts_differ_by_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.rowOf_apply.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R] {ι : Type u_1}
  [inst_1 : Fintype.{u_1} ι] [inst_2 : DecidableEq.{u_1 + 1} ι]
  (L : LinearMap.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} R) (ι → R) R) (x : ι → R),
  Eq.{u_1 + 1} (L x) (dotProduct.{u_1, u_1} (ZInQ.Contrib.RC53Assist.CoordProvenance.rowOf.{u_1} L) x)
'ZInQ.Contrib.RC53Assist.CoordProvenance.rowOf_apply' depends on axioms: [propext, Classical.choice.{u}, Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.rowOf_closed.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  {ι κ : Type u_1} [inst_1 : Fintype.{u_1} ι] [inst_2 : DecidableEq.{u_1 + 1} ι] [inst_3 : Fintype.{u_1} κ]
  [DecidableEq.{u_1 + 1} κ] (L : LinearMap.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} R) (ι → R) R)
  (A : Matrix.{u_1, u_1, u_1} ι κ R),
  (∀ (x : κ → R), Eq.{u_1 + 1} (L (Matrix.mulVec.{u_1, u_1, u_1} A x)) 0) →
    Eq.{u_1 + 1} (Matrix.vecMul.{u_1, u_1, u_1} (ZInQ.Contrib.RC53Assist.CoordProvenance.rowOf.{u_1} L) A) 0
'ZInQ.Contrib.RC53Assist.CoordProvenance.rowOf_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.rowOf_scalar_value.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  {ι : Type u_1} [inst_1 : Fintype.{u_1} ι] [inst_2 : DecidableEq.{u_1 + 1} ι] {F : Type u_1}
  [inst_3 : CommRing.{u_1} F] (φ : RingHom.{u_1, u_1} R F)
  (L : LinearMap.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} R) (ι → R) R) (x : ι → R),
  Eq.{u_1 + 1}
    (dotProduct.{u_1, u_1}
      (Function.comp.{u_1 + 1, u_1 + 1, u_1 + 1} (⇑φ) (ZInQ.Contrib.RC53Assist.CoordProvenance.rowOf.{u_1} L))
      (Function.comp.{u_1 + 1, u_1 + 1, u_1 + 1} (⇑φ) x))
    (φ (L x))
'ZInQ.Contrib.RC53Assist.CoordProvenance.rowOf_scalar_value' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.pairedFun_closed.{u_1} : ∀ {R : Type u_1} [inst : CommRing.{u_1} R]
  {D D' : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData.{u_1} R}
  (P : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.{u_1} D D')
  (tr :
    LinearMap.{u_1, u_1, u_1, u_1} (RingHom.id.{u_1} R)
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
          (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{u_1}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{u_1} P))
          3))
      R),
  (∀
      (c :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{u_1}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{u_1} P))
            2)),
      Eq.{u_1 + 1}
        (tr
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{u_1}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.coneCx.{u_1}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelPairData.resE.{u_1} P))
              2 3 ⋯)
            c))
        0) →
    ∀
      (z :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
            (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{u_1} D) 1)),
      Eq.{u_1 + 1}
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{u_1}
              (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{u_1} D) 1 2 ⋯)
            z)
          0 →
        ∀
          (w :
            ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{u_1}
                (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{u_1} D') 1)),
          Eq.{u_1 + 1}
            ((ZInQ.Contrib.CloudB3RC53.CommonCoordinate.pairedFun.{u_1} P tr z)
              ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{u_1}
                  (ZInQ.Contrib.CloudB3RC53.PairedFunctional.selCx.{u_1} D') 1 2 ⋯)
                w))
            0
'ZInQ.Contrib.RC53Assist.CoordProvenance.pairedFun_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.actual_class_has_model_cycle : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {b dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS b dK hK cE tK)
  (zSel :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M))
        1)),
  Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          1 2 ⋯)
        zSel)
      0 →
    ∃ z,
      Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d1.{0} M.D) z) 0 ∧
        ∃ c,
          Eq.{1} (HSub.hSub.{0, 0, 0} ((ModuleCat.Hom.hom.{0, 0} (HomologicalComplex.Hom.f.{0, 1, 0} M.ψf 1)) z) zSel)
            ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 0 1 ⋯)
              c)
'ZInQ.Contrib.RC53Assist.CoordProvenance.actual_class_has_model_cycle' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG_value : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {b dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS b dK hK cE tK)
  (L :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          2))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (v :
    Sum.{0, 0} (Sum.{0, 0} (Fin M.C.m1) (Sum.{0, 0} Unit (Fin M.C.m2))) M.C.N →
      MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)),
  Eq.{1} (L ((ModuleCat.Hom.hom.{0, 0} (HomologicalComplex.Hom.f.{0, 1, 0} M.ψf 2)) v))
    (dotProduct.{0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG M L) v)
'ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG_value' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG_closed : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {b dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS b dK hK cE tK)
  (L :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          2))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))),
  (∀
      (w :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1)),
      Eq.{1}
        (L
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1 2 ⋯)
            w))
        0) →
    Eq.{1}
      (Matrix.vecMul.{0, 0, 0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG M L)
        (Matrix.fromRows.{0, 0, 0, 0} (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)).X
          (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)).Y))
      0
'ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG_closed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.same_class_and_functional_in_model : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {b dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS b dK hK cE tK)
  (zSel :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M))
        1)),
  Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          1 2 ⋯)
        zSel)
      0 →
    ∀
      (L :
        LinearMap.{0, 0, 0, 0}
          (RingHom.id.{0}
            (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
          (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 2))
          (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))),
      (∀
          (w :
            ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
                (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1)),
          Eq.{1}
            (L
              ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                  (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1 2 ⋯)
                w))
            0) →
        ∃ z lam,
          Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d1.{0} M.D) z) 0 ∧
            Eq.{1}
                (Matrix.vecMul.{0, 0, 0} lam
                  (Matrix.fromRows.{0, 0, 0, 0} (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)).X
                    (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)).Y))
                0 ∧
              (∃ c,
                  Eq.{1}
                    (HSub.hSub.{0, 0, 0} ((ModuleCat.Hom.hom.{0, 0} (HomologicalComplex.Hom.f.{0, 1, 0} M.ψf 1)) z)
                      zSel)
                    ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
                        (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 0 1 ⋯)
                      c)) ∧
                ∀
                  (v :
                    ↑(HomologicalComplex.X.{0, 1, 0}
                        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
                          (M.C.map (ZInQ.Contrib.CloudB3RC53.ClearingComplex.φO b)).toGCx)
                        2)),
                  Eq.{1} (L ((ModuleCat.Hom.hom.{0, 0} (HomologicalComplex.Hom.f.{0, 1, 0} M.ψf 2)) v))
                    (dotProduct.{0, 0} lam v)
'ZInQ.Contrib.RC53Assist.CoordProvenance.same_class_and_functional_in_model' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.actualCycleG_spec : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {b dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS b dK hK cE tK)
  (zSel :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M))
        1))
  (hzSel :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          1 2 ⋯)
        zSel)
      0),
  Eq.{1}
      (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d1.{0} M.D)
        (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCycleG M zSel hzSel))
      0 ∧
    ∃ c,
      Eq.{1}
        (HSub.hSub.{0, 0, 0}
          ((ModuleCat.Hom.hom.{0, 0} (HomologicalComplex.Hom.f.{0, 1, 0} M.ψf 1))
            (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCycleG M zSel hzSel))
          zSel)
        ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 0 1 ⋯)
          c)
'ZInQ.Contrib.RC53Assist.CoordProvenance.actualCycleG_spec' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG_provenance : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {b dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS b dK hK cE tK)
  (zSel :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M))
        1))
  (hzSel :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          1 2 ⋯)
        zSel)
      0)
  (L :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          2))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))),
  ZInQ.Contrib.RC53Assist.CoordLink.RankOneCoordinateProvenanceG M
    (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG M zSel hzSel L)
    (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCycleG M zSel hzSel)
    (ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG M L)
'ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG_provenance' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG_convention : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {b dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS b dK hK cE tK)
  (zSel :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M))
        1))
  (hzSel :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          1 2 ⋯)
        zSel)
      0)
  (L :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          2))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))),
  ZInQ.Contrib.RC53Assist.CoordLink.AcyclicCoordinateConventionG M
    (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG M zSel hzSel L)
'ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG_convention' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.relIsKMG_actualCoordinateG : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {b dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS b dK hK cE tK)
  (zSel :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M))
        1))
  (hzSel :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          1 2 ⋯)
        zSel)
      0)
  (L :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          2))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (hL :
    ∀
      (w :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1)),
      Eq.{1}
        (L
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1 2 ⋯)
            w))
        0),
  ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M
    (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG M zSel hzSel L)
    (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCycleG M zSel hzSel)
    (ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG M L) ⋯ ⋯
'ZInQ.Contrib.RC53Assist.CoordProvenance.relIsKMG_actualCoordinateG' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.alphaB_add_boundary : ∀ {F : Type} [inst : Field.{0} F]
  (E : ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.{0} F),
  IsUnit.{0} (Matrix.det.{0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.A0.{0} E)) →
    ∀
      (z :
        Sum.{0, 0} (Fin (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.m0.{0} E))
            (Sum.{0, 0} Unit (Fin (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.m1.{0} E))) →
          F)
      (c : Fin (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.m0.{0} E) → F),
      Eq.{1}
        (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.alphaB.{0} E
          (HAdd.hAdd.{0, 0, 0} z
            (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d0.{0} E) c)))
        (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.alphaB.{0} E z)
'ZInQ.Contrib.RC53Assist.CoordProvenance.alphaB_add_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG_of_lift : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {b dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS b dK hK cE tK)
  (zSel :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M))
        1))
  (hzSel :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          1 2 ⋯)
        zSel)
      0)
  (L :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          2))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (hL :
    ∀
      (w :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1)),
      Eq.{1}
        (L
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1 2 ⋯)
            w))
        0)
  (z :
    Sum.{0, 0} (Fin (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.m0.{0} M.D))
        (Sum.{0, 0} Unit (Fin (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.m1.{0} M.D))) →
      MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b))
  (hz : Eq.{1} (Matrix.mulVec.{0, 0, 0} (ZInQ.Contrib.CloudB3RC53.ClearingComplex.BlockComplex.d1.{0} M.D) z) 0)
  (c :
    ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
        0)),
  Eq.{1} (HSub.hSub.{0, 0, 0} ((ModuleCat.Hom.hom.{0, 0} (HomologicalComplex.Hom.f.{0, 1, 0} M.ψf 1)) z) zSel)
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          0 1 ⋯)
        c) →
    ∀ (x : ZInQ.Manuscript.RC.Addr b),
      Ne.{1}
          ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x))
            (ZInQ.Manuscript.RC.Determinant.SmithBlocks.Δ.{0, 0} M.toIdentification.B))
          0 →
        Eq.{1}
          (ZInQ.Contrib.CloudB3RC53.CoordLink.kmOrig M z (ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG M L)
            hz ⋯ x)
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG M zSel hzSel L x)
'ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG_of_lift' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.provenance_of_actual_dictionary : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {b dK hK cE tK : ℕ}
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS b dK hK cE tK)
  (zSel :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M))
        1))
  (hzSel :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          1 2 ⋯)
        zSel)
      0)
  (L :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          2))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup b)))
  (hL :
    ∀
      (w :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1)),
      Eq.{1}
        (L
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1 2 ⋯)
            w))
        0)
  (urel : ZInQ.Manuscript.RC.Addr b → FractionRing.{0} ZInQ.Manuscript.RC.Determinant.OO),
  (∀ (x : ZInQ.Manuscript.RC.Determinant.Addr b),
      Ne.{1}
          ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x))
            (ZInQ.Manuscript.RC.Determinant.SmithBlocks.Δ.{0, 0} M.toIdentification.B))
          0 →
        Eq.{1} (urel x) (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG M zSel hzSel L x)) →
    ZInQ.Contrib.RC53Assist.CoordLink.RankOneCoordinateProvenanceG M urel
        (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCycleG M zSel hzSel)
        (ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG M L) ∧
      ZInQ.Contrib.RC53Assist.CoordLink.AcyclicCoordinateConventionG M urel ∧
        ZInQ.Contrib.CloudB3RC53.CoordLink.RelIsKMG M urel
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCycleG M zSel hzSel)
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG M L) ⋯ ⋯
'ZInQ.Contrib.RC53Assist.CoordProvenance.provenance_of_actual_dictionary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.origCoordLink_of_actual_dictionary : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {dK hK cE tK ℓ : ℕ}
  (Dd : ZInQ.Manuscript.RC.RCData ℓ) (F : ZInQ.Manuscript.RC.Family)
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS F.b dK hK cE tK)
  (zSel :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M))
        1))
  (hzSel :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          1 2 ⋯)
        zSel)
      0)
  (L :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          2))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b)))
  (hL :
    ∀
      (w :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1)),
      Eq.{1}
        (L
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1 2 ⋯)
            w))
        0)
  (η : MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b))
  (urel : ZInQ.Manuscript.RC.Addr F.b → FractionRing.{0} ZInQ.Manuscript.RC.Determinant.OO),
  ZInQ.Contrib.CloudB3RC53.CoordLink.CorrectedIsEta Dd F η urel →
    (∀ (x : ZInQ.Manuscript.RC.Determinant.Addr F.b),
        Ne.{1}
            ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x))
              (ZInQ.Manuscript.RC.Determinant.SmithBlocks.Δ.{0, 0} M.toIdentification.B))
            0 →
          Eq.{1} (urel x) (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG M zSel hzSel L x)) →
      ZInQ.Manuscript.RC.Wiring.OrigCoordLink Dd F M (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCycleG M zSel hzSel)
        (ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG M L) ⋯ ⋯ η
'ZInQ.Contrib.RC53Assist.CoordProvenance.origCoordLink_of_actual_dictionary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.origCoordLink_iff_actual_dictionary : ∀ {K : Type} [inst : Field.{0} K]
  [inst_1 : NumberField.{0} K]
  {S S' : Set.{0} (IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} K))} {hS : S ⊆ S'}
  [inst_2 : Fintype.{0} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')]
  [inst_3 : DecidableEq.{1} (ZInQ.Manuscript.RC.SelmerComplex.NewPlaces K S S')] {dK hK cE tK ℓ : ℕ}
  (Dd : ZInQ.Manuscript.RC.RCData ℓ) (F : ZInQ.Manuscript.RC.Family)
  (M : ZInQ.Contrib.CloudB3RC53.ClearingComplex.Identification2G K S S' hS F.b dK hK cE tK)
  (zSel :
    ↑(HomologicalComplex.X.{0, 1, 0}
        (ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.toCC.{0}
          (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M))
        1))
  (hzSel :
    Eq.{1}
      ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          1 2 ⋯)
        zSel)
      0)
  (L :
    LinearMap.{0, 0, 0, 0}
      (RingHom.id.{0}
        (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b)))
      (↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0} (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M)
          2))
      (MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b)))
  (hL :
    ∀
      (w :
        ↑(ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.X.{0}
            (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1)),
      Eq.{1}
        (L
          ((ZInQ.Contrib.CloudB3RC53.PairedFunctional.GCx.d.{0}
              (ZInQ.Contrib.RC53Assist.CoordProvenance.actualSelmerCxG M) 1 2 ⋯)
            w))
        0)
  (η : MonoidAlgebra.{0, 0} ZInQ.Manuscript.RC.Determinant.OO (ZInQ.Manuscript.RC.Determinant.SignGroup F.b))
  (urel : ZInQ.Manuscript.RC.Addr F.b → FractionRing.{0} ZInQ.Manuscript.RC.Determinant.OO),
  ZInQ.Contrib.CloudB3RC53.CoordLink.CorrectedIsEta Dd F η urel →
    ∀ (e₀ : ZInQ.Manuscript.RC.Addr F.b → ℕ) (g₀ : ZInQ.Manuscript.RC.Addr F.b → ZInQ.Manuscript.RC.Determinant.Lam),
      ZInQ.Manuscript.RC.Wiring.UTildeRep Dd F e₀ g₀ →
        (∀ (x : ZInQ.Manuscript.RC.Determinant.Addr F.b),
            Ne.{1}
                ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x))
                  (ZInQ.Manuscript.RC.Determinant.SmithBlocks.Δ.{0, 0} M.toIdentification.B))
                0 →
              Ne.{1} ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x)) η) 0) →
          (ZInQ.Manuscript.RC.Wiring.OrigCoordLink Dd F M
              (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCycleG M zSel hzSel)
              (ZInQ.Contrib.RC53Assist.CoordProvenance.actualModelRowG M L) ⋯ ⋯ η ↔
            ∀ (x : ZInQ.Manuscript.RC.Determinant.Addr F.b),
              Ne.{1}
                  ((ZInQ.Manuscript.RC.Determinant.evK.{0, 0} (ZInQ.Manuscript.RC.Determinant.sgnChar x))
                    (ZInQ.Manuscript.RC.Determinant.SmithBlocks.Δ.{0, 0} M.toIdentification.B))
                  0 →
                Eq.{1} (urel x) (ZInQ.Contrib.RC53Assist.CoordProvenance.actualCoordinateG M zSel hzSel L x))
'ZInQ.Contrib.RC53Assist.CoordProvenance.origCoordLink_iff_actual_dictionary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

Compiler exit code: 0
```

## RepresentativeIndependence

```text
@ZInQ.Contrib.RC53Assist.CoordProvenance.classBoundaryShear_det.{u_1, u_2, u_3, u_4,
    u_5} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  [inst_1 : Fintype.{u_2} ι0] [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3]
  [inst_5 : DecidableEq.{u_2 + 1} ι0] [inst_6 : DecidableEq.{u_3 + 1} ι1] [inst_7 : DecidableEq.{u_4 + 1} ι2]
  [inst_8 : DecidableEq.{u_5 + 1} ι3]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3) (z : ι1 → K) (lam : ι2 → K)
  (hz :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) z) 0)
  (hlam :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (b : ι0 → K),
  Eq.{u_1 + 1}
    (Matrix.det.{u_1, max u_2 u_4}
      (ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.Qe.{u_1, max u_2 u_4, max u_3 u_5}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.classBoundaryShear.{u_1, u_2, u_3, u_4, u_5} C z lam hz hlam b)))
    1
'ZInQ.Contrib.RC53Assist.CoordProvenance.classBoundaryShear_det' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.classBoundaryShear_rebase.{u_1, u_2, u_3, u_4,
    u_5} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  [inst_1 : Fintype.{u_2} ι0] [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3]
  [inst_5 : DecidableEq.{u_2 + 1} ι0] [inst_6 : DecidableEq.{u_3 + 1} ι1] [inst_7 : DecidableEq.{u_4 + 1} ι2]
  [inst_8 : DecidableEq.{u_5 + 1} ι3]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3) (z : ι1 → K) (lam : ι2 → K)
  (hz :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) z) 0)
  (hlam :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (b : ι0 → K)
  (hz' :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)
        (HAdd.hAdd.{max u_1 u_3, max u_1 u_3, max u_1 u_3} z
          (Matrix.mulVec.{u_1, u_3, u_2} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{u_1, u_2, u_3, u_4, u_5} C) b)))
      0),
  Eq.{max (max (max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1)) (u_4 + 1)) (u_5 + 1)}
    (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{u_1, u_2, u_3, u_4, u_5}
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{u_1, u_2, u_3, u_4, u_5} C
        (HAdd.hAdd.{max u_1 u_3, max u_1 u_3, max u_1 u_3} z
          (Matrix.mulVec.{u_1, u_3, u_2} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{u_1, u_2, u_3, u_4, u_5} C) b))
        lam hz' hlam))
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{u_1, max u_2 u_4, max u_3 u_5}
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{u_1, u_2, u_3, u_4, u_5}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{u_1, u_2, u_3, u_4, u_5} C z lam hz hlam))
      (ZInQ.Contrib.RC53Assist.CoordProvenance.classBoundaryShear.{u_1, u_2, u_3, u_4, u_5} C z lam hz hlam b))
'ZInQ.Contrib.RC53Assist.CoordProvenance.classBoundaryShear_rebase' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.kmCoord_class_boundary.{u_1, u_2, u_3, u_4,
    u_5} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  [inst_1 : Fintype.{u_2} ι0] [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3]
  [inst_5 : DecidableEq.{u_2 + 1} ι0] [inst_6 : DecidableEq.{u_3 + 1} ι1] [inst_7 : DecidableEq.{u_4 + 1} ι2]
  [inst_8 : DecidableEq.{u_5 + 1} ι3]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3) (z : ι1 → K) (lam : ι2 → K)
  (hz :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) z) 0)
  (hlam :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (b : ι0 → K)
  (hz' :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)
        (HAdd.hAdd.{max u_1 u_3, max u_1 u_3, max u_1 u_3} z
          (Matrix.mulVec.{u_1, u_3, u_2} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{u_1, u_2, u_3, u_4, u_5} C) b)))
      0)
  (σ :
    Equiv.{max (u_4 + 1) (u_2 + 1), max (u_5 + 1) (u_3 + 1)} (Sum.{u_2, u_4} (Sum.{u_2, 0} ι0 Unit) ι2)
      (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit))),
  Eq.{u_1 + 1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_2, u_3, u_4, u_5} C
      (HAdd.hAdd.{max u_1 u_3, max u_1 u_3, max u_1 u_3} z
        (Matrix.mulVec.{u_1, u_3, u_2} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{u_1, u_2, u_3, u_4, u_5} C) b))
      lam hz' hlam σ)
    (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_2, u_3, u_4, u_5} C z lam hz hlam σ)
'ZInQ.Contrib.RC53Assist.CoordProvenance.kmCoord_class_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.functionalBoundaryShear_det.{u_1, u_2, u_3, u_4,
    u_5} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  [inst_1 : Fintype.{u_2} ι0] [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3]
  [inst_5 : DecidableEq.{u_2 + 1} ι0] [inst_6 : DecidableEq.{u_3 + 1} ι1] [inst_7 : DecidableEq.{u_4 + 1} ι2]
  [inst_8 : DecidableEq.{u_5 + 1} ι3]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3) (z : ι1 → K) (lam : ι2 → K)
  (hz :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) z) 0)
  (hlam :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (r : ι3 → K),
  Eq.{u_1 + 1}
    (Matrix.det.{u_1, max u_3 u_5}
      (ZInQ.Contrib.CloudB3RC53.Torsion.GradedBasisChange.Po.{u_1, max u_2 u_4, max u_3 u_5}
        (ZInQ.Contrib.RC53Assist.CoordProvenance.functionalBoundaryShear.{u_1, u_2, u_3, u_4, u_5} C z lam hz hlam r)))
    1
'ZInQ.Contrib.RC53Assist.CoordProvenance.functionalBoundaryShear_det' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.functionalBoundaryShear_rebase.{u_1, u_2, u_3, u_4,
    u_5} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  [inst_1 : Fintype.{u_2} ι0] [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3]
  [inst_5 : DecidableEq.{u_2 + 1} ι0] [inst_6 : DecidableEq.{u_3 + 1} ι1] [inst_7 : DecidableEq.{u_4 + 1} ι2]
  [inst_8 : DecidableEq.{u_5 + 1} ι3]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3) (z : ι1 → K) (lam : ι2 → K)
  (hz :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) z) 0)
  (hlam :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (r : ι3 → K)
  (hlam' :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3}
        (HAdd.hAdd.{max u_1 u_4, max u_1 u_4, max u_1 u_4} lam
          (Matrix.vecMul.{u_1, u_5, u_4} r (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{u_1, u_2, u_3, u_4, u_5} C)))
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C))
      0),
  Eq.{max (max (max (max (u_1 + 1) (u_2 + 1)) (u_3 + 1)) (u_4 + 1)) (u_5 + 1)}
    (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{u_1, u_2, u_3, u_4, u_5}
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{u_1, u_2, u_3, u_4, u_5} C z
        (HAdd.hAdd.{max u_1 u_4, max u_1 u_4, max u_1 u_4} lam
          (Matrix.vecMul.{u_1, u_5, u_4} r (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{u_1, u_2, u_3, u_4, u_5} C)))
        hz hlam'))
    (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.rebase.{u_1, max u_2 u_4, max u_3 u_5}
      (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.toBased.{u_1, u_2, u_3, u_4, u_5}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.aug.{u_1, u_2, u_3, u_4, u_5} C z lam hz hlam))
      (ZInQ.Contrib.RC53Assist.CoordProvenance.functionalBoundaryShear.{u_1, u_2, u_3, u_4, u_5} C z lam hz hlam r))
'ZInQ.Contrib.RC53Assist.CoordProvenance.functionalBoundaryShear_rebase' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.kmCoord_functional_boundary.{u_1, u_2, u_3, u_4,
    u_5} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  [inst_1 : Fintype.{u_2} ι0] [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3]
  [inst_5 : DecidableEq.{u_2 + 1} ι0] [inst_6 : DecidableEq.{u_3 + 1} ι1] [inst_7 : DecidableEq.{u_4 + 1} ι2]
  [inst_8 : DecidableEq.{u_5 + 1} ι3]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3) (z : ι1 → K) (lam : ι2 → K)
  (hz :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) z) 0)
  (hlam :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (r : ι3 → K)
  (hlam' :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3}
        (HAdd.hAdd.{max u_1 u_4, max u_1 u_4, max u_1 u_4} lam
          (Matrix.vecMul.{u_1, u_5, u_4} r (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{u_1, u_2, u_3, u_4, u_5} C)))
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C))
      0)
  (σ :
    Equiv.{max (u_4 + 1) (u_2 + 1), max (u_5 + 1) (u_3 + 1)} (Sum.{u_2, u_4} (Sum.{u_2, 0} ι0 Unit) ι2)
      (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit))),
  Eq.{u_1 + 1}
    (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_2, u_3, u_4, u_5} C z
      (HAdd.hAdd.{max u_1 u_4, max u_1 u_4, max u_1 u_4} lam
        (Matrix.vecMul.{u_1, u_5, u_4} r (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{u_1, u_2, u_3, u_4, u_5} C)))
      hz hlam' σ)
    (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_2, u_3, u_4, u_5} C z lam hz hlam σ)
'ZInQ.Contrib.RC53Assist.CoordProvenance.kmCoord_functional_boundary' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.classBoundaryCycle.{u_1, u_2, u_3, u_4,
    u_5} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  [inst_1 : Fintype.{u_2} ι0] [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3) (z : ι1 → K),
  Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) z) 0 →
    ∀ (b : ι0 → K),
      Eq.{max (u_1 + 1) (u_4 + 1)}
        (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)
          (HAdd.hAdd.{max u_1 u_3, max u_1 u_3, max u_1 u_3} z
            (Matrix.mulVec.{u_1, u_3, u_2} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{u_1, u_2, u_3, u_4, u_5} C) b)))
        0
'ZInQ.Contrib.RC53Assist.CoordProvenance.classBoundaryCycle' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.functionalBoundaryClosed.{u_1, u_2, u_3, u_4,
    u_5} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  [inst_1 : Fintype.{u_3} ι1] [inst_2 : Fintype.{u_4} ι2] [inst_3 : Fintype.{u_5} ι3]
  (C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3) (lam : ι2 → K),
  Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lam (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0 →
    ∀ (r : ι3 → K),
      Eq.{max (u_1 + 1) (u_3 + 1)}
        (Matrix.vecMul.{u_1, u_4, u_3}
          (HAdd.hAdd.{max u_1 u_4, max u_1 u_4, max u_1 u_4} lam
            (Matrix.vecMul.{u_1, u_5, u_4} r (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{u_1, u_2, u_3, u_4, u_5} C)))
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C))
        0
'ZInQ.Contrib.RC53Assist.CoordProvenance.functionalBoundaryClosed' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]
@ZInQ.Contrib.RC53Assist.CoordProvenance.kmCoord_retained_cohomology_comparison.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8,
    u_9} : ∀ {K : Type u_1} [inst : Field.{u_1} K] {ι0 : Type u_2} {ι1 : Type u_3} {ι2 : Type u_4} {ι3 : Type u_5}
  {ι0' : Type u_6} {ι1' : Type u_7} {ι2' : Type u_8} {ι3' : Type u_9} [inst_1 : Fintype.{u_2} ι0]
  [inst_2 : Fintype.{u_3} ι1] [inst_3 : Fintype.{u_4} ι2] [inst_4 : Fintype.{u_5} ι3] [inst_5 : Fintype.{u_6} ι0']
  [inst_6 : Fintype.{u_7} ι1'] [inst_7 : Fintype.{u_8} ι2'] [inst_8 : Fintype.{u_9} ι3']
  [inst_9 : DecidableEq.{u_2 + 1} ι0] [inst_10 : DecidableEq.{u_3 + 1} ι1] [inst_11 : DecidableEq.{u_4 + 1} ι2]
  [inst_12 : DecidableEq.{u_5 + 1} ι3] [inst_13 : DecidableEq.{u_6 + 1} ι0'] [inst_14 : DecidableEq.{u_7 + 1} ι1']
  [inst_15 : DecidableEq.{u_8 + 1} ι2'] [inst_16 : DecidableEq.{u_9 + 1} ι3']
  {C : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_2, u_3, u_4, u_5} K ι0 ι1 ι2 ι3}
  {D : ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.{u_1, u_6, u_7, u_8, u_9} K ι0' ι1' ι2' ι3'}
  (F : ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} C D) (zC : ι1 → K)
  (lC : ι2 → K)
  (hzC :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.mulVec.{u_1, u_4, u_3} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C) zC) 0)
  (hlC :
    Eq.{max (u_1 + 1) (u_3 + 1)}
      (Matrix.vecMul.{u_1, u_4, u_3} lC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_2, u_3, u_4, u_5} C)) 0)
  (zD : ι1' → K) (lD : ι2' → K)
  (hzD :
    Eq.{max (u_1 + 1) (u_8 + 1)}
      (Matrix.mulVec.{u_1, u_8, u_7} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D) zD) 0)
  (hlD :
    Eq.{max (u_1 + 1) (u_7 + 1)}
      (Matrix.vecMul.{u_1, u_8, u_7} lD (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d1.{u_1, u_6, u_7, u_8, u_9} D)) 0)
  (bD : ι0' → K) (rC : ι3 → K)
  (hclass :
    Eq.{max (u_1 + 1) (u_7 + 1)}
      (Matrix.mulVec.{u_1, u_7, u_3}
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f1.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} F) zC)
      (HAdd.hAdd.{max u_1 u_7, max u_1 u_7, max u_1 u_7} zD
        (Matrix.mulVec.{u_1, u_7, u_6} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{u_1, u_6, u_7, u_8, u_9} D) bD)))
  (hfun :
    Eq.{max (u_1 + 1) (u_4 + 1)}
      (Matrix.vecMul.{u_1, u_8, u_4} lD
        (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.f2.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} F))
      (HAdd.hAdd.{max u_1 u_4, max u_1 u_4, max u_1 u_4} lC
        (Matrix.vecMul.{u_1, u_5, u_4} rC (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{u_1, u_2, u_3, u_4, u_5} C))))
  (σC :
    Equiv.{max (u_4 + 1) (u_2 + 1), max (u_5 + 1) (u_3 + 1)} (Sum.{u_2, u_4} (Sum.{u_2, 0} ι0 Unit) ι2)
      (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit)))
  (σD :
    Equiv.{max (u_8 + 1) (u_6 + 1), max (u_9 + 1) (u_7 + 1)} (Sum.{u_6, u_8} (Sum.{u_6, 0} ι0' Unit) ι2')
      (Sum.{u_7, u_9} ι1' (Sum.{u_9, 0} ι3' Unit))),
  Eq.{u_1 + 1}
      (ZInQ.Contrib.CloudB3RC53.Torsion.torsion.{u_1, max (max u_6 u_8) u_3 u_5, max (max u_7 u_9) u_2 u_4}
        (ZInQ.Contrib.CloudB3RC53.Torsion.BasedCx.cone.{u_1, max u_2 u_4, max u_3 u_5, max u_6 u_8, max u_7 u_9}
          (ZInQ.Contrib.CloudB3RC53.Torsion.FourMap.augMap.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9} F zC
            (HAdd.hAdd.{max u_1 u_4, max u_1 u_4, max u_1 u_4} lC
              (Matrix.vecMul.{u_1, u_5, u_4} rC
                (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d2.{u_1, u_2, u_3, u_4, u_5} C)))
            hzC ⋯
            (HAdd.hAdd.{max u_1 u_7, max u_1 u_7, max u_1 u_7} zD
              (Matrix.mulVec.{u_1, u_7, u_6} (ZInQ.Contrib.CloudB3RC53.Torsion.FourCx.d0.{u_1, u_6, u_7, u_8, u_9} D)
                bD))
            lD ⋯ hlD hclass hfun))
        (Equiv.sumCongr.{max u_7 u_9, max u_3 u_5, max u_2 u_4, max u_6 u_8} σD
          (Equiv.symm.{max (u_2 + 1) (u_4 + 1), max (u_3 + 1) (u_5 + 1)} σC)))
      (HPow.hPow.{u_1, 0, u_1} (-1) (Fintype.card.{max u_5 u_3} (Sum.{u_3, u_5} ι1 (Sum.{u_5, 0} ι3 Unit)))) →
    Eq.{u_1 + 1} (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_2, u_3, u_4, u_5} C zC lC hzC hlC σC)
      (ZInQ.Contrib.CloudB3RC53.Torsion.kmCoord.{u_1, u_6, u_7, u_8, u_9} D zD lD hzD hlD σD)
'ZInQ.Contrib.RC53Assist.CoordProvenance.kmCoord_retained_cohomology_comparison' depends on axioms: [propext,
 Classical.choice.{u},
 Quot.sound.{u}]

Compiler exit code: 0
```
