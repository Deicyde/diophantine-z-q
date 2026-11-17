import ZInQKernel.Contrib.CloudR2Poincare.L1.Source20261116.CechModelH01

/-!
# Produced original Čech models with native field-face squares

This is the closed geometry constructor. No arbitrary model, H1 injection,
rank, or residue-flatness premise is added. It calls the existing original
Čech/good-truncation model construction and retains its SAME maps/homotopies.
Field H0/H1 comparisons are computed from those witnesses, not selected from
ranks. The original Čech complexes are not asserted termwise bounded.

Current status: SOURCE ONLY. Native elaboration, default-budget kernel,
BinderInfo/raw-data comparison and AX3 evidence are unproduced on this host.
-/

noncomputable section

universe u
open CategoryTheory Limits AlgebraicGeometry
open ZInQ.Contrib.CloudR2Poincare.L1.RetainedFaceFibreConstruction

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Exact retained model data, attached to the original C/DX/DY and native
face maps. Bounds apply ONLY to P/PX/PY, not the original Čech terms. -/
structure RetainedNativeCechFaceModels
    (R : Type u) [CommRing R] {X Y Z : Scheme.{u}}
    (q : X ⟶ Spec (.of R)) (jX : Y ⟶ X) (jY : Z ⟶ X)
    (M : X.Modules) {ι : Type u} [Fintype ι] (U : ι → X.Opens)
    (d : Γ(Spec (.of R), ⊤)) where
  P : CochainComplex (ModuleCat.{u} (Localization.Away d)) ℤ
  PX : CochainComplex (ModuleCat.{u} (Localization.Away d)) ℤ
  PY : CochainComplex (ModuleCat.{u} (Localization.Away d)) ℤ
  nonnegativeP : P.IsStrictlyGE 0
  upperP : P.IsStrictlyLE ((Fintype.card ι : ℤ) - 1)
  nonnegativePX : PX.IsStrictlyGE 0
  upperPX : PX.IsStrictlyLE ((Fintype.card ι : ℤ) - 1)
  nonnegativePY : PY.IsStrictlyGE 0
  upperPY : PY.IsStrictlyLE ((Fintype.card ι : ℤ) - 1)
  freeFiniteP : ∀ n, Module.Free (Localization.Away d) (P.X n) ∧ Module.Finite (Localization.Away d) (P.X n)
  freeFinitePX : ∀ n, Module.Free (Localization.Away d) (PX.X n) ∧ Module.Finite (Localization.Away d) (PX.X n)
  freeFinitePY : ∀ n, Module.Free (Localization.Away d) (PY.X n) ∧ Module.Finite (Localization.Away d) (PY.X n)
  eC : P ⟶ (scalarComplexFunctor (algebraMap Γ(Spec (.of R), ⊤) (Localization.Away d))).obj
    (Scheme.Modules.cechModuleComplex q M U)
  eX : PX ⟶ (scalarComplexFunctor (algebraMap Γ(Spec (.of R), ⊤) (Localization.Away d))).obj
    (Scheme.Modules.cechModuleComplex (jX ≫ q) ((Scheme.Modules.pullback jX).obj M)
      (fun i ↦ jX ⁻¹ᵁ U i))
  eY : PY ⟶ (scalarComplexFunctor (algebraMap Γ(Spec (.of R), ⊤) (Localization.Away d))).obj
    (Scheme.Modules.cechModuleComplex (jY ≫ q) ((Scheme.Modules.pullback jY).obj M)
      (fun i ↦ jY ⁻¹ᵁ U i))
  quasiIsoC : QuasiIso eC
  quasiIsoX : QuasiIso eX
  quasiIsoY : QuasiIso eY
  universal : ∀ (B : Type u) [CommRing B] [Algebra (Localization.Away d) B],
    QuasiIso ((scalarComplexFunctor (algebraMap (Localization.Away d) B)).map eC) ∧
    QuasiIso ((scalarComplexFunctor (algebraMap (Localization.Away d) B)).map eX) ∧
    QuasiIso ((scalarComplexFunctor (algebraMap (Localization.Away d) B)).map eY)
  ψX : P ⟶ PX
  ψY : P ⟶ PY
  homotopyX : Homotopy (ψX ≫ eX)
    (eC ≫ (scalarComplexFunctor (algebraMap Γ(Spec (.of R), ⊤) (Localization.Away d))).map
      (cechModuleFaceMap q jX M U))
  homotopyY : Homotopy (ψY ≫ eY)
    (eC ≫ (scalarComplexFunctor (algebraMap Γ(Spec (.of R), ⊤) (Localization.Away d))).map
      (cechModuleFaceMap q jY M U))

namespace RetainedNativeCechFaceModels

variable {R : Type u} [CommRing R] {X Y Z : Scheme.{u}}
  {q : X ⟶ Spec (.of R)} {jX : Y ⟶ X} {jY : Z ⟶ X} {M : X.Modules}
  {ι : Type u} [Fintype ι] {U : ι → X.Opens} {d : Γ(Spec (.of R), ⊤)}

/-- All-algebra comparison for the SAME eC. -/
theorem universalC (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (B : Type u) [CommRing B] [Algebra (Localization.Away d) B] :
    QuasiIso ((scalarComplexFunctor (algebraMap (Localization.Away d) B)).map m.eC) :=
  (m.universal B).1

/-- All-algebra comparison for the SAME eX. -/
theorem universalX (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (B : Type u) [CommRing B] [Algebra (Localization.Away d) B] :
    QuasiIso ((scalarComplexFunctor (algebraMap (Localization.Away d) B)).map m.eX) :=
  (m.universal B).2.1

/-- All-algebra comparison for the SAME eY. -/
theorem universalY (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (B : Type u) [CommRing B] [Algebra (Localization.Away d) B] :
    QuasiIso ((scalarComplexFunctor (algebraMap (Localization.Away d) B)).map m.eY) :=
  (m.universal B).2.2

/-- κ-linear source comparison computed from the produced eC and the actual
Cartesian fibre map, valid in every nonnegative degree. -/
def sourceFieldH [IsProper q] [M.IsInvertible]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    {XB : Scheme.{u}} (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X)
    (HC : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d) κ β)) (n : ℕ) :
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    ((scalarComplexFunctor β).obj m.P).homology n ≃ₗ[κ] ((Scheme.Modules.pullback a).obj M).H n :=
  retainedCechModelHFieldLinearEquiv R (Localization.Away d) q M U affineU coverU m.P m.eC
    m.universalC κ β qB a HC n

/-- Actual degree0/1 target comparison for the SAME eX. -/
def faceXFieldH [IsProper q] [M.IsInvertible] [IsAffineHom jX] [IsProper (jX ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    {XB YB : Scheme.{u}} (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X) (bX : YB ⟶ Y) (jXB : YB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HX : IsPullback bX (jXB ≫ qB) (jX ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (squareX : jXB ≫ a = bX ≫ jX) (n : ℕ) (hn : n ≤ 1) :
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    letI : YB.Over (Spec (.of κ)) := ⟨jXB ≫ qB⟩
    ((scalarComplexFunctor β).obj m.PX).homology n ≃ₗ[κ]
      ((Scheme.Modules.pullback jXB).obj ((Scheme.Modules.pullback a).obj M)).H n :=
  retainedCechModelFaceHFieldLinearEquiv R (Localization.Away d) q jX M U affineU coverU
    m.PX m.eX m.universalX κ β qB a bX jXB HC HX squareX n hn

/-- Actual degree0/1 target comparison for the SAME eY. -/
def faceYFieldH [IsProper q] [M.IsInvertible] [IsAffineHom jY] [IsProper (jY ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    {XB ZB : Scheme.{u}} (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X) (bY : ZB ⟶ Z) (jYB : ZB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HY : IsPullback bY (jYB ≫ qB) (jY ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (squareY : jYB ≫ a = bY ≫ jY) (n : ℕ) (hn : n ≤ 1) :
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    letI : ZB.Over (Spec (.of κ)) := ⟨jYB ≫ qB⟩
    ((scalarComplexFunctor β).obj m.PY).homology n ≃ₗ[κ]
      ((Scheme.Modules.pullback jYB).obj ((Scheme.Modules.pullback a).obj M)).H n :=
  retainedCechModelFaceHFieldLinearEquiv R (Localization.Away d) q jY M U affineU coverU
    m.PY m.eY m.universalY κ β qB a bY jYB HC HY squareY n hn

/-- The SAME scalar ψX identifies with the existing H.pullback, not a
rank-selected map between the comparison objects. -/
theorem faceXFieldH_square [IsProper q] [M.IsInvertible] [IsAffineHom jX] [IsProper (jX ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    {XB YB : Scheme.{u}} (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X) (bX : YB ⟶ Y) (jXB : YB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HX : IsPullback bX (jXB ≫ qB) (jX ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (squareX : jXB ≫ a = bX ≫ jX) (n : ℕ) (hn : n ≤ 1)
    (z : ((scalarComplexFunctor β).obj m.P).homology n) :
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    letI : YB.Over (Spec (.of κ)) := ⟨jXB ≫ qB⟩
    m.faceXFieldH affineU coverU κ β qB a bX jXB HC HX squareX n hn
        (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map m.ψX) (n : ℤ) z) =
      Scheme.Modules.H.pullback jXB ((Scheme.Modules.pullback a).obj M) n
        (m.sourceFieldH affineU coverU κ β qB a HC n z) :=
  retainedCechModelFaceHFieldLinearEquiv_square R (Localization.Away d) q jX M U affineU coverU
    m.P m.PX m.ψX m.eC m.eX m.homotopyX m.universalC m.universalX
    κ β qB a bX jXB HC HX squareX n hn z

/-- The SAME scalar ψY identifies with the existing H.pullback. -/
theorem faceYFieldH_square [IsProper q] [M.IsInvertible] [IsAffineHom jY] [IsProper (jY ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    {XB ZB : Scheme.{u}} (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X) (bY : ZB ⟶ Z) (jYB : ZB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HY : IsPullback bY (jYB ≫ qB) (jY ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (squareY : jYB ≫ a = bY ≫ jY) (n : ℕ) (hn : n ≤ 1)
    (z : ((scalarComplexFunctor β).obj m.P).homology n) :
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    letI : ZB.Over (Spec (.of κ)) := ⟨jYB ≫ qB⟩
    m.faceYFieldH affineU coverU κ β qB a bY jYB HC HY squareY n hn
        (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map m.ψY) (n : ℤ) z) =
      Scheme.Modules.H.pullback jYB ((Scheme.Modules.pullback a).obj M) n
        (m.sourceFieldH affineU coverU κ β qB a HC n z) :=
  retainedCechModelFaceHFieldLinearEquiv_square R (Localization.Away d) q jY M U affineU coverU
    m.P m.PY m.ψY m.eC m.eY m.homotopyY m.universalC m.universalY
    κ β qB a bY jYB HC HY squareY n hn z

/-- Full field/model statement: every actual Cartesian field face in degrees
0/1 commutes with the SAME scalar model map and the existing native H map. -/
def NativeH01Compatible [IsProper q] [M.IsInvertible]
    [IsAffineHom jX] [IsProper (jX ≫ q)] [IsAffineHom jY] [IsProper (jY ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) : Prop :=
  ∀ (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    {XB YB ZB : Scheme.{u}} (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X)
    (bX : YB ⟶ Y) (jXB : YB ⟶ XB) (bY : ZB ⟶ Z) (jYB : ZB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HX : IsPullback bX (jXB ≫ qB) (jX ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HY : IsPullback bY (jYB ≫ qB) (jY ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (squareX : jXB ≫ a = bX ≫ jX) (squareY : jYB ≫ a = bY ≫ jY)
    (n : ℕ) (hn : n ≤ 1) (z : ((scalarComplexFunctor β).obj m.P).homology n),
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    letI : YB.Over (Spec (.of κ)) := ⟨jXB ≫ qB⟩
    letI : ZB.Over (Spec (.of κ)) := ⟨jYB ≫ qB⟩
    m.faceXFieldH affineU coverU κ β qB a bX jXB HC HX squareX n hn
        (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map m.ψX) (n : ℤ) z) =
      Scheme.Modules.H.pullback jXB ((Scheme.Modules.pullback a).obj M) n
        (m.sourceFieldH affineU coverU κ β qB a HC n z) ∧
    m.faceYFieldH affineU coverU κ β qB a bY jYB HC HY squareY n hn
        (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map m.ψY) (n : ℤ) z) =
      Scheme.Modules.H.pullback jYB ((Scheme.Modules.pullback a).obj M) n
        (m.sourceFieldH affineU coverU κ β qB a HC n z)

/-- Compatibility is proved from the retained comparisons and homotopies.
It is never supplied as a model/H1/rank premise to the geometry constructor. -/
theorem nativeH01Compatible [IsProper q] [M.IsInvertible]
    [IsAffineHom jX] [IsProper (jX ≫ q)] [IsAffineHom jY] [IsProper (jY ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤) :
    m.NativeH01Compatible affineU coverU := by
  intro κ _ β XB YB ZB qB a bX jXB bY jYB HC HX HY squareX squareY n hn z
  exact ⟨m.faceXFieldH_square affineU coverU κ β qB a bX jXB HC HX squareX n hn z,
    m.faceYFieldH_square affineU coverU κ β qB a bY jYB HC HY squareY n hn z⟩

end RetainedNativeCechFaceModels

/-- Closed combined field/model constructor. The caller supplies geometry,
not an arbitrary model, rank fact, H1 injection, or scalar-flatness witness. -/
theorem exists_retained_nativeCechFaceModels_with_nativeH01
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X Y Z : Scheme.{u}} (q : X ⟶ Spec (.of R)) (jX : Y ⟶ X) (jY : Z ⟶ X)
    [IsProper q] [Flat q] [IsProper (jX ≫ q)] [Flat (jX ≫ q)]
    [IsProper (jY ≫ q)] [Flat (jY ≫ q)] [IsAffineHom jX] [IsAffineHom jY]
    (M : X.Modules) [M.IsInvertible]
    {ι : Type u} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (p : Ideal Γ(Spec (.of R), ⊤)) [p.IsPrime] :
    ∃ d ∉ p, ∃ m : RetainedNativeCechFaceModels R q jX jY M U d,
      m.NativeH01Compatible affineU coverU := by
  obtain ⟨d, hd, P, PX, PY, loP, hiP, loPX, hiPX, loPY, hiPY,
    freeP, freePX, freePY, eC, eX, eY, qeC, qeX, qeY, universal, ψX, ψY, hX, hY⟩ :=
    exists_retained_nativeCechFace_models R q jX jY M U affineU coverU p
  let m : RetainedNativeCechFaceModels R q jX jY M U d := {
    P := P, PX := PX, PY := PY
    nonnegativeP := loP, upperP := hiP, nonnegativePX := loPX, upperPX := hiPX
    nonnegativePY := loPY, upperPY := hiPY
    freeFiniteP := freeP, freeFinitePX := freePX, freeFinitePY := freePY
    eC := eC, eX := eX, eY := eY
    quasiIsoC := qeC, quasiIsoX := qeX, quasiIsoY := qeY
    universal := universal, ψX := ψX, ψY := ψY
    homotopyX := hX.some, homotopyY := hY.some }
  exact ⟨d, hd, m, m.nativeH01Compatible affineU coverU⟩

end ZInQ.Contrib.CloudR2Poincare.L1
