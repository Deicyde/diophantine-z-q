import ZInQKernel.Contrib.CloudR2Poincare.L1.Source20261116.ConsumerStatements

/-!
# Literal residue-functor spelling of the retained field comparisons

The raw scalar is L2.nativeResidueScalarMap with the ORIGINAL residue-field
object and Field dictionary. The original residue morphism and actual chart
map determine the geometric fibre. No new field identification or flatness
hypothesis is introduced. Cone/fibre dimension transport remains L2-owned.
-/

noncomputable section

universe u
open CategoryTheory Limits AlgebraicGeometry
open ZInQ.Contrib.CloudR2Poincare.L1.RetainedFaceFibreConstruction

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Actual base chart of the raw localized model. The inverse is the native
Spec-of-global-sections comparison of the original affine base. -/
def retainedModelBaseChart
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S] :
    Spec (.of S) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(Spec (.of R), ⊤) S)) ≫
    (Spec (.of R)).isoSpec.inv

/-- Every raw field point factors through that SAME model chart. -/
theorem retainedFieldBasePoint_factorization
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    (κ : Type u) [Field κ] (β : S →+* κ) :
    retainedFieldBasePoint R S κ β =
      Spec.map (CommRingCat.ofHom β) ≫ retainedModelBaseChart R S := by
  unfold retainedFieldBasePoint retainedModelBaseChart fieldPointFromGlobalSections
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- The field point in the model comparison is the ORIGINAL actual residue
morphism composed with the SAME chart. L2's native ring arrow is reused. -/
theorem retainedFieldBasePoint_residue
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    (s : Spec (.of S)) :
    retainedFieldBasePoint R S ((Spec (.of S)).residueField s) (L2.nativeResidueScalarMap S s) =
      (Spec (.of S)).fromSpecResidueField s ≫ retainedModelBaseChart R S := by
  rw [retainedFieldBasePoint_factorization]
  have hβ : CommRingCat.ofHom (L2.nativeResidueScalarMap S s) = L2.nativeResidueRingMap S s := rfl
  rw [hβ, L2.nativeResidueScalarMap_specMap]

/-- Raw scalar extension has precisely the L2 residue-functor data, not an
avatar of its homology. -/
theorem scalarComplexFunctor_nativeResidue
    (S : Type u) [CommRing S] (s : Spec (.of S)) :
    scalarComplexFunctor (L2.nativeResidueScalarMap S s) = L2.nativeResidueCochainFunctor S s := rfl

/-- The fibre of the actual chart family is a Cartesian field fibre over the
original base. The scheme and its fibreι are kept, not replaced objectwise. -/
theorem retainedChartFibre_isPullback
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of R)) (s : Spec (.of S)) :
    let chart := retainedModelBaseChart R S
    let qS := pullback.snd q chart
    IsPullback (qS.fiberι s ≫ pullback.fst q chart) (qS.fiberToSpecResidueField s) q
      (retainedFieldBasePoint R S ((Spec (.of S)).residueField s) (L2.nativeResidueScalarMap S s)) := by
  let chart := retainedModelBaseChart R S
  let qS := pullback.snd q chart
  have hf : IsPullback (qS.fiberι s) (qS.fiberToSpecResidueField s) qS
      ((Spec (.of S)).fromSpecResidueField s) := IsPullback.of_hasPullback qS _
  have hc : IsPullback (pullback.fst q chart) qS q chart := IsPullback.of_hasPullback q chart
  rw [retainedFieldBasePoint_residue]
  exact hf.paste_horiz hc

/-- Actual coefficient comparison to the fibre of the chart family. Its
orientation is composite pullback → iterated physical fibre pullback. -/
def retainedChartFibreCoefficientIso
    (R S : Type u) [CommRing R] [CommRing S] [Algebra Γ(Spec (.of R), ⊤) S]
    {X : Scheme.{u}} (q : X ⟶ Spec (.of R)) (M : X.Modules) (s : Spec (.of S)) :
    let chart := retainedModelBaseChart R S
    let qS := pullback.snd q chart
    (Scheme.Modules.pullback (qS.fiberι s ≫ pullback.fst q chart)).obj M ≅
      (Scheme.Modules.pullback (qS.fiberι s)).obj
        ((Scheme.Modules.pullback (pullback.fst q chart)).obj M) :=
  ((Scheme.Modules.pullbackComp ((pullback.snd q (retainedModelBaseChart R S)).fiberι s)
    (pullback.fst q (retainedModelBaseChart R S))).app M).symm

/-- The existing native face H map commutes with the ACTUAL coefficient-iso
transport (for instance retainedChartFibreCoefficientIso). No H map is replaced. -/
theorem nativeFaceH_coefficientIso_square
    {Q F : Scheme.{u}} (j : F ⟶ Q) {M N : Q.Modules} (e : M ≅ N) (n : ℕ) (z : M.H n) :
    Scheme.Modules.H.map ((Scheme.Modules.pullback j).map e.hom) n
        (Scheme.Modules.H.pullback j M n z) =
      Scheme.Modules.H.pullback j N n (Scheme.Modules.H.map e.hom n z) :=
  (Scheme.Modules.H.pullback_naturality j e.hom n z).symm

namespace RetainedNativeCechFaceModels

variable {R : Type u} [CommRing R] {X Y Z : Scheme.{u}}
  {q : X ⟶ Spec (.of R)} {jX : Y ⟶ X} {jY : Z ⟶ X} {M : X.Modules}
  {ι : Type u} [Fintype ι] {U : ι → X.Opens} {d : Γ(Spec (.of R), ⊤)}

/-- The original κ(s)-linear source iso, spelled with the ACTUAL L2 residue
functor and actual chart/residue morphism. -/
def sourceResidueH [IsProper q] [M.IsInvertible]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (s : Spec (.of (Localization.Away d)))
    {XB : Scheme.{u}} (qB : XB ⟶ Spec ((Spec (.of (Localization.Away d))).residueField s))
    (a : XB ⟶ X)
    (HC : IsPullback a qB q
      ((Spec (.of (Localization.Away d))).fromSpecResidueField s ≫
        retainedModelBaseChart R (Localization.Away d))) (n : ℕ) :
    letI : XB.Over (Spec ((Spec (.of (Localization.Away d))).residueField s)) := ⟨qB⟩
    ((L2.nativeResidueCochainFunctor (Localization.Away d) s).obj m.P).homology n ≃ₗ[
      (Spec (.of (Localization.Away d))).residueField s] ((Scheme.Modules.pullback a).obj M).H n := by
  have hc : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d)
      ((Spec (.of (Localization.Away d))).residueField s)
      (L2.nativeResidueScalarMap (Localization.Away d) s)) := by
    rw [retainedFieldBasePoint_residue]
    exact HC
  exact m.sourceFieldH affineU coverU ((Spec (.of (Localization.Away d))).residueField s)
    (L2.nativeResidueScalarMap (Localization.Away d) s) qB a hc n

/-- The original κ(s)-linear X-target iso, retaining original scalar ψX. -/
def faceXResidueH [IsProper q] [M.IsInvertible] [IsAffineHom jX] [IsProper (jX ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (s : Spec (.of (Localization.Away d)))
    {XB YB : Scheme.{u}} (qB : XB ⟶ Spec ((Spec (.of (Localization.Away d))).residueField s))
    (a : XB ⟶ X) (bX : YB ⟶ Y) (jXB : YB ⟶ XB)
    (HC : IsPullback a qB q ((Spec (.of (Localization.Away d))).fromSpecResidueField s ≫
      retainedModelBaseChart R (Localization.Away d)))
    (HX : IsPullback bX (jXB ≫ qB) (jX ≫ q) ((Spec (.of (Localization.Away d))).fromSpecResidueField s ≫
      retainedModelBaseChart R (Localization.Away d)))
    (squareX : jXB ≫ a = bX ≫ jX) (n : ℕ) (hn : n ≤ 1) :
    letI : XB.Over (Spec ((Spec (.of (Localization.Away d))).residueField s)) := ⟨qB⟩
    letI : YB.Over (Spec ((Spec (.of (Localization.Away d))).residueField s)) := ⟨jXB ≫ qB⟩
    ((L2.nativeResidueCochainFunctor (Localization.Away d) s).obj m.PX).homology n ≃ₗ[
      (Spec (.of (Localization.Away d))).residueField s]
      ((Scheme.Modules.pullback jXB).obj ((Scheme.Modules.pullback a).obj M)).H n := by
  have hc : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d)
      ((Spec (.of (Localization.Away d))).residueField s) (L2.nativeResidueScalarMap (Localization.Away d) s)) := by
    rw [retainedFieldBasePoint_residue]; exact HC
  have hx : IsPullback bX (jXB ≫ qB) (jX ≫ q) (retainedFieldBasePoint R (Localization.Away d)
      ((Spec (.of (Localization.Away d))).residueField s) (L2.nativeResidueScalarMap (Localization.Away d) s)) := by
    rw [retainedFieldBasePoint_residue]; exact HX
  exact m.faceXFieldH affineU coverU ((Spec (.of (Localization.Away d))).residueField s)
    (L2.nativeResidueScalarMap (Localization.Away d) s) qB a bX jXB hc hx squareX n hn

/-- The original κ(s)-linear Y-target iso, retaining original scalar ψY. -/
def faceYResidueH [IsProper q] [M.IsInvertible] [IsAffineHom jY] [IsProper (jY ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (s : Spec (.of (Localization.Away d)))
    {XB ZB : Scheme.{u}} (qB : XB ⟶ Spec ((Spec (.of (Localization.Away d))).residueField s))
    (a : XB ⟶ X) (bY : ZB ⟶ Z) (jYB : ZB ⟶ XB)
    (HC : IsPullback a qB q ((Spec (.of (Localization.Away d))).fromSpecResidueField s ≫
      retainedModelBaseChart R (Localization.Away d)))
    (HY : IsPullback bY (jYB ≫ qB) (jY ≫ q) ((Spec (.of (Localization.Away d))).fromSpecResidueField s ≫
      retainedModelBaseChart R (Localization.Away d)))
    (squareY : jYB ≫ a = bY ≫ jY) (n : ℕ) (hn : n ≤ 1) :
    letI : XB.Over (Spec ((Spec (.of (Localization.Away d))).residueField s)) := ⟨qB⟩
    letI : ZB.Over (Spec ((Spec (.of (Localization.Away d))).residueField s)) := ⟨jYB ≫ qB⟩
    ((L2.nativeResidueCochainFunctor (Localization.Away d) s).obj m.PY).homology n ≃ₗ[
      (Spec (.of (Localization.Away d))).residueField s]
      ((Scheme.Modules.pullback jYB).obj ((Scheme.Modules.pullback a).obj M)).H n := by
  have hc : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d)
      ((Spec (.of (Localization.Away d))).residueField s) (L2.nativeResidueScalarMap (Localization.Away d) s)) := by
    rw [retainedFieldBasePoint_residue]; exact HC
  have hy : IsPullback bY (jYB ≫ qB) (jY ≫ q) (retainedFieldBasePoint R (Localization.Away d)
      ((Spec (.of (Localization.Away d))).residueField s) (L2.nativeResidueScalarMap (Localization.Away d) s)) := by
    rw [retainedFieldBasePoint_residue]; exact HY
  exact m.faceYFieldH affineU coverU ((Spec (.of (Localization.Away d))).residueField s)
    (L2.nativeResidueScalarMap (Localization.Away d) s) qB a bY jYB hc hy squareY n hn

/-- Literal κ(s)-linear squares for the SAME raw residue maps ψX/ψY.
These are the concrete equations consumed by the cube cone argument. -/
theorem residueFieldH_squares [IsProper q] [M.IsInvertible]
    [IsAffineHom jX] [IsProper (jX ≫ q)] [IsAffineHom jY] [IsProper (jY ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (s : Spec (.of (Localization.Away d)))
    {XB YB ZB : Scheme.{u}} (qB : XB ⟶ Spec ((Spec (.of (Localization.Away d))).residueField s))
    (a : XB ⟶ X) (bX : YB ⟶ Y) (jXB : YB ⟶ XB) (bY : ZB ⟶ Z) (jYB : ZB ⟶ XB)
    (HC : IsPullback a qB q ((Spec (.of (Localization.Away d))).fromSpecResidueField s ≫
      retainedModelBaseChart R (Localization.Away d)))
    (HX : IsPullback bX (jXB ≫ qB) (jX ≫ q) ((Spec (.of (Localization.Away d))).fromSpecResidueField s ≫
      retainedModelBaseChart R (Localization.Away d)))
    (HY : IsPullback bY (jYB ≫ qB) (jY ≫ q) ((Spec (.of (Localization.Away d))).fromSpecResidueField s ≫
      retainedModelBaseChart R (Localization.Away d)))
    (squareX : jXB ≫ a = bX ≫ jX) (squareY : jYB ≫ a = bY ≫ jY)
    (n : ℕ) (hn : n ≤ 1)
    (z : ((L2.nativeResidueCochainFunctor (Localization.Away d) s).obj m.P).homology n) :
    letI : XB.Over (Spec ((Spec (.of (Localization.Away d))).residueField s)) := ⟨qB⟩
    letI : YB.Over (Spec ((Spec (.of (Localization.Away d))).residueField s)) := ⟨jXB ≫ qB⟩
    letI : ZB.Over (Spec ((Spec (.of (Localization.Away d))).residueField s)) := ⟨jYB ≫ qB⟩
    m.faceXResidueH affineU coverU s qB a bX jXB HC HX squareX n hn
        (HomologicalComplex.homologyMap ((L2.nativeResidueCochainFunctor (Localization.Away d) s).map m.ψX) (n : ℤ) z) =
      Scheme.Modules.H.pullback jXB ((Scheme.Modules.pullback a).obj M) n
        (m.sourceResidueH affineU coverU s qB a HC n z) ∧
    m.faceYResidueH affineU coverU s qB a bY jYB HC HY squareY n hn
        (HomologicalComplex.homologyMap ((L2.nativeResidueCochainFunctor (Localization.Away d) s).map m.ψY) (n : ℤ) z) =
      Scheme.Modules.H.pullback jYB ((Scheme.Modules.pullback a).obj M) n
        (m.sourceResidueH affineU coverU s qB a HC n z) := by
  let κ := (Spec (.of (Localization.Away d))).residueField s
  let β := L2.nativeResidueScalarMap (Localization.Away d) s
  have hc : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d) κ β) := by
    rw [retainedFieldBasePoint_residue]; exact HC
  have hx : IsPullback bX (jXB ≫ qB) (jX ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β) := by
    rw [retainedFieldBasePoint_residue]; exact HX
  have hy : IsPullback bY (jYB ≫ qB) (jY ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β) := by
    rw [retainedFieldBasePoint_residue]; exact HY
  exact ⟨m.faceXFieldH_square affineU coverU κ β qB a bX jXB hc hx squareX n hn z,
    m.faceYFieldH_square affineU coverU κ β qB a bY jYB hc hy squareY n hn z⟩

end RetainedNativeCechFaceModels

end ZInQ.Contrib.CloudR2Poincare.L1
