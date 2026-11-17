import ZInQKernel.Contrib.CloudR2Poincare.L1.Source20261116.ResidueFieldModels
import Mathlib.Algebra.Homology.Additive

/-!
# Actual paired-model/native-face transport

The target comparison is the additive functor's ACTUAL biproduct comparison,
followed by θX/θY. Thus the SAME scalar biprod.lift ψX ψY is conjugate to the
existing native H.pullback pair. Injectivity and finrank consequences are
proved as an iff/equality, not supplied as rank/injection/model premises.
L6's already proved native product-face facts discharge their native sides;
L2 owns the resulting cone-rank and positive-fibre argument.
-/

noncomputable section

universe u
open CategoryTheory Limits AlgebraicGeometry
open ZInQ.Contrib.CloudR2Poincare.L1.RetainedFaceFibreConstruction

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Actual scalar extension FOLLOWED by homology. This is not an assertion
that possibly nonflat extension commutes with homology. -/
abbrev scalarHomologyFunctor {S κ : Type u} [CommRing S] [Field κ]
    (β : S →+* κ) (n : ℤ) :
    CochainComplex (ModuleCat.{u} S) ℤ ⥤ ModuleCat.{u} κ :=
  scalarComplexFunctor β ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} κ) (.up ℤ) n

/-- The canonical biproduct homology comparison: forward projections and
inverse inclusions of the SAME extended/homology functor. No rank selection. -/
def scalarBiprodHomologyPairEquiv {S κ : Type u} [CommRing S] [Field κ]
    (β : S →+* κ) (PX PY : CochainComplex (ModuleCat.{u} S) ℤ) (n : ℤ) :
    ((scalarComplexFunctor β).obj (PX ⊞ PY)).homology n ≃ₗ[κ]
      (((scalarComplexFunctor β).obj PX).homology n ×
        ((scalarComplexFunctor β).obj PY).homology n) := by
  let F := scalarHomologyFunctor β n
  refine {
    toFun := fun z ↦ (F.map biprod.fst z, F.map biprod.snd z)
    invFun := fun z ↦ F.map biprod.inl z.1 + F.map biprod.inr z.2
    map_add' := fun x y ↦ Prod.ext (map_add _ _ _) (map_add _ _ _)
    map_smul' := fun a z ↦ Prod.ext ((F.map biprod.fst).hom.map_smul a z)
      ((F.map biprod.snd).hom.map_smul a z)
    left_inv := ?_
    right_inv := ?_ }
  · intro z
    have ht : F.map (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) = 𝟙 (F.obj (PX ⊞ PY)) := by
      rw [biprod.total, F.map_id]
    have hz := ConcreteCategory.congr_hom ht z
    rw [F.map_add, F.map_comp, F.map_comp] at hz
    change F.map biprod.inl (F.map biprod.fst z) + F.map biprod.inr (F.map biprod.snd z) = z at hz
    exact hz
  · intro z
    apply Prod.ext
    · change F.map biprod.fst (F.map biprod.inl z.1 + F.map biprod.inr z.2) = z.1
      rw [map_add]
      have hL : F.map biprod.fst (F.map biprod.inl z.1) = z.1 := by
        rw [← ConcreteCategory.comp_apply, ← F.map_comp, biprod.inl_fst, F.map_id]
        rfl
      have hR : F.map biprod.fst (F.map biprod.inr z.2) = 0 := by
        rw [← ConcreteCategory.comp_apply, ← F.map_comp, biprod.inr_fst, F.map_zero]
        rfl
      rw [hL, hR, add_zero]
    · change F.map biprod.snd (F.map biprod.inl z.1 + F.map biprod.inr z.2) = z.2
      rw [map_add]
      have hL : F.map biprod.snd (F.map biprod.inl z.1) = 0 := by
        rw [← ConcreteCategory.comp_apply, ← F.map_comp, biprod.inl_snd, F.map_zero]
        rfl
      have hR : F.map biprod.snd (F.map biprod.inr z.2) = z.2 := by
        rw [← ConcreteCategory.comp_apply, ← F.map_comp, biprod.inr_snd, F.map_id]
        rfl
      rw [hL, hR, zero_add]

/-- Forward components are literally the two extended/homology projections. -/
theorem scalarBiprodHomologyPairEquiv_lift {S κ : Type u} [CommRing S] [Field κ]
    (β : S →+* κ) {P PX PY : CochainComplex (ModuleCat.{u} S) ℤ}
    (ψX : P ⟶ PX) (ψY : P ⟶ PY) (n : ℤ)
    (z : ((scalarComplexFunctor β).obj P).homology n) :
    scalarBiprodHomologyPairEquiv β PX PY n
        (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map (biprod.lift ψX ψY)) n z) =
      (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map ψX) n z,
        HomologicalComplex.homologyMap ((scalarComplexFunctor β).map ψY) n z) := by
  let F := scalarHomologyFunctor β n
  apply Prod.ext
  · change F.map biprod.fst (F.map (biprod.lift ψX ψY) z) = F.map ψX z
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, biprod.lift_fst]
  · change F.map biprod.snd (F.map (biprod.lift ψX ψY) z) = F.map ψY z
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, biprod.lift_snd]

/-- Elementary exact-map conjugation. The application below uses only the
constructed θ comparisons, not an arbitrary isomorphism chosen from ranks. -/
theorem injective_iff_of_commuting_equivalences
    {A B C D : Type*} (eS : A ≃ B) (eT : C ≃ D) (f : A → C) (g : B → D)
    (square : ∀ a, eT (f a) = g (eS a)) : Function.Injective f ↔ Function.Injective g := by
  constructor
  · intro hf b b' hb
    have hz : f (eS.symm b) = f (eS.symm b') := by
      apply eT.injective
      rw [square, square, eS.apply_symm_apply, eS.apply_symm_apply]
      exact hb
    exact eS.symm.injective (hf hz)
  · intro hg a a' ha
    apply eS.injective
    apply hg
    rw [← square, ← square, ha]

namespace RetainedNativeCechFaceModels

variable {R : Type u} [CommRing R] {X Y Z : Scheme.{u}}
  {q : X ⟶ Spec (.of R)} {jX : Y ⟶ X} {jY : Z ⟶ X} {M : X.Modules}
  {ι : Type u} [Fintype ι] {U : ι → X.Opens} {d : Γ(Spec (.of R), ⊤)}

/-- κ-linear target comparison attached to the SAME paired model PX⊞PY. -/
def targetFieldPairH [IsProper q] [M.IsInvertible]
    [IsAffineHom jX] [IsProper (jX ≫ q)] [IsAffineHom jY] [IsProper (jY ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    {XB YB ZB : Scheme.{u}} (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X)
    (bX : YB ⟶ Y) (jXB : YB ⟶ XB) (bY : ZB ⟶ Z) (jYB : ZB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HX : IsPullback bX (jXB ≫ qB) (jX ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HY : IsPullback bY (jYB ≫ qB) (jY ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (squareX : jXB ≫ a = bX ≫ jX) (squareY : jYB ≫ a = bY ≫ jY)
    (n : ℕ) (hn : n ≤ 1) :
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    letI : YB.Over (Spec (.of κ)) := ⟨jXB ≫ qB⟩
    letI : ZB.Over (Spec (.of κ)) := ⟨jYB ≫ qB⟩
    ((scalarComplexFunctor β).obj (m.PX ⊞ m.PY)).homology n ≃ₗ[κ]
      (((Scheme.Modules.pullback jXB).obj ((Scheme.Modules.pullback a).obj M)).H n ×
        ((Scheme.Modules.pullback jYB).obj ((Scheme.Modules.pullback a).obj M)).H n) := by
  letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
  letI : YB.Over (Spec (.of κ)) := ⟨jXB ≫ qB⟩
  letI : ZB.Over (Spec (.of κ)) := ⟨jYB ≫ qB⟩
  exact (scalarBiprodHomologyPairEquiv β m.PX m.PY (n : ℤ)).trans
    (LinearEquiv.prodCongr (m.faceXFieldH affineU coverU κ β qB a bX jXB HC HX squareX n hn)
      (m.faceYFieldH affineU coverU κ β qB a bY jYB HC HY squareY n hn))

/-- Paired square identifies the actual scalar biprod.lift ψX ψY with the
EXISTING native H.pullback pair. -/
theorem targetFieldPairH_square [IsProper q] [M.IsInvertible]
    [IsAffineHom jX] [IsProper (jX ≫ q)] [IsAffineHom jY] [IsProper (jY ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    {XB YB ZB : Scheme.{u}} (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X)
    (bX : YB ⟶ Y) (jXB : YB ⟶ XB) (bY : ZB ⟶ Z) (jYB : ZB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HX : IsPullback bX (jXB ≫ qB) (jX ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HY : IsPullback bY (jYB ≫ qB) (jY ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (squareX : jXB ≫ a = bX ≫ jX) (squareY : jYB ≫ a = bY ≫ jY)
    (n : ℕ) (hn : n ≤ 1) (z : ((scalarComplexFunctor β).obj m.P).homology n) :
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    letI : YB.Over (Spec (.of κ)) := ⟨jXB ≫ qB⟩
    letI : ZB.Over (Spec (.of κ)) := ⟨jYB ≫ qB⟩
    m.targetFieldPairH affineU coverU κ β qB a bX jXB bY jYB HC HX HY squareX squareY n hn
        (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map (biprod.lift m.ψX m.ψY)) (n : ℤ) z) =
      (Scheme.Modules.H.pullback jXB ((Scheme.Modules.pullback a).obj M) n
          (m.sourceFieldH affineU coverU κ β qB a HC n z),
        Scheme.Modules.H.pullback jYB ((Scheme.Modules.pullback a).obj M) n
          (m.sourceFieldH affineU coverU κ β qB a HC n z)) := by
  letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
  letI : YB.Over (Spec (.of κ)) := ⟨jXB ≫ qB⟩
  letI : ZB.Over (Spec (.of κ)) := ⟨jYB ≫ qB⟩
  change LinearEquiv.prodCongr
      (m.faceXFieldH affineU coverU κ β qB a bX jXB HC HX squareX n hn)
      (m.faceYFieldH affineU coverU κ β qB a bY jYB HC HY squareY n hn)
      (scalarBiprodHomologyPairEquiv β m.PX m.PY (n : ℤ)
        (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map (biprod.lift m.ψX m.ψY)) (n : ℤ) z)) = _
  rw [scalarBiprodHomologyPairEquiv_lift]
  apply Prod.ext
  · exact m.faceXFieldH_square affineU coverU κ β qB a bX jXB HC HX squareX n hn z
  · exact m.faceYFieldH_square affineU coverU κ β qB a bY jYB HC HY squareY n hn z

/-- Actual model injection iff actual native field-face injection. No injection
is assumed here; native product-face facts supply the right side downstream. -/
theorem homology_modelPair_injective_iff_nativeFacePair [IsProper q] [M.IsInvertible]
    [IsAffineHom jX] [IsProper (jX ≫ q)] [IsAffineHom jY] [IsProper (jY ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    {XB YB ZB : Scheme.{u}} (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X)
    (bX : YB ⟶ Y) (jXB : YB ⟶ XB) (bY : ZB ⟶ Z) (jYB : ZB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HX : IsPullback bX (jXB ≫ qB) (jX ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HY : IsPullback bY (jYB ≫ qB) (jY ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (squareX : jXB ≫ a = bX ≫ jX) (squareY : jYB ≫ a = bY ≫ jY)
    (n : ℕ) (hn : n ≤ 1) :
    Function.Injective (HomologicalComplex.homologyMap
      ((scalarComplexFunctor β).map (biprod.lift m.ψX m.ψY)) (n : ℤ)) ↔
    Function.Injective (fun z : ((Scheme.Modules.pullback a).obj M).H n ↦
      (Scheme.Modules.H.pullback jXB ((Scheme.Modules.pullback a).obj M) n z,
        Scheme.Modules.H.pullback jYB ((Scheme.Modules.pullback a).obj M) n z)) := by
  letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
  letI : YB.Over (Spec (.of κ)) := ⟨jXB ≫ qB⟩
  letI : ZB.Over (Spec (.of κ)) := ⟨jYB ≫ qB⟩
  exact injective_iff_of_commuting_equivalences
    (m.sourceFieldH affineU coverU κ β qB a HC n).toEquiv
    (m.targetFieldPairH affineU coverU κ β qB a bX jXB bY jYB HC HX HY squareX squareY n hn).toEquiv
    (HomologicalComplex.homologyMap ((scalarComplexFunctor β).map (biprod.lift m.ψX m.ψY)) (n : ℤ))
    (fun z ↦ (Scheme.Modules.H.pullback jXB ((Scheme.Modules.pullback a).obj M) n z,
      Scheme.Modules.H.pullback jYB ((Scheme.Modules.pullback a).obj M) n z))
    (m.targetFieldPairH_square affineU coverU κ β qB a bX jXB bY jYB HC HX HY squareX squareY n hn)

/-- Paired model H0 finrank equals the ACTUAL native paired face H0 finrank.
The downstream value2 is derived from entire-face trivializations, not assumed. -/
theorem finrank_modelTargetPair_eq_nativeFaces [IsProper q] [M.IsInvertible]
    [IsAffineHom jX] [IsProper (jX ≫ q)] [IsAffineHom jY] [IsProper (jY ≫ q)]
    (m : RetainedNativeCechFaceModels R q jX jY M U d)
    (affineU : ∀ i, IsAffineOpen (U i)) (coverU : ⨆ i, U i = ⊤)
    (κ : Type u) [Field κ] (β : Localization.Away d →+* κ)
    {XB YB ZB : Scheme.{u}} (qB : XB ⟶ Spec (.of κ)) (a : XB ⟶ X)
    (bX : YB ⟶ Y) (jXB : YB ⟶ XB) (bY : ZB ⟶ Z) (jYB : ZB ⟶ XB)
    (HC : IsPullback a qB q (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HX : IsPullback bX (jXB ≫ qB) (jX ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (HY : IsPullback bY (jYB ≫ qB) (jY ≫ q) (retainedFieldBasePoint R (Localization.Away d) κ β))
    (squareX : jXB ≫ a = bX ≫ jX) (squareY : jYB ≫ a = bY ≫ jY) :
    letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
    letI : YB.Over (Spec (.of κ)) := ⟨jXB ≫ qB⟩
    letI : ZB.Over (Spec (.of κ)) := ⟨jYB ≫ qB⟩
    Module.finrank κ (((scalarComplexFunctor β).obj (m.PX ⊞ m.PY)).homology 0) =
      Module.finrank κ (((Scheme.Modules.pullback jXB).obj ((Scheme.Modules.pullback a).obj M)).H 0 ×
        ((Scheme.Modules.pullback jYB).obj ((Scheme.Modules.pullback a).obj M)).H 0) := by
  letI : XB.Over (Spec (.of κ)) := ⟨qB⟩
  letI : YB.Over (Spec (.of κ)) := ⟨jXB ≫ qB⟩
  letI : ZB.Over (Spec (.of κ)) := ⟨jYB ≫ qB⟩
  exact (m.targetFieldPairH affineU coverU κ β qB a bX jXB bY jYB HC HX HY squareX squareY 0 (by omega)).finrank_eq

end RetainedNativeCechFaceModels

end ZInQ.Contrib.CloudR2Poincare.L1
