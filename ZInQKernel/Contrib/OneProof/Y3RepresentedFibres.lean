import ZInQKernel.Contrib.OneProof.Y3RepresentableQ

/-!
# Field fibres of the represented level-three model

The proof refines Jack McCarthy's fibre construction in `Y3Audit.y3FineModuliAbP_of_rep`
from the project's `Y3RepresentableQ` module. Keeping the given universal
family identifies the classifying equivalence at each of its field fibres.
-/

noncomputable section

namespace Y3Audit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open ShimuraCFT RayClassCFT Y3Fix SGRSplit

/-- The point equivalence of the represented rational model keeps the
specified universal family and its exact field fibres. -/
theorem exists_fineModuliAt_of_rep (hT : ObjBridge.TorsionStructure)
    {Y : Over (Spec (CommRingCat.of ℚ))} {𝒜 : QMAbSchemeP Y.left}
    (hp : IsProper Y.hom) (hs : SmoothOfRelativeDimension 1 Y.hom)
    (hU : ∀ (S : Over (Spec (CommRingCat.of ℚ))), IsLocallyNoetherian S.left →
      ∀ 𝒜' : QMAbSchemeP S.left, ∃! g : S ⟶ Y, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily) :
    ∃ Φ : PtEquiv Y, R1fpPropsAbP Y Φ ∧
      ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
        Φ K y = M3.mk P ↔ IsFibreOf 𝒜.toQMFamily y.left P := by
  -- the fibre object at a field point
  have hfib : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      ∃ P : QML3 K, IsFibreOf 𝒜.toQMFamily y.left P := fun K _ _ y =>
    qmAbFieldFibre _ (toKer 𝒜) K y.left
  let φ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) → M3 K :=
    fun K _ _ y => M3.mk (hfib K y).choose
  -- `φ y = [P]` iff `P` is a fibre at `y`
  have hφ : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
      φ K y = M3.mk P ↔ IsFibreOf 𝒜.toQMFamily y.left P := by
    intro K _ _ y P
    constructor
    · intro h
      obtain ⟨f⟩ := Quotient.exact h
      exact isFibreOf_of_iso _ f.symm (hfib K y).choose_spec
    · intro h
      exact fibreClassUnique _ _ K y.left _ _ (hfib K y).choose_spec h
  have hbij : ∀ (K : Type) [Field K] [Algebra ℚ K], Function.Bijective (φ K) := by
    intro K _ _
    constructor
    · intro y y' hyy
      set P := (hfib K y).choose
      have hP : IsFibreOf 𝒜.toQMFamily y.left P := (hfib K y).choose_spec
      have hP' : IsFibreOf 𝒜.toQMFamily y'.left P := (hφ K y' P).mp hyy.symm
      obtain ⟨𝒜P, h𝒜P⟩ := exists_schemeP hT K P
      obtain ⟨g, -, hg⟩ := hU (fieldPt K) inferInstance 𝒜P
      exact (hg y ((h𝒜P _ _ _).mp hP)).trans (hg y' ((h𝒜P _ _ _).mp hP')).symm
    · intro c
      obtain ⟨P, rfl⟩ := Quotient.exists_rep c
      obtain ⟨𝒜P, h𝒜P⟩ := exists_schemeP hT K P
      obtain ⟨g, hg, -⟩ := hU (fieldPt K) inferInstance 𝒜P
      exact ⟨g, (hφ K g P).mpr ((h𝒜P _ _ _).mpr hg)⟩
  let Φ : PtEquiv Y := fun K _ _ => Equiv.ofBijective (φ K) (hbij K)
  have hΦ : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
      Φ K y = M3.mk P ↔ IsFibreOf 𝒜.toQMFamily y.left P := hφ
  refine ⟨Φ, ⟨hp, hs, ?_, ⟨𝒜, fun K _ _ y P h => (hΦ K y P).mp h⟩, ?_⟩, hΦ⟩
  · -- naturality in the field
    intro K L _ _ _ _ f y P hP
    obtain ⟨Q, hQ⟩ := hfib L (fieldMap f ≫ y)
    refine ⟨Q, (hΦ L _ Q).mpr hQ, ?_⟩
    exact isBaseChangeOf_of_fibres 𝒜.toQMFamily (f : K →+* L) y.left P Q ((hΦ K y P).mp hP) hQ
  · -- classifying maps of families over proper smooth curves
    intro S hpS hsS 𝒜' _
    obtain ⟨g, hg, -⟩ := hU S (isLocallyNoetherian_of_smooth_Q S hsS) 𝒜'
    exact ⟨g, fun K _ _ s P hP => (hΦ K (s ≫ g) P).mpr (isFibreOf_comp hg hP)⟩

end Y3Audit
