/-
H5 FIX EDITION STEP-F4 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step-fix3/ZInQKernel/Contrib/CloudR2NOS/Step1/Interfaces.lean (sha256 20f9b1bef0d9e4b765f9c0290cbafad5032c3ed8887542a66905b2708b7123dc).
Body change relative to the base: ONLY P7, four explicit `haveI` instances on the twist inserted before
`have h0 := eulerChar_eq_zero_of_shear …` (record step-fix4/FIX_RECORD_STEP_F4.json). Headers below describe the bases.
-/
/-
H5 FIX EDITION STEP-F3 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step1-i1/src/ZInQKernel/Contrib/CloudR2NOS/Step1/Interfaces.lean (sha256 2c3fb3623ba4a17b23e34409edcacb8500a32fbd0b461686c60f72bd0df0f44c).
Body change relative to the base: ONLY P6, a local `(Msbar Hs Ms).IsInvertible` instance (explicit W07 `Scheme.Modules.isInvertible_pullback`) after each of the 1 `intro k _ Hs _ Ms _ hinf` lines (record step-fix3/FIX_RECORD_STEP_F3.json). Any header below describes the BASE edition.
-/
/-
H5 lane3 Step 1: interfaces and the CoreGap assembly. 2026-11-17. INTERFACE v2 (lead-approved
03:31Z; v1 dd093d6f in history/). On the Y side, the binder `[PkgI2.IsAbelianVariety Y]` becomes
the INTERNAL smoothness-free `[IsProperIntegralGroup Y]` (ProperIntegralGroup.lean). This applies
to the E output, SectionsVanishPicZero, I5b (agreed with C2), G6, T and SS. The A/H̄-side Props
(I5a, I0, I4) are unchanged, and so is the original NOS statement. SOURCE-ONLY,
UNCOMPILED. Universe u, any characteristic or dimension. No Facts: every hypothesis of
`coreGap_of_parts` is a NAMED Prop that remains to be proved.

Consumer interfaces fixed with their producers. Each is stated for ANY abelian variety over an
algebraically closed field, with the agreed conventions: points are morphisms `𝟙_ ⟶ A.X`, `transl`
is RIGHT translation, `⊗`/`ᵛ` are W07 native, and pullback is `Scheme.Modules.pullback`.
* I5a `TheoremOfSquare` (C2, ). Accepted 02:31Z; it comes from the H71 cube, which is pending.
* I5b `InversionTranslationInvariant` (C2). Accepted; C2 derives it from my GM1 `SeesawPulledBack`.
* I0 `ExistsFBSLine` (C2). Accepted; it uses the prefixed FLT/Source `FiniteBySections`.
* I4 `EulerCharTwistInvariant` (C4, ). Form sent 02:29Z; confirmation pending.

Producer contract owned by this lane:
* GM1 `SeesawPulledBack`: a line on `X ×_K T` that is trivial on all `K`-slices `X × {t}` is
  pulled back from `T`.

Further sub-gaps owned by this lane, each stated as an implication from the producer it uses:
* E `InfiniteStabilizerExtraction`: GM1 closedness of the triviality locus, plus GM3, the reduced
  identity component.
* G6 `NontrivialTranslateFromR3`: FBS restricts along closed immersions; FBS on a nonempty scheme
  has a nonzero section; `O_Y` FBS on proper connected `Y` forces `Y` finite.
* T `TwistSelectionFromSquare`: line-bundle algebra via W07 PullbackMonoidal/Dual, plus the
  composition of translations.
* SS `SeesawShearFromSeesaw`: GM1 on `A ×_K Y`, with the shear `ψ(a, y) = (a + y, y)`.
* R3 `SectionsVanishFromInversion`: `s ⊗ [-1]^*s ∈ Γ(O_Y) = K`. It uses C5's
  PureMathlibGlobalFunctions `appTop_bijective`, which is held and independently compiled
  (review 002).
* R1a, R1b, R2 (`ShearVanishing.lean`).

ROUTE NOTE: z ∈ {0, j w} replaces the "finite kernel ⇒ infinite image" step. No finiteness of
`K(N|_Y)` and no homomorphism `Y → Pic Y` is needed.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.I1Assembly
import ZInQKernel.Contrib.CloudR2NOS.Step1.ProperIntegralGroup
import ZInQKernel.Contrib.CloudR2NOS.Step1.ShearVanishing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Dual
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.TensorInvertible
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.PullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

/-- The terminal object of `Over (Spec K)`; its morphisms to `A.X` are the `K`-points. -/
abbrev Pt (K : Type u) [Field K] : Over (Spec (CommRingCat.of K)) :=
  𝟙_ (Over (Spec (CommRingCat.of K)))

/-- Right translation by a point, on the underlying scheme (agreed convention). -/
abbrev transl {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K))))
    (x : Pt K ⟶ A.X) : A.X.left ⟶ A.X.left :=
  (CartesianMonoidalCategory.lift (𝟙 A.X) (CartesianMonoidalCategory.toUnit A.X ≫ x) ≫
    μ[A.X]).left

/-- The prefixed FLT/Source finite-by-sections predicate (consumer form agreed with C2). -/
abbrev FBS {K : Type u} [Field K] {X : Scheme.{u}} (N : X.Modules)
    (f : X ⟶ Spec (CommRingCat.of K)) : Prop :=
  ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.FiniteBySections N f

/-- The twisted line `M ⊗ (t_z^*N ⊗ Nᵛ) = M ⊗ P_z`. -/
abbrev twist {K : Type u} [Field K] (A : Grp (Over (Spec (CommRingCat.of K))))
    (M N : A.X.left.Modules) (z : Pt K ⟶ A.X) : A.X.left.Modules :=
  M ⊗ ((Scheme.Modules.pullback (transl A z)).obj N ⊗ Scheme.Modules.dual N)

/-! ### Consumer interfaces (producers C2/C4) -/

/-- I5a (C2): the theorem of the square, pointwise. -/
def TheoremOfSquare : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A] (N : A.X.left.Modules) [N.IsInvertible] (x y : Pt K ⟶ A.X),
    Nonempty ((Scheme.Modules.pullback (transl A (x * y))).obj N ⊗ N ≅
      (Scheme.Modules.pullback (transl A x)).obj N ⊗ (Scheme.Modules.pullback (transl A y)).obj N)

/-- I5b (C2, via my GM1): `[-1]^*Q ⊗ Q ≅ O` for a translation-invariant line. -/
def InversionTranslationInvariant : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [IsProperIntegralGroup A] (Q : A.X.left.Modules) [Q.IsInvertible],
    (∀ x : Pt K ⟶ A.X, Nonempty ((Scheme.Modules.pullback (transl A x)).obj Q ≅ Q)) →
      Nonempty ((Scheme.Modules.pullback (ι[A.X]).left).obj Q ⊗ Q ≅ 𝟙_ A.X.left.Modules)

/-- I0 (C2): an invertible FBS line. -/
def ExistsFBSLine : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A], ∃ N : A.X.left.Modules, N.IsInvertible ∧ FBS N A.X.hom

/-- I4 (C4): `χ(M ⊗ P_z) = χ(M)`. -/
def EulerCharTwistInvariant : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A] (M N : A.X.left.Modules) [M.IsInvertible] [N.IsInvertible]
    (z : Pt K ⟶ A.X),
    (letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨A.X.hom⟩
     (twist A M N z).eulerChar K) =
    (letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨A.X.hom⟩
     M.eulerChar K)

/-! ### Producer contract of this lane (GM1), consumed by C2 for I5b -/

/-- GM1 seesaw: on `X ×_K T`, with `X` proper and geometrically integral and `T` reduced and
locally of finite type over an algebraically closed `K`, a line that is trivial on every slice
`X × {t}` (for `t` a `K`-point) is the pullback of its restriction to `{x₀} × T`. -/
def SeesawPulledBack : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] {X T : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fT : T ⟶ Spec (CommRingCat.of K)) [IsProper fX] [GeometricallyIntegral fX]
    [LocallyOfFiniteType fT] [IsReduced T]
    (x₀ : Spec (CommRingCat.of K) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (L : (Limits.pullback fX fT).Modules) [L.IsInvertible],
    (∀ (t : Spec (CommRingCat.of K) ⟶ T) (ht : t ≫ fT = 𝟙 _),
      Nonempty ((Scheme.Modules.pullback (pullback.lift (𝟙 X) (fX ≫ t)
        (by rw [Category.id_comp, Category.assoc, ht, Category.comp_id]))).obj L ≅
          𝟙_ X.Modules)) →
      Nonempty (L ≅ (Scheme.Modules.pullback (pullback.snd fX fT)).obj
        ((Scheme.Modules.pullback (pullback.lift (fT ≫ x₀) (𝟙 T)
          (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp]))).obj L))

/-! ### Sub-gaps owned by this lane (each UNPROVED, stated exactly) -/

/-- E: an infinite stabilizer contains the points of a positive-dimensional abelian
subvariety. This needs GM1 closedness of the triviality locus, plus GM3 (the reduced identity
component of a closed subgroup is an abelian subvariety). -/
def InfiniteStabilizerExtraction : Prop :=
  ∀ {k : Type u} [Field k] (Hs : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety Hs]
    (Ms : Hs.X.left.Modules) [Ms.IsInvertible],
    (stabilizerSet Hs Ms).Infinite →
      ∃ (Y : Grp (Over (Spec (CommRingCat.of (AlgebraicClosure k))))) (_ : IsProperIntegralGroup Y)
        (j : Y.X ⟶ (PkgI2.baseChange Hs (AlgebraicClosure k)).X) (_ : IsMonHom j),
        IsClosedImmersion j.left ∧ ¬ IsFinite Y.X.hom ∧
          ∀ y : Pt (AlgebraicClosure k) ⟶ Y.X, y ≫ j ∈ stabilizerSet Hs Ms

/-- R3 target: a nontrivial translation-invariant line on an abelian variety has no global
sections. -/
def SectionsVanishPicZero : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (Y : Grp (Over (Spec (CommRingCat.of K))))
    [IsProperIntegralGroup Y] (Q : Y.X.left.Modules) [Q.IsInvertible],
    (∀ x : Pt K ⟶ Y.X, Nonempty ((Scheme.Modules.pullback (transl Y x)).obj Q ≅ Q)) →
      ¬ Nonempty (Q ≅ 𝟙_ Y.X.left.Modules) → Subsingleton (Q.H 0)

/-- R3: `SectionsVanishPicZero` from I5b. -/
def SectionsVanishFromInversion : Prop :=
  InversionTranslationInvariant.{u} → SectionsVanishPicZero.{u}

/-- G6 target: an FBS line has a translate on `Y` that is not isomorphic to it. -/
def NontrivialTranslateOnSubvariety : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A Y : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A] [IsProperIntegralGroup Y] (j : Y.X ⟶ A.X) [IsMonHom j],
    IsClosedImmersion j.left → ¬ IsFinite Y.X.hom →
      ∀ (N : A.X.left.Modules) [N.IsInvertible], FBS N A.X.hom →
        ∃ w : Pt K ⟶ Y.X, ¬ Nonempty ((Scheme.Modules.pullback (transl Y w)).obj
          ((Scheme.Modules.pullback j.left).obj N) ≅ (Scheme.Modules.pullback j.left).obj N)

/-- G6: `NontrivialTranslateOnSubvariety` from R3. -/
def NontrivialTranslateFromR3 : Prop :=
  SectionsVanishPicZero.{u} → NontrivialTranslateOnSubvariety.{u}

/-- T target: choose `z ∈ {0, j w}` so that `L' = M ⊗ P_z` is translation-invariant along `Y`
and nontrivial on `Y`. -/
def TwistSelection : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A Y : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A] [IsProperIntegralGroup Y] (j : Y.X ⟶ A.X) [IsMonHom j]
    (M N : A.X.left.Modules) [M.IsInvertible] [N.IsInvertible] (w : Pt K ⟶ Y.X),
    ¬ Nonempty ((Scheme.Modules.pullback (transl Y w)).obj ((Scheme.Modules.pullback j.left).obj N) ≅
      (Scheme.Modules.pullback j.left).obj N) →
    (∀ y : Pt K ⟶ Y.X, Nonempty ((Scheme.Modules.pullback (transl A (y ≫ j))).obj M ≅ M)) →
      ∃ z : Pt K ⟶ A.X,
        (∀ y : Pt K ⟶ Y.X, Nonempty ((Scheme.Modules.pullback (transl A (y ≫ j))).obj
          (twist A M N z) ≅ twist A M N z)) ∧
        (∀ y : Pt K ⟶ Y.X, Nonempty ((Scheme.Modules.pullback (transl Y y)).obj
          ((Scheme.Modules.pullback j.left).obj (twist A M N z)) ≅
            (Scheme.Modules.pullback j.left).obj (twist A M N z))) ∧
        ¬ Nonempty ((Scheme.Modules.pullback j.left).obj (twist A M N z) ≅ 𝟙_ Y.X.left.Modules)

/-- T: `TwistSelection` from I5a. -/
def TwistSelectionFromSquare : Prop :=
  TheoremOfSquare.{u} → TwistSelection.{u}

/-- SS target: the shear automorphism over `Y` and the seesaw iso
`ψ^*(pr₁^*L) ≅ pr₁^*L ⊗ pr₂^*(j^*L)`. -/
def SeesawShear : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] (A Y : Grp (Over (Spec (CommRingCat.of K))))
    [PkgI2.IsAbelianVariety A] [IsProperIntegralGroup Y] (j : Y.X ⟶ A.X) [IsMonHom j],
    IsClosedImmersion j.left →
      ∀ (L : A.X.left.Modules) [L.IsInvertible],
        (∀ y : Pt K ⟶ Y.X, Nonempty ((Scheme.Modules.pullback (transl A (y ≫ j))).obj L ≅ L)) →
          ∃ (ψ : Limits.pullback A.X.hom Y.X.hom ⟶ Limits.pullback A.X.hom Y.X.hom) (_ : IsIso ψ),
            ψ ≫ pullback.snd A.X.hom Y.X.hom = pullback.snd A.X.hom Y.X.hom ∧
            Nonempty ((Scheme.Modules.pullback ψ).obj
                ((Scheme.Modules.pullback (pullback.fst A.X.hom Y.X.hom)).obj L) ≅
              (Scheme.Modules.pullback (pullback.fst A.X.hom Y.X.hom)).obj L ⊗
                (Scheme.Modules.pullback (pullback.snd A.X.hom Y.X.hom)).obj
                  ((Scheme.Modules.pullback j.left).obj L))

/-- SS: `SeesawShear` from GM1. -/
def SeesawShearFromSeesaw : Prop :=
  SeesawPulledBack.{u} → SeesawShear.{u}

/-! ### Assembly (proved from the named parts) -/

theorem coreGap_of_parts
    (hE : InfiniteStabilizerExtraction.{u}) (hI0 : ExistsFBSLine.{u})
    (hI4 : EulerCharTwistInvariant.{u}) (hI5a : TheoremOfSquare.{u})
    (hI5b : InversionTranslationInvariant.{u}) (hGM1 : SeesawPulledBack.{u})
    (hT : TwistSelectionFromSquare.{u}) (hSS : SeesawShearFromSeesaw.{u})
    (hR3 : SectionsVanishFromInversion.{u}) (hG6 : NontrivialTranslateFromR3.{u})
    (hR1a : RelativeVanishingSections.{u}) (hR1b : RelativeDetectionSections.{u})
    (hR2 : HigherDirectImageAutomorphism.{u}) :
    CoreGap.{u} := by
  intro k _ Hs _ Ms _ hinf
  haveI : (Msbar Hs Ms).IsInvertible :=
    Scheme.Modules.isInvertible_pullback
      (pullback.fst Hs.X.hom (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) Ms
  obtain ⟨Y, hY, j, hj, hjc, hfin, hstab⟩ := hE Hs Ms hinf
  haveI := hY
  haveI := hj
  haveI : IsProper (PkgI2.baseChange Hs (AlgebraicClosure k)).X.hom :=
    PkgI2.IsAbelianVariety.proper
  haveI : IsProper Y.X.hom := IsProperIntegralGroup.proper
  haveI : CompactSpace Y.X.left := QuasiCompact.compactSpace_of_compactSpace Y.X.hom
  haveI : Nonempty Y.X.left :=
    ⟨(η[Y.X] : Pt (AlgebraicClosure k) ⟶ Y.X).left.base
      (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of (AlgebraicClosure k)))))⟩
  -- I0, then G6 (from R3, from I5b): a translate of `N|_Y` not isomorphic to `N|_Y`
  obtain ⟨N, hN, hNfbs⟩ := hI0 (PkgI2.baseChange Hs (AlgebraicClosure k))
  haveI := hN
  obtain ⟨w, hw⟩ := hG6 (hR3 hI5b) (PkgI2.baseChange Hs (AlgebraicClosure k)) Y j hjc hfin N hNfbs
  -- T (from I5a): `L' = M̄ ⊗ P_z`, translation-invariant along `Y` and nontrivial on `Y`
  obtain ⟨z, h1, h2, h3⟩ := hT hI5a (PkgI2.baseChange Hs (AlgebraicClosure k)) Y j
    (Msbar Hs Ms) N w hw hstab
  -- I4: `χ(L') = χ(M̄)`
  have hχ := hI4 (PkgI2.baseChange Hs (AlgebraicClosure k)) (Msbar Hs Ms) N z
  -- SS (from GM1): the shear automorphism and the seesaw iso for `L'`
  obtain ⟨ψ, hψiso, hψ, ⟨σ⟩⟩ := hSS hGM1 (PkgI2.baseChange Hs (AlgebraicClosure k)) Y j hjc
    (twist (PkgI2.baseChange Hs (AlgebraicClosure k)) (Msbar Hs Ms) N z) h1
  haveI := hψiso
  -- R3: `Γ(Y, L'|_Y) = 0`
  have hQ := hR3 hI5b Y
    ((Scheme.Modules.pullback j.left).obj
      (twist (PkgI2.baseChange Hs (AlgebraicClosure k)) (Msbar Hs Ms) N z)) h2 h3
  -- GM5′ (proved from R1a, R1b, R2): `χ(L') = 0`
  -- STEP-F4: instances on the twist (it lives on the non-reducible `PkgI2.baseChange`), explicitly
  haveI hLinv : (twist (PkgI2.baseChange Hs (AlgebraicClosure k)) (Msbar Hs Ms) N z).IsInvertible := inferInstance
  haveI : (twist (PkgI2.baseChange Hs (AlgebraicClosure k)) (Msbar Hs Ms) N z).IsQuasicoherent :=
    SheafOfModules.IsInvertible.isQuasicoherent.{u, u, u} hLinv
  haveI : (twist (PkgI2.baseChange Hs (AlgebraicClosure k)) (Msbar Hs Ms) N z).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  haveI : (twist (PkgI2.baseChange Hs (AlgebraicClosure k)) (Msbar Hs Ms) N z).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have h0 := eulerChar_eq_zero_of_shear hR1a hR1b hR2
    (PkgI2.baseChange Hs (AlgebraicClosure k)).X.hom Y.X.hom
    (twist (PkgI2.baseChange Hs (AlgebraicClosure k)) (Msbar Hs Ms) N z)
    ((Scheme.Modules.pullback j.left).obj
      (twist (PkgI2.baseChange Hs (AlgebraicClosure k)) (Msbar Hs Ms) N z)) hQ ψ hψ σ
  exact hχ.symm.trans h0

/-- I1, in the agreed form, from the named parts and the seam's `hEuler`. -/
theorem stabilizer_finite_of_parts
    (hE : InfiniteStabilizerExtraction.{u}) (hI0 : ExistsFBSLine.{u})
    (hI4 : EulerCharTwistInvariant.{u}) (hI5a : TheoremOfSquare.{u})
    (hI5b : InversionTranslationInvariant.{u}) (hGM1 : SeesawPulledBack.{u})
    (hT : TwistSelectionFromSquare.{u}) (hSS : SeesawShearFromSeesaw.{u})
    (hR3 : SectionsVanishFromInversion.{u}) (hG6 : NontrivialTranslateFromR3.{u})
    (hR1a : RelativeVanishingSections.{u}) (hR1b : RelativeDetectionSections.{u})
    (hR2 : HigherDirectImageAutomorphism.{u})
    {k : Type u} [Field k] (Hs : Grp (Over (Spec (CommRingCat.of k)))) [PkgI2.IsAbelianVariety Hs]
    (Ms : Hs.X.left.Modules) [Ms.IsInvertible]
    (hχ : (letI : Hs.X.left.Over (Spec (CommRingCat.of k)) := ⟨Hs.X.hom⟩
           Ms.eulerChar k) ≠ 0) :
    (stabilizerSet Hs Ms).Finite :=
  stabilizer_finite_of_eulerChar_ne_zero
    (coreGap_of_parts hE hI0 hI4 hI5a hI5b hGM1 hT hSS hR3 hG6 hR1a hR1b hR2) Hs Ms hχ

end ZInQ.Contrib.CloudR2NOS.Step1
