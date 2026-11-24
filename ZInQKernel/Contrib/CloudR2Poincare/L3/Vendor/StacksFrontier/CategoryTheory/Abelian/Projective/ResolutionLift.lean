import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.CategoryTheory.Abelian.Projective.ResolutionLift`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Lifting a projective resolution into an arbitrary resolution

Mathlib's `CategoryTheory.ProjectiveResolution.lift` and
`CategoryTheory.ProjectiveResolution.liftHomotopy` lift a morphism `f : Y ⟶ Z` to a chain map
between projective resolutions of `Y` and of `Z`, and show that the lift is unique up to
homotopy. Both are stated with *both* sides a `ProjectiveResolution`, but inspecting their proofs
shows that the projectivity of the **target** is never used: the source contributes the
projectivity of its terms, through `Projective.factorThru` and
`CategoryTheory.ShortComplex.Exact.liftFromProjective`, and the target contributes only its
exactness, through `ProjectiveResolution.exact₀` and `ProjectiveResolution.exact_succ`. Neither
`Q.projective` nor any consequence of it appears.

This file records the resulting hypothesis weakening: the target may be an arbitrary resolution,
that is, an arbitrary `ℕ`-indexed chain complex `Q` together with a quasi-isomorphism
`ε : Q ⟶ Z[0]`, with no projectivity assumed. The homotopy statements weaken the source as well,
to an arbitrary chain complex of projective objects, since they never use its augmentation. The
generalized declarations are named after the Mathlib ones with a prime; Mathlib's versions are
the special case `ε = Q.π`.

The exactness of such a target, which Mathlib derives as a method of `ProjectiveResolution`, is
re-derived here for a bare augmented complex, in the `ChainComplex` namespace.

## Main results

* `ChainComplex.exact₀_and_epi_of_quasiIso` and `ChainComplex.exact_succ_of_quasiIso`: the
  exactness of `… → Q₁ → Q₀ → Z → 0` carried by a quasi-isomorphism `ε : Q ⟶ Z[0]`.
* `CategoryTheory.ProjectiveResolution.lift'`: a morphism `f : Y ⟶ Z` lifts to a chain map from a
  projective resolution of `Y` to any resolution of `Z`, compatibly with the augmentations
  (`CategoryTheory.ProjectiveResolution.lift'_commutes`).
* `CategoryTheory.ProjectiveResolution.liftHomotopy'`: two chain maps from a complex of
  projectives into a resolution which agree after the augmentation are homotopic.
* `CategoryTheory.ProjectiveResolution.homologyMap_map_eq_of_comp_eq`: hence the maps they induce
  on the homology of the image under an additive functor agree, which is the form in which left
  derived functors consume the statement.
* `CategoryTheory.Functor.mapAugmentation`: the image of such an augmentation under an additive
  functor, a quasi-isomorphism again as soon as the functor preserves homology. This is how a
  non-projective resolution arises in practice: apply an exact functor to a projective one.

## Implementation notes

The projectivity of the source is taken as the instance-implicit `[∀ n, Projective (P.X n)]`,
which makes Mathlib's statements literal special cases, since `ProjectiveResolution.projective` is
already an instance. No boundedness hypothesis is needed: the complexes are indexed by `ℕ`, which
is exactly the bounded-below condition that the inductive argument consumes.

Two places need care, both instances of the same phenomenon: `((ChainComplex.single₀ C).obj Z).X 0`
is equal to `Z` only by default-transparency unfolding of the `if` in
`HomologicalComplex.single`. Mathlib covers for this with
`set_option backward.isDefEq.respectTransparency false` on `liftFZero` and `liftFOne`; here the
spelling is changed instead, which removes the need for it.

* `liftFZero'` factors `(R.π ≫ (ChainComplex.single₀ C).map f).f 0` rather than the equal
  `R.π.f 0 ≫ f`, so that the codomain of the morphism being factored is spelled
  `((ChainComplex.single₀ C).obj Z).X 0`, which is how `Epi (ε.f 0)` is stated. Instance search
  runs below default transparency, so with the other spelling the `Epi` hypothesis of
  `Projective.factorThru` cannot be synthesized at all.
* For the same reason `simp` cannot apply `ProjectiveResolution.complex_d_comp_π_f_zero_assoc` to
  `R.complex.d 1 0 ≫ R.π.f 0 ≫ f`, so the side condition of `liftFOne'` is discharged by an
  explicit rewrite chain that stays at the `((ChainComplex.single₀ C).map f).f 0` spelling.
-/

 noncomputable section
#cloudR2LocalInstances

open _root_.CategoryTheory
open CategoryTheory Category Limits

universe v u v₂ u₂

namespace ChainComplex
#cloudR2LocalInstances

variable {C : Type u} [Category.{v} C] [Abelian C] {Z : C} {Q : ChainComplex C ℕ}
#cloudR2Vendor d_one_zero_comp_f_zero in

/-- The augmentation of a chain complex kills the image of the differential out of degree `1`:
if `ε : Q ⟶ Z[0]` then `Q.d 1 0 ≫ ε.f 0 = 0`. -/
@[reassoc (attr := simp)]
lemma d_one_zero_comp_f_zero (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) :
    Q.d 1 0 ≫ ε.f 0 = 0 := by
  rw [← ε.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]
#cloudR2Vendor exact₀_and_epi_of_quasiIso in

/-- If `ε : Q ⟶ Z[0]` is a quasi-isomorphism then `Q₁ → Q₀ → Z` is exact and `Q₀ → Z` is an
epimorphism; that is, `Z` is the cokernel of `Q.d 1 0`. This is the degree-zero half of the
exactness of `… → Q₁ → Q₀ → Z → 0`. -/
lemma exact₀_and_epi_of_quasiIso (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε] :
    (ShortComplex.mk _ _ (d_one_zero_comp_f_zero ε)).Exact ∧ Epi (ε.f 0) := by
  have h : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map ε) :=
    (ChainComplex.quasiIsoAt₀_iff ε).mp inferInstance
  exact (ShortComplex.quasiIso_iff_of_zeros'
    ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.down ℕ) 1 0 0).map ε)
    (Q.shape 0 0 (by simp)) rfl rfl).mp h
#cloudR2Vendor exact₀_of_quasiIso in

/-- The exactness of `Q₁ → Q₀ → Z` carried by a quasi-isomorphism `ε : Q ⟶ Z[0]`. This is the
analogue for an arbitrary resolution of `CategoryTheory.ProjectiveResolution.exact₀`. -/
lemma exact₀_of_quasiIso (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε] :
    (ShortComplex.mk _ _ (d_one_zero_comp_f_zero ε)).Exact :=
  (exact₀_and_epi_of_quasiIso ε).1
#cloudR2Vendor epi_f_zero_of_quasiIso in

/-- The augmentation of a resolution is an epimorphism in degree zero. -/
local instance epi_f_zero_of_quasiIso (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε] :
    Epi (ε.f 0) :=
  (exact₀_and_epi_of_quasiIso ε).2
#cloudR2Vendor exactAt_succ_of_quasiIso in

/-- A complex admitting a quasi-isomorphism to a complex concentrated in degree `0` is exact in
every positive degree. This is the analogue for an arbitrary resolution of
`CategoryTheory.ProjectiveResolution.complex_exactAt_succ`. -/
lemma exactAt_succ_of_quasiIso (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε] (n : ℕ) :
    Q.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt' ε (n + 1) (ChainComplex.exactAt_succ_single_obj _ _)]
  infer_instance
#cloudR2Vendor exact_succ_of_quasiIso in

/-- The exactness of `Qₙ₊₂ → Qₙ₊₁ → Qₙ` carried by a quasi-isomorphism `ε : Q ⟶ Z[0]`. This is
the analogue for an arbitrary resolution of
`CategoryTheory.ProjectiveResolution.exact_succ`. -/
lemma exact_succ_of_quasiIso (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε] (n : ℕ) :
    (ShortComplex.mk _ _ (Q.d_comp_d (n + 2) (n + 1) n)).Exact :=
  ((HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n)
    (by simp only [ChainComplex.prev]; rfl) (by simp)).1 (exactAt_succ_of_quasiIso ε n)

end ChainComplex

namespace CategoryTheory.Functor
#cloudR2LocalInstances

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {Z : C} {Q : ChainComplex C ℕ}
#cloudR2Vendor mapAugmentation in

/-- The image under an additive functor `F` of an augmentation `ε : Q ⟶ Z[0]`, as an augmentation
`F(Q) ⟶ F(Z)[0]`. -/
def mapAugmentation (F : C ⥤ D) [F.Additive] (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q ⟶
      (ChainComplex.single₀ D).obj (F.obj Z) :=
  (F.mapHomologicalComplex _).map ε ≫
    (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).hom.app Z
#cloudR2Vendor quasiIso_mapAugmentation in

/-- An additive functor which preserves homology sends a resolution to a resolution. Together
with `ChainComplex.exact₀_of_quasiIso` and `ChainComplex.exact_succ_of_quasiIso` this is how a
resolution whose terms are *not* projective arises in practice: apply an exact functor to a
projective resolution. -/
local instance quasiIso_mapAugmentation (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε] :
    QuasiIso (F.mapAugmentation ε) := by
  dsimp only [mapAugmentation]
  infer_instance
#cloudR2Vendor mapAugmentation_f_zero in

/-- In degree zero, `CategoryTheory.Functor.mapAugmentation` is the image of the degree-zero
component of the original augmentation. -/
@[simp]
lemma mapAugmentation_f_zero (F : C ⥤ D) [F.Additive]
    (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) :
    (F.mapAugmentation ε).f 0 = F.map (ε.f 0) := by
  simp [mapAugmentation]

end CategoryTheory.Functor

namespace CategoryTheory.ProjectiveResolution
#cloudR2LocalInstances

variable {C : Type u} [Category.{v} C] [Abelian C] {Z : C}

section Lift
#cloudR2LocalInstances

variable {Y : C} {Q : ChainComplex C ℕ} (f : Y ⟶ Z) (R : ProjectiveResolution Y)
  (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε]
#cloudR2Vendor liftFZero' in

/-- An auxiliary construction for `CategoryTheory.ProjectiveResolution.lift'`: the degree-zero
component, obtained by factoring the augmented morphism through the epimorphism `ε.f 0`. -/
def liftFZero' : R.complex.X 0 ⟶ Q.X 0 :=
  Projective.factorThru ((R.π ≫ (ChainComplex.single₀ C).map f).f 0) (ε.f 0)
#cloudR2Vendor liftFZero'_comp in

/-- The defining property of `CategoryTheory.ProjectiveResolution.liftFZero'`. -/
@[reassoc (attr := simp)]
lemma liftFZero'_comp :
    liftFZero' f R ε ≫ ε.f 0 = (R.π ≫ (ChainComplex.single₀ C).map f).f 0 :=
  Projective.factorThru_comp _ _
#cloudR2Vendor liftFOne' in

/-- An auxiliary construction for `CategoryTheory.ProjectiveResolution.lift'`: the degree-one
component. -/
def liftFOne' : R.complex.X 1 ⟶ Q.X 1 :=
  (ChainComplex.exact₀_of_quasiIso ε).liftFromProjective
    (R.complex.d 1 0 ≫ liftFZero' f R ε)
    (by rw [assoc, liftFZero'_comp, HomologicalComplex.comp_f, ← assoc,
      R.complex_d_comp_π_f_zero, zero_comp])
#cloudR2Vendor liftFOne'_zero_comm in

/-- The degree-zero and degree-one components of
`CategoryTheory.ProjectiveResolution.lift'` form a commuting square. -/
@[simp]
lemma liftFOne'_zero_comm :
    liftFOne' f R ε ≫ Q.d 1 0 = R.complex.d 1 0 ≫ liftFZero' f R ε :=
  (ChainComplex.exact₀_of_quasiIso ε).liftFromProjective_comp _ _
#cloudR2Vendor liftFSucc' in

/-- An auxiliary construction for `CategoryTheory.ProjectiveResolution.lift'`: the inductive step,
producing the component in degree `n + 2` from the commuting square in degrees `n + 1` and `n`. -/
def liftFSucc' (n : ℕ) (g : R.complex.X n ⟶ Q.X n) (g' : R.complex.X (n + 1) ⟶ Q.X (n + 1))
    (w : g' ≫ Q.d (n + 1) n = R.complex.d (n + 1) n ≫ g) :
    Σ' g'' : R.complex.X (n + 2) ⟶ Q.X (n + 2),
      g'' ≫ Q.d (n + 2) (n + 1) = R.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨(ChainComplex.exact_succ_of_quasiIso ε n).liftFromProjective
      (R.complex.d (n + 2) (n + 1) ≫ g') (by simp [w]),
    (ChainComplex.exact_succ_of_quasiIso ε n).liftFromProjective_comp _ _⟩
#cloudR2Vendor lift' in

/-- A morphism `f : Y ⟶ Z` lifts to a chain map from a projective resolution of `Y` to an
arbitrary resolution `ε : Q ⟶ Z[0]` of `Z`. This is `CategoryTheory.ProjectiveResolution.lift`
with the target no longer required to be projective. -/
def lift' : R.complex ⟶ Q :=
  ChainComplex.mkHom _ _ (liftFZero' f R ε) (liftFOne' f R ε) (liftFOne'_zero_comm f R ε)
    fun n ⟨g, g', w⟩ => ⟨(liftFSucc' R ε n g g' w).1, (liftFSucc' R ε n g g' w).2⟩
#cloudR2Vendor lift'_commutes in

/-- The augmentations intertwine the lift of a morphism and that morphism. This is
`CategoryTheory.ProjectiveResolution.lift_commutes` with the target no longer required to be
projective. -/
@[reassoc (attr := simp)]
theorem lift'_commutes : lift' f R ε ≫ ε = R.π ≫ (ChainComplex.single₀ C).map f := by
  ext
  exact liftFZero'_comp f R ε
#cloudR2Vendor lift'_commutes_zero in

/-- The degree-zero component of `CategoryTheory.ProjectiveResolution.lift'_commutes`. -/
@[reassoc (attr := simp)]
lemma lift'_commutes_zero : (lift' f R ε).f 0 ≫ ε.f 0 = R.π.f 0 ≫ f :=
  (HomologicalComplex.congr_hom (lift'_commutes f R ε) 0).trans (by simp)

end Lift

section Homotopy
#cloudR2LocalInstances

variable {P Q : ChainComplex C ℕ} [∀ n, Projective (P.X n)]
  (ε : Q ⟶ (ChainComplex.single₀ C).obj Z) [QuasiIso ε]
#cloudR2Vendor liftHomotopyZeroZero' in

/-- An auxiliary construction for
`CategoryTheory.ProjectiveResolution.liftHomotopyZero'`. -/
def liftHomotopyZeroZero' (f : P ⟶ Q) (comm : f ≫ ε = 0) : P.X 0 ⟶ Q.X 1 :=
  (ChainComplex.exact₀_of_quasiIso ε).liftFromProjective (f.f 0)
    (congr_fun (congr_arg HomologicalComplex.Hom.f comm) 0)
#cloudR2Vendor liftHomotopyZeroZero'_comp in

/-- The defining property of
`CategoryTheory.ProjectiveResolution.liftHomotopyZeroZero'`. -/
@[reassoc (attr := simp)]
lemma liftHomotopyZeroZero'_comp (f : P ⟶ Q) (comm : f ≫ ε = 0) :
    liftHomotopyZeroZero' ε f comm ≫ Q.d 1 0 = f.f 0 :=
  (ChainComplex.exact₀_of_quasiIso ε).liftFromProjective_comp _ _
#cloudR2Vendor liftHomotopyZeroOne' in

/-- An auxiliary construction for
`CategoryTheory.ProjectiveResolution.liftHomotopyZero'`. -/
def liftHomotopyZeroOne' (f : P ⟶ Q) (comm : f ≫ ε = 0) : P.X 1 ⟶ Q.X 2 :=
  (ChainComplex.exact_succ_of_quasiIso ε 0).liftFromProjective
    (f.f 1 - P.d 1 0 ≫ liftHomotopyZeroZero' ε f comm)
    (by rw [Preadditive.sub_comp, assoc, HomologicalComplex.Hom.comm,
      liftHomotopyZeroZero'_comp, sub_self])
#cloudR2Vendor liftHomotopyZeroOne'_comp in

/-- The defining property of
`CategoryTheory.ProjectiveResolution.liftHomotopyZeroOne'`. -/
@[reassoc (attr := simp)]
lemma liftHomotopyZeroOne'_comp (f : P ⟶ Q) (comm : f ≫ ε = 0) :
    liftHomotopyZeroOne' ε f comm ≫ Q.d 2 1 =
      f.f 1 - P.d 1 0 ≫ liftHomotopyZeroZero' ε f comm :=
  (ChainComplex.exact_succ_of_quasiIso ε 0).liftFromProjective_comp _ _
#cloudR2Vendor liftHomotopyZeroSucc' in

/-- An auxiliary construction for
`CategoryTheory.ProjectiveResolution.liftHomotopyZero'`: the inductive step. -/
def liftHomotopyZeroSucc' (f : P ⟶ Q) (n : ℕ) (g : P.X n ⟶ Q.X (n + 1))
    (g' : P.X (n + 1) ⟶ Q.X (n + 2))
    (w : f.f (n + 1) = P.d (n + 1) n ≫ g + g' ≫ Q.d (n + 2) (n + 1)) :
    P.X (n + 2) ⟶ Q.X (n + 3) :=
  (ChainComplex.exact_succ_of_quasiIso ε (n + 1)).liftFromProjective
    (f.f (n + 2) - P.d _ _ ≫ g') (by simp [w])
#cloudR2Vendor liftHomotopyZeroSucc'_comp in

/-- The defining property of
`CategoryTheory.ProjectiveResolution.liftHomotopyZeroSucc'`. -/
@[reassoc (attr := simp)]
lemma liftHomotopyZeroSucc'_comp (f : P ⟶ Q) (n : ℕ) (g : P.X n ⟶ Q.X (n + 1))
    (g' : P.X (n + 1) ⟶ Q.X (n + 2))
    (w : f.f (n + 1) = P.d (n + 1) n ≫ g + g' ≫ Q.d (n + 2) (n + 1)) :
    liftHomotopyZeroSucc' ε f n g g' w ≫ Q.d (n + 3) (n + 2) =
      f.f (n + 2) - P.d _ _ ≫ g' :=
  (ChainComplex.exact_succ_of_quasiIso ε (n + 1)).liftFromProjective_comp _ _
#cloudR2Vendor liftHomotopyZero' in

/-- A chain map from a complex of projective objects into a resolution `ε : Q ⟶ Z[0]` which
vanishes on the augmentation is homotopic to zero. This is
`CategoryTheory.ProjectiveResolution.liftHomotopyZero` with the target no longer required to be
projective and the source no longer required to resolve anything. -/

def liftHomotopyZero' (f : P ⟶ Q) (comm : f ≫ ε = 0) : Homotopy f 0 :=
  Homotopy.mkInductive _ (liftHomotopyZeroZero' ε f comm) (by simp)
    (liftHomotopyZeroOne' ε f comm) (by simp) fun n ⟨g, g', w⟩ =>
    ⟨liftHomotopyZeroSucc' ε f n g g' w, by simp⟩
#cloudR2Vendor liftHomotopy' in

/-- Two chain maps from a complex of projective objects into a resolution `ε : Q ⟶ Z[0]` which
agree after the augmentation are homotopic. This is
`CategoryTheory.ProjectiveResolution.liftHomotopy` with the target no longer required to be
projective; accordingly the hypothesis is stated as agreement after `ε` rather than through a
factorization `P.π ≫ (ChainComplex.single₀ C).map f`, which presumes a `P.π`. Mathlib's form
follows by rewriting with the two commutation hypotheses. -/

def liftHomotopy' (g h : P ⟶ Q) (w : g ≫ ε = h ≫ ε) : Homotopy g h :=
  Homotopy.equivSubZero.invFun
    (liftHomotopyZero' ε (g - h) (by rw [Preadditive.sub_comp, w, sub_self]))

omit [∀ n, Projective (P.X n)] [QuasiIso ε] in
#cloudR2Vendor comp_eq_of_f_zero_eq in
/-- A morphism into `Z[0]` is determined by its degree-zero component, so the hypothesis of
`CategoryTheory.ProjectiveResolution.liftHomotopy'` may be checked in degree zero. -/
lemma comp_eq_of_f_zero_eq (g h : P ⟶ Q) (w : g.f 0 ≫ ε.f 0 = h.f 0 ≫ ε.f 0) :
    g ≫ ε = h ≫ ε := by
  ext
  simpa using w
#cloudR2Vendor quotient_map_eq_of_comp_eq in

/-- Two chain maps from a complex of projective objects into a resolution which agree after the
augmentation become equal in the homotopy category. Consequently a morphism out of
`(HomotopyCategory.quotient C (ComplexShape.down ℕ)).obj P` may be specified by *any* lift. -/

theorem quotient_map_eq_of_comp_eq (g h : P ⟶ Q) (w : g ≫ ε = h ≫ ε) :
    (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map g =
      (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map h :=
  HomotopyCategory.eq_of_homotopy _ _ (liftHomotopy' ε g h w)
#cloudR2Vendor quotient_map_map_eq_of_comp_eq in

/-- Applying an additive functor `F` to two chain maps from a complex of projective objects into a
resolution which agree after the augmentation gives equal morphisms in the homotopy category. -/
theorem quotient_map_map_eq_of_comp_eq {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (g h : P ⟶ Q) (w : g ≫ ε = h ≫ ε) :
    (HomotopyCategory.quotient D (ComplexShape.down ℕ)).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map g) =
      (HomotopyCategory.quotient D (ComplexShape.down ℕ)).map
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map h) :=
  HomotopyCategory.eq_of_homotopy _ _ (F.mapHomotopy (liftHomotopy' ε g h w))
#cloudR2Vendor homologyMap_map_eq_of_comp_eq in

/-- The maps induced on the homology of the image under an additive functor `F` by two chain maps
from a complex of projective objects into a resolution which agree after the augmentation are
equal. This is the form in which left derived functors consume the statement: the value of `Lₙ F`
on a morphism may be computed from any lift into any resolution of the target. -/
theorem homologyMap_map_eq_of_comp_eq {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (g h : P ⟶ Q) (w : g ≫ ε = h ≫ ε) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map g) n =
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map h) n :=
  (F.mapHomotopy (liftHomotopy' ε g h w)).homologyMap_eq n

end Homotopy

end CategoryTheory.ProjectiveResolution

end

end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
