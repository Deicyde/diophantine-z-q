/-
H5 lane3 Step 1: GM1 `SeesawPulledBack` reduced to the seesaw primitives. 2026-11-17.
v2: CORRECTS a FALSE primitive. SOURCE-ONLY, UNCOMPILED. Universe u, any characteristic.

CORRECTION (v2; v1 a212642a is frozen in history/Seesaw.v1.a212642a.lean). v1's `SeesawOpenness`
inferred a trivializing neighbourhood from the base section plus ONE trivial slice. That is
FALSE: take `X = T = E` an elliptic curve and the normalized Poincaré bundle (lead/Parent
counterexample). The slice at `0` and the base section are trivial, but every other slice is
nontrivial. v2 states the LOCAL SEESAW (Mumford §5 Cor. 6, local form):
* `T` is reduced and locally of finite type;
* ALL rational slices are trivial (with the base section);
* conclusion: every rational point has a trivializing neighbourhood.
Proof sketch, true:
* on the reduced `T`, `h⁰(L_s) = 1` at every point, by semicontinuity and Jacobson density;
* Grauert, i.e. cohomology and base change in degree 0, makes `pr₂_*L` locally free of rank 1;
* a local generator gives `O → L` on `X × V`;
* that map is an iso on every slice (a nonzero section of a trivial bundle on proper integral `X`
  has no zeros), hence an iso.
Reducedness is essential: over `k[ε]` a nontrivial first-order deformation has a trivial closed
slice. The GM1 assembly is re-checked: its context has `IsReduced T`, `LocallyOfFiniteType fT`
and ALL slices trivial (`hs`), which it now passes.

PROVED here, modulo compile: `seesawPulledBack (hO hD hG hF) : SeesawPulledBack`.
1. Normalize: `L' := L ⊗ (pr₂^* b^*L)ᵛ`.
2. Show `b^*L' ≅ O_T`.
3. Every `K`-slice of `L'` is trivial. Its `pr₂^*b^*L` part is a pullback along `fX ≫ t`, which
   factors through `Spec K`, where every line is trivial (`hF`).
4. Openness (`hO`) and density of rational points (`hD`) make `L'` locally trivial over `T`.
   Gluing along the section (`hG`) makes it trivial.
5. Cancel the invertible factor, using `Iso'.of_tensor_dual_unit` from TwistSelection.lean.

Explicit UNPROVED primitives, each true. The first three are EXACTLY the roles of the UNHELD
StacksFrontier@c496df0d modules that H71's HELD `Cube.TheoremOfTheCube` (3b509d68) imports. Row
data is from the frozen Task-A record d1346f11:
* `SeesawOpenness` (v2): the local seesaw. The RECEIVED Cube4 `Openness` body is the two-face
  CUBE form and does NOT provide it.
* `SeesawDensity`: an open set containing every `K`-point of a scheme locally of finite type over
  an algebraically closed `K` is everything (Jacobson, plus rationality of closed points). Mathlib
  content.
* `SeesawGlue`: local triviality plus triviality along the section give global triviality. This is
  `Cube.GlueTrivial` (d71eaae0…), with `pr₂_* O = O`.
* `LineOnSpecFieldTrivial`: every invertible module on `Spec K` is trivial. C2's
  NativeCubeUnitReduction (42829185…) proves this content.
`Cube.SeesawClosed` (38eb253f…) is the closedness alternative to `hD`; it is not needed here.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.TwistSelection

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2NOS.Step1

section Maps

variable {K : Type u} [Field K] {X T : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
  (fT : T ⟶ Spec (CommRingCat.of K))

/-- The slice `X ≅ X × {t} ⟶ X ×_K T` at a `K`-point `t` of `T`. -/
abbrev sliceAt (t : Spec (CommRingCat.of K) ⟶ T) (ht : t ≫ fT = 𝟙 _) :
    X ⟶ Limits.pullback fX fT :=
  pullback.lift (𝟙 X) (fX ≫ t) (by rw [Category.id_comp, Category.assoc, ht, Category.comp_id])

/-- The base section `T ≅ {x₀} × T ⟶ X ×_K T`. -/
abbrev baseSection (x₀ : Spec (CommRingCat.of K) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _) :
    T ⟶ Limits.pullback fX fT :=
  pullback.lift (fT ≫ x₀) (𝟙 T) (by rw [Category.assoc, hx₀, Category.comp_id, Category.id_comp])

end Maps

/-- Primitive (UNPROVED, v2): the LOCAL SEESAW. `T` is reduced and locally of finite type, and ALL
rational slices and the base section are trivial; then every rational point has a trivializing
neighbourhood. (v1's one-slice form was false.) -/
def SeesawOpenness : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] {X T : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fT : T ⟶ Spec (CommRingCat.of K)) [IsProper fX] [GeometricallyIntegral fX]
    [LocallyOfFiniteType fT] [IsReduced T] (x₀ : Spec (CommRingCat.of K) ⟶ X)
    (hx₀ : x₀ ≫ fX = 𝟙 _) (L : (Limits.pullback fX fT).Modules) [L.IsInvertible],
    Nonempty ((Scheme.Modules.pullback (baseSection fX fT x₀ hx₀)).obj L ≅ 𝟙_ T.Modules) →
    (∀ (t : Spec (CommRingCat.of K) ⟶ T) (ht : t ≫ fT = 𝟙 _),
      Nonempty ((Scheme.Modules.pullback (sliceAt fX fT t ht)).obj L ≅ 𝟙_ X.Modules)) →
    ∀ (t : Spec (CommRingCat.of K) ⟶ T), t ≫ fT = 𝟙 _ →
      ∃ V : T.Opens, t.base (IsLocalRing.closedPoint K) ∈ V ∧
        Nonempty ((Scheme.Modules.pullback (pullback.snd fX fT ⁻¹ᵁ V).ι).obj L ≅ 𝟙_ _)

/-- Primitive (UNPROVED): density of rational points (Jacobson). -/
def SeesawDensity : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] {T : Scheme.{u}} (fT : T ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType fT] (P : T.Opens → Prop),
    (∀ (t : Spec (CommRingCat.of K) ⟶ T), t ≫ fT = 𝟙 _ →
      ∃ V : T.Opens, t.base (IsLocalRing.closedPoint K) ∈ V ∧ P V) →
      ∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ P V

/-- Primitive (UNPROVED): gluing local trivializations along the section (H71 `Cube.GlueTrivial`
role). -/
def SeesawGlue : Prop :=
  ∀ {K : Type u} [Field K] [IsAlgClosed K] {X T : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of K))
    (fT : T ⟶ Spec (CommRingCat.of K)) [IsProper fX] [GeometricallyIntegral fX]
    (x₀ : Spec (CommRingCat.of K) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (L : (Limits.pullback fX fT).Modules) [L.IsInvertible],
    Nonempty ((Scheme.Modules.pullback (baseSection fX fT x₀ hx₀)).obj L ≅ 𝟙_ T.Modules) →
    (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧
      Nonempty ((Scheme.Modules.pullback (pullback.snd fX fT ⁻¹ᵁ V).ι).obj L ≅ 𝟙_ _)) →
      Nonempty (L ≅ 𝟙_ (Limits.pullback fX fT).Modules)

/-- Primitive (UNPROVED): invertible modules on the spectrum of a field are trivial. -/
def LineOnSpecFieldTrivial : Prop :=
  ∀ {K : Type u} [Field K] (M : (Spec (CommRingCat.of K)).Modules) [M.IsInvertible],
    Nonempty (M ≅ 𝟙_ (Spec (CommRingCat.of K)).Modules)

theorem Iso'.dual {X : Scheme.{u}} {A B : X.Modules} (h : Iso' A B) :
    Iso' (Scheme.Modules.dual A) (Scheme.Modules.dual B) :=
  ⟨(Scheme.Modules.dualFunctor.mapIso h.some.op).symm⟩

theorem iso'_dual_unit (X : Scheme.{u}) :
    Iso' (Scheme.Modules.dual (𝟙_ X.Modules)) (𝟙_ X.Modules) :=
  (iso'_unit_left _).symm.trans (iso'_dual (𝟙_ X.Modules))

/-- GM1, PROVED from the seesaw primitives. -/
theorem seesawPulledBack (hO : SeesawOpenness.{u}) (hD : SeesawDensity.{u})
    (hG : SeesawGlue.{u}) (hF : LineOnSpecFieldTrivial.{u}) : SeesawPulledBack.{u} := by
  intro K _ _ X T fX fT _ _ _ _ x₀ hx₀ L _ hslice
  -- `N := pr₂^* b^*L` and the normalized `L' := L ⊗ Nᵛ`
  have hbsnd : baseSection fX fT x₀ hx₀ ≫ pullback.snd fX fT = 𝟙 T := pullback.lift_snd _ _ _
  have hssnd : ∀ (t : Spec (CommRingCat.of K) ⟶ T) (ht : t ≫ fT = 𝟙 _),
      sliceAt fX fT t ht ≫ pullback.snd fX fT = fX ≫ t := fun t ht => pullback.lift_snd _ _ _
  -- (2) `b^*L' ≅ 𝟙`
  have hb : Iso' ((Scheme.Modules.pullback (baseSection fX fT x₀ hx₀)).obj
      (L ⊗ Scheme.Modules.dual ((Scheme.Modules.pullback (pullback.snd fX fT)).obj
        ((Scheme.Modules.pullback (baseSection fX fT x₀ hx₀)).obj L)))) (𝟙_ T.Modules) := by
    refine (iso'_pb_tensor _ _ _).trans ?_
    refine ((iso'_refl _).tensor ((iso'_pb_dual _ _).trans ?_)).trans (iso'_dual _)
    exact ((iso'_pb_comp _ _ _).trans ((iso'_pb_congr hbsnd _).trans (iso'_pb_id _))).dual
  -- (3) every rational slice of `L'` is trivial
  have hs : ∀ (t : Spec (CommRingCat.of K) ⟶ T) (ht : t ≫ fT = 𝟙 _),
      Iso' ((Scheme.Modules.pullback (sliceAt fX fT t ht)).obj
        (L ⊗ Scheme.Modules.dual ((Scheme.Modules.pullback (pullback.snd fX fT)).obj
          ((Scheme.Modules.pullback (baseSection fX fT x₀ hx₀)).obj L)))) (𝟙_ X.Modules) := by
    intro t ht
    have hN : Iso' ((Scheme.Modules.pullback (sliceAt fX fT t ht)).obj
        ((Scheme.Modules.pullback (pullback.snd fX fT)).obj
          ((Scheme.Modules.pullback (baseSection fX fT x₀ hx₀)).obj L))) (𝟙_ X.Modules) :=
      (iso'_pb_comp _ _ _).trans <|
        (iso'_pb_congr (hssnd t ht) _).trans <|
          (iso'_pb_comp _ _ _).symm.trans <|
            (Iso'.pb fX (hF _)).trans (iso'_pb_unit fX)
    refine (iso'_pb_tensor _ _ _).trans ?_
    refine ((hslice t ht).tensor ((iso'_pb_dual _ _).trans hN.dual)).trans ?_
    exact (iso'_unit_left _).trans (iso'_dual_unit X)
  -- (4) local triviality everywhere, then gluing
  have hloc := hD fT (fun V => Nonempty ((Scheme.Modules.pullback (pullback.snd fX fT ⁻¹ᵁ V).ι).obj
      (L ⊗ Scheme.Modules.dual ((Scheme.Modules.pullback (pullback.snd fX fT)).obj
        ((Scheme.Modules.pullback (baseSection fX fT x₀ hx₀)).obj L))) ≅ 𝟙_ _))
    (fun t ht => hO fX fT x₀ hx₀ _ hb hs t ht)
  have hL' := hG fX fT x₀ hx₀ _ hb hloc
  -- (5) cancel the invertible factor
  exact Iso'.of_tensor_dual_unit hL'

end ZInQ.Contrib.CloudR2NOS.Step1
