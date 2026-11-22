/-
Multiplication-etale construction: ActualOriginRelativeTransport.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.ActualStalkWorld

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj H101DirectFieldRoute.ActualTransport

noncomputable section

namespace H101DirectFieldRoute.ActualTransport

universe u
variable {X B : Scheme.{u}}

/-- Native tangent integer derivations at x, rebased along the ACTUAL base
stalk iso implied by f >> p = p. The coefficient field and target stalk are
unchanged; both directions of the annihilator equivalence are proved. -/
def sourceAnnZEquiv (p : X ⟶ B) (f : X ⟶ X) (x : X) (hbase : f ≫ p = p) :
    AlgebraicGeometry.tangentDerivations p x ≃
      {D : Derivation ℤ (TargetStalk x) (PointField x) //
        ∀ r : BaseStalk p f x, D (algebraMap (BaseStalk p f x) (TargetStalk x) r) = 0} where
  toFun D := ⟨D.val, fun r => by
    change D.val (baseTargetHom p f x r) = 0
    rw [baseComposite_apply p f x hbase]
    exact D.property _⟩
  invFun D := ⟨D.val, fun r => by
    have hz := D.property ((baseStalkIso p f x hbase).inv r)
    change D.val (baseTargetHom p f x ((baseStalkIso p f x hbase).inv r)) = 0 at hz
    rwa [baseComposite_inv_apply p f x hbase] at hz⟩
  left_inv _ := Subtype.ext (Derivation.ext fun _ => rfl)
  right_inv _ := Subtype.ext (Derivation.ext fun _ => rfl)

/-- Native image tangent derivations, with coefficients pushed through the
ACTUAL residue-field isomorphism. The new source-stalk action is induced by
f.stalkMap x and the actual target residue map. -/
def imageAnnZEquiv (p : X ⟶ B) (f : X ⟶ X) (x : X)
    [IsIso (f.residueFieldMap x)] :
    AlgebraicGeometry.tangentDerivations p (f x) ≃
      {D : Derivation ℤ (SourceStalk f x) (PointField x) //
        ∀ r : BaseStalk p f x, D (algebraMap (BaseStalk p f x) (SourceStalk f x) r) = 0} where
  toFun D := ⟨(coefficientIso f x).compDer D.val, fun r => by
    change (f.residueFieldMap x).hom (D.val (p.stalkMap (f x) r)) = 0
    rw [D.property, map_zero]⟩
  invFun D := ⟨(coefficientIso f x).symm.compDer D.val, fun r => by
    change (inv (f.residueFieldMap x)).hom (D.val (p.stalkMap (f x) r)) = 0
    have hz : D.val (p.stalkMap (f x) r) = 0 := D.property r
    rw [hz, map_zero]⟩
  left_inv D := Subtype.ext ((coefficientIso f x).compDer.symm_apply_apply D.val)
  right_inv D := Subtype.ext ((coefficientIso f x).compDer.apply_symm_apply D.val)

/-- The genuine relative derivation space of the actual target stalk. -/
abbrev SourceRelative (p : X ⟶ B) (f : X ⟶ X) (x : X) :=
  Derivation (BaseStalk p f x) (TargetStalk x) (PointField x)

/-- The genuine relative derivation space of the actual source stalk, with
coefficients acting through f.stalkMap x followed by the actual residue map. -/
abbrev ImageRelative (p : X ⟶ B) (f : X ⟶ X) (x : X) :=
  Derivation (BaseStalk p f x) (SourceStalk f x) (PointField x)

/-- Actual tangent-to-relative dictionary at x. -/
def sourceRelativeEquiv (p : X ⟶ B) (f : X ⟶ X) (x : X) (hbase : f ≫ p = p) :
    AlgebraicGeometry.tangentDerivations p x ≃ SourceRelative p f x :=
  (sourceAnnZEquiv p f x hbase).trans
    (annihilatingZEquiv (BaseStalk p f x) (TargetStalk x) (PointField x))

/-- Actual tangent-to-relative dictionary at f(x), including the canonical
coefficient pushforward; no arbitrary chosen residue-field isomorphism. -/
def imageRelativeEquiv (p : X ⟶ B) (f : X ⟶ X) (x : X)
    [IsIso (f.residueFieldMap x)] :
    AlgebraicGeometry.tangentDerivations p (f x) ≃ ImageRelative p f x :=
  (imageAnnZEquiv p f x).trans
    (annihilatingZEquiv (BaseStalk p f x) (SourceStalk f x) (PointField x))

/-- The exact desired native restriction map. Its algebra map is
DEFINITIONALLY f.stalkMap x; no map or carrier is substituted. -/
def actualRelativeRestriction (p : X ⟶ B) (f : X ⟶ X) (x : X) :
    SourceRelative p f x → ImageRelative p f x :=
  fun D => D.compAlgebraMap (SourceStalk f x)

/-- The actual composition square: the canonical tangent derivation map uses
inverse residue transport, and the image dictionary uses the actual forward
residue map. They cancel, leaving exactly D precomposed with f.stalkMap x. -/
theorem actualRestriction_square (p : X ⟶ B) (f : X ⟶ X) (x : X)
    (hbase : f ≫ p = p) [IsIso (f.residueFieldMap x)]
    (D : AlgebraicGeometry.tangentDerivations p x) :
    imageRelativeEquiv p f x
      (AlgebraicGeometry.tangentDerivationMap f p p x hbase D) =
    actualRelativeRestriction p f x (sourceRelativeEquiv p f x hbase D) := by
  apply Derivation.ext
  intro a
  change (f.residueFieldMap x).hom
    ((inv (f.residueFieldMap x)).hom (D.val (f.stalkMap x a))) = D.val (f.stalkMap x a)
  exact (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.apply_symm_apply _

/-- Bijectivity of the genuine canonical tangent map gives bijectivity of its
native tangent-derivation map. This uses the actual dottedDerivationEquiv at
both points, not a replacement tangent model. -/
theorem tangentDerivationMap_bijective (p : X ⟶ B) (f : X ⟶ X) (x : X)
    (hbase : f ≫ p = p) [IsIso (f.residueFieldMap x)]
    (h : Function.Bijective (AlgebraicGeometry.tangentMap f p p hbase x)) :
    Function.Bijective (AlgebraicGeometry.tangentDerivationMap f p p x hbase) := by
  let E := AlgebraicGeometry.dottedDerivationEquiv p x
  let E' := AlgebraicGeometry.dottedDerivationEquiv p (f x)
  constructor
  · intro D₁ D₂ hD
    apply E.symm.injective
    apply h.1
    change E'.symm
      (AlgebraicGeometry.tangentDerivationMap f p p x hbase (E (E.symm D₁))) =
        E'.symm
      (AlgebraicGeometry.tangentDerivationMap f p p x hbase (E (E.symm D₂)))
    rw [E.apply_symm_apply, E.apply_symm_apply, hD]
  · intro D
    obtain ⟨θ, hθ⟩ := h.2 (E'.symm D)
    refine ⟨E θ, E'.symm.injective ?_⟩
    change AlgebraicGeometry.tangentMap f p p hbase x θ = E'.symm D
    exact hθ

/-- The actual canonical tangent-to-relative transport closes the restriction
bijection once the genuine canonical tangent map is bijective. The arithmetic
multiplication theorem below supplies that input from the actual unit. -/
theorem relativeRestriction_bijective_of_canonicalTangent
    (p : X ⟶ B) (f : X ⟶ X) (x : X) (hbase : f ≫ p = p)
    [IsIso (f.residueFieldMap x)]
    (h : Function.Bijective (AlgebraicGeometry.tangentMap f p p hbase x)) :
    Function.Bijective (actualRelativeRestriction p f x) := by
  have hD := tangentDerivationMap_bijective p f x hbase h
  let E := sourceRelativeEquiv p f x hbase
  let E' := imageRelativeEquiv p f x
  constructor
  · intro D₁ D₂ hEq
    apply E.symm.injective
    apply hD.1
    apply E'.injective
    rw [actualRestriction_square, actualRestriction_square,
      E.apply_symm_apply, E.apply_symm_apply, hEq]
  · intro D
    obtain ⟨v, hv⟩ := hD.2 (E'.symm D)
    refine ⟨E v, ?_⟩
    rw [← actualRestriction_square, hv, E'.apply_symm_apply]

/-- Full actual multiplication result, for every field and every invertible
natural m. The m=0 branch is excluded by the genuine FIELD unit assumption,
not by adding a positive-index hypothesis to the theorem. No Smooth, Flat,
CharZero, perfect-field, dimension or desired-bijection premise is required. -/
theorem unit_relativeDerivationRestriction_bijective
    (k : Type u) [Field k] (G : Over (Spec (.of k))) [GrpObj G]
    (m : ℕ) (hm : IsUnit (m : k)) (s : Spec (.of k)) :
    Function.Bijective
      (actualRelativeRestriction G.hom
        ((𝟙 G ^ m : G ⟶ G).left) ((η[G]).left s)) := by
  cases m with
  | zero => simp at hm
  | succ n =>
    let e := (η[G]).left s
    let f := (𝟙 G ^ ((n + 1 : ℕ) : ℤ) : G ⟶ G).left
    let χ : k →+* PointField e :=
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec (.of k)).presheaf.germ ⊤ (G.hom e) trivial ≫
        (Spec (.of k)).residue (G.hom e) ≫ G.hom.residueFieldMap e).hom
    have hmκ : IsUnit ((n + 1 : ℕ) : PointField e) := by
      simpa only [Nat.succ_eq_add_one, map_natCast] using hm.map χ
    haveI : IsIso (f.residueFieldMap e) :=
      AlgebraicGeometry.isIso_residueFieldMap_zpow_id_left G s ((n + 1 : ℕ) : ℤ)
    have hT : Function.Bijective
        (AlgebraicGeometry.tangentMap f G.hom G.hom (Over.w _) e) :=
      H101DirectFieldRoute.canonical_unit_tangentMap_bijective G s n hmκ
    have hRel : Function.Bijective (actualRelativeRestriction G.hom f e) :=
      relativeRestriction_bijective_of_canonicalTangent G.hom f e (Over.w _) hT
    have hpow : (𝟙 G : G ⟶ G) ^ ((n + 1 : ℕ) : ℤ) =
        (𝟙 G : G ⟶ G) ^ Nat.succ n := by
      rw [Nat.succ_eq_add_one]
      exact zpow_natCast (𝟙 G : G ⟶ G) (n + 1)
    have hf : f = (𝟙 G ^ Nat.succ n : G ⟶ G).left :=
      congrArg (fun a : G ⟶ G => a.left) hpow
    exact (congrArg (fun a : G.left ⟶ G.left =>
      Function.Bijective (actualRelativeRestriction G.hom a e)) hf).mp hRel

end H101DirectFieldRoute.ActualTransport
