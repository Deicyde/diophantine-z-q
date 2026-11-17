import ZInQKernel.Contrib.OneProof.Y3FineModuli.TangentDimension

/-!
# A concrete model of the actual identity tangent points

Separate new work after the frozen trace helper. The module is the dual of the
actual relative cotangent space at the identity of the geometric fibre. Its
point map is the actual source square-zero lift, not an assumed bijection,
rank, representation or moduli object. The frozen dimension proof's `pointOf`,
`γJ`, `γJ_mul` and smooth cotangent equivalence are reused without changing them.
Original source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2,
S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.
Apache-2.0; source license/notice/attribution are retained in Vendor/AnthropicFLT.
The extraction and named concrete model are new; no R1 witness is claimed.
The ordinary Lean 4.35 type-transparency elaboration option used by the reused
source body is enabled here as well; no kernel trust option is changed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u

namespace ZInQ.Contrib.OneProof.Y3FineModuli.Source.CanonicalTangent

open CategoryTheory AlgebraicGeometry
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open _root_.ZInQ.Contrib.OneProof.Y3FineModuli.Source.CerednikDrinfeld.QM
open _root_.ZInQ.Contrib.OneProof.Y3FineModuli.Source.P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody
open scoped _root_.ZInQ.Contrib.OneProof.Y3FineModuli.Source.P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody
  _root_.ZInQ.Contrib.OneProof.Y3FineModuli.Source.P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.TangentDimBody.TJ

variable {S : Type u} [CommRing S] {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (k : Type u) [Field k] (sk : S →+* k)

/-- The dual of the actual cotangent space of the geometric fibre at identity. -/
def Space : Type u := ωJ L k sk →ₗ[k] k

instance spaceAddCommGroup : AddCommGroup (Space L k sk) :=
  inferInstanceAs (AddCommGroup (ωJ L k sk →ₗ[k] k))

instance spaceModule : Module k (Space L k sk) :=
  inferInstanceAs (Module k (ωJ L k sk →ₗ[k] k))

/-- Casting the base condition forth and back preserves the actual point. -/
theorem castBase_symm_castBase {T : Scheme.{u}}
    {a b : T ⟶ Spec (CommRingCat.of S)} (hab : a = b) (P : SchemeHomOver a f) :
    castBase hab.symm (castBase hab P) = P := by
  subst hab
  rfl

/-- Restore the original tangent base of an actual source tangent point. -/
def fromTJ (t : TJ L k sk k) : SchemeHomOver (tangentBase k sk) f :=
  castBase (tangentBase_eq (k := k) (sk := sk)).symm t.1

theorem fromTJ_isTangentVector (t : TJ L k sk k) :
    IsTangentVector L k sk (fromTJ L k sk t) := by
  change bS k k ≫
    (castBase (tangentBase_eq (k := k) (sk := sk)).symm t.1).1 = (e L k sk).1
  rw [castBase_coe]
  exact t.2

theorem fromTJ_injective : Function.Injective (fromTJ L k sk) := by
  intro t t' htt'
  apply Subtype.ext
  exact castBase_injective (f := f) (tangentBase_eq (k := k) (sk := sk)).symm htt'

theorem fromTJ_range (P : SchemeHomOver (tangentBase k sk) f) :
    P ∈ Set.range (fromTJ L k sk) ↔ IsTangentVector L k sk P := by
  constructor
  · rintro ⟨t, ht⟩
    exact ht ▸ fromTJ_isTangentVector L k sk t
  · intro hP
    obtain ⟨P₀, hP₀⟩ := castBase_surjective (f := f)
      (tangentBase_eq (k := k) (sk := sk)).symm P
    have ht : bS k k ≫ P₀.1 = (e L k sk).1 := by
      change tangentZero k ≫ P₀.1 = (L.one (geomPoint k sk)).1
      rw [← castBase_coe (tangentBase_eq (k := k) (sk := sk)).symm P₀, hP₀]
      exact hP
    exact ⟨⟨P₀, ht⟩, hP₀⟩

/-- The actual square-zero scheme point induced by a cotangent linear form. -/
def pointMap (g : Space L k sk) : SchemeHomOver (tangentBase k sk) f :=
  fromTJ L k sk (pointOf g)

theorem pointMap_isTangentVector (g : Space L k sk) :
    IsTangentVector L k sk (pointMap L k sk g) := by
  change bS k k ≫
    (castBase (tangentBase_eq (k := k) (sk := sk)).symm (pointOf g).1).1 = (e L k sk).1
  rw [castBase_coe]
  exact (pointOf g).2

theorem pointMap_injective : Function.Injective (pointMap L k sk) := by
  intro g h hgh
  apply pointOf_injective (L := L) (k := k) (sk := sk)
  apply Subtype.ext
  exact castBase_injective (f := f) (tangentBase_eq (k := k) (sk := sk)).symm hgh

theorem pointMap_range (P : SchemeHomOver (tangentBase k sk) f) :
    P ∈ Set.range (pointMap L k sk) ↔ IsTangentVector L k sk P := by
  change P ∈ Set.range ((fromTJ L k sk) ∘ (fun g : Space L k sk => pointOf g)) ↔ _
  have honto : Function.Surjective (fun g : Space L k sk => pointOf g) :=
    pointOf_surjective (L := L) (k := k) (sk := sk) (M := k)
  rw [Set.range_comp, Set.range_eq_univ.mpr honto, Set.image_univ]
  exact fromTJ_range L k sk P

theorem pointMap_add (g h : Space L k sk) :
    pointMap L k sk (g + h) =
      L.mul (tangentBase k sk) (pointMap L k sk g) (pointMap L k sk h) := by
  have hpoint : pointOf (g + h) = TJ.mul (pointOf g) (pointOf h) := by
    apply (γJ L k sk k).injective
    rw [γJ_pointOf, γJ_mul, γJ_pointOf, γJ_pointOf]
    rfl
  unfold pointMap fromTJ
  rw [hpoint]
  change castBase _ (L.mul (tA k sk k) (pointOf g).1 (pointOf h).1) = _
  exact castBase_mul _ _ _

theorem pointMap_smul (c : k) (g : Space L k sk) :
    (pointMap L k sk (c • g)).1 = tangentScale k c ≫ (pointMap L k sk g).1 := by
  have hpoint : pointOf (c • g) = TJ.map (c • (LinearMap.id : k →ₗ[k] k)) (pointOf g) := by
    convert pointOf_map (c • (LinearMap.id : k →ₗ[k] k)) g using 1
    rfl
  unfold pointMap fromTJ
  rw [hpoint, castBase_coe, castBase_coe, TJ.map_val_val]
  rfl

/-- Finiteness follows from actual smooth cotangent geometry, not an input. -/
theorem space_finite (n : ℕ) [SmoothOfRelativeDimension n f] :
    Module.Finite k (Space L k sk) := by
  obtain ⟨Eω⟩ := nonempty_ωJ_equiv L k sk n
  let E : Space L k sk ≃ₗ[k] ((Fin n → k) →ₗ[k] k) := Eω.congrLeft k k
  exact Module.Finite.of_injective E.toLinearMap E.injective

/-- The rank of this concrete tangent model is derived from smoothness. -/
theorem space_finrank (n : ℕ) [SmoothOfRelativeDimension n f] :
    Module.finrank k (Space L k sk) = n := by
  exact _root_.ZInQ.Contrib.OneProof.Y3FineModuli.Source.P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.solution
    L n k sk (Space L k sk) (pointMap L k sk) (pointMap_injective L k sk)
    (pointMap_range L k sk) (pointMap_add L k sk) (pointMap_smul L k sk)

end ZInQ.Contrib.OneProof.Y3FineModuli.Source.CanonicalTangent
