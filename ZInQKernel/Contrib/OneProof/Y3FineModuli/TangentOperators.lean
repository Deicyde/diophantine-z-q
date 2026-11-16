import ZInQKernel.HDecomp.QM.Structures
import ZInQKernel.Contrib.OneProof.Y3FineModuli.SourceTangentPoints

/-!
# Operators on the actual tangent-point model

Proof method/body ported from the source's
`S_CerednikDrinfeld_QM_exists_moduleEnd_apply_eq_pushPt_of_isTangentVector`
at FLT `6e837e75355538c7f80bab5b956861e86c4eacc2` (Apache-2.0).
This specialization uses the actual ring `LeafQM.O` instead of a lattice
subtype with partially supplied multiplication. No action on a fabricated
vector space is assumed: the operators are constructed through the given
injective, exhaustive, additive and scalar-compatible tangent-point map.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace ZInQ.Contrib.OneProof.Y3FineModuli.Source

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open CerednikDrinfeld.QM

namespace TangentAct

variable {S : Type u} [CommRing S] {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem push_one_eq (φ : A ⟶ A) (hφ : φ ≫ f = f)
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t f), pushPt φ hφ (L.mul t P Q) =
        L.mul t (pushPt φ hφ P) (pushPt φ hφ Q))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) :
    pushPt φ hφ (L.one t) = L.one t := by
  set e := pushPt φ hφ (L.one t) with he
  have hx : L.mul t e e = e := by rw [he, ← hhom, L.one_mul]
  calc e = L.mul t (L.one t) e := (L.one_mul _ _).symm
    _ = L.mul t (L.mul t (L.inv t e) e) e := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t e) (L.mul t e e) := L.mul_assoc _ _ _ _
    _ = L.mul t (L.inv t e) e := by rw [hx]
    _ = L.one t := L.inv_mul_cancel _ _

end TangentAct

/-- The literal order acts linearly on any exhaustive compatible model of the
actual dual-number tangent points. The action and its uniqueness are proved,
not added as an implicit instance or assumed derivative bridge. -/
theorem literal_order_tangent_operators
    {S : Type u} [CommRing S] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    (act : LeafQM.O → (A ⟶ A)) (act_over : ∀ x : LeafQM.O, act x ≫ f = f)
    (act_hom : ∀ (x : LeafQM.O) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
      (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : act 1 = 𝟙 A)
    (act_mul : ∀ x y : LeafQM.O, act (x * y) = act y ≫ act x)
    (act_add : ∀ (x y : LeafQM.O) {T : Scheme.{u}}
      (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
    (k : Type u) [Field k] (sk : S →+* k)
    (V : Type u) [AddCommGroup V] [Module k V]
    (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k sk) f,
      P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) :
    ∃ ρ : LeafQM.O →+* Module.End k V,
      (∀ (x : LeafQM.O) (v : V), τ (ρ x v) = pushPt (act x) (act_over x) (τ v)) ∧
      (∀ (m : LeafQM.O) (Φ : V →ₗ[k] V),
        (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) → ρ m = Φ) := by
  classical
  have hunit : ∀ x : LeafQM.O,
      pushPt (act x) (act_over x) (L.one (geomPoint k sk)) = L.one (geomPoint k sk) :=
    fun x => TangentAct.push_one_eq L (act x) (act_over x) (act_hom x) _
  have htv : ∀ (x : LeafQM.O) (v : V),
      IsTangentVector L k sk (pushPt (act x) (act_over x) (τ v)) := by
    intro x v
    have hv : IsTangentVector L k sk (τ v) := (hrange (τ v)).mp ⟨v, rfl⟩
    change tangentZero k ≫ ((τ v).1 ≫ act x) = (L.one (geomPoint k sk)).1
    rw [← Category.assoc, show tangentZero k ≫ (τ v).1 = _ from hv]
    exact congrArg Subtype.val (hunit x)
  have hex : ∀ (x : LeafQM.O) (v : V),
      ∃ w : V, τ w = pushPt (act x) (act_over x) (τ v) :=
    fun x v => (hrange _).mpr (htv x v)
  choose θv hθv using hex
  have hθadd : ∀ (x : LeafQM.O) (v w : V), θv x (v + w) = θv x v + θv x w := by
    intro x v w
    apply hinj
    rw [hθv, hadd, hadd, act_hom, hθv, hθv]
  have hθsmul : ∀ (x : LeafQM.O) (c : k) (v : V), θv x (c • v) = c • θv x v := by
    intro x c v
    apply hinj
    apply Subtype.ext
    rw [hsmul, congrArg Subtype.val (hθv x (c • v)), congrArg Subtype.val (hθv x v)]
    change (τ (c • v)).1 ≫ act x = tangentScale k c ≫ ((τ v).1 ≫ act x)
    rw [hsmul, Category.assoc]
  let θ : LeafQM.O → Module.End k V := fun x =>
    { toFun := θv x, map_add' := hθadd x, map_smul' := hθsmul x }
  have hθ : ∀ (x : LeafQM.O) (v : V),
      τ (θ x v) = pushPt (act x) (act_over x) (τ v) := fun x v => hθv x v
  have hθplus : ∀ x y : LeafQM.O, θ (x + y) = θ x + θ y := by
    intro x y
    apply LinearMap.ext; intro v
    apply hinj
    rw [hθ, act_add, LinearMap.add_apply, hadd, hθ, hθ]
  have hθone : θ 1 = 1 := by
    apply LinearMap.ext; intro v
    apply hinj
    rw [hθ, Module.End.one_apply]
    apply Subtype.ext
    change (τ v).1 ≫ act 1 = (τ v).1
    rw [act_one, Category.comp_id]
  have hθmul : ∀ x y : LeafQM.O, θ (x * y) = θ x * θ y := by
    intro x y
    apply LinearMap.ext; intro v
    apply hinj
    rw [hθ, Module.End.mul_apply, hθ, hθ]
    apply Subtype.ext
    change (τ v).1 ≫ act (x * y) = ((τ v).1 ≫ act y) ≫ act x
    rw [act_mul, Category.assoc]
  let θadd : LeafQM.O →+ Module.End k V := AddMonoidHom.mk' θ hθplus
  let ρ : LeafQM.O →+* Module.End k V :=
    { θadd with map_one' := hθone, map_mul' := hθmul }
  refine ⟨ρ, hθ, ?_⟩
  intro m Φ hΦ
  apply LinearMap.ext; intro v
  apply hinj
  exact (hθ m v).trans (hΦ v).symm

end ZInQ.Contrib.OneProof.Y3FineModuli.Source
