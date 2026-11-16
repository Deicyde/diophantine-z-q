import ZInQKernel.Contrib.OneProof.Y3FineModuli.TangentDimension
import ZInQKernel.Contrib.OneProof.Y3FineModuli.TangentOperators
import ZInQKernel.Contrib.OneProof.Y3FineModuli.LiteralOrderTrace

/-!
# Characteristic-zero tangent trace for the actual original QM order

This is the fixed-order counterpart of
`CerednikDrinfeld.QM.trace_eq_intCast_of_charZero_of_smoothOfRelativeDimension_two`
in FLT revision `6e837e75355538c7f80bab5b956861e86c4eacc2`.
The same three genuine steps are used: derive tangent dimension from actual
scheme points, construct the order operators through the exhaustive tangent
map, and prove their reduced trace. No tangent-rank or derivative-action bridge
is assumed. This is a trace prerequisite only, not an `R1fpAb` witness.
-/

set_option autoImplicit false
noncomputable section

namespace ZInQ.Contrib.OneProof.Y3FineModuli

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian
open Source.CerednikDrinfeld.QM

/-- The actual source-style `act_trace` condition for the literal project order,
proved in characteristic zero on genuine dual-number tangent-point models.
The full range, addition and scalar-compatibility conditions on `τ` are retained;
the statement does not substitute a four-dimensional Tate representation. -/
theorem literal_order_charZero_tangent_trace
    {R : Type} [CommRing R] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    [SmoothOfRelativeDimension 2 f]
    (act : LeafQM.O → (A ⟶ A)) (act_over : ∀ x : LeafQM.O, act x ≫ f = f)
    (act_hom : ∀ (x : LeafQM.O) {T : Scheme.{0}}
      (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (act_one : act 1 = 𝟙 A)
    (act_mul : ∀ x y : LeafQM.O, act (x * y) = act y ≫ act x)
    (act_add : ∀ (x y : LeafQM.O) {T : Scheme.{0}}
      (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f),
      pushPt (act (x + y)) (act_over (x + y)) P =
        L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P))
    (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (sk : R →+* k)
    (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V]
    (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k sk) f,
      P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    (m : LeafQM.O) (Φ : V →ₗ[k] V)
    (hΦ : ∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v))
    (n : ℤ)
    (hn : (m : LeafQM.B) + star (m : LeafQM.B) = ((n : ℚ) : LeafQM.B)) :
    LinearMap.trace k V Φ = (n : k) := by
  have hdim : Module.finrank k V = 2 :=
    Source.P2MW.S_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension.solution
      L 2 k sk V τ hinj hrange hadd hsmul
  obtain ⟨ρ, hρ, huniq⟩ := Source.literal_order_tangent_operators
    L act act_over act_hom act_one act_mul act_add k sk V τ hinj hrange hadd hsmul
  have hm : ρ m = Φ := huniq m Φ hΦ
  rw [← hm]
  exact literal_order_trace_eq_intCast ρ hdim m n hn

end ZInQ.Contrib.OneProof.Y3FineModuli
