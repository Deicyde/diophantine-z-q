import ZInQKernel.Contrib.OneProof.RC.ModelLevels.ExactOrder
import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.AffineBaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Base change of the clopen exact-order factor -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion
open scoped TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

private theorem eq_of_idempotent_span {S : Type*} [CommRing S] {e f : S}
    (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : Ideal.span {e} = Ideal.span {f}) : e = f := by
  have hemem : e ∈ Ideal.span {f} := h ▸ Ideal.subset_span (Set.mem_singleton e)
  have hfmem : f ∈ Ideal.span {e} := h.symm ▸ Ideal.subset_span (Set.mem_singleton f)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hemem
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hfmem
  calc
    e = e * f := by rw [ha, mul_right_comm f a f, hf.eq]
    _ = f * e := mul_comm _ _
    _ = f := by rw [hb, mul_right_comm e b e, he.eq]

variable (W : WeierstrassCurve A) [W.IsElliptic] {N : ℕ} (hN : IsUnit (N : A))

/-- Compatibility of the first-wave affine torsion base change with one
divisor-level restriction. -/
def RestrictionBaseChange (d : ℕ) (hd : d ∣ N) : Prop :=
  let V := W.map (algebraMap A B)
  let hNB : IsUnit (N : B) := by
    simpa only [map_natCast] using hN.map (algebraMap A B)
  ∀ x : B ⊗[A] AffineTorsionAlgebra W N,
    affineTorsionAlgebraBaseChange (A := A) (B := B) W d
        (Algebra.TensorProduct.map (AlgHom.id A B) (restrictAffineTorsion W hN hd) x) =
      restrictAffineTorsion V hNB hd
        (affineTorsionAlgebraBaseChange (A := A) (B := B) W N x)

private theorem map_divisorIdempotent {d : ℕ} (hd : d ∣ N)
    (h : RestrictionBaseChange (B := B) W hN d hd) :
    let V := W.map (algebraMap A B)
    let hNB : IsUnit (N : B) := by
      simpa only [map_natCast] using hN.map (algebraMap A B)
    affineTorsionAlgebraBaseChange W N ((1 : B) ⊗ₜ[A] divisorIdempotent W hN hd) =
      divisorIdempotent V hNB hd := by
  let V := W.map (algebraMap A B)
  let hNB : IsUnit (N : B) := by simpa only [map_natCast] using hN.map (algebraMap A B)
  change affineTorsionAlgebraBaseChange W N ((1 : B) ⊗ₜ[A] divisorIdempotent W hN hd) = _
  let e := affineTorsionAlgebraBaseChange (A := A) (B := B) W N
  let e' := affineTorsionAlgebraBaseChange (A := A) (B := B) W d
  let f := restrictAffineTorsion W hN hd
  let g := Algebra.TensorProduct.map (AlgHom.id A B) f
  let g' := restrictAffineTorsion V hNB hd
  let i : AffineTorsionAlgebra W N →ₐ[A] B ⊗[A] AffineTorsionAlgebra W N :=
    Algebra.TensorProduct.includeRight
  have hker : RingHom.ker g = Ideal.span {i (divisorIdempotent W hN hd)} := by
    change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id A B) f) = _
    rw [Algebra.TensorProduct.lTensor_ker _ (restrictAffineTorsion_surjective W hN hd),
      show RingHom.ker f = _ from (divisorIdempotent_spec W hN hd).2,
      Ideal.map_span, Set.image_singleton]
  have hcomap : RingHom.ker g = (RingHom.ker g').comap e.toRingHom := by
    ext x
    have hx := h x
    change e' (g x) = g' (e x) at hx
    change g x = 0 ↔ g' (e x) = 0
    rw [← hx, map_eq_zero_iff e' e'.injective]
  have hspan : Ideal.span {e (i (divisorIdempotent W hN hd))} =
      Ideal.span {divisorIdempotent V hNB hd} := by
    calc
      _ = (RingHom.ker g).map e.toRingHom := by
        rw [hker, Ideal.map_span, Set.image_singleton]
        rfl
      _ = RingHom.ker g' := by
        rw [hcomap]
        exact Ideal.map_comap_of_surjective e.toRingHom e.surjective _
      _ = _ := (divisorIdempotent_spec V hNB hd).2
  exact eq_of_idempotent_span (((divisorIdempotent_spec W hN hd).1.map i).map e)
    (divisorIdempotent_spec V hNB hd).1 hspan

private noncomputable def clopenExactOrderBaseChangeOfRestriction
    (h : ∀ (d : ℕ) (hd : d ∣ N), d < N → RestrictionBaseChange (B := B) W hN d hd) :
    let V := W.map (algebraMap A B)
    let hNB : IsUnit (N : B) := by
      simpa only [map_natCast] using hN.map (algebraMap A B)
    B ⊗[A] ClopenFactor (exactOrderIdempotent W hN) ≃ₐ[B]
      ClopenFactor (exactOrderIdempotent V hNB) := by
  classical
  let V := W.map (algebraMap A B)
  let hNB : IsUnit (N : B) := by simpa only [map_natCast] using hN.map (algebraMap A B)
  let e := affineTorsionAlgebraBaseChange (A := A) (B := B) W N
  let i : AffineTorsionAlgebra W N →ₐ[A] B ⊗[A] AffineTorsionAlgebra W N :=
    Algebra.TensorProduct.includeRight
  have hE : e (i (exactOrderIdempotent W hN)) = exactOrderIdempotent V hNB := by
    simp only [exactOrderIdempotent, map_prod]
    apply Finset.prod_congr rfl
    intro d _
    obtain ⟨hd, hlt⟩ := Nat.mem_properDivisors.mp d.2
    exact map_divisorIdempotent W hN hd (h d.1 hd hlt)
  change e ((1 : B) ⊗ₜ[A] exactOrderIdempotent W hN) = _ at hE
  refine (clopenFactorBaseChange B _).trans <|
    IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers ((1 : B) ⊗ₜ[A] exactOrderIdempotent W hN))
      _ (T := Submonoid.powers (exactOrderIdempotent V hNB)) _ e ?_
  rw [Submonoid.map_powers, hE]

/-- The identification of the affine torsion charts, when natural for the
proper divisor restrictions, identifies the exact-order factor after
arbitrary base change. The equality of idempotents uses right exactness
of tensor product, including for nonflat extensions. -/
noncomputable def exactOrderBaseChangeOfRestriction
    (h : ∀ (d : ℕ) (hd : d ∣ N), d < N → RestrictionBaseChange (B := B) W hN d hd) :
    let V := W.map (algebraMap A B)
    let hNB : IsUnit (N : B) := by
      simpa only [map_natCast] using hN.map (algebraMap A B)
    B ⊗[A] ExactOrderAlgebra W hN ≃ₐ[B] ExactOrderAlgebra V hNB := by
  obtain _ | _ | N := N
  · exact clopenExactOrderBaseChangeOfRestriction W hN h
  · exact Algebra.TensorProduct.rid A B B
  · exact clopenExactOrderBaseChangeOfRestriction W hN h

#print axioms eq_of_idempotent_span
#print axioms map_divisorIdempotent
#print axioms clopenExactOrderBaseChangeOfRestriction
#print axioms exactOrderBaseChangeOfRestriction

end WeierstrassCurve.ModelLevels
