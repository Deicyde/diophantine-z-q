import ZInQKernel.Contrib.OneProof.EllAdic.FlatModuleDirectLimitNatV1
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

open scoped TensorProduct

namespace RC53.EllAdic

universe u v

/-- A countable directed limit of faithfully flat commutative algebras over a fixed base
is faithfully flat over that base. -/
theorem faithfullyFlat_directLimit_nat
    {A : Type u} [CommRing A]
    (B : ℕ → Type v) [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
    (f : ∀ i j, i ≤ j → B i →ₐ[A] B j) [DirectedSystem B (f · · ·)]
    (stageFaithful : ∀ i, Module.FaithfullyFlat A (B i)) :
    Module.FaithfullyFlat A (_root_.DirectLimit B f) := by
  let g : ∀ i j, i ≤ j → B i →ₗ[A] B j := fun i j h => (f i j h).toLinearMap
  let : DirectedSystem B (g · · ·) := by
    change DirectedSystem B (f · · ·)
    infer_instance
  let C := _root_.DirectLimit B f
  let D := Module.DirectLimit B g
  let iC : ∀ i, B i →ₐ[A] C := _root_.DirectLimit.Algebra.of (R := A) B f
  let iD : ∀ i, B i →ₗ[A] D := Module.DirectLimit.of A ℕ B g
  let p : D →ₗ[A] C := Module.DirectLimit.lift A ℕ B g (fun i => (iC i).toLinearMap) (by
    intro i j hij x
    exact _root_.DirectLimit.Algebra.of_f (R := A) (G := B) (f := f) hij x)
  let q : C →ₗ[A] D := _root_.DirectLimit.Module.lift A ℕ B f iD (by
    intro i j hij x
    exact Module.DirectLimit.of_f (R := A) (G := B) (f := g))
  have hp (i : ℕ) (x : B i) : p (iD i x) = iC i x :=
    Module.DirectLimit.lift_of (R := A) (G := B) (f := g) _ _ x
  have hq (i : ℕ) (x : B i) : q (iC i x) = iD i x := by
    change q (_root_.DirectLimit.Module.of A ℕ B f i x) = iD i x
    exact _root_.DirectLimit.Module.lift_of (R := A) (G := B) (f := f) _ _ x
  have hpq : p.comp q = LinearMap.id := by
    apply _root_.DirectLimit.Module.hom_ext (R := A) (G := B) (f := f)
    intro i
    apply LinearMap.ext
    intro x
    change p (q (iC i x)) = iC i x
    rw [hq, hp]
  refine (Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality A C).2 ⟨?_, ?_⟩
  · let : Module.Flat A D := flat_moduleDirectLimit_nat B g (fun i => (stageFaithful i).toFlat)
    exact Module.Flat.of_retract q p hpq
  · intro X _ _ hX
    let : Subsingleton (C ⊗[A] X) := hX
    refine (subsingleton_iff_forall_eq (0 : X)).2 ?_
    intro x
    have hx : (1 : C) ⊗ₜ[A] x = 0 := Subsingleton.elim _ _
    have hxD : iD 0 (1 : B 0) ⊗ₜ[A] x = 0 := by
      rw [← hq 0 (1 : B 0), map_one]
      simpa only [LinearMap.rTensor_tmul, map_zero] using
        congrArg (fun y : C ⊗[A] X => q.rTensor X y) hx
    let t : ∀ i j, i ≤ j → (B i ⊗[A] X) →ₗ[A] (B j ⊗[A] X) :=
      fun i j hij => (g i j hij).rTensor X
    let : DirectedSystem (fun i => B i ⊗[A] X) (t · · ·) := by
      dsimp only [t]
      infer_instance
    let e := TensorProduct.directLimitLeft g X
    have he : e (iD 0 (1 : B 0) ⊗ₜ[A] x) =
        Module.DirectLimit.of A ℕ (fun i => B i ⊗[A] X) t 0 ((1 : B 0) ⊗ₜ[A] x) :=
      TensorProduct.directLimitLeft_tmul_of (f := g) X (i := 0) (1 : B 0) x
    have hxT : Module.DirectLimit.of A ℕ (fun i => B i ⊗[A] X) t 0
        ((1 : B 0) ⊗ₜ[A] x) = 0 :=
      he.symm.trans ((congrArg (fun y : D ⊗[A] X => e y) hxD).trans (map_zero e))
    obtain ⟨j, h0j, hj⟩ := Module.DirectLimit.of.zero_exact hxT
    change (g 0 j h0j).rTensor X ((1 : B 0) ⊗ₜ[A] x) = 0 at hj
    rw [LinearMap.rTensor_tmul] at hj
    change (f 0 j h0j (1 : B 0)) ⊗ₜ[A] x = 0 at hj
    have hj1 : (1 : B j) ⊗ₜ[A] x = 0 := by simpa only [map_one] using hj
    let : Module.FaithfullyFlat A (B j) := stageFaithful j
    exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := A) (M := X) (A := B j) x).1 hj1

end RC53.EllAdic
