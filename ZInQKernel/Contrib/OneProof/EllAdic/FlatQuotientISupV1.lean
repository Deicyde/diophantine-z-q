import ZInQKernel.Contrib.OneProof.EllAdic.FlatSequenceRepresentativesV1
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Span.Defs

set_option autoImplicit false

namespace RC53.EllAdic

/-- For an increasing sequence of ideals in a fixed ring, flatness of
all the actual quotients gives flatness of the quotient by the supremum.
The cocone maps are the canonical quotient factors, not arbitrary maps. -/
theorem flat_quotient_iSup_of_monotone {R : Type*} [CommRing R]
    (I : ℕ → Ideal R) (hi : Monotone I)
    (hflat : ∀ i, Module.Flat R (R ⧸ I i)) :
    Module.Flat R (R ⧸ (⨆ i, I i)) := by
  let J : Ideal R := ⨆ i, I i
  let leg (i : ℕ) : (R ⧸ I i) →ₗ[R] (R ⧸ J) :=
    (Ideal.Quotient.factorₐ R (le_iSup I i)).toLinearMap
  let step {i j : ℕ} (h : i ≤ j) : (R ⧸ I i) →ₗ[R] (R ⧸ I j) :=
    (Ideal.Quotient.factorₐ R (hi h)).toLinearMap
  have hleg (i : ℕ) (x : R) : leg i (Ideal.Quotient.mk (I i) x) = Ideal.Quotient.mk J x := rfl
  have hstep {i j : ℕ} (h : i ≤ j) (x : R) :
      step h (Ideal.Quotient.mk (I i) x) = Ideal.Quotient.mk (I j) x := rfl
  refine flat_of_sequence_representatives (fun i => R ⧸ I i) (fun h => step h) leg ?_ ?_ ?_ hflat
  · intro i j h y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hstep h x, hleg j x, hleg i x]
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨0, Ideal.Quotient.mk (I 0) x, hleg 0 x⟩
  · intro i y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx : x ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp ((hleg i x).symm.trans hy)
    have hdir : Directed (· ≤ ·) I := fun a b =>
      ⟨max a b, hi (le_max_left a b), hi (le_max_right a b)⟩
    obtain ⟨j, hj⟩ := (Submodule.mem_iSup_of_directed I hdir).mp hx
    refine ⟨max i j, le_max_left i j, ?_⟩
    exact (hstep (le_max_left i j) x).trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr (hi (le_max_right i j) hj))

end RC53.EllAdic
