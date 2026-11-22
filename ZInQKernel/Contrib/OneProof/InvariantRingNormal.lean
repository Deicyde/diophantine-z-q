import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! Normality of the invariant subring of a normal domain. -/

open scoped nonZeroDivisors

/-- The fixed subring in a normal domain is integrally closed. The fixed ring
is presented by an injective algebra map and its exact image. -/
theorem isIntegrallyClosed_of_range_eq_fixed
    {A B G : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsIntegrallyClosed B] [Algebra A B] (hinj : Function.Injective (algebraMap A B))
    (act : G → B →+* B)
    (hInv : Set.range (algebraMap A B) = {b | ∀ g, act g b = b}) :
    IsIntegrallyClosed A := by
  let _ : Algebra A (FractionRing B) :=
    ((algebraMap B (FractionRing B)).comp (algebraMap A B)).toAlgebra
  let inc := Algebra.ofId A (FractionRing B)
  have hinc : Function.Injective inc :=
    (IsFractionRing.injective B (FractionRing B)).comp hinj
  let φ : FractionRing A →ₐ[A] FractionRing B := IsFractionRing.liftAlgHom hinc
  have hφ (a : A) :
      φ (algebraMap A (FractionRing A) a) = algebraMap B (FractionRing B) (algebraMap A B a) :=
    φ.commutes a
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (IsIntegral.map_of_comp_eq (algebraMap A B) φ.toRingHom
      (RingHom.ext fun a => (hφ a).symm) hx)
  obtain ⟨u, v, hv, he⟩ := IsFractionRing.div_surjective A x
  have hvA : v ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hv
  have hvB : algebraMap A B v ≠ 0 := fun h => hvA (hinj (h.trans (map_zero _).symm))
  have hu (a : A) (g : G) : act g (algebraMap A B a) = algebraMap A B a := by
    have h : algebraMap A B a ∈ Set.range (algebraMap A B) := ⟨a, rfl⟩
    rw [hInv] at h
    exact h g
  have hm : b * algebraMap A B v = algebraMap A B u := by
    apply IsFractionRing.injective B (FractionRing B)
    rw [map_mul, hb, ← hφ v, ← hφ u]
    change φ x * φ (algebraMap A (FractionRing A) v) = _
    rw [← map_mul]
    apply congrArg φ
    have hvK : algebraMap A (FractionRing A) v ≠ 0 :=
      fun h => hvA ((IsFractionRing.injective A (FractionRing A)) (h.trans (map_zero _).symm))
    rw [← he, div_mul_cancel₀ _ hvK]
  have hbFixed (g : G) : act g b = b := by
    apply mul_right_cancel₀ hvB
    have h := congrArg (act g) hm
    rw [map_mul, hu v g, hu u g] at h
    exact h.trans hm.symm
  have hr : b ∈ Set.range (algebraMap A B) := by
    rw [hInv]
    exact hbFixed
  obtain ⟨a, ha⟩ := hr
  exact ⟨a, φ.injective ((hφ a).trans ((congrArg (algebraMap B (FractionRing B)) ha).trans hb))⟩

#print axioms isIntegrallyClosed_of_range_eq_fixed
