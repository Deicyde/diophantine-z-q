import ZInQKernel.Contrib.OneProof.TateRationalImage

/-! # Invariant complements from endomorphism images in a semisimple algebra -/

noncomputable section

namespace ZInQ.Contrib.TateFiniteApproximation

/-- The idempotent generator of the principal left ideal of x gives an inner inverse. -/
theorem exists_innerInverse_of_semisimple {R : Type*} [Ring R] [IsSemisimpleRing R] (x : R) :
    ∃ y : R, x * y * x = x := by
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {x})
  have hx : x ∈ Ideal.span {e} := hI ▸ Ideal.mem_span_singleton_self x
  have he' : e ∈ Ideal.span {x} := hI.symm ▸ Ideal.mem_span_singleton_self e
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp he'
  refine ⟨b, ?_⟩
  rw [mul_assoc, hb, ← ha, mul_assoc, he.eq]

/-- If every invariant subspace occurs as the image of the action of a
semisimple ring of equivariant endomorphisms, then the representation splits. -/
theorem semisimpleRepresentation_of_endomorphism_ranges
    {F G V R : Type*} [Field F] [Monoid G] [AddCommGroup V] [Module F V]
    [Ring R] [IsSemisimpleRing R] (ρ : Representation F G V)
    (a : R →+* Module.End F V) (ha : ∀ r g, Commute (a r) (ρ g))
    (hrange : ∀ W : Subrepresentation ρ, ∃ r, LinearMap.range (a r) = W.toSubmodule) :
    ρ.IsSemisimpleRepresentation := by
  constructor
  intro W
  obtain ⟨r, hr⟩ := hrange W
  obtain ⟨s, hrs⟩ := exists_innerInverse_of_semisimple r
  let p := a (r * s)
  have hpr : p * a r = a r := by rw [← map_mul, hrs]
  have hp : IsIdempotentElem p := by
    change a (r * s) * a (r * s) = a (r * s)
    rw [← map_mul, ← mul_assoc, hrs]
  have hrp : LinearMap.range p = W.toSubmodule := by
    rw [← hr]
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      exact ⟨a s v, by simp [p, Module.End.mul_apply]⟩
    · rintro _ ⟨v, rfl⟩
      exact ⟨a r v, LinearMap.congr_fun hpr v⟩
  let C : Subrepresentation ρ := {
    toSubmodule := LinearMap.ker p
    apply_mem_toSubmodule := by
      intro g v hv
      change p (ρ g v) = 0
      rw [show p (ρ g v) = ρ g (p v) from LinearMap.congr_fun (ha (r*s) g).eq v,
        show p v = 0 from hv, map_zero] }
  have hc := LinearMap.IsIdempotentElem.isCompl hp
  rw [hrp] at hc
  exact ⟨C, ⟨disjoint_iff.mpr (Subrepresentation.toSubmodule_injective hc.inf_eq_bot),
    codisjoint_iff.mpr (Subrepresentation.toSubmodule_injective hc.sup_eq_top)⟩⟩

end ZInQ.Contrib.TateFiniteApproximation
